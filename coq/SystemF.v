(** * System F **)

Require Export SfLib.


(* ###################################################################### *)
(** ** Syntax *)

Module SYSTEMF.

(* ################################### *)
(** *** Types *)

Inductive ty : Type := 
  | TVar   : nat -> ty 
  | TArrow : ty -> ty -> ty
  | TUniv  : ty -> ty.


Fixpoint tshift (X : nat) (T : ty) : ty :=
  match T with
  | TVar Y       => TVar (if le_gt_dec X Y then 1 + Y else Y)
  | TArrow T1 T2 => TArrow (tshift X T1) (tshift X T2)
  | TUniv T2     => TUniv (tshift (1 + X) T2)
  end.



(* ################################### *)
(** *** Terms *)

Inductive tm : Type :=
  | tvar  : nat -> tm
  | tapp  : tm -> tm -> tm
  | tabs  : ty -> tm -> tm
  | ttapp : tm -> ty -> tm
  | ttabs : tm -> tm.

Tactic Notation "t_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tvar" | Case_aux c "tapp" 
  | Case_aux c "tabs" | Case_aux c "ttapp" 
  | Case_aux c "ttabs" ].


Fixpoint shift (x:nat) (t:tm) : tm :=
  match t with
    | tvar y      => tvar (if le_gt_dec x y then S y else y)
    | tabs T1 t2  => tabs T1 (shift (S x) t2)
    | tapp t1 t2  => tapp (shift x t1) (shift x t2)
    | ttabs t2    => ttabs (shift x t2)
    | ttapp t1 T2 => ttapp (shift x t1) T2
  end.

Fixpoint shift_typ (X : nat) (t : tm) {struct t} : tm :=
  match t with
    | tvar y       => tvar y
    | tabs T1 t2   => tabs (tshift X T1) (shift_typ X t2)
    | tapp t1 t2   => tapp (shift_typ X t1) (shift_typ X t2)
    | ttabs t2     => ttabs (shift_typ (1 + X) t2)
    | ttapp t1 T2  => ttapp (shift_typ X t1) (tshift X T2)
  end.

(** Note that an abstraction [\x:T.t] (formally, [tabs x T t]) is
    always annotated with the type [T] of its parameter, in contrast
    to Coq (and other functional languages like ML, Haskell, etc.),
    which use _type inference_ to fill in missing annotations.  We're
    not considering type inference here, to keep things simple. *)

(* ###################################################################### *)
(** ** Operational Semantics *)

(** To define the small-step semantics of STLC terms, we begin -- as
    always -- by defining the set of values.  Next, we define the
    critical notions of _free variables_ and _substitution_, which are
    used in the reduction rule for application expressions.  And
    finally we give the small-step relation itself. *)

(* ################################### *)
(** *** Values *)

Inductive value : tm -> Prop :=
  | v_abs : forall T t,
      value (tabs T t)
  | v_tabs : forall t,
      value (ttabs t).

Hint Constructors value.


(* ###################################################################### *)
(** *** Free Variables and Substitution *)


Class Subst (X S T : Type) := {
  do_subst : X -> S -> T -> T
}.
Notation "'[' x ':=' s ']' t" := (do_subst x s t) (at level 20).

(* Term Sustitution *)
Fixpoint subst_term_fix (x:nat) (s:tm) (t:tm) : tm :=
  match t with
  | tvar y => 
    if eq_nat_dec x y then s
    else if le_lt_dec x y then tvar (y-1)
         else tvar y
  | tabs T t1 => 
      tabs T (subst_term_fix (S x) (shift 0 s) t1) 
  | tapp t1 t2 => 
      tapp (subst_term_fix x s t1) (subst_term_fix x s t2)
  | ttabs t =>
      ttabs (subst_term_fix x (shift_typ 0 s) t)
  | ttapp t T =>
      ttapp (subst_term_fix x s t) T
  end.

Instance subst_tm_tm : Subst nat tm tm := {
  do_subst := subst_term_fix
}.


Inductive subst_term : tm -> nat -> tm -> tm -> Prop := 
  | s_var1 : forall s x,
      subst_term s x (tvar x) s
  | s_var2 : forall s x x',
      x < x' ->
      subst_term s x (tvar x') (tvar (x' - 1))
  | s_var3 : forall s x x',
      x > x' ->
      subst_term s x (tvar x') (tvar x')
  | s_tabs : forall s x T t t',
      subst_term (shift 0 s) (S x) t t' ->
      subst_term s x (tabs T t) (tabs T t')
  | s_tapp : forall s x t1 t2 t1' t2',
      subst_term s x t1 t1' ->
      subst_term s x t2 t2' ->
      subst_term s x (tapp t1 t2) (tapp t1' t2')
  | s_ttabs : forall s x t t',
      subst_term (shift_typ 0 s) x t t' ->
      subst_term s x (ttabs t) (ttabs t')
  | s_ttapp : forall s x t t' T,
      subst_term s x t t' ->
      subst_term s x (ttapp t T) (ttapp t' T).

Hint Constructors subst_term.

Theorem subst_term_correct : forall s x t t',
  [x:=s]t = t' <-> subst_term s x t t'.
Proof.
  intros s x t. split.
  Case "->".
    generalize dependent t'. generalize dependent x.
    generalize dependent s.
    induction t; intros s x t' H; simpl in H.
    SCase "t = tvar i".
      destruct (eq_nat_dec x n) in H; subst.
      SSCase "x = n".
        constructor.
      SSCase "x <> n".
        destruct (le_lt_dec x n).
          constructor. omega. 
          constructor. omega.
    SCase "t = tapp t1 t2".
      rewrite <- H. constructor.
      apply IHt1. reflexivity.
      apply IHt2. reflexivity.
    SCase "t = tabs i t t0".
      subst. constructor. apply IHt. trivial.
    SCase "t = ttapp".
      subst. constructor. apply IHt. trivial.
    SCase "t = ttabs".
      subst. constructor. apply IHt. trivial.
  Case "<-".
    intro H. induction H; simpl;
    subst; try reflexivity; try assumption.
    destruct (eq_nat_dec x x). trivial. omega.
    destruct (eq_nat_dec x x'). omega. destruct le_lt_dec.
    trivial. omega. 
    destruct (eq_nat_dec x x'). omega. destruct le_lt_dec.
    omega. trivial.
Qed.

(** [] *)


(* Type in Type Sustitution *)

Fixpoint subst_type_in_type_fix (I:nat) (P:ty) (T:ty) : ty :=
  match T with
  | TVar N =>
      if eq_nat_dec I N then P
      else if le_lt_dec I N then TVar (N-1)
           else TVar N
  | TArrow T1 T2 =>
      TArrow (subst_type_in_type_fix I P T1) (subst_type_in_type_fix I P T2)
  | TUniv T => TUniv (subst_type_in_type_fix (I + 1) (tshift 0 P) T)
  end.

Instance subst_ty_ty : Subst nat ty ty := {
  do_subst := subst_type_in_type_fix
}.


Inductive subst_type_in_type (T:ty) (I:nat) : ty -> ty -> Prop :=
  | s_var_eq :
      subst_type_in_type T I (TVar I) T
  | s_var_lt : forall N,
      N < I ->
      subst_type_in_type T I (TVar N) (TVar N)
  | s_var_gt : forall N,
      N > I ->
      subst_type_in_type T I (TVar N) (TVar (N-1))
  | s_arrow : forall T1 T2 T1' T2',
      subst_type_in_type T I T1 T1' ->
      subst_type_in_type T I T2 T2' ->
      subst_type_in_type T I (TArrow T1 T2) (TArrow T1' T2')
  | s_univ : forall T1 T2,
      subst_type_in_type (tshift 0 T) (I+1) T1 T2 ->
      subst_type_in_type T I (TUniv T1) (TUniv T2).

Lemma subst_type_in_type_correct : forall N P T1 T2,
  [N:=P]T1 = T2 <-> subst_type_in_type P N T1 T2.
Proof.
  intros. split.
  Case "->".
    generalize dependent N; generalize dependent P;
    generalize dependent T2;
    induction T1; intros T2 P N H; simpl in H.
    SCase "T1 = TVar n".
      destruct (eq_nat_dec N n); subst.
      SSCase "N = n".
        constructor.
      SSCase "N <> n".
        destruct (le_lt_dec N n); subst.
        SSSCase "N <= n".
          apply s_var_gt. unfold gt.
          apply le_lt_or_eq in l. inversion l; subst.
          assumption. apply ex_falso_quodlibet; apply n0; reflexivity.
        SSSCase "N > n".
          apply s_var_lt. assumption.
    SCase "T1 = TArrow T11 T12".
      rewrite <- H. constructor.
      apply IHT1_1. reflexivity.
      apply IHT1_2. reflexivity.
    SCase "T2 = TUniv T".
      rewrite <- H. constructor. apply IHT1. reflexivity.
  Case "<-".
    intro H. induction H; simpl;
    subst; try reflexivity; try assumption.
    destruct (eq_nat_dec I I); try reflexivity. apply ex_falso_quodlibet; auto.
    destruct (eq_nat_dec I N); try reflexivity. apply ex_falso_quodlibet; auto.
    subst; unfold lt in H; eapply le_Sn_n; apply H.
    destruct (le_lt_dec I N); try reflexivity.
    apply ex_falso_quodlibet. eapply lt_not_le. apply H; assumption. assumption.
    destruct (eq_nat_dec I N). apply ex_falso_quodlibet; subst. eapply gt_irrefl.
    apply H.
    destruct (le_lt_dec I N); try reflexivity. unfold gt in H.
    apply ex_falso_quodlibet. eapply lt_asym. apply H. trivial.
Qed.

(* Type in Term Substitution *)

Fixpoint subst_type_fix (X:nat) (T:ty) (t:tm) : tm :=
  match t with
  | tvar x =>
      tvar x
  | tabs T' t1 => 
      tabs ([X := T] T') (subst_type_fix X T t1) 
  | tapp t1 t2 => 
      tapp (subst_type_fix X T t1) (subst_type_fix X T t2)
  | ttabs t1 =>
      ttabs (subst_type_fix (X+1) (tshift 0 T) t1) 
  | ttapp t' T' =>
      ttapp (subst_type_fix X T t') ([X := T] T')
  end.

Instance subst_ty_tm : Subst nat ty tm := {
  do_subst := subst_type_fix
}.

Inductive subst_type (P:ty) (I:nat) : tm -> tm -> Prop := 
  | st_var : forall x,
      subst_type P I (tvar x) (tvar x)
  | st_tabs : forall T1 T2 t t',
      subst_type P I t t' ->
      subst_type_in_type P I T1 T2 ->
      subst_type P I (tabs T1 t) (tabs T2 t')
  | st_tapp : forall t1 t2 t1' t2',
      subst_type P I t1 t1' ->
      subst_type P I t2 t2' ->
      subst_type P I (tapp t1 t2) (tapp t1' t2')
  | st_ttabs : forall t t',
      subst_type (tshift 0 P) (I+1) t t' ->
      subst_type P I (ttabs t) (ttabs t')
  | st_ttapp : forall t t' T1 T2,
      subst_type P I t t' ->
      subst_type_in_type P I T1 T2 ->
      subst_type P I (ttapp t T1) (ttapp t' T2).

Hint Constructors subst_type.

Theorem subst_type_correct : forall P I t t',
  [I := P] t = t' <-> subst_type P I t t'.
Proof.
  intros. split.
  Case "->".
    generalize dependent I. generalize dependent P.
    generalize dependent t'.
    induction t; intros t' P I H; simpl in H.
    SCase "t = tvar i".
      rewrite <- H. constructor.
    SCase "t = tapp t1 t2".
      rewrite <- H. constructor.
      apply IHt1. reflexivity.
      apply IHt2. reflexivity.
    SCase "t = tabs i t t0".
      rewrite <- H. constructor.
      apply IHt. reflexivity.
      apply subst_type_in_type_correct. reflexivity.
    SCase "t = ttapp".
      subst. constructor. apply IHt. reflexivity.
      apply subst_type_in_type_correct. reflexivity.
    SCase "t = ttabs".
      subst. constructor. apply IHt. reflexivity.
  Case "<-".
    intro H. induction H; simpl;
    subst; try reflexivity; try assumption;
    apply subst_type_in_type_correct in H0;
    unfold do_subst in H0; unfold subst_ty_ty in H0;
    rewrite -> H0; reflexivity.    
Qed.

(** [] *)


(* ################################### *)
(** *** Reduction *)

(** The small-step reduction relation for STLC now follows the same
    pattern as the ones we have seen before.  Intuitively, to reduce a
    function application, we first reduce its left-hand side until it
    becomes a literal function; then we reduce its right-hand
    side (the argument) until it is also a value; and finally we
    substitute the argument for the bound variable in the body of the
    function.  This last rule, written informally as
      (\x:T.t12) v2 ==> [x:=v2]t12
    is traditionally called "beta-reduction". *)

(** 
                               value v2
                     ----------------------------                   (ST_AppAbs)
                     (\x:T.t12) v2 ==> [x:=v2]t12

                              t1 ==> t1'
                           ----------------                           (ST_App1)
                           t1 t2 ==> t1' t2

                              value v1
                              t2 ==> t2'
                           ----------------                           (ST_App2)
                           v1 t2 ==> v1 t2'
*)


Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | E_AppAbs : forall T t12 v2,
         value v2 ->
         (tapp (tabs T t12) v2) ==> [0:=v2]t12
  | E_App1 : forall t1 t1' t2,
         t1 ==> t1' ->
         tapp t1 t2 ==> tapp t1' t2
  | E_App2 : forall v1 t2 t2',
         value v1 ->
         t2 ==> t2' -> 
         tapp v1 t2 ==> tapp v1  t2'
  | E_TApp : forall t1 t1' T2,
         t1 ==> t1' ->
         ttapp t1 T2 ==> ttapp t1' T2
  | E_TAappTabs : forall t12 T2,
         ttapp (ttabs t12) T2 ==> [0:=T2] t12

where "t1 '==>' t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_AppAbs" | Case_aux c "E_App1" 
  | Case_aux c "E_App2" | Case_aux c "E_TApp" 
  | Case_aux c "E_TAppTabs" ].

Hint Constructors step.

Notation multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

(* ###################################################################### *)
(** ** Typing *)

(* ################################### *)
(** *** Contexts *)

(* Reimplementing this as in the DeBruijn Indices paper *)

Inductive context : Set :=
  | empty : context
  | ext_var : context -> ty -> context
  | ext_tvar : context -> context.

Definition opt_map {A B : Type} (f : A -> B) (x : option A) :=
  match x with
  | Some x => Some (f x)
  | None => None
  end.

Fixpoint get_var (E : context) (x : nat) : option ty :=
  match E with
    | empty => None
    | ext_var E' T =>
      match x with
        | O   => Some T
        | S y => get_var E' y
      end
    | ext_tvar E'  => opt_map (tshift 0) (get_var E' x)
  end.

Fixpoint get_tvar (E : context) (N : nat) : bool :=
  match E with
    | empty => false
    | ext_var E' _ => get_tvar E' N
    | ext_tvar E'  =>
      match N with
        | O => true
        | S N' => get_tvar E' N'
      end
  end.

(* Should maybe have some proofs *)

Fixpoint wf_ty (Gamma : context) (T : ty) : Prop :=
  match T with
  | TVar X       => get_tvar Gamma X = true
  | TArrow T1 T2 => wf_ty Gamma T1 /\ wf_ty Gamma T2
  | TUniv  T     => wf_ty (ext_tvar Gamma) T
  end.

Inductive well_formed_type (Gamma : context) : ty -> Prop :=
  | WF_TVar : forall X,
      get_tvar Gamma X = true ->
      well_formed_type Gamma (TVar X)
  | WF_TArrow : forall T1 T2,
      well_formed_type Gamma T1 ->
      well_formed_type Gamma T2 ->
      well_formed_type Gamma (TArrow T1 T2)
  | WF_TUniv : forall T,
      well_formed_type (ext_tvar Gamma) T ->
      well_formed_type Gamma (TUniv T).

Lemma wf_type_correct : forall Gamma T,
  well_formed_type Gamma T <-> wf_ty Gamma T.
Proof.
  split; intros.
  Case "->".
    induction H; try split; trivial.
  Case "<-".
    generalize dependent Gamma. induction T.
    constructor. simpl in H. trivial.
    constructor; simpl in H; inversion H. apply IHT1. trivial.
      apply IHT2. trivial.
    constructor. simpl in H. apply IHT. trivial.
Qed.


Inductive well_formed_context : context -> Prop :=
  | WFC_empty :
      well_formed_context empty
  | WFC_ext_var : forall T Gamma,
      well_formed_type Gamma T ->
      well_formed_context Gamma ->
      well_formed_context (ext_var Gamma T)
  | WFC_ext_tvar : forall Gamma,
      well_formed_context Gamma ->
      well_formed_context (ext_tvar Gamma).


(* Context Substitution *)
(* Fixpoint subst_context_fix (n:nat) (T':ty) (Gamma:context) : context := *)
(*   match Gamma with *)
(*     | empty => empty *)
(*     | ext_var Gamma' x T => ext_var (subst_context_fix n T' Gamma') x ([n:=T']T) *)
(*     | ext_tvar Gamma' => *)
(*       match n with *)
(*         | S n' => ext_tvar (subst_context_fix n' (tunshift 0 T') Gamma') *)
(*         | 0    => Gamma' *)
(*       end *)
(*   end. *)

(* Instance subst_ctx : Subst nat ty context := { *)
(*   do_subst := subst_context_fix *)
(* }. *)

Inductive subst_context : ty -> nat -> context -> context -> Prop := 
  (* | s_empty : forall T n, *)
  (*     subst_context T n empty empty *)
  | s_ext_var : forall T n Gamma Gamma' U U',
      subst_context T n Gamma Gamma' ->
      subst_type_in_type T n U U' ->
      subst_context T n (ext_var Gamma U) (ext_var Gamma' U')
  | s_ext_tvar0 : forall T Gamma,
      (* the variable is removed because it has been replaced *)
      well_formed_type Gamma T  ->
      well_formed_context Gamma ->
      subst_context T 0 (ext_tvar Gamma) Gamma
  | s_ext_tvar : forall T n Gamma Gamma',
      subst_context T n Gamma Gamma' ->
      subst_context (tshift 0 T) (S n) (ext_tvar Gamma) (ext_tvar Gamma').

Hint Constructors subst_context.


(* Theorem subst_context_correct : forall T n Gamma Gamma', *)
(*   [n := T] Gamma = Gamma' <-> subst_context T n Gamma Gamma'. *)
(* Proof with auto. *)
(*   intros; split. *)
(*   Case "->". *)
(*     generalize dependent Gamma'. generalize dependent n. *)
(*     generalize dependent T. induction Gamma; intros; rewrite <- H... *)
(*     SCase "Gamma = ext_var Gamma i t". *)
(*       constructor. apply IHGamma. reflexivity. *)
(*       apply subst_type_in_type_correct. trivial. *)
(*     SCase "Gamma = ext_tvar Gamma". *)
(*       destruct n. *)
(*       SSCase "n = 0". *)
(*         simpl... *)
(*       SSCase "n = S n'". *)
(*         simpl. constructor. apply IHGamma. reflexivity. *)
(*   Case "<-". *)
(*     intro H. induction H; simpl; *)
(*     subst; try reflexivity; try assumption. *)
(*     apply subst_type_in_type_correct in H0. subst... *)
(* Qed. *)

(** [] *)


(* ################################### *)
(** *** Typing Relation *)

(** 
                             Gamma x = T
                            --------------                              (T_Var)
                            Gamma |- x \in T

                      Gamma , x:T11 |- t12 \in T12
                     ----------------------------                       (T_Abs)
                     Gamma |- \x:T11.t12 \in T11->T12

                        Gamma |- t1 \in T11->T12
                          Gamma |- t2 \in T11
                        ----------------------                          (T_App)
                         Gamma |- t1 t2 \in T12

                         --------------------                          (T_True)
                         Gamma |- true \in Bool

                        ---------------------                         (T_False)
                        Gamma |- false \in Bool

       Gamma |- t1 \in Bool    Gamma |- t2 \in T    Gamma |- t3 \in T
       --------------------------------------------------------          (T_If)
                  Gamma |- if t1 then t2 else t3 \in T


    We can read the three-place relation [Gamma |- t \in T] as: 
    "to the term [t] we can assign the type [T] using as types for
    the free variables of [t] the ones specified in the context 
    [Gamma]." *)


Reserved Notation "Gamma '|-' t '\in' T" (at level 40).
    
Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      well_formed_context Gamma ->
      get_var Gamma x = Some T ->
      Gamma |- tvar x \in T
  | T_Abs : forall Gamma T11 T12 t12,
      ext_var Gamma T11 |- t12 \in T12 -> 
      Gamma |- tabs T11 t12 \in TArrow T11 T12
  | T_App : forall T11 T12 Gamma t1 t2,
      Gamma |- t1 \in TArrow T11 T12 -> 
      Gamma |- t2 \in T11 -> 
      Gamma |- tapp t1 t2 \in T12
  | T_TAbs : forall Gamma t T,
      ext_tvar Gamma |- t \in T ->
      Gamma |- ttabs t \in (TUniv T)
  | T_TApp : forall Gamma t1 T12 T2,
      Gamma |- t1 \in (TUniv T12) ->
      Gamma |- ttapp t1 T2 \in [0 := T2] T12
      
where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var" | Case_aux c "T_Abs" 
  | Case_aux c "T_App" | Case_aux c "T_TAbs" 
  | Case_aux c "T_TApp" ].

Hint Constructors has_type.

(* ################################### *)
(** *** Examples *)

Lemma type_unique : (forall S T, ~ (S = (TArrow S T))).
  induction S; intros T contra; inversion contra; clear contra.
  apply (IHS1 S2). assumption.
Qed.  


End SYSTEMF.

