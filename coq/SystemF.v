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
  | TUniv  : forall (X : ty),ty.

(* ################################### *)
(** *** Terms *)

Inductive tm : Type :=
  | tvar  : id -> tm
  | tapp  : tm -> tm -> tm
  | tabs  : id -> ty -> tm -> tm
  | ttapp : tm -> ty -> tm
  | ttabs : tm -> tm.

Tactic Notation "t_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tvar" | Case_aux c "tapp" 
  | Case_aux c "tabs" | Case_aux c "ttapp" 
  | Case_aux c "ttabs" ].

(** Note that an abstraction [\x:T.t] (formally, [tabs x T t]) is
    always annotated with the type [T] of its parameter, in contrast
    to Coq (and other functional languages like ML, Haskell, etc.),
    which use _type inference_ to fill in missing annotations.  We're
    not considering type inference here, to keep things simple. *)

(** Some examples... *)

Definition x := (Id 0).
Definition y := (Id 1).
Definition z := (Id 2).
Hint Unfold x.
Hint Unfold y.
Hint Unfold z.


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
  | v_abs : forall x T t,
      value (tabs x T t)
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
Fixpoint subst_term_fix (x:id) (s:tm) (t:tm) : tm :=
  match t with
  | tvar x' => 
      if eq_id_dec x x' then s else t
  | tabs x' T t1 => 
      tabs x' T (if eq_id_dec x x' then t1 else subst_term_fix x s t1) 
  | tapp t1 t2 => 
      tapp (subst_term_fix x s t1) (subst_term_fix x s t2)
  | ttabs t =>
      ttabs (subst_term_fix x s t)
  | ttapp t T =>
      ttapp (subst_term_fix x s t) T
  end.

Instance subst_tm_tm : Subst id tm tm := {
  do_subst := subst_term_fix
}.


Inductive subst_term (s:tm) (x:id) : tm -> tm -> Prop := 
  | s_var1 :
      subst_term s x (tvar x) s
  | s_var2 : forall x',
      x <> x' ->
      subst_term s x (tvar x') (tvar x')
  | s_tabs1 : forall T t,
      subst_term s x (tabs x T t) (tabs x T t)
  | s_tabs2 : forall x' T t t',
      x <> x' ->
      subst_term s x t t' ->
      subst_term s x (tabs x' T t) (tabs x' T t')
  | s_tapp : forall t1 t2 t1' t2',
      subst_term s x t1 t1' ->
      subst_term s x t2 t2' ->
      subst_term s x (tapp t1 t2) (tapp t1' t2')
  | s_ttabs : forall t t',
      subst_term s x t t' ->
      subst_term s x (ttabs t) (ttabs t')
  | s_ttapp : forall t t' T,
      subst_term s x t t' ->
      subst_term s x (ttapp t T) (ttapp t' T).

Hint Constructors subst_term.

Theorem subst_term_correct : forall s x t t',
  [x:=s]t = t' <-> subst_term s x t t'.
Proof.
  intros s x t. split.
  Case "->".
    generalize dependent t'. induction t; intros t' H; simpl in H.
    SCase "t = tvar i".
      destruct (eq_id_dec x i) in H; subst.
      SSCase "x = i".
        constructor.
      SSCase "x <> i".
        constructor. assumption.
    SCase "t = tapp t1 t2".
      rewrite <- H. constructor.
      apply IHt1. reflexivity.
      apply IHt2. reflexivity.
    SCase "t = tabs i t t0".
      destruct (eq_id_dec x i) in H; subst.
      SSCase "x = i".
        constructor.
      SSCase "x <> i".
        constructor. assumption.
        apply IHt. reflexivity.
    SCase "t = ttapp".
      subst. constructor. apply IHt. reflexivity.
    SCase "t = ttabs".
      subst. constructor. apply IHt. reflexivity.
  Case "<-".
    intro H. induction H; simpl;
    try (rewrite -> eq_id); try (rewrite -> neq_id);
    subst; try reflexivity; try assumption.
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
  | TUniv T' => TUniv (subst_type_in_type_fix (I + 1) P T')
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
  | u_univ : forall T1 T2,
      subst_type_in_type T (I+1) T1 T2 ->
      subst_type_in_type T I (TUniv T1) (TUniv T2).

Lemma subst_type_in_type_correct : forall N P T1 T2,
  [N:=P]T1 = T2 <-> subst_type_in_type P N T1 T2.
Proof.
  intros. split.
  Case "->".
    generalize dependent N; generalize dependent T2;
    induction T1; intros T2 N H; simpl in H.
    SCase "T1 = TVar n". SearchAbout eq_nat.
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
    SCase "T2 = TUniv T1".
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
    apply ex_falso_quodlibet. eapply lt_asym. apply H. assumption.
Qed.

(* Type in Term Substitution *)

Fixpoint subst_type_fix (X:nat) (T:ty) (t:tm) : tm :=
  match t with
  | tvar x =>
      tvar x
  | tabs x T' t1 => 
      tabs x ([X := T'] T) (subst_type_fix X T t1) 
  | tapp t1 t2 => 
      tapp (subst_type_fix X T t1) (subst_type_fix X T t2)
  | ttabs t1 =>
      ttabs (subst_type_fix (X+1) T t1) 
  | ttapp t' T' =>
      ttapp (subst_type_fix X T t') ([X := T'] T)
  end.

Instance subst_ty_tm : Subst nat ty tm := {
  do_subst := subst_type_fix
}.

Inductive subst_type (T:ty) (X:nat) : tm -> tm -> Prop := 
  | st_var : forall x,
      subst_type T X (tvar x) (tvar x)
  | st_tabs : forall T1 T2 x t t',
      subst_type T X t t' ->
      subst_type_in_type T X T1 T2 ->
      subst_type T X (tabs x T1 t) (tabs x T2 t')
  | st_tapp : forall t1 t2 t1' t2',
      subst_type T X t1 t1' ->
      subst_type T X t2 t2' ->
      subst_type T X (tapp t1 t2) (tapp t1' t2')
  | st_ttabs : forall t t',
      subst_type T (X+1) t t' ->
      subst_type T X (ttabs t) (ttabs t')
  | st_ttapp : forall t t' T1 T2,
      subst_type T X t t' ->
      subst_type_in_type T X T1 T2 ->
      subst_type T X (ttapp t T1) (ttapp t' T2).

Hint Constructors subst_type.

Theorem subst_type_correct : forall T X t t',
  [X := T] t = t' <-> subst_type T X t t'.
Proof.
  intros. split.
  Case "->".
    generalize dependent X. generalize dependent t'.
    induction t; intros t' X H; simpl in H.
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
  | E_AppAbs : forall x T t12 v2,
         value v2 ->
         (tapp (tabs x T t12) v2) ==> [x:=v2]t12
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

(** _Question_: What is the type of the term "[x y]"?

    _Answer_: It depends on the types of [x] and [y]!  

    I.e., in order to assign a type to a term, we need to know
    what assumptions we should make about the types of its free
    variables.

    This leads us to a three-place "typing judgment", informally
    written [Gamma |- t : T], where [Gamma] is a
    "typing context" -- a mapping from variables to their types. *)

(** We hide the definition of partial maps in a module since it is
    actually defined in [SfLib]. *)

Module PartialMap.

Inductive label := tm_var : id -> label
                 | ty_var : id -> label.

Definition partial_map (A:Type) := label -> option A.

Definition empty {A:Type} : partial_map A := (fun _ => None). 

(** Informally, we'll write [Gamma, x:T] for "extend the partial
    function [Gamma] to also map [x] to [T]."  Formally, we use the
    function [extend] to add a binding to a partial map. *)

Theorem eq_label_dec : forall l1 l2 : label, {l1 = l2} + {l1 <> l2}.
Proof.
   intros.
   destruct l1; destruct l2.
   Case "l1 is term, l2 is term".
     destruct (eq_id_dec i i0).
     SCase "i = i0".
       subst. left. reflexivity. 
     SCase "i <> i0".
       right. unfold not. unfold not in n.
       intros H. apply n. inversion H. reflexivity.
   Case "l1 is term, l2 is type".
     right. unfold not. intros H. inversion H.
   Case "l1 is type, l2 is term".
     right. unfold not. intros H. inversion H.     
   Case "l1 is type, l2 is type".
     destruct (eq_id_dec i i0).
     SCase "i = i0".
       subst. left. reflexivity. 
     SCase "i <> i0".
       right. unfold not. unfold not in n.
       intros H. apply n. inversion H. reflexivity.
Qed.

Definition eq_label_refl := fun (T:Type) (l:label) (p q : T) =>
  let s := eq_label_dec l l in
  match s as s0 return ((if s0 then p else q) = p) with
  | left _ => eq_refl
  | right n => ex_falso_quodlibet (q = p) (n eq_refl)
  end.

Lemma neq_label_refl : forall (T:Type) (l1 l2 : label) (p q : T),
  l1 <> l2 -> (if eq_label_dec l1 l2 then p else q) = q.
Proof.
  intros. destruct (eq_label_dec l1 l2).
  Case "l1 = l2".  
    unfold not in H. apply ex_falso_quodlibet. apply H. assumption.
  Case "l1 <> l2".
    reflexivity.
Qed.

Definition extend {A:Type} (Gamma : partial_map A) (x:label) (T : A) :=
  fun x' => if eq_label_dec x x' then Some T else Gamma x'.

Lemma extend_eq : forall A (ctxt: partial_map A) x T,
  (extend ctxt x T) x = Some T.
Proof.
  intros. unfold extend. rewrite eq_label_refl. auto.
Qed.

Lemma extend_neq : forall A (ctxt: partial_map A) x1 T x2,
  x1 <> x2 ->
  (extend ctxt x2 T) x1 = ctxt x1.
Proof.
  intros. unfold extend. apply neq_label_refl; auto.
Qed.

End PartialMap.

Definition context := partial_map ty.

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
      Gamma x = Some T ->
      Gamma |- tvar x \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      extend Gamma x T11 |- t12 \in T12 -> 
      Gamma |- tabs x T11 t12 \in TArrow T11 T12
  | T_App : forall T11 T12 Gamma t1 t2,
      Gamma |- t1 \in TArrow T11 T12 -> 
      Gamma |- t2 \in T11 -> 
      Gamma |- tapp t1 t2 \in T12
  | T_TAbs : forall Gamma T t2 T2,
      extend Gamma X T |- t2 \in T2 ->
      Gamma |- ttabs t2 \in (TUniv T2)
  | T_TApp : forall Gamma X t1 T12 T2,
      Gamma |- t1 \in (TUniv T12) ->
      Gamma |- ttapp t1 T2 \in subst_type_in_type_fix X T12 T2
      
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

Example typing_nonexample :
  ~ (exists S, exists T,
        empty |- 
          (tabs x S
             (tapp (tvar x) (tvar x))) \in
          T).
Proof.
  intros H.
  inversion H. clear H.
  inversion H0. clear H0.
  inversion H; subst. clear H.
  inversion H5; subst. clear H5.
  inversion H4; subst. clear H4.
  inversion H2; subst. clear H2.
  rewrite H3 in H1. inversion H1. 
  apply (type_unique T11 T12). symmetry. assumption.
Qed.  

(** [] *)


End SYSTEMF.

