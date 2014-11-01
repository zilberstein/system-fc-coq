(** * System F **)

Require Export Types.


(* ###################################################################### *)
(** ** Syntax *)

Module SystemF.

(* ################################### *)
(** *** Types *)

Inductive ty : Type := 
  | TVar   : id -> ty 
  | TArrow : ty -> ty -> ty
  | TUniv  : forall (X : ty),ty.

(* ################################### *)
(** *** Terms *)

Inductive tm : Type :=
  | tvar  : id -> tm
  | tapp  : tm -> tm -> tm
  | tabs  : id -> ty -> tm -> tm
  | ttapp : tm -> ty -> tm
  | ttabs : id -> tm -> tm.

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
  | v_tabs : forall X t,
      value (ttabs X t).

Hint Constructors value.


(* ###################################################################### *)
(** *** Free Variables and Substitution *)

(* Term Sustitution *)

Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst_term_fix (x:id) (s:tm) (t:tm) : tm :=
  match t with
  | tvar x' => 
      if eq_id_dec x x' then s else t
  | tabs x' T t1 => 
      tabs x' T (if eq_id_dec x x' then t1 else ([x:=s] t1)) 
  | tapp t1 t2 => 
      tapp ([x:=s] t1) ([x:=s] t2)
  | ttabs X t =>
      ttabs X ([x:=s] t)
  | ttapp t T =>
      ttapp ([x:=s] t) T      
  end

where "'[' x ':=' s ']' t" := (subst_term_fix x s t).

(** _Technical note_: Substitution becomes trickier to define if we
    consider the case where [s], the term being substituted for a
    variable in some other term, may itself contain free variables.
    Since we are only interested here in defining the [step] relation
    on closed terms (i.e., terms like [\x:Bool. x], that do not mention
    variables are not bound by some enclosing lambda), we can skip
    this extra complexity here, but it must be dealt with when
    formalizing richer languages. *)

(** *** *)
(** **** Exercise: 3 stars (substi) *)  

(** The definition that we gave above uses Coq's [Fixpoint] facility
    to define substitution as a _function_.  Suppose, instead, we
    wanted to define substitution as an inductive _relation_ [substi].
    We've begun the definition by providing the [Inductive] header and
    one of the constructors; your job is to fill in the rest of the
    constructors. *)

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
  | s_ttabs : forall t t' X,
      subst_term s x t t' ->
      subst_term s x (ttabs X t) (ttabs X t')
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


(* Type Sustitution *)

Fixpoint subst_type_in_type_fix (X:id) (T:ty) (T':ty) : ty :=
  match T with
  | TVar X' =>
      if eq_id_dec X X' then T' else T
  | TArrow T1 T2 =>
      TArrow (subst_type_in_type_fix X T1 T') (subst_type_in_type_fix X T2 T')
  | TUniv T1 => TUniv (subst_type_in_type_fix X T1 T')
  end.

Reserved Notation "'[' X '|=' s ']' t" (at level 20).

Fixpoint subst_type_fix (X:id) (T:ty) (t:tm) : tm :=
  match t with
  | tvar x =>
      tvar x
  | tabs x T' t1 => 
      tabs x (subst_type_in_type_fix X T' T) ([X|=T] t1) 
  | tapp t1 t2 => 
      tapp ([X|=T] t1) ([X|=T] t2)
  | ttabs X' t1 =>
      ttabs X' (if eq_id_dec X X' then t1 else ([X|=T] t1)) 
  | ttapp t' T' =>
      ttapp ([X|=T] t') (subst_type_in_type_fix X T' T)
  end

where "'[' x '|=' s ']' t" := (subst_type_fix x s t).

(** _Technical note_: Substitution becomes trickier to define if we
    consider the case where [s], the term being substituted for a
    variable in some other term, may itself contain free variables.
    Since we are only interested here in defining the [step] relation
    on closed terms (i.e., terms like [\x:Bool. x], that do not mention
    variables are not bound by some enclosing lambda), we can skip
    this extra complexity here, but it must be dealt with when
    formalizing richer languages. *)

(** *** *)
(** **** Exercise: 3 stars (substi) *)  

(** The definition that we gave above uses Coq's [Fixpoint] facility
    to define substitution as a _function_.  Suppose, instead, we
    wanted to define substitution as an inductive _relation_ [substi].
    We've begun the definition by providing the [Inductive] header and
    one of the constructors; your job is to fill in the rest of the
    constructors. *)

Inductive subst_type_in_type (T:ty) (X:id) : ty -> ty -> Prop :=
  | s_var_eq :
      subst_type_in_type T X (TVar X) T
  | s_var_neq : forall X',
      X <> X' ->
      subst_type_in_type T X (TVar X') (TVar X')
  | s_arrow : forall T1 T2 T1' T2',
      subst_type_in_type T X T1 T1' ->
      subst_type_in_type T X T2 T2' ->
      subst_type_in_type T X (TArrow T1 T2) (TArrow T1' T2')
  | u_univ : forall T1 T2,
      subst_type_in_type T X T1 T2 ->
      subst_type_in_type T X (TUniv T1) (TUniv T2).

Lemma subst_type_in_type_correct : forall T X T1 T2,
  subst_type_in_type_fix X T1 T = T2 <-> subst_type_in_type T X T1 T2.
Proof.
  intros. split.
  Case "->".
    generalize dependent T2; induction T1; intros T2 H; simpl in H.
    SCase "T1 = TVar i".
      destruct (eq_id_dec X i) in H; subst.
      SSCase "X = i".
        constructor.
      SSCase "X <> i".
        constructor. assumption.
    SCase "T1 = TArrow T11 T12".
      rewrite <- H. constructor.
      apply IHT1_1. reflexivity.
      apply IHT1_2. reflexivity.
    SCase "T2 = TUniv T1".
      rewrite <- H. constructor.
      apply IHT1. reflexivity.
  Case "<-".
    intro H. induction H; simpl;
    try (rewrite -> eq_id); try (rewrite -> neq_id);
    subst; try reflexivity; try assumption.
Qed.

Inductive subst_type (T:ty) (X:id) : tm -> tm -> Prop := 
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
  | st_ttabs_eq : forall t,
      subst_type T X (ttabs X t) (ttabs X t)
  | st_ttabs_neq : forall t t' X',
      X <> X' ->
      subst_type T X t t' ->
      subst_type T X (ttabs X' t) (ttabs X' t')
  | st_ttapp : forall t t' T1 T2,
      subst_type T X t t' ->
      subst_type_in_type T X T1 T2 ->
      subst_type T X (ttapp t T1) (ttapp t' T2).

Hint Constructors subst_type.

Theorem subst_type_correct : forall T X t t',
  [X|=T]t = t' <-> subst_type T X t t'.
Proof.
  intros. split.
  Case "->".
    generalize dependent t'. induction t; intros t' H; simpl in H.
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
      subst. destruct (eq_id_dec X i).
      SSCase "X = i".
        subst. constructor.
      SSCase "X <> i".
        constructor. assumption. apply IHt. reflexivity.
  Case "<-".
    intro H. induction H; simpl;
    try (rewrite -> eq_id); try (rewrite -> neq_id);
    subst; try reflexivity; try assumption;
    apply subst_type_in_type_correct in H0; rewrite H0; reflexivity.    
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
  | E_TAappTabs : forall X t12 T2,
         ttapp (ttabs X t12) T2 ==> [X|=T2] t12

where "t1 '==>' t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_AppAbs" | Case_aux c "E_App1" 
  | Case_aux c "E_App2" | Case_aux c "E_TApp" 
  | Case_aux c "E_TAppTabs" ].

Hint Constructors step.

Notation multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

(* ##################################### *)
(** *** Examples *)

(** Example:
    ((\x:Bool->Bool. x) (\x:Bool. x)) ==>* (\x:Bool. x)
i.e.
    (idBB idB) ==>* idB
*)

Lemma step_example1 :
  (tapp idBB idB) ==>* idB.
Proof.
  eapply multi_step.
    apply ST_AppAbs.
    apply v_abs.
  simpl.
  apply multi_refl.  Qed.  

(** Example:
((\x:Bool->Bool. x) ((\x:Bool->Bool. x) (\x:Bool. x))) 
      ==>* (\x:Bool. x)
i.e.
  (idBB (idBB idB)) ==>* idB.
*)

Lemma step_example2 :
  (tapp idBB (tapp idBB idB)) ==>* idB.
Proof.
  eapply multi_step.
    apply ST_App2. auto.
    apply ST_AppAbs. auto.
  eapply multi_step.
    apply ST_AppAbs. simpl. auto.
  simpl. apply multi_refl.  Qed. 

(** Example:
((\x:Bool->Bool. x) (\x:Bool. if x then false
                              else true)) true)
      ==>* false
i.e.
  ((idBB notB) ttrue) ==>* tfalse.
*)

Lemma step_example3 :
  tapp (tapp idBB notB) ttrue ==>* tfalse.
Proof. 
  eapply multi_step.
    apply ST_App1. apply ST_AppAbs. auto. simpl.
  eapply multi_step.
    apply ST_AppAbs. auto. simpl.
  eapply multi_step.
    apply ST_IfTrue. apply multi_refl.  Qed. 

(** Example:
((\x:Bool->Bool. x) ((\x:Bool. if x then false
                               else true) true))
      ==>* false
i.e.
  (idBB (notB ttrue)) ==>* tfalse.
*)

Lemma step_example4 :
  tapp idBB (tapp notB ttrue) ==>* tfalse.
Proof. 
  eapply multi_step.
    apply ST_App2. auto. 
    apply ST_AppAbs. auto. simpl.
  eapply multi_step.
    apply ST_App2. auto. 
    apply ST_IfTrue. 
  eapply multi_step.
    apply ST_AppAbs. auto. simpl.
  apply multi_refl.  Qed. 


(** A more automatic proof *)

Lemma step_example1' :
  (tapp idBB idB) ==>* idB.
Proof. normalize.  Qed.  

(** Again, we can use the [normalize] tactic from above to simplify
    the proof. *)

Lemma step_example2' :
  (tapp idBB (tapp idBB idB)) ==>* idB.
Proof.
  normalize.
Qed. 

Lemma step_example3' :
  tapp (tapp idBB notB) ttrue ==>* tfalse.
Proof. normalize.  Qed.  

Lemma step_example4' :
  tapp idBB (tapp notB ttrue) ==>* tfalse.
Proof. normalize.  Qed.  

(** **** Exercise: 2 stars (step_example3) *)  
(** Try to do this one both with and without [normalize]. *)

Lemma step_example5 :
       (tapp (tapp idBBBB idBB) idB)
  ==>* idB.
Proof.
  (* FILL IN HERE *) Admitted.

(* FILL IN HERE *)
(** [] *)

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

Definition partial_map (A:Type) := id -> option A.

Definition empty {A:Type} : partial_map A := (fun _ => None). 

(** Informally, we'll write [Gamma, x:T] for "extend the partial
    function [Gamma] to also map [x] to [T]."  Formally, we use the
    function [extend] to add a binding to a partial map. *)

Definition extend {A:Type} (Gamma : partial_map A) (x:id) (T : A) :=
  fun x' => if beq_id x x' then Some T else Gamma x'.

Lemma extend_eq : forall A (ctxt: partial_map A) x T,
  (extend ctxt x T) x = Some T.
Proof.
  intros. unfold extend. rewrite <- beq_id_refl. auto.
Qed.

Lemma extend_neq : forall A (ctxt: partial_map A) x1 T x2,
  beq_id x2 x1 = false ->
  (extend ctxt x2 T) x1 = ctxt x1.
Proof.
  intros. unfold extend. rewrite H. auto.
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
  | T_True : forall Gamma,
       Gamma |- ttrue \in TBool
  | T_False : forall Gamma,
       Gamma |- tfalse \in TBool
  | T_If : forall t1 t2 t3 T Gamma,
       Gamma |- t1 \in TBool ->
       Gamma |- t2 \in T ->
       Gamma |- t3 \in T ->
       Gamma |- tif t1 t2 t3 \in T

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var" | Case_aux c "T_Abs" 
  | Case_aux c "T_App" | Case_aux c "T_True" 
  | Case_aux c "T_False" | Case_aux c "T_If" ].

Hint Constructors has_type.

(* ################################### *)
(** *** Examples *)

Example typing_example_1 :
  empty |- tabs x TBool (tvar x) \in TArrow TBool TBool.
Proof.
  apply T_Abs. apply T_Var. reflexivity.  Qed.

(** Note that since we added the [has_type] constructors to the hints
    database, auto can actually solve this one immediately. *)

Example typing_example_1' :
  empty |- tabs x TBool (tvar x) \in TArrow TBool TBool.
Proof. auto.  Qed.

(** Another example:
     empty |- \x:A. \y:A->A. y (y x)) 
           \in A -> (A->A) -> A.
*)

Example typing_example_2 :
  empty |-
    (tabs x TBool
       (tabs y (TArrow TBool TBool)
          (tapp (tvar y) (tapp (tvar y) (tvar x))))) \in
    (TArrow TBool (TArrow (TArrow TBool TBool) TBool)).
Proof with auto using extend_eq.
  apply T_Abs.
  apply T_Abs.
  eapply T_App. apply T_Var...
  eapply T_App. apply T_Var...
  apply T_Var...
Qed.

(** **** Exercise: 2 stars, optional (typing_example_2_full) *)
(** Prove the same result without using [auto], [eauto], or
    [eapply]. *)

Example typing_example_2_full :
  empty |-
    (tabs x TBool
       (tabs y (TArrow TBool TBool)
          (tapp (tvar y) (tapp (tvar y) (tvar x))))) \in
    (TArrow TBool (TArrow (TArrow TBool TBool) TBool)).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars (typing_example_3) *)
(** Formally prove the following typing derivation holds: *)
(** 
   empty |- \x:Bool->B. \y:Bool->Bool. \z:Bool.
               y (x z) 
         \in T.
*)

Example typing_example_3 :
  exists T, 
    empty |-
      (tabs x (TArrow TBool TBool)
         (tabs y (TArrow TBool TBool)
            (tabs z TBool
               (tapp (tvar y) (tapp (tvar x) (tvar z)))))) \in
      T.
Proof with auto.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** We can also show that terms are _not_ typable.  For example, let's
    formally check that there is no typing derivation assigning a type
    to the term [\x:Bool. \y:Bool, x y] -- i.e.,
    ~ exists T,
        empty |- \x:Bool. \y:Bool, x y : T.
*)

Example typing_nonexample_1 :
  ~ exists T,
      empty |- 
        (tabs x TBool
            (tabs y TBool
               (tapp (tvar x) (tvar y)))) \in
        T.
Proof.
  intros Hc. inversion Hc.
  (* The [clear] tactic is useful here for tidying away bits of
     the context that we're not going to need again. *)
  inversion H. subst. clear H.
  inversion H5. subst. clear H5.
  inversion H4. subst. clear H4.
  inversion H2. subst. clear H2.
  inversion H5. subst. clear H5.
  (* rewrite extend_neq in H1. rewrite extend_eq in H1. *)
  inversion H1.  Qed.

(** **** Exercise: 3 stars, optional (typing_nonexample_3) *)
(** Another nonexample:
    ~ (exists S, exists T,
          empty |- \x:S. x x : T).
*)

Example typing_nonexample_3 :
  ~ (exists S, exists T,
        empty |- 
          (tabs x S
             (tapp (tvar x) (tvar x))) \in
          T).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)




End SystemF.

