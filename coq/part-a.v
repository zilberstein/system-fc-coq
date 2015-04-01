(* PoplMark Challenge, parts 1a and 2a
   By Jerome Vouillon
   March-May 2005

   The proofs are written in Coq using de Bruijn indices.
   The whole development took about twelve days.
*)

Set Implicit Arguments.
Unset Strict Implicit.

Require Import Arith.
Require Import Omega.


(*************************************************************************)
(*                          Definition of Fsub                           *)
(*************************************************************************)


(*** Standard de Bruijn presentation of Fsub types and terms ***)

Inductive typ : Set :=
  | tvar : nat -> typ
  | top : typ
  | arrow : typ -> typ -> typ
  | all : typ -> typ -> typ.

Inductive term : Set :=
  | var : nat -> term
  | abs : typ -> term -> term
  | app : term -> term -> term
  | tabs : typ -> term -> term
  | tapp : term -> typ -> term.

(****)

(*** Shiftings and substitutions ***)

Fixpoint tshift (X : nat) (T : typ) {struct T} : typ :=
  match T with
  | tvar Y      => tvar (if le_gt_dec X Y then 1 + Y else Y)
  | top         => top
  | arrow T1 T2 => arrow (tshift X T1) (tshift X T2)
  | all T1 T2   => all (tshift X T1) (tshift (1 + X) T2)
  end.

Fixpoint shift (x : nat) (t : term) {struct t} : term :=
  match t with
  | var y      => var (if le_gt_dec x y then 1 + y else y)
  | abs T1 t2  => abs T1 (shift (1 + x) t2)
  | app t1 t2  => app (shift x t1) (shift x t2)
  | tabs T1 t2 => tabs T1 (shift x t2)
  | tapp t1 T2 => tapp (shift x t1) T2
  end.

Fixpoint shift_typ (X : nat) (t : term) {struct t} : term :=
  match t with
  | var y      => var y
  | abs T1 t2  => abs (tshift X T1) (shift_typ X t2)
  | app t1 t2  => app (shift_typ X t1) (shift_typ X t2)
  | tabs T1 t2 => tabs (tshift X T1) (shift_typ (1 + X) t2)
  | tapp t1 T2 => tapp (shift_typ X t1) (tshift X T2)
  end.

Fixpoint tsubst (T : typ) (X : nat) (T' : typ) {struct T} : typ :=
  match T with
  | tvar Y =>
      match lt_eq_lt_dec Y X with
      | inleft (left _)  => tvar Y
      | inleft (right _) => T'
      | inright _        => tvar (Y - 1)
      end
  | top         => top
  | arrow T1 T2 => arrow (tsubst T1 X T') (tsubst T2 X T')
  | all T1 T2   => all (tsubst T1 X T') (tsubst T2 (1 + X) (tshift 0 T'))
  end.

Fixpoint subst (t : term) (x : nat) (t' : term) {struct t} : term :=
  match t with
  | var y =>
      match lt_eq_lt_dec y x with
      | inleft (left _)  => var y
      | inleft (right _) => t'
      | inright _        => var (y - 1)
      end
  | abs T1 t2  => abs T1 (subst t2 (1 + x) (shift 0 t'))
  | app t1 t2  => app (subst t1 x t') (subst t2 x t')
  | tabs T1 t2 => tabs T1 (subst t2 x (shift_typ 0 t'))
  | tapp t1 T2 => tapp (subst t1 x t') T2
  end.

Fixpoint subst_typ (t : term) (X : nat) (T : typ) {struct t} : term :=
  match t with
  | var y      => var y
  | abs T1 t2  => abs (tsubst T1 X T) (subst_typ t2 X T)
  | app e1 e2  => app (subst_typ e1 X T) (subst_typ e2 X T)
  | tabs T1 e1 => tabs (tsubst T1 X T) (subst_typ e1 (1 + X) (tshift 0 T))
  | tapp e1 T2 => tapp (subst_typ e1 X T) (tsubst T2 X T)
  end.

(****)

(*** Contexts ***)

(* We define the contexts [env] and the two functions [get_bound] and
   [get_var] which access the context. *)

Inductive env : Set :=
  | empty : env
  | evar : env -> typ -> env
  | ebound : env -> typ -> env.

Definition opt_map (A B : Set) (f : A -> B) (x : option A) :=
  match x with
  | Some x => Some (f x)
  | None => None
  end.

Fixpoint get_bound (e : env) (X : nat) {struct e} : option typ :=
  match e with
    empty     => None
  | evar e' _ => get_bound e' X
  | ebound e' T =>
      opt_map (tshift 0)
        (match X with
         | O    => Some T
         | S X' => get_bound e' X'
         end)
  end.

Fixpoint get_var (e : env) (x : nat) {struct e} : option typ :=
  match e with
    empty       => None
  | ebound e' _ => opt_map (tshift 0) (get_var e' x)
  | evar e' T =>
      match x with
      | O    => Some T
      | S x' => get_var e' x'
      end
  end.

(****)

(*** Well-formedness conditions ***)

(* The variables must all be bound *)

Fixpoint wf_typ (e : env) (T : typ) {struct T} : Prop :=
  match T with
  | tvar X      => get_bound e X <> None
  | top         => True
  | arrow T1 T2 => wf_typ e T1 /\ wf_typ e T2
  | all T1 T2   => wf_typ e T1 /\ wf_typ (ebound e T1) T2
  end.

Fixpoint wf_term (e : env) (t : term) {struct t} : Prop :=
  match t with
  | var x      => get_var e x <> None
  | abs T1 t2  => wf_typ e T1  /\ wf_term (evar e T1) t2
  | app t1 t2  => wf_term e t1 /\ wf_term e t2
  | tabs T1 t2 => wf_typ e T1  /\ wf_term (ebound e T1) t2
  | tapp t1 T2 => wf_term e t1 /\ wf_typ e T2
  end.

Fixpoint wf_env (e : env) : Prop :=
  match e with
    empty      => True
  | evar e T   => wf_typ e T /\ wf_env e
  | ebound e T => wf_typ e T /\ wf_env e
  end.

(****)

(*** Subtyping relation ***)

(* In the definition of the subtyping and typing relations, we insert
   some well-formedness condition that ensure that all environments,
   types and terms occuring in these relations are well-formed. The
   lemmas [sub_wf] and [typing_wf] show that this is indeed the case.

   We inserted as few well-formedness condition as possible in order
   to reduce the number of time we need to prove that a
   well-formedness condition holds when building a derivation.
*)

Inductive sub : env -> typ -> typ -> Prop :=
  | SA_Top :
      forall (e : env) (S : typ), wf_env e -> wf_typ e S -> sub e S top
  | SA_Refl_TVar :
      forall (e : env) (X : nat),
      wf_env e -> wf_typ e (tvar X) -> sub e (tvar X) (tvar X)
  | SA_Trans_TVar :
      forall (e : env) (X : nat) (T U : typ),
      get_bound e X = Some U -> sub e U T -> sub e (tvar X) T
  | SA_Arrow :
      forall (e : env) (T1 T2 S1 S2 : typ),
      sub e T1 S1 -> sub e S2 T2 -> sub e (arrow S1 S2) (arrow T1 T2)
  | SA_All :
      forall (e : env) (T1 T2 S1 S2 : typ),
      sub e T1 S1 -> sub (ebound e T1) S2 T2 -> sub e (all S1 S2) (all T1 T2).

(****)

(*** Typing relation ***)

Inductive typing : env -> term -> typ -> Prop :=
  | T_Var :
      forall (e : env) (x : nat) (T : typ),
      wf_env e -> get_var e x = Some T -> typing e (var x) T
  | T_Abs :
      forall (e : env) (t : term) (T1 T2 : typ),
      typing (evar e T1) t T2 ->
      typing e (abs T1 t) (arrow T1 T2)
  | T_App :
      forall (e : env) (t1 t2 : term) (T11 T12 : typ),
      typing e t1 (arrow T11 T12) ->
      typing e t2 T11 -> typing e (app t1 t2) T12
  | T_Tabs :
      forall (e : env) (t : term) (T1 T2 : typ),
      typing (ebound e T1) t T2 -> typing e (tabs T1 t) (all T1 T2)
  | T_Tapp :
      forall (e : env) (t1 : term) (T11 T12 T2 : typ),
      typing e t1 (all T11 T12) ->
      sub e T2 T11 -> typing e (tapp t1 T2) (tsubst T12 0 T2)
  | T_Sub :
      forall (e : env) (t : term) (T1 T2 : typ),
      typing e t T1 -> sub e T1 T2 -> typing e t T2.

(****)

(*** Reduction rules ***)

Definition value (t : term) :=
  match t with
  | abs _ _  => True
  | tabs _ _ => True
  | _        => False
  end.

Inductive ctx : Set :=
    c_hole : ctx
  | c_appfun : ctx -> term -> ctx
  | c_apparg : forall (t : term), value t -> ctx -> ctx
  | c_typefun : ctx -> typ -> ctx.

Fixpoint ctx_app (c : ctx) (t : term) {struct c} : term :=
  match c with
    c_hole           => t
  | c_appfun c' t'   => app (ctx_app c' t) t'
  | c_apparg t' _ c' => app t' (ctx_app c' t)
  | c_typefun c' T   => tapp (ctx_app c' t) T
  end.

Inductive red : term -> term -> Prop :=
  | E_AppAbs :
      forall (t11 : typ) (t12 t2 : term),
      value t2 -> red (app (abs t11 t12) t2) (subst t12 0 t2)
  | E_TappTabs :
      forall (t11 t2 : typ) (t12 : term),
      red (tapp (tabs t11 t12) t2) (subst_typ t12 0 t2)
  | E_Ctx :
      forall (c : ctx) (t1 t1' : term),
      red t1 t1' -> red (ctx_app c t1) (ctx_app c t1').


(*************************************************************************)
(*                            General lemmas                             *)
(*************************************************************************)


(*** Commutation properties of shifting and substitution ***)

Ltac tvar_case :=
  unfold tshift; unfold tsubst; fold tshift; fold tsubst;
  match goal with
  | |- ?x =>
      match x with
      | context [le_gt_dec ?n ?n'] =>
          case (le_gt_dec n n')
      | context C [(lt_eq_lt_dec ?n ?n')] =>
          case (lt_eq_lt_dec n n'); [intro s; case s; clear s | idtac ]
      end
  end.

Ltac common_cases n T :=
  simpl; generalize n; clear n; induction T; intros n''; intros;
    [ repeat tvar_case;
      simpl; trivial; try (intros; apply f_equal with (f := tvar); omega);
      try (intros; assert False; [ omega | contradiction ])
    | trivial
    | simpl; apply f_equal2 with (f := arrow); trivial
    | simpl; apply f_equal2 with (f := all); trivial ].

Lemma tsubst_tshift_prop :
  forall (n : nat) (T T' : typ), T = tsubst (tshift n T) n T'.
intros n T; common_cases n T.
Qed.

Lemma tshift_tshift_prop_1 :
  forall (n n' : nat) (T : typ),
  tshift n (tshift (n + n') T) = tshift (1 + (n + n')) (tshift n T).
intros n n' T; common_cases n T; exact (IHT2 (S n'')).
Qed.

Lemma tshift_tsubst_prop_1 :
  forall (n n' : nat) (T T' : typ),
  tshift n (tsubst T (n + n') T') =
  tsubst (tshift n T) (1 + n + n') (tshift n T').
intros n n' T; common_cases n T;
rewrite (tshift_tshift_prop_1 0 n''); apply (IHT2 (S n'')).
Qed.

Lemma tshift_tsubst_prop_2 :
  forall (n n' : nat) (T T' : typ),
  (tshift (n + n') (tsubst T n T')) =
  (tsubst (tshift (1 + n + n') T) n (tshift (n + n') T')).
intros n n' T; common_cases n T;
rewrite (tshift_tshift_prop_1 0 (n'' + n')); apply (IHT2 (S n'')).
Qed.

Lemma tsubst_tsubst_prop :
  forall (n n' : nat) (T U V : typ),
  (tsubst (tsubst T n U) (n + n') V) =
  (tsubst (tsubst T (1 + n + n') (tshift n V)) n (tsubst U (n + n') V)).
intros n n' T; common_cases n T;
  [ intros; apply tsubst_tshift_prop
  | rewrite (tshift_tsubst_prop_1 0 (n'' + n'));
    rewrite (tshift_tshift_prop_1 0 n'');
    apply (IHT2 (S n'')) ].
Qed.

(****)

(*** Some properties of the well-formedness conditions *)

Lemma wf_typ_env_weaken :
  forall (T : typ) (e e' : env),
  (forall (X : nat), get_bound e' X = None -> get_bound e X = None) ->
  wf_typ e T -> wf_typ e' T.
induction T; simpl; auto; intros e e' H (H1, H2); split;
  [ apply (IHT1 _ _ H H1)
  | apply (IHT2 _ _ H H2)
  | apply (IHT1 _ _ H H1)
  | apply IHT2 with (2 := H2); induction X;
      [ trivial
      | simpl; intro H3; rewrite H; trivial;
        generalize H3; case (get_bound e' X); simpl; trivial;
        intros; discriminate ] ].
Qed.

Lemma wf_typ_extensionality :
  forall (T : typ) (e e' : env),
  (forall (X : nat), get_bound e X = get_bound e' X) ->
  wf_typ e T -> wf_typ e' T.
intros T e e' H1 H2; apply wf_typ_env_weaken with (2 := H2);
intros n H3; rewrite H1; trivial.
Qed.

(****)

(*** Removal of a term variable binding ***)

(*
   This corresponds to the environment operation
      E, x : T, E'  |-->  E.
*)

Fixpoint remove_var (e : env) (x : nat) {struct e} : env :=
  match e with
  | empty       => empty
  | ebound e' T => ebound (remove_var e' x) T
  | evar e' T =>
      match x with
      | O   => e'
      | S x => evar (remove_var e' x) T
      end
  end.

Lemma get_var_remove_var_lt :
  forall (e : env) (x x' : nat),
  x < x' -> get_var (remove_var e x') x = get_var e x.
induction e; simpl; trivial; intros n n' H;
  [ induction n';
      [ inversion H
      | clear IHn'; induction n; simpl; trivial;
        apply IHe; omega ]
  | apply f_equal with (f := opt_map (tshift 0)); auto ].
Qed.

Lemma get_var_remove_var_ge :
  forall (e : env) (x x' : nat),
  x >= x' -> get_var (remove_var e x') x = get_var e (1 + x).
induction e; simpl; trivial; intros n n' H;
  [ induction n'; trivial;
    clear IHn'; induction n;
      [ inversion H
      | simpl; apply (IHe n); omega ]
  | apply f_equal with (f := opt_map (tshift 0)); apply (IHe n); trivial ].
Qed.

Lemma get_bound_remove_var :
  forall (e : env) (X x': nat), get_bound e X = get_bound (remove_var e x') X.
induction e; simpl; trivial; intros n n';
  [ induction n'; simpl; trivial
  | induction n; trivial;
    apply f_equal with (f := opt_map (tshift 0)); trivial ].
Qed.

Lemma wf_typ_remove_var :
  forall (e : env) (x : nat) (T : typ),
  wf_typ e T -> wf_typ (remove_var e x) T.
intros e n T; apply wf_typ_extensionality;
intro n'; apply get_bound_remove_var.
Qed.

Lemma wf_typ_insert_var :
  forall (e : env) (n : nat) (T : typ),
  wf_typ (remove_var e n) T -> wf_typ e T.
intros e n T; apply wf_typ_extensionality; intro n';
apply sym_eq; apply get_bound_remove_var.
Qed.

Lemma wf_env_remove_var :
  forall (e : env) (x : nat), wf_env e -> wf_env (remove_var e x).
induction e; simpl; trivial;
  [ intros n (H1, H2); induction n; trivial;
    simpl; split; auto; apply wf_typ_remove_var; trivial
  | intros n (H1, H2); split; auto; apply wf_typ_remove_var; trivial ].
Qed.

(****)

(*** Insertion of a type variable binding in an environment ****)

(*
   This corresponds to the environment operation
       E, E'  |-->  E, X <: T, E'.
   Note that all type variable in E' has to be shifted.
*)

Inductive insert_bound : nat -> env -> env -> Prop :=
    ib_here :
      forall (T : typ) (e : env), wf_typ e T -> insert_bound 0 e (ebound e T)
  | ib_var :
      forall (X : nat) (T : typ) (e e' : env),
      insert_bound X e e' ->
      insert_bound X (evar e T) (evar e' (tshift X T))
  | ib_bound :
      forall (X : nat) (T : typ) (e e' : env),
      insert_bound X e e' ->
      insert_bound (1 + X) (ebound e T) (ebound e' (tshift X T)).

Lemma get_bound_insert_bound_ge :
  forall (X X' : nat) (e e' : env),
  insert_bound X' e e' -> X' <= X ->
  get_bound e' (1 + X) = opt_map (tshift X') (get_bound e X).
simpl; intros n n' e e' H; generalize n; clear n; induction H; simpl; trivial;
intros n' H1; induction n'; simpl;
  [ inversion H1
  | clear IHn'; rewrite IHinsert_bound; try omega;
    case (get_bound e n'); simpl; trivial;
    intro T''; apply f_equal with (f := @Some typ);
    apply (tshift_tshift_prop_1 0 X) ].
Qed.

Lemma get_bound_insert_bound_lt :
  forall (X X' : nat) (e e' : env),
  insert_bound X' e e' -> X < X' ->
  get_bound e' X = opt_map (tshift X') (get_bound e X).
intros n n' e e' H; generalize n; clear n; induction H; simpl; trivial;
  [ intros n H1; inversion H1
  | intros n' H1; induction n';
      [ simpl; apply f_equal with (f := @Some typ);
        apply (tshift_tshift_prop_1 0 X)
      | clear IHn'; rewrite IHinsert_bound; try omega;
        case (get_bound e n'); simpl; trivial;
        intro T''; apply f_equal with (f := @Some typ);
        apply (tshift_tshift_prop_1 0 X) ] ].
Qed.

Lemma get_var_insert_bound :
  forall (x X' : nat) (e e' : env),
  insert_bound X' e e' -> get_var e' x = opt_map (tshift X') (get_var e x).
intros n n' e e' H; generalize n; clear n; induction H; simpl; intro n';
  [ trivial
  | induction n'; trivial
  | rewrite IHinsert_bound; case (get_var e n'); simpl; trivial;
    intro T'; apply f_equal with (f := @Some typ);
    apply (tshift_tshift_prop_1 0 X) ].
Qed.

Lemma insert_bound_wf_typ :
  forall (T : typ) (X : nat) (e e' : env),
  insert_bound X e e' -> wf_typ e T -> wf_typ e' (tshift X T).
induction T;
  [ unfold tshift; fold tshift; intros n' e e' H1 H2; case (le_gt_dec n' n);
      [ intro H3; unfold wf_typ; rewrite (get_bound_insert_bound_ge H1 H3);
        intro H4; apply H2; induction (get_bound e n); trivial; discriminate
      | intro H3; simpl; rewrite (get_bound_insert_bound_lt H1 H3);
        intro H4; apply H2; induction (get_bound e n); trivial; discriminate ]
  | trivial
  | simpl; intros n e e' H1 (H2, H3); eauto
  | simpl; intros n e e' H1 (H2, H3); split;
      [ apply (IHT1 _ _ _ H1 H2)
      | apply IHT2 with (e := (ebound e T1)); trivial;
        exact (ib_bound T1 H1) ] ].
Qed.

Lemma insert_bound_wf_env :
  forall (X : nat) (e e' : env),
  insert_bound X e e' -> wf_env e -> wf_env e'.
intros n e e' H; induction H; simpl; auto;
intros (H1, H2); split; auto; exact (insert_bound_wf_typ H H1).
Qed.

(****)

(*** More properties of the well-formedness conditions *)

Lemma wf_typ_weakening_bound :
  forall (e : env) (T U : typ),
  wf_typ e T -> wf_typ e U -> wf_typ (ebound e U) (tshift 0 T).
intros e T U H1 H2; apply insert_bound_wf_typ with (2 := H1);
apply ib_here; trivial.
Qed.

Lemma wf_typ_weakening_var :
  forall (e : env) (T U : typ),
  wf_typ e U -> wf_typ (evar e T) U.
intros e T U H; apply wf_typ_env_weaken with (2 := H); simpl; trivial.
Qed.

Lemma wf_typ_strengthening_var :
  forall (e : env) (T U : typ),
  wf_typ (evar e T) U -> wf_typ e U.
intros e T U H; apply wf_typ_env_weaken with (2 := H); simpl; trivial.
Qed.

Lemma wf_typ_ebound :
  forall (T U V : typ) (e : env),
  wf_typ (ebound e U) T -> wf_typ (ebound e V) T.
intros T U V e; apply wf_typ_env_weaken; intro X; induction X;
  [ intros; discriminate
  | trivial ].
Qed.

Lemma get_var_wf :
  forall (e : env) (n : nat) (T : typ),
  wf_env e -> get_var e n = Some T -> wf_typ e T.
induction e; simpl;
  [ intros; discriminate
  | induction n; intros T (H1, H2) E;
      [ injection E; clear E; intro E;
        rewrite <- E; exact (wf_typ_weakening_var t H1)
      | apply wf_typ_weakening_var; eauto ]
  | intros n T (H1, H2) E; assert (H3 := IHe n); clear IHe;
    induction (get_var e n);
      [ simpl in E; injection E; clear E; intro E; rewrite <- E;
        apply wf_typ_weakening_bound with (2 := H1); apply H3 with (1 := H2);
        trivial
      | discriminate ] ].
Qed.


(*************************************************************************)
(*                       Transitivity of subtyping                       *)
(*************************************************************************)


(*** Subtyping relation well-formedness ***)

Lemma sub_wf :
  forall (e : env) (T U : typ),
  sub e T U -> wf_env e /\ wf_typ e T /\ wf_typ e U.
intros e T U H; induction H; repeat split; simpl; trivial; try tauto;
  [ rewrite H; discriminate
  | apply wf_typ_ebound with (U := T1); tauto ].
Qed.

(****)

(*** A.1 Lemma [Reflexivity] ***)

Lemma sub_reflexivity :
  forall (e : env) (T : typ), wf_env e -> wf_typ e T -> sub e T T.
intros e T; generalize e; clear e; induction T; intros e H1 H2;
  [ apply SA_Refl_TVar; trivial
  | apply SA_Top; trivial
  | apply SA_Arrow;
      [ exact (IHT1 _ H1 (proj1 H2))
      | exact (IHT2 _ H1 (proj2 H2)) ]
  | apply SA_All;
      [ exact (IHT1 _ H1 (proj1 H2))
      | apply IHT2 with (2 := (proj2 H2)); simpl; simpl in H2; tauto ] ].
Qed.

(****)

(*** A.2 Lemma [Permutation and Weakening] ***)
(*** A.5 Lemma [Weakening for Subtyping and Typing] (subtyping part) ***)

(*
   Our proof does not make use of any permutation lemma.
   We only use one-step weakening with a variable inserted anywhere in
   the environment.
   The shifting is needed as a type variable binding is inserted in
   the environment.
*)

Lemma sub_weakening_bound_ind :
  forall (e e' : env) (X : nat) (U V : typ),
  insert_bound X e e' -> sub e U V -> sub e' (tshift X U) (tshift X V).
intros e e' X U V H1 H2; generalize X e' H1; clear X e' H1;
induction H2; intros X' e' H1; simpl;
  [ apply SA_Top;
      [ exact (insert_bound_wf_env H1 H)
      | exact (insert_bound_wf_typ H1 H0) ]
  | apply SA_Refl_TVar;
      [ exact (insert_bound_wf_env H1 H)
      | exact (insert_bound_wf_typ H1 H0) ]
  | apply SA_Trans_TVar with (2 := (IHsub X' e' H1));
    case (le_gt_dec X' X); intro H3;
      [ change (S X) with (1 + X); trivial;
        rewrite get_bound_insert_bound_ge with (1 := H1) (2 := H3);
        rewrite H; trivial
      | rewrite get_bound_insert_bound_lt with (1 := H1) (2 := H3);
        rewrite H; trivial ]
  | apply SA_Arrow; auto
  | apply SA_All; auto;
    exact (IHsub2 (1 + X') _ (ib_bound T1 H1)) ].
Qed.

Lemma sub_weakening_bound :
  forall (e : env) (T U V : typ),
  wf_typ e V -> sub e T U -> sub (ebound e V) (tshift 0 T) (tshift 0 U).
intros e T U V H0 H; apply sub_weakening_bound_ind with (2 := H);
apply ib_here; trivial.
Qed.

(*
   Rather than proving the weakening property for term variable
   bindings by induction on a derivation on a derivation (as in the
   paper proof), we prove the more general result that the subtyping
   relation does not depend on the term variable bindings.  Then, this
   intermediate result can be used for proving strengthening.
*)

Lemma sub_extensionality :
  forall (e e' : env) (U V : typ),
  (forall (X : nat), (get_bound e X) = (get_bound e' X)) -> wf_env e' ->
  sub e U V -> sub e' U V.
intros e e' U V H0 H1 H2; generalize e' H0 H1; clear e' H0 H1;
induction H2; intros e' H3 H1;
  [ apply SA_Top; trivial; exact (wf_typ_extensionality H3 H0)
  | apply SA_Refl_TVar; trivial; exact (wf_typ_extensionality H3 H0)
  | rewrite H3 in H; apply SA_Trans_TVar with (1 := H); auto
  | apply SA_Arrow; auto
  | apply SA_All; auto;
    apply IHsub2 with (e' := (ebound e' T1));
      [ intro X; induction X; simpl; trivial; rewrite H3; trivial
      | simpl; split; trivial;
        apply wf_typ_extensionality with (1 := H3);
        exact (proj1 (proj2 (sub_wf H2_))) ] ].
Qed.

Lemma sub_weakening_var_ind :
  forall (e : env) (x : nat) (U V : typ),
  wf_env e -> sub (remove_var e x) U V -> sub e U V.
intros e x U V H1; apply sub_extensionality; trivial;
intro X; apply sym_eq; apply get_bound_remove_var.
Qed.

Lemma sub_weakening_var :
  forall (e : env) (T U V : typ),
  wf_typ e V -> sub e T U -> sub (evar e V) T U.
intros e T U V H1 H2; generalize H2; apply sub_extensionality; trivial;
simpl; split; trivial; exact (proj1 (sub_wf H2)).
Qed.

(****)

(*** Relation "E' is a narrow of E" ***)

(*
   The environments E,X <: Q,E' and E,X<:P,E' are in a narrowing relation
   if E |- P <: Q.
*)

Inductive narrow : nat -> env -> env -> Prop :=
    narrow_0 :
      forall (e : env) (T T' : typ),
      sub e T' T -> narrow 0 (ebound e T) (ebound e T')
  | narrow_extend_bound :
      forall (e e' : env) (T : typ) (X : nat),
      wf_typ e' T -> narrow X e e' ->
      narrow (1 + X) (ebound e T) (ebound e' T)
  | narrow_extend_var :
      forall (e e' : env) (T : typ) (X : nat),
      wf_typ e' T -> narrow X e e' -> narrow X (evar e T) (evar e' T).

Lemma get_bound_narrow_ne :
  forall (X X' : nat) (e e' : env),
  narrow X e e' -> X' <> X -> get_bound e X' = get_bound e' X'.
intros n n' e e' H; generalize n'; clear n'; induction H; intros n' H1; simpl;
  [ induction n'; trivial; case H1; trivial
  | induction n'; trivial; rewrite IHnarrow; trivial; omega
  | auto ].
Qed.

Lemma get_bound_narrow_eq :
  forall (X : nat) (e e' : env),
  narrow X e e' ->
  exists T, exists T',
  get_bound e X = Some T /\ get_bound e' X = Some T' /\ sub e' T' T.
intros n e e' H; induction H;
  [ exists (tshift 0 T); exists (tshift 0 T'); repeat split;
    apply sub_weakening_bound; trivial; exact (proj1 (proj2 (sub_wf H)))
  | generalize IHnarrow; intros (Q, (P, (H1, (H2, H3))));
    exists (tshift 0 Q); exists (tshift 0 P); simpl; repeat split;
      [ rewrite H1; trivial
      | rewrite H2; trivial
      | apply sub_weakening_bound; trivial ]
  | generalize IHnarrow; intros (Q, (P, (H1, (H2, H3))));
    exists Q; exists P; repeat split; trivial;
    apply sub_weakening_var; trivial ].
Qed.

Lemma get_var_narrow :
  forall (X x' : nat) (e e' : env),
  narrow X e e' -> get_var e x' = get_var e' x'.
intros n n' e e' H; generalize n'; clear n'; induction H;
  [ trivial
  | simpl; intros n'; rewrite IHnarrow; trivial
  | simpl; induction n'; trivial ].
Qed.

Lemma narrow_wf_typ :
  forall (e e' : env) (T : typ) (X : nat),
  narrow X e e' -> wf_typ e T -> wf_typ e' T.
intros e e' T n H1 H2;
apply wf_typ_env_weaken with (2 := H2); intros n' H3;
case (eq_nat_dec n' n);
  [ intros E; rewrite E in H3;
    generalize (get_bound_narrow_eq H1);
    intros (Q, (P, (H4, (H5, H6)))); rewrite H5 in H3; discriminate
  | intro H4; rewrite (get_bound_narrow_ne H1 H4); trivial ].
Qed.

Lemma narrow_wf_env :
  forall (e e' : env) (X : nat),
  narrow X e e' -> wf_env e -> wf_env e'.
intros e e' n H; induction H; simpl;
intros (H1, H2); split; auto;
exact (proj1 (proj2 (sub_wf H))).
Qed.

(****)

(* A.3 Lemma [Transitivity and Narrowing] *)

(* The statements of the properties of transitivity and narrowing
   (we give the *statement* here and the *proof* below) *)

Definition transitivity_prop (Q : typ) :=
  forall (e : env) (S T : typ), sub e S Q -> sub e Q T -> sub e S T.

Definition narrowing_prop (Q : typ) :=
  forall (e e' : env) (X : nat) (S T : typ),
  narrow X e e' -> get_bound e X = Some Q ->
  sub e S T -> sub e' S T.

(* The proof follows closely the paper proof.  However, we cannot
   perform a proof on the distinguished type [Q] as the induction in
   the paper proof is on [Q] *up to alpha conversion* (shifting).
   Instead, we perform a proof by induction on the size of types. *)

Fixpoint size (T : typ) : nat :=
  match T with
  | tvar _      => 0
  | top         => 0
  | arrow T1 T2 => 1 + size T1 + size T2
  | all T1 T2   => 1 + size T1 + size T2
  end.

Lemma shift_preserves_size :
 forall (T : typ) (X : nat), size (tshift X T) = size T.
induction T; trivial;
simpl; intros n; rewrite IHT1; rewrite IHT2; trivial.
Qed.

(* Now we give the crucial step in the proof of transitivity, showing
   that transitivity holds if we assume that both transitivity and
   narrowing hold for smaller "cut types" q' *)

Lemma transitivity_case :
  forall Q : typ,
  (forall Q' : typ,
   size Q' < size Q -> transitivity_prop Q' /\ narrowing_prop Q') ->
  transitivity_prop Q.
intros Q H e S T H1 H2; induction H1;
  [ inversion_clear H2; apply SA_Top; trivial
  | trivial
  | exact (SA_Trans_TVar H0 (IHsub H H2))
  | inversion_clear H2;
      [ apply SA_Top; trivial;
        simpl; split;
          [ apply (proj2 (proj2 (sub_wf H1_)))
          | apply (proj1 (proj2 (sub_wf H1_0))) ]
      | apply SA_Arrow;
          [ assert (H5 : size T1 < size (arrow T1 T2)); try (simpl; omega);
            generalize (H _ H5); intros (H6, _); exact (H6 _ _ _ H0 H1_)
          | assert (H5 : size T2 < size (arrow T1 T2)); try (simpl; omega);
            generalize (H _ H5); intros (H6, _);
            exact (H6 _ _ _ H1_0 H1) ] ]
  | inversion_clear H2;
      [ apply SA_Top; trivial;
        simpl; split;
          [ apply (proj2 (proj2 (sub_wf H1_)))
          | apply wf_typ_ebound with (U := T1);
            apply (proj1 (proj2 (sub_wf H1_0))) ]
      | assert (H5 : size T1 < size (all T1 T2)); try (simpl; omega);
        apply SA_All;
          [ generalize (H _ H5); intros (H6, _); exact (H6 _ _ _ H0 H1_)
          | assert (H5' : size (tshift 0 T1) < size (all T1 T2));
              [ rewrite shift_preserves_size; trivial
              | generalize (H _ H5'); intros (_, H6);
                assert (H7 := narrow_0 H0);
                assert
                  (H7' : get_bound (ebound e T1) 0 = Some (tshift 0 T1));
                  [ trivial
                  | assert (H8 := H6 _ _ _ _ _ H7 H7' H1_0);
                    assert (H9 : size T2 < size (all T1 T2));
                    try (simpl; omega);
                    assert (G1 := proj1 (H _ H9));
                    exact (G1 (ebound e T0) _ _ H8 H1) ] ] ] ] ].
Qed.

(* Next we give the crucial step in the proof of narrowing, showing
   that narrowing for q holds if we assume transitivity for types of
   the same size as q.  (Not "for q itself" because there is some
   shifting involved.) *)

Lemma narrowing_case :
  forall Q : typ,
  (forall Q' : typ, size Q' = size Q -> transitivity_prop Q') ->
  narrowing_prop Q.
intros Q H2 e e' n T1 T2 H3 H4 H5; generalize e' n H3 H4; clear e' n H3 H4;
generalize Q H2; clear Q H2; induction H5; intros Q H2 e' n H3 H4;
  [ apply SA_Top;
      [ exact (narrow_wf_env H3 H)
      | exact (narrow_wf_typ H3 H0) ]
  | apply SA_Refl_TVar;
      [ exact (narrow_wf_env H3 H)
      | exact (narrow_wf_typ H3 H0) ]
  | case (eq_nat_dec X n);
      [ intro E; rewrite E in H; rewrite E; clear X E;
        assert (H4' := IHsub _ H2 _ _ H3 H4);
        rewrite H in H4; injection H4; intro E; rewrite E in H4';
        apply (H2 _ (refl_equal (size Q))) with (2 := H4');
        rewrite <- E;
        generalize (get_bound_narrow_eq H3);
        intros (T1, (T2, (H6, (H7, H8))));
        rewrite H in H6; injection H6;
        intro E1; rewrite <- E1 in H8;
        apply SA_Trans_TVar with (2 := H8); trivial
      | intro H6; apply SA_Trans_TVar with (2 := IHsub _ H2 _ _ H3 H4);
        rewrite <- (get_bound_narrow_ne H3 H6); trivial ]
 | apply SA_Arrow; eauto
 | apply SA_All;
     [ eauto
     | apply IHsub2 with (Q := tshift 0 Q) (n := (1 + n));
         [ intros Q' E; apply H2; rewrite E; apply shift_preserves_size
         | apply narrow_extend_bound with (2 := H3);
           apply narrow_wf_typ with (1 := H3);
           exact (proj1 (proj2 (sub_wf H5_)))
         | simpl; rewrite H4; trivial ] ] ].
Qed.

(* Now we combine the above lemmas into the full proof of transitivity
   and narrowing, by induction on the size of q.  (Note that this
   departs slightly from the paper proof, which was by structural
   induction on q.) *)

Lemma transitivity_and_narrowing :
 forall Q : typ, transitivity_prop Q /\ narrowing_prop Q.
assert
 (H :
  forall (n : nat) (Q : typ),
  size Q < n -> transitivity_prop Q /\ narrowing_prop Q);
 [ induction n;
    [ intros Q H; assert False; [ omega | contradiction ]
    | intros Q H; case (le_lt_or_eq _ _ H);
       [ intro H'; apply IHn; omega
       | intro E; injection E; clear E; intro E; rewrite <- E in IHn;
          assert
           (H1 : forall Q' : typ, size Q' = size Q -> transitivity_prop Q');
          [ intros Q' E1; rewrite <- E1 in IHn; apply transitivity_case;
             trivial
          | split; [ apply H1; trivial | apply narrowing_case; trivial ] ] ] ]
 | intro Q; apply (H (S (size Q))); omega ].
Qed.

Lemma sub_transitivity :
  forall (e : env) (T U V : typ), sub e T U -> sub e U V -> sub e T V.
intros e T U; apply (proj1 (transitivity_and_narrowing U)).
Qed.

Lemma sub_narrowing :
  forall (e e' : env) (X : nat) (S T : typ),
  narrow X e e' -> sub e S T -> sub e' S T.
intros e e' n S T H1 H2;
generalize (get_bound_narrow_eq H1); intros (Q, (P, (H3, _)));
exact (proj2 (transitivity_and_narrowing Q) _ _ _ _ _ H1 H3 H2).
Qed.


(*************************************************************************)
(*                              Type safety                              *)
(*************************************************************************)


(*** Substitution of a type variable in an environment ****)

(*
   This corresponds to the environment operation
      E, X <: T, E'  |-->  E, [X|->T']E',
   assuming that E |- T' <: T.
   (see definition A.9)
*)

Inductive env_subst : nat -> typ -> env -> env -> Prop :=
    es_here :
      forall (e : env) (T T' : typ),
      sub e T' T -> env_subst 0 T' (ebound e T) e
  | es_var :
      forall (X : nat) (T T' : typ) (e e' : env),
      env_subst X T' e e' ->
      env_subst X T' (evar e T) (evar e' (tsubst T X T'))
  | es_bound :
      forall (X : nat) (T T' : typ) (e e' : env),
      env_subst X T' e e' ->
      env_subst (1 + X) (tshift 0 T') (ebound e T) (ebound e' (tsubst T X T')).

Lemma env_subst_get_var :
  forall (x X' : nat) (e e' : env) (T : typ),
  (env_subst  X' T e e') ->
  get_var e' x = opt_map (fun T' => tsubst T' X' T) (get_var e x).
intros n n' e e' T H; generalize n; clear n; induction H;
  [ intro n; simpl; induction (get_var e n); simpl; trivial;
    apply f_equal with (f := @Some typ); apply tsubst_tshift_prop
  | intro n'; induction n'; simpl; trivial
  | simpl; intro n'; rewrite IHenv_subst;
    induction (get_var e n'); simpl; trivial;
    apply f_equal with (f := @Some typ);
    apply (tshift_tsubst_prop_1 0 X) ].
Qed.

Lemma env_subst_get_bound_lt :
  forall (X X' : nat) (e e' : env) (T : typ),
  (env_subst X' T e e') -> X < X' ->
  get_bound e' X = opt_map (fun T' => tsubst T' X' T) (get_bound e X).
intros n n' e e' T H; generalize n; clear n;
induction H; simpl; trivial; intros n' H1;
  [ inversion H1
  | induction n';
      [ simpl; apply f_equal with (f := @Some typ);
        apply (tshift_tsubst_prop_1 0 X)
      | clear IHn'; rewrite IHenv_subst;
          [ case (get_bound e n'); simpl; trivial; intro T'';
            apply f_equal with (f := @Some typ);
            apply (tshift_tsubst_prop_1 0 X)
          | omega ] ] ].
Qed.

Lemma env_subst_get_bound_ge :
  forall (X X' : nat) (e e' : env) (T : typ),
  env_subst X' T e e' -> X' < X ->
  get_bound e' (X - 1) = opt_map (fun T' => tsubst T' X' T) (get_bound e X).
intros n n' e e' T H; generalize n; clear n;
induction H; simpl; trivial; intros n' H1;
  [ induction n';
      [ inversion H1
      | simpl; rewrite <- minus_n_O; case (get_bound e n'); simpl; trivial;
        intro T''; apply f_equal with (f := @Some typ);
        apply tsubst_tshift_prop ]
  | induction n';
      [ inversion H1
      | clear IHn'; replace ((S n') - 1) with (S (n' - 1)); try omega;
        rewrite IHenv_subst; try omega;
        case (get_bound e n'); simpl; trivial; intro T'';
        apply f_equal with (f := @Some typ);
        apply (tshift_tsubst_prop_1 0 X) ] ].
Qed.

Lemma env_subst_wf_typ_0 :
  forall (e e' : env) (T : typ) (X : nat),
  env_subst X T e e' -> wf_env e' -> wf_typ e' T.
intros e e' T X H; induction H; simpl;
  [ intros _; exact (proj1 (proj2 (sub_wf H)))
  | intros (H1, H2); apply wf_typ_weakening_var; auto
  | intros (H1, H2); apply wf_typ_weakening_bound; auto ].
Qed.

Lemma env_subst_wf_typ :
  forall (e e' : env) (S T : typ) (X : nat),
  env_subst X T e e' -> wf_typ e S -> wf_env e' -> wf_typ e' (tsubst S X T).
intros e e' S; generalize e e'; clear e e'; induction S;
  [ intros e e' T n' H1 H2 H3; simpl; simpl in H2; case (lt_eq_lt_dec n n');
      [ intro s; case s; clear s; intro H5;
          [ simpl; rewrite env_subst_get_bound_lt with (1 := H1) (2 := H5);
            induction (get_bound e n); trivial; discriminate
          | exact (env_subst_wf_typ_0 H1 H3) ]
      | intro H5; simpl;
        rewrite env_subst_get_bound_ge with (1 := H1) (2 := H5);
        induction (get_bound e n); trivial; discriminate ]
  | trivial
  | simpl; intros e e' T n H0 (H1, H2) H3; eauto
  | simpl; intros e e' T n H0 (H1, H2) H3; split; eauto;
    apply IHS2 with (e := (ebound e S1)); trivial;
      [ exact (es_bound S1 H0)
      | simpl; split; trivial; apply IHS1 with (1 := H0); trivial ] ].
Qed.

Lemma env_subst_wf_env :
  forall (e e' : env) (T : typ) (X : nat),
  env_subst X T e e' -> wf_env e -> wf_env e'.
intros e e' T X H; induction H; simpl; try tauto;
intros (H1, H2); split; auto;
apply env_subst_wf_typ with (1 := H); auto.
Qed.

(****)

(*** Typing relation well-formedness ***)

Lemma typing_wf :
  forall (e : env) (t : term) (U : typ),
  typing e t U -> wf_env e /\ wf_term e t /\ wf_typ e U.
intros e t U H; induction H;
  [ repeat split; simpl; trivial;
      [ simpl; rewrite H0; discriminate
      | exact (get_var_wf H H0) ]
  | simpl in IHtyping; simpl; repeat split; try tauto;
    apply wf_typ_strengthening_var with (T := T1); tauto
  | simpl; simpl in IHtyping1; tauto
  | simpl; simpl in IHtyping; tauto
  | simpl; simpl in IHtyping; assert (H1 := proj1 (proj2 (sub_wf H0)));
    repeat split; try tauto;
    apply env_subst_wf_typ with (1 := es_here H0); tauto
  | repeat split; try tauto; exact (proj2 (proj2 (sub_wf H0))) ].
Qed.

(****)

(*** A.4 Lemma [Permutation for Typing] ***)

(* We don't need any permutation lemma. *)

(****)

(*** A.5 Lemma [Weakening for typing] (typing part) ***)

Lemma typing_weakening_bound_ind :
  forall (e e' : env) (X : nat) (t : term) (U : typ),
  insert_bound X e e' ->
  typing e t U -> typing e' (shift_typ X t) (tshift X U).
intros e e' n t U H1 H2; generalize n e' H1; clear n e' H1;
induction H2; intros n1 e' H1; simpl;
  [ apply T_Var;
      [ exact (insert_bound_wf_env H1 H)
      | rewrite get_var_insert_bound with (1 := H1); rewrite H0; trivial ]
  | apply T_Abs; apply IHtyping; apply ib_var; trivial
  | assert (H2 := (IHtyping1 _ _ H1)); assert (H3 := (IHtyping2 _ _ H1));
    exact (T_App H2 H3)
  | apply T_Tabs; apply IHtyping; exact (ib_bound T1 H1)
  | rewrite (tshift_tsubst_prop_2 0 n1);
    apply (T_Tapp (IHtyping _ _ H1) (sub_weakening_bound_ind H1 H))
  | exact (T_Sub (IHtyping _ _ H1) (sub_weakening_bound_ind H1 H)) ].
Qed.

Lemma typing_weakening_bound :
  forall (e : env) (t : term) (U V : typ),
  wf_typ e V -> typing e t U ->
  typing (ebound e V) (shift_typ 0 t) (tshift 0 U).
intros e t U V H1 H2; apply typing_weakening_bound_ind with (2 := H2);
apply ib_here; trivial.
Qed.

Lemma typing_weakening_var_ind :
  forall (e : env) (x : nat) (t : term) (U : typ),
  wf_env e -> typing (remove_var e x) t U -> typing e (shift x t) U.
intros e n t U H1 H2; cut (exists e', e' = remove_var e n);
  [ intros (e', E); rewrite <- E in H2; generalize n e E H1; clear n e E H1;
    induction H2; intros n' e' E H1; simpl;
      [ apply T_Var; trivial; rewrite E in H0;
        case (le_gt_dec n' x); intro H2;
          [ rewrite get_var_remove_var_ge in H0; trivial; omega
          | rewrite get_var_remove_var_lt in H0; trivial; omega ]
      | apply T_Abs; apply IHtyping;
          [ rewrite E; trivial
          | simpl; split; trivial;
            assert (H3 := proj1 (proj1 (typing_wf H2))); rewrite E in H3;
            exact (wf_typ_insert_var H3) ]
      | exact (T_App (IHtyping1 _ _ E H1) (IHtyping2 _ _ E H1))
      | apply T_Tabs; apply IHtyping;
          [ rewrite E; trivial
          | simpl; split; trivial;
            assert (H3 := proj1 (proj1 (typing_wf H2))); rewrite E in H3;
            exact (wf_typ_insert_var H3) ]
      | apply (T_Tapp (T2 := T2) (IHtyping _ _ E H1));
        rewrite E in H; exact (sub_weakening_var_ind H1 H)
      | apply (T_Sub (T2 := T2) (IHtyping _ _ E H1));
        rewrite E in H; exact (sub_weakening_var_ind H1 H) ]
  | exists (remove_var e n); trivial ].
Qed.

Lemma typing_weakening_var :
  forall (e : env) (t : term) (U V : typ),
  wf_typ e V -> typing e t U -> typing (evar e V) (shift 0 t) U.
intros e t U V H1 H2; apply (@typing_weakening_var_ind (evar e V));
simpl; trivial; split; trivial; exact (proj1 (typing_wf H2)).
Qed.

(****)

(*** A.6 Lemma [Strengthening] ***)

Lemma sub_strengthening_var :
  forall (e : env) (x : nat) (U V : typ),
  sub e U V -> sub (remove_var e x) U V.
intros e x U V H1; generalize H1; apply sub_extensionality;
  [ intro X; apply get_bound_remove_var
  | apply wf_env_remove_var; exact (proj1 (sub_wf H1)) ].
Qed.

(****)

(*** A.7 Lemma [Narrowing for the Typing Relation] ***)

Lemma typing_narrowing_ind :
  forall (e e' : env) (X : nat) (t : term) (U : typ),
  narrow X e e' -> typing e t U -> typing e' t U.
intros e e' n t U H1 H2; generalize e' n H1; clear e' n H1;
induction H2; intros e' n1 H1;
  [ apply T_Var;
      [ exact (narrow_wf_env H1 H)
      | rewrite <- get_var_narrow with (1 := H1); trivial ]
  | apply T_Abs; apply IHtyping with (n := n1);
    apply narrow_extend_var; trivial;
    exact (narrow_wf_typ H1 (proj1 (proj1 (typing_wf H2))))
  | eapply T_App; eauto
  | apply T_Tabs; apply IHtyping with (n := S n1);
    apply narrow_extend_bound with (X := n1); trivial;
    exact (narrow_wf_typ H1 (proj1 (proj1 (typing_wf H2))))
  | eapply T_Tapp; eauto; exact (sub_narrowing H1 H)
  | apply T_Sub with (1 := IHtyping _ _ H1); exact (sub_narrowing H1 H) ].
Qed.

Lemma typing_narrowing :
 forall (e : env) (t : term) (U V1 V2 : typ),
 typing (ebound e V1) t U -> sub e V2 V1 -> typing (ebound e V2) t U.
intros e t U V1 V2 H1 H2; exact (typing_narrowing_ind (narrow_0 H2) H1).
Qed.

(****)

(*** A.8 Lemma [Subtyping preserves typing] ***)

(* Compared to the lemma in the paper proof, this lemma is slightly
   stronger: [u] is typed in a larger environment.  This makes it
   possible to use our one-step weakning lemmas rather that the
   stronger lemmas of the paper proof. *)

Lemma subst_preserves_typing :
  forall (e : env) (x : nat) (t u : term) (V W : typ),
  typing e t V ->
  typing (remove_var e x) u W -> get_var e x = Some W ->
  typing (remove_var e x) (subst t x u) V.
intros e n t u V W H; generalize n u W; clear n u W;
induction H; intros n' u W H1 E1;
  [ simpl; case (lt_eq_lt_dec x n');
      [ intro s; case s; clear s; intro H2;
          [ apply T_Var;
              [ apply wf_env_remove_var; trivial
              | rewrite get_var_remove_var_lt with (1 := H2); trivial ]
          | rewrite H2 in H0; rewrite H0 in E1; injection E1;
            intro E3; rewrite E3; trivial ]
      | intro H2; apply T_Var;
          [ apply wf_env_remove_var; trivial
          | induction x;
              [ inversion H2
              | simpl; rewrite <- minus_n_O;
                rewrite get_var_remove_var_ge; trivial; omega ] ] ]
  | simpl; apply T_Abs; apply (IHtyping (S n') (shift 0 u) W); trivial;
    assert (H2 := wf_typ_remove_var n' (proj1 (proj1 (typing_wf H))));
    exact (typing_weakening_var H2 H1)
  | exact (T_App (IHtyping1 _ u W H1 E1) (IHtyping2 _ u W H1 E1))
  | simpl; apply T_Tabs; apply (IHtyping n' (shift_typ 0 u) (tshift 0 W));
      [ assert (H2 := wf_typ_remove_var n' (proj1 (proj1 (typing_wf H))));
        exact (typing_weakening_bound H2 H1)
      | simpl; rewrite E1; trivial ]
  | simpl; apply T_Tapp with (1 := (IHtyping _ u W H1 E1));
    exact (sub_strengthening_var n' H0)
  | simpl; apply T_Sub with (1 := (IHtyping _ u W H1 E1));
    exact (sub_strengthening_var n' H0) ].
Qed.

(****)

(*** A.10 Lemma [Type substitution preserves subtyping] ***)

Lemma env_subst_sub :
  forall (e e' : env) (T T' : typ) (X : nat),
  env_subst X T' e e' -> (get_bound e X) = (Some T) -> wf_env e' ->
  (sub e' T' (tsubst T X T')).
intros e e' T T' X H; generalize T; clear T; induction H; simpl;
  [ intros T'' E H1; injection E; clear E; intro E; rewrite <- E;
    rewrite <- tsubst_tshift_prop; trivial
  | intros T'' E (H1, H2);
    exact (sub_weakening_var H1 (IHenv_subst _ E H2))
  | intros T'' E (H1, H2); induction (get_bound e X); try discriminate;
    injection E; clear E; intro E; rewrite <- E;
    rewrite <- (tshift_tsubst_prop_1 0 X);
    apply sub_weakening_bound with (1 := H1); auto ].
Qed.

Lemma tsubst_preserves_subtyping :
  forall (e e' : env) (X : nat) (T U V : typ),
  env_subst X T e e' -> sub e U V -> sub e' (tsubst U X T) (tsubst V X T).
intros e e' n T U V H1 H2; generalize n e' T H1; clear n e' T H1; induction H2;
  [ intros n e' T H1; apply SA_Top;
      [ exact (env_subst_wf_env H1 H)
      | exact (env_subst_wf_typ H1 H0 (env_subst_wf_env H1 H)) ]
  | intros n e' T H1; apply sub_reflexivity;
      [ exact (env_subst_wf_env H1 H)
      | exact (env_subst_wf_typ H1 H0 (env_subst_wf_env H1 H)) ]
  | intros n e' T' H1; simpl; case (lt_eq_lt_dec X n);
      [ intros s; case s; clear s;
          [ intro H5; apply SA_Trans_TVar with (U := tsubst U n T');
              [ rewrite env_subst_get_bound_lt with (1 := H1) (2 := H5);
                rewrite H; trivial
              | apply IHsub; trivial ]
          | intro E; apply sub_transitivity with (2 := IHsub _ _ _ H1);
            rewrite E in H; apply (env_subst_sub H1 H);
            exact (env_subst_wf_env H1 (proj1 (sub_wf H2))) ]
      | intro H5; apply SA_Trans_TVar with (U := tsubst U n T');
          [ rewrite env_subst_get_bound_ge with (1 := H1); try omega;
            induction X;
              [ assert False; [ omega | contradiction ]
              | simpl; rewrite H; trivial ]
          | apply IHsub; trivial ] ]
  | intros n e' T H1; simpl; apply SA_Arrow; auto
  | intros n e' T H1; simpl; apply SA_All; auto;
    exact (IHsub2 _ _ _ (es_bound T1 H1)) ].
Qed.

(****)

(* A.11 Lemma [Type substitution preserves typing] *)

Lemma subst_typ_preserves_typing_ind :
  forall (e e' : env) (t : term) (U P : typ) (X : nat),
  env_subst X P e e' ->
  typing e t U -> typing e' (subst_typ t X P) (tsubst U X P).
intros e e' t U P n H1 H2; generalize n e' P H1; clear n e' P H1;
induction H2;
  [ intros n' e' P H1; simpl; apply T_Var;
      [ exact (env_subst_wf_env H1 H)
      | rewrite env_subst_get_var with (1 := H1); rewrite H0; trivial ]
  | intros n e' P H1; simpl; apply T_Abs; exact (IHtyping _ _ _ (es_var _ H1))
  | intros n e' P H1; exact (T_App (IHtyping1 _ _ _ H1) (IHtyping2 _ _ _ H1))
  | intros n e' P H1; exact (T_Tabs (IHtyping _ _ _ (es_bound _ H1)))
  | intros n e' P H1; simpl;
    assert (H4 := T_Tapp (T2 := (tsubst T2 n P)) (IHtyping _ _ _ H1));
    fold tsubst in H4; rewrite (tsubst_tsubst_prop 0 n);
    apply H4; exact (tsubst_preserves_subtyping H1 H)
  | intros n e' P H1; apply T_Sub with (1 := IHtyping _ _ _ H1);
    exact (tsubst_preserves_subtyping H1 H) ].
Qed.

Lemma subst_typ_preserves_typing :
  forall (e : env) (t : term) (U P Q : typ),
  typing (ebound e Q) t U -> sub e P Q ->
  typing e (subst_typ t 0 P) (tsubst U 0 P).
intros e t U P Q H1 H2; exact (subst_typ_preserves_typing_ind (es_here H2) H1).
Qed.

(****)

(*** A.12 Lemma [Inversion of subtyping] ***)

(* We use Coq inversion tactics instead. *)

(****)

(*** A.13 Lemma ***)

Lemma t_abs_inversion :
  forall (e : env) (t : term) (T0 T1 T2 T3 : typ),
  typing e (abs T1 t) T0 ->
  sub e T0 (arrow T2 T3) ->
  sub e T2 T1 /\
  (exists T4, sub e T4 T3 /\ typing (evar e T1) t T4).
intros e t T0 T1 T2 T3 H; cut (exists t' : _, t' = abs T1 t);
  [ intros (t', E1); rewrite <- E1 in H; generalize t T1 T2 T3 E1;
    clear t T1 T2 T3 E1;
    induction H; intros; try discriminate;
      [ injection E1; intros E2 E3; rewrite <- E2; rewrite <- E3;
        inversion_clear H0; split; [ trivial | exists T2; split; trivial ]
      | apply IHtyping with (1 := E1) (2 := sub_transitivity H0 H1) ]
  | exists (abs T1 t); trivial ].
Qed.

Lemma t_tabs_inversion :
  forall (e : env) (t : term) (T0 T1 T2 T3 : typ),
  typing e (tabs T1 t) T0 ->
  sub e T0 (all T2 T3) ->
  sub e T2 T1 /\
  (exists T4, sub (ebound e T2) T4 T3 /\ typing (ebound e T2) t T4).
intros e t T0 T1 T2 T3 H; cut (exists t' : _, t' = tabs T1 t);
  [ intros (t', E1); rewrite <- E1 in H; generalize t T1 T2 T3 E1;
    clear t T1 T2 T3 E1;
    induction H; intros; try discriminate;
      [ injection E1; intros E2 E3; rewrite <- E2; rewrite <- E3;
        inversion_clear H0; split; trivial;
        exists T2; split; trivial; exact (typing_narrowing H H1)
      | apply IHtyping with (1 := E1) (2 := sub_transitivity H0 H1) ]
  | exists (tabs T1 t); trivial ].
Qed.

(****)

(*** A.14 Lemma [Canonical Forms] ***)

Lemma fun_value :
  forall (t : term) (T1 T2 : typ),
  value t -> typing empty t (arrow T1 T2) ->
  exists t' , exists T1' , t = abs T1' t'.
intros t T1 T2 H1 H; cut (exists e, e = empty);
  [ intros (e, E1); rewrite <- E1 in H; cut (exists T0, T0 = arrow T1 T2);
      [ intros (T0, E2); rewrite <- E2 in H; generalize T1 T2 E2;
        clear T1 T2 E2; induction H; try contradiction;
          [ intros T3 T4 E; exists t; exists T1; trivial
          | intros; discriminate
          | intros T3 T4 E2; rewrite E2 in H0; inversion H0;
              [ rewrite E1 in H2; induction X; discriminate
              | exact (IHtyping H1 E1 _ _ (sym_eq H5)) ] ]
      | exists (arrow T1 T2); trivial ]
  | exists empty; trivial ].
Qed.

Lemma typefun_value :
  forall (t : term) (T1 T2 : typ),
  value t -> typing empty t (all T1 T2) ->
  exists t', exists T1', t = tabs T1' t'.
intros t T1 T2 H1 H; cut (exists e, e = empty);
  [ intros (e, E1); rewrite <- E1 in H; cut (exists T0, T0 = all T1 T2);
      [ intros (T0, E2); rewrite <- E2 in H; generalize T1 T2 E2;
        clear T1 T2 E2; induction H; try contradiction;
          [ intros; discriminate
          | intros T3 T4 E; exists t; exists T1; trivial
          | intros T3 T4 E2; rewrite E2 in H0; inversion H0;
              [ rewrite E1 in H2; induction X; discriminate
              | exact (IHtyping H1 E1 _ _ (sym_eq H5)) ] ]
      | exists (all T1 T2); trivial ]
  | exists empty; trivial ].
Qed.

(****)

(*** A.15 Lemma ***)

Lemma local_progress :
  forall (t : term) (U : typ),
  typing empty t U -> value t \/
  exists c, exists t0, exists t0', red t0 t0' /\ t = ctx_app c t0.
intros t U H; cut (exists e, e = empty);
  [ intros (e, E); rewrite <- E in H;
    induction H;
      [ rewrite E in H0; induction x; discriminate
      | simpl; auto
      | right; case (IHtyping1 E); clear IHtyping1;
          [ intro H2; case (IHtyping2 E); clear IHtyping2;
              [ intro H3; rewrite E in H; generalize (fun_value H2 H);
                intros (t', (T1', E1)); rewrite E1; exists c_hole;
                exists (app (abs T1' t') t2); exists (subst t' 0 t2);
                split; trivial; apply E_AppAbs; trivial
              | intros (c, (t0, (t0', (H3, E1)))); exists (c_apparg H2 c);
                exists t0; exists t0'; rewrite E1; auto ]
          | intros (c, (t0, (t0', (H3, E1)))); exists (c_appfun c t2);
            exists t0; exists t0'; rewrite E1; auto ]
      | simpl; auto
      | right; case (IHtyping E); clear IHtyping;
          [ intro H1; rewrite E in H; generalize (typefun_value H1 H);
            intros (t', (T1', E1)); rewrite E1; exists c_hole;
            exists (tapp (tabs T1' t') T2); exists (subst_typ t' 0 T2);
            split; trivial; apply E_TappTabs
          | intros (c, (t0, (t0', (H3, E1)))); exists (c_typefun c T2);
            exists t0; exists t0'; rewrite E1; auto ]
      | auto ]
  | exists empty; trivial ].
Qed.

(****)

(*** A.16 Theorem [Progress] ***)

Theorem progress :
  forall (t : term) (U : typ),
  typing empty t U -> value t \/ exists t', red t t'.
intros t U H; generalize (local_progress H);
intros [H1 | (c, (t0, (t0', (H1, H2))))]; auto;
right; exists (ctx_app c t0'); rewrite H2; apply E_Ctx; trivial.
Qed.

(****)

(*** A.18 Lemma ***)

(*
   We only prove the first part of the lemma, as the second part is
   not needed.
   We don't follow the paper proof sketch (induction on the structure
   of evaluation contexts, then case on the last rule used in the
   typing derivation) as this does not go through...  Instead, our
   proof is by induction on the typing derivation and case on the
   evaluation context.
*)

Lemma context_replacement :
   forall (e : env) (c : ctx) (t t' : term) (T : typ),
   (forall (T' : typ), (typing e t T') -> (typing e t' T')) ->
   typing e (ctx_app c t) T -> typing e (ctx_app c t') T.
intros e c t t' T H1 H2; cut (exists t'', t'' = ctx_app c t);
  [ intros (t'', E); rewrite <- E in H2;
    generalize c E; clear c E; induction H2;
      [ induction c; try (intros; discriminate); simpl;
        intros E; apply H1; rewrite <- E; apply T_Var; trivial
      | induction c; try (intros; discriminate); simpl;
        intros E; apply H1; rewrite <- E; apply T_Abs; trivial
      | induction c; try (intros; discriminate); simpl;
          [ intros E; apply H1; rewrite <- E; exact (T_App H2_ H2_0)
          | intro E; injection E; clear E; intros E1 E2;
            rewrite <- E1; apply T_App with (2 := H2_0);
            apply IHtyping1; trivial
          | intro E; injection E; clear E; intros E1 E2;
            rewrite <- E2; apply T_App with (1 := H2_);
            apply IHtyping2; trivial ]
      | induction c; try (intros; discriminate); simpl;
        intros E; apply H1; rewrite <- E; exact (T_Tabs H2)
      | induction c; try (intros; discriminate); simpl;
          [ intros E; apply H1; rewrite <- E; exact (T_Tapp H2 H)
          | intro E; injection E; clear E; intros E1 E2;
            rewrite <- E1; apply T_Tapp with (2 := H);
            apply IHtyping; trivial ]
      | intros c E; apply T_Sub with (2 := H); apply IHtyping; trivial ]
  | exists (ctx_app c t); trivial ].
Qed.

(****)

(*** A.18 Lemma ***)

Lemma local_preservation_app :
  forall (e : env) (t12 t2 : term) (T11 U : typ),
  typing e (app (abs T11 t12) t2) U -> typing e (subst t12 0 t2) U.
intros e t12 t2 T11 U H; cut (exists t, t = app (abs T11 t12) t2);
  [ intros (t, E); rewrite <- E in H; induction H; try discriminate;
      [ injection E; clear E; intros E1 E2; rewrite E2 in H;
        assert (H6 := proj1 (typing_wf H));
        assert (H7 := proj2 (proj2 (typing_wf H)));
        generalize (t_abs_inversion H (sub_reflexivity H6 H7));
        intros (H2, (T4, (H4, H5))); apply T_Sub with (2 := H4);
        apply (subst_preserves_typing (x := 0) (u := t2) (W := T11) H5);
        trivial; simpl; rewrite <- E1; exact (T_Sub H0 H2)
      | apply T_Sub with (2 := H0); auto ]
  | exists (app (abs T11 t12) t2); trivial ].
Qed.

Lemma local_preservation_tapp :
  forall (e : env) (t12 : term) (T11 T2 U : typ),
  typing e (tapp (tabs T11 t12) T2) U -> typing e (subst_typ t12 0 T2) U.
intros e t12 T11 T2 U H; cut (exists t, t = tapp (tabs T11 t12) T2);
  [ intros (t, E); rewrite <- E in H; induction H; try discriminate;
      [ injection E; clear E; intros E1 E2; rewrite E2 in H;
        assert (H7 := proj1 (typing_wf H));
        assert (H8 := proj2 (proj2 (typing_wf H)));
        generalize (t_tabs_inversion H (sub_reflexivity H7 H8));
        intros (H2, (T3, (H4, H5))); assert (H6 := T_Sub H5 H4);
        rewrite <- E1; exact (subst_typ_preserves_typing H6 H0)
      | apply T_Sub with (2 := H0); auto ]
  | exists (tapp (tabs T11 t12) T2); trivial ].
Qed.

(****)

(*** A.20 Theorem [Preservation] ***)

Theorem preservation :
  forall (e : env) (t t' : term) (U : typ),
  typing e t U -> red t t' -> typing e t' U.
intros e t t' U H1 H2; generalize U H1; clear U H1; induction H2; intros U H1;
  [ exact (local_preservation_app H1)
  | exact (local_preservation_tapp H1)
  | exact (context_replacement IHred H1) ].
Qed.


(*************************************************************************)
(*                      Alternate reduction relation                     *)
(*************************************************************************)


Inductive red' : term -> term -> Prop :=
  | appabs :
      forall (t11 : typ) (t12 t2 : term),
      value t2 -> red' (app (abs t11 t12) t2) (subst t12 0 t2)
  | tapptabs :
      forall (t11 t2 : typ) (t12 : term),
      red' (tapp (tabs t11 t12) t2) (subst_typ t12 0 t2)
  | appfun :
      forall t1 t1' t2 : term, red' t1 t1' -> red' (app t1 t2) (app t1' t2)
  | apparg :
      forall t1 t2 t2' : term,
      value t1 -> red' t2 t2' -> red' (app t1 t2) (app t1 t2')
  | typefun :
      forall (t1 t1' : term) (t2 : typ),
      red' t1 t1' -> red' (tapp t1 t2) (tapp t1' t2).

Theorem progress' :
  forall (t : term) (U : typ),
  typing empty t U -> value t \/ exists t', red' t t'.
intros t U H; cut (exists e, e = empty);
  [ intros (e, E); rewrite <- E in H;
    induction H;
      [ rewrite E in H0; induction x; discriminate
      | simpl; auto
      | right; case (IHtyping1 E);
          [ intro H2; case (IHtyping2 E);
              [ intro H3; rewrite E in H; generalize (fun_value H2 H);
                intros (t', (T1', E1)); rewrite E1; exists (subst t' 0 t2);
                apply appabs; trivial
              | intros (t2', H3); exists (app t1 t2'); apply apparg; trivial ]
          | intros (t1', H2); exists (app t1' t2); apply appfun; trivial ]
      | simpl; auto
      | right; case (IHtyping E);
          [ intro H1; rewrite E in H; generalize (typefun_value H1 H);
            intros (t', (T1', E1)); rewrite E1; exists (subst_typ t' 0 T2);
            apply tapptabs; trivial
          | intros (t1', H1); exists (tapp t1' T2); apply typefun; trivial ]
      | auto ]
  | exists empty; trivial ].
Qed.

Theorem preservation' :
  forall (e : env) (t t' : term) (U : typ),
  typing e t U -> red' t t' -> typing e t' U.
intros e t t' U H1; generalize t'; clear t'; induction H1;
  [ intros t' H1; inversion_clear H1
  | intros t' H2; inversion_clear H2
  | intros t' H2; generalize H1_ IHtyping1; clear H1_ IHtyping1;
    inversion_clear H2;
      [ intros H1 IHtyping1;
        assert (H6 := proj1 (typing_wf H1));
        assert (H7 := proj2 (proj2 (typing_wf H1)));
        generalize (t_abs_inversion H1 (sub_reflexivity H6 H7));
        intros (H2, (T4, (H4, H5))); apply T_Sub with (2 := H4);
        apply (subst_preserves_typing (x := 0) (u := t2) (W := t11) H5);
        trivial; simpl; exact (T_Sub H1_0 H2)
      | intros H1 IHtyping1; apply T_App with (1 := IHtyping1 _ H); trivial
      | intros H2 IHtyping1; apply T_App with (2 := IHtyping2 _ H0); trivial ]
  | intros t' H2; inversion_clear H2
  | intros t' H2; generalize H1 IHtyping; clear H1 IHtyping;
    inversion_clear H2; intros H1 IHtyping;
      [ assert (H7 := proj1 (typing_wf H1));
        assert (H8 := proj2 (proj2 (typing_wf H1)));
        generalize (t_tabs_inversion H1 (sub_reflexivity H7 H8));
        intros (H2, (T3, (H4, H5))); assert (H6 := T_Sub H5 H4);
        exact (subst_typ_preserves_typing H6 H)
      | apply T_Tapp with (1 := IHtyping _ H0); trivial ]
  | intros t' H2; eapply T_Sub; auto ].
Qed.
