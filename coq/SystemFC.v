(** * System F **)

Require Export SfLib.


(* ###################################################################### *)
(** ** Syntax *)

Module SYSTEMFC.

(* ################################### *)
(** *** Types *)

Inductive ty : Type := 
  | TVar    : nat -> ty 
  | TArrow  : ty -> ty -> ty
  | TUniv   : ty -> ty
  | TCoerce : ty -> ty -> ty -> ty.


Fixpoint tshift (X : nat) (T : ty) : ty :=
  match T with
  | TVar Y          => TVar (if le_gt_dec X Y then 1 + Y else Y)
  | TArrow T1 T2    => TArrow (tshift X T1) (tshift X T2)
  | TUniv T2        => TUniv (tshift (1 + X) T2)
  | TCoerce T1 T2 T => TCoerce (tshift X T1) (tshift X T2) (tshift X T) 
  end.

(* ################################### *)
(** *** Coercions *)

Inductive cn : Type :=
  | CVar   : nat -> cn
  | CRefl  : cn
  | CSym   : cn -> cn
  | CTrans : cn -> cn -> cn
  | CApp   : cn -> cn -> cn
  | CAbs   : cn -> cn
  | CLeft  : cn -> cn
  | CRight : cn -> cn
  | CTAbs  : cn -> cn
  | CTApp  : cn -> ty -> cn.

Tactic Notation "c_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "CVar"   | Case_aux c "CRefl"
  | Case_aux c "CSym"   | Case_aux c "CTrans"
  | Case_aux c "CApp"   | Case_aux c "CAbs"
  | Case_aux c "CLeft"  | Case_aux c "CRight"
  | Case_aux c "CTAbs"  | Case_aux c "CTApp" ].

Fixpoint cshift (X : nat) (c : cn) : cn :=
  match c with
  | CVar Y       => CVar (if le_gt_dec X Y then 1 + Y else Y)
  | CRefl        => CRefl
  | CSym c       => CSym (cshift X c)
  | CTrans c1 c2 => CTrans (cshift X c1) (cshift X c2)
  | CApp c1 c2   => CApp (cshift X c1) (cshift X c2)
  | CAbs c       => CAbs (cshift (S X) c)
  | CLeft c      => CLeft (cshift X c)
  | CRight c     => CRight (cshift X c)
  | CTAbs c      => CTAbs (cshift X c)
  | CTApp c T    => CTApp (cshift X c) T
  end.

Fixpoint cshift_typ (X : nat) (c : cn) : cn :=
  match c with
  | CVar Y       => CVar Y
  | CRefl        => CRefl
  | CSym c       => CSym (cshift_typ X c)
  | CTrans c1 c2 => CTrans (cshift_typ X c1) (cshift_typ X c2)
  | CApp c1 c2   => CApp (cshift_typ X c1) (cshift_typ X c2)
  | CAbs c       => CAbs (cshift_typ X c)
  | CLeft c      => CLeft (cshift_typ X c)
  | CRight c     => CRight (cshift_typ X c)
  | CTAbs c      => CTAbs (cshift_typ (S X) c)
  | CTApp c T    => CTApp (cshift_typ X c) (tshift X T)
  end.

(* ################################### *)
(** *** Terms *)

Inductive tm : Type :=
  | tvar    : nat -> tm
  | tapp    : tm -> tm -> tm
  | tabs    : ty -> tm -> tm
  | ttapp   : tm -> ty -> tm
  | ttabs   : tm -> tm
  | tcapp   : tm -> cn -> tm
  | tcabs   : ty -> ty -> tm -> tm
  | tcoerce : tm -> cn -> tm.

Tactic Notation "t_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tvar"  | Case_aux c "tapp" 
  | Case_aux c "tabs"  | Case_aux c "ttapp" 
  | Case_aux c "ttabs" | Case_aux c "tcapp"
  | Case_aux c "tcabs" | Case_aux c "tcoerce" ].


Fixpoint shift (x:nat) (t:tm) : tm :=
  match t with
    | tvar y         => tvar (if le_gt_dec x y then S y else y)
    | tabs T1 t2     => tabs T1 (shift (S x) t2)
    | tapp t1 t2     => tapp (shift x t1) (shift x t2)
    | ttabs t2       => ttabs (shift x t2)
    | ttapp t1 T2    => ttapp (shift x t1) T2
    | tcapp t1 c2    => tcapp (shift x t1) c2
    | tcabs T1 T2 t2 => tcabs T1 T2 (shift x t2)
    | tcoerce t c    => tcoerce (shift x t) c
  end.

Fixpoint shift_cn (X : nat) (t : tm) : tm :=
  match t with
    | tvar y         => tvar y
    | tabs T1 t2     => tabs T1 (shift_cn X t2)
    | tapp t1 t2     => tapp (shift_cn X t1) (shift_cn X t2)
    | ttabs t2       => ttabs (shift_cn X t2)
    | ttapp t1 T2    => ttapp (shift_cn X t1) T2
    | tcapp t1 c2    => tcapp (shift_cn X t1) (cshift X c2)
    | tcabs T1 T2 t2 => tcabs T1 T2 (shift_cn (S X) t2)
    | tcoerce t c    => tcoerce (shift_cn X t) (cshift X c)
  end.

Fixpoint shift_typ (X : nat) (t : tm) {struct t} : tm :=
  match t with
    | tvar y         => tvar y
    | tabs T1 t2     => tabs (tshift X T1) (shift_typ X t2)
    | tapp t1 t2     => tapp (shift_typ X t1) (shift_typ X t2)
    | ttabs t2       => ttabs (shift_typ (1 + X) t2)
    | ttapp t1 T2    => ttapp (shift_typ X t1) (tshift X T2)
    | tcapp t1 c2    => tcapp (shift_typ X t1) (cshift X c2)
    | tcabs T1 T2 t2 => tcabs (tshift X T1) (tshift X T2) (shift_typ X t2)
    | tcoerce t1 c2  => tcoerce (shift_typ X t1) (cshift_typ X c2)
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

Inductive uncoerced_value : tm -> Prop :=
  | uv_abs : forall T t,
      uncoerced_value (tabs T t)
  | uv_tabs : forall t,
      uncoerced_value (ttabs t)
  | uv_cabs : forall t T1 T2,
      uncoerced_value (tcabs T1 T2 t).

Hint Constructors uncoerced_value.

Inductive value : tm -> Prop :=
  | v_uncoerced : forall t,
      uncoerced_value t ->
      value t
  | v_coerced : forall t c,
      uncoerced_value t ->
      value (tcoerce t c).

Hint Constructors value.


(* ###################################################################### *)
(** *** Free Variables and Substitution *)


Class Subst (X S T : Type) := {
  do_subst : X -> S -> T -> T
}.
Notation "'[' x ':=' s ']' t" := (do_subst x s t) (at level 20).

Fixpoint subst_coercion_fix (x:nat) (d:cn) (c:cn) : cn :=
  match c with
    | CVar y => 
      if eq_nat_dec x y then d
      else if le_lt_dec x y then CVar (y-1)
           else CVar y
    | CRefl        => CRefl
    | CSym c       => CSym (subst_coercion_fix x d c)
    | CTrans c1 c2 => CTrans (subst_coercion_fix x d c1) (subst_coercion_fix x d c2)
    | CApp c1 c2   => CApp (subst_coercion_fix x d c1) (subst_coercion_fix x d c2)
    | CAbs c       => CAbs (subst_coercion_fix (S x) (cshift 0 d) c)
    | CLeft c      => CLeft (subst_coercion_fix x d c)
    | CRight c     => CRight (subst_coercion_fix x d c)
    | CTAbs c      => CTAbs (subst_coercion_fix x (cshift_typ 0 d) c)
    | CTApp c T    => CTApp (subst_coercion_fix x d c) T
  end.

Instance subst_cn : Subst nat cn cn := {
  do_subst := subst_coercion_fix
}.

Inductive subst_coercion : cn -> nat -> cn -> cn -> Prop :=
  | sc_var_here : forall d x,
      subst_coercion d x (CVar x) d
  | sc_var_lt : forall d x x',
      x < x' ->
      subst_coercion d x (CVar x') (CVar (x' - 1))
  | sc_var_gt : forall d x x',
      x > x' ->
      subst_coercion d x (CVar x') (CVar x')
  | sc_refl : forall d x,
      subst_coercion d x CRefl CRefl
  | sc_sym : forall d x c c',
      subst_coercion d x c c' ->
      subst_coercion d x (CSym c) (CSym c')
  | sc_trans : forall d x c1 c1' c2 c2',
      subst_coercion d x c1 c1' ->
      subst_coercion d x c2 c2' ->
      subst_coercion d x (CTrans c1 c2) (CTrans c1' c2')
  | sc_capp : forall d x c1 c1' c2 c2',
      subst_coercion d x c1 c1' ->
      subst_coercion d x c2 c2' ->
      subst_coercion d x (CApp c1 c2) (CApp c1' c2')
  | sc_cabs : forall d x c c',
      subst_coercion (cshift 0 d) (S x) c c' ->
      subst_coercion d x (CAbs c) (CAbs c')
  | sc_left : forall d x c c',
      subst_coercion d x c c' ->
      subst_coercion d x (CLeft c) (CLeft c')
  | sc_right : forall d x c c',
      subst_coercion d x c c' ->
      subst_coercion d x (CRight c) (CRight c')
  | sc_tabs : forall d x c c',
      subst_coercion (cshift_typ 0 d) x c c' ->
      subst_coercion d x (CTAbs c) (CTAbs c')
  | sc_tapp : forall d x c c' T,
      subst_coercion d x c c' ->
      subst_coercion d x (CTApp c T) (CTApp c' T).

Hint Constructors subst_coercion.

 
Lemma subst_coercion_correct : forall d x c c',
  [x:=d]c = c' <-> subst_coercion d x c c'.
Proof.
  intros d x c. split.
  Case "->".
    generalize dependent c'. generalize dependent x.
    generalize dependent d.
    induction c; intros d x c' H; simpl in H;
      try (subst; constructor; apply IHc; trivial).
    SCase "c = CVar n".
      destruct (eq_nat_dec x n) in H; subst.
      SSCase "x = n".
        constructor.
      SSCase "x <> n".
        destruct (le_lt_dec x n).
          constructor. omega. 
          constructor. omega.
    SCase "c = CTrans c1 c2".
      rewrite <- H. constructor.
      apply IHc1. trivial.
      apply IHc2. trivial.
    SCase "c = CApp c1 c2".
      rewrite <- H. constructor.
      apply IHc1. trivial.
      apply IHc2. trivial.
  Case "<-".
    intro H. induction H; simpl;
    subst; try reflexivity; try assumption.
    destruct (eq_nat_dec x x). trivial. omega.
    destruct (eq_nat_dec x x'). omega. destruct le_lt_dec.
    trivial. omega. 
    destruct (eq_nat_dec x x'). omega. destruct le_lt_dec.
    omega. trivial.
Qed.  

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
  | tcabs T1 T2 t =>
      tcabs T1 T2 (subst_term_fix x (shift_cn 0 s) t)
  | tcapp t c =>
      tcapp (subst_term_fix x s t) c
  | tcoerce t c =>
      tcoerce (subst_term_fix x s t) c
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
      subst_term s x (ttapp t T) (ttapp t' T)
  | s_tcabs : forall s x t t' T1 T2,
      subst_term (shift_cn 0 s) x t t' ->
      subst_term s x (tcabs T1 T2 t) (tcabs T1 T2 t')
  | s_tcapp : forall s x t t' c,
      subst_term s x t t' ->
      subst_term s x (tcapp t c) (tcapp t' c)
  | s_tcoerce : forall s x t t' c,
      subst_term s x t t' ->
      subst_term s x (tcoerce t c) (tcoerce t' c).


Hint Constructors subst_term.

Theorem subst_term_correct : forall s x t t',
  [x:=s]t = t' <-> subst_term s x t t'.
Proof.
  intros s x t. split.
  Case "->".
    generalize dependent t'. generalize dependent x.
    generalize dependent s.
    induction t; intros s x t' H; simpl in H;
      try (subst; constructor; apply IHt; trivial).
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
  | TUniv T   => TUniv (subst_type_in_type_fix (I + 1) (tshift 0 P) T)
  | TCoerce T1 T2 U =>
    TCoerce (subst_type_in_type_fix I P T1) (subst_type_in_type_fix I P T2)
            (subst_type_in_type_fix I P U)
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
      subst_type_in_type T I (TUniv T1) (TUniv T2)
  | s_coerce : forall U U1 U2 V V1 V2,
      subst_type_in_type T I U1 V1 ->
      subst_type_in_type T I U2 V2 ->
      subst_type_in_type T I U  V  ->
      subst_type_in_type T I (TCoerce U1 U2 U) (TCoerce V1 V2 V).

Lemma subst_type_in_type_correct : forall N P T1 T2,
  [N:=P]T1 = T2 <-> subst_type_in_type P N T1 T2.
Proof.
  intros. split.
  Case "->".
    generalize dependent N; generalize dependent P;
    generalize dependent T2;
    induction T1; intros; simpl in H.
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
    SCase "T2 = TCoerce T".
      rewrite <- H. constructor. apply IHT1_1. trivial.
      apply IHT1_2; trivial. apply IHT1_3; trivial.
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

(* Type in Coercion Substitution *)

Fixpoint subst_ty_in_cn_fix (X:nat) (U:ty) (c:cn) : cn :=
  match c with
    | CVar y       => CVar y
    | CRefl        => CRefl
    | CSym c       => CSym (subst_ty_in_cn_fix X U c)
    | CTrans c1 c2 => CTrans (subst_ty_in_cn_fix X U c1)
                             (subst_ty_in_cn_fix X U c2)
    | CApp c1 c2   => CApp (subst_ty_in_cn_fix X U c1)
                           (subst_ty_in_cn_fix X U c2)
    | CAbs c       => CAbs (subst_ty_in_cn_fix X U c)
    | CLeft c      => CLeft (subst_ty_in_cn_fix X U c)
    | CRight c     => CRight (subst_ty_in_cn_fix X U c)
    | CTAbs c      => CTAbs (subst_ty_in_cn_fix (S X) (tshift 0 U) c)
    | CTApp c T    => CTApp (subst_ty_in_cn_fix X U c) ([X := U] T)
  end.

Instance subst_ty_cn : Subst nat ty cn := {
  do_subst := subst_ty_in_cn_fix
}.

Inductive subst_ty_in_cn (T:ty) (X:nat) : cn -> cn -> Prop :=
  | stc_var : forall x,
      subst_ty_in_cn T X (CVar x) (CVar x)
  | stc_refl :
      subst_ty_in_cn T X CRefl CRefl
  | stc_sym : forall c c',
      subst_ty_in_cn T X c c' ->
      subst_ty_in_cn T X (CSym c) (CSym c')
  | stc_trans : forall c1 c1' c2 c2',
      subst_ty_in_cn T X c1 c1' ->
      subst_ty_in_cn T X c2 c2' ->
      subst_ty_in_cn T X (CTrans c1 c2) (CTrans c1' c2')
  | stc_capp : forall c1 c1' c2 c2',
      subst_ty_in_cn T X c1 c1' ->
      subst_ty_in_cn T X c2 c2' ->
      subst_ty_in_cn T X (CApp c1 c2) (CApp c1' c2')
  | stc_cabs : forall c c',
      subst_ty_in_cn T X c c' ->
      subst_ty_in_cn T X (CAbs c) (CAbs c')
  | stc_left : forall c c',
      subst_ty_in_cn T X c c' ->
      subst_ty_in_cn T X (CLeft c) (CLeft c')
  | stc_right : forall c c',
      subst_ty_in_cn T X c c' ->
      subst_ty_in_cn T X (CRight c) (CRight c')
  | stc_tabs : forall c c',
      subst_ty_in_cn (tshift 0 T) (S X) c c' ->
      subst_ty_in_cn T X (CTAbs c) (CTAbs c')
  | stc_tapp : forall c c' U V,
      subst_ty_in_cn T X c c'    ->
      subst_type_in_type T X U V ->
      subst_ty_in_cn T X (CTApp c U) (CTApp c' V).


Lemma subst_ty_in_cn_correct : forall U X c c',
  [X := U]c = c' <-> subst_ty_in_cn U X c c'.
Proof.
  intros. split.
  Case "->".
    generalize dependent c'. generalize dependent X.
    generalize dependent U.
    induction c; intros; simpl in H;
      try (subst; constructor; apply IHc; trivial).
    SCase "c = CTrans c1 c2".
      rewrite <- H. constructor.
      apply IHc1. trivial.
      apply IHc2. trivial.
    SCase "c = CApp c1 c2".
      rewrite <- H. constructor.
      apply IHc1. trivial.
      apply IHc2. trivial.
    SCase "c = CInst c T".
      rewrite <- H. constructor.
      apply IHc. trivial.
      apply subst_type_in_type_correct. trivial.
  Case "<-".
    intro H. induction H; simpl;
    subst; try reflexivity; try assumption.
    apply subst_type_in_type_correct in H0. subst. trivial.
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
  | tcabs T1 T2 t1 =>
      tcabs ([X:=T]T1) ([X:=T]T2) (subst_type_fix X T t1)
  | tcapp t1 c2 =>
      tcapp (subst_type_fix X T t1) ([X := T] c2)
  | tcoerce t1 c2 =>
      tcoerce (subst_type_fix X T t1) ([X := T] c2)
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
      subst_type P I (ttapp t T1) (ttapp t' T2)
  | st_tcabs : forall t t' U1 U2 V1 V2,
      subst_type P I t t'          ->
      subst_type_in_type P I U1 V1 ->
      subst_type_in_type P I U2 V2 ->
      subst_type P I (tcabs U1 U2 t) (tcabs V1 V2 t')
  | st_tcapp : forall t t' c c',
      subst_type P I t t'     ->
      subst_ty_in_cn P I c c' ->
      subst_type P I (tcapp t c) (tcapp t' c')
  | st_tcoerce : forall t t' c c',
      subst_type P I t t'     ->
      subst_ty_in_cn P I c c' ->
      subst_type P I (tcoerce t c) (tcoerce t' c').

Hint Constructors subst_type.

Theorem subst_type_correct : forall P I t t',
  [I := P] t = t' <-> subst_type P I t t'.
Proof.
  intros. split.
  Case "->".
    generalize dependent I. generalize dependent P.
    generalize dependent t'.
    induction t; intros t' P I H; simpl in H;
      try (rewrite <- H; constructor; apply IHt; reflexivity).
    SCase "t = tapp t1 t2".
      rewrite <- H. constructor.
      apply IHt1. reflexivity.
      apply IHt2. reflexivity.
    SCase "t = tabs T t0".
      rewrite <- H. constructor.
      apply IHt. reflexivity.
      apply subst_type_in_type_correct. reflexivity.
    SCase "t = ttapp".
      subst. constructor. apply IHt. reflexivity.
      apply subst_type_in_type_correct. reflexivity.
    SCase "t = tcapp".
      subst. constructor. apply IHt. reflexivity.
      apply subst_ty_in_cn_correct. reflexivity.
    SCase "t = tcabs".
      subst. constructor. apply IHt. reflexivity.
      apply subst_type_in_type_correct; trivial.
      apply subst_type_in_type_correct; trivial.
    SCase "t = tcoerce".
      subst. constructor. apply IHt. trivial.
      apply subst_ty_in_cn_correct. reflexivity.
  Case "<-".
    intro H. induction H; simpl;
    subst; try reflexivity; try assumption;
    try (apply subst_type_in_type_correct in H0;
         unfold do_subst in H0; unfold subst_ty_ty in H0;
         rewrite -> H0; reflexivity);
    try (apply subst_ty_in_cn_correct in H0;
         unfold do_subst in H0; unfold subst_ty_cn in H0;
         rewrite -> H0; reflexivity).
    apply subst_type_in_type_correct in H0.
    apply subst_type_in_type_correct in H1. subst. trivial.
Qed.

(** [] *)


(* Type in Term Substitution *)

Fixpoint subst_cn_in_tm_fix (x:nat) (c:cn) (t:tm) : tm :=
  match t with
  | tvar x =>
      tvar x
  | tabs T t1 => 
      tabs T (subst_cn_in_tm_fix x c t1) 
  | tapp t1 t2 => 
      tapp (subst_cn_in_tm_fix x c t1) (subst_cn_in_tm_fix x c t2)
  | ttabs t1 =>
      ttabs (subst_cn_in_tm_fix x c t1) 
  | ttapp t' T' =>
      ttapp (subst_cn_in_tm_fix x c t') T'
  | tcabs T1 T2 t1 =>
      tcabs T1 T2 (subst_cn_in_tm_fix (S x) (cshift 0 c) t1)
  | tcapp t1 c2 =>
      tcapp (subst_cn_in_tm_fix x c t1) ([x := c] c2)
  | tcoerce t1 c2 =>
      tcoerce (subst_cn_in_tm_fix x c t1) ([x := c] c2)
  end.

Instance subst_cn_tm : Subst nat cn tm := {
  do_subst := subst_cn_in_tm_fix
}.

Inductive subst_cn_in_tm (c:cn) (x:nat) : tm -> tm -> Prop := 
  | sct_var : forall y,
      subst_cn_in_tm c x (tvar y) (tvar y)
  | sct_tabs : forall T t t',
      subst_cn_in_tm c x t t'          ->
      subst_cn_in_tm c x (tabs T t) (tabs T t')
  | sct_tapp : forall t1 t2 t1' t2',
      subst_cn_in_tm c x t1 t1' ->
      subst_cn_in_tm c x t2 t2' ->
      subst_cn_in_tm c x (tapp t1 t2) (tapp t1' t2')
  | sct_ttabs : forall t t',
      subst_cn_in_tm c x t t' ->
      subst_cn_in_tm c x (ttabs t) (ttabs t')
  | sct_ttapp : forall t t' T,
      subst_cn_in_tm c x t t' ->
      subst_cn_in_tm c x (ttapp t T) (ttapp t' T)
  | sct_tcabs : forall t t' T1 T2,
      subst_cn_in_tm (cshift 0 c) (S x) t t' ->
      subst_cn_in_tm c x (tcabs T1 T2 t) (tcabs T1 T2 t')
  | sct_tcapp : forall t t' d d',
      subst_cn_in_tm c x t t'     ->
      subst_coercion c x d d' ->
      subst_cn_in_tm c x (tcapp t d) (tcapp t' d')
  | sct_tcoerce : forall t t' d d',
      subst_cn_in_tm c x t t'     ->
      subst_coercion c x d d' ->
      subst_cn_in_tm c x (tcoerce t d) (tcoerce t' d').

Hint Constructors subst_type.

Theorem subst_cn_in_tm_correct : forall c x t t',
  [x := c] t = t' <-> subst_cn_in_tm c x t t'.
Proof.
  intros. split.
  Case "->".
    generalize dependent x. generalize dependent c.
    generalize dependent t'.
    induction t; intros; simpl in H;
      try (rewrite <- H; try constructor; apply IHt; reflexivity).
    SCase "t = tapp t1 t2".
      rewrite <- H. constructor.
      apply IHt1. reflexivity.
      apply IHt2. reflexivity.
     SCase "t = tcapp".
      subst. constructor. apply IHt. reflexivity.
      apply subst_coercion_correct. reflexivity.
    SCase "t = tcoerce".
      subst. constructor. apply IHt. reflexivity.
      apply subst_coercion_correct. reflexivity.
  Case "<-".
    intro H. induction H; simpl;
    subst; try reflexivity; try assumption;
    try (apply subst_coercion_correct in H0;
         unfold do_subst in H0; unfold subst_cn in H0;
         rewrite -> H0; reflexivity).
Qed.


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
  | E_TAppTAbs : forall t12 T2,
         ttapp (ttabs t12) T2 ==> [0:=T2] t12
  | E_CApp : forall t1 t1' c2,
         t1 ==> t1' ->
         tcapp t1 c2 ==> tcapp t1' c2
  | E_CAppCAbs : forall t12 c2 T1 T2,
         tcapp (tcabs T1 T2 t12) c2 ==> [0:=c2] t12
  | E_Coerce : forall t1 t1' c2,
         t1 ==> t1' ->
         tcoerce t1 c2 ==> tcoerce t1' c2
  | E_CTrans : forall c1 c2 t,
         tcoerce (tcoerce t c1) c2 ==> tcoerce t (CTrans c1 c2)
  | E_PushApp : forall v1 v2 c,
         value v1 ->
         value v2 ->
         tapp (tcoerce v1 c) v2 ==>
              tcoerce (tapp v1 (tcoerce v2 (CSym (CLeft c)))) (CRight c)
  | E_PushTApp : forall v1 T2 c,
         value v1 ->
         ttapp (tcoerce v1 c) T2 ==>
              tcoerce (ttapp v1 T2) (CTApp c T2)
  | E_PushCApp : forall v1 c2 c,
         value v1 ->
         tcapp (tcoerce v1 c) c2 ==>
              tcoerce (tcapp v1 c2) (CApp c c2)

where "t1 '==>' t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_AppAbs"   | Case_aux c "E_App1" 
  | Case_aux c "E_App2"     | Case_aux c "E_TApp" 
  | Case_aux c "E_TAppTAbs" | Case_aux c "E_CApp"
  | Case_aux c "E_CAppCAbs" | Case_aux c "E_Coerce"
  | Case_aux c "E_CTrans"   | Case_aux c "E_PushApp"
  | Case_aux c "E_PushTApp" | Case_aux c "E_PushCApp"
  ].

Hint Constructors step.

Notation multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

(* ###################################################################### *)
(** ** Typing *)

(* ################################### *)
(** *** Contexts *)

(* Reimplementing this as in the DeBruijn Indices paper *)

Inductive context : Set :=
  | empty    : context
  | ext_var  : context -> ty -> context
  | ext_tvar : context -> context
  | ext_cvar : context -> ty * ty -> context.

Definition opt_map {A B : Type} (f : A -> B) (x : option A) :=
  match x with
  | Some x => Some (f x)
  | None => None
  end.

Definition opt_map_prod {A B : Type} (f : A -> B) (p : option (A * A)) :=
  match p with
    | Some (x, y) => Some (f x, f y)
    | None        => None
  end.

Fixpoint get_var (E : context) (x : nat) : option ty :=
  match E with
    | empty => None
    | ext_var E' T =>
      match x with
        | O   => Some T
        | S y => get_var E' y
      end
    | ext_tvar E'   => opt_map (tshift 0) (get_var E' x)
    | ext_cvar E' _ => get_var E' x
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
    | ext_cvar E' _ => get_tvar E' N
  end.

Fixpoint get_cvar (E : context) (N : nat) : option (ty * ty) :=
  match E with
    | empty => None
    | ext_var E' _  => get_cvar E' N
    | ext_tvar E'   => opt_map_prod (tshift 0) (get_cvar E' N)
    | ext_cvar E' c =>
      match N with
        | O    => Some c
        | S N' => get_cvar E' N'
      end
  end.

Fixpoint wf_ty (Gamma : context) (T : ty) : Prop :=
  match T with
  | TVar X          => get_tvar Gamma X = true
  | TArrow T1 T2    => wf_ty Gamma T1 /\ wf_ty Gamma T2
  | TUniv  T        => wf_ty (ext_tvar Gamma) T
  | TCoerce T1 T2 T => wf_ty Gamma T1 /\ wf_ty Gamma T2 /\ wf_ty Gamma T
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
      well_formed_type Gamma (TUniv T)
  | WF_TCoerce : forall T T1 T2,
      well_formed_type Gamma T1 ->
      well_formed_type Gamma T2 ->
      well_formed_type Gamma T  ->
      well_formed_type Gamma (TCoerce T1 T2 T).

Lemma wf_type_correct : forall Gamma T,
  well_formed_type Gamma T <-> wf_ty Gamma T.
Proof.
  split; intros.
  Case "->".
    induction H; try split; try split; trivial.
  Case "<-".
    generalize dependent Gamma. induction T.
    constructor. simpl in H. trivial.
    constructor; simpl in H; inversion H. apply IHT1. trivial.
      apply IHT2. trivial.
    constructor. simpl in H. apply IHT. trivial.
    constructor; simpl in H; inversion H; inversion H1. apply IHT1. trivial.
      apply IHT2. trivial. apply IHT3. trivial.
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
      well_formed_context (ext_tvar Gamma)
  | WFC_ext_cvar : forall Gamma U V,
      well_formed_context Gamma ->
      well_formed_type Gamma U  ->
      well_formed_type Gamma V  ->
      well_formed_context (ext_cvar Gamma (U, V)).


Inductive subst_context : ty -> nat -> context -> context -> Prop := 
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



(* ################################### *)
(** *** Typing Relation *)

Reserved Notation "Gamma '|-' t ';' T1 '~' T2" (at level 40).
    
Inductive well_formed_coercion (Gamma : context) : cn -> ty -> ty -> Prop :=
  | C_Var : forall x T1 T2,
      well_formed_context Gamma        ->
      get_cvar Gamma x = Some (T1, T2) ->
      Gamma |- CVar x ; T1 ~ T2
  | C_Refl : forall T,
      well_formed_context Gamma ->
      well_formed_type Gamma T  ->
      Gamma |- CRefl ; T ~ T
  | C_Sym : forall c T1 T2,
      Gamma |- c ; T1 ~ T2 ->
      Gamma |- CSym c ; T2 ~ T1
  | C_Trans : forall c1 c2 U V W,
      Gamma |- c1 ; U ~ V ->
      Gamma |- c2 ; V ~ W ->
      Gamma |- CTrans c1 c2 ; U ~ W
  | C_App : forall c1 c2 U1 U2 V1 V2,
      Gamma |- c1 ; U1 ~ V1 ->
      Gamma |- c2 ; U2 ~ V2 ->
      Gamma |- CApp c1 c2 ; (TArrow U1 U2) ~ (TArrow V1 V2)
  | C_Forall : forall c U V,
      ext_tvar Gamma |- c ; U ~ V ->
      Gamma |- CTAbs c ; TUniv U ~ TUniv V
  | C_Left : forall c U1 U2 V1 V2,
      Gamma |- c ; (TArrow U1 U2) ~ (TArrow V1 V2) ->
      Gamma |- CLeft c ; U1 ~ V1
  | C_Right : forall c U1 U2 V1 V2,
      Gamma |- c ; (TArrow U1 U2) ~ (TArrow V1 V2) ->
      Gamma |- CRight c ; U2 ~ V2
  | C_Inst : forall c U V T,
      Gamma |- c ; TUniv U ~ TUniv V ->
      well_formed_type Gamma T       ->
      Gamma |- CTApp c T ; ([0 := T] U) ~ ([0 := T] V)
    
where "Gamma '|-' c ';' T1 '~' T2" := (well_formed_coercion Gamma c T1 T2).



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
      well_formed_type Gamma T2   ->
      well_formed_context Gamma   ->
      Gamma |- ttapp t1 T2 \in [0 := T2] T12
  | T_CAbs : forall Gamma t T1 T2 T,
      Gamma |- t \in T ->
      Gamma |- tcabs T1 T2 t \in TCoerce T1 T2 T
  | T_CApp : forall Gamma U1 U2 T t c,
      Gamma |- t \in (TCoerce U1 U2 T) ->
      Gamma |- c ; U1 ~ U2             ->
      Gamma |- tcapp t c \in T
  | T_Coerce : forall Gamma t c T1 T2,
      Gamma |- c ; T1 ~ T2 ->
      Gamma |- t \in T1    ->
      Gamma |- tcoerce t c \in T2

      
where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var"  | Case_aux c "T_Abs" 
  | Case_aux c "T_App"  | Case_aux c "T_TAbs" 
  | Case_aux c "T_TApp" | Case_aux c "T_CAbs"
  | Case_aux c "T_CApp" | Case_aux c "T_Coerce" ].

Hint Constructors has_type.

End SYSTEMFC.

