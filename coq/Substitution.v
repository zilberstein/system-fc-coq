Require Export Shifting.

(* ###################################################################### *)
(** *** Substitution *)

Module SUBSTITUTION.
Import SYSTEMFC.
Import SHIFTING.

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
    | CRefl T      => CRefl T
    | CSym c       => CSym (subst_coercion_fix x d c)
    | CTrans c1 c2 => CTrans (subst_coercion_fix x d c1) (subst_coercion_fix x d c2)
    | CArrow c1 c2   => CArrow (subst_coercion_fix x d c1) (subst_coercion_fix x d c2)
    | CTCoerce c1 c2 c3 => CTCoerce (subst_coercion_fix x d c1)
                                    (subst_coercion_fix x d c2)
                                    (subst_coercion_fix x d c3)
    | CNth n c     => CNth n (subst_coercion_fix x d c)
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
  | sc_refl : forall d x T,
      subst_coercion d x (CRefl T) (CRefl T)
  | sc_sym : forall d x c c',
      subst_coercion d x c c' ->
      subst_coercion d x (CSym c) (CSym c')
  | sc_trans : forall d x c1 c1' c2 c2',
      subst_coercion d x c1 c1' ->
      subst_coercion d x c2 c2' ->
      subst_coercion d x (CTrans c1 c2) (CTrans c1' c2')
  | sc_carrow : forall d x c1 c1' c2 c2',
      subst_coercion d x c1 c1' ->
      subst_coercion d x c2 c2' ->
      subst_coercion d x (CArrow c1 c2) (CArrow c1' c2')
  | sc_ctcoerce : forall d x c1 c1' c2 c2' c3 c3',
      subst_coercion d x c1 c1' ->
      subst_coercion d x c2 c2' ->
      subst_coercion d x c3 c3' ->
      subst_coercion d x (CTCoerce c1 c2 c3) (CTCoerce c1' c2' c3')
  | sc_nth : forall d x n c c',
      subst_coercion d x c c' ->
      subst_coercion d x (CNth n c) (CNth n c')
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
    SCase "c = CArrow c1 c2".
      rewrite <- H. constructor.
      apply IHc1. trivial.
      apply IHc2. trivial.
    SCase "c = CTCoerce c1 c2 c3".
      rewrite <- H. constructor.
      apply IHc1. trivial.
      apply IHc2. trivial.
      apply IHc3. trivial.
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
    | CRefl T      => CRefl ([X := U] T)
    | CSym c       => CSym (subst_ty_in_cn_fix X U c)
    | CTrans c1 c2 => CTrans (subst_ty_in_cn_fix X U c1)
                             (subst_ty_in_cn_fix X U c2)
    | CArrow c1 c2 => CArrow (subst_ty_in_cn_fix X U c1)
                             (subst_ty_in_cn_fix X U c2)
    | CTCoerce c1 c2 c3 => CTCoerce (subst_ty_in_cn_fix X U c1)
                                    (subst_ty_in_cn_fix X U c2)
                                    (subst_ty_in_cn_fix X U c3)
    | CNth n c     => CNth n (subst_ty_in_cn_fix X U c)
    | CTAbs c      => CTAbs (subst_ty_in_cn_fix (S X) (tshift 0 U) c)
    | CTApp c T    => CTApp (subst_ty_in_cn_fix X U c) ([X := U] T)
  end.

Instance subst_ty_cn : Subst nat ty cn := {
  do_subst := subst_ty_in_cn_fix
}.

Inductive subst_ty_in_cn (T:ty) (X:nat) : cn -> cn -> Prop :=
  | stc_var : forall x,
      subst_ty_in_cn T X (CVar x) (CVar x)
  | stc_refl : forall U U',
      subst_type_in_type T X U U' ->
      subst_ty_in_cn T X (CRefl U) (CRefl U')
  | stc_sym : forall c c',
      subst_ty_in_cn T X c c' ->
      subst_ty_in_cn T X (CSym c) (CSym c')
  | stc_trans : forall c1 c1' c2 c2',
      subst_ty_in_cn T X c1 c1' ->
      subst_ty_in_cn T X c2 c2' ->
      subst_ty_in_cn T X (CTrans c1 c2) (CTrans c1' c2')
  | stc_carrow : forall c1 c1' c2 c2',
      subst_ty_in_cn T X c1 c1' ->
      subst_ty_in_cn T X c2 c2' ->
      subst_ty_in_cn T X (CArrow c1 c2) (CArrow c1' c2')
  | stc_ctcoerce : forall c1 c1' c2 c2' c3 c3',
      subst_ty_in_cn T X c1 c1' ->
      subst_ty_in_cn T X c2 c2' ->
      subst_ty_in_cn T X c3 c3' ->
      subst_ty_in_cn T X (CTCoerce c1 c2 c3) (CTCoerce c1' c2' c3')
  | stc_nth : forall c c' n,
      subst_ty_in_cn T X c c' ->
      subst_ty_in_cn T X (CNth n c) (CNth n c')
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
      try (subst; constructor; apply IHc; trivial);
      try (rewrite <- H; constructor);
      try (apply IHc; trivial);
      try (apply IHc1; trivial);
      try (apply IHc2; trivial);
      try (apply IHc3; trivial);
      try (apply subst_type_in_type_correct; trivial).
  Case "<-".
    intro H. induction H; simpl;
    subst; try reflexivity; try assumption;
    try (apply subst_type_in_type_correct in H; subst; trivial);
    try (apply subst_type_in_type_correct in H0; subst; trivial).
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
      ttabs (subst_cn_in_tm_fix x (cshift_typ 0 c) t1) 
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
      subst_cn_in_tm (cshift_typ 0 c) x t t' ->
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

End SUBSTITUTION.