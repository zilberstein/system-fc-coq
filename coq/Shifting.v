(** * Shifting in System FC *)
Require Export SystemFC.

Module SHIFTING.
Import SYSTEMFC.

(* ################################### *)
(** *** Types *)

(* Types in Types *)
Fixpoint tshift (X : nat) (T : ty) : ty :=
  match T with
  | TVar Y          => TVar (if le_gt_dec X Y then 1 + Y else Y)
  | TArrow T1 T2    => TArrow (tshift X T1) (tshift X T2)
  | TUniv T2        => TUniv (tshift (1 + X) T2)
  | TCoerce T1 T2 T => TCoerce (tshift X T1) (tshift X T2) (tshift X T) 
  end.

(* ################################### *)
(** *** Coercions *)

(* Coercions in Coercions *)
Fixpoint cshift (X : nat) (c : cn) : cn :=
  match c with
  | CVar Y            => CVar (if le_gt_dec X Y then 1 + Y else Y)
  | CRefl T           => CRefl T
  | CSym c            => CSym (cshift X c)
  | CTrans c1 c2      => CTrans (cshift X c1) (cshift X c2)
  | CArrow c1 c2      => CArrow (cshift X c1) (cshift X c2)
  | CTCoerce c1 c2 c3 => CTCoerce (cshift X c1) (cshift X c2) (cshift X c3)
  | CNth n c          => CNth n (cshift X c)
  | CTAbs c           => CTAbs (cshift X c)
  | CTApp c T         => CTApp (cshift X c) T
  end.

(* Types in Coercions *)
Fixpoint cshift_typ (X : nat) (c : cn) : cn :=
  match c with
  | CVar Y            => CVar Y
  | CRefl T           => CRefl (tshift X T)
  | CSym c            => CSym (cshift_typ X c)
  | CTrans c1 c2      => CTrans (cshift_typ X c1) (cshift_typ X c2)
  | CArrow c1 c2      => CArrow (cshift_typ X c1) (cshift_typ X c2)
  | CTCoerce c1 c2 c3 => CTCoerce (cshift_typ X c1) (cshift_typ X c2)
                                  (cshift_typ X c3)
  | CNth n c          => CNth n (cshift_typ X c)
  | CTAbs c           => CTAbs (cshift_typ (S X) c)
  | CTApp c T         => CTApp (cshift_typ X c) (tshift X T)
  end.

(* ################################### *)
(** *** Terms *)

(* Terms in Terms *)
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

(* Coercions in Terms *)
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

(* Types in Terms *)
Fixpoint shift_typ (X : nat) (t : tm) {struct t} : tm :=
  match t with
    | tvar y         => tvar y
    | tabs T1 t2     => tabs (tshift X T1) (shift_typ X t2)
    | tapp t1 t2     => tapp (shift_typ X t1) (shift_typ X t2)
    | ttabs t2       => ttabs (shift_typ (1 + X) t2)
    | ttapp t1 T2    => ttapp (shift_typ X t1) (tshift X T2)
    | tcapp t1 c2    => tcapp (shift_typ X t1) (cshift_typ X c2)
    | tcabs T1 T2 t2 => tcabs (tshift X T1) (tshift X T2) (shift_typ X t2)
    | tcoerce t1 c2  => tcoerce (shift_typ X t1) (cshift_typ X c2)
  end.

End SHIFTING.