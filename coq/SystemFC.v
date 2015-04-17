(** * System FC **)

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

(* ################################### *)
(** *** Coercions *)

Inductive cn : Type :=
  | CVar   : nat -> cn
  | CRefl  : cn
  | CSym   : cn -> cn
  | CTrans : cn -> cn -> cn
  | CApp   : cn -> cn -> cn
  | CAbs   : cn -> cn
  | CNth   : nat -> cn -> cn
  | CTAbs  : cn -> cn
  | CTApp  : cn -> ty -> cn.

Tactic Notation "c_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "CVar"   | Case_aux c "CRefl"
  | Case_aux c "CSym"   | Case_aux c "CTrans"
  | Case_aux c "CApp"   | Case_aux c "CAbs"
  | Case_aux c "CNth"
  | Case_aux c "CTAbs"  | Case_aux c "CTApp" ].


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


End SYSTEMFC.