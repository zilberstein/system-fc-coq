Require Export Shifting.
Require Export Substitution.

Module TYPING.
Import SYSTEMFC.
Import SHIFTING.
Import SUBSTITUTION.

(* ###################################################################### *)
(** ** Typing *)

(* ################################### *)
(** *** Contexts *)

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


(* ################################### *)
(** *** Well Formed Types *)

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



(* ################################### *)
(** *** Well Formed Contexts *)

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
      subst_context (tshift 0 T) (S n) (ext_tvar Gamma) (ext_tvar Gamma')
  | s_ext_cvar : forall T U1 V1 U2 V2 n Gamma Gamma',
      subst_context T n Gamma Gamma' ->
      subst_type_in_type T n U1 U2   ->
      subst_type_in_type T n V1 V2   ->
      subst_context T n (ext_cvar Gamma (U1, V1)) (ext_cvar Gamma' (U2, V2)).

Hint Constructors subst_context.

(* ################################### *)
(** *** Homogeneity of Types *)

Inductive types_homogenius : ty -> ty -> Prop :=
  | HT_Var : forall X,
      types_homogenius (TVar X) (TVar X)
  | HT_Arrow : forall U1 U2 V1 V2,
      types_homogenius U1 V1 ->
      types_homogenius U2 V2 ->
      types_homogenius (TArrow U1 U2) (TArrow V1 V2)
  | HT_Forall : forall U V,
      types_homogenius U V ->
      types_homogenius (TUniv U) (TUniv V)
  | HT_CAbs : forall U1 U2 U V1 V2 V,
      types_homogenius U1 V1 ->
      types_homogenius U2 V2 ->
      types_homogenius U  V  ->
      types_homogenius (TCoerce U1 U2 U) (TCoerce V1 V2 V).


(* ################################### *)
(** *** Coercion Relation *)

Reserved Notation "Gamma '|-' t ';' T1 '~' T2" (at level 40).
    
Inductive well_formed_coercion (Gamma : context) : cn -> ty -> ty -> Prop :=
  | C_Var : forall x T1 T2,
      well_formed_context Gamma        ->
      get_cvar Gamma x = Some (T1, T2) ->
      types_homogenius T1 T2           ->
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
  | C_App : forall c1 c2 U1 U2 V1 V2 S T,
      Gamma |- c1 ; (TCoerce U1 U2 S) ~ (TCoerce V1 V2 T) ->
      Gamma |- c2 ; U1 ~ U2 ->
      Gamma |- CApp c1 c2 ; S ~ T
  | C_Forall : forall c U V,
      ext_tvar Gamma |- c ; U ~ V ->
      Gamma |- CTAbs c ; TUniv U ~ TUniv V
  | C_ALeft : forall c U1 U2 V1 V2,
      Gamma |- c ; (TArrow U1 U2) ~ (TArrow V1 V2) ->
      Gamma |- CNth 1 c ; U1 ~ V1
  | C_ARight : forall c U1 U2 V1 V2,
      Gamma |- c ; (TArrow U1 U2) ~ (TArrow V1 V2) ->
      Gamma |- CNth 2 c ; U2 ~ V2
  | C_CLeft11 : forall c U1 U2 S V1 V2 T,
      Gamma |- c ; TCoerce U1 U2 S ~ TCoerce V1 V2 T ->
      Gamma |- CNth 1 (CNth 1 c) ; U1 ~ V1 
  | C_CLeft12 : forall c U1 U2 S V1 V2 T,
      Gamma |- c ; TCoerce U1 U2 S ~ TCoerce V1 V2 T ->
      Gamma |- CNth 2 (CNth 1 c) ; U2 ~ V2
  | C_CRight : forall c U1 U2 S V1 V2 T,
      Gamma |- c ; TCoerce U1 U2 S ~ TCoerce V1 V2 T ->
      Gamma |- CNth 2 c ; S ~ T  
  | C_Inst : forall c U V T,
      Gamma |- c ; TUniv U ~ TUniv V ->
      well_formed_type Gamma T       ->
      Gamma |- CTApp c T ; ([0 := T] U) ~ ([0 := T] V)
    
where "Gamma '|-' c ';' T1 '~' T2" := (well_formed_coercion Gamma c T1 T2).

Tactic Notation "coercion_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "C_Var"   | Case_aux c "C_Refl" 
  | Case_aux c "C_Sym"   | Case_aux c "C_Trans" 
  | Case_aux c "C_App"   | Case_aux c "C_Forall"
  | Case_aux c "C_ALeft" | Case_aux c "C_ARight"
  | Case_aux c "C_CLeft11" | Case_aux c "C_CLeft12"
  | Case_aux c "C_CRight"  | Case_aux c "C_Inst" ].

Hint Constructors well_formed_coercion.



(* ################################### *)
(** *** Typing Relation *)

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
      ext_cvar Gamma (T1, T2) |- t \in T ->
      well_formed_type Gamma T1 ->
      well_formed_type Gamma T2 ->
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

End TYPING.