Require Export Substitution.
Require Export Typing.

Module EVALUATION.
Import SYSTEMFC.
Import SHIFTING.
Import SUBSTITUTION.
Import TYPING.

(* ################################### *)
(** *** Reduction *)


Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | E_AppAbs : forall T t12 t2,
         (tapp (tabs T t12) t2) ==> [0:=t2]t12
  | E_App : forall t1 t1' t2,
         t1 ==> t1' ->
         tapp t1 t2 ==> tapp t1' t2
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
  | E_CTrans : forall c1 c2 v,
         uncoerced_value v ->
         tcoerce (tcoerce v c1) c2 ==> tcoerce v (CTrans c1 c2)
  | E_PushApp : forall v1 t2 c U1 U2,
         uncoerced_value v1           ->
         empty |- v1 \in TArrow U1 U2 ->
         tapp (tcoerce v1 c) t2 ==>
              tcoerce (tapp v1 (tcoerce t2 (CSym (CNth 1 c)))) (CNth 2 c)
  | E_PushTApp : forall v T c U,
         uncoerced_value v      ->
         empty |- v \in TUniv U ->
         ttapp (tcoerce v c) T ==>
              tcoerce (ttapp v T) (CTApp c T)
  | E_PushCApp : forall v c c0 U1 U2 U,
         uncoerced_value v              ->
         empty |- v \in TCoerce U1 U2 U ->
         tcapp (tcoerce v c0) c ==>
               tcoerce (tcapp v (CTrans (CTrans (CNth 1 c0) c)
                                        (CSym (CNth 3 c0))))
               (CNth 2 c0)

where "t1 '==>' t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_AppAbs"   | Case_aux c "E_App" 
  | Case_aux c "E_TApp" 
  | Case_aux c "E_TAppTAbs" | Case_aux c "E_CApp"
  | Case_aux c "E_CAppCAbs" | Case_aux c "E_Coerce"
  | Case_aux c "E_CTrans"   | Case_aux c "E_PushApp"
  | Case_aux c "E_PushTApp" | Case_aux c "E_PushCApp"
  ].

Hint Constructors step.

Notation multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

End EVALUATION.