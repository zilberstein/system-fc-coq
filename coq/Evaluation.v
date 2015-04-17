Require Export Substitution.
Require Export Shifting.

Module EVALUATION.
Import SYSTEMFC.
Import SHIFTING.
Import SUBSTITUTION.


(* ################################### *)
(** *** Reduction *)


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
         tapp v1 t2 ==> tapp v1 t2'
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
  | E_PushApp : forall v1 v2 c,
         uncoerced_value v1 ->
         value v2 ->
         tapp (tcoerce v1 c) v2 ==>
              tcoerce (tapp v1 (tcoerce v2 (CSym (CNth 1 c)))) (CNth 2 c)
  | E_PushTApp : forall v T c,
         uncoerced_value v        ->
         ttapp (tcoerce v c) T ==>
              tcoerce (ttapp v T) (CTApp c T)
  | E_PushCApp : forall v c c0,
         uncoerced_value v ->
         tcapp (tcoerce v c0) c ==>
               tcoerce (tcapp v (CTrans (CTrans (CNth 1 (CNth 1 c0)) c)
                                        (CSym (CNth 2 (CNth 1 c0)))))
               (CNth 2 c0)

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

End EVALUATION.