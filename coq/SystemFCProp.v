(** * SystemFCProp: Properties of System FC *)

Require Export SubstProp.
Require Export Evaluation.

Module SYSTEMFCPROP.
Import SYSTEMFC.
Import SHIFTING.
Import SUBSTITUTION.
Import TYPING.
Import EVALUATION.
Import SUBSTPROP.

(* ###################################################################### *)
(** * Canonical Forms *)


Lemma canonical_forms_fun : forall t T1 T2,
  empty |- t \in (TArrow T1 T2) ->
  uncoerced_value t ->
  exists u, t = tabs T1 u.
Proof.
  intros t T1 T2 HT HVal.
  inversion HVal; intros; subst; try inversion HT; subst; auto.
  exists t0.  auto.
Qed.

Lemma canonical_forms_tabs : forall t T,
  empty |- t \in TUniv T ->
  uncoerced_value t ->
  exists t', t = ttabs t'.
Proof.
  intros. inversion H0; subst;
  inversion H; subst.
  exists t0. reflexivity.
Qed.

Lemma canonical_forms_cabs : forall t U V T,
  empty |- t \in TCoerce U V T ->
  uncoerced_value t        ->
  exists t', t = tcabs U V t'.
Proof.
  intros; inversion H0; subst; inversion H; subst.
  exists t0. trivial.
Qed.

(* Lemma coercion_unique : forall c Gamma U1 U2 V1 V2, *)
(*   Gamma |- c ; U1 ~ U2 -> *)
(*   Gamma |- c ; V1 ~ V2 -> *)
(*   U1 = V1 /\ U2 = V2. *)
(* Proof. *)
(*   intros; generalize dependent V1; generalize dependent V2; *)
(*   coercion_cases (induction H) Case; inversion H0; subst. *)
(*   Case "C_Var". *)
(*     rewrite H1 in H4. inversion H4. split; trivial. *)
(*   Case "C_Refl". *)
(*     split; trivial. *)
(*   Case "C_Sym". *)
    
Inductive types_consistent : ty -> ty -> Prop :=
  | TC_Arrow : forall U1 U2 V1 V2,
    types_consistent (TArrow U1 U2) (TArrow V1 V2)
  | TC_Univ : forall U V,
    types_consistent (TUniv U) (TUniv V)
  | TC_Coerce : forall U1 U2 U3 V1 V2 V3,
    types_consistent (TCoerce U1 U2 U3) (TCoerce V1 V2 V3).

Fixpoint type_size (T:ty) : nat :=
  match T with
  | TVar _ => 1
  | TArrow T1 T2 => 1 + type_size T1 + type_size T2
  | TUniv T1     => 1 + type_size T1
  | TCoerce T1 T2 T3 => 1 + type_size T1 + type_size T2 + type_size T3
  end.

Fixpoint coercion_size (c:cn) : nat :=
  match c with
  | CVar Y            => 1
  | CRefl T           => 1 + type_size T
  | CSym c            => 1 + coercion_size c
  | CTrans c1 c2      => 1 + coercion_size c1 + coercion_size c2
  | CArrow c1 c2      => 1 + coercion_size c1 + coercion_size c2
  | CTCoerce c1 c2 c3 => 1 + coercion_size c1 + coercion_size c2 +
                         coercion_size c3
  | CNth n c          => 1 + coercion_size c
  | CTAbs c           => 1 + coercion_size c
  | CTApp c T         => 1 + coercion_size c + type_size T
  end.

Lemma ty_size_gt_0 : forall T,
  type_size T > 0.
Proof.
  intros. induction T; simpl; omega.
Qed.

Lemma cn_size_gt_0 : forall c,
  coercion_size c > 0.
Proof.
  intros. induction c; simpl; omega.
Qed.

Lemma cn_size_1 : forall c,
  coercion_size c = 1 ->
  exists X, c = CVar X.
Proof with auto.
  intros. induction c;
  inversion H;
  try (assert (type_size t > 0) by apply ty_size_gt_0; omega);
  try (assert (coercion_size c > 0) by apply cn_size_gt_0; omega);
  try (assert (coercion_size c1 > 0) by apply cn_size_gt_0; omega);
  exists n...
Qed.

Lemma admissibility : forall Gamma c S T,
  (forall n, get_cvar Gamma n = None) ->
  Gamma |- c ; S ~ T ->
  (forall U1 U2 V1 V2,
     S = TArrow U1 U2 /\ T = TArrow V1 V2 ->
     exists c1 c2,
       Gamma |- c1 ; U1 ~ V1 /\
       Gamma |- c2 ; U2 ~ V2 /\
       coercion_size c1 < coercion_size c /\
       coercion_size c2 < coercion_size c) /\
  (forall U V,
     S = TUniv U /\ T = TUniv V ->
     exists c1,
       ext_tvar Gamma |- c1 ; U ~ V /\
       coercion_size c1 < coercion_size c) /\
  (forall U1 U2 U3 V1 V2 V3,
     S = TCoerce U1 U2 U3 /\ T = TCoerce V1 V2 V3 ->
     exists c1 c2 c3,
       Gamma |- c1 ; U1 ~ V1 /\
       Gamma |- c2 ; U2 ~ V2 /\
       Gamma |- c3 ; U3 ~ V3 /\
       coercion_size c1 < coercion_size c /\
       coercion_size c2 < coercion_size c /\
       coercion_size c3 < coercion_size c).
Proof.
  intros.
  coercion_cases (induction H0) Case; subst; split; intros; try split; intros.
  Case "C_Var".
    rewrite H in H1; inversion H1.
    rewrite H in H1; inversion H1.
    rewrite H in H1; inversion H1.
  Case "C_Refl".
    SCase "Arrow".
      inversion H2; subst.
      exists (CRefl U1). exists (CRefl U2).
      inversion H4; subst. inversion H1.
      split. constructor; trivial.
      split. constructor; trivial.
      split; simpl; omega.
    SCase "Univ".
      inversion H2; subst.
      exists (CRefl V).
      inversion H4; subst. inversion H1.
      split. constructor. constructor. trivial. trivial.
      simpl. omega.
    SCase "Coerce".
      inversion H2; subst.
      exists (CRefl U1). exists (CRefl U2). exists (CRefl U3).
      inversion H4; subst. inversion H1; subst.
      split. constructor; trivial.
      split. constructor; trivial.
      split. constructor; trivial.
      split; simpl; omega.
Admitted.

Lemma consistency_sym : forall U V,
  types_consistent U V ->
  types_consistent V U.
Proof.
  intros. inversion H; constructor.
Qed.

Lemma consistency_trans : forall U V W,
  types_consistent U V ->
  types_consistent V W ->
  types_consistent U W.
Proof.
  intros. inversion H; inversion H0; subst; try constructor;
  try inversion H0.
Qed.

Lemma subst_preserves_consistency : forall U V n (T:ty),
  types_consistent U V ->
  types_consistent ([n := T] U) ([n := T] V).
Proof.
  intros. induction H; simpl; constructor.
Qed.

Lemma coercion_consistency : forall Gamma c U V,
  (forall n, get_cvar Gamma n = None) ->
  Gamma |- c ; U ~ V ->
  types_consistent U V.
Proof with eauto.
  intros. remember (coercion_size c) as n.
  generalize dependent c; generalize dependent U; generalize dependent V; 
  generalize dependent Gamma. induction n using strong_induction; intros.
  coercion_cases (inversion H1) Case; subst; try constructor;
  try (apply (admissibility _ _ _ _ H0) in H2; inversion H2; clear H2; clear H4;
       pose proof (H3 _ _ _ _ (conj eq_refl eq_refl));
       destruct H2; destruct H2; destruct H2; destruct H4; destruct H5);
  try (apply (admissibility _ _ _ _ H0) in H2; destruct H2; clear H2;
       destruct H3; clear H2;
       pose proof (H3 _ _ _ _ _ _ (conj eq_refl eq_refl));
       destruct H2; destruct H2; destruct H2; destruct H2; destruct H4;
       destruct H5; destruct H6; destruct H7).
  Case "C_Var".
    inversion H3. rewrite H0 in H5. inversion H5.
  Case "C_Refl".
    admit.
  Case "C_Sym".
    apply consistency_sym. apply H with (coercion_size c0) Gamma c0;
    simpl. omega; trivial. trivial. trivial. trivial.
  Case "C_Trans".
    apply consistency_trans with V0.
    apply H with (coercion_size c1) Gamma c1; try (simpl; omega); trivial. 
    apply H with (coercion_size c2) Gamma c2; try (simpl; omega); trivial.
  Case "C_ALeft".
    apply H with (coercion_size x) Gamma x; try (simpl; omega); trivial. 
  Case "C_ARight".
    apply H with (coercion_size x0) Gamma x0; try (simpl; omega); trivial.
  Case "C_CLeft11".
    apply H with (coercion_size x) Gamma x; try (simpl; omega); trivial.
  Case "C_CLeft12".
    apply H with (coercion_size x0) Gamma x0; try (simpl; omega); trivial.
  Case "C_CRight".
    apply H with (coercion_size x1) Gamma x1; try (simpl; omega); trivial.
  Case "C_Inst".
    apply subst_preserves_consistency.
    apply admissibility in H2. destruct H2. destruct H4. clear H2. clear H5.
    pose proof (H4 _ _ (conj eq_refl eq_refl)). destruct H2.
    destruct H2.
    apply H with (coercion_size x) (ext_tvar Gamma) x; try (simpl; omega); trivial.
    intros. simpl. rewrite H0. trivial. trivial.
Qed.    


Lemma canonical_coercion_abs : forall c T U1 U2,
  (empty |- c ; T ~ TArrow U1 U2 \/
   empty |- c ; TArrow U1 U2 ~ T) ->
  exists V1 V2, T = TArrow V1 V2.
Proof with eauto.
  intros; remember empty as Gamma; remember (TArrow U1 U2) as V.
  generalize dependent U1; generalize dependent U2.
  coercion_cases (induction H) Case; intros...
  Case "C_Var".
    subst; inversion H0.
  Case "C_Sym".
    
 
    pose (IHwell_formed_coercion eq_refl U2 U1).


(* ###################################################################### *)
(** * Progress *)

(** As before, the _progress_ theorem tells us that closed, well-typed
    terms are not stuck: either a well-typed term is a value, or it
    can take an evaluation step.  The proof is a relatively
    straightforward extension of the progress proof we saw in the
    [Types] chapter. *)

Theorem progress : forall t T, 
     empty |- t \in T ->
     value t \/ exists t', t ==> t'.

(** _Proof_: by induction on the derivation of [|- t \in T].

    - The last rule of the derivation cannot be [T_Var], since a
      variable is never well typed in an empty context.

    - The [T_True], [T_False], and [T_Abs] cases are trivial, since in
      each of these cases we know immediately that [t] is a value.

    - If the last rule of the derivation was [T_App], then [t = t1
      t2], and we know that [t1] and [t2] are also well typed in the
      empty context; in particular, there exists a type [T2] such that
      [|- t1 \in T2 -> T] and [|- t2 \in T2].  By the induction
      hypothesis, either [t1] is a value or it can take an evaluation
      step.

        - If [t1] is a value, we now consider [t2], which by the other
          induction hypothesis must also either be a value or take an
          evaluation step.

            - Suppose [t2] is a value.  Since [t1] is a value with an
              arrow type, it must be a lambda abstraction; hence [t1
              t2] can take a step by [ST_AppAbs].

            - Otherwise, [t2] can take a step, and hence so can [t1
              t2] by [ST_App2].

        - If [t1] can take a step, then so can [t1 t2] by [ST_App1].

    - If the last rule of the derivation was [T_If], then [t = if t1
      then t2 else t3], where [t1] has type [Bool].  By the IH, [t1]
      either is a value or takes a step.

        - If [t1] is a value, then since it has type [Bool] it must be
          either [true] or [false].  If it is [true], then [t] steps
          to [t2]; otherwise it steps to [t3].

        - Otherwise, [t1] takes a step, and therefore so does [t] (by
          [ST_If]).
*)

Proof with eauto.
  intros t T Ht.
  remember (@empty) as Gamma.
  has_type_cases (induction Ht) Case; subst Gamma...
  Case "T_Var".
    (* contradictory: variables cannot be typed in an 
       empty context *)
    inversion H0.

  Case "T_App". 
    (* [t] = [t1 t2].  Proceed by cases on whether [t1] is a 
       value or steps... *)
    right. destruct IHHt1...
    SCase "t1 is a value".
      destruct IHHt2...
      SSCase "t2 is also a value".
        destruct H...
        SSSCase "t1 is an uncoerced value".
          assert (exists t0, t = tabs T11 t0).
          eapply canonical_forms_fun; eauto.
          destruct H1 as [t0 Heq]. subst.
          exists ([0:=t2]t0)...

      SSCase "t2 steps".
        inversion H0 as [t2' Hstp]. exists (tapp t1 t2')...

    SCase "t1 steps".
      inversion H as [t1' Hstp]. exists (tapp t1' t2)...
      
  Case "T_TApp".
    right. destruct IHHt...    
    SCase "t1 is a value".
      destruct H1...
      SSCase "t1 is uncoerced".
        assert (exists t0, t = ttabs t0).
        eapply canonical_forms_tabs; eauto.
        destruct H2; subst.
        exists ([0 := T2] x)...

    SCase "t1 also steps".
      inversion H1. exists (ttapp x T2)...

  Case "T_CApp".
    right. destruct IHHt...
    SCase "t is a value".
      destruct H0...
      SSCase "t is uncoerced".
        assert (exists t0, t = tcabs U1 U2 t0).
        eapply canonical_forms_cabs...
        destruct H1; subst. exists ([0:=c] x)...

SCase "t steps".
      inversion H0. exists (tcapp x c)...

  Case "T_Coerce".
    destruct IHHt...
    SCase "t is a value".
      destruct H0...
    SCase "t steps". 
      right. inversion H0. exists (tcoerce x c)...
Qed.


(* [] *)

(* ###################################################################### *)
(** * Preservation *)

(** The other half of the type soundness property is the preservation
    of types during reduction.  For this, we need to develop some
    technical machinery for reasoning about variables and
    substitution.  Working from top to bottom (the high-level property
    we are actually interested in to the lowest-level technical lemmas
    that are needed by various cases of the more interesting proofs),
    the story goes like this:

      - The _preservation theorem_ is proved by induction on a typing
        derivation, pretty much as we did in the [Types] chapter.  The
        one case that is significantly different is the one for the
        [ST_AppAbs] rule, which is defined using the substitution
        operation.  To see that this step preserves typing, we need to
        know that the substitution itself does.  So we prove a...

      - _substitution lemma_, stating that substituting a (closed)
        term [s] for a variable [x] in a term [t] preserves the type
        of [t].  The proof goes by induction on the form of [t] and
        requires looking at all the different cases in the definition
        of substitition.  This time, the tricky cases are the ones for
        variables and for function abstractions.  In both cases, we
        discover that we need to take a term [s] that has been shown
        to be well-typed in some context [Gamma] and consider the same
        term [s] in a slightly different context [Gamma'].  For this
        we prove a...

      - _context invariance_ lemma, showing that typing is preserved
        under "inessential changes" to the context [Gamma] -- in
        particular, changes that do not affect any of the free
        variables of the term.  For this, we need a careful definition
        of

      - the _free variables_ of a term -- i.e., the variables occuring
        in the term that are not in the scope of a function
        abstraction that binds them.
*)


(* ###################################################################### *)
(** ** Substitution *)

(** We first need a technical lemma connecting free variables and
    typing contexts.  If a variable [x] appears free in a term [t],
    and if we know [t] is well typed in context [Gamma], then it must
    be the case that [Gamma] assigns a type to [x]. *)

    


(** The substitution lemma can be viewed as a kind of "commutation"
    property.  Intuitively, it says that substitution and typing can
    be done in either order: we can either assign types to the terms
    [t] and [v] separately (under suitable contexts) and then combine
    them using substitution, or we can substitute first and then
    assign a type to [ [x:=v] t ] -- the result is the same either
    way. *)

(* ###################################################################### *)
(** ** Main Theorem *)

(** We now have the tools we need to prove preservation: if a closed
    term [t] has type [T], and takes an evaluation step to [t'], then [t']
    is also a closed term with type [T].  In other words, the small-step
    evaluation relation preserves types.
*)

Lemma preservation_app_abs : forall Gamma t12 t2 T11 U,
  Gamma |- tapp (tabs T11 t12) t2 \in U ->
  Gamma |- [0 := t2] t12 \in U.
Proof.
  intros. remember (tapp (tabs T11 t12) t2) as t.
  induction H; try discriminate.
    inversion Heqt; subst.
    inversion H; subst.
    eapply substitution_preserves_typing_term_term 
    with (ext_var Gamma T0) 0 T0 t12 t2 T12 in H3.
    simpl in H3. trivial. simpl. trivial. simpl. trivial.
Qed.


Lemma preservation_tapp_tabs : forall Gamma t12 T2 U,
  Gamma |- ttapp (ttabs t12) T2 \in U ->
  Gamma |- [0 := T2] t12 \in U.
Proof.
  intros. remember (ttapp (ttabs t12) T2) as t.
  induction H; try discriminate.
    inversion Heqt; subst.
    inversion H; subst.
    eapply subst_typ_preserves_typing. trivial.
    trivial.
Qed.

Lemma preservation_capp_cabs : forall Gamma t12 c T1 T2 U,
  Gamma |- tcapp (tcabs T1 T2 t12) c \in U ->
  Gamma |- [0 := c] t12 \in U.
Proof.                               
  intros. remember (tcapp (tcabs T1 T2 t12) c) as t.
  induction H; try discriminate.
    inversion Heqt; subst.
    inversion H; subst.
    eapply cn_substitution_preserves_typing with (x:=0) in H6.
    simpl in H6. eassumption.
    simpl. eassumption. simpl. trivial.
Qed.


Theorem preservation : forall Gamma t t' T,
     Gamma |- t \in T  ->
     t ==> t'  ->
     Gamma |- t' \in T.

(** _Proof_: by induction on the derivation of [|- t \in T].

    - We can immediately rule out [T_Var], [T_Abs], [T_True], and
      [T_False] as the final rules in the derivation, since in each of
      these cases [t] cannot take a step.

    - If the last rule in the derivation was [T_App], then [t = t1
      t2].  There are three cases to consider, one for each rule that
      could have been used to show that [t1 t2] takes a step to [t'].

        - If [t1 t2] takes a step by [ST_App1], with [t1] stepping to
          [t1'], then by the IH [t1'] has the same type as [t1], and
          hence [t1' t2] has the same type as [t1 t2].

        - The [ST_App2] case is similar.

        - If [t1 t2] takes a step by [ST_AppAbs], then [t1 =
          \x:T11.t12] and [t1 t2] steps to [[x:=t2]t12]; the
          desired result now follows from the fact that substitution
          preserves types.

    - If the last rule in the derivation was [T_If], then [t = if t1
      then t2 else t3], and there are again three cases depending on
      how [t] steps.

        - If [t] steps to [t2] or [t3], the result is immediate, since
          [t2] and [t3] have the same type as [t].

        - Otherwise, [t] steps by [ST_If], and the desired conclusion
          follows directly from the induction hypothesis.
*)

Proof with eauto.
  intros Gamma t t' T HT. generalize dependent t'.   
  has_type_cases (induction HT) Case;
       intros t' HE; 
       try solve [inversion HE; subst; auto].
  Case "T_App".
    inversion HE; subst...
    (* Most of the cases are immediate by induction, 
       and [eauto] takes care of them *)
    SCase "ST_AppAbs".
      eapply preservation_app_abs.
      inversion HT1... 
    SCase "ST_PushApp".
      inversion HT1; subst. remember H4 as Hy. clear HeqHy.
      apply coercion_homogeneity in H4. inversion H4; subst.
      econstructor. econstructor. eassumption.
      econstructor. eassumption. econstructor. econstructor. econstructor.
      eassumption. trivial.
  Case "T_TApp".
    inversion HE; subst...
    SCase "ST_TAppTAbs".
      inversion HT; subst. apply preservation_tapp_tabs. constructor. trivial.
      trivial. trivial. 
    SCase "ST_PushTApp".
      inversion HT; subst. remember H5 as Hy; clear HeqHy.
      apply coercion_homogeneity in H5. inversion H5; subst. 
      econstructor. econstructor. eassumption. trivial. constructor.
      trivial. trivial. trivial.
  Case "T_CApp".
    inversion HE; subst...
    SCase "ST_CAppCAbs".
      eapply preservation_capp_cabs...
    SCase "ST_PushCApp".
      inversion HT; subst. remember H4 as Hy; clear HeqHy.
      apply coercion_homogeneity in H4.
      inversion H4.  subst.
      econstructor. eapply C_CRight. eassumption.
      econstructor. eassumption. econstructor. econstructor. eapply C_CLeft11.
      eassumption. eassumption. econstructor. eapply C_CLeft12. eassumption.
  Case "T_Coerce".
    inversion HE; subst...
    SCase "ST_CTrans".
      inversion HT. econstructor. econstructor. eassumption. trivial.
      trivial.
Qed.

(* ###################################################################### *)
(** * Type Soundness *)

(** Put progress and preservation together and show that a well-typed
    term can _never_ reach a stuck state.  *)

Definition normal_form {X:Type} (R:relation X) (t:X) : Prop :=
  ~ exists t', R t t'.

Definition stuck (t:tm) : Prop :=
  (normal_form step) t /\ ~ value t.

Corollary soundness : forall t t' T,
  empty |- t \in T -> 
  t ==>* t' ->
  ~(stuck t').
Proof.
  intros t t' T Hhas_type Hmulti. unfold stuck.
  intros [Hnf Hnot_val]. unfold normal_form in Hnf.
  induction Hmulti.
  assert (value x \/ exists t', x ==> t')
    by (eapply progress; apply Hhas_type); inversion H.
  Case "Hmulti 1".
    apply Hnot_val. assumption.
    apply Hnf; assumption.
  Case "Hmulti 2".
    apply IHHmulti. eapply preservation. apply Hhas_type.
    assumption. assumption. assumption.
Qed.

End SYSTEMFCPROP.