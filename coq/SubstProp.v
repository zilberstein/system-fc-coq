Require Export Typing.
Require Export Coq.Logic.Decidable.

Module SUBSTPROP.
Import SYSTEMFC.
Import SHIFTING.
Import SUBSTITUTION.
Import TYPING.

Lemma context_subst_ge : forall Gamma Gamma' X X' T,
  X' < X ->
  subst_context T X' Gamma Gamma' ->
  get_tvar Gamma' (X - 1) = get_tvar Gamma X. 
Proof.
  intros. generalize dependent X. induction H0; intros.
    simpl. apply IHsubst_context. trivial.
    induction X. inversion H1.
      simpl. assert (X - 0 = X) by omega. rewrite H2.
      trivial.
    inversion H; subst. simpl. 
    assert (get_tvar Gamma' (S n - 1) = get_tvar Gamma (S n)).
      apply IHsubst_context. omega.
    assert (S n - 1 = n) by omega. rewrite H2 in H1.
    trivial.
    simpl. destruct m. inversion H1.
    simpl. assert (get_tvar Gamma' (S m - 1) = get_tvar Gamma (S m)).
      apply IHsubst_context. omega. assert (S m - 1 = m) by omega.
      rewrite H3 in H2. trivial.
    simpl. apply IHsubst_context. trivial.
Qed.

Lemma context_subst_lt : forall Gamma Gamma' X X' T,
  X' > X ->
  subst_context T X' Gamma Gamma' ->
  get_tvar Gamma' X = get_tvar Gamma X. 
Proof.
  intros. generalize dependent X. induction H0; intros.
    simpl. apply IHsubst_context. trivial.
    inversion H1.
    induction X. simpl. trivial.
    simpl. apply IHsubst_context. omega.
    simpl. apply IHsubst_context. omega.
Qed.


Lemma wf_type_context_weaken : forall T Gamma Gamma',
  (forall X, get_tvar Gamma' X = false -> get_tvar Gamma X = false) ->
  well_formed_type Gamma T -> well_formed_type Gamma' T.
Proof.
  intro T. induction T; intros.
  Case "TVar".
    constructor. inversion H0; subst.
    assert (get_tvar Gamma' n = false -> get_tvar Gamma n = false) by apply H.
    rewrite <- contrapositive in H1. 
  apply not_false_is_true. intro. apply not_false_iff_true in H2. apply H1.
  apply H2. apply H3. right. apply not_false_iff_true. trivial.
  Case "TArrow T1 T2".
    constructor; inversion H0. eapply IHT1. intros. apply H. trivial. trivial.
    eapply IHT2. intros. apply H. trivial. trivial.
  Case "TUniv".
    constructor; inversion H0. apply IHT with (ext_tvar Gamma). intros. 
    induction X. simpl in H3. inversion H3.
      simpl in H3. simpl. apply H. trivial.
    trivial.
  Case "TCoerce".
    constructor; inversion H0. subst. 
    eapply IHT1. intros. apply H. trivial. trivial.
    eapply IHT2. intros. apply H. trivial. trivial.
    eapply IHT3. intros. apply H. trivial. trivial.    
Qed.

Lemma context_invariance_types : forall T Gamma Gamma',
  (forall X, get_tvar Gamma' X = get_tvar Gamma X) ->
  well_formed_type Gamma T -> well_formed_type Gamma' T.
Proof.
  intros T Gamma Gamma' H. eapply wf_type_context_weaken. intros.
  rewrite <- H. trivial. 
Qed.    

Lemma wf_weakening_var : forall Gamma U T,
  well_formed_type Gamma U ->
  well_formed_type (ext_var Gamma T) U.
Proof.  
  intros. eapply context_invariance_types with Gamma. intros. 
  simpl. trivial. trivial.
Qed.

Lemma wf_strengthening_var : forall Gamma U T,
  well_formed_type (ext_var Gamma T) U ->
  well_formed_type Gamma U.
Proof.
  intros. apply context_invariance_types with (ext_var Gamma T). intros.
  simpl. trivial. trivial.
Qed.

Lemma larger_context_true : forall Gamma X,
  get_tvar Gamma X = true ->
  get_tvar (ext_tvar Gamma) X = true.
Proof.
  intros. generalize dependent X. induction Gamma; intros.
    inversion H.
    assert ((get_tvar (ext_tvar (ext_var Gamma t)) X = true) =
            (get_tvar (ext_tvar Gamma) X = true)) by trivial.
    rewrite H0. apply IHGamma. simpl in H. trivial.
    destruct X. trivial.
    apply IHGamma. simpl in H. trivial.
    destruct X. trivial.
    simpl in H. apply IHGamma in H. simpl. simpl in H. trivial.
Qed.

Lemma wf_weakening_tvar : forall Gamma U,
  well_formed_type Gamma U ->
  well_formed_type (ext_tvar Gamma) (tshift 0 U).
Proof.
  intros. generalize 0. generalize dependent Gamma. induction U; intros;
    inversion H. constructor. destruct (le_gt_dec n0 n).
      simpl. trivial.
      apply larger_context_true. trivial.
    simpl. constructor. apply IHU1. trivial.
      apply IHU2. trivial.
    simpl. constructor. apply IHU. trivial.
    simpl. constructor. apply IHU1; trivial. apply IHU2; trivial.
      apply IHU3; trivial.
Qed.
 

 (* The next two tactics come from the POPL paper *)
 Ltac tvar_case :=
   unfold tshift; unfold do_subst; fold tshift; fold do_subst;
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
     | simpl; try (apply f_equal2 with (f := TArrow); trivial)
     | simpl
     | simpl ].
 (* ; apply f_equal2 with (f := TUniv); trivial ]. *)

 Lemma subst_shift_same : forall X T U,
   T = [X := U] (tshift X T).
 Proof.
   intros. generalize dependent X. generalize dependent U.
   induction T; intros.
     simpl. destruct (le_gt_dec X n).
       destruct (eq_nat_dec X (S n)).
         omega.
       destruct (le_lt_dec X (S n)). assert (n = S n - 1) by omega. auto.
         omega.
       destruct (eq_nat_dec X n).
         omega.
         destruct (le_lt_dec X n). omega. trivial.
     simpl. simpl in IHT1. rewrite <- IHT1. simpl in IHT2; rewrite <- IHT2. trivial.
     simpl. simpl in IHT. assert (S X = X + 1) by omega. rewrite H.
       rewrite <- IHT. trivial.
     simpl. rewrite <- IHT1. rewrite <- IHT2. rewrite <- IHT3. trivial.
 Qed.

 Lemma tshift_tshift_prop : forall X Y T,
   tshift X (tshift (X + Y) T) = tshift (1 + X + Y) (tshift X T).
 Proof.
   intros. common_cases X T.
   rewrite IHT. trivial. 
   rewrite IHT1. rewrite IHT2. rewrite IHT3. trivial.
 Qed.

 Lemma tshift_subst_prop : forall X Y T U,
   tshift X ([X + Y := U] T) =
   [S (X + Y) := tshift X U] (tshift X T).
 Proof.
   intros. generalize dependent U. common_cases X T. intros.
   simpl. destruct (eq_nat_dec (n'' + Y) n). simpl. trivial.
   destruct (le_lt_dec (n'' + Y) n). simpl.
   destruct (le_gt_dec n'' (n - 1)). assert (S (n - 1) = n - 0) by omega.
     rewrite H. trivial. omega. 
     simpl. destruct (le_gt_dec n'' n). trivial. omega.
   intros. destruct (eq_nat_dec (n'' + Y) n). omega.
     destruct (le_lt_dec (n'' + Y) n). omega.
     simpl. destruct (le_gt_dec n'' n). omega.
     destruct
       (match n as n1 return ({S (n'' + Y) = n1} + {S (n'' + Y) <> n1}) with
          | 0 => right (not_eq_sym (O_S (n'' + Y)))                           
          | S m =>                                                     
            sumbool_rec                                                     
              (fun _ : {n'' + Y = m} + {n'' + Y <> m} =>                    
                 {S (n'' + Y) = S m} + {S (n'' + Y) <> S m})                  
              (fun a : n'' + Y = m => left (f_equal S a))                   
              (fun b : n'' + Y <> m => right (not_eq_S (n'' + Y) m b))      
              (eq_nat_dec (n'' + Y) m)                                      
        end). omega. 
     destruct (le_gt_dec (S (n'' + Y)) n). omega.
     destruct n. trivial. simpl. unfold sumbool_rec. unfold sumbool_rect.
     destruct (le_lt_dec (n'' + Y) n). omega. trivial.
     apply f_equal. assert (n'' + Y + 1 = S n'' + Y) by omega. rewrite H.
     assert (tshift 0 (tshift (0 + n'') U) = tshift (1 + 0 + n'') (tshift 0 U))
       by (apply tshift_tshift_prop).
     simpl in H0. rewrite H0.
     rewrite IHT. trivial.
     rewrite IHT1. rewrite IHT2. rewrite IHT3. trivial.
 Qed.

Lemma tshift_subst_prop_2 : forall n n' T T',
  (tshift (n + n') ([n := T'] T)) =
  ([n := (tshift (n + n') T')] (tshift (1 + n + n') T)).
Proof.
  intros. generalize dependent T'. common_cases n T. intros.
  destruct (eq_nat_dec n'' n). omega.
    destruct (le_lt_dec n'' n).
      destruct (eq_nat_dec n'' (S n)).
        omega.
        destruct (le_lt_dec n'' (S n)).
          simpl. destruct (le_gt_dec (n'' + n') (n - 1)).
          assert (S (n - 1) = n - 0) by omega. rewrite H. trivial.
          omega.
        omega.
      omega.
    intros.
    destruct (eq_nat_dec n'' n).
      trivial.
      destruct (le_lt_dec n'' n).
        simpl. destruct (le_gt_dec (n'' + n') (n - 1)).
          omega.
          trivial.
        simpl.
      destruct (le_gt_dec (n'' + n') n).
        omega.
        trivial.
    apply f_equal. assert (n'' + n' = 0 + (n'' + n')) by trivial.
    rewrite H. rewrite tshift_tshift_prop. simpl.
    assert (S (n'' + n') = (n'' + 1) + n') by omega.
    rewrite H0. apply IHT.
    rewrite IHT1. rewrite IHT2. rewrite IHT3. trivial.
Qed.

 Lemma context_subst_get_var : forall X Y Gamma Gamma' U,
  subst_context U Y Gamma Gamma' ->
  get_var Gamma' X = opt_map (fun T => [Y := U] T) (get_var Gamma X).
Proof.
   intros. generalize dependent X. induction H; intros. 
     simpl. destruct X.
       simpl. apply subst_type_in_type_correct in H0. rewrite <- H0.
       trivial.
       apply IHsubst_context.
     simpl. induction (get_var Gamma X).
       simpl. apply f_equal. apply subst_shift_same. trivial.
     simpl. rewrite IHsubst_context. induction (get_var Gamma X).
       simpl. apply f_equal. assert (S n = S (0 + n)) by omega. rewrite H0.
       assert (subst_type_in_type_fix n T a = [0 + n := T] a) by trivial.
       rewrite H1. apply tshift_subst_prop. trivial.
     simpl. apply IHsubst_context.
 Qed.

Lemma context_subst_get_cvar : forall X Y Gamma Gamma' U,
  subst_context U Y Gamma Gamma' ->
  get_cvar Gamma' X = opt_map_prod (fun T => [Y := U] T) (get_cvar Gamma X).
Proof.
   intros. generalize dependent X. induction H; intros. 
   Case "ext_var".  
     simpl. apply IHsubst_context.
   Case "ext_tvar".
     simpl. induction (get_cvar Gamma X).
       simpl. destruct a. simpl. apply f_equal.
       assert (t = subst_type_in_type_fix 0 T (tshift 0 t)) by
           (apply subst_shift_same). rewrite <- H1; clear H1.
       assert (t0 = subst_type_in_type_fix 0 T (tshift 0 t0)) by
           (apply subst_shift_same). rewrite <- H1; clear H1.
       trivial.
       simpl. trivial.
       simpl. rewrite IHsubst_context. induction (get_cvar Gamma X).
         simpl. assert (S n = S (0 + n)) by omega. rewrite H0. destruct a.
         simpl. 
         assert (forall t, subst_type_in_type_fix n T t = [0 + n := T] t) by trivial.
         rewrite H1. rewrite tshift_subst_prop. trivial. rewrite H1.
         rewrite tshift_subst_prop. trivial.
         simpl. trivial.     
     Case "ext_cvar".
       simpl. destruct X.
         simpl. apply subst_type_in_type_correct in H0. rewrite <- H0.
         apply subst_type_in_type_correct in H1. rewrite <- H1.
         trivial.
       apply IHsubst_context.
 Qed.


 Lemma tsubst_tsubst_prop : forall X Y (T U V : ty),
   [X + Y := V] ([X := U] T) =
   [X := [X + Y := V] U] ([1 + X + Y := tshift X V] T).
 Proof.
   intros X Y T. common_cases X T. 
   destruct (eq_nat_dec n'' n). 
   destruct n. simpl. destruct (eq_nat_dec n'' 0).
   trivial. omega.
   unfold sumbool_rec. unfold sumbool_rect.
   destruct (eq_nat_dec (n'' + Y) n). omega.
   destruct (le_lt_dec (n'' + Y) n). omega. simpl.
   destruct (eq_nat_dec n'' (S n)).
   trivial. omega.
   destruct (le_lt_dec n'' n). simpl.
   destruct (eq_nat_dec (n'' + Y) (n - 1)). destruct n.
   omega. unfold sumbool_rec. unfold sumbool_rect.
   destruct (eq_nat_dec (n'' + Y) n). subst.
   apply subst_shift_same. simpl. omega.
   destruct (le_lt_dec (n'' + Y) (n - 1)).
   unfold sumbool_rec. unfold sumbool_rect. destruct n. simpl.
   omega. simpl. destruct (eq_nat_dec (n'' + Y) n). omega.
   simpl. destruct (le_lt_dec (n'' + Y) n). simpl.
   destruct (eq_nat_dec n'' (n - 0) ). omega. simpl.
   destruct (le_lt_dec n'' (n - 0)). trivial. omega. omega.
   destruct (match n as n2 return ({S (n'' + Y) = n2} + {S (n'' + Y) <> n2}) with
               | 0 => right (not_eq_sym (O_S (n'' + Y)))
               | S m =>
                 sumbool_rec
                   (fun _ : {n'' + Y = m} + {n'' + Y <> m} =>
                      {S (n'' + Y) = S m} + {S (n'' + Y) <> S m})
                   (fun a : n'' + Y = m => left (f_equal S a))
                   (fun b : n'' + Y <> m => right (not_eq_S (n'' + Y) m b))
                   (eq_nat_dec (n'' + Y) m)
             end).
   omega. unfold sumbool_rec. unfold sumbool_rect. destruct n. omega.
   destruct (le_lt_dec (n'' + Y) n). omega. simpl.
   destruct (eq_nat_dec n'' (S n)). omega.
   destruct (le_lt_dec n'' (S n)). trivial. omega. simpl.
   destruct (eq_nat_dec (n'' + Y) n). unfold sumbool_rec. unfold sumbool_rect.
   destruct n. simpl. destruct (eq_nat_dec n'' 0). omega.
   destruct (le_lt_dec n'' 0). omega. omega. simpl. omega.
   destruct (le_lt_dec (n'' + Y) n). omega.
   unfold sumbool_rec. unfold sumbool_rect. destruct n. simpl.
   destruct (eq_nat_dec n'' 0). omega.
   destruct (le_lt_dec n'' 0). trivial. trivial. 
   destruct (eq_nat_dec (n'' + Y) n). omega.
   destruct (le_lt_dec (n'' + Y) n). omega. simpl.
   destruct (eq_nat_dec n'' (S n)). omega.
   destruct (le_lt_dec n'' (S n)). omega. trivial.

   assert (n'' + Y = 0 + (n'' + Y)) by trivial. rewrite H. clear H. 
   rewrite tshift_subst_prop. simpl.
   assert (n'' = 0 + n'') by trivial. rewrite H. clear H.
   rewrite tshift_tshift_prop. simpl. 
   assert (n'' + Y + 1 = n'' + 1 + Y) by omega. rewrite H. clear H.
   rewrite IHT.
   assert (n'' + 1 = S n'') by omega. rewrite H. clear H.
   trivial.
   rewrite IHT1. rewrite IHT2. rewrite IHT3. trivial.
Qed.

Inductive insert_tvar : nat -> context -> context -> Prop :=
  | it_here : forall T Gamma,
      well_formed_type Gamma T ->
      insert_tvar 0 Gamma (ext_tvar Gamma)
  | it_var : forall X T Gamma Gamma',
      insert_tvar X Gamma Gamma' ->
      insert_tvar X (ext_var Gamma T) (ext_var Gamma' (tshift X T))
  | it_bound : forall X Gamma Gamma',
      insert_tvar X Gamma Gamma' ->
      insert_tvar (S X) (ext_tvar Gamma) (ext_tvar Gamma')
  | it_cvar : forall X Gamma Gamma' U V,
      insert_tvar X Gamma Gamma' ->
      insert_tvar X (ext_cvar Gamma (U, V))
                  (ext_cvar Gamma' (tshift X U, tshift X V)).

Lemma get_tvar_insert_ge : forall Gamma Gamma' n m,
  insert_tvar n Gamma Gamma' ->
  n <= m                     ->
  get_tvar Gamma' (S m) = get_tvar Gamma m.
Proof.
  intros. generalize dependent m.
  induction H; intros. 
    simpl. trivial.
    simpl. apply IHinsert_tvar. trivial.
    simpl. destruct m. omega.
      apply IHinsert_tvar. omega.
    simpl. apply IHinsert_tvar. trivial.
Qed.

Lemma get_tvar_insert_lt : forall Gamma Gamma' n m,
  insert_tvar n Gamma Gamma' ->
  n > m                      ->
  get_tvar Gamma' m = get_tvar Gamma m.
Proof.
  intros. generalize dependent m.
  induction H; intros. 
    simpl. omega.
    simpl. apply IHinsert_tvar. trivial.
    simpl. destruct m. trivial.
      apply IHinsert_tvar. omega.
    simpl. apply IHinsert_tvar. trivial.
Qed.

Lemma insert_tvar_wf_type : forall Gamma Gamma' U n,
  insert_tvar n Gamma Gamma' ->
  well_formed_type Gamma U   ->
  well_formed_type Gamma' (tshift n U).
Proof.
  intros. generalize dependent Gamma. generalize dependent Gamma'. 
  generalize dependent n. induction U; intros.
    simpl. constructor. destruct (le_gt_dec n0 n); inversion H0;
      rewrite <- H2. eapply get_tvar_insert_ge. apply H. omega.
      eapply get_tvar_insert_lt. apply H. omega.
    simpl. constructor; inversion H0. eapply IHU1. apply H.
      trivial. eapply IHU2. apply H. trivial.
    simpl. constructor. eapply IHU. constructor. apply H.
      inversion H0. trivial.
    simpl. constructor; inversion H0. eapply IHU1. apply H.
      trivial. eapply IHU2. apply H. trivial. eapply IHU3. apply H. trivial.
Qed.

Lemma insert_tvar_wf_context : forall Gamma Gamma' n,
  insert_tvar n Gamma Gamma' ->
  well_formed_context Gamma  ->
  well_formed_context Gamma'.
Proof.
  intros. induction H; try constructor.
    trivial.
    eapply insert_tvar_wf_type. apply H. inversion H0. trivial.
      apply IHinsert_tvar. inversion H0. trivial.
    apply IHinsert_tvar. inversion H0. trivial.
    apply IHinsert_tvar. inversion H0. trivial.
    eapply insert_tvar_wf_type. apply H. inversion H0. trivial.
    eapply insert_tvar_wf_type. apply H. inversion H0. trivial.
Qed.    

Lemma get_var_insert_tvar : forall Gamma Gamma' x X,
  insert_tvar X Gamma Gamma' ->
  get_var Gamma' x = opt_map (tshift X) (get_var Gamma x).
Proof.
  intros. generalize dependent x. induction H; intros; simpl.
    trivial.
    destruct x.
      trivial.
      apply IHinsert_tvar.
    rewrite IHinsert_tvar. destruct (get_var Gamma x).
      simpl. apply f_equal. assert (X = 0 + X) by trivial. 
      rewrite H0. rewrite tshift_tshift_prop. trivial.
      trivial.
    rewrite IHinsert_tvar. trivial.
Qed.



Lemma subst_context_var : forall Gamma Gamma' U X x,
  subst_context U X Gamma Gamma' ->
  get_var Gamma x = None         ->
  get_var Gamma' x = None.
Proof.
  intros. generalize dependent x. induction H; intros.
    simpl. destruct x.
      subst. inversion H1.
      apply IHsubst_context. inversion H1. trivial.
    simpl in H1. unfold opt_map in H1. destruct (get_var Gamma x).
      inversion H1. trivial.
    simpl. rewrite IHsubst_context. trivial. simpl in H0.
      destruct (get_var Gamma x). inversion H0. trivial.
    simpl. simpl in H2. apply IHsubst_context. trivial.
Qed.


Fixpoint remove_var (Gamma : context) (x : nat) : context :=
  match Gamma with
  | empty       => empty
  | ext_tvar Gamma' => ext_tvar (remove_var Gamma' x)
  | ext_var Gamma' T =>
    match x with
      | O   => Gamma'
      | S y => ext_var (remove_var Gamma' y) T
    end
  | ext_cvar Gamma' (U, V) =>
    ext_cvar (remove_var Gamma' x) (U, V)
  end.

Lemma remove_preserves_get : forall Gamma x n,
  get_tvar Gamma n = get_tvar (remove_var Gamma x) n.
Proof.
  induction Gamma; intros. simpl. trivial.
  induction x; intros. trivial.
    induction n. simpl. trivial.
    simpl. trivial.
  simpl. destruct n. trivial. trivial.
  simpl. destruct p. simpl. trivial.
Qed.
      
Lemma wf_type_remove : forall Gamma x T,
  well_formed_type Gamma T ->
  well_formed_type (remove_var Gamma x) T.
Proof.
  intros. generalize dependent Gamma. induction T; intros;
                                      inversion H; constructor.
    rewrite <- remove_preserves_get. trivial.
    apply IHT1. trivial. apply IHT2. trivial.
    apply IHT in H1. simpl in H1. trivial.
    apply IHT1; trivial.
    apply IHT2; trivial.
    apply IHT3; trivial.
Qed.  

Lemma wf_context_weakening : forall Gamma x,
  well_formed_context Gamma ->
  well_formed_context (remove_var Gamma x).
Proof.
  intros. generalize dependent x. induction Gamma; intro x.
    simpl. trivial.
    simpl. destruct x.
      inversion H; trivial.
      constructor. inversion H; subst. apply wf_type_remove.
      trivial.
    apply IHGamma. inversion H. trivial.
    simpl. constructor. apply IHGamma. inversion H. trivial.
    simpl. destruct p. inversion H. constructor. apply IHGamma. trivial.
      apply wf_type_remove. trivial.
      apply wf_type_remove. trivial.
Qed.

Lemma get_var_remove_lt : forall Gamma x y,
  x < y -> get_var (remove_var Gamma y) x = get_var Gamma x.
Proof.
  intros. generalize dependent x. generalize dependent y.
  induction Gamma; intros.
    trivial.
    simpl. destruct y.
      omega.
      destruct x.
        trivial.
        apply IHGamma. omega.
    simpl. apply f_equal. apply IHGamma. trivial.
    simpl. destruct p. erewrite <- IHGamma. simpl. reflexivity. trivial.
Qed.

Lemma get_var_remove_ge : forall Gamma x y,
  x >= y -> get_var (remove_var Gamma y) x = get_var Gamma (S x).
Proof.
  intros. generalize dependent x. generalize dependent y.
  induction Gamma; intros.
    trivial.
    simpl. destruct y.
      trivial.
      destruct x.
        omega.
        apply IHGamma. omega.
    simpl. apply f_equal. apply IHGamma. trivial.
    simpl. destruct p. simpl. apply IHGamma. trivial.
Qed.


Fixpoint remove_cvar (Gamma : context) (x : nat) : context :=
  match Gamma with
  | empty            => empty
  | ext_tvar Gamma'  => ext_tvar (remove_cvar Gamma' x)
  | ext_var Gamma' T => ext_var (remove_cvar Gamma' x) T
  | ext_cvar Gamma' (U, V) =>
    match x with
      | O   => Gamma'
      | S y => ext_cvar (remove_cvar Gamma' y) (U, V)
    end
  end.

Lemma remove_cvar_get_tvar : forall Gamma X x,
  get_tvar Gamma X = get_tvar (remove_cvar Gamma x) X.
Proof with eauto.
  induction Gamma; intros; try (destruct X); try (destruct p; destruct x);
  simpl; trivial.
Qed.    

Lemma remove_cvar_ty_weakening : forall Gamma X T,
  well_formed_type Gamma T ->
  well_formed_type (remove_cvar Gamma X) T.
Proof.
  intros. generalize dependent X; generalize dependent Gamma;
          induction T; intros; constructor; inversion H.
  Case "TVar".
    subst. rewrite <- remove_cvar_get_tvar. trivial.
  Case "TArrow".
    apply IHT1; trivial. apply IHT2; trivial.
  Case "TUniv".
    eapply IHT in H1. simpl in H1. apply H1.
  Case "TCoerce".
    apply IHT1; trivial. apply IHT2; trivial. apply IHT3; trivial.
Qed.

Lemma wf_typ_extensionality : forall T Gamma Gamma',
  (forall X, get_tvar Gamma X = get_tvar Gamma' X) ->
  well_formed_type Gamma T -> well_formed_type Gamma' T.
Proof.
  intros T Gamma Gamma' H1 H2.
  apply context_invariance_types with (2 := H2).
  intros. symmetry. trivial.
Qed.

Lemma wf_type_remove_var : forall Gamma x T,
  well_formed_type Gamma T ->
  well_formed_type (remove_var Gamma x) T.
Proof.
  intros Gamma x T. apply wf_typ_extensionality.
  intro X. apply remove_preserves_get.
Qed.

Lemma wf_type_insert_var : forall Gamma n T,
  well_formed_type (remove_var Gamma n) T ->
  well_formed_type Gamma T.
Proof.
  intros Gamma n T. apply wf_typ_extensionality. intro X.
  symmetry. apply remove_preserves_get.
Qed.


Lemma remove_var_get_cvar : forall Gamma x y,
  get_cvar Gamma x = get_cvar (remove_var Gamma y) x.
Proof.
  induction Gamma; intros; try (destruct x); try(destruct p); try (destruct y);
  simpl; try (apply f_equal); simpl; trivial.
Qed.

Lemma remove_cvar_ty_strengthening : forall Gamma X T,
  well_formed_type (remove_cvar Gamma X) T ->
  well_formed_type Gamma T.
Proof.
  intros. generalize dependent X; generalize dependent Gamma;
          induction T; intros; constructor; inversion H.
  Case "TVar".
    subst. erewrite remove_cvar_get_tvar. apply H1.
  Case "TArrow".
    eapply IHT1; apply H2. eapply IHT2; apply H3.
  Case "TUniv".
    eapply IHT. simpl. apply H1.
  Case "TCoerce".
    eapply IHT1; apply H3. eapply IHT2; apply H4. eapply IHT3; eassumption.
Qed.

Lemma wf_context_strengthening_cvar : forall Gamma X,
  well_formed_context Gamma ->
  well_formed_context (remove_cvar Gamma X).
Proof.
  induction Gamma; intros.
  Case "empty".
    constructor.
  Case "ext_var".
    simpl. constructor. inversion H; subst. apply remove_cvar_ty_weakening.
    trivial. apply IHGamma. inversion H. trivial.
  Case "ext_tvar".
    simpl. constructor. apply IHGamma. inversion H. trivial.
  Case "ext_cvar".
    simpl. inversion H; subst. destruct X. trivial.
    constructor. apply IHGamma. trivial.
    apply remove_cvar_ty_weakening. trivial.
    apply remove_cvar_ty_weakening. trivial.
Qed.


Lemma wf_type_weakening_cvar : forall Gamma U V T,
  well_formed_type Gamma T ->
  well_formed_type (ext_cvar Gamma (U, V)) T.
Proof.
  intros. apply remove_cvar_ty_strengthening with 0. simpl. trivial.
Qed.    

 Lemma context_subst_wf : forall Gamma Gamma' X U,
   subst_context U X Gamma Gamma'       ->
   well_formed_context Gamma' ->
   well_formed_type Gamma' U.
 Proof with auto.
   intros Gamma Gamma' X U Hs. induction Hs; intros.
     apply wf_weakening_var. apply IHHs.
       inversion H0; subst. trivial.
     trivial.
     apply wf_weakening_tvar. apply IHHs.
       inversion H; subst.
       trivial.
     apply wf_type_weakening_cvar. apply IHHs. inversion H1. trivial.
 Qed.


 Lemma subst_preserves_well_formed_type : forall X Gamma Gamma' U T,
   subst_context U X Gamma Gamma'    ->
   well_formed_type Gamma T          ->
   well_formed_context Gamma'        ->
   well_formed_type Gamma' ([X := U] T).
 Proof.
   intros. generalize dependent U. generalize dependent Gamma.
   generalize dependent Gamma'. generalize dependent X.
   induction T; intros.
   Case "TVar".
     simpl. inversion H0; subst. 
     destruct (eq_nat_dec X n).
     SCase "X = n".
       eapply context_subst_wf. apply H. trivial.
     SCase "X <> n".
       inversion H0; subst. destruct (le_lt_dec X n).
       SSCase "X < n".
         constructor. rewrite <- H3. apply context_subst_ge with X U.
         omega. trivial.
       SSCase "X > n".
         constructor. rewrite <- H3. apply context_subst_lt with X U.
         omega. trivial.
   Case "TArrow".
     inversion H0; subst. simpl. constructor. eapply IHT1; trivial.
     apply H4. trivial.
     eapply IHT2; trivial. apply H5. trivial.
   Case "TUniv".
     simpl. constructor. eapply IHT. constructor. trivial. 
     inversion H0. apply H3.
     assert (X + 1 = S X) by omega. rewrite H2. constructor.
     trivial.
  Case "TCoerce".
    simpl. constructor; inversion H0.
    eapply IHT1; trivial. apply H5. trivial.
    eapply IHT2; trivial. apply H6. trivial.
    eapply IHT3; trivial. apply H7. trivial.
 Qed.

 (** WOOOOOOO!!! *)

 Lemma subst_context_wf : forall Gamma Gamma' X U,
   subst_context U X Gamma Gamma' ->
   well_formed_context Gamma      ->
   well_formed_context Gamma'.
 Proof.
   intros Gamma Gamma' X U H. induction H; intros.
     constructor. apply subst_type_in_type_correct in H0. 
     rewrite <- H0. eapply subst_preserves_well_formed_type.
     apply H. inversion H1; subst. trivial.

     apply IHsubst_context. inversion H1; subst. trivial.
     apply IHsubst_context. inversion H1; subst. trivial.

     trivial. constructor. apply IHsubst_context. inversion H0; trivial.
     inversion H2. constructor. apply IHsubst_context. trivial.
     subst. apply subst_type_in_type_correct in H0. rewrite <- H0.
     eapply subst_preserves_well_formed_type. eassumption.
     trivial. apply IHsubst_context. trivial.
     apply subst_type_in_type_correct in H1. rewrite <- H1.
     eapply subst_preserves_well_formed_type. eassumption.
     trivial. apply IHsubst_context. trivial.
 Qed.


Lemma type_in_context_wf_coercion : forall Gamma n U V,
  well_formed_context Gamma      ->
  get_cvar Gamma n = Some (U, V) ->
  well_formed_type Gamma U /\ well_formed_type Gamma V.
Proof.
  induction Gamma; intros.
  Case "empty".
    inversion H0.
  Case "ext_var".
    assert (well_formed_type Gamma U /\ well_formed_type Gamma V).
      SCase "Pf of assertion".
      eapply IHGamma. inversion H. trivial. eassumption.
    inversion H1; split; apply wf_weakening_var; trivial. 
  Case "ext_tvar".
    simpl in H0. destruct (get_cvar Gamma n) eqn:Heq; inversion H0; subst.
      destruct p.
      assert (well_formed_type Gamma t /\ well_formed_type Gamma t0).
      SSCase "Pf of assertion".
        eapply IHGamma; inversion H; trivial; eassumption.
      inversion H2; subst; inversion H1; split; apply wf_weakening_tvar; trivial.
  Case "ext_cvar".
    destruct p; inversion H; subst; destruct n.
    SCase "n = 0".
      split; apply wf_type_weakening_cvar; inversion H0; subst; trivial.
    SCase "n = S n".
      assert (well_formed_type Gamma U /\ well_formed_type Gamma V).
      SSCase "Pf of assertion".
        eapply IHGamma. trivial. eassumption.
      inversion H1; split; apply wf_type_weakening_cvar; trivial. 
Qed.      

Lemma forall_type_well_formed : forall Gamma U V,
  well_formed_context Gamma        ->
  well_formed_type Gamma (TUniv U) ->
  well_formed_type Gamma V         ->
  well_formed_type Gamma ([0:=V] U).
Proof.
  intros. apply subst_preserves_well_formed_type with (ext_tvar Gamma).
  constructor. trivial. trivial. inversion H0. trivial.
  trivial.
Qed.

Lemma coercion_well_formed : forall Gamma c U V,
  Gamma |- c ; U ~ V ->
  well_formed_context Gamma /\
  well_formed_type Gamma U /\ well_formed_type Gamma V.
Proof.
  intros; coercion_cases (induction H) Case; intros;
  try (inversion IHwell_formed_coercion; inversion H1; split; trivial; split;
      assumption);
  try (inversion IHwell_formed_coercion);
  try (inversion IHwell_formed_coercion1; inversion IHwell_formed_coercion2; 
       inversion H2; inversion H4; subst);
  try (split; trivial; split; assumption);
  try (inversion H1; inversion H2; inversion H3; subst; split; trivial;
       split; assumption).
  Case "C_Var".
    split. trivial. eapply type_in_context_wf_coercion. trivial. eassumption.
  Case "C_App".
    inversion H2. inversion H9. inversion H10. split. trivial. split; trivial.
  Case "C_Forall".
    inversion H1; subst. split. inversion H0. trivial. split; constructor; trivial.
  Case "C_Inst".
    subst. split. trivial. inversion H2. split; apply forall_type_well_formed;
    trivial. 
Qed.


Lemma ext_var_coercion_strengthening : forall Gamma c n U V,
  Gamma |- c ; U ~ V ->
  remove_var Gamma n |- c ; U ~ V.
Proof.
  intros; coercion_cases (induction H) Case; try constructor;
  try (eapply C_Trans); try (eapply C_App);
  try (inversion IHwell_formed_coercion; subst; eassumption);
  try (inversion IHwell_formed_coercion1; subst; eassumption);
  try (inversion IHwell_formed_coercion2; subst; eassumption);
  try (apply wf_type_remove_var; trivial);
  try (apply wf_context_weakening; trivial); trivial.
  Case "C_Var".
    erewrite <- remove_var_get_cvar. trivial.
  Case "C_ALeft".
    eapply C_ALeft. eassumption.
  Case "C_ARight".
    eapply C_ARight. eassumption.
  Case "C_CLeft11".
    eapply C_CLeft11. eassumption.
  Case "C_CLeft12".
    eapply C_CLeft12. eassumption.
  Case "C_CRight".
    eapply C_CRight. eassumption.
Qed.

    
Lemma get_cvar_remove_lt : forall Gamma x y,
   x < y ->
   get_cvar Gamma x = get_cvar (remove_cvar Gamma y) x.
Proof.
  induction Gamma; intros.
  Case "empty".
    trivial.
  Case "ext_var".
    simpl. apply IHGamma. trivial.
  Case "ext_tvar".
    simpl. erewrite IHGamma. reflexivity. trivial.
  Case "ext_cvar".
    simpl. destruct x; destruct p; destruct y; try omega; trivial.
    simpl. apply IHGamma. omega.
Qed.

Lemma get_cvar_remove_ge : forall Gamma x y,
   x >= y ->
   get_cvar Gamma (S x) = get_cvar (remove_cvar Gamma y) x.
Proof.
  induction Gamma; intros.
  Case "empty".
    trivial.
  Case "ext_var".
    simpl. apply IHGamma. trivial.
  Case "ext_tvar".
    simpl. erewrite IHGamma. reflexivity. trivial.
  Case "ext_cvar".
    simpl. destruct x; destruct p; destruct y; try omega; trivial.
    simpl. apply IHGamma. omega.
Qed.

Lemma coercion_weakening : forall Gamma c X U V,
  well_formed_context Gamma ->
  remove_cvar Gamma X |- c ; U ~ V ->
  Gamma |- cshift X c ; U ~ V.
Proof.
  intros; remember (remove_cvar Gamma X) as G; generalize dependent Gamma;
  coercion_cases (induction H0) Case; intros; subst; simpl;
  try constructor; trivial;
  try (eapply C_Trans); try (eapply C_App);
  try (eapply remove_cvar_ty_strengthening; eassumption);
  try (eapply IHwell_formed_coercion; trivial);
  try (eapply IHwell_formed_coercion1; trivial);
  try (eapply IHwell_formed_coercion2; trivial).
  Case "C_Var".
    destruct (le_gt_dec X x); rewrite <- H0.
    SCase "X <= n".
      apply get_cvar_remove_ge; omega.
    SCase "X > n".
      apply get_cvar_remove_lt; omega.
  Case "C_Forall".
    constructor. trivial.
  Case "C_ALeft".
    eapply C_ALeft. apply IHwell_formed_coercion; trivial.
  Case "C_ARight".
    eapply C_ARight. apply IHwell_formed_coercion; trivial.
  Case "C_CLeft11".
    eapply C_CLeft11. apply IHwell_formed_coercion; trivial.
  Case "C_CLeft12".
    eapply C_CLeft12. apply IHwell_formed_coercion; trivial.
  Case "C_CRight".
    eapply C_CRight. apply IHwell_formed_coercion; trivial.
Qed.


Lemma get_cvar_insert_tvar : forall Gamma Gamma' x X,
  insert_tvar X Gamma Gamma' ->
  get_cvar Gamma' x = opt_map_prod (tshift X) (get_cvar Gamma x).
Proof.
  intros; generalize dependent x; induction H; intros; trivial.
  Case "ext_var".
    simpl. apply IHinsert_tvar.
  Case "ext_tvar".
    simpl. rewrite IHinsert_tvar. destruct get_cvar.
      destruct p. simpl. apply f_equal.
        assert (X = O + X) by trivial. rewrite H0. rewrite tshift_tshift_prop.
        rewrite tshift_tshift_prop. trivial.
        trivial.
  Case "ext_cvar".      
    simpl. destruct x. trivial. apply IHinsert_tvar.
Qed.

Lemma coercion_weakening_tvar_ind : forall Gamma Gamma' c n U V,
  insert_tvar n Gamma Gamma' ->
  Gamma  |- c ; U ~ V ->
  Gamma' |- cshift_typ n c ; tshift n U ~ tshift n V.
Proof.
  intros; generalize dependent Gamma'; generalize dependent n;
  coercion_cases (induction H0) Case; intros; simpl; try constructor;
  try (eapply C_Trans); try (eapply C_App);
  try (eapply insert_tvar_wf_context; eassumption; trivial);
  try (apply IHwell_formed_coercion; trivial);
  try (apply IHwell_formed_coercion1; trivial);
  try (apply IHwell_formed_coercion2; trivial).
  Case "C_Var".    
    rewrite get_cvar_insert_tvar with Gamma Gamma' x n.
    rewrite H0. simpl. trivial. trivial.
  Case "C_Refl".
    eapply insert_tvar_wf_type. eassumption. trivial.
  Case "C_Forall".
    constructor. trivial.
  Case "C_ALeft".
    eapply C_ALeft. apply IHwell_formed_coercion. trivial.
  Case "C_ARight".
    eapply C_ARight. apply IHwell_formed_coercion. trivial.
  Case "C_CLeft11".
    eapply C_CLeft11. apply IHwell_formed_coercion. trivial.
  Case "C_CLeft12".
    eapply C_CLeft12. apply IHwell_formed_coercion. trivial.
  Case "C_CRight".
    eapply C_CRight. apply IHwell_formed_coercion. trivial.
  Case "C_Inst".    
    assert (n = 0 + n) by trivial. rewrite H2. rewrite tshift_subst_prop_2.
    rewrite tshift_subst_prop_2. constructor. apply IHwell_formed_coercion.
    trivial.
    eapply insert_tvar_wf_type. eassumption. trivial.
Qed.

Lemma coercion_weakening_tvar : forall Gamma c U V T,
  well_formed_type Gamma T ->
  Gamma |- c ; U ~ V ->
  ext_tvar Gamma |- cshift_typ 0 c ; tshift 0 U ~ tshift 0 V.
Proof.
  intros. eapply coercion_weakening_tvar_ind. econstructor. apply H. trivial.
Qed.

Lemma cn_substitution_preserves_coercion : forall Gamma x c c' U1 U2 V1 V2,
  Gamma |- c ; U1 ~ U2                ->
  remove_cvar Gamma x |- c' ; V1 ~ V2 ->
  get_cvar Gamma x = Some (V1, V2)    ->
  remove_cvar Gamma x |- [x := c'] c ; U1 ~ U2.
Proof.
  intros; generalize dependent x;  generalize dependent V1;
  generalize dependent V2; generalize dependent c';
  coercion_cases (induction H) Case; intros; simpl; try constructor;
  try (eapply C_Trans); try (eapply C_App);
  try (eapply IHwell_formed_coercion; eassumption; trivial);
  try (eapply IHwell_formed_coercion1; eassumption; trivial);
  try (eapply IHwell_formed_coercion2; eassumption; trivial);
  try (apply wf_context_strengthening_cvar; trivial).
  Case "C_Var".
    destruct (eq_nat_dec x0 x).
    SCase "x = x0".
      subst. rewrite H0 in H2. inversion H2; subst. trivial.
    SCase "x <> x0".
      destruct le_lt_dec; constructor;
      try (apply wf_context_strengthening_cvar); trivial;
      rewrite <- H0; symmetry.
      SSCase "x0 <= x".
        assert (x = S (x-1)) by omega.
        rewrite H3. assert (S (x-1) - 1 = x - 1) by omega. rewrite H4.
        apply get_cvar_remove_ge. omega.
      SSCase "x < x0".
        apply get_cvar_remove_lt. trivial.
  apply remove_cvar_ty_weakening; trivial.
  Case "C_Forall".
    eapply IHwell_formed_coercion. simpl. remember H0 as Hx. clear HeqHx.
    apply coercion_well_formed in H0. inversion H0. inversion H3.
    eapply coercion_weakening_tvar. apply H4. eassumption.
    simpl. rewrite H1. simpl. trivial.
  Case "C_ALeft".
    eapply C_ALeft. eauto.
  Case "C_ARight".
    eapply C_ARight. eauto.
  Case "C_CLeft11".
    eapply C_CLeft11. eauto.
  Case "C_CLeft12".
    eapply C_CLeft12. eauto.
  Case "C_CRight".
    eapply C_CRight. eauto.
  Case "C_Inst".
    apply remove_cvar_ty_weakening; trivial.
Qed.


Lemma type_in_context_wf : forall x T Gamma,
  well_formed_context Gamma ->
  get_var Gamma x = Some T  ->
  well_formed_type Gamma T.
Proof.
  intros. generalize dependent T. generalize dependent x.
  induction Gamma; intros. 
    inversion H0.
    inversion H0; subst. destruct x.
    apply wf_weakening_var. inversion H; subst. inversion H2; subst.
      trivial.
      apply wf_weakening_var. eapply IHGamma. inversion H; subst. trivial.
      apply H2.
    
    simpl in H0. unfold opt_map in H0. destruct (get_var Gamma x) eqn:Hg.
    inversion H0; subst. apply wf_weakening_tvar. eapply IHGamma.
    inversion H.
    trivial. apply Hg.
    inversion H0.
    destruct p. apply wf_type_weakening_cvar. eapply IHGamma. inversion H.
    trivial. simpl in H0. eassumption.
Qed.


Lemma typing_well_formed : forall Gamma t U,
  Gamma |- t \in U ->
  (well_formed_type Gamma U /\ well_formed_context Gamma).
Proof.
  intros. has_type_cases (induction H) Case; split.
  Case "T_Var".
    eapply type_in_context_wf. trivial. apply H0. trivial.
    constructor; inversion IHhas_type. inversion H1; subst.
      trivial. apply wf_strengthening_var in H0. trivial.
  Case "T_Abs".
    inversion IHhas_type. inversion H1. trivial.
  Case "T_App".
    inversion IHhas_type1. inversion H1. trivial.
    inversion IHhas_type2. trivial.
  Case "T_TAbs".
    inversion IHhas_type. constructor. trivial.
    inversion IHhas_type. inversion H1. trivial.
  Case "T_TApp".
    inversion IHhas_type. simpl.
    eapply subst_preserves_well_formed_type. constructor. trivial.
    trivial. inversion H2. trivial. trivial. trivial.
  Case "T_CAbs".
    inversion IHhas_type. constructor; trivial.
    inversion IHhas_type. apply remove_cvar_ty_weakening with (X:=0) in H4.
    simpl in H4. trivial.
    inversion IHhas_type. inversion H3. trivial.
  Case "T_CApp".
    inversion IHhas_type. inversion H1. trivial.
    inversion IHhas_type. trivial.
    apply coercion_well_formed in H. inversion H. inversion H2. trivial.
    inversion IHhas_type. trivial.
Qed.

Lemma coercion_weakening_var : forall Gamma c x U V,
  well_formed_context Gamma ->
  remove_var Gamma x |- c ; U ~ V ->
  Gamma |- c; U ~ V.
Proof with eauto.
  intros; remember (remove_var Gamma x) as G; generalize dependent Gamma;
  coercion_cases (induction H0) Case; intros; subst; try constructor;
  try (eapply C_Trans); try (eapply C_App); trivial;
  try (eapply wf_type_insert_var; eassumption);
  try (apply IHwell_formed_coercion; trivial; trivial);
  try (apply IHwell_formed_coercion1; trivial; trivial);
  try (apply IHwell_formed_coercion2; trivial; trivial);
  try (constructor; trivial).
  Case "C_Var".
    erewrite remove_var_get_cvar. eassumption.
  Case "C_ALeft"; eapply C_ALeft...
  Case "C_ARight"; eapply C_ARight...
  Case "C_CLeft11"; eapply C_CLeft11...
  Case "C_CLeft12"; eapply C_CLeft12...
  Case "C_CRight"; eapply C_CRight...
Qed.

Lemma typing_weakening_var_ind : forall Gamma n t U,
  well_formed_context Gamma ->
  remove_var Gamma n |- t \in U ->
  Gamma |- shift n t \in U.
Proof.
  intros. generalize dependent U. 
  generalize dependent Gamma. generalize dependent n.
  t_cases (induction t) Case; intros;
  inversion H0; subst.
  Case "tvar".
    constructor. trivial.
    destruct (le_gt_dec n0 n);
      rewrite <- H4; symmetry. apply get_var_remove_ge. omega.
      apply get_var_remove_lt. omega.
  Case "tapp".
    simpl. eapply T_App. apply IHt1. trivial. apply H4.
    apply IHt2. trivial. trivial.
  Case "tabs".
    simpl. constructor. apply IHt. constructor. 
    eapply wf_type_insert_var. apply typing_well_formed in H5.
    inversion H5. inversion H2. apply H6. trivial.
    simpl. trivial.
  Case "ttapp".
    simpl. constructor. apply IHt. trivial. trivial.
    eapply wf_type_insert_var. apply H5. trivial.
  Case "ttabs".
    simpl. constructor. apply IHt. constructor. trivial.
    simpl. trivial.
  Case "tcapp".
    simpl. econstructor. apply IHt. trivial. eassumption.
    eapply coercion_weakening_var. trivial. eassumption.
  Case "tcabs".
    simpl. constructor. apply IHt. constructor; trivial.
    eapply wf_type_insert_var. eassumption.
    eapply wf_type_insert_var. eassumption.
    simpl. trivial.
    eapply wf_type_insert_var. eassumption.
    eapply wf_type_insert_var. eassumption.
  Case "tcoerce".
    simpl. econstructor. eapply coercion_weakening_var. trivial.
    eassumption.
    apply IHt. trivial. trivial.
Qed.

Lemma typing_weakening_var : forall Gamma t U V,
  well_formed_type Gamma V ->
  Gamma |- t \in U         ->
  ext_var Gamma V |- shift 0 t \in U.
Proof.
  intros. eapply typing_weakening_var_ind. constructor. trivial.
  apply typing_well_formed in H0. inversion H0. trivial.
  simpl. trivial.
Qed.


Lemma typing_weakening_tvar_ind : forall Gamma Gamma' n t U,
  insert_tvar n Gamma Gamma' ->
  Gamma  |- t \in U          ->
  Gamma' |- shift_typ n t \in tshift n U.
Proof.
  intros. generalize dependent n. generalize dependent Gamma'.
  has_type_cases (induction H0) Case; intros; simpl.
  Case "T_Var".
    constructor. eapply insert_tvar_wf_context. apply H1.
    trivial. rewrite get_var_insert_tvar with Gamma Gamma' x n.
    rewrite H0. trivial. trivial.
  Case "T_Abs".
    constructor. apply IHhas_type. constructor. trivial.
  Case "T_App".
    apply T_App with (tshift n T11). simpl in IHhas_type1.
    apply IHhas_type1. trivial. apply IHhas_type2. trivial.
  Case "T_TAbs".
    constructor. apply IHhas_type. constructor. trivial.
  Case "T_TApp".
    assert (n = 0 + n) by trivial. rewrite H3. rewrite tshift_subst_prop_2.
    constructor. apply IHhas_type. trivial. eapply insert_tvar_wf_type.
    apply H2. trivial. eapply insert_tvar_wf_context. apply H2.
    trivial.
  Case "T_CAbs".
    constructor. apply IHhas_type. constructor. trivial.
    eapply insert_tvar_wf_type. eassumption. trivial.
    eapply insert_tvar_wf_type. eassumption. trivial.
  Case "T_CApp".
    econstructor. simpl in IHhas_type. apply IHhas_type. trivial.
    eapply coercion_weakening_tvar_ind. eassumption. trivial.
  Case "T_Coerce".
    econstructor. eapply coercion_weakening_tvar_ind. eassumption. eassumption.
    apply IHhas_type. trivial.
Qed.

Lemma typing_weakening_tvar : forall Gamma t U,
  Gamma |- t \in U ->
  ext_tvar Gamma |- shift_typ 0 t \in tshift 0 U.
Proof.
  intros. eapply typing_weakening_tvar_ind. econstructor.
  apply typing_well_formed in H. inversion H. apply H0. trivial.
Qed.

Lemma remove_cvar_get_var : forall Gamma x y,
  get_var Gamma x = get_var (remove_cvar Gamma y) x.
Proof.
  induction Gamma; intros; try (destruct x); try (destruct p); try (destruct y);
  simpl; try (apply f_equal); simpl; trivial.
Qed.

Lemma typing_weakening_cvar_ind : forall Gamma x t T,
  well_formed_context Gamma      ->
  remove_cvar Gamma x |- t \in T ->
  Gamma |- shift_cn x t \in T.
Proof.
  intros Gamma x t; generalize dependent Gamma; generalize dependent x;
  t_cases (induction t) Case; intros; simpl; inversion H0; subst; econstructor;
  try (apply IHt1; trivial; eassumption);
  try (apply IHt2; trivial; eassumption);
  try (apply IHt; try constructor; trivial; simpl; trivial);
  try (eapply remove_cvar_ty_strengthening; eassumption; trivial); trivial.
  Case "tvar".
    trivial. erewrite remove_cvar_get_var. eassumption.
  Case "tabs".
    apply typing_well_formed in H5.
    inversion H5. inversion H2. eapply remove_cvar_ty_strengthening.
    eassumption.
  Case "tcapp".
    eassumption. apply coercion_weakening. trivial. trivial.
  Case "tcoerce".
    apply coercion_weakening. trivial. eassumption.
    trivial.
Qed.


Lemma substitution_preserves_typing_term_term : forall Gamma x U t v T,
     Gamma |- t \in T              ->
     remove_var Gamma x |- v \in U ->
     get_var Gamma x = Some U      ->
     remove_var Gamma x |- [x:=v]t \in T.
Proof with auto.
  intros Gamma x U t v T Ht Hv Hx.
  generalize dependent Gamma. generalize dependent T.
  generalize dependent U. generalize dependent v. generalize dependent x. 
  t_cases (induction t) Case; intros x v U T Gamma H Hv Hx;
    (* in each case, we'll want to get at the derivation of H *)
    inversion H; subst; simpl...
  Case "tvar".
    destruct (eq_nat_dec x n).
    SCase "x=n".
      subst. rewrite H3 in Hx. inversion Hx; subst. trivial.
    SCase "x<>n".
      destruct (le_lt_dec x n).
      SSCase "x <= n".
        apply T_Var. apply wf_context_weakening. trivial.
        assert (n = S (n - 1)) by omega. rewrite H0 in H3.
        rewrite <- H3. apply get_var_remove_ge. omega.
      SSCase "x > n".
        constructor. apply wf_context_weakening. trivial.
        rewrite <- H3. apply get_var_remove_lt. omega.
  Case "tapp".
    apply T_App with T11. apply IHt1 with U. trivial. trivial.
    trivial. apply IHt2 with U. trivial. trivial.
    trivial.
  Case "tabs".
    apply T_Abs. assert (ext_var (remove_var Gamma x) t =
                         remove_var (ext_var Gamma t) (S x)) by trivial.
    rewrite H0. eapply IHt. trivial. simpl. apply typing_weakening_var.
    apply typing_well_formed in H4. inversion H4. inversion H2; subst.
    apply wf_type_remove_var. trivial. apply Hv. simpl. trivial.
  Case "ttapp".        
    econstructor. apply IHt with U. trivial. trivial.
    trivial. apply wf_type_remove_var. trivial. apply wf_context_weakening.
    trivial.
  Case "ttabs".
    apply T_TAbs. assert (ext_tvar (remove_var Gamma x) =
                         remove_var (ext_tvar Gamma) x) by trivial.
    rewrite H0. apply IHt with (tshift 0 U).
    trivial. rewrite <- H0. apply typing_weakening_tvar. trivial.
    simpl. rewrite Hx. trivial.
  Case "tcapp".
    econstructor. eapply IHt. eassumption. eassumption.
    trivial. eapply ext_var_coercion_strengthening. trivial.
  Case "tcabs".
    constructor. assert (ext_cvar (remove_var Gamma x) (t, t0) =
                         remove_var (ext_cvar Gamma (t, t0)) x) by trivial.
    rewrite H0. eapply IHt. trivial. 
    simpl. apply typing_weakening_cvar_ind. constructor.
    apply typing_well_formed in H. inversion H. apply wf_context_weakening.
    trivial. apply wf_type_remove; trivial. apply wf_type_remove; trivial.
    simpl. eassumption. simpl. trivial. apply wf_type_remove; trivial.
    apply wf_type_remove; trivial.
  Case "tcoerce".
    econstructor. eapply ext_var_coercion_strengthening.
    eassumption. eapply IHt. trivial. eassumption. trivial.
Qed.

Lemma cn_substitution_preserves_typing : forall Gamma t c x U V T,
  Gamma |- t \in T                 ->
  remove_cvar Gamma x |- c ; U ~ V ->
  get_cvar Gamma x = Some (U, V)   ->
  remove_cvar Gamma x |- [x:=c]t \in T.
Proof.
  intros Gamma t c; generalize dependent Gamma; generalize dependent c;
  t_cases (induction t) Case; intros; inversion H; subst;
  simpl; econstructor;
  try (eapply IHt; eassumption; eassumption; trivial);
  try (eapply IHt1; eassumption; eassumption; trivial);
  try (eapply IHt2; eassumption; eassumption; trivial);
  try (eapply cn_substitution_preserves_coercion; trivial; eassumption;
       trivial).
  Case "tvar".
    simpl. apply wf_context_strengthening_cvar. trivial.
    rewrite <- remove_cvar_get_var. trivial.
  Case "tabs".
    assert (ext_var (remove_cvar Gamma x) t = remove_cvar (ext_var Gamma t) x)
    by trivial. rewrite H2. eapply IHt. trivial. simpl.
    eapply coercion_weakening_var with 0. apply typing_well_formed in H6.
    inversion H6. constructor; inversion H4; subst. apply remove_cvar_ty_weakening.
    trivial. apply wf_context_strengthening_cvar. trivial.
    simpl. eassumption. trivial.
  Case "ttapp".
    eapply remove_cvar_ty_weakening. trivial.
    apply wf_context_strengthening_cvar. trivial.
  Case "ttabs".
    assert (ext_tvar (remove_cvar Gamma x) = remove_cvar (ext_tvar Gamma) x) by
      trivial.
    rewrite H2. eapply IHt. trivial. simpl. eapply coercion_weakening_tvar.
    apply coercion_well_formed in H0. inversion H0. inversion H5. eassumption.
    eassumption. simpl. rewrite H1. trivial.
  Case "tcabs".
    assert (ext_cvar (remove_cvar Gamma x) (t, t0) =
            remove_cvar (ext_cvar Gamma (t, t0)) (S x)) by trivial.
    rewrite H2. eapply IHt. trivial. simpl. apply coercion_weakening.
    constructor. apply coercion_well_formed in H0. inversion H0. trivial.
    apply remove_cvar_ty_weakening. trivial.
    apply remove_cvar_ty_weakening. trivial.
    simpl. eassumption. simpl. trivial. apply remove_cvar_ty_weakening. trivial.
    apply remove_cvar_ty_weakening. trivial.
Qed.

Lemma subst_typ_preserves_coercion_ind : forall Gamma Gamma' c U1 U2 V X,
  subst_context V X Gamma Gamma' ->
  Gamma  |- c ; U1 ~ U2          ->
  Gamma' |- [X := V] c ; [X := V] U1 ~ [X := V] U2.
Proof with eauto.
  intros; generalize dependent Gamma'; generalize dependent X;
  generalize dependent V; coercion_cases (induction H0) Case; intros;
  simpl; try constructor; try (eapply C_Trans); try (eapply C_App);
  try (eapply subst_context_wf; eassumption; trivial);
  try (apply IHwell_formed_coercion; trivial);
  try (apply IHwell_formed_coercion1; trivial);
  try (apply IHwell_formed_coercion2; trivial).
  Case "C_Var".
    erewrite context_subst_get_cvar with (Gamma:=Gamma). erewrite H0.
    simpl. trivial. trivial.
  Case "C_Refl".
    eapply subst_preserves_well_formed_type. eassumption. trivial.
    eapply subst_context_wf. eassumption. trivial.
  Case "C_Forall".
    assert (X + 1 = S X) by omega. rewrite H1. apply IHwell_formed_coercion.
    constructor. trivial.
  Case "C_ALeft"; eapply C_ALeft. apply IHwell_formed_coercion...
  Case "C_ARight"; eapply C_ARight. apply IHwell_formed_coercion...
  Case "C_CLeft11"; eapply C_CLeft11. apply IHwell_formed_coercion...
  Case "C_CLeft12"; eapply C_CLeft12. apply IHwell_formed_coercion...
  Case "C_CRight"; eapply C_CRight. apply IHwell_formed_coercion...  
  Case "C_Inst".
    assert (X = 0 + X) by trivial. rewrite H2. rewrite tsubst_tsubst_prop. 
    rewrite tsubst_tsubst_prop. constructor.
    simpl in IHwell_formed_coercion. simpl.
    assert (S X = X + 1) by omega. rewrite H3.
    apply IHwell_formed_coercion. trivial. eapply subst_preserves_well_formed_type.
    simpl. eassumption. trivial. eapply subst_context_wf. eassumption.
    apply coercion_well_formed in H0. inversion H0. trivial.
Qed.

Lemma subst_typ_preserves_typing_ind : forall Gamma Gamma' t U V X,
  subst_context V X Gamma Gamma' ->
  Gamma |- t \in U               ->
  Gamma' |- [X := V]t \in [X := V]U.
Proof.
  intros. generalize dependent Gamma'. generalize dependent X. 
  generalize dependent V.
  has_type_cases (induction H0) Case; intros.
  Case "T_Var".
    constructor. eapply subst_context_wf. apply H1. trivial.
    simpl. erewrite context_subst_get_var with (Gamma:=Gamma). erewrite H0.
    simpl. trivial. trivial.
  Case "T_Abs".
    simpl. constructor. apply IHhas_type. constructor. trivial. 
    rewrite <- subst_type_in_type_correct. trivial.
  Case "T_App".
    simpl. econstructor. apply IHhas_type1. trivial. apply IHhas_type2. trivial.
  Case "T_TAbs".
    simpl. constructor. apply IHhas_type.
    assert (X + 1 = S X) by omega. rewrite H1. clear H1.
    constructor. trivial.
  Case "T_TApp".
    simpl. assert (X = 0 + X) by trivial. rewrite H3. clear H3. 
    rewrite tsubst_tsubst_prop. simpl. constructor. 
    assert (S X = X + 1) by omega.  rewrite H3. clear H3. 
    apply IHhas_type. trivial. eapply subst_preserves_well_formed_type. apply H2.
    trivial. eapply subst_context_wf. apply H2. trivial.
    eapply subst_context_wf. apply H2. trivial.
  Case "T_CAbs".
    simpl. constructor. apply IHhas_type. constructor. trivial.
    rewrite <- subst_type_in_type_correct. trivial.
    rewrite <- subst_type_in_type_correct. trivial.
    eapply subst_preserves_well_formed_type. eassumption.
    trivial. apply typing_well_formed in H0. inversion H0. inversion H4; subst.
    eapply subst_context_wf. eassumption. trivial.
    eapply subst_preserves_well_formed_type. eassumption.
    trivial. apply typing_well_formed in H0. inversion H0. inversion H4; subst.
    eapply subst_context_wf. eassumption. trivial.
  Case "T_CApp".    
    simpl. econstructor. simpl in IHhas_type.  apply IHhas_type. trivial.
    eapply subst_typ_preserves_coercion_ind. eassumption. trivial.
  Case "T_Coerce".
    simpl. econstructor.
    eapply subst_typ_preserves_coercion_ind. eassumption. eassumption.
    apply IHhas_type. trivial.
Qed.

Lemma subst_typ_preserves_typing : forall Gamma t U V,
  well_formed_type Gamma V   ->
  ext_tvar Gamma |- t \in U ->
  Gamma |- [0 := V]t \in [0 := V]U.
Proof.
  intros. eapply subst_typ_preserves_typing_ind. constructor.
  trivial. apply typing_well_formed in H0. inversion H0. inversion H2. trivial.
  trivial.
Qed.


End SUBSTPROP.