From Coq Require Import ZArith Lia Bool List Program.Equality.

From Coq Require Import FunctionalExtensionality PropExtensionality.

From CDF Require Import Sequences Separation.

Open Scope Z_scope.

CoInductive com: Type :=
  | PURE (x: Z)                         
  | LET (c: com) (f: Z -> com)          
  | IFTHENELSE (b: Z) (c1 c2: com)      
  | ALLOC (sz: nat)                     
  | GET (l: addr)                       
  | SET (l: addr) (v: Z)                
  | FREE (l: addr)                      
  | PICK (n: Z).

Definition SKIP: com := PURE 0.

Definition SEQ (c1 c2: com) := LET c1 (fun _ => c2).

Definition EITHER (c1 c2: com) := LET (PICK 2) (fun n => IFTHENELSE n c1 c2).

Inductive red: com * heap -> com * heap -> Prop :=
  | red_pick: forall n i h,
      0 <= i < n ->
      red (PICK n, h) (PURE i, h)
  | red_let_done: forall x f h,
      red (LET (PURE x) f, h) (f x, h)
  | red_let_step: forall c f h c' h',
      red (c, h) (c', h') ->
      red (LET c f, h) (LET c' f, h')
  | red_ifthenelse: forall b c1 c2 h,
      red (IFTHENELSE b c1 c2, h) ((if b =? 0 then c2 else c1), h)
  | red_alloc: forall sz (h: heap) l,
      (forall i, l <= i < l + Z.of_nat sz -> h i = None) ->
      l <> 0 ->
      red (ALLOC sz, h) (PURE l, hinit l sz h)
  | red_get: forall l (h: heap) v,
      h l = Some v ->
      red (GET l, h) (PURE v, h)
  | red_set: forall l v (h: heap),
      h l <> None ->
      red (SET l v, h) (SKIP, hupdate l v h)
  | red_free: forall l (h: heap),
      h l <> None ->
      red (FREE l, h) (SKIP, hfree l h).

Inductive immsafe: com * heap -> Prop :=
  | immsafe_pure: forall v h,
      immsafe (PURE v, h)
  | immsafe_let: forall c f h,
      immsafe (c, h) -> immsafe (LET c f, h)
  | immsafe_ifthenelse: forall b c1 c2 h,
      immsafe (IFTHENELSE b c1 c2, h)
  | immsafe_alloc: forall sz (h: heap) l,
      l <> 0 -> (forall i, l <= i < l + Z.of_nat sz -> h i = None) ->
      immsafe (ALLOC sz, h)
  | immsafe_get: forall l (h: heap),
      h l <> None -> immsafe (GET l, h)
  | immsafe_set: forall l v (h: heap),
      h l <> None -> immsafe (SET l v, h)
  | immsafe_free: forall l (h: heap),
      h l <> None -> immsafe (FREE l, h)
  | immsafe_pick: forall n h,
      immsafe (PICK n, h).

Definition precond := assertion.

Definition postcond := Z -> assertion.

Inductive safe: com -> heap -> postcond -> Prop :=
  | safe_done: forall v h (Q: postcond),
      Q v h ->
      safe (PURE v) h Q
  | safe_step: forall c h Q,
      match c with PURE _ => False | _ => True end ->
      immsafe (c, h) ->
      (forall c' h', red (c, h) (c', h') -> safe c' h' Q) ->
      safe c h Q.

Definition triple (P: precond) (c: com) (Q: postcond) :=
  forall h, P h -> safe c h Q.

Notation "⦃ P ⦄ c ⦃ Q ⦄" := (triple P c Q) (at level 90, c at next level).

Ltac inv H := inversion H; clear H; subst.

Lemma immsafe_frame: forall h' c h,
  immsafe (c, h) -> hdisjoint h h' -> immsafe (c, hunion h h').
Proof. intros h' c h IMM; dependent induction IMM; intros DISJ. - constructor. - constructor; auto. - constructor. - destruct (isfinite (hunion h h')) as [l' FIN]. apply immsafe_alloc with (Z.max 1 l'). lia. intros. apply FIN. lia. - constructor. cbn. destruct (h l) as [z|]; congruence. - constructor. cbn. destruct (h l) as [z|]; congruence. - constructor. cbn. destruct (h l) as [z|]; congruence. - constructor. Qed.

Lemma red_frame: forall h2 c h1 c' h',
  red (c, hunion h1 h2) (c', h') ->
  immsafe (c, h1) ->
  hdisjoint h1 h2 ->
  exists h1', red (c, h1) (c', h1') /\ hdisjoint h1' h2 /\ h' = hunion h1' h2.
Proof. intros until h'; intros RED; dependent induction RED; intros IMM DISJ; inv IMM. - exists h1; intuition auto. constructor; auto. - exists h1; intuition auto. constructor; auto. - edestruct IHRED as (h1' & R & D & U); eauto. exists h1'; intuition auto. constructor; auto. - exists h1; intuition auto. constructor; auto. - exists (hinit l sz h1); intuition auto. + constructor; auto. intros. apply H in H1. cbn in H1. destruct (h1 i) as [z|]; congruence. + red; cbn; intros i. assert (EITHER: l <= i < l + Z.of_nat sz \/ (i < l \/ l + Z.of_nat sz <= i)) by lia. destruct EITHER. * right. apply H in H1. cbn in H1. destruct (h1 i) as [z|], (h2 i) as [z'|]; congruence. * rewrite hinit_outside by auto. apply DISJ. + apply heap_extensionality; intros i; cbn. assert (EITHER: l <= i < l + Z.of_nat sz \/ (i < l \/ l + Z.of_nat sz <= i)) by lia. destruct EITHER. * rewrite ! hinit_inside by auto. auto. * rewrite ! hinit_outside by auto. auto. - exists h1; intuition auto. constructor; auto. cbn in H. destruct (h1 l) as [z|]; congruence. - exists (hupdate l v h1); intuition auto. + constructor; auto. + intros i; cbn. generalize (DISJ i). destruct (Z.eq_dec l i); intuition congruence. + apply heap_extensionality; intros i; cbn. destruct (Z.eq_dec l i); auto. - exists (hfree l h1); intuition auto. + constructor; auto. + intros i; cbn. generalize (DISJ i). destruct (Z.eq_dec l i); intuition congruence. + apply heap_extensionality; intros i; cbn. destruct (Z.eq_dec l i); auto. subst i. generalize (DISJ l). intuition. Qed.

Lemma safe_frame:
  forall (R: assertion) h', R h' ->
  forall c h Q,
  safe c h Q -> hdisjoint h h' -> safe c (hunion h h') (fun v => Q v ** R).
Proof. induction 2; intros DISJ. - constructor. exists h, h'; auto. - constructor. auto. apply immsafe_frame; auto. intros. edestruct red_frame as (h1' & RED1 & D & U); eauto. subst h'0. apply H3; auto. Qed.

Lemma triple_frame: forall P c Q R,
  ⦃ P ⦄ c ⦃ Q ⦄ ->
  ⦃ P ** R ⦄ c ⦃ fun v => Q v ** R ⦄.
Proof. intros P c Q R TR h (h1 & h2 & P1 & R2 & D & U). subst h. apply safe_frame; auto. Qed.

Lemma triple_get: forall l v,
  ⦃ contains l v ⦄ GET l ⦃ fun v' => (v' = v) //\\ contains l v ⦄.
Proof. intros l v h P. assert (L: h l = Some v). red in P. subst h. apply hupdate_same. constructor; auto. - constructor. congruence. - intros c' h' RED. inv RED. constructor. split; auto; congruence. Qed.

Lemma triple_set: forall l v,
  ⦃ valid l ⦄ SET l v ⦃ fun _ => contains l v ⦄.
Proof. intros l v h (v0 & P). assert (L: h l = Some v0). red in P; subst h; apply hupdate_same. constructor; auto. - constructor. congruence. - intros c' h' RED. inv RED. constructor. red in P; subst h. red. apply heap_extensionality; intros l'; cbn. destruct (Z.eq_dec l l'); auto. Qed.

Fixpoint valid_N (l: addr) (sz: nat) : assertion :=
  match sz with O => emp | S sz => valid l ** valid_N (l + 1) sz end.

Remark valid_N_init: forall sz l,
  (valid_N l sz) (hinit l sz hempty).
Proof. intro sz. induction sz as [ | sz]; intros l; cbn. - red; auto. - exists (hupdate l 0 hempty), (hinit (l + 1) sz hempty); intuition auto. + exists 0. red; auto. + intros x. unfold hupdate, hempty; cbn. destruct (Z.eq_dec l x); auto. right. rewrite hinit_outside by lia. auto. + apply heap_extensionality; intros x. cbn. destruct (Z.eq_dec l x); auto. Qed.

Lemma triple_alloc: forall sz,
  ⦃ emp ⦄
  ALLOC sz
  ⦃ fun l => (l <> 0) //\\ valid_N l sz ⦄.
Proof. intros sz h P. red in P. subst h. constructor; auto. - apply immsafe_alloc with 1; intros. + lia. + auto. - intros c' h' RED; inv RED. constructor. split; auto. apply valid_N_init; auto. Qed.

Lemma triple_free: forall l,
  ⦃ valid l ⦄
  FREE l
  ⦃ fun _ => emp ⦄.
Proof. intros l h (v0 & P). red in P. assert (L: h l = Some v0). subst h. apply hupdate_same. constructor; auto. - constructor. congruence. - intros c' h' RED; inv RED. constructor. red. apply heap_extensionality; intros x. cbn. destruct (Z.eq_dec l x); auto. Qed.

Lemma safe_pure: forall v h Q,
  safe (PURE v) h Q -> Q v h.
Proof. intros. inv H. - auto. - contradiction. Qed.

Lemma safe_red: forall c h Q c' h',
  safe  c h Q -> red (c, h) (c', h') -> safe c' h' Q.
Proof. intros. inv H. - inv H0. - eauto. Qed.

Lemma safe_immsafe: forall c h Q,
  safe c h Q -> immsafe (c, h).
Proof. intros. inv H. - constructor. - auto. Qed.

Lemma safe_let: forall (Q R: postcond) f,
  (forall v h', Q v h' -> safe (f v) h' R) ->
  forall c h,
  safe c h Q ->
  safe (LET c f) h R.
Proof. intros Q R f POST. induction 1. - constructor; auto. + constructor. constructor. + intros c' h' RED; inv RED. apply POST; auto. inv H1. - constructor; auto. + constructor; auto. + intros c' h' RED; inv RED. contradiction. eauto. Qed.

Lemma safe_consequence: forall (Q Q': postcond),
  (forall v, Q v -->> Q' v) ->
  forall c h, safe c h Q -> safe c h Q'.
Proof. intros Q Q' IMP. induction 1. - apply safe_done. apply IMP. assumption. - apply safe_step; auto. Qed.

Lemma triple_pure: forall P v (Q: postcond),
  P -->> Q v ->
  ⦃ P ⦄ PURE v ⦃ Q ⦄.
Proof. intros; intros h Ph. constructor. apply H; auto. Qed.

Lemma triple_let:
  forall c f (P: precond) (Q R: postcond),
  ⦃ P ⦄ c ⦃ Q ⦄ ->
  (forall v, ⦃ Q v ⦄ f v ⦃ R ⦄) ->
  ⦃ P ⦄ LET c f ⦃ R ⦄.
Proof. intros until R; intros HR1 HR2 h Ph. apply safe_let with Q. apply HR2. apply HR1. auto. Qed.

Lemma triple_ifthenelse: forall b c1 c2 P Q,
  ⦃ (b <> 0) //\\ P ⦄ c1 ⦃ Q ⦄ ->
  ⦃ (b = 0) //\\ P ⦄ c2 ⦃ Q ⦄ ->
  ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄.
Proof. intros until Q; intros HR1 HR2 h Ph. constructor; auto. - constructor. - intros c' h' RED; inv RED. destruct (Z.eqb_spec b 0). + apply HR2. split; auto. + apply HR1. split; auto. Qed.

Lemma triple_consequence: forall P P' c Q' Q,
  ⦃ P' ⦄ c ⦃ Q' ⦄ ->
  P -->> P' -> (forall v, Q' v -->> Q v) ->
  ⦃ P ⦄ c ⦃ Q ⦄.
Proof. intros; red; intros. apply safe_consequence with Q'; auto. Qed.

Lemma triple_pick: forall n,
  ⦃ emp ⦄
  PICK n
  ⦃ fun i => pure (0 <= i < n) ⦄.
Proof. intros n h Ph. constructor; auto. - constructor. - intros c' h' RED; inv RED. constructor. split; auto. Qed.

Lemma triple_consequence_pre: forall P P' c Q,
  ⦃ P' ⦄ c ⦃ Q ⦄ ->
  P -->> P' ->
  ⦃ P ⦄ c ⦃ Q ⦄.
Proof. intros. apply triple_consequence with P' Q; auto. intros; red; auto. Qed.

Lemma triple_consequence_post: forall P c Q Q',
  ⦃ P ⦄ c ⦃ Q' ⦄ ->
  (forall v, Q' v -->> Q v) ->
  ⦃ P ⦄ c ⦃ Q ⦄.
Proof. intros. apply triple_consequence with P Q'; auto. red; auto. Qed.

Lemma triple_lift_pure: forall (P: Prop) P' c Q,
  (P -> ⦃ P' ⦄ c ⦃ Q ⦄) ->
  ⦃ P //\\ P' ⦄ c ⦃ Q ⦄.
Proof. intros. intros h [P1 P2]. apply H; auto. Qed.

Lemma triple_lift_exists: forall (X: Type) (P: X -> assertion) c Q,
  (forall x, ⦃ P x ⦄ c ⦃ Q ⦄) ->
  ⦃ aexists P ⦄ c ⦃ Q ⦄.
Proof. intros. intros h (x & Px). apply (H x); auto. Qed.

Lemma triple_ifthen: forall b c1 c2 P Q,
  b <> 0 -> ⦃ P ⦄ c1 ⦃ Q ⦄ ->
  ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄.
Proof. intros. apply triple_ifthenelse; apply triple_lift_pure; intros. - auto. - lia. Qed.

Lemma triple_ifelse: forall b c1 c2 P Q,
  b = 0 -> ⦃ P ⦄ c2 ⦃ Q ⦄ ->
  ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄.
Proof. intros. apply triple_ifthenelse; apply triple_lift_pure; intros. - lia. - auto. Qed.

Lemma unroll_com: forall c,
  c = match c with
      | PURE x => PURE x
      | LET c f => LET c f
      | IFTHENELSE b c1 c2 => IFTHENELSE b c1 c2
      | ALLOC sz => ALLOC sz
      | GET l => GET l
      | SET l v => SET l v
      | FREE l => FREE l
      | PICK n => PICK n
      end.
Proof. destruct c; auto. Qed.

Fixpoint list_at (a: addr) (l: list Z) : assertion :=
  match l with
  | nil => (a = 0) //\\ emp
  | h :: t => (a <> 0) //\\ aexists (fun a' => contains a h ** contains (a + 1) a' ** list_at a' t)
  end.

Definition list_cons (n: Z) (a: addr) : com :=
  LET (ALLOC 2) (fun a' => SEQ (SET a' n) (SEQ (SET (a' + 1) a) (PURE a'))).

Lemma list_cons_correct: forall a n l,
    ⦃ list_at a l ⦄
  list_cons n a
    ⦃ fun a' => list_at a' (n :: l) ⦄.
Proof. intros. eapply triple_let. rewrite <- sepconj_emp at 1. apply triple_frame. apply triple_alloc. intros b; simpl. rewrite lift_pureconj, ! sepconj_assoc, sepconj_emp. apply triple_lift_pure; intros H1. eapply triple_let. apply triple_frame. apply triple_set. simpl; intros _. eapply triple_let. rewrite sepconj_pick2. apply triple_frame. apply triple_set. simpl; intros _. rewrite sepconj_pick2. apply triple_pure. intros h A. split. auto. exists a; auto. Qed.

CoFixpoint list_length_rec (a: addr) (len: Z) : com :=
  IFTHENELSE a (LET (GET (a + 1)) (fun t => list_length_rec t (len + 1))) (PURE len).

Definition list_length (a: addr) : com := list_length_rec a 0.

Lemma list_length_rec_correct: forall l a len,
    ⦃ list_at a l ⦄
  list_length_rec a len
    ⦃ fun len' => (len' = len + Z.of_nat (List.length l)) //\\ list_at a l ⦄.
Proof. intro l. induction l as [ | h t]; intros; rewrite (unroll_com (list_length_rec a len)); cbn. - apply triple_lift_pure; intro H1. apply triple_ifelse; auto. apply triple_pure. intros h H2. split. lia. split; auto. - apply triple_lift_pure; intro H1. apply triple_lift_exists; intros a'. apply triple_ifthen; auto. eapply triple_let. rewrite sepconj_pick2. apply triple_frame. apply triple_get. simpl. intros a''. rewrite lift_pureconj. apply triple_lift_pure; intros H3. subst a''. rewrite sepconj_swap3. eapply triple_consequence_post. apply triple_frame. apply IHt. intros len'; simpl. rewrite lift_pureconj. rewrite <- sepconj_swap3, sepconj_pick2. intros h1 (A & B). split. lia. split. auto. exists a'; auto. Qed.

Corollary list_length_correct: forall l a,
    ⦃ list_at a l ⦄
  list_length a
    ⦃ fun len => (len = Z.of_nat (length l)) //\\ list_at a l ⦄.
Proof. intros. apply list_length_rec_correct. Qed.

CoFixpoint list_concat_rec (a1 a2: addr) : com :=
  LET (GET (a1 + 1)) (fun t => IFTHENELSE t (list_concat_rec t a2) (SET (a1 + 1) a2)).

Definition list_concat (a1 a2: addr) : com :=
  IFTHENELSE a1 (SEQ (list_concat_rec a1 a2) (PURE a1)) (PURE a2).

Lemma list_concat_rec_correct: forall l2 a2 l1 a1,
  a1 <> 0 ->
    ⦃ list_at a1 l1 ** list_at a2 l2 ⦄
  list_concat_rec a1 a2
    ⦃ fun _ => list_at a1 (l1 ++ l2) ⦄.
Proof. intros l2 a2 l1. induction l1 as [ | h1 t1]; intros; rewrite (unroll_com (list_concat_rec a1 a2)); simpl. - rewrite lift_pureconj. apply triple_lift_pure; intros. lia. - rewrite lift_pureconj. apply triple_lift_pure. intros H1. rewrite lift_aexists. apply triple_lift_exists. intros a'. rewrite sepconj_assoc. eapply triple_let. + rewrite sepconj_assoc, sepconj_pick2. apply triple_frame. apply triple_get. + intros t. simpl. rewrite lift_pureconj. apply triple_lift_pure. intros H2; subst t. apply triple_ifthenelse. * apply triple_lift_pure. intros H2. rewrite <- sepconj_assoc, sepconj_comm. eapply triple_consequence_post. apply triple_frame. apply IHt1. auto. simpl. intros _. rewrite sepconj_pick2, sepconj_swap3. intros h P. split; auto. exists a'; auto. * apply triple_lift_pure. intros H2. eapply triple_consequence_post. apply triple_frame. eapply triple_consequence_pre. apply triple_set. intros h P; exists a'; auto. simpl. intros _. rewrite sepconj_pick2, sepconj_pick3. destruct t1; simpl. ** rewrite lift_pureconj, sepconj_emp. intros h (A & B). split; auto. exists a2; auto. ** rewrite lift_pureconj. intros h (A & B). lia. Qed.

Lemma list_concat_correct: forall l1 a1 l2 a2,
    ⦃ list_at a1 l1 ** list_at a2 l2 ⦄
  list_concat a1 a2
    ⦃ fun a => list_at a (l1 ++ l2) ⦄.
Proof. intros. unfold list_concat. apply triple_ifthenelse. - apply triple_lift_pure; intros H1. eapply triple_let. apply list_concat_rec_correct; auto. simpl. intros _. apply triple_pure. red; auto. - apply triple_lift_pure; intros H1. destruct l1; simpl. + apply triple_pure. rewrite lift_pureconj, sepconj_emp. intros h (A & B); auto. + rewrite lift_pureconj. apply triple_lift_pure. intros; lia. Qed.

CoFixpoint list_rev_rec (a p: addr) : com :=
  IFTHENELSE a
    (LET (GET (a + 1)) (fun n =>
     SEQ (SET (a + 1) p)
         (list_rev_rec n a)))
    (PURE p).

Definition list_rev (a: addr) : com := list_rev_rec a 0.

Lemma list_rev_rec_correct: forall l a l' p,
    ⦃ list_at a l ** list_at p l' ⦄
  list_rev_rec a p
    ⦃ fun x => list_at x (List.rev_append l l') ⦄.
Proof. intro l. induction l as [ | hd l]; intros; rewrite (unroll_com (list_rev_rec a p)); simpl. - rewrite lift_pureconj, sepconj_emp. apply triple_lift_pure; intros H1. apply triple_ifelse; auto. apply triple_pure. red; auto. - rewrite lift_pureconj; apply triple_lift_pure; intros H1. rewrite lift_aexists; apply triple_lift_exists; intros a'. apply triple_ifthen; auto. eapply triple_let. rewrite ! sepconj_assoc, sepconj_pick2. apply triple_frame. apply triple_get. intros a''. simpl. rewrite lift_pureconj. apply triple_lift_pure. intros H3. subst a''. eapply triple_let. apply triple_frame. eapply triple_consequence_pre. apply triple_set. intros h P; exists a'; auto. simpl. intros _. rewrite sepconj_pick2, sepconj_pick3. eapply triple_consequence_pre. apply IHl. simpl. apply sepconj_imp_r. intros h A. split; auto. exists p; auto. Qed.

Lemma list_rev_correct: forall a l,
    ⦃ list_at a l ⦄
  list_rev a
    ⦃ fun x => list_at x (List.rev l) ⦄.
Proof. intros. rewrite List.rev_alt. eapply triple_consequence_pre. apply list_rev_rec_correct. simpl. rewrite sepconj_comm, lift_pureconj, sepconj_emp. intros h A; split; auto. Qed.

Module AlternateSeplog.

Definition Hoare (P: precond) (c: com) (Q: postcond) : Prop :=
  forall h, P h -> safe c h Q.

Definition triple (P: precond) (c: com) (Q: postcond) :=
  forall (R: assertion), Hoare (P ** R) c (fun v => Q v ** R).

Notation "⦃ P ⦄ c ⦃ Q ⦄" := (triple P c Q) (at level 90, c at next level).

Lemma triple_frame: forall P c Q R,
  ⦃ P ⦄ c ⦃ Q ⦄ ->
  ⦃ P ** R ⦄ c ⦃ fun v => Q v ** R ⦄.
Proof. intros P c Q R TR R'. rewrite sepconj_assoc. replace (fun v => (Q v ** R) ** R') with (fun v => Q v ** (R ** R')). apply TR. apply functional_extensionality; intros. rewrite sepconj_assoc; auto. Qed.

Lemma triple_get: forall l v,
  ⦃ contains l v ⦄ GET l ⦃ fun v' => (v' = v) //\\ contains l v ⦄.
Proof. intros l v R h (h1 & h2 & H1 & H2 & D & U). assert (L1: h1 l = Some v). red in H1. subst h1. apply hupdate_same. assert (L: h l = Some v). intros. rewrite U; simpl. rewrite L1; auto. constructor; auto. - constructor. congruence. - intros c' h' RED. inv RED. constructor. exists h1, h2. unfold pureconj. intuition congruence. Qed.

Lemma triple_set: forall l v,
  ⦃ valid l ⦄ SET l v ⦃ fun _ => contains l v ⦄.
Proof. intros l v R h (h1 & h2 & H1 & H2 & D & U). destruct H1 as (v0 & H1). red in H1. assert (L1: h1 l = Some v0). subst h1; apply hupdate_same. assert (L: h l = Some v0). rewrite U; cbn. rewrite L1; auto. constructor; auto. - constructor. congruence. - intros c' h' RED. inv RED. constructor. exists (hupdate l v hempty), h2. split. red. auto. split. auto. split. intro l'. specialize (D l'). cbn in *. destruct D; auto. destruct (Z.eq_dec l l'); auto. congruence. apply heap_extensionality; intros l'; cbn. destruct (Z.eq_dec l l'); auto. Qed.

Remark valid_N_init:
  forall (R: assertion) sz l h,
  R h ->
  (forall i, l <= i < l + Z.of_nat sz -> h i = None) ->
  (valid_N l sz ** R) (hinit l sz h).
Proof. intros R sz. induction sz as [ | sz]; intros l h Rh EMPTY; cbn. - rewrite sepconj_emp. auto. - rewrite sepconj_assoc. exists (hupdate l 0 hempty), (hinit (l + 1) sz h). split. exists 0. red; auto. split. apply IHsz. auto. intros. apply EMPTY. lia. split. intros x. unfold hupdate, hempty; cbn. destruct (Z.eq_dec l x); auto. right. rewrite hinit_outside by lia. apply EMPTY; lia. apply heap_extensionality; intros x. cbn. destruct (Z.eq_dec l x); auto. Qed.

Lemma triple_alloc: forall sz,
  ⦃ emp ⦄
  ALLOC sz
  ⦃ fun l => (l <> 0) //\\ valid_N l sz ⦄.
Proof. intros sz R h H. rewrite sepconj_emp in H. constructor; auto. - destruct (isfinite h) as (l0 & FIN). apply immsafe_alloc with (Z.max l0 1); intros. + lia. + apply FIN. lia. - intros c' h' RED; inv RED. constructor. rewrite lift_pureconj; split. auto. apply valid_N_init; auto. Qed.

Lemma triple_free: forall l,
  ⦃ valid l ⦄
  FREE l
  ⦃ fun _ => emp ⦄.
Proof. intros l R h (h1 & h2 & H1 & H2 & D & U). destruct H1 as (v0 & H1). assert (L1: h1 l = Some v0). rewrite H1. apply hupdate_same. assert (L: h l = Some v0). rewrite U; cbn. rewrite L1. auto. constructor; auto. - constructor. congruence. - intros c' h' RED; inv RED. constructor. rewrite sepconj_emp. replace (hfree l (hunion h1 h2)) with h2; auto. apply heap_extensionality; intros x. generalize (D x); rewrite H1; cbn. destruct (Z.eq_dec l x); auto. intuition congruence. Qed.

Lemma Hoare_pure: forall P v (Q: postcond),
  P -->> Q v ->
  Hoare P (PURE v) Q.
Proof. intros; intros h Ph. constructor. apply H; auto. Qed.

Lemma triple_pure: forall P v (Q: postcond),
  P -->> Q v ->
  ⦃ P ⦄ PURE v ⦃ Q ⦄.
Proof. intros; intros R. apply Hoare_pure. apply sepconj_imp_l; auto. Qed.

Lemma Hoare_let:
  forall c f (P: precond) (Q R: postcond),
  Hoare P c Q ->
  (forall v, Hoare (Q v) (f v) R) ->
  Hoare P (LET c f) R.
Proof. intros until R; intros HR1 HR2 h Ph. apply safe_let with Q. apply HR2. apply HR1. auto. Qed.

Lemma triple_let:
  forall c f (P: precond) (Q R: postcond),
  ⦃ P ⦄ c ⦃ Q ⦄ ->
  (forall v, ⦃ Q v ⦄ f v ⦃ R ⦄) ->
  ⦃ P ⦄ LET c f ⦃ R ⦄.
Proof. intros c f P Q R TR1 TR2 R'. apply Hoare_let with (fun v => Q v ** R'). apply TR1. intros. apply TR2. Qed.

Lemma Hoare_ifthenelse: forall b c1 c2 P Q,
  Hoare ((b <> 0) //\\ P) c1 Q ->
  Hoare ((b = 0) //\\ P) c2 Q ->
  Hoare P (IFTHENELSE b c1 c2) Q.
Proof. intros until Q; intros HR1 HR2 h Ph. constructor; auto. - constructor. - intros c' h' RED; inv RED. destruct (Z.eqb_spec b 0). + apply HR2. split; auto. + apply HR1. split; auto. Qed.

Lemma triple_ifthenelse: forall b c1 c2 P Q,
  ⦃ (b <> 0) //\\ P ⦄ c1 ⦃ Q ⦄ ->
  ⦃ (b = 0) //\\ P ⦄ c2 ⦃ Q ⦄ ->
  ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄.
Proof. intros b c1 c2 P Q TR1 TR2 R. apply Hoare_ifthenelse; rewrite <- lift_pureconj; auto. Qed.

Lemma Hoare_consequence: forall P P' c Q' Q,
  Hoare P' c Q' ->
  P -->> P' -> (forall v, Q' v -->> Q v) ->
  Hoare P c Q.
Proof. intros; red; intros. apply safe_consequence with Q'; auto. Qed.

Lemma triple_consequence: forall P P' c Q' Q,
  ⦃ P' ⦄ c ⦃ Q' ⦄ ->
  P -->> P' -> (forall v, Q' v -->> Q v) ->
  ⦃ P ⦄ c ⦃ Q ⦄.
Proof. intros; red; intros. apply Hoare_consequence with (P' ** R) (fun v => Q' v ** R). apply H. apply sepconj_imp_l; auto. intros; apply sepconj_imp_l; auto. Qed.

Lemma Hoare_pick: forall P n,
  Hoare P (PICK n) (fun i => (0 <= i < n) //\\ P).
Proof. intros P n h Ph. constructor; auto. - constructor. - intros c' h' RED; inv RED. constructor. split; auto. Qed.

Lemma triple_pick: forall n,
  ⦃ emp ⦄
  PICK n
  ⦃ fun i => pure (0 <= i < n) ⦄.
Proof. intros; intros R. rewrite sepconj_emp. eapply Hoare_consequence with (P' := R). apply Hoare_pick. red; auto. intros; red; intros. rewrite pureconj_sepconj. auto. Qed.

End AlternateSeplog.

Lemma triple_frame_consequence: forall R P c Q P' Q',
  ⦃ P ⦄ c ⦃ Q ⦄ ->
  P' -->> P ** R ->
  (forall v, Q v ** R -->> Q' v) ->
  ⦃ P' ⦄ c ⦃ Q' ⦄.
Proof. intros. apply triple_consequence with (P ** R) (fun v => Q v ** R); auto. apply triple_frame; auto. Qed.

Lemma triple_ramification: forall P c Q P' Q',
 ⦃ P ⦄ c ⦃ Q ⦄ ->
  P' -->> P ** (aforall (fun v => Q v --* Q' v)) ->
  ⦃ P' ⦄ c ⦃ Q' ⦄.
Proof. intros. eapply triple_frame_consequence with (R := aforall (fun v => Q v --* Q' v)). eassumption. assumption. intros v h (h1 & h2 & Q1 & W2 & D & U). apply (wand_cancel (Q v)). exists h1, h2; auto. Qed.

Definition wp (c: com) (Q: postcond) : precond :=
  aexists (fun P => ⦃ P ⦄ c ⦃ Q ⦄ //\\ P).

Lemma wp_precond: forall c Q,
  ⦃ wp c Q ⦄ c ⦃ Q ⦄.
Proof. intros c Q h (P & T & C). apply T. auto. Qed.

Lemma wp_weakest: forall P c Q,
  ⦃ P ⦄ c ⦃ Q ⦄ ->
  P -->> wp c Q.
Proof. intros P c Q T h Ph. exists P; split; auto. Qed.

Corollary wp_equiv: forall P c Q,
  ⦃ P ⦄ c ⦃ Q ⦄ <-> (P -->> wp c Q).
Proof. intros; split; intros. - apply wp_weakest; auto. - apply triple_consequence_pre with (wp c Q); auto using wp_precond. Qed.

Definition wp' (c: com) (Q: postcond) : precond :=
  fun h => safe c h Q.

Lemma wp'_precond: forall c Q,
  ⦃ wp' c Q ⦄ c ⦃ Q ⦄.
Proof. intros c Q h SAFE. apply SAFE. Qed.

Lemma wp'_weakest: forall P c Q,
  ⦃ P ⦄ c ⦃ Q ⦄ ->
  P -->> wp' c Q.
Proof. intros; intros h Ph. apply H. auto. Qed.

Lemma wp_consequence: forall (Q Q': postcond) c,
  (forall v, Q v -->> Q' v) ->
  wp c Q -->> wp c Q'.
Proof. intros. apply wp_weakest. apply triple_consequence_post with Q; auto using wp_precond. Qed.

Lemma wp_frame: forall R c Q,
  wp c Q ** R -->> wp c (fun v => Q v ** R).
Proof. intros. apply wp_weakest. apply triple_frame. apply wp_precond. Qed.

Corollary wp_frame_consequence: forall R Q c Q',
  (forall v, Q v ** R -->> Q' v) ->
  wp c Q ** R -->> wp c Q'.
Proof. intros; red; intros. apply wp_consequence with (fun v => Q v ** R). assumption. apply wp_frame; auto. Qed.

Ltac custom_tac3 H0 := intros; apply H0.

Ltac custom_tac15 H0 H1 := exists H0, H1; auto.

Corollary wp_ramification: forall c Q Q',
  wp c Q ** aforall (fun v => Q v --* Q' v) -->> wp c Q'.
Proof. custom_tac3 wp_frame_consequence. intros v h ( h1 & h2 & A & B & D & U). apply ( wand_cancel ( Q v)). custom_tac15 h1 h2. Qed.

Lemma wp_pure: forall (Q: postcond) v,
  Q v -->> wp (PURE v) Q.
Proof. intros. apply wp_weakest. apply triple_pure. red; auto. Qed.

Lemma wp_let: forall c f Q,
  wp c (fun v => wp (f v) Q) -->> wp (LET c f) Q.
Proof. intros. apply wp_weakest. eapply triple_let. apply wp_precond. intros. apply wp_precond. Qed.

Lemma wp_ifthenelse: forall b c1 c2 Q,
  (if b =? 0 then wp c2 Q else wp c1 Q) -->> wp (IFTHENELSE b c1 c2) Q.
Proof. intros. apply wp_weakest. apply triple_ifthenelse. - apply triple_consequence_pre with (wp c1 Q). apply wp_precond. intros h (A & B). rewrite <- Z.eqb_neq in A. rewrite A in B. auto. - apply triple_consequence_pre with (wp c2 Q). apply wp_precond. intros h (A & B). subst b. auto. Qed.

Lemma wp_alloc: forall sz Q,
  aforall (fun l => (l <> 0) //\\ valid_N l sz --* Q l) -->> wp (ALLOC sz) Q.
Proof. intros; red; intros. apply wp_ramification with (Q := fun l => (l <> 0) //\\ valid_N l sz). apply sepconj_imp_l with emp. apply wp_weakest. apply triple_alloc. rewrite sepconj_emp. assumption. Qed.

Lemma wp_get: forall l v Q,
  contains l v ** (contains l v --* Q v) -->> wp (GET l) Q.
Proof. intros. assert (W: contains l v -->> wp (GET l) (fun v' => (v' = v) //\\ contains l v)). apply wp_weakest. apply triple_get. intros; red; intros. eapply wp_ramification. eapply sepconj_imp_l. eexact W. eapply sepconj_imp_r. 2: eexact H. intros h' H' v' h'' D (A & B). subst v'. apply H'; auto. Qed.

Lemma wp_set: forall l v Q,
  valid l ** aforall (fun v' => (contains l v --* Q v')) -->> wp (SET l v) Q.
Proof. intros. assert (W: valid l -->> wp (SET l v) (fun _ => contains l v)). apply wp_weakest. apply triple_set. intros; red; intros. eapply wp_ramification. eapply sepconj_imp_l. eexact W. eapply sepconj_imp_r. 2: eexact H. red; auto. Qed.

Corollary wp_set': forall l v Q,
  valid l ** (contains l v --* Q) -->> wp (SET l v) (fun _ => Q).
Proof. intros; red; intros. apply wp_set. eapply sepconj_imp_r. - instantiate (1 := contains l v --* Q). intros h' H' v'. auto. - eauto. Qed.

Lemma wp_free: forall l Q,
  valid l ** aforall (fun v' => Q v') -->> wp (FREE l) Q.
Proof. intros. assert (W: valid l -->> wp (FREE l) (fun _ => emp)). apply wp_weakest. apply triple_free. intros; red; intros. eapply wp_ramification. eapply sepconj_imp_l. eexact W. eapply sepconj_imp_r. 2: eexact H. red; intros. intros v h' D E. rewrite E in *. rewrite hunion_comm, hunion_empty by HDISJ. apply H0. Qed.

Corollary wp_free': forall l Q,
  valid l ** Q -->> wp (FREE l) (fun _ => Q).
Proof. intros; red; intros. apply wp_free. eapply sepconj_imp_r. - instantiate (1 := Q). intros h' H' v'. auto. - eauto. Qed.

Lemma wp_pick: forall n Q,
  aforall (fun i => pure (0 <= i < n) --* Q i) -->> wp (PICK n) Q.
Proof. intros. assert (W: emp -->> wp (PICK n) (fun i => pure (0 <= i < n))). apply wp_weakest. apply triple_pick. intros; red; intros. eapply wp_ramification. eapply sepconj_imp_l. eexact W. eapply sepconj_imp_r. 2: rewrite sepconj_emp; eexact H. red; auto. Qed.

