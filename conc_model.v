(* Extending the block model to concurrency. *)
Require Import Coqlib.
Require Import Util.
Require Import Arith.
Require Import block_model.
Import ListNotations.
Import Bool.
Import EquivDec.
Import CoqEqDec.

Local Close Scope Z.

Set Implicit Arguments.

Section Concurrency.
  Context `(ML : Memory_Layout) {thread : Type}.

  Definition seq_con := @block_model.consistent _ _ _ ML.
  Definition mem_op := mem_op block val.

  Class MM_base (conc_op : Type) :=
    { thread_of : conc_op -> thread;
      to_seq : conc_op -> list mem_op;
      lower := fun m => flatten (map to_seq m);
      synchronizes_with : conc_op -> conc_op -> Prop;
      drop_b_reads : block -> list conc_op -> list conc_op;
      drop_b_reads_spec : forall b ops, lower (drop_b_reads b ops) =
       filter (fun op => not_read op || negb (beq (block_of op) b)) (lower ops);
      read_safe : forall c i p v
        (Hread : nth_error (to_seq c) i = Some (MRead p v)) j (Hlt : j < i) v',
        nth_error (to_seq c) j <> Some (MWrite p v') }.

  Context `{Mb : MM_base}.

  Definition mem := ilist conc_op.

  Section Happens_Before.

  Inductive happens_before (m : mem) i j : Prop :=
  | hb_prog (Hlt : i < j) a (Ha : inth m i = Some a) b (Hb : inth m j = Some b)
      (Hthread : thread_of a = thread_of b) : happens_before m i j
  | hb_sync (Hlt : i < j) a (Ha : inth m i = Some a) b (Hb : inth m j = Some b)
      (Hsync : synchronizes_with a b) : happens_before m i j
  | hb_trans k (Hi : happens_before m i k) (Hj : happens_before m k j) :
      happens_before m i j.

  Lemma hb_lt : forall m i j, happens_before m i j -> i < j.
  Proof. intros; induction H; clarify; abstract omega. Qed.
  Corollary hb_irrefl : forall m i, ~happens_before m i i.
  Proof. repeat intro; exploit hb_lt; eauto; abstract omega. Qed.
  Corollary hb_antisym : forall m i j, happens_before m i j ->
    ~happens_before m j i.
  Proof. intros ? ? ? H1 H2; generalize (hb_lt H1), (hb_lt H2); abstract omega. 
  Qed.

  Lemma hb_app : forall m1 m2 i j m2' (Hhb : happens_before (iapp m1 m2) i j)
    (Hi : i < length m1) (Hj : j < length m1), happens_before (iapp m1 m2') i j.
  Proof.
    intros; induction Hhb.
    - eapply hb_prog; eauto; rewrite iapp_nth in *; clarify.
    - eapply hb_sync; eauto; rewrite iapp_nth in *; clarify.
    - generalize (hb_lt Hhb2); intro.
      generalize (lt_trans _ _ _ H Hj); clarify.
      eapply hb_trans; eauto.
  Qed.
  
  Corollary hb_app_impl : forall m1 m2 i j
    (Hhb : happens_before (iapp m1 m2) i j)
    (Hi : i < length m1) (Hj : j < length m1), happens_before m1 i j.
  Proof.
    intros; exploit hb_app; eauto.
    rewrite iapp_nil_ilist; auto.
  Qed.

  Lemma hb_app' : forall m1 m2 i j m1' (Hhb : happens_before (iapp m1 m2) i j)
    (Hi : ~i < length m1) (Hj : ~j < length m1),
    happens_before (iapp m1' m2)
      (i - length m1 + length m1') (j - length m1 + length m1').
  Proof.
    intros; induction Hhb.
    - rewrite iapp_nth in *; clarify.
      eapply hb_prog; eauto; try rewrite iapp_nth.
      + abstract omega.
      + destruct (lt_dec (i - length m1 + length m1') (length m1'));
          [abstract omega|].
        rewrite NPeano.Nat.add_sub; auto.
      + destruct (lt_dec (j - length m1 + length m1') (length m1'));
          [abstract omega|].
        rewrite NPeano.Nat.add_sub; auto.
    - rewrite iapp_nth in *; clarify.
      eapply hb_sync; eauto; try rewrite iapp_nth.
      + abstract omega.
      + destruct (lt_dec (i - length m1 + length m1') (length m1'));
          [abstract omega|].
        rewrite NPeano.Nat.add_sub; auto.
      + destruct (lt_dec (j - length m1 + length m1') (length m1'));
          [abstract omega|].
        rewrite NPeano.Nat.add_sub; auto.
    - generalize (hb_lt Hhb1); intro.
      destruct (lt_dec k (length m1)); [abstract omega | clarify].
      eapply hb_trans; eauto.
  Qed.

  Corollary hb_app'_eq : forall m1 m2 i j m1' (Hlen : length m1' = length m1)
    (Hhb : happens_before (iapp m1 m2) i j) (Hi : ~ i < length m1)
    (Hj : ~ j < length m1), happens_before (iapp m1' m2) i j.
  Proof.
    intros; generalize (hb_app' _ _ m1' Hhb); clarify.
    rewrite Hlen, NPeano.Nat.sub_add, NPeano.Nat.sub_add in *; auto; omega.
  Qed.

  Definition hbe m i j := happens_before m i j \/ i = j.

  Lemma hbe_app : forall m1 m2 i j m2' (Hhb : hbe (iapp m1 m2) i j)
    (Hi : i < length m1) (Hj : j < length m1), hbe (iapp m1 m2') i j.
  Proof. unfold hbe; clarify; left; eapply hb_app; eauto. Qed.
  
  Lemma hbe_app' : forall m1 m2 i j m1' (Hhbe : hbe (iapp m1 m2) i j)
    (Hi : ~i < length m1) (Hj : ~j < length m1),
    hbe (iapp m1' m2) (i - length m1 + length m1')
                      (j - length m1 + length m1').
  Proof.
    unfold hbe; clarify.
    left; apply hb_app'; auto.
  Qed.

  Lemma hb_next : forall m i j, happens_before m i j ->
    exists a, inth m i = Some a /\ exists k b, i < k /\ inth m k = Some b /\
      (thread_of a = thread_of b \/ synchronizes_with a b) /\ hbe m k j.
  Proof.
    unfold hbe; intros; induction H; clarify.
    - repeat eexists; eauto.
    - repeat eexists; eauto.
    - eexists; split; eauto.
      exists x3; repeat eexists; eauto.
      destruct IHhappens_before12222, IHhappens_before22222; clarify;
        left; eapply hb_trans; eauto.
  Qed.

  Lemma hb_prev : forall m i j, happens_before m i j ->
    exists b, inth m j = Some b /\ exists k a, k < j /\ inth m k = Some a /\
      (thread_of a = thread_of b \/ synchronizes_with a b) /\ hbe m i k.
  Proof.
    unfold hbe; intros; induction H; clarify.
    - repeat eexists; eauto.
    - repeat eexists; eauto.
    - eexists; split; eauto.
      exists x1; repeat eexists; eauto.
      destruct IHhappens_before22222; clarify.
      left; eapply hb_trans; eauto.
  Qed.

  Lemma hbe_trans : forall m i j k (Hhbe1 : hbe m i j) (Hhbe2 : hbe m j k),
    hbe m i k.
  Proof.
    unfold hbe; clarify.
    left; eapply hb_trans; eauto.
  Qed.

  Lemma hb_inv : forall m i j, happens_before m i j ->
    exists a b, inth m i = Some a /\ inth m j = Some b /\
      ((thread_of a = thread_of b) \/ synchronizes_with a b \/
      exists k c, inth m k = Some c /\ (*~not_sync c /\*)
                  happens_before m i k /\ happens_before m k j).
  Proof.
    intros; induction H; clarsimp; repeat eexists; eauto.
    destruct IHhappens_before122 as [? | [? | ?]]; clarify.
    - destruct IHhappens_before222 as [? | [? | ?]]; clarify.
      + clarsimp.
      + right; right; exists k; repeat eexists; eauto.
(*        intro Hsync; generalize (no_sync _ Hsync x0); clarify.*)
      + right; right; exists x2; repeat eexists; eauto.
        eapply hb_trans; eauto.
    - destruct IHhappens_before222 as [? | [? | ?]]; clarify.
      + right; right; exists k; repeat eexists; eauto.
(*        intro Hsync; generalize (no_sync _ Hsync x1); clarify.*)
      + right; right; exists k; repeat eexists; eauto.
(*        intro Hsync; generalize (no_sync _ Hsync x1); clarify.*)
      + right; right; exists x2; repeat eexists; eauto.
        eapply hb_trans; eauto.
    - right; right; exists x2; repeat eexists; eauto.
      eapply hb_trans; eauto.
  Qed.

  Lemma seq_hb : forall ops t (Ht : Forall (fun c => thread_of c = t) ops)
    m1 m2 i j (Hlt : length m1 <= i < j) (Hlen : j < length m1 + length ops),
    happens_before (iapp m1 (iapp ops m2)) i j.
  Proof.
    intros.
    assert (j - length m1 < length ops) by abstract omega.
    exploit nth_error_succeeds; eauto; intros [b Hj]; clarify.
    assert (i - length m1 < length ops) by abstract omega.
    exploit nth_error_succeeds; eauto; intros [a Hi].
    generalize (nth_error_in _ _ Hi), (nth_error_in _ _ Hj); intros Ha Hb.
    rewrite Forall_forall in Ht; generalize (Ht _ Ha); specialize (Ht _ Hb);
      clarify.
    eapply hb_prog; eauto; rewrite iapp_inter; clarify; abstract omega.
  Qed.

  Corollary seq_hb_iff : forall ops t
    (Ht : Forall (fun c => thread_of c = t) ops) m1 m2 i j
    (Hlt : length m1 <= i < j) (Hlen : j < length m1 + length ops),
    happens_before (iapp m1 (iapp ops m2)) i j <-> i < j.
  Proof. intros; split; intro; [eapply hb_lt | eapply seq_hb]; eauto. Qed.    

  Corollary seq_hbe : forall ops t (Ht : Forall (fun c => thread_of c = t) ops)
    m1 m2 i j (Hlt : length m1 <= i <= j) (Hlen : j < length m1 + length ops),
    hbe (iapp m1 (iapp ops m2)) i j.
  Proof.
    intros; unfold hbe; destruct (eq_dec i j); auto.
    left; eapply seq_hb; eauto; omega.
  Qed.

  Definition adjust_range {A} (l1 l l' : list A) i :=
    if lt_dec i (length l1) then i else i - length l + length l'.

  Lemma adjust_range_nth : forall {A} i (m1 ops : list A) m2 ops'
    (Hrange : i < length m1 \/ i >= length m1 + length ops),
    inth (iapp m1 (iapp ops' m2)) (adjust_range m1 ops ops' i) =
    inth (iapp m1 (iapp ops m2)) i.
  Proof.
    intros; repeat rewrite iapp_nth.
    unfold adjust_range; destruct (lt_dec i (length m1)); clarify.
    destruct (lt_dec (i - length m1) (length ops)); [abstract omega|].
    destruct (lt_dec (i - length ops + length ops') (length m1));
      [abstract omega|].
    destruct (lt_dec (i - length ops + length ops' - length m1) (length ops'));
      [abstract omega|].
    assert (i - length ops + length ops' - length m1 - length ops' =
      i - length m1 - length ops) as Heq; [|rewrite Heq; auto].
    rewrite NPeano.Nat.add_sub_swap;
      [rewrite NPeano.Nat.add_sub | abstract omega].
    repeat rewrite <- NPeano.Nat.sub_add_distr; rewrite plus_comm; auto.
  Qed.

  Lemma adjust_adjust : forall {A} (l1 l l' : list A) i
    (Hrange : i < length l1 \/ i >= length l1 + length l),
    adjust_range l1 l' l (adjust_range l1 l l' i) = i.
  Proof.
    unfold adjust_range; intros.
    destruct (lt_dec i (length l1)); clarify.
    destruct (lt_dec (i - length l + length l')); abstract omega.
  Qed.

  Lemma adjust_lt : forall {A} (l1 l l' : list A) i j
    (Hi : i < length l1 \/ i >= length l1 + length l)
    (Hj : j < length l1 \/ j >= length l1 + length l),
    adjust_range l1 l l' i < adjust_range l1 l l' j <-> i < j.
  Proof.
    unfold adjust_range; intros.
    destruct (lt_dec i (length l1)), (lt_dec j (length l1)); try abstract omega.
  Qed.

  Lemma hb_delay : forall m1 ops m2 i j
    (Hhb : happens_before (iapp m1 m2) i j),
    happens_before (iapp m1 (iapp ops m2))
      (adjust_range m1 [] ops i) (adjust_range m1 [] ops j).
  Proof.
    intros; induction Hhb.
    - eapply hb_prog; eauto.
      + apply adjust_lt; clarify; abstract omega.
      + rewrite adjust_range_nth; clarify; abstract omega.
      + rewrite adjust_range_nth; clarify; abstract omega.
    - eapply hb_sync; eauto.
      + apply adjust_lt; clarify; abstract omega.
      + rewrite adjust_range_nth; clarify; abstract omega.
      + rewrite adjust_range_nth; clarify; abstract omega.
    - eapply hb_trans; eauto.
  Qed.

  Lemma hbe_le : forall m i j (Hhbe : hbe m i j), i <= j.
  Proof.
    unfold hbe; intros; destruct Hhbe; clarify.
    generalize (hb_lt H); abstract omega.
  Qed.

  Lemma hb_hbe_trans : forall m i j k, happens_before m i k -> hbe m k j ->
    happens_before m i j.
  Proof.
    intros ? ? ? ? ? Hhbe; unfold hbe in Hhbe; destruct Hhbe; clarify;
      eapply hb_trans; eauto.
  Qed.

  Lemma hbe_hb_trans : forall m i j k, hbe m i k -> happens_before m k j ->
    happens_before m i j.
  Proof.
    intros ? ? ? ? Hhbe; unfold hbe in Hhbe; destruct Hhbe; clarify;
      eapply hb_trans; eauto.
  Qed.

  Lemma hb_boundary : forall m1 m2 i j
    (Hhb : happens_before (iapp m1 m2) i j)
    (Hi : i < length m1) (Hj : length m1 <= j),
    exists k k', k < length m1 /\ length m1 <= k' /\
      hbe (iapp m1 m2) i k /\ hbe (iapp m1 m2) k' j /\
      exists a a', nth_error m1 k = Some a /\ inth m2 (k' - length m1) = Some a'
                   /\ (thread_of a = thread_of a' \/ synchronizes_with a a').
  Proof.
    intros; induction Hhb.
    - exists i, j; unfold hbe; clarify.
      rewrite iapp_nth in *; clarify.
      destruct (lt_dec j (length m1)); [abstract omega|].
      repeat eexists; eauto.
    - exists i, j; unfold hbe; clarify.
      rewrite iapp_nth in *; clarify.
      destruct (lt_dec j (length m1)); [abstract omega|].
      repeat eexists; eauto.
    - destruct (lt_dec k (length m1)); clarify.
      + exists x, x0; clarify.
        repeat split; eauto.
        eapply hbe_trans; eauto; unfold hbe; clarify.
      + use IHHhb1; [clarify | abstract omega].
        exists x, x0; clarify.
        repeat split; eauto.
        eapply hbe_trans; eauto; unfold hbe; clarify.
  Qed.

  Lemma hb_app'' : forall m1 ops m2 i j ops'
    (Hhb : happens_before (iapp m1 (iapp ops m2)) i j)
    (Hi : ~ i < length m1 + length ops) (Hj : ~ j < length m1 + length ops),
    happens_before (iapp m1 (iapp ops' m2)) (i - length ops + length ops')
         (j - length ops + length ops').
  Proof.
    intros; rewrite iapp_app in *; exploit hb_app'; eauto.
    - rewrite app_length; auto.
    - rewrite app_length; auto.
    - instantiate (1 := (m1 ++ ops')); repeat rewrite app_length.
      assert (i - (length m1 + length ops) + (length m1 + length ops') =
        i - length ops + length ops') as Heq1 by abstract omega;
        assert (j - (length m1 + length ops) + (length m1 + length ops') =
          j - length ops + length ops') as Heq2 by abstract omega;
        rewrite Heq1, Heq2; auto.
  Qed.

  Corollary hbe_app'' : forall m1 ops m2 i j ops'
    (Hhb : hbe (iapp m1 (iapp ops m2)) i j)
    (Hi : ~ i < length m1 + length ops) (Hj : ~ j < length m1 + length ops),
    hbe (iapp m1 (iapp ops' m2)) (i - length ops + length ops')
         (j - length ops + length ops').
  Proof. unfold hbe; clarify; left; eapply hb_app''; eauto. Qed.

  Lemma filter_snoc_inv : forall A (f : A -> bool) l l' x
    (Hfilter : filter f l = l' ++ [x]),
    exists l1 l2, l = l1 ++ x :: l2 /\ filter f l1 = l' /\
      Forall (fun a => f a = false) l2.
  Proof.
    intros.
    assert (nth_error (filter f l) (length l') = Some x)
      by (rewrite Hfilter, nth_error_app; clarsimp).
    exploit nth_error_in; eauto; intro.
    rewrite filter_In in *; clarify.
    exploit nth_filter_split; eauto; intros [k1 [k2 Hk]]; clarify.
    symmetry in Hk21.
    rewrite filter_app in *; generalize (app_eq_inv _ _ _ _ Hk21 Hfilter);
      clarify.
    rewrite filter_none_iff in *; eauto.
  Qed.

  End Happens_Before.

  Definition not_read := @not_read block val.

(*  Require Import Sorting.Permutation.

  Inductive linearization (m m' : list _) : Prop :=
    linI p (Hp : Permutation (interval 0 (length m)) p)
    (Hlen : length m' = length m)
    (Hperm : forall i i', nth_error p i = Some i' ->
       nth_error m' i' = nth_error m i)
    (Hhb : forall i j i' j', nth_error p i = Some i' ->
       nth_error p j = Some j' ->
       (happens_before m i j <-> happens_before m' i' j')).

  Instance lin_refl : Reflexive linearization.
  Proof.
    intro; econstructor.
    - reflexivity.
    - auto.
    - intros; rewrite nth_error_interval in *; clarify.
    - intros; rewrite nth_error_interval in *; clarify; reflexivity.
  Qed.

  Fixpoint inv_perm_aux p i :=
    match i with
    | O => Some []
    | S i' => match (find_index (fun x => beq x i') p, inv_perm_aux p i') with
              | (Some j, Some rest) => Some (rest ++ [j])
              | _ => None
              end
    end.

  Definition inv_perm p := inv_perm_aux p (length p).

  Require Import Permutation.

  Opaque minus.

  Lemma exists_inv_aux : forall p j (Hin : forall i, i < j -> In i p),
    exists p', inv_perm_aux p j = Some p'.
  Proof.
    induction j; clarify; eauto.
    destruct (find_index (fun x => beq x j) p) eqn: Hfind; eauto.
    rewrite find_index_fail in Hfind.
    specialize (Hin j); clarify.
    rewrite Forall_forall in Hfind; specialize (Hfind _ Hin); unfold beq in *;
      clarify.
  Qed.
      
  Corollary exists_inv : forall p (Hin : forall i, i < length p -> In i p),
    exists p', inv_perm p = Some p'.
  Proof. intros; apply exists_inv_aux; auto. Qed.

  Lemma inv_aux_length : forall p j p' (Hinv : inv_perm_aux p j = Some p'),
    length p' = j.
  Proof.
    induction j; clarify.
    exploit IHj; eauto; clarsimp; omega.
  Qed.    

  Corollary inv_length : forall p p' (Hinv : inv_perm p = Some p'),
    length p' = length p.
  Proof. intros; eapply inv_aux_length; eauto. Qed.

  Lemma inv_aux_nth : forall p j p' i' i (Hinv : inv_perm_aux p j = Some p')
    (Hnth : nth_error p' i' = Some i), nth_error p i = Some i'.
  Proof.
    induction j; clarsimp.
    rewrite nth_error_app in Hnth; destruct (lt_dec i' (length x0)).
    - eapply IHj; eauto; omega.
    - destruct (i' - length x0) eqn: Hminus; clarsimp.
      destruct (eq_dec i' (length x0)); [clarify | omega].
      rewrite find_index_spec in *; unfold beq in *; clarify.
      erewrite inv_aux_length; eauto.
  Qed.

  Corollary inv_nth : forall p p' i' i (Hinv : inv_perm p = Some p')
    (Hnth : nth_error p' i' = Some i), nth_error p i = Some i'.
  Proof. intros; eapply inv_aux_nth; eauto. Qed.

  Corollary inv_aux_NoDup : forall p j p' (Hinv : inv_perm_aux p j = Some p'),
    NoDup p'.
  Proof.
    intros; rewrite NoDup_inj_iff; intros.
    generalize (inv_aux_nth _ _ _ Hinv Hi), (inv_aux_nth _ _ _ Hinv Hj);
      clarsimp.
  Qed.

  Corollary inv_NoDup : forall p p' (Hinv : inv_perm p = Some p'), NoDup p'.
  Proof. intros; eapply inv_aux_NoDup; eauto. Qed.

  Lemma inv_nil : inv_perm [] = Some [].
  Proof. unfold inv_perm; auto. Qed.
  Hint Resolve inv_nil.

  Lemma inv_perm_aux_in : forall p j p' (Hinv : inv_perm_aux p j = Some p')
    i (Hlt : i < j),
    exists i', find_index (fun x => beq x i) p = Some i' /\ In i' p'.
  Proof.
    induction j; clarify; [omega|].
    destruct (eq_dec i j); clarify.
    - setoid_rewrite in_app; simpl; eauto.
    - specialize (IHj _ Hinv21 i); use IHj; [|omega].
      setoid_rewrite in_app; clarify; eauto.
  Qed.
             
  Lemma inv_perm_spec : forall j p (Hperm : Permutation (interval 0 j) p),
    exists p', inv_perm p = Some p' /\ Permutation (interval 0 j) p'.
  Proof.
    intros.
    assert (length p = j) as Hlen; clarify.
    { erewrite <- Permutation_length, interval_length in *; eauto; omega. }
    exploit (exists_inv p).
    { intros; eapply Permutation_in; eauto.
      apply interval_in; omega. }
    intros [p' Hp']; exists p'; clarify.
    apply NoDup_Permutation.
    - apply interval_distinct.
    - eapply inv_NoDup; eauto.
    - intro; rewrite interval_in_iff.
      split; clarify.
      + exploit nth_error_succeeds; eauto; clarify.
        exploit nth_error_in; eauto; intro.
        exploit Permutation_NoDup; [apply interval_distinct | eauto |
          intro Hdistinct].
        symmetry in Hperm; exploit Permutation_in; eauto.
        rewrite interval_in_iff; clarify.
        exploit inv_perm_aux_in; eauto; intros [? [Hfind ?]].
        rewrite find_index_spec in *; unfold beq in *; clarify.
        generalize (NoDup_inj _ _ Hdistinct H Hfind1); clarify.
      + exploit in_nth_error; eauto; clarify.
        exploit inv_nth; eauto.
        apply nth_error_lt.
  Qed.

  Instance lin_sym : Symmetric linearization.
  Proof.
    repeat intro; inversion H.
    exploit inv_perm_spec; eauto; intros [p' [Hinv ?]].
    exists p'; clarify.
    - rewrite Hlen; auto.
    - exploit inv_nth; eauto; intro.
      erewrite Hperm; eauto.
    - generalize (inv_nth _ _ Hinv H1), (inv_nth _ _ Hinv H2); intros.
      rewrite Hhb; [reflexivity | auto | auto].
  Qed.

  Definition perm_index p i :=
    match nth_error p i with Some i' => i' | None => i end.

  Lemma perm_index_ge : forall p i (Hge : length p <= i), perm_index p i = i.
  Proof.
    unfold perm_index; intros.
    destruct (nth_error p i) eqn: Hi'; clarify.
    exploit nth_error_lt; eauto; omega.
  Qed.

  Inductive lin_p p m m' :=
    lin_pI (Hp : Permutation (interval 0 (length m)) p)
    (Hlen : length m' = length m)
    (Hperm : forall i i', nth_error p i = Some i' ->
       nth_error m' i' = nth_error m i)
    (Hhb : forall i j i' j', nth_error p i = Some i' ->
       nth_error p j = Some j' ->
       (happens_before m i j <-> happens_before m' i' j')).

  Lemma lin_lin_p : forall m m', linearization m m' <-> exists p, lin_p p m m'.
  Proof.
    split; intro Hlin; clarify; inversion Hlin.
    - exists p; constructor; auto.
    - econstructor; eauto.
  Qed.

  Lemma perm_index_nth : forall p m1 m1' m2 i (Hlin : lin_p p m1 m1'),
    inth (iapp m1' m2) (perm_index p i) = inth (iapp m1 m2) i.
  Proof.
    intros; inversion Hlin.
    assert (length p = length m1) as Hlen'.
    { erewrite <- Permutation_length, interval_length; eauto; clarsimp. }
    unfold perm_index; destruct (nth_error p i) eqn: Hi'.
    - exploit nth_error_lt; eauto.
      rewrite Hlen'; repeat rewrite iapp_nth; clarsimp.
      exploit nth_error_succeeds; eauto; clarify.
      specialize (Hperm _ _ Hi'); rewrite <- Hperm in *.
      contradiction n0; eapply nth_error_lt; eauto.
    - repeat rewrite iapp_nth; rewrite Hlen; clarify.
      clear cond; rewrite <- Hlen' in l; exploit nth_error_succeeds; eauto;
        clarify.
  Qed.

  Lemma hb_lin_lt : forall p m1 m1' m2 i j (Hlin : lin_p p m1 m1')
    (Hhb : happens_before (iapp m1 m2) i j), perm_index p i < perm_index p j.
  Proof.
    intros; inversion Hlin.
    assert (length p = length m1) as Hlen'.
    { erewrite <- Permutation_length, interval_length; eauto; clarsimp. }
    generalize (hb_lt Hhb); intro.
    destruct (lt_dec i (length m1)), (lt_dec j (length m1)); try omega.
    - exploit hb_app_impl; eauto; intro Hhb'.
      rewrite <- Hlen' in *; generalize (nth_error_succeeds _ l),
        (nth_error_succeeds _ l0); unfold perm_index; clarify.
      rewrite Hhb0 in Hhb'; eauto; eapply hb_lt; eauto.
    - setoid_rewrite perm_index_ge at 2; [|omega].
      exploit nth_error_succeeds; eauto; clarify.
      rewrite <- Hlen' in *; exploit nth_error_succeeds; eauto;
        unfold perm_index; clarify.
      erewrite <- Hperm in *; eauto.
      exploit nth_error_lt; eauto.
      rewrite Hlen; omega.
    - repeat rewrite perm_index_ge; auto; omega.
  Qed.

  Lemma hb_lin_prefix : forall p m1 m1' m2 i j (Hlin : lin_p p m1 m1')
    (Hhb : happens_before (iapp m1 m2) i j),
    happens_before (iapp m1' m2) (perm_index p i) (perm_index p j).
  Proof.
    intros; exploit hb_lin_lt; eauto; intro.
    induction Hhb.
    - eapply hb_prog; eauto; erewrite perm_index_nth; eauto.
    - eapply hb_sync; eauto; erewrite perm_index_nth; eauto.
    - eapply hb_trans; [apply IHHhb1 | apply IHHhb2]; eapply hb_lin_lt; eauto.
  Qed.*)

  Lemma lower_app : forall m1 m2, lower (m1 ++ m2) = lower m1 ++ lower m2.
  Proof.
    intros; unfold lower; rewrite map_app, flatten_app; auto.
  Qed.
  
  Lemma nth_lower_split : forall m i x (Hnth : nth_error (lower m) i = Some x),
    exists m1 c m2 i', m = m1 ++ c :: m2 /\ nth_error (to_seq c) i' = Some x /\
      i = length (lower m1) + i'.
  Proof.
    intros.
    exploit nth_flatten_split; eauto; clarify.
    exploit list_append_map_inv; eauto; intros [m1 [m2 ?]]; clarify.
    destruct m2; clarify.
    repeat eexists; eauto.
  Qed.

  Definition SC m := seq_con (lower m).

  Definition reads m r p v := exists a, inth m r = Some a /\
    In (MRead p v) (to_seq a).
  Definition writes m w p v := exists a, inth m w = Some a /\
    In (MWrite p v) (to_seq a).
  Definition mods m i p := exists a op, inth m i = Some a /\ In op (to_seq a) /\
    op_modifies _ op p = true.

  Definition b_not_read b op := not_read op && beq (block_of op) b.

  Lemma b_not_read_spec : forall b m, filter (b_not_read b) m =
    filter not_read (proj_block m b).
  Proof.
    intros; setoid_rewrite filter_filter; apply filter_ext.
    rewrite Forall_forall; auto.
  Qed.

  Definition race_free m := forall i j (Hdiff : i <> j) a b
    (Ha : inth m i = Some a) (Hb : inth m j = Some b)
    (Hint : exists bl op1 op2 o, In op1 (to_seq a) /\ In op2 (to_seq b) /\
      op_modifies _ op1 (bl, o) = true /\ block_of op2 = bl),
    happens_before m i j \/ happens_before m j i.

  Lemma inth_plus : forall A (l1 : list A) l2 i,
    inth (iapp l1 l2) (length l1 + i) = inth l2 i.
  Proof.
    intros; rewrite iapp_nth, lt_dec_plus_r, minus_plus; auto.
  Qed.

  Corollary inth_length : forall A (l1 : list A) x l2,
    inth (iapp l1 (icons x l2)) (length l1) = Some x.
  Proof. intros; rewrite (plus_n_O (length l1)), inth_plus; auto. Qed.

  Lemma hb_replace1 : forall c c' (Ht : thread_of c = thread_of c')
    (Hsync : forall a, (synchronizes_with a c <-> synchronizes_with a c') /\
       (synchronizes_with c a <-> synchronizes_with c' a)) m1 m2 i j,
    happens_before (iapp m1 (icons c m2)) i j ->
    happens_before (iapp m1 (icons c' m2)) i j.
  Proof.
    intros; induction H.
    - rewrite (iapp_split_nth _ _ _ _ c') in Ha;
        rewrite (iapp_split_nth _ _ _ _ c') in Hb.
      destruct (eq_dec i (length m1)), (eq_dec j (length m1)); clarify.
      + omega.
      + rewrite Ht in Hthread; eapply hb_prog; eauto; apply inth_length.
      + rewrite Ht in Hthread; eapply hb_prog; eauto; apply inth_length.
      + eapply hb_prog; eauto.
    - rewrite (iapp_split_nth _ _ _ _ c') in Ha;
        rewrite (iapp_split_nth _ _ _ _ c') in Hb.
      destruct (eq_dec i (length m1)), (eq_dec j (length m1)); clarify.
      + omega.
      + specialize (Hsync b); destruct Hsync as [_ Hsync].
        rewrite Hsync in Hsync0; eapply hb_sync; eauto; apply inth_length.
      + specialize (Hsync a); destruct Hsync as [Hsync _].
        rewrite Hsync in Hsync0; eapply hb_sync; eauto; apply inth_length.
      + eapply hb_sync; eauto.
    - eapply hb_trans; eauto.
  Qed.

  Corollary hb_replace : forall c c' (Ht : thread_of c = thread_of c')
    (Hsync : forall a, (synchronizes_with a c <-> synchronizes_with a c') /\
       (synchronizes_with c a <-> synchronizes_with c' a)) m1 m2 i j,
    happens_before (iapp m1 (icons c m2)) i j <->
    happens_before (iapp m1 (icons c' m2)) i j.
  Proof.
    split; apply hb_replace1; auto.
    split; symmetry; apply Hsync.
  Qed.

  Lemma drop_race_free_single : forall m1 c m2 (b : block)
    (Hrf : race_free (iapp m1 (icons c m2)))
    drop_b_reads c' (Hdrop : drop_b_reads b [c] = [c'])
    (Hc' : forall op, In op (to_seq c') -> In op (to_seq c))
    (Hc : forall op p, op_modifies _ op p = true -> In op (to_seq c) ->
            In op (to_seq c'))
    (Hiff : forall i j,
      happens_before (iapp m1 (iapp (drop_b_reads b [c]) m2)) i j <->
      happens_before (iapp m1 (icons c m2)) i j),
    race_free (iapp m1 (iapp (drop_b_reads b [c]) m2)).
  Proof.
    repeat intro; clarsimp.
    repeat rewrite Hiff; eapply Hrf; auto.
    - instantiate (1 := if eq_dec i (length m1) then c else a).
      erewrite iapp_split_nth; clarify; eauto.
    - instantiate (1 := if eq_dec j (length m1) then c else b0).
      erewrite iapp_split_nth; clarify; eauto.
    - repeat eexists; eauto; clarify.
      + rewrite iapp_nth, lt_dec_eq, minus_diag in Ha; clarify.
      + rewrite iapp_nth, lt_dec_eq, minus_diag in Hb; clarify.
  Qed.
      
  Class Memory_Model := { well_formed : ilist conc_op -> Prop;
    consistent : ilist conc_op -> Prop;
    consistent_nil : consistent inil;
    read_free : forall (m : list _) (Hno_reads : (forall r p v, ~reads m r p v))
      (Hwrite : write_alloc (lower m)), consistent m <-> seq_con (lower m);
    read_write : forall m r p v (Hread_init : read_init (lower m))
      (Hcon : consistent m) (Hread : reads m r p v), 
      exists w, r <> w /\ writes m w p v /\
      (forall w2 v2, writes m w2 p v2 ->
         ~(happens_before m w w2 /\ happens_before m w2 r)) /\
       ~happens_before m r w;
    drop_wf : forall m1 ops m2 b, well_formed (iapp m1 (iapp ops m2)) ->
      well_formed (iapp m1 (iapp (drop_b_reads b ops) m2));
    drop_race_free : forall m1 c m2 b (Hwf : well_formed (iapp m1 (icons c m2)))
      (Hrf : race_free (iapp m1 (icons c m2))),
      race_free (iapp m1 (iapp (drop_b_reads b [c]) m2));
    private_seq : forall ops t (Ht : Forall (fun c => thread_of c = t) ops)
    (Hlen : length ops > 0) (m1 : list _) m2 b
    (Hbefore : forall i o, mods m1 i (b, o) ->
       happens_before (iapp m1 (iapp ops m2)) i (length m1))
    (Huniform : forall i o v, reads ops i (b, o) v ->
       exists j, j < length m1 + i /\ writes (m1 ++ ops) j (b, o) v /\
       forall k v', k < length m1 + i -> writes (m1 ++ ops) k (b, o) v' ->
       hbe (iapp m1 (iapp ops m2)) k j)
    (Hafter : forall i o, mods m2 i (b, o) ->
       happens_before (iapp m1 (iapp ops m2))
         (length m1 + length ops - 1) (i + length m1 + length ops))
    (Hread_init : read_init (filter (b_not_read b) (lower m1) ++
       proj_block (lower ops) b))
    (Hwrite_alloc : write_alloc (lower (m1 ++ ops)))
    (Hwf : well_formed (iapp m1 (iapp ops m2))),
    consistent (iapp m1 (iapp ops m2)) <->
    consistent (iapp m1 (iapp (drop_b_reads b ops) m2)) /\
      seq_con (filter (b_not_read b) (lower m1) ++ proj_block (lower ops) b) }.

  Lemma lower_cons : forall x l, lower (x :: l) = to_seq x ++ lower l.
  Proof. auto. Qed.

  Corollary lower_single : forall x, lower [x] = to_seq x.
  Proof. intro; rewrite lower_cons; clarsimp. Qed.

  Lemma nth_error_plus : forall A (l1 l2 : list A) i,
    nth_error (l1 ++ l2) (length l1 + i) = nth_error l2 i.
  Proof.
    intros; rewrite nth_error_app, lt_dec_plus_r, minus_plus; auto.
  Qed.

  Lemma read_init_drop_b : forall ops b m1 m2
    (Hread : read_init (iapp m1 (iapp (lower ops) m2))),
    read_init (iapp m1 (iapp (lower (drop_b_reads b ops)) m2)).
  Proof.
    intros ? ?.
    generalize (drop_b_reads_spec b ops); intro Hdrop; rewrite Hdrop.
    clear Hdrop; induction (lower ops); clarify.
    specialize (IHl (m1 ++ [a]) m2);
      repeat rewrite <- iapp_app in IHl; clarify.
    destruct a; clarsimp.
    eapply read_init_drop; eauto.
  Qed.

  Corollary read_init_drop_b' : forall m1 ops m2 b
    (Hread : read_init (m1 ++ lower ops ++ m2)),
    read_init (m1 ++ lower (drop_b_reads b ops) ++ m2).
  Proof.
    intros; repeat rewrite to_ilist_app in *; apply read_init_drop_b; auto.
  Qed.

  Lemma write_alloc_drop_b : forall ops b m1 m2
    (Hread : write_alloc (iapp m1 (iapp (lower ops) m2))),
    write_alloc (iapp m1 (iapp (lower (drop_b_reads b ops)) m2)).
  Proof.
    intros ? ?.
    generalize (drop_b_reads_spec b ops); intro Hdrop; rewrite Hdrop.
    clear Hdrop; induction (lower ops); clarify.
    specialize (IHl (m1 ++ [a]) m2);
      repeat rewrite <- iapp_app in IHl; clarify.
    destruct a; clarsimp.
    eapply write_alloc_drop; eauto.
  Qed.

  Corollary write_alloc_drop_b' : forall m1 ops m2 b
    (Hwrite : write_alloc (m1 ++ lower ops ++ m2)),
    write_alloc (m1 ++ lower (drop_b_reads b ops) ++ m2).
  Proof.
    intros; repeat rewrite to_ilist_app in *; apply write_alloc_drop_b; auto.
  Qed.

  Lemma drop_reads : forall m1 c m2 p v (Hread : In (MRead p v) (to_seq c)),
    length (filter (fun op => negb (not_read op))
      (lower (m1 ++ drop_b_reads (fst p) [c] ++ m2))) <
    length (filter (fun op => negb (not_read op)) (lower (m1 ++ c :: m2))).
  Proof.
    intros; repeat rewrite lower_app; rewrite lower_cons.
    repeat rewrite filter_app, app_length.
    apply plus_lt_compat_l, plus_lt_compat_r.
    rewrite drop_b_reads_spec, lower_single, filter_comm.
    exploit in_split; eauto.
    clear; clarsimp; repeat rewrite filter_app; clarify.
    destruct p; unfold negb at 3; clarify.
    repeat rewrite app_length; apply plus_le_lt_compat; [apply filter_length|].
    simpl; eapply le_lt_trans; [apply filter_length | auto].
  Qed.

  Lemma last_drop : forall r m1 ops m2 b p a (Hrange : r < length (lower m1) \/
    r >= length (lower m1) + length (lower ops)),
    last_op (firstn (adjust_range (lower m1) (lower ops)
      (lower (drop_b_reads b ops)) r)
      (lower m1 ++ lower (drop_b_reads b ops) ++ lower m2)) (Ptr p) a <->
    last_op (firstn r (lower m1 ++ lower ops ++ lower m2)) (Ptr p) a.
  Proof.
    intros.
    unfold adjust_range; repeat rewrite firstn_app;
      destruct (lt_dec r (length (lower m1))).
    - rewrite not_le_minus_0; [clarify | omega].
      repeat rewrite NPeano.Nat.sub_0_l; clarify; reflexivity.
    - rewrite firstn_length'; [|omega].
      rewrite firstn_length'; [|omega].
      setoid_rewrite firstn_length' at 2; [|omega].
      setoid_rewrite firstn_length' at 2; [|omega].
      rewrite minus_comm, NPeano.Nat.add_sub; [|omega].
      rewrite minus_comm; [|omega].
      rewrite drop_b_reads_spec.
      setoid_rewrite <- last_op_filter; repeat rewrite filter_app.
      rewrite filter_filter.
      setoid_rewrite (filter_ext _ not_read) at 2; [reflexivity|].
      rewrite Forall_forall; unfold andb, orb; clarify.
  Qed.

  Corollary last_drop' : forall r m1 c m2 b p a (Hrange : r < length (lower m1) 
    \/ r >= length (lower m1) + length (to_seq c)),
    last_op (firstn (adjust_range (lower m1) (to_seq c)
      (lower (drop_b_reads b [c])) r)
      (lower m1 ++ lower (drop_b_reads b [c]) ++ lower m2)) (Ptr p) a <->
    last_op (firstn r (lower m1 ++ to_seq c ++ lower m2)) (Ptr p) a.
  Proof. intros; rewrite <- lower_single in *; apply last_drop; auto. Qed.

  Variable (val_eq : EqDec_eq val).

  Lemma in_range_dec : forall i a b, (i < a \/ i >= b) \/ (a <= i < b).
  Proof. intros; omega. Qed.

  Lemma adjust_range_nth' : forall A (l1 l2 l3 l2' : list A) i
    (Hout : i < length l1 \/ i >= length l1 + length l2),
    nth_error (l1 ++ l2' ++ l3) (adjust_range l1 l2 l2' i) =
    nth_error (l1 ++ l2 ++ l3) i.
  Proof.
    intros; unfold adjust_range; repeat rewrite nth_error_app;
      destruct (lt_dec i (length l1)); clarify.
    destruct (lt_dec (i - length l1) (length l2)); [omega|].
    destruct (lt_dec (i - length l2 + length l2') (length l1)); [omega|].
    destruct (lt_dec (i - length l2 + length l2' - length l1) (length l2'));
      [omega|].
    assert (i - length l2 + length l2' - length l1 - length l2' =
      i - length l1 - length l2) as Heq.
    { rewrite minus_comm, NPeano.Nat.add_sub, minus_comm; auto.
      - rewrite plus_comm; auto.
      - omega. }
    rewrite Heq; auto.
  Qed.

  Lemma drop_SC : forall m1 ops m2 (Hseq : SC (m1 ++ ops ++ m2))
    (Hread : read_init (lower (m1 ++ ops ++ m2)))
    (Hwrite : write_alloc (lower (m1 ++ ops ++ m2))) b,
    SC (m1 ++ drop_b_reads b ops ++ m2).
  Proof.
    unfold SC; intros.
    setoid_rewrite consistent_split_reads in Hseq; auto.
    repeat rewrite lower_app in *.
    setoid_rewrite consistent_split_reads;
      [|apply read_init_drop_b' | apply write_alloc_drop_b']; clarify.
    split.
    - rewrite drop_b_reads_spec; repeat rewrite filter_app in *.
      rewrite filter_filter; setoid_rewrite (filter_ext _ not_read) at 2; auto.
      rewrite Forall_forall; unfold andb; clarify.
    - intros.
      destruct (in_range_dec r (length (lower m1))
        (length (lower m1) + length (lower (drop_b_reads b ops))))
        as [Hrange | [Hrange1 Hrange2]].
      + specialize (Hseq2 (adjust_range (lower m1) (lower (drop_b_reads b ops))
          (lower ops) r)); rewrite adjust_range_nth' in Hseq2; auto.
        specialize (Hseq2 _ _ H).
        rewrite <- (adjust_adjust (lower m1) (lower (drop_b_reads b ops))
          (lower ops) Hrange), last_drop; auto.
        { unfold adjust_range; destruct (lt_dec r (length (lower m1))); clarify;
            omega. }
      + rewrite nth_error_app in *; destruct (lt_dec r (length (lower m1)));
          [omega|].
        rewrite nth_error_app in *; destruct (lt_dec (r - length (lower m1))
          (length (lower (drop_b_reads b ops)))); [|omega].
        rewrite drop_b_reads_spec in H.
        exploit nth_filter_split; eauto; intros (l1 & l2 & Hl & Hr & ?);
          clarify.
        specialize (Hseq2 (length (lower m1) + length l1));
          rewrite nth_error_plus, Hl in Hseq2.
        rewrite <- app_assoc in Hseq2; simpl in Hseq2.
        specialize (Hseq2 _ _ (nth_error_split _ _ _)).
        rewrite firstn_app, firstn_length', minus_plus in Hseq2; [|omega].
        rewrite firstn_app, firstn_length, minus_diag in Hseq2; clarify.
        rewrite drop_b_reads_spec, Hl, filter_app.
        rewrite firstn_app, firstn_length', Hr; [|omega].
        rewrite <- app_assoc, firstn_app, firstn_length, minus_diag; clarify.
        rewrite app_nil_r in *.
        rewrite <- last_op_filter in Hseq2; rewrite <- last_op_filter.
        repeat rewrite filter_app in *.
        rewrite filter_filter; setoid_rewrite (filter_ext _ not_read) at 2;
          auto.
        rewrite Forall_forall; unfold andb; clarify.
  Qed.

  Lemma merge_SC : forall m1 ops m2 b
    (Hread : read_init (lower (m1 ++ ops ++ m2)))
    (Hwrite : write_alloc (lower (m1 ++ ops ++ m2)))
    (Hseq : SC (m1 ++ (drop_b_reads b ops) ++ m2))
    (Hseq' : seq_con (filter (b_not_read b) (lower m1) ++
                      proj_block (lower ops) b)),
    SC (m1 ++ ops ++ m2).
  Proof.
    unfold SC; intros.
    repeat rewrite lower_app in *.
    setoid_rewrite consistent_split_reads; auto.
    setoid_rewrite consistent_split_reads in Hseq;
      [|apply read_init_drop_b' | apply write_alloc_drop_b']; clarify.
    split.
    { rewrite drop_b_reads_spec in Hseq1; repeat rewrite filter_app in *.
      rewrite filter_filter in Hseq1; setoid_rewrite (filter_ext _ not_read)
        in Hseq1 at 2; auto.
      rewrite Forall_forall; unfold andb; clarify. }
    intros ??? Hreads.
    destruct (in_range_dec r (length (lower m1))
      (length (lower m1) + length (lower ops))) as [Hrange | [Hrange1 Hrange2]].
    - specialize (Hseq2 (adjust_range (lower m1) (lower ops) (lower
        (drop_b_reads b ops)) r)); rewrite adjust_range_nth' in Hseq2; auto.
      specialize (Hseq2 _ _ Hreads); rewrite last_drop in Hseq2; auto.
    - rewrite nth_error_app in *; destruct (lt_dec r (length (lower m1)));
        [omega|].
      rewrite nth_error_app in *; destruct (lt_dec (r - length (lower m1))
        (length (lower ops))); [|omega].
      exploit nth_error_split'; eauto; intros (l1 & l2 & Hr & Hl).
      rewrite firstn_app, firstn_length', Hl; [|omega].
      rewrite <- app_assoc; simpl.
      rewrite <- Hr, firstn_app, firstn_length, minus_diag; clarify.
      destruct p as (b', o); destruct (eq_dec b' b).
      + subst; rewrite Hl in Hseq'.
        rewrite proj_block_app in Hseq'; clarify.
        rewrite app_assoc, to_ilist_app in Hseq'.
        generalize (read_justified_op _ _ _ _ Hseq'); intro Hlast; use Hlast.
        rewrite last_op_proj, app_nil_r; simpl.
        setoid_rewrite proj_block_app.
        rewrite <- last_op_filter; rewrite <- last_op_filter in Hlast.
        repeat rewrite filter_app in *.
        rewrite b_not_read_spec, filter_filter in Hlast.
        erewrite filter_ext in Hlast; eauto.
        rewrite Forall_forall; clarsimp.
        { rewrite app_assoc in Hread; generalize (read_init_app _ _ Hread).
          intro Hread1; generalize (read_init_proj _ Hread1 b).
          rewrite Hl; repeat setoid_rewrite proj_block_app; intro Hread2.
          generalize (read_init_filter' _ _ Hread2).
          rewrite b_not_read_spec; clarify.
          rewrite <- iapp_app; repeat rewrite to_ilist_app in *; auto. }
      + rewrite drop_b_reads_spec, Hl in Hseq2.
        specialize (Hseq2 (length (lower m1) + length (filter (fun op =>
          block_model.not_read op || negb (beq (block_of op) b)) l1))).
        rewrite nth_error_plus, filter_app in Hseq2; clarify.
        unfold negb, beq in Hseq2; destruct (eq_dec b' b); clarify.
        rewrite <- app_assoc in Hseq2; simpl in Hseq2.
        specialize (Hseq2 _ _ (nth_error_split _ _ _)).
        rewrite firstn_app, firstn_length', minus_plus, firstn_app,
          firstn_length, minus_diag in Hseq2; [clarify | omega].
        rewrite app_nil_r in *.
        rewrite <- last_op_filter in Hseq2; rewrite <- last_op_filter.
        repeat rewrite filter_app in *.
        rewrite filter_filter in Hseq2;
          setoid_rewrite (filter_ext _ not_read) in Hseq2 at 2; auto.
        rewrite Forall_forall; unfold andb; clarify.
  Qed.

  Variable (b0 : block).

  Section SC.

    Hypothesis drop_race_free : forall m1 c m2 b
      (Hrf : race_free (iapp m1 (icons c m2))),
      race_free (iapp m1 (iapp (drop_b_reads b [c]) m2)).

    Global Instance SC_MM : Memory_Model := { consistent := fun m =>
      exists m', to_ilist m' = m /\ SC m';
      well_formed := fun m => exists m', to_ilist m' = m /\
        read_init (lower m') /\ write_alloc (lower m') }.
    Proof.
      - exists []; unfold SC; clarify.
        apply block_model.consistent_nil; auto.
      - unfold SC; split; clarify; eauto.
        exploit to_ilist_inj; eauto; clarify.
      - clarify.
        exploit to_ilist_inj; eauto; clarify.
        destruct Hread as (opr & Hr & Hopr).
        rewrite inth_nth_error in Hr; exploit nth_error_split'; eauto;
          intros (m1 & m2 & ?); clarify.
        exploit in_split; eauto; intros (l1 & l2 & Hl).
        unfold SC in Hcon2; rewrite lower_app, lower_cons, Hl
          in Hread_init, Hcon2.
        rewrite <- app_assoc, app_assoc in Hread_init, Hcon2; clarify.
        rewrite to_ilist_app in Hread_init, Hcon2.
        generalize (read_justified_op _ _ _ _ Hcon2 Hread_init);
          intros (w & Hlast & Hw).
        rewrite inth_nth_error, nth_error_app in Hw;
          destruct (lt_dec w (length (lower m1))).
        exploit nth_lower_split; eauto;
          intros (m1' & opw & m2' & i & ? & Hi & ?); clarify.
        generalize (nth_error_in _ _ Hi); intro.
        exists (length m1'); repeat split.
        + rewrite app_length; simpl; omega.
        + unfold writes; rewrite <- app_assoc, inth_nth_error.
          simpl; rewrite nth_error_split; eauto.
        + unfold writes; intros ?? Hwrite [Hhb1 Hhb2]; clarify.
          generalize (hb_lt Hhb1), (hb_lt Hhb2); intros.
          rewrite inth_nth_error, nth_error_app in Hwrite1; clarify.
          rewrite nth_error_app in Hwrite1; destruct (lt_dec w2 (length m1'));
            [omega|].
          destruct (w2 - length m1') eqn: Hminus; [omega | clarify].
          inversion Hlast.
          rewrite inth_nth_error, nth_error_app in Hop1; clarify.
          rewrite Hw in Hop1; clarify.
          exploit nth_error_split'; eauto; intros (l1' & l2' & ?); clarify.
          generalize (in_nth_error _ _ Hwrite2); intros (i2 & Hlt2 & Hi2).
          specialize (Hlast0 (length (lower m1') + (length (to_seq opw) +
            (length (lower l1') + i2)))).
          rewrite lower_app, lower_cons, lower_app, lower_cons in Hlast0.
          repeat rewrite <- app_assoc in Hlast0.
          rewrite inth_nth_error in Hlast0;
            repeat rewrite nth_error_plus in Hlast0.
          generalize (nth_error_lt _ _ Hi); intro.
          rewrite nth_error_app in Hlast0; clarify.
          specialize (Hlast0 _ Hi2); clarify; omega.
        + intro Hhb; generalize (hb_lt Hhb); rewrite app_length; omega.
        + generalize (read_safe opr); rewrite Hl; intro Hsafe.
          specialize (Hsafe (length l1)); rewrite nth_error_split in Hsafe.
          exploit nth_error_lt; eauto; intro Hlt.
          specialize (Hsafe _ _ eq_refl _ Hlt v);
            rewrite nth_error_app in Hsafe; clarify.
      - clarify.
        exploit to_ilist_app_inv; eauto; clarify.
        exploit (to_ilist_app_inv ops); eauto; clarify.
        exists (m1 ++ drop_b_reads b ops ++ x); split;
          [repeat rewrite to_ilist_app; auto|].
        repeat rewrite lower_app in *; split;
          [apply read_init_drop_b' | apply write_alloc_drop_b']; auto.
      - intros; apply drop_race_free; auto.
      - clarify.
        exploit to_ilist_app_inv; eauto; clarify.
        exploit (to_ilist_app_inv ops); eauto; clarify.
        split; intro Hcon; clarify.
        + repeat rewrite <- to_ilist_app in *.
          exploit to_ilist_inj; eauto; clarify.
          split.
          * do 2 eexists; eauto.
            apply drop_SC; auto.
          * unfold SC in *; repeat rewrite lower_app in *.
            rewrite app_assoc in *; generalize (read_init_app _ _ Hwf21),
              (write_alloc_app _ _ Hwf22), (consistent_app _ _ Hcon2);
              intros ? ? Hcon.
            generalize (consistent_proj _ b Hcon); intro Hcon'; clarify.
            setoid_rewrite proj_block_app in Hcon'.
            rewrite consistent_core_ops in Hcon'.
            rewrite proj_idem in Hcon'.
            rewrite b_not_read_spec; clarify.
            { apply filter_Forall; unfold beq; clarify. }
            { rewrite <- proj_block_app; apply read_init_proj; auto. }
            { rewrite <- proj_block_app; apply write_alloc_proj; auto. }
        + exploit to_ilist_app_inv; eauto; clarify.
          exploit (to_ilist_app_inv (drop_b_reads b ops)); eauto; clarify.
          exploit to_ilist_inj; eauto; clarify.
          do 2 eexists; eauto.
          eapply merge_SC; eauto.
    Defined.

  End SC.

  Context {MM : Memory_Model}.

(* Well-synchronized programs *)

  Lemma race_free_app : forall m1 m2, race_free (m1 ++ m2) -> race_free m1.
  Proof.
    unfold race_free; intros.
    specialize (H _ _ Hdiff).
    repeat rewrite inth_nth_error, nth_error_app in *.
    generalize (nth_error_lt _ _ Ha), (nth_error_lt _ _ Hb); clarify.
    rewrite to_ilist_app in H.
    exploit H; eauto; [repeat eexists; eauto|].
    intros [Hhb | Hhb]; [left | right]; eapply hb_app_impl;
      eauto.
  Qed.

  (* up? *)
  Instance mem_op_eq : EqDec_eq mem_op.
  Proof. eq_dec_inst. Qed.

  Definition has_read (c : conc_op) :=
    existsb (fun op => negb (not_read op)) (to_seq c).

  Lemma drop_b_filter : forall b ops,
    filter not_read (lower (drop_b_reads b ops)) = filter not_read (lower ops).
  Proof.
    intros.
    generalize (drop_b_reads_spec b ops); intro Hdrop.
    erewrite Hdrop, filter_filter, filter_ext; eauto.
    rewrite Forall_forall; clarify.
    rewrite absoption_andb; auto.
  Qed.

  (* up? *)
  Definition read_init_op (m : ilist mem_op) := forall i p v
    (Hread : inth m i = Some (MRead p v)),
    exists v', last_op (itake i m) (Ptr p) (MWrite p v').
    
  Lemma read_init_alt : forall m, read_init m <-> read_init_op m.
  Proof.
    intro; split; repeat intro.
    - specialize (H i p v); clarify.
      unfold last_op; eexists; eexists; split; eauto.
      generalize (last_mod_lt _ H1); intro.
      generalize (itake_length i m); intro.
      rewrite inth_nth_error, itake_nth; destruct (lt_dec x i); eauto; omega.
    - specialize (H i p v); clarify.
      unfold last_op in *; clarify.
      eexists; eexists; split; eauto.
      rewrite inth_nth_error, itake_nth in *; clarify; eauto.
  Qed.
  (* This is a much better definition. *)

  (* up *)
  Lemma read_init_snoc : forall (m : list mem_op) op (Hread : read_init m),
    read_init (m ++ [op]) <->
      match op with
      | MRead p v => exists v', last_op m (Ptr p) (MWrite p v')
      | _ => True
      end.
  Proof.
    intros; rewrite read_init_alt in *; split; intro.
    - destruct op; clarify.
      specialize (H (length m) p v);
        rewrite inth_nth_error, nth_error_split in H; clarsimp; eauto.
    - repeat intro; specialize (Hread i p v).
      rewrite inth_nth_error, nth_error_app in *.
      destruct (lt_dec i (length m)); clarify.
      + exists x; clarsimp.
        rewrite not_le_minus_0, app_nil_r; clarify; omega.
      + rewrite nth_error_single in *; clarify.
        exists x; clarsimp.
        rewrite firstn_length'; auto; omega.
  Qed.

  (* up *)
  Definition write_alloc_op (m : ilist mem_op) := forall i p v
    (Hwrite : inth m i = Some (MWrite p v)),
    (exists v', last_op (itake i m) (Ptr p) (MWrite p v')) \/
    (exists n, last_op (itake i m) (Ptr p) (MAlloc (fst p) n) /\ snd p < n).
    
  Lemma write_alloc_alt : forall m, write_alloc m <-> write_alloc_op m.
  Proof.
    intro; split; intro Hw; repeat intro.
    - specialize (Hw i p v); clarify.
      generalize (lt_le_trans _ _ _ (last_mod_lt _ Hw1) (itake_length i m)).
      unfold last_op; destruct Hw2; [left | right]; clarify.
      + do 3 eexists; eauto.
        rewrite inth_nth_error, itake_nth; clarify; eauto.
      + do 2 eexists; eauto.
        do 2 eexists; eauto.
        rewrite inth_nth_error, itake_nth; clarify.
    - specialize (Hw i p v); clarify.
      unfold last_op in *; destruct Hw; clarify; do 2 eexists; eauto.
      + rewrite inth_nth_error, itake_nth in *; clarify; eauto.
      + rewrite inth_nth_error, itake_nth in *; clarify; eauto.
  Qed.
  (* This is a much better definition. *)

  (* up *)
  Lemma write_alloc_snoc : forall (m : list mem_op) op (Hwrite : write_alloc m),
    write_alloc (m ++ [op]) <->
      match op with
      | MWrite p v => (exists v', last_op m (Ptr p) (MWrite p v')) \/
          exists n, last_op m (Ptr p) (MAlloc (fst p) n) /\ snd p < n
      | _ => True
      end.
  Proof.
    intros; rewrite write_alloc_alt in *; split; intro.
    - destruct op; clarify.
      specialize (H (length m) p v);
        rewrite inth_nth_error, nth_error_split in H; clarsimp; eauto.
    - repeat intro; specialize (Hwrite i p v).
      rewrite inth_nth_error, nth_error_app in *.
      destruct (lt_dec i (length m)); clarify.
      + destruct Hwrite; [left | right]; clarsimp;
          rewrite not_le_minus_0, app_nil_r; clarify; eauto; omega.
      + rewrite nth_error_single in *; clarify.
        destruct H; [left | right]; clarsimp;
          rewrite firstn_length'; eauto; omega.
  Qed.

  Lemma race_free_mods_read : forall m i j a p v o (Hrf : race_free m)
    (Hdiff : i <> j)  (Hmods : mods m i (fst p, o)) (Ha : inth m j = Some a)
    (Hread : In (MRead p v) (to_seq a)),
    happens_before m i j \/ happens_before m j i.
  Proof.
    intros; unfold mods in *; clarify.
    eapply Hrf; eauto.
    do 3 eexists; eauto.
  Qed.

  Lemma race_free_read : forall m r p v (Hread_init : read_init (lower m))
    (Hcon : consistent m) (Hrf : race_free m)
    (Hread : reads m r p v), exists w, writes m w p v /\
      happens_before m w r /\
      forall w2 v2, w2 < r -> writes m w2 p v2 -> hbe m w2 w.
  Proof.
    intros.
    exploit read_write; eauto; intros [w Hw]; exists w; clarify.
    generalize (Hrf w r); intro Hwr; clarify.
    unfold reads, writes in *; clarify.
    destruct p; specialize (Hwr _ _ Hw211 Hread1); use Hwr; clarify.
    generalize (Hrf w w2); intro Hww.
    unfold hbe; destruct (eq_dec w2 w); clarify; left.
    specialize (Hww _ _ Hw211 H01); use Hww; clarify.
    specialize (Hrf w2 r).
    destruct (eq_dec w2 r); [omega | clarify].
    specialize (Hrf _ _ H01 Hread1); use Hrf; clarify.
    specialize (Hw221 w2 v2); use Hw221; [|eauto].
    contradiction Hw221; clarify.
    exploit hb_lt; eauto; omega.
    - do 5 eexists; eauto; split; eauto; clarify.
    - do 5 eexists; eauto; split; eauto; clarify.
    - do 5 eexists; eauto; split; eauto; clarify.
  Qed.

  Lemma race_free_before : forall m1 c m2 i b o o' v
    (Hrf : race_free (iapp m1 (icons c m2)))
    (Hread : In (MRead (b, o') v) (to_seq c)) (Hmods : mods m1 i (b, o)),
     happens_before (iapp m1 (icons c m2)) i (length m1).
  Proof.
    unfold mods; clarify.
    rewrite inth_nth_error in *; exploit nth_error_lt; eauto; intro.
    destruct (eq_dec i (length m1)); [omega|].
    exploit race_free_mods_read; eauto; clarify.
    { unfold mods; rewrite iapp_nth; clarify; eauto. }
    { rewrite iapp_nth; clarsimp. }
    exploit hb_lt; eauto; omega.
  Qed.

  Lemma race_free_after : forall m1 c m2 i b o o' v
    (Hrf : race_free (iapp m1 (icons c m2)))
    (Hread : In (MRead (b, o') v) (to_seq c)) (Hmods : mods m2 i (b, o)),
    happens_before (iapp m1 (icons c m2)) (length m1) (i + length m1 + 1).
  Proof.
    unfold mods; clarify.
    rewrite (plus_comm i); rewrite <- plus_assoc, NPeano.Nat.add_1_r.
    destruct (eq_dec (length m1 + S i) (length m1)); [omega|].
    exploit race_free_mods_read; eauto.
    { unfold mods; rewrite iapp_nth, lt_dec_plus_r, minus_plus; clarify; eauto. 
    }
    { rewrite iapp_nth; clarsimp. }
    intro Hhb; clarify.
    generalize (lt_plus _ (hb_lt Hhb)); clarify.
  Qed.

  (* We could let m be infinite and do "for all prefixes" instead if we want. *)
  Theorem race_free_SC : forall (m : list _) (Hrf : race_free m)
    (Hread : read_init (lower m)) (Hwrite : write_alloc (lower m))
    (Hwf : well_formed m), consistent m <-> SC m.
  Proof.
    unfold SC; intros; split; intro Hcon.
    - remember (length (filter (fun op => negb (not_read op)) (lower m)))
        as nreads; generalize dependent m; induction nreads using lt_wf_ind;
        intros.
      destruct nreads.
      { rewrite <- read_free; auto.
        repeat intro.
        unfold reads in *; clarify.
        destruct (filter (fun op => negb (not_read op)) (lower m)) eqn: Hfilter;
          clarify.
        rewrite filter_none_iff in Hfilter.
        rewrite Forall_forall in Hfilter.
        setoid_rewrite flatten_in in Hfilter.
        setoid_rewrite in_map_iff in Hfilter.
        rewrite inth_nth_error in *; exploit nth_error_in; eauto; intro.
        specialize (Hfilter (MRead p v)); use Hfilter; eauto; clarify. }
      destruct (find has_read (rev m)) eqn: Hfind.
      rewrite find_spec in Hfind; clarify.
      exploit nth_error_rev'; eauto; intro Hnth.
      unfold has_read in Hfind21; rewrite existsb_exists in Hfind21; clarify.
      destruct x0; clarify.
      exploit nth_error_split'; eauto; intros [m1 [m2 ?]]; clarify.
      rewrite split_app in Hcon; rewrite <- app_assoc in Hcon;
        repeat rewrite to_ilist_app in Hcon.
      assert (read_init (filter (b_not_read (fst p)) (lower m1) ++
        proj_block (to_seq c ++ []) (fst p))) as Hread0.
      { rewrite split_app, lower_app in Hread.
        generalize (read_init_app _ _ Hread); rewrite lower_app; intro Hr.
        generalize (read_init_proj _ Hr (fst p));
          setoid_rewrite proj_block_app at 1; intro Hr'.
        generalize (read_init_filter' _ _ Hr'); unfold proj_block at 1;
          rewrite filter_filter; clarify. }
      assert (write_alloc (lower (m1 ++ [c]))) as Hwrite0.
      { eapply write_alloc_app; rewrite split_app, lower_app in Hwrite; eauto. }
      rewrite to_ilist_app in Hwf; erewrite private_seq in Hcon; clarify; eauto.
      repeat rewrite <- to_ilist_app in *; clarify.
      specialize (H (length (filter (fun op => negb (not_read op))
        (lower (m1 ++ drop_b_reads (fst p) [c] ++ m2))))).
      use H.
      specialize (H (m1 ++ drop_b_reads (fst p) [c] ++ m2)).
      assert (read_init (lower (m1 ++ drop_b_reads (fst p) [c] ++ m2)))
        as Hread'.
      { repeat rewrite lower_app in *; apply read_init_drop_b'.
        rewrite <- lower_app; auto. }
      assert (write_alloc (lower (m1 ++ drop_b_reads (fst p) [c] ++ m2)))
        as Hwrite'.
      { repeat rewrite lower_app in *; apply write_alloc_drop_b'.
        rewrite <- lower_app; auto. }
      use H; clarify.
      use H; clarify.
      + rewrite split_app; rewrite <- app_assoc; eapply merge_SC; eauto.
      + repeat rewrite to_ilist_app in *; apply drop_wf; auto.
      + repeat rewrite to_ilist_app in *; apply drop_race_free; auto.
      + rewrite Heqnreads; eapply drop_reads; eauto.
      + destruct p; rewrite to_ilist_app in *; eapply race_free_before; eauto.
      + unfold reads in *; clarify.
        destruct i; clarify; [|rewrite inth_nil in *; clarify].
        exploit race_free_read; eauto.
        { rewrite to_ilist_app in *; auto. }
        { unfold reads.
          clear Hfind211; do 2 eexists; eauto.
          instantiate (1 := length m1); rewrite inth_nth_error;
            apply nth_error_split. }
        intros [w Hw]; exists w; clarify.
        rewrite plus_0_r; exploit hb_lt; eauto; clarify.
        unfold writes in *; clarify.
        rewrite inth_nth_error, nth_error_app in *; clarify.
        split; eauto; clarify.
        rewrite to_ilist_app in Hw22; eapply Hw22; auto.
        rewrite inth_nth_error, nth_error_app, iapp_nth in *; clarify; eauto.
      + rewrite NPeano.Nat.add_sub.
        destruct p; rewrite to_ilist_app in *; eapply race_free_after; eauto.
      + rewrite find_fail, Forall_rev in Hfind.
        rewrite filter_none in Heqnreads; clarify.
        rewrite Forall_forall in *; intros ? Hin.
        setoid_rewrite flatten_in in Hin; clarify.
        rewrite in_map_iff in Hin2; clarify.
        specialize (Hfind _ Hin22); unfold has_read in *.
        destruct x; clarify.
        assert (existsb (fun op => negb (not_read op)) (to_seq x1) = true);
          clarify.
        rewrite existsb_exists; eauto.
    - remember (length (filter (fun op => negb (not_read op)) (lower m)))
        as nreads; generalize dependent m; induction nreads using lt_wf_ind;
        intros.
      destruct nreads.
      { rewrite read_free; auto.
        repeat intro.
        unfold reads in *; clarify.
        destruct (filter (fun op => negb (not_read op)) (lower m)) eqn: Hfilter;
          clarify.
        rewrite filter_none_iff in Hfilter.
        rewrite Forall_forall in Hfilter.
        setoid_rewrite flatten_in in Hfilter.
        setoid_rewrite in_map_iff in Hfilter.
        rewrite inth_nth_error in *; exploit nth_error_in; eauto; intro.
        specialize (Hfilter (MRead p v)); use Hfilter; eauto; clarify. }
      destruct (find has_read (rev m)) eqn: Hfind.
      rewrite find_spec in Hfind; clarify.
      exploit nth_error_rev'; eauto; intro Hnth.
      unfold has_read in Hfind21; rewrite existsb_exists in Hfind21; clarify.
      destruct x0; clarify.
      exploit nth_error_split'; eauto; intros [m1 [m2 ?]]; clarify.
      rewrite split_app; rewrite <- app_assoc; repeat rewrite to_ilist_app.
      assert (read_init (filter (b_not_read (fst p)) (lower m1) ++
        proj_block (lower [c]) (fst p))) as Hread0.
      { rewrite split_app, lower_app in Hread.
        generalize (read_init_app _ _ Hread); rewrite lower_app; intro Hr.
        generalize (read_init_proj _ Hr (fst p));
          setoid_rewrite proj_block_app at 1; intro Hr'.
        generalize (read_init_filter' _ _ Hr'); unfold proj_block at 1;
          rewrite filter_filter; clarify. }
      assert (write_alloc (lower (m1 ++ [c]))) as Hwrite0.
      { eapply write_alloc_app; rewrite split_app, lower_app in Hwrite; eauto. }
      rewrite to_ilist_app in Hwf; erewrite private_seq; clarify; eauto 2.
      repeat rewrite <- to_ilist_app; clarify.
      split.
      + assert (read_init (lower (m1 ++ drop_b_reads (fst p) [c] ++ m2)))
          as Hread'.
        { repeat rewrite lower_app in *; apply read_init_drop_b'.
          rewrite <- lower_app; auto. }
        assert (write_alloc (lower (m1 ++ drop_b_reads (fst p) [c] ++ m2)))
          as Hwrite'.
        { repeat rewrite lower_app in *; apply write_alloc_drop_b'.
          rewrite <- lower_app; auto. }
        eapply H; try reflexivity; auto.
        { rewrite Heqnreads; eapply drop_reads; eauto. }
        { repeat rewrite to_ilist_app in *; apply drop_race_free; auto. }
        { repeat rewrite to_ilist_app in *; apply drop_wf; auto. }
        apply drop_SC; auto.
      + setoid_rewrite consistent_split_reads in Hcon; auto;
          destruct Hcon as [Hseq Hreads].
        setoid_rewrite consistent_split_reads; auto.
        * split.
          { rewrite lower_app, lower_cons in Hread, Hwrite, Hseq.
            generalize (consistent_proj _ (fst p) Hseq (read_init_none _)).
            rewrite write_alloc_filter; intro Hcon; clarify.
            rewrite proj_filter_comm, app_assoc in Hcon.
            repeat setoid_rewrite proj_block_app in Hcon;
              repeat rewrite filter_app in *.
            rewrite lower_single; unfold proj_block at 1 in Hcon.
            rewrite filter_filter in *.
            erewrite filter_ext in Hcon; [eapply consistent_app; eauto|].
            { rewrite Forall_forall; unfold b_not_read, andb; clarify. } }
          intros ? ? ? Hr.
          rewrite nth_error_app in Hr; destruct (lt_dec r
            (length (filter (b_not_read (fst p)) (lower m1)))).
          { exploit nth_error_in; eauto; rewrite filter_In; clarify. }
          rewrite lower_single in Hr; unfold proj_block in Hr.
          exploit nth_error_in; eauto; rewrite filter_In; intro Hin; clarify.
          destruct p0 as (b', ?); unfold beq in Hin2; clarify.
          exploit nth_filter_split; eauto; intros (l1 & l2 & Hc & Hlen & ?).
          rewrite lower_app, lower_cons in Hreads; rewrite lower_single;
            rewrite Hc in *.
          rewrite <- app_assoc in Hreads; simpl in Hreads;
            rewrite app_assoc in Hreads.
          specialize (Hreads (length (lower m1 ++ l1)));
            rewrite nth_error_split in Hreads.
          specialize (Hreads _ _ eq_refl).
          rewrite firstn_app, firstn_length, minus_diag in Hreads; clarify.
          rewrite firstn_app, firstn_length', Hlen, proj_block_app,
            firstn_app, firstn_length, minus_diag; [simpl | omega].
          rewrite app_nil_r in *;
            rewrite last_op_proj, proj_block_app in Hreads;
            rewrite <- last_op_filter in Hreads; rewrite <- last_op_filter.
          rewrite filter_app in *.
          unfold proj_block at 1 in Hreads; rewrite filter_filter in *.
          erewrite filter_ext in Hreads; eauto.
          { rewrite Forall_forall; unfold b_not_read, andb; clarify. }
        * rewrite lower_app in Hwrite0.
          generalize (write_alloc_proj _ Hwrite0 (fst p)).
          rewrite <- write_alloc_filter; setoid_rewrite proj_block_app;
            intro Hw.
          simpl; rewrite app_nil_r, lower_single in *.
          rewrite <- write_alloc_filter; repeat rewrite filter_app in *.
          unfold proj_block at 1 in Hw; rewrite filter_filter in *;
            erewrite filter_ext; eauto.
          { clear; rewrite Forall_forall; unfold b_not_read, andb; clarify. }
      + destruct p; rewrite to_ilist_app in *; eapply race_free_before; eauto.
      + setoid_rewrite consistent_split_reads in Hcon; clarify.
        unfold reads in *; clarify.
        destruct i; clarify; [|rewrite inth_nil in *; clarify].
        clear Hfind211; exploit in_nth_error; eauto; intros [i Hi].
        rewrite lower_app, lower_cons in Hcon2.
        specialize (Hcon2 (length (lower m1) + i)); rewrite nth_error_app,
          lt_dec_plus_r, minus_plus, nth_error_app in Hcon2; clarify.
        specialize (Hcon2 _ _ Hi2).
        destruct Hcon2 as [w Hw]; clarify.
        rewrite inth_nth_error, nth_error_firstn in *; clarify.
        rewrite nth_error_app in Hw2; destruct (lt_dec w (length (lower m1))).
        exploit nth_lower_split; eauto; intros (l1' & ? & l2' & ? & ? & Hw & ?);
          clarify.
        generalize (nth_error_in _ _ Hw); intro.
        exists (length l1'); rewrite plus_0_r; split;
          [rewrite app_length; simpl; omega|].
        unfold writes; rewrite <- app_assoc; simpl.
        rewrite inth_nth_error, nth_error_split; split; [eauto|].
        intros ? ? Hlt Hk; clarify.
        specialize (Hrf k (length l1')); unfold hbe;
          destruct (eq_dec k (length l1')); clarify; left.
        rewrite inth_nth_error, nth_error_app in Hrf; clarify.
        rewrite inth_nth_error, split_app in Hk1.
        rewrite app_assoc in Hk1; rewrite <- (app_assoc l1'), nth_error_app
          in Hk1; clarify.
        rewrite <- app_assoc in Hrf; simpl in Hrf;
          rewrite inth_nth_error, nth_error_split in Hrf.
        specialize (Hrf _ _ Hk1 eq_refl); use Hrf.
        rewrite split_app, app_assoc, to_ilist_app in Hrf; simpl in Hrf.
        rewrite <- app_assoc in Hrf; clarify.
        exploit hb_lt; eauto; intro.
        inversion Hw1.
        rewrite nth_error_app in Hk1; destruct (lt_dec k (length l1'));
          [omega|].
        destruct (k - length l1') eqn: Hminus; [omega | clarify].
        setoid_rewrite firstn_app in Hlast; rewrite firstn_length' in Hlast;
          [|omega].
        exploit nth_error_split'; eauto; intros (l3' & l4' & ?); clarify.
        rewrite split_app, app_assoc, lower_app, lower_cons in Hlast.
        repeat rewrite <- app_assoc in Hlast.
        exploit in_nth_error; eauto; intros [i' Hi']; clarify.
        exploit nth_error_lt; eauto; intro.
        specialize (Hlast (length (lower (l1' ++ [x1] ++ l3')) + i'));
          rewrite inth_nth_error, nth_error_app, lt_dec_plus_r, nth_error_app,
          minus_plus in Hlast; clarify.
        specialize (Hlast _ Hi'2); clarify.
        rewrite lower_app, lower_cons in Hlast;
          repeat rewrite app_length in Hlast.
        generalize (nth_error_lt _ _ Hw); omega.
        * do 5 eexists; eauto; split; eauto; clarify.
        * generalize (read_safe _ Hi2); intro Hsafe.
          specialize (Hsafe (w - length (lower m1))); use Hsafe; [|omega].
          rewrite nth_error_app in Hw2; destruct (lt_dec (w - length (lower m1))
            (length (to_seq x0))); [|omega].
          exploit Hsafe; eauto; clarify.
      + rewrite NPeano.Nat.add_sub.
        destruct p; rewrite to_ilist_app in *; eapply race_free_after; eauto.
      + rewrite find_fail, Forall_rev in Hfind.
        rewrite filter_none in Heqnreads; clarify.
        rewrite Forall_forall in *; intros ? Hin.
        setoid_rewrite flatten_in in Hin; clarify.
        rewrite in_map_iff in Hin2; clarify.
        specialize (Hfind _ Hin22); unfold has_read in *.
        destruct x; clarify.
        assert (existsb (fun op => negb (not_read op)) (to_seq x1) = true);
          clarify.
        rewrite existsb_exists; eauto.
  Qed.

  Context (thread_eq : EqDec_eq thread).

  Definition event_structure := thread -> list conc_op.
  Definition evst_of (m : list conc_op) t :=
    filter (fun c => beq (thread_of c) t) m.

  Hypothesis alpha : forall (m : list _), consistent m ->
    race_free m \/ exists m', evst_of m' = evst_of m /\ SC m' /\ ~race_free m'.

  Theorem race_free_SC' : forall E
    (Hrf : forall m, evst_of m = E -> SC m -> race_free m)
    m (HE : evst_of m = E)
    (Hread : read_init (flatten (map to_seq m)))
    (Hwrite : write_alloc (flatten (map to_seq m))) (Hwf : well_formed m),
    consistent m <-> SC m.
  Proof.
    split; intros; [rewrite <- race_free_SC | rewrite race_free_SC]; auto.
    generalize (alpha _ H); intros [? | [m' Hm']]; clarify.
    specialize (Hrf m'); clarify.
  Qed.
    
End Concurrency.