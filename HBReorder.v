Require Import Util.
Require Import VectorClocks.
Require Import block_model.
Require Import conc_model.
Require Import Lang.
Require Import FunctionalExtensionality.
Require Import HBRaceDetector.
Require Import SCFacts.
Require Import ExecFacts.
Set Implicit Arguments.

Section Reordering.

Context {ML : @Memory_Layout var nat _}.

Context {meta : metadata}.

Hint Resolve zt_non_zero.

Definition state_suffix := Forall2 (fun (t1 t2 : tid * list instr) =>
  let (t, li) := t1 in fst t2 = t /\ exists n,
    n < length (instrument_instr (hd (Assign 0 (I 0)) li) t) /\
    snd t2 = skipn n (instrument li t)).

Lemma final_suffix : forall P P' (Hsuffix : state_suffix P P')
  (Hfinal : final_state (Some P')), final_state (Some P).
Proof.
  induction P; clarify.
  inversion Hsuffix; clarify.
  destruct a, y; clarify.
  inversion Hfinal; clarify.
  constructor; [|eapply IHP; eauto].
  rewrite skipn_all_iff in *; destruct l; clarify.
  rewrite app_length in *; omega.
Qed.

Lemma upd_triv1 : forall (G : env) t, upd G t (G t) = G.
Proof.
  intros; extensionality x; apply VectorClocks.upd_triv.
Qed.

Lemma iexec_decr : forall P G t o c P' G' (Hstep : iexec P G t o c P' G'),
  size P' < size P.
Proof.
  intros; inversion Hstep; subst; repeat rewrite size_app; clarify;
    repeat rewrite instr_list_size_app; try (clarify; omega).
  unfold instr_list_size at 4; fold instr_list_size.
  rewrite spawn_size; simpl; omega.
Qed.

Lemma iexec_step' : forall P G t lo lc P' G' rd mops
  (Hstep : iexec P G t lo lc P' G') lo' lc' P'' G''
  (Hsteps : iexec_star P' G' lo' lc' P'' G'')
  (Hrd : rd = lo ++ lo') (Hmops : mops = lc ++ lc'),
  iexec_star P G rd mops P'' G''.
Proof.
  clarify; eapply iexec_step; eauto.
Qed.

(*
Fixpoint to_mem G t li vs :=
  match li with
  | [] => Some ([], G, vs)
  | i :: li =>
      match i with
      | Assign a e => to_mem (upd G a (eval G e)) t li vs
      | Load a x => match vs with [] => None | v :: vs =>
          match to_mem (upd G a v) t li vs with None => None
          | Some (lc, G, vs) => Some (Read t x v :: lc, G, vs) end end
      | Store x e => match to_mem G t li vs with None => None
          | Some (lc, G', vs) => Some (Write t x (eval G e) :: lc, G', vs) end
      | Lock m => match to_mem G t li vs with None => None
          | Some (lc, G, vs) => Some (Acq t m :: lc, G, vs) end
      | Unlock m => match to_mem G t li vs with None => None
          | Some (lc, G, vs) => Some (Rel t m :: lc, G, vs) end
      | _ => to_mem G t li vs
      end
  end.
*)

(*
(* up? *)
Lemma eval_old1: forall G t a v e (Hfresh : expr_fresh a e),
  eval (upd_env G t a v t) e = eval (G t) e.
Proof.
  induction e; clarify.
  apply upd_old; auto.
Qed.

Lemma upd_other_comm : forall G t t' a a' v v' (Hdiff : t' <> t),
  upd_env (upd_env G t a v) t' a' v' = upd_env (upd_env G t' a' v') t a v.
Proof.
  intros; unfold upd_env.
  rewrite upd_comm; auto.
  do 2 (rewrite VectorClocks.upd_old; auto).
Qed.

Lemma exec_mem : forall P G lo lc P' G' (Hdistinct : distinct P)
  (Hsteps : exec_star (Some P) G lo lc (Some P') G')
  t li1 li2 (Hin : In (t, li1 ++ li2) P) (Hin' : In (t, li2) P'),
  exists vs lc' vs', to_mem (G t) t li1 vs = Some (lc', G' t, vs') /\
    filter (fun c => beq (thread_of c) t) lc = lc'.
Proof.
  intros until t; remember (Some P) as Pa; remember (Some P') as Pb;
    generalize dependent P; induction Hsteps; clarify.
  { exploit distinct_in; [eauto | apply Hin | apply Hin' | intro H].
    exploit app_nil_inv; eauto; clear H.
    exists [], [], []; clarify. }
  destruct P'0; [|inversion Hsteps].
  exploit exec_result; eauto; intros (? & i & ? & ? & v & ?); clarify.
  destruct (instr_result t0 i (G t0) v) as [((((?, ?), ?), u), ?)|] eqn: Hi;
    clarify.
  destruct (eq_dec t0 t).
  - subst; exploit distinct_in; [eauto | apply split_in | eauto | clarify].
    exploit distinct_step; eauto; intro.
    destruct li1; clarify.
    { exploit exec_mono; eauto; [apply split_in|].
      clarify; exploit skip_cons_neq; eauto; contradiction. }
    exploit IHHsteps; try reflexivity; eauto.
    { apply split_in. }
    intros (vs & lc' & vs' & Hvs & Heq).
    destruct i0; clarify; try solve [do 3 eexists; setoid_rewrite Hvs; auto].
    + unfold upd_env in Hvs; rewrite upd_new in Hvs; eauto.
    + exists (v :: vs).
      unfold upd_env in Hvs; rewrite upd_new in Hvs; auto.
      do 2 eexists; setoid_rewrite Hvs; auto.
  - exploit exec_other_thread; try apply Hexec; eauto; intro.
    exploit distinct_step; eauto; intro.
    exploit IHHsteps; eauto; intros (? & ? & ? & Hvs & ?).
    exploit exec_ops; eauto; intro Hops.
    rewrite filter_app, filter_none.
    destruct u as [(?, ?)|]; eauto.
    unfold upd_env in Hvs; rewrite VectorClocks.upd_old in Hvs; eauto.
    { eapply Forall_impl; eauto 2; unfold beq; clarify. }
Qed.             

Lemma t_steps_None : forall t n P G lo lc G'
  (Hsteps : t_steps P G t n lo lc None G'),
  n > 0 /\ exists P1 G1 lo1 lc1 lo2 lc2,
    t_steps P G t (n - 1) lo1 lc1 (Some P1) G1 /\
    t_steps P1 G1 t 1 lo2 lc2 None G' /\ lo = lo1 ++ lo2 /\ lc = lc1 ++ lc2.
Proof.
  induction n; simpl; intros.
  { clarify. }
  destruct Hsteps as (? & ? & P1 & ? & ? & ? & ? & P2 & ? & ? & ? & Hminus1 &
    ?); clarify.
  destruct P2; clarify.
  - exploit IHn; eauto; intros (? & ? & ? & ? & ? & ? & ? & ? & ?).
    do 7 eexists.
    + destruct n; [omega | simpl].
      do 5 eexists; eauto.
      do 7 eexists; eauto; simpl in *.
      rewrite <- minus_n_O in *; eauto.
    + clarify.
      split; [repeat eexists; eauto|].
      repeat rewrite <- app_assoc; auto.
  - clear IHn.
    do 8 eexists; eauto; simpl; eauto.
    do 5 eexists; eauto.
    do 4 eexists; exists [], []; split; [eauto | clarify].
Qed.*)

(*
Lemma to_mem_app : forall t li1 li2 G vs lc G' vs',
  to_mem G t (li1 ++ li2) vs = Some (lc, G', vs') <->
  match to_mem G t li1 vs with None => False
  | Some (lc1, G1, vs1) => match to_mem G1 t li2 vs1 with None => False
  | Some (lc2, G2, vs2) => lc = lc1 ++ lc2 /\ G' = G2 /\ vs' = vs2 end end.
Proof.
  induction li1; clarify.
  - destruct (to_mem G t li2 vs) as [((?, ?), ?)|]; split; clarify.
  - assert (forall c G1 vs1, match to_mem G1 t (li1 ++ li2) vs1 with
      | Some (lc0, G0, vs0) => Some (c :: lc0, G0, vs0)
      | None => None end = Some (lc, G', vs') <->
      match match to_mem G1 t li1 vs1 with
            | Some (lc0, G0, vs0) => Some (c :: lc0, G0, vs0)
            | None => None end with
      | Some (lc1, G1, vs1) =>
          match to_mem G1 t li2 vs1 with
          | Some (lc2, G2, vs2) => lc = lc1 ++ lc2 /\ G' = G2 /\ vs' = vs2
          | None => False end
      | None => False end).
    { intros.
      specialize (IHli1 li2 G1 vs1).
      destruct (to_mem G1 t li1 vs1) as [((?, ?), ?)|]; clarify.
      destruct (to_mem n t li2 l0) as [((?, ?), ?)|]; clarify.
      destruct (to_mem G1 t (li1 ++ li2) vs1) as [((?, ?), ?)|];
        clarify.
      * specialize (IHli1 l0 n l3); destruct IHli1; split; clarify.
      * specialize (IHli1 (l ++ l1) n0 l2); destruct IHli1; clarify.
      * split; clarify.
        destruct x as ((?, ?), ?); clarify.
        rewrite IHli1 in *; auto.
      * split; clarify.
        destruct x as ((?, ?), ?); clarify.
        rewrite IHli1 in *; auto. }
    destruct a; clarify.
    destruct vs; [split|]; clarify.
Qed.

Lemma t_steps_mem : forall t n P G lo lc P' G' (Hdistinct : distinct P)
  (Hsteps : t_steps P G t n lo lc P' G') li (Hin : In (t, li) P),
  exists vs vs', to_mem (G t) t (firstn n li) vs =
    Some (filter (fun c => beq (thread_of c) t) lc, G' t, vs').
Proof.
  induction n; intros.
  { exists [], []; clarify. }
  simpl in Hsteps.
  destruct Hsteps as (? & c & P1 & ? & ? & ? & ? & P2 & ? & ? & ? & Hminus & ?);
    clarify.
  exploit exec_result; eauto; intros (? & i & rest & ? & v & ?); clarify.
  assert (li = i :: rest).
  { exploit distinct_in; [eauto | eauto | apply split_in | clarify]. }
  assert (match li with [] => [] | a :: l => a :: firstn n l end =
    [i] ++ firstn n rest) as Heq by clarify; subst; rewrite Heq.
  setoid_rewrite to_mem_app.
  assert (exists lcr, lc = opt_to_list c ++ lcr) as (lcr & ?).
  { destruct P2; clarify; eauto. }
  subst.
  assert (exists vs vs', to_mem match instr_result t i (G t) v with
    Some (_, _, _, u, _) => upd_env' G t u t | None => G t end t (firstn n rest)
    vs = Some (filter (fun c => beq (thread_of c) t) lcr, G' t, vs'))
    as (vs & vs' & Hm2).
  { exploit exec_minus_ops; eauto; intro Hops'.
    destruct P1; [|inversion Hminus]; clarify.
    - exploit distinct_step; eauto; intro.
      destruct (instr_result t i (G t) v) as [((((?, ?), ?), ?), ?)|]; clarify.
      destruct P2; clarify.
      + exploit exec_other_threads; try apply Hminus; try apply split_in; intro.
        exploit distinct_steps; try eapply exec_minus_exec; eauto; intro.
        exploit IHn; eauto.
        intros (vs & vs' & Heq); exists vs, vs'.
        erewrite exec_minus_env in Heq; eauto.
        exploit app_inv_head; eauto; clarify.
        rewrite filter_app, (filter_none _ Hops'); auto.
      + exploit app_inv_head; eauto; clarify.        
        rewrite (filter_none _ Hops').
        rewrite (exec_minus_env Hminus); exists [], []; auto.
    - exploit app_inv_head; eauto; clarify.
      exists [], [].
      destruct (instr_result t i (G t) v) as [((((?, ?), ?), ?), ?)|]; clarify.
  }
  exists (match i with Load _ _ => v :: vs | _ => vs end), vs'; destruct i;
    clarify.
  - unfold upd_env in Hm2; rewrite upd_new in Hm2; rewrite Hm2; auto.
  - unfold upd_env in Hm2; rewrite upd_new in Hm2; rewrite Hm2; auto.
  - inversion H; clarify.
Qed.
*)
(*
Lemma t_steps_indep : forall t li P G li2 lo lc P' G' (Hdistinct : distinct P)
  (Ht : In (t, li ++ li2) P)
  (Ht_steps : t_steps P G t (length li) lo lc (Some P') G')
  (Hwait : forall i u, nth_error li i = Some (Wait u) -> i = 0)
  m (Hcon : consistent (m ++ lc))
  lct lcr (Hpart : partition (fun c => beq (thread_of c) t) lc = (lct, lcr))
  (Hindep : Forall (fun c => Forall (fun c' => loc_of c' <> loc_of c) lct) lcr),
  exists lot P1 G1 lor,
    exec_star_t t (Some P) G lot lct (Some P1) G1 /\ In (t, li2) P1 /\
    exec_star_minus t (Some P1) G1 lor lcr (Some P') G' /\
    consistent (m ++ lct ++ lcr).
Proof.
  induction li using rev_ind; simpl; intros.
  { clarify; repeat eexists; eauto.
    - apply exec_refl_t.
    - apply exec_refl_m. }
  rewrite app_length in Ht_steps; exploit t_steps_plus; eauto; clear Ht_steps.
  intros (lo1 & lc1 & P1 & G1 & lo2 & lc2 & Hsteps1 & Hsteps2 & ? & ?); subst.
  rewrite <- app_assoc in Ht; simpl in Ht.
  specialize (IHli _ _ _ _ _ _ _ Hdistinct Ht Hsteps1); use IHli.
  rewrite app_assoc in Hcon; specialize (IHli _ (consistent_app_SC _ _ Hcon)).
  rewrite partition_filter in *; specialize (IHli _ _ eq_refl); use IHli.
  destruct IHli as (lot & Pt & Gt & lor & Htsteps & HPt & Hminus & Hcon').
  simpl in Hsteps2.
  destruct Hsteps2 as (o & c & P2 & G2 & Hstep & lo3 & lc3 & [P3|] & G3 & lo4 &
    lc4 & Hminus2 & Hresult); clarify.
  repeat rewrite filter_app in *.
  destruct P2; [|inversion Hminus2; clarify].
  exploit distinct_steps; eauto.
  { eapply exec_t_exec; eauto. }
  intro Hdistinctt.
  generalize (exec_minus_ops Hminus2); intro Hall2.
  rewrite (filter_none _ Hall2), (filter_negb_all _ Hall2) in *.
  generalize (exec_ops Hstep); intro Hallt.
  rewrite (filter_all _ Hallt), (filter_negb_none _ Hallt) in *.
  destruct (nil_dec li); clarify.
  { repeat eexists.
    - eapply exec_step_t; [eauto | apply exec_refl_t].
    - exploit step_thread; eauto; clarify.
    - rewrite app_nil_r; eauto.
    - repeat rewrite app_nil_r in *; auto. }
  generalize (exec_sooner_t Hminus Hstep Hdistinctt); intro Hswap; use Hswap.
  specialize (Hswap _ HPt); destruct Hswap as (Pt' & Gt' & Hstep' & Hminus').
  destruct Pt'; [|inversion Hminus'; clarify].
  repeat eexists.
  - rewrite app_nil_r; eapply exec_step_inv_t; eauto.
  - exploit step_thread; eauto; clarify.
  - rewrite app_nil_r; eapply exec_minus_trans; eauto.
  - rewrite <- app_assoc, app_nil_r in *.
    rewrite app_nil_r; eapply loc_split; eauto.
    { rewrite partition_filter; auto. }
    rewrite Forall_app in *; clarify.
    eapply Forall_impl; eauto 2; clarify.
    rewrite Forall_app in *; clarify.
    { eapply prog_steps, t_steps_exec; eauto. }
    { eapply prog_step; eauto. }
  - intro Hin; generalize (NoDup_id_inj _ _ _ Hdistinctt HPt Hin); clarify.
    specialize (Hwait (length li) u); clarify.
    rewrite nth_error_split in Hwait; destruct li; clarify.
  - repeat rewrite filter_app in Hindep; rewrite Forall_app in Hindep; clarify.
    eapply Forall_impl; eauto 2; clarify.
    rewrite Forall_app in *; clarify.
  - exploit nth_error_lt; eauto.
    specialize (Hwait i u); rewrite nth_error_app in Hwait; clarify.
Qed.*)

(*Lemma hb_check_no_wait : forall C1 C2 z tmp1 tmp2 j u,
  nth_error (hb_check C1 C2 z tmp1 tmp2) j <> Some (Wait u).
Proof.
  induction z; clarsimp.
  do 3 (destruct j; clarify).
Qed.

Lemma max_vc_no_wait : forall src tgt z tmp1 tmp2 j u,
  nth_error (max_vc src tgt z tmp1 tmp2) j <> Some (Wait u).
Proof.
  induction z; clarsimp.
  do 4 (destruct j; clarify).
Qed.

Lemma max_vc_no_wait' : forall src tgt tgt' z tmp1 tmp2 j u t,
  nth_error (max_vc src tgt z tmp1 tmp2 ++ inc_vc t tgt' tmp1 ) j <> Some (Wait u).
Proof.
  induction z; clarsimp.
  do 4 (destruct j; clarify).
  do 4 (destruct j; clarify).
Qed.

Transparent move.

Lemma set_vc_no_wait : forall src tgt z tmp j u,
  nth_error (set_vc src tgt z tmp) j <> Some (Wait u).
Proof.
  induction z; clarsimp.
  do 2 (destruct j; clarify).
Qed.

Lemma instrument_wait : forall i t j u
  (Hnth : nth_error (instrument_instr i t) j = Some (Wait u)), j = 0.
Proof.
  destruct i; clarsimp.
  - destruct x.
    destruct j; clarify.
    rewrite <- app_assoc, nth_error_app in Hnth;
      destruct (lt_dec j (length (hb_check (W + v) (C + t) zt tmp1 tmp2)));
      [exploit hb_check_no_wait; eauto; clarify|].
    destruct (j - length (hb_check (W + v) (C + t) zt tmp1 tmp2)); clarify.
    do 4 (destruct n1; clarify).
  - destruct x.
    destruct j; clarify.
    rewrite <- app_assoc, nth_error_app in Hnth;
      destruct (lt_dec j (length (hb_check (W + v) (C + t) zt tmp1 tmp2)));
      [exploit hb_check_no_wait; eauto; clarify|].
    rewrite <- app_assoc, nth_error_app in Hnth;
      destruct (lt_dec (j - length (hb_check (W + v) (C + t) zt tmp1 tmp2))
                       (length (hb_check (R + v) (C + t) zt tmp1 tmp2)));
      [exploit hb_check_no_wait; eauto; clarify|].
    destruct (j - length (hb_check (W + v) (C + t) zt tmp1 tmp2) -
              length (hb_check (R + v) (C + t) zt tmp1 tmp2)); clarify.
    do 4 (destruct n2; clarify).
  - destruct j; clarify.
    exploit max_vc_no_wait; eauto; clarify.
  - unfold unlock_handler in Hnth.
    rewrite <- app_assoc, nth_error_app in Hnth;
      destruct (lt_dec j (length (set_vc (C + t) (L + m) zt tmp1)));
      [exploit set_vc_no_wait; eauto; clarify|].
    destruct (j - length (set_vc (C + t) (L + m) zt tmp1)); clarify.
    do 4 (destruct n0; clarify).
  - unfold spawn_handler in Hnth.
    rewrite <- app_assoc, nth_error_app in Hnth;
      destruct (lt_dec j (length (max_vc (C + t0) (C + t) zt tmp1 tmp2)));
      [exploit max_vc_no_wait; eauto; clarify|].
    destruct (j - length (max_vc (C + t0) (C + t) zt tmp1 tmp2)); clarify.
    do 4 (destruct n0; clarify).
  -unfold wait_handler in Hnth.
    destruct j; clarify.
    exploit max_vc_no_wait'; eauto; clarify.
Qed.*)

Lemma instrument_single : forall i t i', instrument_instr i t = [i'] ->
  match i with Assign _ _ => True | Assert_le _ _ => True | _ => False end.
Proof.
  destruct i; clarify; try destruct x; generalize zt_non_zero; destruct zt;
    clarify.
Qed.

Lemma state_sim_inv : forall P1a P1b P2a P2b t li li'
  (Hsim : state_sim (P1a ++ (t, li) :: P1b) (P2a ++ (t, li') :: P2b))
  (Hdistinct : distinct (P2a ++ (t, li') :: P2b)),
  state_sim P1a P2a /\ state_sim P1b P2b /\ li' = instrument li t.
Proof.
  induction P1a; clarify.
  - destruct P2a; clarify.
    + inversion Hsim; clarify; apply Forall2_refl.
    + inversion Hsim; clarify.
      generalize (NoDup_inj(x := fst p) 0 (S (length (map fst P2a))) Hdistinct);
        clarify.
      rewrite map_app in *; simpl in *; rewrite nth_error_split in *; clarify.
  - destruct P2a; clarify.
    + inversion Hsim; clarify.
      assert (nth_error (a :: P1a ++ (fst a, li) :: P1b) (S (length P1a)) =
        Some (fst a, li)) by (simpl; apply nth_error_split).
      exploit Forall2_nth; eauto; intros (? & Hnth & ?).
      generalize (NoDup_inj(x := fst a) 0 (S (length P1a)) Hdistinct);
        clarify.
      erewrite map_nth_error in *; eauto; clarify.
    + inversion Hsim; clarify.
      inversion Hdistinct; clarify.
      exploit IHP1a; eauto; clarify.
      constructor; auto.
Qed.
(*
Opaque minus.

Lemma to_mem_suffix : forall t li G vs lc G' vs'
  (Hmem : to_mem G t li vs = Some (lc, G', vs')), exists vs1, vs = vs1 ++ vs'.
Proof.
  induction li; clarify.
  - exists []; auto.
  - destruct a; clarify; eauto.
    + destruct vs; clarify.
      destruct x0 as ((?, ?), ?); clarify.
      exploit IHli; eauto; clarify.
      setoid_rewrite <- list_cons_plus_assoc; eauto.
    + destruct x0 as ((?, ?), ?); clarify; eauto.
    + destruct x as ((?, ?), ?); clarify; eauto.
    + destruct x as ((?, ?), ?); clarify; eauto.
Qed.

Corollary to_mem_le : forall G t li vs lc G' vs'
  (Hmem : to_mem G t li vs = Some (lc, G', vs')), length vs' <= length vs.
Proof.
  intros; exploit to_mem_suffix; eauto; clarify; rewrite app_length; omega.
Qed.
*)

Lemma hb_check_len : forall C1 C2 z tmp1 tmp2,
  length (hb_check C1 C2 z tmp1 tmp2) = 3 * z.
Proof.
  induction z; clarify.
  rewrite IHz; omega.
Qed.

Lemma max_vc_len : forall src tgt z tmp1 tmp2,
  length (max_vc src tgt z tmp1 tmp2) = 4 * z.
Proof.
  induction z; clarify.
  rewrite IHz; omega.
Qed.

Transparent move.

Lemma load_handler_len : forall t x z,
  length (load_handler t x z) = 3 * z + 3.
Proof.
  unfold load_handler; clarify.
  rewrite app_length, hb_check_len; simpl; omega.
Qed.

Lemma store_handler_len : forall t x z,
  length (store_handler t x z) = 6 * z + 3.
Proof.
  unfold store_handler; clarify.
  repeat rewrite app_length, hb_check_len; simpl; omega.
Qed.

Lemma lock_handler_len : forall t l z,
  length (lock_handler t l z) = 4 * z.
Proof.
  intros; apply max_vc_len.
Qed.

Lemma spawn_handler_len : forall t l z,
  length (spawn_handler t l z) = 4 * z + 3.
Proof.
  unfold spawn_handler; clarify.
  rewrite app_length, max_vc_len; simpl; omega.
Qed.

Lemma unlock_handler_len : forall t u z tmp,
  length (unlock_handler t u z tmp) = 2 * z + 3.
Proof.
  unfold unlock_handler; clarify.
  rewrite app_length, set_vc_len; simpl; omega.
Qed.

Lemma wait_handler_len : forall t u z,
  length (wait_handler t u z) = 4 * z+3 .
Proof.
  unfold wait_handler; clarify.
  rewrite app_length,  max_vc_len; simpl. omega.
Qed.

Lemma hb_check_locs : forall C1 C2 z vs1 vs2 t l,
  In l (map loc_of (mops_hb_check C1 C2 vs1 vs2 z t)) ->
    exists n, n < z /\ (l = (C1, n) \/ l = (C2, n)).
Proof.
  induction z; clarify; destruct vs1; clarify.
  destruct vs2; clarify.
  destruct H as [? | [? | ?]]; eauto.
  destruct (leb n n0); clarify.
  exploit IHz; eauto; intros (n & ?); exists n; clarify.
Qed.  

Lemma hb_check_instr : forall C1 C2 z tmp1 tmp2 i
  (Hi : In i (hb_check C1 C2 z tmp1 tmp2)) l (Haccess : accesses i = Some l),
  exists n, n < z /\ (l = (C1, n) \/ l = (C2, n)).
Proof.
  induction z; clarify.
  destruct Hi as [? | [? | ?]]; clarify; eauto.
  exploit IHz; eauto; intros (n & ?); exists n; clarify.
Qed.  

Lemma max_vc_instr : forall src tgt z tmp1 tmp2 i
  (Hi : In i (max_vc src tgt z tmp1 tmp2)) l (Haccess : accesses i = Some l),
  exists n, n < z /\ (l = (src, n) \/ l = (tgt, n)).
Proof.
  induction z; clarify.
  destruct Hi as [? | [? | [? | [? | ?]]]]; clarify; eauto.
  exploit IHz; eauto; intros (n & ?); exists n; clarify.
Qed.  

Lemma set_vc_instr : forall src tgt z tmp i
  (Hi : In i (set_vc src tgt z tmp)) l (Haccess : accesses i = Some l),
  exists n, n < z /\ (l = (src, n) \/ l = (tgt, n)).
Proof.
  induction z; clarify.
  destruct Hi as [? | [? | ?]]; clarify; eauto.
  exploit IHz; eauto; intros (n & ?); exists n; clarify.
Qed.

Lemma instrument_own : forall li (Hsafe : Forall safe_instr li)
  t i (Hi : In i (instrument li t)) t' (Ht' : t' < zt) n
  (Haccess : accesses i = Some (C + t', n)), t' = t \/
  (exists i', In i' li /\ In i (instrument_instr i' t) /\
   match i' with Spawn u _ | Wait u => t' = u
   | _ => False end).
Proof.
  induction li; clarify.
  inversion Hsafe as [|?? Hsafe' ?]; clarify.
  rewrite in_app in Hi; destruct Hi.
  destruct a; try destruct x; clarify.
  - left.
    repeat rewrite in_app in H; simpl in H.
    destruct H as [H | [[H | H] | [H | H]]]; clarify.
    + exploit Hmetalocs_disjoint_CX; eauto; clarify.
    + exploit hb_check_instr; eauto; intros (? & ? & [? | ?]); clarify.
      * exploit Hmetalocs_disjoint_CW; try apply Ht'; eauto; contradiction.
      * eapply plus_reg_l; eauto.
    + destruct H as [H | H]; clarify.
      * eapply plus_reg_l; eauto.
      * exploit Hmetalocs_disjoint_CR; eauto; contradiction.
    + contradiction Hsafe'1; unfold meta_loc; left; simpl; omega.
    + exploit Hmetalocs_disjoint_CX; eauto; clarify.
  - left.
    repeat rewrite in_app in H; simpl in H.
    destruct H as [H | [[H | [H | [H | H]]] | [H | H]]]; clarify.
    + exploit Hmetalocs_disjoint_CX; eauto; clarify.
    + exploit hb_check_instr; eauto; intros (? & ? & [? | ?]); clarify.
      * exploit Hmetalocs_disjoint_CW; try apply Ht'; eauto; contradiction.
      * eapply plus_reg_l; eauto.
    + exploit hb_check_instr; eauto; intros (? & ? & [? | ?]); clarify.
      * exploit Hmetalocs_disjoint_CR; try apply Ht'; eauto; contradiction.
      * eapply plus_reg_l; eauto.
    + eapply plus_reg_l; eauto.
    + exploit Hmetalocs_disjoint_CW; eauto; contradiction.
    + contradiction Hsafe'1; unfold meta_loc; left; simpl; omega.
    + exploit Hmetalocs_disjoint_CX; eauto; clarify.
  - left; unfold lock_handler in H.
    destruct H; clarify.
    + contradiction Hsafe'1; left; simpl; omega.
    + exploit max_vc_instr; eauto; intros (? & ? & [? | ?]); clarify.
      * exploit Hmetalocs_disjoint_CL; try (apply H4); eauto; clarify.
      * eapply plus_reg_l; eauto.
  - left; unfold unlock_handler in H; repeat rewrite in_app in H.
    destruct H as [[? | ?] | ?]; clarify.
    + exploit set_vc_instr; eauto; intros (? & ? & [? | ?]); clarify.
      * eapply plus_reg_l; eauto.
      * exploit Hmetalocs_disjoint_CL; try (apply H4); eauto; clarify.
    + destruct H as [? | [? | ?]]; clarify; eapply plus_reg_l; eauto.
    + contradiction Hsafe'1; left; simpl; omega.
  - unfold spawn_handler in H; repeat rewrite in_app in H.
    destruct H as [[? | ?] | ?]; clarify.
    +exploit max_vc_instr; eauto; intros (? & ? & [? | ?]); clarify.
      * left. eapply plus_reg_l; eauto.
      * right; eexists; split; eauto; simpl.
        split; [|eapply plus_reg_l; eauto].
        unfold spawn_handler; repeat rewrite in_app; auto.
    + left; destruct H as [? | [? | ?]]; clarify; eapply plus_reg_l; eauto.
   
  - unfold wait_handler in H; repeat rewrite in_app in H.
    destruct H as [? | ?]; clarify.
    +exploit max_vc_instr; eauto; intros (? & ? & [? | ?]); clarify.
     *right; eexists; split; eauto; clarify.
      split; clarify. right. unfold wait_handler. rewrite in_app. clarify.
      eapply plus_reg_l; eauto.
     *left; eapply plus_reg_l; eauto.
    + destruct H as [? | [? | [?|?]]]; clarify.
      * right; eexists; split; eauto; clarify.
        split; clarify. right. unfold wait_handler. rewrite in_app. clarify.
        apply plus_reg_l in H1. clarify.
      * right; eexists; split; eauto; clarify.
        split; clarify. right. unfold wait_handler. rewrite in_app. clarify.
        apply plus_reg_l in H1. clarify.
  - exploit IHli; eauto; clarify.
    right; eauto.
Qed.

Lemma hb_check_instrs : forall C1 C2 z tmp1 tmp2 i,
  In i (hb_check C1 C2 z tmp1 tmp2) -> (exists n, n < z /\
    (i = Load tmp1 (C1, n) \/ i = Load tmp2 (C2, n))) \/
    i = Assert_le (V tmp1) (V tmp2).
Proof.
  induction z; clarify.
  destruct H as [? | [? | ?]]; [left | left |]; clarify; eauto.
  exploit IHz; eauto; intros [(x & ? & [? | ?]) | ?]; clarify; left;
    exists x; clarify.
Qed.  

Lemma max_vc_instrs : forall src tgt z tmp1 tmp2 i,
  In i (max_vc src tgt z tmp1 tmp2) -> (exists n, n < z /\
    (i = Load tmp1 (src, n) \/ i = Load tmp2 (tgt, n) \/
     i = Store (tgt, n) (V tmp2))) \/ i = Assign tmp2 (Max (V tmp1) (V tmp2)).
Proof.
  induction z; clarify.
  destruct H as [? | [? | [? | [? | ?]]]]; clarify;
    try solve [left; repeat eexists; [|clarify]; auto].
  exploit IHz; eauto; intros [(x & ? & [? | ?]) | ?]; clarify; left;
    exists x; clarify.
Qed.  

Lemma set_vc_instrs : forall src tgt z tmp i,
  In i (set_vc src tgt z tmp) -> exists n, n < z /\
    (i = Load tmp (src, n) \/ i = Store (tgt, n) (V tmp)).
Proof.
  induction z; clarify.
  destruct H as [? | [? | ?]]; clarify; eauto.
  exploit IHz; eauto; clarify; eauto.
Qed.

Lemma spawn_in_handler : forall u li i t,
  In (Spawn u li) (instrument_instr i t) -> exists li', i = Spawn u li' /\
    li = instrument li' u.
Proof.
  destruct i; clarify.
  - destruct x; clarify.
    repeat rewrite in_app in H; destruct H as [[? | ?] | ?]; clarify.
    exploit hb_check_instrs; eauto; clarify.
  - destruct x; clarify.
    repeat rewrite in_app in H; destruct H as [[? | [? | ?]] | ?]; clarify;
      exploit hb_check_instrs; eauto; clarify.
  - exploit max_vc_instrs; eauto; clarify.
  - repeat setoid_rewrite in_app in H.
    destruct H as [[? | ?] | ?]; clarify.
    exploit set_vc_instrs; eauto; clarify.
  - repeat setoid_rewrite in_app in H.
    destruct H as [[? | ?] | ?]; clarify.
    + exploit max_vc_instrs; eauto; clarify.
    + inversion H.
      do 2 eexists; eauto.
  -repeat setoid_rewrite in_app in H.
   destruct H as [?|?]; clarify.
   exploit max_vc_instrs; eauto; clarify.
Qed.

Lemma spawn_in_instrument : forall u li t l, In (Spawn u li) (instrument l t) ->
  exists li', In (Spawn u li') l /\ li = instrument li' u.
Proof.
  induction l; clarify.
  rewrite in_app in *; destruct H; clarify; eauto.
  exploit spawn_in_handler; eauto; clarify; eauto.
Qed.

Lemma safe_instrs : forall l, (fix list_safe l := match l with [] => True |
  i :: rest => safe_instr i /\ list_safe rest end) l <->
  Forall safe_instr l.
Proof.
  induction l; split; clarify; rewrite IHl in *; clarify.
  inversion H; clarify.
Qed.

Lemma spawn_instrumented : forall P P1 (Hsim : state_sim P P1)
  (Hsafe : safe_locs P)
  G lo lc P' G' (Hsteps : exec_star (Some P1) G lo lc (Some P') G')
  t li (Ht : In (t, li) P') u li' (Hspawn : In (Spawn u li') li),
  exists li0, li' = instrument li0 u /\ Forall safe_instr li0.
Proof.
  intros ??????????; remember (Some P1) as Pa; remember (Some P') as Pb;
    generalize dependent P'; generalize dependent P1.
  rewrite exec_rev in Hsteps; induction Hsteps; clarify.
  - generalize (in_split _ _ Ht); clarify.
    exploit Forall2_app_inv_r; eauto; intros (? & ? & ? & Hsim2 & ?).
    inversion Hsim2; clarify.
    exploit spawn_in_instrument; eauto; clarify.
    setoid_rewrite Forall_app in Hsafe; clarify.
    inversion Hsafe2 as [|?? Hl]; clarify.
    rewrite Forall_forall in Hl; exploit Hl; eauto; clarify.
    rewrite safe_instrs in *; eauto.
  - exploit exec_result; eauto.
    intros (P'a & i1 & li1 & P'b & v & ? & Hresult); subst.
    destruct (instr_result t i1 (G' t) v)
      as [((((t', ?), ?), ?), ?)|] eqn: Hi1; clarify.
    rewrite in_app in Ht; clarify; rewrite in_app in Ht.
    specialize (IHHsteps _ Hsim eq_refl _ eq_refl).
    setoid_rewrite in_app in IHHsteps; simpl in IHHsteps.
    destruct Ht as [? | [? | [? | ?]]]; eauto.
    { inversion H; subst; exploit IHHsteps; eauto; clarify. }
    destruct t'; clarify.
    destruct i1; clarify.
    exploit IHHsteps; clarify.
    exploit spawn_in_instrument; eauto; clarify.
    rewrite Forall_forall in H2; exploit H2; eauto; clarify.
    rewrite safe_instrs in *; eauto.
Qed.

Lemma step_into_instrument : forall P P1 (Hsim : state_sim P P1)
  (Hsafe : safe_locs P)
  G1 lo lc P1' G1' (Hsteps : exec_star (Some P1) G1 lo lc (Some P1') G1')
  t i li (Ht : In (t, i :: li) P1') (Hdistinct : distinct P1),
  exists P2 lo2 lc2 G2 n' i' li' rest lo2' lc2', lc = lc2 ++ lc2' /\
    exec_star (Some P1) G1 lo2 lc2 (Some P2) G2 /\
    In (t, instrument_instr i' t ++ instrument rest t) P2 /\
    skipn n' (instrument_instr i' t) = i :: li' /\
    li = li' ++ instrument rest t /\ safe_instr i' /\ Forall safe_instr rest /\
    exec_star (Some P2) G2 lo2' lc2' (Some P1') G1'.
Proof.
  intros ???????????; remember (Some P1) as Pa; remember (Some P1') as Pb;
    generalize dependent P1'; generalize dependent P1.
  rewrite exec_rev in Hsteps; induction Hsteps; clarify.
  - exploit in_split; eauto; clarify.
    exploit Forall2_app_inv_r; eauto; intros (? & ? & ? & Hsim2 & ?).
    inversion Hsim2 as [|(t', li')]; clarify.
    destruct li'; clarify.
    destruct (instrument_instr i0 t) eqn: Hi0;
      [exploit instrument_nonnil; eauto|]; clarify.
    repeat eexists; try apply exec_refl; auto.
    + rewrite in_app; setoid_rewrite Hi0; simpl; eauto.
    + instantiate (1 := 0); eauto.
    + setoid_rewrite Forall_app in Hsafe; clarify.
      inversion Hsafe2 as [|?? Hi]; inversion Hi; clarify.
    + setoid_rewrite Forall_app in Hsafe; clarify.
      inversion Hsafe2 as [|?? Hi]; inversion Hi; clarify.
  - specialize (IHHsteps _ Hsim eq_refl _ eq_refl).
    exploit exec_result; eauto.
    intros (P'a & i1 & li1 & P'b & v & ? & Hresult); subst.
    destruct (instr_result t0 i1 (G' t0) v)
      as [((((t', ?), ?), ?), ?)|] eqn: Hi1; clarify.
    rewrite in_app in Ht; clarify; rewrite in_app in Ht.
    setoid_rewrite in_app in IHHsteps; simpl in IHHsteps.
    destruct Ht as [? | [? | [? | ?]]].
    + exploit IHHsteps; eauto; clarify; do 11 eexists.
      { rewrite <- app_assoc; eauto. }
      repeat split; eauto; eapply exec_step_inv; eauto.
    + clarify.
      exploit IHHsteps; eauto; intros (? & ? & ? & ? & n' & i' & li' & rest & ? 
        & ? & ? & ? & ? & Hli' & Hli & ? & Hrest & ?); clarify.
      destruct li'; clarify.
      * destruct rest; clarify.
        inversion Hrest; clarify.
        do 11 eexists.
        { instantiate (1 := []); rewrite app_nil_r; eauto. }
        repeat eexists.
        { eapply exec_step_inv; try apply Hexec'; eauto.
          eapply exec_star_trans; eauto. }
        { rewrite Hli, in_app; clarify. }
        { instantiate (2 := 0); simpl.
          instantiate (1 := tl (instrument_instr i0 t));
            destruct (instrument_instr i0 t) eqn: Hi0; clarify.
          exploit instrument_nonnil; eauto; clarify. }
        { destruct (instrument_instr i0 t) eqn: Hi0; clarify.
          exploit instrument_nonnil; eauto; clarify. }
        { auto. }
        { auto. }
        { apply exec_refl. }
      * do 11 eexists; [|split; eauto; repeat split; eauto].
        { rewrite <- app_assoc; eauto. }
        { instantiate (1 := n' + 1); rewrite <- skipn_skipn, Hli'; auto. }
        { eapply exec_step_inv; eauto. }
    + destruct t'; clarify.
      destruct i1; clarify.
      rewrite <- exec_rev in *.
      exploit spawn_instrumented; eauto.
      { rewrite in_app; clarify. }
      { clarify. }
      intros ([|?] & Hli & Hsafe'); clarify.
      inversion Hsafe'; clarify.
      repeat eexists.
      * eapply exec_step_inv; eauto.
        simpl; rewrite app_nil_r; auto.
      * rewrite in_app, Hli; simpl; eauto.
      * instantiate (2 := 0); simpl.
        instantiate (1 := tl (instrument_instr i0 t));
          destruct (instrument_instr i0 t) eqn: Hi0; clarify.
        exploit instrument_nonnil; eauto; clarify.
      * destruct (instrument_instr i0 t) eqn: Hi0; clarify.
        exploit instrument_nonnil; eauto; clarify.
      * auto.
      * auto.
      * apply exec_refl.
    + exploit IHHsteps; eauto; clarify; do 11 eexists.
      { rewrite <- app_assoc; eauto. }
      repeat split; eauto; eapply exec_step_inv; eauto.
Qed.

Lemma instrument_thread' : forall P (Hsafe : safe_locs P) P1
  (Hsim : state_sim P P1) (Hdistinct : distinct P1)
  P1' G1 lo lc G1' (Hroot : exec_star (Some P1) G1 lo lc (Some P1') G1')
  t o c t' n P1'' G' (Hstep : exec P1' G1' t o (Some c) P1'' G')
  (Hloc : loc_of c = (C + t', n)) (Ht' : t' < zt),
  t' = t \/ exists P2 lo2 lc2 G2 i' n' rest lo2' lc2',
    exec_star (Some P1) G1 lo2 lc2 (Some P2) G2 /\
    In (t, instrument_instr i' t ++ instrument rest t) P2 /\
    In (t, skipn n' (instrument_instr i' t) ++ instrument rest t) P1' /\
    n' < length (instrument_instr i' t) /\
    exec_star (Some P2) G2 lo2' lc2' (Some P1') G1' /\
    match i' with Spawn u _ | Wait u => t' = u | _ => False end.
Proof.
  intros.
  exploit exec_result; eauto; intros (P1a & i & li & P1b & v & ? & Hresult);
    subst.
  exploit step_into_instrument; eauto.
  { rewrite in_app; clarify. }
  intros (? & ? & ? & ? & n' & i' & ? & ? & ? & ? & ? & ? & ? & Hi' & ?);
    clarify.
  assert (In i (instrument [i'] t)) as Hi.
  { simpl; rewrite app_nil_r; eapply skipn_in.
    eapply nth_error_in; setoid_rewrite Hi'.
    instantiate (1 := 0); simpl; eauto. }
  exploit distinct_steps; eauto; intro.
  exploit instrument_own; try apply Hi; eauto.
  { rewrite <- exec_accesses; try apply Hstep; clarify; eauto.
    rewrite in_app; clarify. }
  intros [? | (i1 & ?)]; clarify.
  right; exists x; repeat eexists; eauto.
  - setoid_rewrite Hi'; rewrite in_app; clarify.
  - destruct (le_lt_dec (length (instrument_instr i1 t)) n'); auto.
    rewrite skipn_all in *; clarify.
Qed.

Definition spawns t := instr_rect'' _ _ (fun _ => 0)
  (fun u _ r => if eq_dec u t then S r else r) 0 (fun _ _ r1 r2 => r1 + r2).

Fixpoint spawns_list t li :=
  match li with
  | [] => 0
  | i :: rest => spawns t i + spawns_list t rest
  end.

Lemma spawns_list_def : forall t li, instr_list_rect _ _ (fun _ => 0)
  (fun u _ r => if eq_dec u t then S r else r) 0 (fun _ _ r1 r2 => r1 + r2) li =
   spawns_list t li.
Proof. induction li; clarify. Qed.

Fixpoint spawn_count t (P : state) :=
  match P with
  | [] => 0
  | (_, li) :: rest => spawns_list t li + spawn_count t rest
  end.

Definition safe_spawns P := forall t, spawn_count t P <= 1 /\
  (forall li, In (t, li) P -> spawn_count t P = 0).

Lemma spawn_count_app : forall t P1 P2, spawn_count t (P1 ++ P2) =
  spawn_count t P1 + spawn_count t P2.
Proof.
  induction P1; clarify.
  destruct a; clarify.
  rewrite IHP1; omega.
Qed.

Lemma safe_spawns_step : forall P (Hspawns : safe_spawns P)
  G t o c P' G' (Hstep : exec P G t o c (Some P') G'), safe_spawns P'.
Proof.
  intros; exploit exec_result; eauto; intros (? & i & ? & ? & v & ?).
  destruct (instr_result t i (G t) v) as [((((?, ?), ?), ?), ?)|] eqn: Hi;
    clarify.
  intro t'; specialize (Hspawns t'); rewrite spawn_count_app in *; clarify.
  destruct o0 as [(u, li)|]; clarify.
  destruct i; clarify.
  generalize (Hspawns2 li).
  unfold spawns in *; simpl in *; rewrite (spawns_list_def t') in *.
  destruct (eq_dec u t'); [split; intros; omega|].
  split; [omega | intros ? Hin].
  destruct (eq_dec t' t).
  - subst; exploit Hspawns2.
    { rewrite in_app; clarify. }
    omega.
  - rewrite <- (Hspawns2 li0); [omega|].
    rewrite in_app in *; simpl in *.
    destruct Hin as [? | [? | [? | ?]]]; clarify.
  - assert (spawns t' i = 0) as Hz by (destruct i; clarify); rewrite Hz in *;
      clarify.
    generalize (Hspawns2 li); rewrite in_app in *; clarify.
    eapply Hspawns2; rewrite in_app; clarify.
Qed.

Lemma spawns_list_app : forall t P1 P2, spawns_list t (P1 ++ P2) =
  spawns_list t P1 + spawns_list t P2.
Proof.
  induction P1; clarify.
  rewrite IHP1; omega.
Qed.

(*
Lemma own_thread : forall t P1 G lo lc P1' G' (Ht : t < zt)
  (Hsteps : exec_star_minus t (Some P1) G lo lc P1' G')
  P (Hsafe : safe_locs P) P0 (Hsim : state_sim P P0)
  (Hdistinct : distinct P0) G0 lo0 lc0
  (Hroot : exec_star (Some P0) G0 lo0 lc0 (Some P1) G)
  li (Hlive : In (t, li) P1) (Hli : li <> []) (Hspawns : safe_spawns P1),
  Forall (fun c => fst (loc_of c) <> C' + t) lc.
Proof.
  intros ?????????; remember (Some P1) as Pa; generalize dependent P1;
    induction Hsteps; clarify.
  exploit exec_result; eauto.
  intros (Pa & i & li' & Pb & v & ?); clarify.
  rewrite Forall_app; split.
  - rewrite Forall_forall; intros c' ? ?.
    destruct c; clarify.
    destruct (loc_of c') eqn: Hloc; clarify.
    exploit instrument_thread'; eauto.
    intros [? | (? & ? & ? & ? & i' & n' & ? & ? & ? & ? & ? & Ht' & ?)];
      clarify.
    exploit distinct_steps; eauto; intro.
    exploit distinct_steps; eauto; intro.
    exploit in_split; eauto; clarify; exploit distinct_thread; eauto;
      intros (? & ? & Hli'); subst.
    destruct i'; clarify.
    + specialize (Hspawns t0); clarify.
      exploit Hspawns2; eauto.
      rewrite H4, spawn_count_app; simpl.
      rewrite skipn_app; repeat rewrite spawns_list_app.
      rewrite app_length in *; simpl in *.
      destruct (n' - length (spawn_handler t' t0 zt)) eqn: Hminus;
        [clarify | omega].
      unfold spawns in *; simpl in *; clarify; omega.
    + destruct n'; clarify.
      rewrite <- skipn_app' in Ht'; [|omega].
      exploit step_instr; try apply Ht'; eauto.
      intros (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Hpre & Hwait & Hrest & ?);
        clarify.
      exploit exec_other_threads; try apply Hpre; eauto; intro.
      exploit in_split; eauto; clarify.
      exploit distinct_steps; try (eapply exec_minus_exec; eauto); auto; intro.
      inversion Hwait; subst; exploit distinct_thread; eauto 2;
        intros (? & ? & Hi); inversion Hi; subst; clear Hi.
      exploit distinct_step; eauto; intro.
      exploit exec_mono; try apply Hrest; eauto.
      { instantiate (1 := []); rewrite in_app in Hdone; rewrite in_app; clarify.
      }
      clarify; rewrite skipn_nil in *; clarify.
  - destruct P'; [|inversion Hsteps]; clarify.
    destruct (instr_result t' i (G t') v)
      as [((((th, ?), ?), ?), ?)|] eqn: Hresult; clarify.
    generalize (safe_spawns_step Hspawns Hexec); intro.
    destruct th; simpl in *.
    + destruct i; clarify.
      eapply IHHsteps; eauto.
      * eapply exec_step_inv; eauto.
      * eapply exec_other_thread; eauto.
    + eapply IHHsteps; eauto.
      * eapply exec_step_inv; eauto.
      * eapply exec_other_thread; eauto.
Qed.

Lemma safe_spawns_steps : forall P (Hspawns : safe_spawns P)
  G o c P' G' (Hsteps : exec_star (Some P) G o c (Some P') G'), safe_spawns P'.
Proof.
  intros; remember (Some P) as P1; remember (Some P') as P2;
    generalize dependent P'; generalize dependent P;
    induction Hsteps; clarify.
  destruct P'; [|inversion Hsteps].
  apply (IHHsteps s); auto.
  eapply safe_spawns_step; eauto.
Qed.
*)
Lemma instrument_own_thread : forall t (Ht : t < zt) P G lo lc P1 G1
  (Hsteps : exec_star (Some P) G lo lc (Some P1) G1)
  P0 (Hsafe : safe_locs P0) P0' (Hdistinct : distinct P0')
  (Hspawns : safe_spawns P0') (Hsim : state_sim P0 P0') G0 lo0 lc0
  (Hroot : exec_star (Some P0') G0 lo0 lc0 (Some P) G)
  li (Hin : In (t, li) P) li1 (Hin : In (t, li1) P1) (Hlive : li1 <> []),
  Forall (fun c => fst (loc_of c) <> C + t)
    (filter (fun x => negb (beq (thread_of x) t)) lc).
Proof.
  admit.
(*  intros until li; remember (Some P) as Pa; remember (Some P1) as Pb;
    generalize dependent P1; generalize dependent P;
    rewrite exec_rev in Hsteps; induction Hsteps; clarify.
  specialize (IHHsteps _ eq_refl _ eq_refl); clarify.
  rewrite <- exec_rev in Hsteps.
  exploit distinct_steps; eauto; intro.
  exploit exec_keep; eauto; clarify.
  specialize (IHHsteps (skipn x li)); use IHHsteps.
  exploit distinct_steps; eauto; intro.
  destruct (eq_dec t0 t).
  - subst; exploit exec_ops; eauto; intro.
    exploit step_thread; eauto; intros (? & ? & Heq & ?).
    rewrite Heq in IHHsteps; use IHHsteps.
    rewrite filter_app, Forall_app; clarify.
    rewrite filter_negb_none; auto.
  - exploit exec_step_m; eauto.
    { apply exec_refl_m. }
    repeat rewrite app_nil_r; intro.
    exploit exec_other_thread; eauto; intro.
    exploit distinct_step; eauto; intro.
    exploit distinct_in; [eauto | apply Hin0 | eauto | clarify].
    rewrite filter_app, Forall_app; clarify.
    exploit own_thread; eauto.
    { eapply exec_star_trans; eauto. }
    { eapply safe_spawns_steps; eauto.
      eapply exec_star_trans; eauto. }
    intro; apply Forall_filter; auto.*)
Qed.

(* up *)
Lemma C_meta : forall t (Ht : t < zt) o, meta_loc (C + t, o).
Proof. intros; unfold meta_loc; simpl; omega. Qed. 

Definition good_lock x := state_forall (fun i =>
  match i with Load _ p | Store p _ => p <> x | _ => True end).

Lemma good_lock_ops : forall x P G lo lc P' G' (Hlock : good_lock (x, 0) P)
  (Hsteps : exec_star (Some P) G lo lc P' G'),
  Forall (fun a => loc_of a = (x, 0) -> lock_op x a) lc.
Proof.
  intros.
  remember (Some P) as P1; generalize dependent P; induction Hsteps; clarify.
  rewrite Forall_app; split.
  - rewrite Forall_forall; intros.
    inversion Hexec; clarify; unfold lock_op; eauto;
      setoid_rewrite Forall_app in Hlock; clarify;
      inversion Hlock2 as [|?? Hi]; inversion Hi; unfold instr_forall in *;
      clarify.
  - clarify.
    destruct P'; [|inversion Hsteps; clarify].
    exploit forall_step; eauto.
Qed.

Lemma rel_inv : forall t x P G lo lc P' G' (Hdistinct : distinct P)
  (Hsteps : exec_star (Some P) G lo lc P' G') li (Hin : In (t, li) P)
  (Hrel : In (Rel t x) lc), exists li1 li2, li = li1 ++ Unlock x :: li2 /\
  match P' with Some s' => exists n, In (t, skipn n li2) s' | None => True end.
Proof.
  intros; rewrite exec_rev in Hsteps; remember (Some P) as P0;
    generalize dependent P; induction Hsteps; clarify.
  rewrite <- exec_rev in Hsteps.
  rewrite in_app in Hrel; destruct Hrel.
  - clarify.
    specialize (IHHsteps P0); clarify.
    repeat eexists; eauto.
    destruct P''; clarify.
    exploit distinct_steps; eauto; intro.
    exploit exec_keep.
    + eauto.
    + eapply exec_step, exec_refl; eauto.
    + eauto.
    + clarify; rewrite skipn_skipn in *; eauto.
  - inversion Hexec'; clarify.
    inversion H; clarify.
    exploit exec_mono; eauto.
    { rewrite in_app; clarify. }
    intros (n & Hn).
    exists (firstn n li), rest.
    rewrite Hn, firstn_skipn; clarify.
    exists 0; rewrite in_app; clarify.
Qed.  

Lemma critical_section : forall x P G lo lc P' G' (Hlock : good_lock (x, 0) P)
  (Hsteps : exec_star (Some P) G lo lc (Some P') G')
  (Hdistinct : distinct P) m (Hinit : initialized m (x, 0))
  (Hcon : consistent (m ++ lc))
  t li (HP : In (t, Lock x :: li) P) n (HP' : In (t, skipn n li) P'),
  In (Unlock x) (firstn n li) \/ can_read (m ++ lc) (x, 0) (S t).
Proof.
  intros.
  exploit step_instr; eauto.
  intros (P1 & G1 & lo1 & lc1 & o & c & P1' & G1' & lo2 & lc2 & Hpre & Hacq &
    Hrest & ?); clarify.
  exploit exec_other_threads; try apply Hpre; eauto; intro.
  exploit distinct_steps; [|eapply exec_minus_exec|]; eauto; intro.
  exploit in_split; eauto; intros (Pa & Pb & ?).
  inversion Hacq; subst; exploit distinct_thread; eauto; clarify.
  rewrite split_app, app_assoc in Hcon; exploit consistent_app_SC; eauto.
  rewrite app_assoc; intro.
  exploit can_read_arwritten; eauto; intro Hlocked.
  exploit lock_hold; try apply Hcon; rewrite <- app_assoc in Hlocked; eauto.
  { rewrite app_assoc; apply init_step; clarify.
    apply init_steps; auto.
    eapply prog_steps, exec_minus_exec; eauto. }
  { eapply prog_steps; eauto. }
  { eapply good_lock_ops, Hrest.
    eapply forall_steps; eauto.
    eapply exec_step_inv; try eapply exec_minus_exec; eauto. }
  repeat rewrite <- app_assoc; clarify.
  exploit distinct_step; eauto; intro.
  left; exploit rel_inv; eauto.
  { rewrite in_app; clarify. }
  intros (li1 & li2 & ? & n' & HP'2); clarify.
  generalize (in_split _ _ HP'), (in_split _ _ HP'2); clarify.
  exploit distinct_steps; eauto; intro.
  exploit distinct_thread; eauto; intros (? & ? & Heq); subst.
  rewrite firstn_app.
  destruct (n - length li1) eqn: Hminus; [|rewrite in_app; clarify].
  assert (length (skipn n' li2) = length (skipn n (li1 ++ Unlock x :: li2)))
    by (rewrite Heq; auto).
  repeat rewrite skipn_length in *; rewrite app_length in *; clarify; omega.
Qed.  

(* up *)
Lemma X_meta : forall v (Ht : v < zv) o, meta_loc (X + v, o).
Proof. intros; unfold meta_loc; simpl; omega. Qed.
(*
Lemma instrument_hd : forall i t, let i' := hd (Lock 0) (instrument_instr i t)
  in match i' with
  | Assign _ _ | Wait _ | Assert_le _ _ => i' = i
  | Load _ (x, _) => x = C + t
  | Lock l => i' = i \/ exists v, accesses i = Some v /\ l = X + fst v /\
      (safe_instr i -> fst v < zv)
  | _ => False
  end.
Proof.
  destruct i; try (destruct x); clarify; eauto; destruct zt; clarify.
  - right; repeat eexists; clarify.
  - right; repeat eexists; clarify.
Qed.

Corollary instrument_access : forall i t i' li rest v
  (Hli : i :: li = instrument_instr i' t ++ rest)
  (Haccess : accesses i = Some v), (exists o, v = (C + t, o)) \/
    snd v = 0 /\ (i = Lock (fst v) /\ i' = i \/
    exists v', accesses i' = Some v' /\ fst v = X + fst v' /\
      (safe_instr i' -> fst v' < zv)).
Proof.
  intros.
  generalize (instrument_hd i' t); intro Hcases.
  generalize (instrument_nonnil i' t); destruct (instrument_instr i' t);
    clarify.
  destruct i0; try destruct v; clarify; eauto.
  right; clarify; eauto.
Qed.
*)
Lemma R_meta : forall v (Ht : v < zv) o, meta_loc (R + v, o).
Proof. intros; unfold meta_loc; simpl; omega. Qed.

Lemma W_meta : forall v (Ht : v < zv) o, meta_loc (W + v, o).
Proof. intros; unfold meta_loc; simpl; omega. Qed.
(*
Lemma v_not_C : forall t (Ht : t < zt) (o1 : nat) v (Hv : ~meta_loc v)
  (Hv2 : fst v < zv) (Haccess : Some (C + t, o1) = Some v \/
    (exists o, Some (C + t, o1) = Some (R + fst v, o)) \/
    (exists o, Some (C + t, o1) = Some (W + fst v, o))), False.
Proof.
  intros; destruct Haccess as [? | [? | ?]]; clarify.
  - contradiction Hv; apply C_meta; auto.
  - eapply Hmetalocs_disjoint_CR; eauto.
  - eapply Hmetalocs_disjoint_CW; eauto.
Qed.

Lemma v_not_X : forall v' (Hv' : v' < zv) (o1 : nat) v (Hv : ~meta_loc v)
  (Hv2 : fst v < zv) (Haccess : Some (X + v', o1) = Some v \/
    (exists o, Some (X + v', o1) = Some (R + fst v, o)) \/
    (exists o, Some (X + v', o1) = Some (W + fst v, o))), False.
Proof.
  intros; destruct Haccess as [? | [? | ?]]; clarify.
  - contradiction Hv; apply X_meta; auto.
  - eapply Hmetalocs_disjoint_RX; try (symmetry; apply H1); eauto.
  - eapply Hmetalocs_disjoint_WX; try (symmetry; apply H1); eauto.
Qed.

Lemma v_W : forall v' (Hv' : v' < zv) (o1 : nat) v (Hv : ~meta_loc v)
  (Hv2 : fst v < zv) (Haccess : Some (W + v', o1) = Some v \/
    (exists o, Some (W + v', o1) = Some (R + fst v, o)) \/
    (exists o, Some (W + v', o1) = Some (W + fst v, o))), v' = fst v.
Proof.
  intros; destruct Haccess as [? | [? | ?]]; clarify.
  - contradiction Hv; apply W_meta; auto.
  - exploit Hmetalocs_disjoint_WR; try apply H1; auto; contradiction.
  - eapply plus_reg_l; eauto.
Qed.
*)
Lemma unlock_last : forall i t n l rest, skipn n (instrument_instr i t) =
  Unlock l :: rest -> rest = [].
Proof.
  intros.
  assert (nth_error (skipn n (instrument_instr i t)) 0 = Some (Unlock l))
    by clarsimp.
  rewrite skipn_nth in *; clarify.
  destruct i; try destruct x; clarsimp.
  - destruct n; clarify.
    exploit nth_error_app'; eauto; intros [? | ?]; clarify.
    + exploit nth_error_in; eauto; intro.
      exploit hb_check_instrs; eauto; clarify.
    + destruct (n - length (hb_check (W + v) (C + t) zt tmp1 tmp2))
        eqn: Hminus; clarify.
      destruct n1; clarify.
      rewrite nth_error_two in *; clarify.
      rewrite skipn_app, skipn_all, Hminus in H; clarify.
  - destruct n; clarify.
    exploit nth_error_app'; eauto; intros [? | ?]; clarify.
    + exploit nth_error_in; eauto; intro.
      exploit hb_check_instrs; eauto; clarify.
    + exploit nth_error_app'; eauto; intros [? | ?]; clarify.
      * exploit nth_error_in; eauto; intro.
        exploit hb_check_instrs; eauto; clarify.
      * destruct (n - length (hb_check (W + v) (C + t) zt tmp1 tmp2) -
          length (hb_check (R + v) (C + t) zt tmp1 tmp2)) eqn: Hminus;
          clarify.
        destruct n1; clarify.
        rewrite nth_error_two in *; clarify.
        rewrite skipn_app, skipn_all, skipn_app, skipn_all, Hminus in H;
          clarify.
  - destruct n; clarify.
    exploit nth_error_in; eauto; intro.
    exploit max_vc_instrs; eauto; clarify.
  - unfold unlock_handler in *; rewrite <- app_assoc in *.
    exploit nth_error_app'; eauto; intros [? | ?]; clarify.
    + exploit nth_error_in; eauto; intro.
      exploit set_vc_instrs; eauto; clarify.
    + destruct (n - length (set_vc (C + t) (L + m) zt tmp1)) eqn: Hminus;
        clarify.
      destruct n0; clarify.
      rewrite nth_error_two in *; clarify.
      rewrite skipn_app, skipn_all, Hminus in H; clarify.
      rewrite app_length, Nat.sub_add_distr, Hminus in H; clarify.
  - unfold spawn_handler in *; rewrite <- app_assoc in *.
    exploit nth_error_app'; eauto; intros [? | ?]; clarify.
    + exploit nth_error_in; eauto; intro.
      exploit max_vc_instrs; eauto; clarify.
    + destruct (n - length (max_vc (C + t) (C + t0) zt tmp1 tmp2))
        eqn: Hminus; clarify.
      destruct n0; clarify.
      rewrite nth_error_two in *; clarify.
  - destruct n; clarify.
    unfold wait_handler in *; exploit nth_error_app'; eauto; intros [? | ?];
      clarify.
    + exploit nth_error_in; eauto; intro.
      exploit max_vc_instrs; eauto; clarify.
    + destruct (n - length (max_vc (C + t0) (C + t) zt tmp1 tmp2))
        eqn: Hminus; clarify.
      rewrite nth_error_two in *; clarify.
Qed.      

Lemma lock_first : forall i t n l rest, skipn n (instrument_instr i t) =
  Lock l :: rest -> n = 0.
Proof.
  intros.
  assert (nth_error (skipn n (instrument_instr i t)) 0 = Some (Lock l))
    by clarsimp.
  rewrite skipn_nth in *; clarify.
  destruct i; try destruct x; clarsimp.
  - destruct n; clarify.
    rewrite nth_error_app in *;
      destruct (lt_dec n (length (hb_check (W + v) (C + t) zt tmp1 tmp2))).
    + exploit nth_error_in; eauto; intro.
      exploit hb_check_instrs; eauto; clarify.
    + destruct (n - length (hb_check (W + v) (C + t) zt tmp1 tmp2))
        eqn: Hminus; clarify.
      destruct n2; clarify.
      destruct n2; clarsimp.
  - destruct n; clarify.
    repeat rewrite nth_error_app in *;
      destruct (lt_dec n (length (hb_check (W + v) (C + t) zt tmp1 tmp2)));
      [|destruct (lt_dec (n - length (hb_check (W + v) (C + t) zt tmp1 tmp2))
             (length (hb_check (R + v) (C + t) zt tmp1 tmp2)))].
    + exploit nth_error_in; eauto; intro.
      exploit hb_check_instrs; eauto; clarify.
    + exploit nth_error_in; eauto; intro.
      exploit hb_check_instrs; eauto; clarify.
    + destruct (n - length (hb_check (W + v) (C + t) zt tmp1 tmp2) -
        length (hb_check (R + v) (C + t) zt tmp1 tmp2)) eqn: Hminus; clarify.
      destruct n3; clarify.
      destruct n3; clarsimp.
  - destruct n; clarify.
    exploit nth_error_in; eauto; intro.
    exploit max_vc_instrs; eauto; clarify.
  - unfold unlock_handler in *; rewrite <- app_assoc in *.
    repeat rewrite nth_error_app in *;
      destruct (lt_dec n (length (set_vc (C + t) (L + m) zt tmp1 )));
      [|destruct (lt_dec (n - length (set_vc (C + t) (L + m) zt tmp1))
             (length (inc_vc t (C + t) tmp1)))].
    + exploit nth_error_in; eauto; intro.
      exploit set_vc_instrs; eauto; clarify.
    + destruct (n - length (set_vc (C + t) (L + m) zt tmp1)); clarify.
      destruct n1; clarsimp.
    + clarsimp.
  - unfold spawn_handler in *; rewrite <- app_assoc in *.
    repeat rewrite nth_error_app in *;
      destruct (lt_dec n (length (max_vc (C + t) (C + t0) zt tmp1 tmp2)));
      [|destruct (lt_dec (n - length (max_vc (C + t) (C + t0) zt tmp1 tmp2))
             (length (inc_vc t (C + t) tmp1)))].
    + exploit nth_error_in; eauto; intro.
      exploit max_vc_instrs; eauto; clarify.
    + destruct (n - length (max_vc (C + t) (C + t0) zt tmp1 tmp2)); clarify.
      destruct n1; clarsimp.
    + clarsimp.
  - destruct n; clarify.
    exploit nth_error_in; eauto; intro.
    unfold wait_handler in *; rewrite in_app in H1; destruct H1 as [?|[?|[?|?]]]; clarify.
    exploit max_vc_instrs; eauto; clarify.
Qed.  

Lemma L_meta : forall l (Ht : l < zl) o, meta_loc (L + l, o).
Proof. intros; unfold meta_loc; simpl; omega. Qed.
(*
Lemma v_not_L : forall l (Hl : l < zl) (o1 : nat) v (Hv : ~meta_loc v)
  (Hv2 : fst v < zv) (Haccess : Some (L + l, o1) = Some v \/
    (exists o, Some (L + l, o1) = Some (R + fst v, o)) \/
    (exists o, Some (L + l, o1) = Some (W + fst v, o))), False.
Proof.
  intros; destruct Haccess as [? | [? | ?]]; clarify.
  - contradiction Hv; apply L_meta; auto.
  - eapply Hmetalocs_disjoint_LR; eauto.
  - eapply Hmetalocs_disjoint_LW; eauto.
Qed.
*)
Definition bounded_instr := instr_rect'' _ _ (fun _ => True)
  (fun u li r => u < zt /\ r) True (fun _ _ r1 r2 => r1 /\ r2).

Definition bounded_threads (P : state) := Forall (fun e => fst e < zt /\
  Forall bounded_instr (snd e)) P.

Lemma bounded_spawn : forall u li, bounded_instr (Spawn u li) <->
  u < zt /\ Forall bounded_instr li.
Proof.
  unfold bounded_instr; induction li; split; clarify.
  - constructor; auto.
    apply IHli; auto.
  - inversion H2; clarify.
    apply IHli; auto.
Qed.

Lemma bounded_step : forall P (Hbounded : bounded_threads P)
  G t o c P' G' (Hstep : exec P G t o c (Some P') G'), bounded_threads P'.
Proof.
  intros; inversion Hstep; clarify; unfold bounded_threads in *;
    rewrite Forall_app in *; clarify; inversion Hbounded2 as [|?? [? Hbound]];
    inversion Hbound; clarify.
  rewrite bounded_spawn in *.
  inversion Hbound; repeat constructor; clarify.
Qed.

Corollary bounded_steps : forall P (Hbounded : bounded_threads P)
  G o c P' G' (Hsteps : exec_star (Some P) G o c (Some P') G'),
  bounded_threads P'.
Proof.
  intros; remember (Some P) as P1; remember (Some P') as P2;
    generalize dependent P'; generalize dependent P; induction Hsteps; clarify.
  destruct P'; [|inversion Hsteps; clarify].
  exploit bounded_step; eauto.
Qed.

Lemma no_spawn_bounded : forall l (Hout : Forall (fun i =>
  match i with Spawn _ _ => False | _ => True end) l),
  Forall bounded_instr l.
Proof.
  intros; rewrite Forall_forall in *; clarify.
  specialize (Hout x); destruct x; unfold bounded_instr; clarify.
Qed.

Lemma bounded_instrument : forall i, safe_instr i ->
  forall t, Forall bounded_instr (instrument_instr i t).
Proof.
  intro; eapply instr_ind' with (Q := fun l => Forall safe_instr l ->
    forall t, Forall bounded_instr (instrument l t))(i := i); clarify.
  - destruct i0; auto; intros; apply no_spawn_bounded; rewrite Forall_forall;
      intros i' ?; destruct i'; auto; exploit spawn_in_handler; eauto; clarify.
  - rewrite Forall_app; split.
    + apply no_spawn_bounded; rewrite Forall_forall; intros ? Hin.
      destruct x; auto.
      setoid_rewrite in_app in Hin; destruct Hin; clarify.
      exploit max_vc_instrs; eauto; clarify.
    + constructor; clarify.
      rewrite bounded_spawn, safe_instrs in *; auto.
  - inversion H; rewrite Forall_app; clarify.
Qed.

Corollary bounded_instr_list : forall li, Forall safe_instr li ->
  forall t, Forall bounded_instr (instrument li t).
Proof.
  induction li; clarify.
  inversion H; rewrite Forall_app; clarify.
  apply bounded_instrument; auto.
Qed.

Corollary bounded_sim : forall P (Hsafe : safe_locs P)
  (Ht : Forall (fun e => fst e < zt) P) P' (Hsim : state_sim P P'),
  bounded_threads P'.
Proof.
  induction P; clarify.
  - inversion Hsim; clarify; constructor.
  - inversion Hsim; inversion Hsafe; inversion Ht; clarify.
    constructor; [|apply IHP; auto].
    clarsimp.
    apply bounded_instr_list; auto.
Qed.

Definition v_access v a := loc_of a = v \/
  (exists o, loc_of a = (R + fst v, o)) \/
  (exists o, loc_of a = (W + fst v, o)).

Lemma instrument_length : forall i t, length (instrument_instr i t) <> 0.
Proof.
  repeat intro.
  destruct (instrument_instr i t) eqn: Hi; clarify.
  exploit instrument_nonnil; eauto.
Qed.

(*
Lemma lock_hold' : forall m l t ops (Hinit : initialized m (l, 0))
  (Hheld : can_read (m ++ ops) (l, 0) (S t)) (Hcon : consistent (m ++ ops))
  (Hprog : Forall prog_op ops) (Hlock : Forall (fun a => loc_of a = (l, 0) ->
     lock_op l a) ops),
  can_read m (l, 0) (S t) \/ In (Acq t l) ops.
Proof.
  induction ops using rev_ind; clarsimp.
  rewrite app_assoc in Hcon; exploit consistent_app_SC; eauto.
  rewrite Forall_app in *; clarify.
  inversion Hlock2 as [|?? Hx]; inversion Hprog2; rewrite in_app; clarify.
  unfold can_read in *.
  repeat rewrite <- app_assoc in *; simpl.
  destruct (eq_dec (loc_of x) (l, 0)).
  - unfold lock_op in Hx; clarify.
    destruct Hx as [? | ?]; clarify.
    + assert (S t = S x0) as Heq; [|inversion Heq; clarify].
      rewrite app_assoc in Hcon; rewrite <- read_arwritten_SC; eauto.
      apply can_read_thread.
      unfold can_read; repeat rewrite <- app_assoc; auto.
    + generalize (init_steps Hinit Hprog1); intro.
      inversion Hprog2; subst; exploit init_step; eauto; rewrite <- app_assoc;
        intro.
      generalize (can_read_unique(m := m ++ ops ++ [Rel x0 l])(p := (l, 0))
        (S t) 0); intro Heq; clarify.
      use Heq.
      * use Heq; clarify.
        eapply can_read_thread'.
        unfold can_read; rewrite app_assoc, read_arwritten_SC; auto.
        rewrite <- app_assoc; auto.
      * unfold can_read; repeat rewrite <- app_assoc; auto.
  - simpl in Hheld; rewrite app_assoc, loc_valid_SC in Hheld; clarify.
    repeat rewrite <- app_assoc in *; clarify.
Qed.
*)
Definition good_var x := state_forall
  (fun i => match i with Lock l | Unlock l => l <> x | _ => True end).
(*
Lemma protect_self : forall P0 (Hsafe : safe_locs P0)
  (Ht : Forall (fun e => fst e < zt) P0) P0' (Hsim : state_sim P0 P0')
  (Hdistinct : distinct P0') G0 lo0 lc0 P G
  (Hsteps : exec_star (Some P0') G0 lo0 lc0 (Some P) G)
  l (Hlock : good_lock (l, 0) P0')
  m (Hinit : initialized m (l, 0))
  t (Hheld : can_read (m ++ lc0) (l, 0) (S t))
  lo lc P' G' (Hsteps' : exec_star (Some P) G lo lc P' G')
  (Hno_lock : Forall (fun a => a <> Rel t l) lc)
  (Hcon : consistent (m ++ lc0 ++ lc)),
  Forall (fun a => loc_of a <> (l, 0))
    (filter (fun x => negb (beq (thread_of x) t)) lc).
Proof.
  intros.
  remember (Some P) as P1; generalize dependent P; rewrite exec_rev in Hsteps'; 
    induction Hsteps'; clarify.
  rewrite Forall_app in Hno_lock.
  do 2 rewrite app_assoc in Hcon; exploit consistent_app_SC; eauto.
  rewrite <- app_assoc; clarify.
  specialize (IHHsteps' _ eq_refl).
  rewrite filter_app, Forall_app; clarify.
  rewrite Forall_forall; repeat intro.
  rewrite <- exec_rev in Hsteps'.
  rewrite app_assoc in H; exploit lock_hold; try apply H; eauto.
  { eapply init_steps, prog_steps; eauto. }
  { eapply prog_steps; eauto. }
  { exploit forall_steps; eauto; intro.
    eapply good_lock_ops; eauto. }
  intros [Hheld' | ?].
  exploit exec_star_trans; [apply Hsteps | apply Hsteps' | intro].
  destruct c; clarify.
  exploit forall_steps; eauto; intro.
  exploit good_lock_ops; eauto.
  { eapply exec_step'; eauto; apply exec_refl. }
  rewrite Forall_app; simpl; intros [Hx _].
  inversion Hx as [|?? Hl]; clarify.
  destruct Hl as [? [? | ?]]; subst.
  - inversion Hexec'; clarify.
    rewrite can_arw_SC_iff in Hcon.
    specialize (Hcon 0); exploit consistent_app_SC; try apply Hcon; intro.
    exploit can_read_thread'; eauto; intro.
    exploit can_read_unique.
    { apply H. }
    { do 2 (eapply init_steps, prog_steps; eauto). }
    { apply Hheld'. }
    { eauto. }
    clarify.
  - inversion Hexec'; clarify.
    rewrite can_arw_SC_iff in Hcon.
    specialize (Hcon 0); exploit consistent_app_SC; try apply Hcon; intro.
    exploit can_read_thread'; eauto; intro.
    exploit can_read_unique.
    { apply H. }
    { do 2 (eapply init_steps, prog_steps; eauto). }
    { apply Hheld'. }
    { eauto. }
    intro Heq; inversion Heq; unfold beq, negb in cond; clarify.
  - rewrite Forall_forall in Hno_lock1; exploit Hno_lock1; eauto.
Qed.

Lemma access_v : forall i t n i' rest (Ht : t < zt)
  (Hn : skipn n (instrument_instr i t) = i' :: rest)
  v o (Hv : v < zv) (Hmeta : ~meta_loc (v, o))
  (Hi : i <> Lock v /\ i <> Unlock v) (Hsafe : safe_instr i)
  (Hwait : match i with Wait u => u < zt | _ => True end)
  (Haccess : accesses i' = Some (v, o) \/ accesses i' = Some (R + v, o) \/
             accesses i' = Some (W + v, o)),
  n > 0 /\ match i with Load _ p => fst p = v | Store p _ => fst p = v
                  | _ => False end.
Proof.
  intros.
  destruct (accesses i') as [(?, ?)|] eqn: Hi'; [|clarify].
  destruct n; clarify.
  - exfalso; exploit instrument_access; eauto.
    { setoid_rewrite <- app_nil_r in Hn at 1; eauto. }
    intros [[? ?] | [? [? | ?]]]; clarify.
    + eapply v_not_C with (v := (v, o)); eauto.
      destruct Haccess as [? | [? | ?]]; eauto.
    + contradiction Hsafe1; destruct Haccess; clarify;
        [apply R_meta | apply W_meta]; auto.
    + eapply v_not_X with (v := (v, o))(v' := fst x); eauto.
      destruct Haccess as [? | [? | ?]]; eauto.
  - destruct (instrument_instr i t) eqn: Hinstr; clarify.
    destruct i; try destruct x; clarify; try (rewrite skipn_nil in *; clarify).
    + repeat rewrite skipn_app in Hn; rewrite <- app_assoc in Hn.
      destruct (skipn n (hb_check (W + v1) (C + t) zt tmp1 tmp2)) eqn: Hskip;
        clarify.
      destruct (skipn (n - length (hb_check (W + v1) (C + t) zt tmp1 tmp2))
        (move (C + t, t) (R + v1, t) tmp1)) eqn: Hskip'; clarify.
      destruct ((n - length (hb_check (W + v1) (C + t) zt tmp1 tmp2 ++
        move (C + t, t) (R + v1, t) tmp1))); clarify.
      * contradiction Hsafe1; destruct Haccess; clarify;
          [apply R_meta | apply W_meta]; auto.
      * destruct n2; clarify; [|rewrite skipn_nil in *; clarify].
        exfalso; eapply v_not_X with (v := (v, o))(v' := v1); eauto.
        destruct Haccess as [? | [? | ?]]; eauto.
      * unfold move in Hskip';
          destruct (n - length (hb_check (W + v1) (C + t) zt tmp1 tmp2));
          clarify.
        { exfalso; eapply v_not_C with (v := (v, o)); eauto.
          destruct Haccess as [? | [? | ?]]; eauto. }
        destruct n2; clarify; [|rewrite skipn_nil in Hskip'; clarify].
        destruct Haccess as [? | [? | ?]]; clarify.
        { contradiction Hmeta; apply R_meta; auto. }
        eapply plus_reg_l; eauto.
        { exploit (Hmetalocs_disjoint_WR Hv Hsafe2); auto; contradiction. }
      * exploit hb_check_instr; eauto.
        { eapply skipn_in; setoid_rewrite Hskip; simpl; auto. }
        intros (? & ? & [? | ?]); clarify.
        { destruct Haccess as [? | [? | ?]]; clarify.
          { contradiction Hmeta; apply W_meta; auto. }
          { exploit (Hmetalocs_disjoint_WR Hsafe2 Hv); auto; contradiction. }
          eapply plus_reg_l; eauto. }
        { exfalso; eapply v_not_C with (v := (v, o))(t := t); eauto.
          destruct Haccess as [? | [? | ?]]; eauto. }
    + repeat rewrite skipn_app in Hn; repeat rewrite <- app_assoc in Hn.
      destruct (skipn n (hb_check (W + v1) (C + t) zt tmp1 tmp2)) eqn: Hskip;
        clarify.
      destruct (skipn (n - length (hb_check (W + v1) (C + t) zt tmp1 tmp2))
        (hb_check (R + v1) (C + t) zt tmp1 tmp2)) eqn: Hskip'; clarify.
      destruct (skipn (n - length (hb_check (W + v1) (C + t) zt tmp1 tmp2) -
        length (hb_check (R + v1) (C + t) zt tmp1 tmp2))
        (move (C + t, t) (W + v1, t) tmp1)) eqn: Hskip''; clarify.
      destruct ((n - length (hb_check (W + v1) (C + t) zt tmp1 tmp2 ++
             hb_check (R + v1) (C + t) zt tmp1 tmp2 ++
             move (C + t, t) (W + v1, t) tmp1))); clarify.
      * contradiction Hsafe1; destruct Haccess; clarify;
          [apply R_meta | apply W_meta]; auto.
      * destruct n2; clarify; [|rewrite skipn_nil in *; clarify].
        exfalso; eapply v_not_X with (v := (v, o))(v' := v1); eauto.
        destruct Haccess as [? | [? | ?]]; eauto.
      * unfold move in Hskip'';
          destruct (n - length (hb_check (W + v1) (C + t) zt tmp1 tmp2) -
            length (hb_check (R + v1) (C + t) zt tmp1 tmp2)); clarify.
        { exfalso; eapply v_not_C with (v := (v, o)); eauto.
          destruct Haccess as [? | [? | ?]]; eauto. }
        destruct n2; clarify; [|rewrite skipn_nil in Hskip''; clarify].
        destruct Haccess as [? | [? | ?]]; clarify.
        { contradiction Hmeta; apply W_meta; auto. }
        { exploit (Hmetalocs_disjoint_WR Hsafe2 Hv); auto; contradiction. }
        eapply plus_reg_l; eauto.
      * exploit hb_check_instr; eauto.
        { eapply skipn_in; setoid_rewrite Hskip'; simpl; auto. }
        intros (? & ? & [? | ?]); clarify.
        { destruct Haccess as [? | [? | ?]]; clarify.
          { contradiction Hmeta; apply R_meta; auto. }
          eapply plus_reg_l; eauto.
          { exploit (Hmetalocs_disjoint_WR Hv Hsafe2); auto; contradiction. } }
        { exfalso; eapply v_not_C with (v := (v, o))(t := t); eauto.
          destruct Haccess as [? | [? | ?]]; eauto. }
      * exploit hb_check_instr; eauto.
        { eapply skipn_in; setoid_rewrite Hskip; simpl; auto. }
        intros (? & ? & [? | ?]); clarify.
        { destruct Haccess as [? | [? | ?]]; clarify.
          { contradiction Hmeta; apply W_meta; auto. }
          { exploit (Hmetalocs_disjoint_WR Hsafe2 Hv); auto; contradiction. }
          eapply plus_reg_l; eauto. }
        { exfalso; eapply v_not_C with (v := (v, o))(t := t); eauto.
          destruct Haccess as [? | [? | ?]]; eauto. }
    + exploit max_vc_instr; eauto.
      { eapply skipn_in; setoid_rewrite Hn; simpl; auto. }
      intros (? & ? & [? | ?]); clarify.
      * eapply v_not_L with (v := (v, o)); eauto.
        destruct Haccess as [? | [? | ?]]; eauto.
      * eapply v_not_C with (v := (v, o))(t := t); eauto.
        destruct Haccess as [? | [? | ?]]; eauto.
    + unfold unlock_handler in Hinstr.
      destruct (set_vc (C + t) (L + m) zt tmp1) eqn: Hset; clarify.
      { destruct zt; clarify. }
      repeat rewrite skipn_app in Hn; rewrite <- app_assoc in Hn.
      destruct (skipn n l) eqn: Hskip.
      destruct (skipn (n - length l) (inc_vc t (C + t) tmp1)) eqn: Hskip'.
      * destruct (n - length (l ++ inc_vc t (C + t) tmp1)); clarify;
          [|rewrite skipn_nil in *; clarify].
        destruct Haccess; clarify; contradiction Hsafe1;
          [apply R_meta | apply W_meta]; auto.
      * unfold inc_vc in Hskip'; destruct (n - length l); clarify.
        { eapply v_not_C with (v := (v, o)); eauto.
          destruct Haccess as [? | [? | ?]]; eauto. }
        destruct n1; clarify.
        destruct n1; clarify; [|rewrite skipn_nil in *; clarify].
        eapply v_not_C with (v := (v, o)); eauto.
        destruct Haccess as [? | [? | ?]]; eauto.
      * clarify.
        exploit set_vc_instr; eauto.
        { eapply skipn_in; setoid_rewrite Hset; instantiate (1 := 1); simpl.
          eapply skipn_in; setoid_rewrite Hskip; simpl; auto. }
        intros (? & ? & [? | ?]); clarify.
        { eapply v_not_C with (v := (v, o))(t := t); eauto.
          destruct Haccess as [? | [? | ?]]; eauto. }
        { eapply v_not_L with (v := (v, o)); eauto.
          destruct Haccess as [? | [? | ?]]; eauto. }
    + unfold spawn_handler in Hinstr.
      destruct (max_vc (C + t) (C + t0) zt tmp1 tmp2) eqn: Hmax; clarify.
      { destruct zt; clarify. }
      repeat rewrite skipn_app in Hn; rewrite <- app_assoc in Hn.
      destruct (skipn n l) eqn: Hskip.
      destruct (skipn (n - length l) (inc_vc t (C + t) tmp1)) eqn: Hskip'.
      * destruct (n - length (l ++ inc_vc t (C + t) tmp1)); clarify.
        rewrite skipn_nil in *; clarify.
      * unfold inc_vc in Hskip'; destruct (n - length l); clarify.
        { eapply v_not_C with (v := (v, o)); eauto.
          destruct Haccess as [? | [? | ?]]; eauto. }
        destruct n1; clarify.
        destruct n1; clarify; [|rewrite skipn_nil in *; clarify].
        eapply v_not_C with (v := (v, o)); eauto.
        destruct Haccess as [? | [? | ?]]; eauto.
      * clarify.
        exploit max_vc_instr; eauto.
        { eapply skipn_in; setoid_rewrite Hmax; instantiate (1 := 1); simpl.
          eapply skipn_in; setoid_rewrite Hskip; simpl; auto. }
        intros (? & ? & [? | ?]); clarify.
        { eapply v_not_C with (v := (v, o))(t := t); eauto.
          destruct Haccess as [? | [? | ?]]; eauto. }
        { eapply v_not_C with (v := (v, o))(t := t0); eauto.
          destruct Haccess as [? | [? | ?]]; eauto. }
    + unfold wait_handler in Hn; rewrite skipn_app in Hn.
      destruct (skipn n (max_vc (C + t0) (C + t) zt tmp1 tmp2)) eqn: Hskip.
      * unfold inc_vc in Hn;
          destruct (n - length (max_vc (C + t0) (C + t) zt tmp1 tmp2));
          clarify.
        { eapply v_not_C with (v := (v, o))(t := n0); eauto.
          destruct Haccess as [? | [? | ?]]; eauto. }
        destruct n1; clarify.
        destruct n1; clarify; [|rewrite skipn_nil in *; clarify].
        eapply v_not_C with (v := (v, o)); eauto.
        destruct Haccess as [? | [? | ?]]; eauto.
      * clarify.
        exploit max_vc_instr; eauto.
        { eapply skipn_in; setoid_rewrite Hskip; simpl; auto. }
        intros (? & ? & [? | ?]); clarify.
        { eapply v_not_C with (v := (v, o))(t := t0); eauto.
          destruct Haccess as [? | [? | ?]]; eauto. }
        { eapply v_not_C with (v := (v, o))(t := t); eauto.
          destruct Haccess as [? | [? | ?]]; eauto. }
Qed.*)

(*
Lemma step_into_instruments1 : forall P P1 (Hsim : state_sim P P1)
  (Hsafe : safe_locs P) (Hdistinct : distinct P1)
  G1 lo lc P1' G1' (Hsteps : exec_star (Some P1) G1 lo lc (Some P1') G1')
  Pa n (HPa : Pa = skipn n P1'),
  exists P', safe_locs P' /\ state_suffix P' Pa.
Proof.
  induction Pa; clarify.
  - repeat eexists; constructor.
  - destruct P1'; [rewrite skipn_nil in HPa; clarify|].
    exploit skipn_cons; eauto; intro.
    specialize (IHPa (S n)); use IHPa; destruct IHPa as (P' & ?).
    assert (In a (p :: P1')).
    { eapply skipn_in; setoid_rewrite <- HPa; simpl; auto. }
    destruct a as (t, li); destruct li.
    + exists ((t, []) :: P'); repeat split; constructor; clarify; eauto.
    + exploit step_into_instrument; eauto.
      intros (? & ? & ? & ? & n' & i' & li' & rest & ?).
      exists ((t, i' :: rest) :: P'); repeat split; constructor; clarify.
      exists n'; rewrite skipn_app.
      destruct (le_gt_dec (length (instrument_instr i' t)) n').
      { rewrite skipn_all in *; clarify. }
      rewrite not_le_minus_0; [clarsimp | omega].
Qed.

Corollary step_into_instruments : forall P P1 (Hsim : state_sim P P1)
  (Hsafe : safe_locs P) (Hdistinct : distinct P1)
  G1 lo lc P1' G1' (Hsteps : exec_star (Some P1) G1 lo lc (Some P1') G1'),
  exists P', safe_locs P' /\ state_suffix P' P1'.
Proof.
  intros; eapply step_into_instruments1 with (n := 0); eauto.
Qed.
*)
Lemma rel_inv' : forall t x P G lo lc P' G' (Hdistinct : distinct P)
  (Hsteps : exec_star (Some P) G lo lc (Some P') G') li li'
  (Hin : In (t, li ++ li') P) (Hin' : In (t, li') P') (Hrel : In (Rel t x) lc),
  In (Unlock x) li.
Proof.
  intros.
  exploit rel_inv; eauto; intros (li1 & li2 & Heq & ? & Hin2).
  exploit distinct_steps; eauto; intro.
  exploit distinct_in.
  { eauto. }
  { apply Hin'. }
  { eauto. }
  clarify.
  symmetry in Heq.
  rewrite split_app in Heq; exploit app_eq_inv_ge.
  { eauto. }
  { assert (length ((li1 ++ [Unlock x]) ++ li2) = length (li ++ skipn x0 li2))
      by (rewrite Heq; auto).
    repeat rewrite app_length in *; rewrite skipn_length in *; omega. }
  intros (? & _ & ?); subst.
  repeat rewrite in_app; simpl; auto.
Qed.
(*    
Lemma access_held : forall P0 (Hsafe : safe_locs P0)
  (Ht : Forall (fun e => fst e < zt) P0) P0' (Hsim : state_sim P0 P0')
  (Hdistinct : distinct P0') G0 lo0 lc0 P G
  (Hsteps : exec_star (Some P0') G0 lo0 lc0 (Some P) G)
  v o (Hv : v < zv) (Hmeta : ~meta_loc (v, o))
  (Hlock : good_lock (X + v, 0) P0') (Hvar : good_var v P0')
  m (Hinit : initialized m (X + v, 0)) (Hcon : consistent (m ++ lc0))
  t i' rest (Hin : In (t, i' :: rest) P)
  (Haccess : accesses i' = Some (v, o) \/ accesses i' = Some (R + v, o) \/
             accesses i' = Some (W + v, o)),
  can_read (m ++ lc0) (X + v, 0) (S t).
Proof.
  intros.
  exploit step_into_instrument; eauto.
  intros (Pl & ? & ? & ? & n & i0 & ? & ? & ? & ? & ? & Hstepsl & Hinl & Heq &
    ?); clarify.
  exploit bounded_sim; eauto; intro.
  exploit bounded_steps; eauto; intro Hbound.
  setoid_rewrite Forall_forall in Hbound; exploit Hbound; eauto; clarify.
  exploit distinct_steps; try apply Hstepsl; auto; intro.
  exploit access_v; eauto.
  { exploit forall_steps; try apply Hstepsl; eauto.
    setoid_rewrite Forall_forall; intro X; exploit X; eauto; intro Hi0.
    split; intro; subst; simpl in *.
    * inversion Hi0; clarify.
    * repeat rewrite Forall_app in Hi0; destruct Hi0 as ((_ & Hi0) & ?).
      inversion Hi0; clarify. }
  { destruct i0; auto; clarify.
    destruct n; clarify.
    exploit step_instr; try apply Hinl; eauto.
    { rewrite skipn_app, not_le_minus_0.
      setoid_rewrite Heq; simpl; auto.
      { intro; rewrite skipn_all in Heq; clarify. } }
    intros (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Hwait & ?); clarify.
    exploit exec_other_threads; try apply Hinl; eauto; intro.
    exploit in_split; eauto; clarify.
    exploit distinct_steps; try eapply exec_minus_exec; eauto; intro.
    exploit exec_next; eauto; clarify.
    exploit bounded_steps; try apply Hstepsl; auto; intro.
    exploit bounded_steps; try eapply exec_minus_exec; eauto; intro Hbound'.
    setoid_rewrite Forall_forall in Hbound'; exploit Hbound'; eauto; clarify. }
  intros (? & ?); destruct n; [omega|].
  destruct i0; try contradiction; try destruct x6; clarify.
  - exploit step_instr; try apply Hinl; eauto.
    { rewrite skipn_app, not_le_minus_0.
      setoid_rewrite Heq; simpl; auto.
      { intro; rewrite skipn_all in Heq; clarify. } }
    intros (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & HX & ?); clarify.
    exploit exec_other_threads; try apply Hinl; eauto; intro.
    exploit in_split; eauto; clarify.
    exploit distinct_steps; try eapply exec_minus_exec; eauto; intro.
    exploit exec_next; eauto; clarify.
    rewrite split_app in Hcon; repeat rewrite app_assoc in Hcon.
    exploit lock_hold; try apply Hcon.
    { instantiate (1 := X + v).
      repeat rewrite <- app_assoc.
      eapply init_steps; auto.
      repeat (rewrite Forall_app; split).
      * eapply prog_steps; eauto.
      * eapply prog_steps, exec_minus_exec; eauto.
      * constructor; simpl; auto. }
    { apply can_read_arwritten.
      eapply consistent_app_SC; eauto. }
    { eapply prog_steps; eauto. }
    { exploit forall_steps; try apply Hlock; try apply Hstepsl; intro.
      exploit forall_steps; try eapply exec_minus_exec; eauto; intro.
      exploit forall_step; eauto; intro.
      eapply good_lock_ops; eauto. }
    repeat rewrite <- app_assoc; clarify.
    exploit distinct_step; eauto; intro.
    exploit rel_inv'; eauto.
    { instantiate (1 := firstn n _).
      setoid_rewrite <- (firstn_skipn n ((hb_check _ _ _ _ _ ++ _) ++ _)).
      rewrite Heq, <- app_assoc; simpl; apply split_in. }
    repeat rewrite firstn_app, in_app; intros [[? | ?] | Hin'].
    + exploit firstn_in; eauto; intro.
      exploit hb_check_instrs; eauto; clarify.
    + exploit firstn_in; eauto; clarify.
    + destruct (n - length (hb_check (W + v) (C + t) zt tmp1 tmp2 ++
        move (C + t, t) (R + v, t) tmp1)) eqn: Hn; setoid_rewrite Hn in Hin';
        clarify.
      destruct n1; clarify.
      rewrite skipn_all in Heq; [clarify|].
      rewrite app_length; simpl.
      clear - Hn.
      erewrite <- Nat.sub_add.
      setoid_rewrite Hn.
      rewrite plus_comm; apply plus_le_compat_r; omega.
      { omega. }
  - exploit step_instr; try apply Hinl; eauto.
    { rewrite skipn_app, not_le_minus_0.
      setoid_rewrite Heq; simpl; auto.
      { intro; rewrite skipn_all in Heq; clarify. } }
    intros (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & HX & ?); clarify.
    exploit exec_other_threads; try apply Hinl; eauto; intro.
    exploit in_split; eauto; clarify.
    exploit distinct_steps; try eapply exec_minus_exec; eauto; intro.
    exploit exec_next; eauto; clarify.
    rewrite split_app in Hcon; repeat rewrite app_assoc in Hcon.
    exploit lock_hold; try apply Hcon.
    { instantiate (1 := X + v).
      repeat rewrite <- app_assoc.
      eapply init_steps; auto.
      repeat (rewrite Forall_app; split).
      * eapply prog_steps; eauto.
      * eapply prog_steps, exec_minus_exec; eauto.
      * constructor; simpl; auto. }
    { apply can_read_arwritten.
      eapply consistent_app_SC; eauto. }
    { eapply prog_steps; eauto. }
    { exploit forall_steps; try apply Hlock; try apply Hstepsl; intro.
      exploit forall_steps; try eapply exec_minus_exec; eauto; intro.
      exploit forall_step; eauto; intro.
      eapply good_lock_ops; eauto. }
    repeat rewrite <- app_assoc; clarify.
    exploit distinct_step; eauto; intro.
    exploit rel_inv'; eauto.
    { instantiate (1 := firstn n _).
      setoid_rewrite <- (firstn_skipn n ((hb_check _ _ _ _ _ ++ _) ++ _)).
      rewrite Heq, <- app_assoc; simpl; apply split_in. }
    repeat rewrite firstn_app, in_app; intros [[? | [? | ?]] | Hin'].
    + exploit firstn_in; eauto; intro.
      exploit hb_check_instrs; eauto; clarify.
    + exploit firstn_in; eauto; intro.
      exploit hb_check_instrs; eauto; clarify.
    + exploit firstn_in; eauto; clarify.
    + destruct (n - length (hb_check (W + v) (C + t) zt tmp1 tmp2 ++
        hb_check (R + v) (C + t) zt tmp1 tmp2 ++
        move (C + t, t) (W + v, t) tmp1)) eqn: Hn; setoid_rewrite Hn in Hin';
        clarify.
      destruct n1; clarify.
      rewrite skipn_all in Heq; [clarify|].
      rewrite app_length; simpl.
      clear - Hn.
      erewrite <- Nat.sub_add.
      setoid_rewrite Hn.
      rewrite plus_comm; apply plus_le_compat_r; omega.
      { omega. }
Qed.

Lemma protect_held : forall P0 (Hsafe : safe_locs P0)
  (Ht : Forall (fun e => fst e < zt) P0) P0' (Hsim : state_sim P0 P0')
  (Hdistinct : distinct P0') G0 lo0 lc0 P G
  (Hsteps : exec_star (Some P0') G0 lo0 lc0 (Some P) G)
  v (Hv : fst v < zv) (Hmeta : ~meta_loc v)
  (Hlock : good_lock (X + fst v, 0) P0') (Hvar : good_var (fst v) P0')
  m (Hinit : initialized m (X + fst v, 0))
  t (Hheld : can_read (m ++ lc0) (X + fst v, 0) (S t))
  lo lc P' G' (Hsteps' : exec_star (Some P) G lo lc P' G')
  (Hno_lock : Forall (fun a => a <> Rel t (X + fst v)) lc)
  (Hcon : consistent (m ++ lc0 ++ lc)),
  Forall (fun a => ~v_access v a /\ loc_of a <> (X + fst v, 0))
    (filter (fun x => negb (beq (thread_of x) t)) lc).
Proof.
  intros.
  remember (Some P) as P1; generalize dependent P; rewrite exec_rev in Hsteps'; 
    induction Hsteps'; clarify.
  rewrite Forall_app in Hno_lock.
  do 2 rewrite app_assoc in Hcon; exploit consistent_app_SC; eauto.
  rewrite <- app_assoc; clarify.
  specialize (IHHsteps' _ eq_refl).
  rewrite filter_app, Forall_app; clarify.
  rewrite Forall_forall; repeat intro.
  rewrite <- exec_rev in Hsteps'.
  rewrite app_assoc in H; exploit lock_hold; try apply H; eauto.
  { eapply init_steps, prog_steps; eauto. }
  { eapply prog_steps; eauto. }
  { exploit forall_steps; try apply Hlock; eauto; intro.
    eapply good_lock_ops; eauto. }
  intros [Hheld' | ?].
  exploit exec_star_trans; [apply Hsteps | apply Hsteps' | intro].
  exploit protect_self; eauto.
  { rewrite <- app_assoc in Hheld'; auto. }
  { eapply exec_step'; eauto.
    * apply exec_refl.
    * rewrite app_nil_r; auto. }
  { repeat rewrite <- app_assoc in *; auto. }
  intro Hlocked; destruct c; clarify.
  inversion Hlocked; clarify.
  assert (Forall (fun a => a <> Acq t0 (X + fst v)) [x]).
  { constructor; auto; intro; clarify. }
  exploit exec_ops; eauto.
  simpl; unfold beq; intro Hthread; inversion Hthread; clarify.
  destruct P''; [|inversion Hexec'; clarify].
  intro Haccess.
  exploit step_thread'; eauto; intros (i & ? & Hin' & ?); clarify.
  assert (exists o, ~meta_loc (fst v, o) /\ (accesses i = Some (fst v, o) \/
    accesses i = Some (R + fst v, o) \/ accesses i = Some (W + fst v, o)))
    as (o' & Hmeta' & Haccess').
  { exploit distinct_steps; eauto; intro Hdistinct'.
    generalize (exec_accesses Hdistinct' Hexec' _ _ Hin'); intro Hloc.
    destruct Haccess as [? | [? | ?]].
    * rewrite Hloc in *; destruct v; eauto.
    * clarify; rewrite Hloc in *; eauto.
    * clarify; rewrite Hloc in *; eauto. }
  rewrite <- app_assoc in *.
  exploit access_held; eauto; intro.
  exploit can_read_unique.
  { apply H. }
  { do 2 (eapply init_steps, prog_steps; eauto). }
  { apply Hheld'. }
  { eauto. }
  intro Heq; inversion Heq; unfold beq, negb in cond; clarify.
  { rewrite Forall_forall in Hno_lock1; exploit Hno_lock1; eauto. }
Qed.

Lemma L_access : forall i1 i t (Ht : t < zt)
  (Hsafe : safe_instr i) (Hi : match i with Wait u => u < zt | _ => True end)
  (His : In i1 (instrument_instr i t))
  l (Hv : l < zl) (Hv2 : ~meta_loc (l, 0))
  o (Haccess : accesses i1 = Some (L + l, o)),
  match i with Lock p => p = l | Unlock p => p = l | _ => False end.
Proof.
  destruct i; try destruct x; clarify; repeat rewrite in_app in *.
  - destruct His as [? | [[? | ?] | ?]]; clarify.
    + exploit Hmetalocs_disjoint_LX; eauto.
    + exploit hb_check_instrs; eauto; intros [[? [? [? | ?]]] | ?]; clarify.
      * exploit Hmetalocs_disjoint_LW; eauto.
      * eapply Hmetalocs_disjoint_CL with (t := t); eauto.
    + destruct H; clarify.
      * eapply Hmetalocs_disjoint_CL; eauto.
      * eapply Hmetalocs_disjoint_LR; eauto.
    + destruct H; clarify.
      * contradiction Hsafe1; apply L_meta; auto.
      * eapply Hmetalocs_disjoint_LX; eauto.
  - destruct His as [? | [[? | [? | ?]] | ?]]; clarify.
    + exploit Hmetalocs_disjoint_LX; eauto.
    + exploit hb_check_instrs; eauto; intros [[? [? [? | ?]]] | ?]; clarify.
      * exploit Hmetalocs_disjoint_LW; eauto.
      * eapply Hmetalocs_disjoint_CL with (t := t); eauto.
    + exploit hb_check_instrs; eauto; intros [[? [? [? | ?]]] | ?]; clarify.
      * exploit Hmetalocs_disjoint_LR; eauto.
      * eapply Hmetalocs_disjoint_CL with (t := t); eauto.
    + destruct H; clarify.
      * eapply Hmetalocs_disjoint_CL; eauto.
      * eapply Hmetalocs_disjoint_LW; eauto.
    + destruct H; clarify.
      * contradiction Hsafe1; apply L_meta; auto.
      * eapply Hmetalocs_disjoint_LX; eauto.
  - destruct His; clarify.
    + contradiction Hsafe1; apply L_meta; auto.
    + exploit max_vc_instrs; eauto; intros [[? [? [? | ?]]] | ?]; clarify.
      * eapply plus_reg_l; eauto.
      * destruct H1; clarify; exploit Hmetalocs_disjoint_CL; try apply H2;
          eauto; contradiction.
  - setoid_rewrite in_app in His; destruct His as [[? | ?] | ?]; clarify.
    + exploit set_vc_instrs; eauto; intros [? [? [? | ?]]]; clarify.
      * exploit Hmetalocs_disjoint_CL; try apply H2; eauto; contradiction.
      * eapply plus_reg_l; eauto.
    + destruct H as [? | [? | ?]]; clarify; exploit Hmetalocs_disjoint_CL;
        eauto; contradiction.
    + contradiction Hsafe1; apply L_meta; auto.
  - setoid_rewrite in_app in His; destruct His as [[? | ?] | ?]; clarify.
    + exploit max_vc_instrs; eauto; intros [[? [? [? | ?]]] | ?]; clarify.
      * eapply Hmetalocs_disjoint_CL with (t := t0); eauto.
      * destruct H1; clarify; eapply Hmetalocs_disjoint_CL with (t := t); eauto.
    + destruct H as [? | [? | ?]]; clarify; eapply Hmetalocs_disjoint_CL; eauto.
  - setoid_rewrite in_app in His; destruct His; clarify.
    + exploit max_vc_instrs; eauto; intros [[? [? [? | ?]]] | ?]; clarify.
      * eapply Hmetalocs_disjoint_CL with (t := t); eauto.
      * destruct H1; clarify; eapply Hmetalocs_disjoint_CL with (t := t0);
          eauto.
    + destruct H; clarify; eapply Hmetalocs_disjoint_CL; eauto.
Qed.
*)
Definition good_unlock l li := forall i, nth_error li i = Some (Unlock l) ->
  exists j, j < i /\ nth_error li j = Some (Lock l) /\
  forall k, j < k < i -> nth_error li k <> Some (Unlock l).

Definition good_unlocks l := instr_rect'' (fun _ => Prop) _ (fun _ => True)
  (fun _ li r => good_unlock l li /\ r) True (fun _ _ r1 r2 => r1 /\ r2).

Lemma good_unlocks_list_iff : forall x li, instr_list_rect _ _ (fun _ => True)
  (fun _ li r => good_unlock x li /\ r) True (fun _ _ r1 r2 => r1 /\ r2) li <->
  Forall (good_unlocks x) li.
Proof.
  unfold good_unlocks; induction li; split; clarify.
  - constructor; auto.
    apply IHli; auto.
  - inversion H; clarify; apply IHli; auto.
Qed.

Definition well_locked l (P : state) :=
  Forall (fun e => good_unlock l (snd e) /\ Forall (good_unlocks l) (snd e)) P.
(*
Lemma well_locked_spawn : forall l P G lo lc P' G'
  (Hwell_locked : well_locked l P)
  (Hsteps : exec_star (Some P) G lo lc (Some P') G') t li (Hin : In (t, li) P')
  u li' (Hspawn : In (Spawn u li') li),
  good_unlock l li' /\ Forall (good_unlocks l) li'.
Proof.
  intros ?????????; remember (Some P) as Pa; remember (Some P') as Pb;
    generalize dependent P'; generalize dependent P;
    rewrite exec_rev in Hsteps; induction Hsteps; clarify.
  - setoid_rewrite Forall_forall in Hwell_locked; exploit Hwell_locked; eauto;
      intros (? & Hgood).
    rewrite Forall_forall in Hgood; exploit Hgood; eauto; clarify.
    unfold good_unlocks in *; clarify.
    rewrite (good_unlocks_list_iff l) in *; auto.
  - specialize (IHHsteps P0); clarify.
    specialize (IHHsteps _ eq_refl).
    rewrite <- exec_rev in Hsteps.
    exploit exec_result; eauto.
    intros (Pa & i & li2 & Pb & v & ? & Hresult).
    destruct (instr_result t i (G' t) v) as [((((?, ?), ?), ?), ?)|] eqn: Hi; 
      clarify.
    rewrite in_app in Hin; simpl in Hin; rewrite in_app in Hin.
    setoid_rewrite in_app in IHHsteps; simpl in IHHsteps.
    destruct Hin as [? | [? | [? | ?]]]; eauto; clarify.
    + exploit IHHsteps; eauto.
      simpl; eauto.
    + destruct o0; clarify.
      destruct i; clarify.
      exploit IHHsteps.
      { eauto. }
      { simpl; eauto. }
      intros (? & Hgood).
      rewrite Forall_forall in Hgood; exploit Hgood; eauto; clarify.
      unfold good_unlocks in *; clarify.
      rewrite (good_unlocks_list_iff l) in *; auto.
Qed.        

Lemma well_locked_steps : forall l P G lo lc P' G'
  (Hwell_locked : well_locked l P) (Hdistinct : distinct P)
  (Hsteps : exec_star (Some P) G lo lc (Some P') G') t li (Hin : In (t, li) P'),
  exists P1 G1 lo1 lc1 lo2 lc2 li1, exec_star (Some P) G lo1 lc1 (Some P1) G1 /\
    In (t, li1) P1 /\ good_unlock l li1 /\ Forall (good_unlocks l) li1 /\
    exec_star (Some P1) G1 lo2 lc2 (Some P') G' /\ lo = lo1 ++ lo2 /\
    lc = lc1 ++ lc2.
Proof.
  intros until t; remember (Some P) as Pa; remember (Some P') as Pb;
    generalize dependent P'; generalize dependent P;
    rewrite exec_rev in Hsteps; induction Hsteps; clarify.
  - do 8 eexists; try apply exec_refl.
    split; eauto.
    setoid_rewrite Forall_forall in Hwell_locked; exploit Hwell_locked; eauto;
      clarify.
    apply exec_refl.
  - specialize (IHHsteps P0); clarify.
    specialize (IHHsteps _ eq_refl).
    rewrite <- exec_rev in Hsteps.
    exploit exec_result; eauto.
    intros (Pa & i & li' & Pb & v & ? & Hresult).
    destruct (instr_result t0 i (G' t0) v) as [((((?, ?), ?), ?), ?)|] eqn: Hi; 
      clarify.
    rewrite in_app in Hin; simpl in Hin; rewrite in_app in Hin.
    setoid_rewrite in_app in IHHsteps; simpl in IHHsteps.
    destruct Hin as [? | [? | [? | ?]]].
    + exploit IHHsteps; eauto; intros (P1 & ?); clarify.
      exists P1; do 7 eexists; eauto.
      split; eauto; clarify.
      split; [eapply exec_step_inv; eauto|].
      repeat rewrite <- app_assoc; auto.
    + clarify.
      exploit IHHsteps; eauto; intros (P1 & ?); clarify.
      exists P1; do 7 eexists; eauto.
      split; eauto; clarify.
      split; [eapply exec_step_inv; eauto|].
      repeat rewrite <- app_assoc; auto.
    + destruct o0; clarify.
      exists (Pa ++ (t0, li') :: (t, li) :: Pb); do 7 eexists.
      { eapply exec_step_inv; eauto. }
      split; [rewrite in_app; clarify|].
      destruct i; clarify.
      exploit well_locked_spawn; eauto.
      { rewrite in_app; clarify. }
      { simpl; eauto. }
      clarify.
      split; [apply exec_refl|].
      repeat rewrite app_nil_r; auto.
    + exploit IHHsteps; eauto; intros (P1 & ?); clarify.
      exists P1; do 7 eexists; eauto.
      split; eauto; clarify.
      split; [eapply exec_step_inv; eauto|].
      repeat rewrite <- app_assoc; auto.
Qed.

Lemma critical_section' : forall x P G lo lc P' G' (Hlock : good_lock (x, 0) P)
  (Hsteps : exec_star (Some P) G lo lc (Some P') G')
  (Hdistinct : distinct P) m (Hinit : initialized m (x, 0))
  (Hcon : consistent (m ++ lc))
  t li0 li1 li2 (HP : In (t, li0 ++ Lock x :: li1 ++ li2) P)
  (HP' : In (t, li2) P'),
  In (Unlock x) li1 \/ can_read (m ++ lc) (x, 0) (S t).
Proof.
  intros.
  exploit step_invariant; eauto.
  { repeat intro.
    exploit distinct_in.
    { eauto. }
    { apply Ht. }
    { eauto. }
    intro Heq; exploit app_nil_inv.
    { rewrite split_app, app_assoc in Heq; eauto. }
    rewrite <- app_assoc; intro.
    destruct (skipn n li0); clarify. }
  intros (? & ? & ? & ? & ? & ? & Hsteps0 & Hlock' & ?); clarify.
  exploit forall_steps; try apply Hsteps0; eauto; intro.
  exploit distinct_steps; try apply Hsteps0; eauto; intro.
  rewrite app_assoc in Hcon.
  exploit critical_section; try apply Hlock'; try apply Hcon; eauto.
  { eapply init_steps, prog_steps; eauto. }
  { instantiate (1 := length li1); rewrite skipn_app, skipn_all, minus_diag;
      auto. }
  rewrite firstn_app, firstn_length, minus_diag, app_nil_r, <- app_assoc;
    auto.
Qed.
*)
(* With well-locked programs, if we're up to an unlock we should know we hold
   the lock. *)
Lemma unlock_locked : forall P0 l (Hdistinct : distinct P0)
  (Hlock : good_lock (l, 0) P0) (Hlock' : well_locked l P0)
  G0 lo lc P G (Hsteps : exec_star (Some P0) G0 lo lc (Some P) G)
  t li1 li2 (Hin : In (t, li1 ++ Unlock l :: li2) P)
  (Hlocked : Forall (fun i => i <> Lock l) li1)
  m (Hinit : initialized m (l, 0)) (Hcon : consistent (m ++ lc)),
  can_read (m ++ lc) (l, 0) (S t).
Proof.
  admit.
(*  intros until G; intro; rewrite exec_rev in Hsteps.
  remember (Some P0) as P1; remember (Some P) as P2; generalize dependent P;
    generalize dependent P0; induction Hsteps; clarify.
  - setoid_rewrite Forall_forall in Hlock'.
    exploit Hlock'; eauto; intros (Hgood & _).
    specialize (Hgood _ (nth_error_split _ _ _)).
    destruct Hgood as (j & ?); clarify.
    rewrite nth_error_app in *; clarify.
    exploit nth_error_in; eauto; intro.
    rewrite Forall_forall in Hlocked; exploit Hlocked; eauto; contradiction.
  - specialize (IHHsteps P0); clarify.
    specialize (IHHsteps _ eq_refl).
    exploit exec_result; eauto; intros (? & i & ? & ? & v & ? & Hresult).
    destruct (instr_result t i (G' t) v) as [((((?, ?), ?), ?), ?)|] eqn: Hi;
      clarify.
    rewrite app_assoc in Hcon; exploit consistent_app_SC; eauto; intro.
    rewrite <- exec_rev in Hsteps.
    assert (can_read (m ++ lc) (l, 0) (S t0) ->
      can_read (m ++ lc ++ opt_to_list c) (l, 0) (S t0)).
    { intro; exploit lock_hold; try apply Hcon; eauto.
      { eapply init_steps, prog_steps; eauto. }
      { eapply prog_step; eauto. }
      { exploit forall_steps; eauto; intro.
        eapply good_lock_ops; eauto.
        eapply exec_step'; eauto.
        * apply exec_refl.
        * rewrite app_nil_r; auto. }
      rewrite <- app_assoc; intro Hrel; clarify.
      destruct c; clarify.
      destruct i; clarify.
      exploit distinct_steps; eauto; intro.
      exploit distinct_step; eauto; intro.
      exploit distinct_in; [eauto | rewrite in_app; clarify | apply Hin |
        clarify].
      exploit well_locked_steps; eauto.
      { rewrite in_app; clarify. }
      intros (? & ? & ? & ? & ? & ? & ? & ? & ? & Hgood & ? & Hsteps0 & ?);
        clarify.
      exploit exec_keep'; try apply Hsteps0; eauto.
      { eapply distinct_steps; [apply Hdistinct | eauto]. }
      { rewrite in_app; clarify. }
      intros (n & Hskip).
      specialize (Hgood (S (length li1) + n)).
      rewrite <- skipn_nth, <- Hskip in Hgood; simpl in Hgood.
      use Hgood; [|apply nth_error_split].
      destruct Hgood as (j & ? & Hj & Hk); clarify.
      destruct (le_dec n j).
      { rewrite <- (Nat.sub_add n j) in Hj; auto.
        rewrite <- skipn_nth, <- Hskip in Hj.
        destruct (j - n) eqn: Hminus; clarify.
        rewrite nth_error_app in Hj; destruct (lt_dec n0 (length li1));
          [|omega].
        exploit nth_error_in; eauto; intro.
        rewrite Forall_forall in Hlocked; exploit Hlocked; eauto;
          contradiction. }
      specialize (Hk n); use Hk; [|omega].
      rewrite <- (plus_O_n n), <- skipn_nth, <- Hskip in Hk; clarify. }
    rewrite in_app in Hin; simpl in Hin; rewrite in_app in Hin.
    setoid_rewrite in_app in IHHsteps; simpl in IHHsteps.
    destruct Hin as [? | [? | [? | ?]]]; clarify; eauto.
    + specialize (IHHsteps t0 (i :: li1) li2); clarify.
      destruct (instr_eq_dec i (Lock l)); clarify.
      rewrite app_assoc; apply can_read_arwritten; auto.
    + destruct o0; clarify.
      destruct i; clarify.
      exploit well_locked_spawn; eauto.
      { rewrite in_app; clarify. }
      { simpl; eauto. }
      intros (Hgood & _).
      specialize (Hgood (length li1)); use Hgood; [|apply nth_error_split].
      destruct Hgood as (j & ? & Hj & Hk).
      rewrite nth_error_app in Hj; clarify.
      exploit nth_error_in; eauto; intro.
      rewrite Forall_forall in Hlocked; exploit Hlocked; eauto;
        contradiction.*)
Qed.
(*
Transparent minus.
      
Lemma protect_l : forall P0 (Hsafe : safe_locs P0)
  (Ht : Forall (fun e => fst e < zt) P0) P0' (Hsim : state_sim P0 P0')
  (Hdistinct : distinct P0') G0 lo lc P G
  (Hsteps : exec_star (Some P0') G0 lo lc (Some P) G)
  l (Hv : l < zl) (Hmeta : ~meta_loc (l, 0))
  (Hlock : good_lock (l, 0) P0') (Hlock' : well_locked l P0')
  m (Hinit : initialized m (l, 0)) (Hcon : consistent (m ++ lc))
  t i li (Hin : In (t, i :: li) P)
  (Haccess : exists o, accesses i = Some (L + l, o)),
  can_read (m ++ lc) (l, 0) (S t).
Proof.
  intros until m; intros ??; rewrite exec_rev in Hsteps.
  remember (Some P0') as P1; remember (Some P) as P2; generalize dependent P;
    generalize dependent P0'; induction Hsteps; clarify.
  - exploit in_split; eauto; clarify.
    exploit Forall2_app_inv_r; eauto; intros (? & ? & ? & Hrest & ?).
    inversion Hrest as [|(?, li') Hi]; inversion Hi; clarify.
    destruct li'; clarify.
    setoid_rewrite Forall_app in Hsafe; clarify.
    inversion Hsafe2 as [|?? Hsafe_i]; inversion Hsafe_i as [|?? Hsafei ?];
      clarify.
    exploit instrument_access; eauto; intros [[? ?] | [? [? | ?]]]; clarify.
    + rewrite Forall_app in Ht; clarify.
      inversion Ht2; clarify.
      exploit Hmetalocs_disjoint_CL; eauto; clarify.
    + contradiction Hsafei1; apply L_meta; auto.
    + exploit Hmetalocs_disjoint_LX; eauto; clarify.
  - rewrite app_assoc in Hcon; exploit consistent_app_SC; eauto; clarify.
    specialize (IHHsteps P0'); clarify.
    specialize (IHHsteps _ eq_refl).
    exploit exec_result; eauto; intros (Pa & i' & li' & Pb & v' & ? & Hresult).
    rewrite <- exec_rev in Hsteps.
    destruct (eq_dec t0 t).
    + subst.
      exploit step_into_instrument; eauto.
      { rewrite in_app; clarify. }
      intros (? & ? & ? & ? & n' & i2 & li2 & rest & ? & ? & ? & ? & Hi2 & ? &
        ? & ? & Hsafe_i & ?); clarify.
      exploit bounded_sim; eauto; intro.
      exploit bounded_steps; eauto; setoid_rewrite Forall_app.
      intros [? Ht']; inversion Ht'; clarify.
      exploit step_thread; eauto.
      { eapply distinct_steps; eauto. }
      { rewrite in_app; clarify. }
      clarify.
      exploit distinct_steps; eauto; intro.
      exploit distinct_step; eauto; intro.
      exploit distinct_in.
      { eauto. }
      { apply Hin. }
      { eauto. }
      intro Heq.
      destruct li2; clarify.
      { destruct rest; clarify.
        inversion Hsafe_i as [|?? Hsafei]; subst.
        exploit L_access; eauto.
        { destruct i0; auto; clarify. }
        { generalize (instrument_nonnil i0 t);
            destruct (instrument_instr i0 t); clarify. }
        destruct i0; try contradiction; clarify.
        * contradiction Hmeta; rewrite H11; apply L_meta; auto.
        * destruct zt; clarify.
          exploit Hmetalocs_disjoint_CL; eauto; contradiction. }
      assert (distinct x0).
      { eapply distinct_steps; [|eauto]; auto. }
      assert (S n' - length (instrument_instr i2 t) = 0) as Hn'.
      { destruct (lt_dec n' (length (instrument_instr i2 t))); [omega|].
        rewrite skipn_all in H2; [inversion H2 | simpl; omega]. }
      exploit L_access; eauto.
      { destruct i2; auto.
        exploit step_instr; try apply Hi2.
        { auto. }
        { eapply exec_step_inv; eauto. }
        { instantiate (1 := n'); rewrite skipn_app.
          simpl in Hn'; rewrite Hn'.
          simpl; erewrite skipn_cons; [|apply H2]; auto. }
        intros (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Hwait & ?).
        exploit exec_other_threads; try apply Hi2; eauto; intro.
        exploit distinct_steps; [|eapply exec_minus_exec; eauto|]; auto.
        exploit in_split; eauto; clarify.
        inversion Hwait; subst; exploit distinct_thread; eauto; clarify.
        exploit bounded_steps; try apply H1; auto; intro.
        exploit bounded_steps; [|eapply exec_minus_exec; eauto|]; auto.
        setoid_rewrite Forall_forall; intro Hbound; exploit Hbound; eauto;
          clarify. }
      { eapply skipn_in.
        setoid_rewrite H2; simpl; auto. }
      destruct i2; try contradiction; intro; subst; simpl in *.
      * exploit forall_steps; try apply H1; eauto; intro.
        rewrite <- app_assoc, <- app_assoc, app_assoc in Hcon.
        exploit critical_section; try apply Hcon; eauto.
        { eapply exec_step_inv; eauto. }
        { eapply init_steps, prog_steps; eauto. }
        { instantiate (1 := n').
          exploit skipn_cons; eauto; intro Heq.
          rewrite skipn_app, Heq, Hn'; simpl; auto. }
        repeat rewrite <- app_assoc; intro Hunlock; clarify.
        rewrite firstn_app, Hn' in Hunlock.
        rewrite in_app in Hunlock; clarify.
        exploit firstn_in; eauto; intro.
        exploit max_vc_instrs; eauto; clarify.
      * rewrite app_length, Nat.add_1_r in Hn'; simpl in Hn'.
        rewrite <- app_assoc; eapply unlock_locked; try apply Hlock.
        { auto. }
        { auto. }
        { rewrite app_assoc; eapply exec_step_inv; eauto. }
        { rewrite skipn_app, Hn' in H2; simpl in H2.
          instantiate (2 := skipn 1 (skipn n' (unlock_handler t l zt tmp1)));
            simpl.
          destruct (skipn n' (unlock_handler t l zt tmp1)) eqn: Hskip;
            clarify.
          assert (In (t, (i0 :: li2) ++ instrument rest t) P1) as Hin by auto.
          rewrite <- H11, <- app_assoc in Hin; eauto. }
        { rewrite Forall_forall; intros.
          exploit skipn_in; eauto; intro.
          exploit skipn_in; eauto; intro Hin'.
          setoid_rewrite in_app in Hin'; intro; destruct Hin'; clarify.
          exploit set_vc_instrs; eauto; clarify. }
        { auto. }
        { repeat rewrite <- app_assoc in Hcon; auto. }
    + destruct (instr_result t i' (G' t) v') as [((((?, ?), ?), ?), ?)|]
        eqn: Hi'; clarify.
      assert (In (t0, i :: li) (Pa ++ (t, i' :: li') :: Pb) ->
        can_read (m ++ lc ++ opt_to_list c) (l, 0) (S t0)).
      { intro; exploit IHHsteps; eauto; intro Hhold.
        exploit lock_hold; try apply Hcon; try apply Hhold.
        { eapply init_steps, prog_steps; eauto. }
        { eapply prog_step; eauto. }
        { eapply good_lock_ops.
          * eapply forall_steps; eauto.
          * eapply exec_step'; try apply exec_refl; eauto; clarsimp. }
        rewrite <- app_assoc; clarify.
        destruct c; clarify.
        inversion Hexec'; clarify.
        contradiction n; auto. }
      rewrite in_app in *; clarify.
      destruct Hin; clarify.
      rewrite in_app in *; clarify.
      destruct o0; clarify.
      destruct i'; clarify.
      exploit spawn_instrumented; eauto.
      { rewrite in_app; clarify. }
      { clarify. }
      intros (? & ? & Hsafe_i).
      destruct x0; clarify.
      inversion Hsafe_i as [|?? Hsafei]; subst.
      exploit instrument_access; eauto; intros [[? ?] | [? [? | ?]]]; clarify.
      * exploit bounded_sim; eauto; intro.
        exploit bounded_steps; eauto.
        setoid_rewrite Forall_app; intros [_ Ht'].
        inversion Ht' as [|?? [? Hi1]]; subst.
        inversion Hi1; unfold bounded_instr in *; clarify.
        exploit Hmetalocs_disjoint_CL; eauto; contradiction.
      * contradiction Hsafei1; apply L_meta; auto.
      * exploit Hmetalocs_disjoint_LX; eauto; contradiction.
Qed.

Lemma protect_l' : forall P0 (Hsafe : safe_locs P0)
  (Ht : Forall (fun e => fst e < zt) P0) P0' (Hsim : state_sim P0 P0')
  (Hdistinct : distinct P0') G0 lo0 lc0 P G
  (Hsteps : exec_star (Some P0') G0 lo0 lc0 (Some P) G)
  l (Hv : l < zl) (Hmeta : ~meta_loc (l, 0))
  (Hlock : good_lock (l, 0) P0') (Hlock' : well_locked l P0')
  m (Hinit : initialized m (l, 0))
  lo lc P' G' (Hsteps' : exec_star (Some P) G lo lc P' G')
  t (Hno_lock : Forall (fun a => a <> Acq t l) lc)
  (Hcon : consistent (m ++ lc0 ++ lc))
  a (Ha : In a lc) (Ht : thread_of a = t) (Haccess : fst (loc_of a) = L + l),
  can_read (m ++ lc0) (l, 0) (S t).
Proof.
  intros.
  remember (Some P) as P1; generalize dependent P; rewrite exec_rev in Hsteps'; 
    induction Hsteps'; clarify.
  rewrite Forall_app in Hno_lock; clarify.
  do 2 rewrite app_assoc in Hcon; exploit consistent_app_SC; eauto.
  rewrite <- app_assoc; intro.
  rewrite in_app in Ha; destruct Ha; [clarify; eauto|].
  exploit step_thread0; eauto; intros (? & ? & Hin).
  exploit distinct_steps; eauto; intro.
  rewrite <- exec_rev in Hsteps'; exploit distinct_steps; eauto;
    intro Hdistinct'.
  generalize (exec_accesses Hdistinct' Hexec' _ _ Hin); intro Hloc.
  exploit exec_star_trans; [apply Hsteps | apply Hsteps' | intro].
  destruct c; clarify; inversion Hno_lock2; clarify.
  exploit forall_steps; eauto; intro.
  exploit protect_l; eauto.
  { setoid_rewrite <- Hloc.
    destruct (loc_of a); eauto. }
  rewrite app_assoc; intro Hheld.
  exploit lock_hold'; try apply Hheld.
  - eapply init_steps, prog_steps; eauto.
  - rewrite <- app_assoc; auto.
  - eapply prog_steps; eauto.
  - eapply good_lock_ops; [|eauto].
    eapply forall_steps; [apply Hlock | eauto].
  - exploit exec_ops; eauto; simpl; intro Hthread.
    inversion Hthread; unfold beq in *; clarify.
    rewrite Forall_forall in Hno_lock1; exploit Hno_lock1; eauto; clarify.
Qed.

Lemma protect_lock : forall P0 (Hsafe : safe_locs P0)
  (Ht : Forall (fun e => fst e < zt) P0) P0' (Hsim : state_sim P0 P0')
  (Hdistinct : distinct P0') G0 lo0 lc0 P G
  (Hsteps : exec_star (Some P0') G0 lo0 lc0 (Some P) G)
  l (Hl : l < zl) (Hmeta : ~meta_loc (l, 0))
  (Hlock : good_lock (l, 0) P0') (Hlock2 : well_locked l P0')
  m (Hinit : initialized m (l, 0))
  t (Hheld : can_read (m ++ lc0) (l, 0) (S t))
  lo lc P' G' (Hsteps' : exec_star (Some P) G lo lc P' G')
  (Hno_lock : Forall (fun a => a <> Rel t l) lc)
  (Hcon : consistent (m ++ lc0 ++ lc)),
  Forall (fun a => forall o, loc_of a <> (L + l, o))
    (filter (fun x => negb (beq (thread_of x) t)) lc).
Proof.
  intros.
  remember (Some P) as P1; generalize dependent P; rewrite exec_rev in Hsteps'; 
    induction Hsteps'; clarify.
  rewrite Forall_app in Hno_lock.
  do 2 rewrite app_assoc in Hcon; exploit consistent_app_SC; eauto.
  rewrite <- app_assoc; clarify.
  specialize (IHHsteps' _ eq_refl).
  rewrite filter_app, Forall_app; clarify.
  rewrite Forall_forall; repeat intro.
  rewrite <- exec_rev in Hsteps'.
  rewrite app_assoc in H; exploit lock_hold; try apply H; eauto.
  { eapply init_steps, prog_steps; eauto. }
  { eapply prog_steps; eauto. }
  { exploit forall_steps; eauto; intro.
    eapply good_lock_ops; eauto. }
  intros [Hheld' | ?].
  exploit exec_star_trans; [apply Hsteps | apply Hsteps' | intro].
  exploit protect_self; eauto.
  { rewrite <- app_assoc in Hheld'; auto. }
  { eapply exec_step'; eauto.
    * apply exec_refl.
    * rewrite app_nil_r; auto. }
  { repeat rewrite <- app_assoc in *; auto. }
  intro Hlocked; destruct c; clarify.
  inversion Hlocked; clarify.
  assert (Forall (fun a => a <> Acq t0 l) [x]).
  { constructor; auto; intro; clarify. }
  exploit exec_ops; eauto.
  simpl; unfold beq; intro Hthread; inversion Hthread; clarify.
  exploit protect_l'; eauto.
  { eapply exec_step'; eauto.
    { apply exec_refl. }
    { rewrite app_nil_r; auto. } }
  { repeat rewrite <- app_assoc in *; auto. }
  { simpl; auto. }
  { rewrite H1; auto. }
  intro; exploit can_read_unique.
  { apply H. }
  { do 2 (eapply init_steps, prog_steps; eauto). }
  { apply Hheld'. }
  { rewrite <- app_assoc; eauto. }
  intro Heq; inversion Heq; unfold beq, negb in cond; clarify.
  { rewrite Forall_forall in Hno_lock1; exploit Hno_lock1; eauto. }
Qed.
*)
Lemma instrument_incom : forall i i' l l' t,
  instrument_instr i t ++ l = instrument_instr i' t ++ l' -> i' = i /\ l' = l.
Proof.
  generalize zt_non_zero; intros ??.
  eapply instr_ind' with (Q := fun l => forall l' t, instrument l t =
    instrument l' t -> l' = l)(i := i); clarify.
  - destruct i0; clarify; destruct i'; clarify; try (destruct x; clarify);
    try (destruct zt; clarify); try (destruct x0; clarify);
    try (repeat rewrite <- app_assoc in *; exploit app_eq_inv; eauto; clarify).
    repeat rewrite <- app_assoc in *; exploit app_eq_inv; eauto; clarify.
  - destruct i'; clarify; destruct zt; clarify; try (destruct x; clarify).
    repeat rewrite <- app_assoc in *; exploit app_eq_inv; eauto; clarify.
    exploit IHli; eauto; clarify.
  - destruct l'; clarify.
    exploit app_eq_nil; eauto; clarify; exploit instrument_nonnil; eauto;
      clarify.
  - destruct l'; clarify.
    + exploit app_eq_nil; eauto; clarify; exploit instrument_nonnil; eauto;
        clarify.
    + exploit IHi; eauto; clarify.
      exploit IHli; symmetry; eauto; clarify.
Qed.

(*
(* This should probably replace all other versions. *)
Lemma in_mops_set_vc'': forall n c vc1 vc2 vs t
  (Hin: In c (mops_set_vc vc1 vc2 n t vs)),
match c with
  | Read _ (x, o) _ => x = vc1 /\ o < n
  | Write _ (x, o) _ => x = vc2 /\ o < n
  | _ => False
end.
Proof.
  induction n; clarify.
  destruct vs; clarify.
  exploit IHn; eauto; destruct c; try destruct x; clarify.
Qed.

Lemma instrument_thread'' : forall P (Hsafe : safe_locs P) P1
  (Hsim : state_sim P P1) (Hdistinct : distinct P1)
  P1' G1 lo lc G1' (Hroot : exec_star (Some P1) G1 lo lc (Some P1') G1')
  t o c t' n P1'' G' (Hstep : exec P1' G1' t o (Some c) P1'' G')
  (Hloc : loc_of c = (C + t', n)) (Ht' : t' < zt),
  t' = t \/ exists P2 lo2 lc2 G2 i' n' rest lo2' lc2',
    exec_star (Some P1) G1 lo2 lc2 (Some P2) G2 /\
    In (t, instrument_instr i' t ++ instrument rest t) P2 /\
    In (t, skipn n' (instrument_instr i' t) ++ instrument rest t) P1' /\
    n' < length (instrument_instr i' t) /\
    exec_star (Some P2) G2 lo2' lc2' (Some P1') G1' /\
    match i' with Spawn u _ => t' = u | Wait u => t' = u /\ In (u, []) P1'
      | _ => False end.
Proof.
  intros.
  exploit exec_result; eauto; intros (P1a & i & li & P1b & v & ? & Hresult);
    subst.
  exploit step_into_instrument; eauto.
  { rewrite in_app; clarify. }
  intros (? & ? & ? & ? & n' & i' & ? & ? & ? & ? & ? & ? & ? & Hi' & ?);
    clarify.
  assert (In i (instrument [i'] t)) as Hi.
  { simpl; rewrite app_nil_r; eapply skipn_in.
    eapply nth_error_in; setoid_rewrite Hi'.
    instantiate (1 := 0); simpl; eauto. }
  exploit distinct_steps; eauto; intro.
  exploit instrument_own; try apply Hi; eauto.
  { rewrite <- exec_accesses; try apply Hstep; clarify; eauto.
    rewrite in_app; clarify. }
  intros [? | (i1 & ?)]; clarify.
  right; exists x; repeat eexists; eauto.
  - setoid_rewrite Hi'; rewrite in_app; clarify.
  - destruct (le_lt_dec (length (instrument_instr i1 t)) n'); auto.
    rewrite skipn_all in *; clarify.
  - destruct i1; clarify.
    destruct n'; clarify.
    exploit distinct_steps; try apply H0; auto; intro.
    exploit step_instr; eauto.
    { instantiate (1 := n'); rewrite skipn_app, Hi'.
      destruct (le_dec (length (wait_handler t t0 zt)) n').
      { rewrite skipn_all in Hi'; clarify. }
      destruct (n' - length (wait_handler t t0 zt)) eqn: Hminus; [|omega].
      rewrite in_app; simpl; auto. }
    intros (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Hminus' & Hwait & ?);
      clarify.
    exploit exec_other_threads; try apply Hminus'; eauto; intro.
    exploit distinct_steps; try eapply exec_minus_exec; eauto; intro.
    exploit in_split; eauto; clarify.
    inversion Hwait; subst; exploit distinct_thread; eauto; clarify.
    exploit exec_keep; eauto.
    { eapply exec_step; eauto. }
    intros (? & ?); rewrite skipn_nil in *; auto.
Qed.

Lemma protect_spawn : forall P0 (Hsafe : safe_locs P0)
  (Ht : Forall (fun e => fst e < zt) P0) P0' (Hsim : state_sim P0 P0')
  (Hdistinct : distinct P0') (Hspawns : safe_spawns P0') G0 lo0 lc0 P G
  (Hsteps : exec_star (Some P0') G0 lo0 lc0 (Some P) G)
  u (Hl : u < zt)
  lo lc P' G' (Hsteps' : exec_star (Some P) G lo lc (Some P') G')
  (Hout : Forall (fun e => fst e <> u /\
    forall li, ~In (Spawn u li) (snd e)) P'),
  Forall (fun a => forall o, loc_of a <> (C + u, o)) lc.
Proof.
  intros until G'; intro.
  remember (Some P) as P1; remember (Some P') as P2; generalize dependent P';
    generalize dependent P; rewrite exec_rev in Hsteps'; 
    induction Hsteps'; clarify.
  exploit exec_result; eauto; intros (? & i & li & ? & v & ? & Hresult).
  destruct (instr_result t i (G' t) v) as [((((?, ?), ?), ?), ?)|] eqn: Hi;
    clarify.
  specialize (IHHsteps' _ eq_refl _ eq_refl).
  rewrite Forall_app in *; clarify.
  inversion Hout2 as [|?? [Hu1 Hu2] Hu']; rewrite Forall_app in *; clarify.
  assert (forall li', ~In (Spawn u li') (i :: li)) as Hout_i.
  { simpl; intro; intros [? | ?]; [clarify | exploit Hu2; eauto].
    inversion Hu'1; clarify. }
  use IHHsteps'; clarify.
  rewrite Forall_forall; intros.
  intro; destruct c; clarify.
  rewrite <- exec_rev in Hsteps'.
  exploit instrument_thread''; try apply Hexec'; eauto.
  { eapply exec_star_trans; eauto. }
  intros [? | (? & ? & ? & ? & i' & n' & ? & ? & ? & ? & ? & Hin & ? & Hsteps2 &
    Hop)]; clarify.
  exploit distinct_steps; try apply Hsteps; eauto; intro.
  exploit distinct_steps; try apply Hsteps'; eauto; intro.
  exploit distinct_in; [eauto | rewrite in_app; clarify | apply Hin |
    intro Heq].
  destruct i'; auto; clarify.
  - rewrite skipn_app in Heq.
    rewrite app_length in *; simpl in *.
    destruct (n' - length (spawn_handler t t0 zt)) eqn: Hminus; [|omega].
    assert (In (Spawn t0 ((fix f p t1 := match p with [] => []
      | ins :: inss => instrument_instr ins t1 ++ f inss t1 end) li0 t0))
      (i :: li)).
    { rewrite Heq, in_app, in_app; simpl; auto. }
    simpl in *; eapply Hout_i; eauto.
  - rewrite Forall_forall in *.
    rewrite in_app in Hop2; destruct Hop2; clarify.
    + exploit Hout1; eauto; clarify.
    + exploit Hu'2; eauto; clarify.
Qed.    

Lemma has_spawn : forall u li li', In (Spawn u li') li ->
  spawns_list u li > 0.
Proof.
  induction li; clarify.
  destruct H; clarify.
  - unfold spawns; simpl; rewrite (spawns_list_def u); clarify.
  - exploit IHli; eauto; omega.
Qed.

Lemma has_spawn_thread : forall u P e, In e P ->
  spawn_count u P >= spawns_list u (snd e).
Proof.
  induction P; clarify.
  destruct a, H; clarify; [omega|].
  exploit IHP; eauto; omega.
Qed.

Lemma protect_spawn' : forall P0 (Hsafe : safe_locs P0)
  (Ht : Forall (fun e => fst e < zt) P0) P0' (Hsim : state_sim P0 P0')
  (Hdistinct : distinct P0') (Hspawns : safe_spawns P0') G0 lo0 lc0 P G
  (Hsteps : exec_star (Some P0') G0 lo0 lc0 (Some P) G)
  u (Hl : u < zt)
  lo lc P' G' (Hsteps' : exec_star (Some P) G lo lc (Some P') G')
  t li (Hin : In (t, li) P') li' (Hspawn : In (Spawn u li') li),
  Forall (fun a => forall o, loc_of a <> (C + u, o))
    (filter (fun x => negb (beq (thread_of x) t)) lc).
Proof.
  intros until G'; intro.
  remember (Some P) as P1; remember (Some P') as P2; generalize dependent P';
    generalize dependent P; rewrite exec_rev in Hsteps'; 
    induction Hsteps'; clarify.
  specialize (IHHsteps' _ eq_refl _ eq_refl).
  exploit exec_result; eauto; intros (? & i & ? & ? & v & ? & Hresult).
  destruct (instr_result t i (G' t) v) as [((((?, ?), ?), ?), ?)|] eqn: Hi;
    clarify.
  rewrite <- exec_rev in Hsteps'.
  rewrite filter_app, Forall_app; split.
  - rewrite in_app in Hin; simpl in Hin; rewrite in_app in Hin.
    setoid_rewrite in_app in IHHsteps'.
    destruct Hin as [? | [? | [? | ?]]]; clarify; eauto.
    + eapply IHHsteps'; eauto.
      simpl; eauto.
    + destruct o0; clarify.
      destruct i; clarify.
      exploit protect_spawn; eauto.
      { generalize (safe_spawns_steps Hspawns Hsteps); intro Hspawns1.
        generalize (safe_spawns_steps Hspawns1 Hsteps'); intro Hspawns'.
        specialize (Hspawns' u); rewrite spawn_count_app in Hspawns';
          simpl in Hspawns'.
        unfold spawns in Hspawns'; simpl in Hspawns';
          rewrite (spawns_list_def u) in Hspawns'.
        exploit has_spawn; eauto; intro.
        destruct (eq_dec t0 u); clarify; [omega|].
        rewrite Forall_forall; intros ? Hin; split.
        * intro; specialize (Hspawns'2 (snd x2)); destruct x2; clarify; omega.
        * intros ? Hin'.
          destruct (spawns_list u li); [omega|].
          simpl in *; rewrite <- plus_n_Sm in *.
          generalize (le_S_n _ _ Hspawns'1); intro.
          exploit has_spawn; eauto; intro.
          destruct (spawns_list u (snd x2)) eqn: Hn1; [omega|].
          rewrite in_app in Hin; simpl in Hin; destruct Hin as [? | [? | ?]].
          { exploit (has_spawn_thread u); eauto; setoid_rewrite Hn1; omega. }
          { clarify.
            destruct Hin' as [Hin' | ?]; [inversion Hin'; clarify|].
            exploit has_spawn; eauto; omega. }
          { exploit (has_spawn_thread u); eauto; setoid_rewrite Hn1; omega. } }
      apply Forall_filter.
  - rewrite Forall_forall; intros.
    destruct c; clarify; intro.
    generalize (safe_spawns_steps Hspawns Hsteps); intro Hspawns1.
    generalize (safe_spawns_steps Hspawns1 Hsteps'); intro Hspawns'.
    generalize (safe_spawns_step Hspawns' Hexec'); intro Hspawns''.
    specialize (Hspawns'' u); clarify.
    exploit instrument_thread''; try apply Hexec'; eauto.
    { eapply exec_star_trans; eauto. }
    intros [? | (? & ? & ? & ? & i' & n' & ? & ? & ? & Hsteps0 & ? & Hin2 & ?)].
    { subst; exploit Hspawns''2.
      { rewrite in_app; clarify. }
      exploit has_spawn; eauto; intros.
      exploit (has_spawn_thread t); eauto; simpl; omega. }
    destruct i'; clarify.
    + rewrite skipn_app in Hin2.
      rewrite app_length in *; simpl in *.
      assert (n' - length (spawn_handler t t1 zt) = 0) as Hzero by omega.
      rewrite Hzero in Hin2; simpl in Hin2.
      exploit distinct_steps; try apply Hsteps; auto; intro.
      exploit distinct_steps; try apply Hsteps'; auto; intro.
      exploit distinct_in; [eauto | rewrite in_app; clarify | apply Hin2
        | intro Heq].
      destruct (skipn n' (spawn_handler t t1 zt)) eqn: Hskip; clarify.
      rewrite spawn_count_app in Hspawns''1; simpl in Hspawns''1.
      repeat rewrite spawns_list_app in Hspawns''1; clarify.
      unfold spawns in Hspawns''1; simpl in Hspawns''1;
        rewrite (spawns_list_def t1) in Hspawns''1; clarify.
      do 2 ( rewrite <- plus_n_Sm in *; simpl in * ).
      generalize (le_S_n _ _ Hspawns''1); intro.
      assert (t0 <> t).
      { exploit exec_ops; eauto; simpl; intro Hx; inversion Hx; clarify.
        unfold negb, beq in *; clarify. }
      exploit has_spawn; eauto; intro.
      rewrite in_app in Hin; destruct Hin as [Hin | Hin]; clarify;
        generalize (has_spawn_thread t1 _ _ Hin); simpl; omega.
    + specialize (Hspawns''2 []); use Hspawns''2.
      exploit has_spawn; eauto; intro.
      generalize (has_spawn_thread t1 _ _ Hin); simpl; omega.
      { clear Hin Hin2; rewrite in_app in *; clarify; rewrite in_app; clarify. }
Qed.
*)
Definition waits t := instr_rect'' (fun _ => nat) _
  (fun i => match i with Wait u => if eq_dec u t then 1 else 0 | _ => 0 end)
  (fun _ _ r => r) 0 (fun _ _ r1 r2 => r1 + r2).

Fixpoint waits_list t li :=
  match li with
  | [] => 0
  | i :: rest => waits t i + waits_list t rest
  end.

Lemma waits_list_def : forall t li, instr_list_rect (fun _ => nat) _
  (fun i => match i with Wait u => if eq_dec u t then 1 else 0 | _ => 0 end)
  (fun _ _ r => r) 0 (fun _ _ r1 r2 => r1 + r2) li =
   waits_list t li.
Proof. induction li; clarify. Qed.

Fixpoint wait_count t (P : state) :=
  match P with
  | [] => 0
  | (_, li) :: rest => waits_list t li + wait_count t rest
  end.

Definition safe_waits P := forall t, wait_count t P <= 1.

Lemma wait_count_app : forall t P1 P2, wait_count t (P1 ++ P2) =
  wait_count t P1 + wait_count t P2.
Proof.
  induction P1; clarify.
  destruct a; clarify.
  rewrite IHP1; omega.
Qed.

Lemma safe_waits_step : forall P (Hwaits : safe_waits P)
  G t o c P' G' (Hstep : exec P G t o c (Some P') G'), safe_waits P'.
Proof.
  intros; intro t'; specialize (Hwaits t'); inversion Hstep; clarify;
    rewrite wait_count_app in *; clarify;
    try solve [generalize (Hwaits2 li); rewrite in_app in *; clarify;
    eapply Hwaits2; rewrite in_app; clarify]; try omega.
  unfold waits in Hwaits; simpl in Hwaits;
    rewrite (waits_list_def t') in *; omega.
Qed.
(*
Definition waiter t u := instr_rect'' _ (fun _ => tid -> Prop)
  (fun i => match i with Wait u' => fun t' => u' = u /\ t' = t
   | _ => fun _ => False end)
  (fun u _ r _ => r u) (fun _ => False) (fun _ _ r1 r2 t' => r1 t' \/ r2 t').

Lemma waiter_list_def : forall t u u' li t', waiter t u (Spawn u' li) t' <->
  Exists (fun i => waiter t u i u') li.
Proof.
  unfold waiter; induction li; split; clarify.
  - inversion H.
  - rewrite IHli in H; auto.
  - inversion H; clarify.
    rewrite IHli; auto.
Qed.

Definition t_waits t u P := exists e, In e P /\
  Exists (fun i => waiter t u i (fst e)) (snd e).

Lemma no_waiters : forall u i, waits u i = 0 -> forall t t', ~waiter t u i t'.
Proof.
  intros ??; eapply instr_ind' with (Q := fun l => waits_list u l = 0 ->
    forall t t', ~Exists (fun i => waiter t u i t') l)(i := i); clarify.
  - destruct i0; clarify.
    unfold waiter; unfold waits in *; intro; clarify.
  - unfold waits in *; clarify.
    rewrite (waits_list_def u) in *; rewrite (waiter_list_def t u); auto.
  - intro H; inversion H.
  - use IHi; [|omega].
    use IHli; [|omega].
    intro H1; inversion H1; [eapply IHi | eapply IHli]; eauto.
Qed.  

Corollary no_waiters_list : forall u li, waits_list u li = 0 ->
  forall t t', ~Exists (fun i => waiter t u i t') li.
Proof.
  induction li; clarify.
  { intro H; inversion H. }
  use IHli; [|omega].
  intro H1; inversion H1.
  - exploit no_waiters; eauto; omega.
  - eapply IHli; eauto.
Qed.

Lemma one_waiter : forall u i (Hsafe : waits u i <= 1) t', exists t,
  forall t1, waiter t1 u i t' -> t1 = t.
Proof.
  intros ??; eapply instr_ind' with (Q := fun l => waits_list u l <= 1 ->
    forall t', exists t, forall t1, Exists (fun i => waiter t1 u i t') l ->
    t1 = t) (i := i); clarify.
  - destruct i0; clarify; try solve [exists 0; clarify].
    exists t'; unfold waiter; clarify.
  - unfold waits in *; simpl in *; rewrite (waits_list_def u) in *; clarify.
    specialize (IHli u0); clarify.
    exists x; intros.
    rewrite (waiter_list_def t1 u) in *; auto.
  - exists 0; intros ? H1; inversion H1.
  - destruct (waits u i0) eqn: Hi; clarify.
    + specialize (IHli t'); clarify.
      exists x; intros ? H1; inversion H1; clarify.
      exploit no_waiters; eauto; contradiction.
    + use IHi; [|omega].
      specialize (IHi t'); clarify.
      exists x; intros ? H1; inversion H1; clarify.
      exploit no_waiters_list; eauto; omega.
Qed.      
    
Corollary one_waiter_list : forall u li (Hsafe : waits_list u li <= 1) t',
  exists t, forall t1, Exists (fun i => waiter t1 u i t') li -> t1 = t.
Proof.
  induction li; clarify.
  { exists 0; intros; inversion H. }
  destruct (waits u a) eqn: Ha; clarify.
  - specialize (IHli t'); clarify.
    exists x; intros ? H; inversion H; clarify.
    exploit no_waiters; eauto; contradiction.
  - generalize (one_waiter u a); intro H; clarify.
    use H; [|omega].
    specialize (H t'); clarify.
    exists x; intros ? H1; inversion H1; clarify.
    exploit no_waiters_list; eauto; omega.
Qed.  

Lemma safe_waits_cons : forall e P, safe_waits (e :: P) -> safe_waits P.
Proof.
  repeat intro.
  specialize (H t); clarify.
  destruct e; omega.
Qed.

Lemma no_waiters' : forall u P (Hnone : wait_count u P = 0) t, ~t_waits t u P.
Proof.
  induction P; unfold t_waits; repeat intro; clarify.
  destruct a; use IHP; [|omega].
  destruct H1; clarify.
  - exploit no_waiters_list; eauto; omega.
  - eapply IHP.
    unfold t_waits; eauto.
Qed.

Lemma one_waiter' : forall P (Hsafe : safe_waits P) u, exists t,
  forall t', t_waits t' u P -> t' = t.
Proof.
  induction P; unfold t_waits; clarify.
  { exists 0; clarify. }
  generalize (safe_waits_cons Hsafe); clarify.
  specialize (Hsafe u); simpl in Hsafe.
  destruct a.
  destruct (waits_list u l) eqn: Hl; clarify.
  - specialize (IHP u); clarify.
    exists x; clarify.
    destruct H01; clarify.
    + exploit no_waiters_list; eauto; contradiction.
    + apply IHP; unfold t_waits; eauto.
  - exploit (one_waiter_list u l); [omega|].
    instantiate (1 := t).
    intros (x & Hx); exists x; clarify.
    assert (wait_count u P = 0) by omega.
    exploit no_waiters'; eauto; [|contradiction].
    unfold t_waits; eauto.
Qed.

Lemma t_waits_step : forall P G t o c P' G'
  (Hstep : exec P G t o c (Some P') G')
  t' u (Hwait : t_waits t' u P'), t_waits t' u P.
Proof.
  unfold t_waits; clarify.
  exploit exec_result; eauto; intros (? & i & ? & ? & v & ?); clarify.
  destruct (instr_result t i (G t) v) as [((((?, ?), ?), ?), ?)|] eqn: Hi;
    clarify.
  rewrite in_app in Hwait1; simpl in Hwait1; rewrite in_app in Hwait1.
  setoid_rewrite in_app.
  destruct Hwait1 as [? | [? | [? | ?]]]; clarify; eauto.
  - do 2 eexists; eauto; clarify.
  - destruct o0; clarify.
    destruct i; clarify.
    do 2 eexists; eauto; clarify.
    constructor; rewrite (waiter_list_def t' u); auto.
Qed.    

Corollary t_waits_steps : forall P G lo lc P' G'
  (Hsteps : exec_star (Some P) G lo lc (Some P') G')
  t u (Hwait : t_waits t u P'), t_waits t u P.
Proof.
  intros; remember (Some P) as P1; remember (Some P') as P2;
    generalize dependent P'; generalize dependent P; induction Hsteps; clarify.
  destruct P'; [|inversion Hsteps].
  exploit IHHsteps; eauto.
  eapply t_waits_step; eauto.
Qed.

Corollary unique_wait : forall P (Hsafe : safe_waits P) u, exists t,
  forall G lo lc P' G' (Hsteps : exec_star (Some P) G lo lc (Some P') G')
  t' li (Hwait : In (t', Wait u :: li) P'), t' = t.
Proof.
  intros.
  exploit one_waiter'; eauto; intros (t & Ht); exists t; clarify.
  exploit t_waits_steps; eauto.
  do 2 eexists; eauto; clarify.
  constructor; unfold waiter; clarify.
Qed.    
    
Lemma protect_wait : forall P0 (Hsafe : safe_locs P0)
  (Ht : Forall (fun e => fst e < zt) P0) P0' (Hsim : state_sim P0 P0')
  (Hdistinct : distinct P0') (Hspawns : safe_spawns P0')
  (Hwaits : safe_waits P0') G0 lo0 lc0 P G
  (Hsteps : exec_star (Some P0') G0 lo0 lc0 (Some P) G)
  u (Hdone : In (u, []) P)
  lo lc P' G' (Hsteps' : exec_star (Some P) G lo lc P' G')
  t li (Hin : In (t, Wait u :: li) P),
  Forall (fun a => forall o, loc_of a <> (C + u, o))
    (filter (fun x => negb (beq (thread_of x) t)) lc).
Proof.
  intros; remember (Some P) as P1; rewrite exec_rev in Hsteps';
    induction Hsteps'; clarify.
  rewrite filter_app, Forall_app; clarify.
  exploit exec_result; eauto; intros (? & i & ? & ? & v & ? & Hresult).
  destruct (instr_result t0 i (G' t0) v) as [((((?, ?), ?), ?), ?)|] eqn: Hi;
    clarify.
  rewrite <- exec_rev in Hsteps'.
  rewrite Forall_forall; intros.
  destruct c; clarify; intro.
  exploit distinct_steps; eauto; intro.
  exploit exec_keep; try apply Hdone; eauto; intros (? & Hdone').
  rewrite skipn_nil in Hdone'; clarify.
  exploit instrument_thread''; try apply Hexec'; eauto.
  { eapply exec_star_trans; eauto. }
  { exploit bounded_sim; eauto; intro.
    exploit bounded_steps; eauto; intro Hu.
    setoid_rewrite Forall_forall in Hu; specialize (Hu _ Hdone); clarify. }
  intros [? | (? & ? & ? & ? & i' & n' & ? & ? & ? & ? & ? & Hin' & ?)].
  { exploit distinct_steps; eauto; intro; subst.
    exploit distinct_in; [eauto | rewrite in_app; clarify | eauto | clarify]. }
  destruct i'; clarify.
  - generalize (safe_spawns_steps Hspawns Hsteps); intro Hspawns1.
    generalize (safe_spawns_steps Hspawns1 Hsteps'); intro Hspawns'.
    specialize (Hspawns' t1); clarify.
    specialize (Hspawns'2 []); clarify.
    rewrite skipn_app in Hin'.
    rewrite app_length in *; simpl in *.
    assert (n' - length (spawn_handler t0 t1 zt) = 0) as Hzero by omega.
    rewrite Hzero in Hin'; simpl in Hin'.
    generalize (has_spawn_thread t1 _ _ Hin'); simpl.
    repeat rewrite spawns_list_app; clarify.
    unfold spawns in *; clarify; rewrite (spawns_list_def t1) in *; omega.
  - assert (t0 <> t).
    { exploit exec_ops; eauto; simpl; intro Hx; inversion Hx; clarify.
      unfold negb, beq in *; clarify. }
    exploit unique_wait; eauto; intros (t' & Ht').
    exploit Ht'; try apply Hin; eauto; clarify.
    exploit Ht'; try apply H2; eauto.
  - inversion Hexec'; clarify.
Qed.
*)
Definition lock_instr l := instr_rect'' (fun _ => Prop) _
  (fun i => match i with Lock m | Unlock m => m = l | _ => False end)
  (fun _ _ r => r) False (fun _ _ r1 r2 => r1 \/ r2).

Lemma lock_list_iff : forall x u li, lock_instr x (Spawn u li) <->
  Exists (lock_instr x) li.
Proof.
  unfold lock_instr; induction li; split; clarify.
  - inversion H.
  - apply Exists_cons_tl, IHli; auto.
  - inversion H; clarify.
    right; apply IHli; auto.
Qed.  

Definition locks x (P : state) := exists e, In e P /\
  Exists (lock_instr x) (snd e).

Corollary instr_in_step_rev : forall P G t o c P' G'
  (Hstep : exec P G t o c (Some P') G')
  t' li i (Hin : In (t', li) P') (Hi : In i li),
  (exists li', In (t', li') P /\ In i li') \/
  exists li', In (t, Spawn t' li :: li') P.
Proof.
  intros.
  exploit in_step_rev; eauto; intros [? | [? | ?]]; clarify; eauto.
  left; do 2 eexists; eauto; clarify.
Qed.
  
Lemma locks_steps : forall l P G lo lc P' G'
  (Hsteps : exec_star (Some P) G lo lc (Some P') G') (Hlocks : locks l P'),
  locks l P.
Proof.
  intros until G'; intro; remember (Some P) as Pa; remember (Some P') as Pb;
    generalize dependent P'; generalize dependent P; rewrite exec_rev in Hsteps;
    induction Hsteps; clarify.
  eapply IHHsteps; eauto.
  unfold locks; destruct Hlocks as ((?, ?) & ? & He).
  exploit in_step_rev; eauto; intros [? | [? | ?]]; clarify; eauto.
  - do 2 eexists; eauto.
    apply Exists_cons_tl; auto.
  - do 2 eexists; eauto.
    constructor; rewrite (lock_list_iff l); auto.
Qed.

Corollary locks_spec : forall l P G lo lc P' G'
  (Hsteps : exec_star (Some P) G lo lc (Some P') G') t li (Hin : In (t, li) P')
  (Hlock : In (Lock l) li \/ In (Unlock l) li), locks l P.
Proof.
  intros; eapply locks_steps; eauto.
  do 2 eexists; eauto.
  rewrite Exists_exists; destruct Hlock; do 2 eexists; eauto;
    unfold lock_instr; clarify.
Qed.

Lemma list_fresh_iff : forall v li, (fix list_fresh l :=
  match l with [] => True | i :: rest => fresh v i /\ list_fresh rest end) li
  <-> Forall (fresh v) li.
Proof.
  induction li; split; clarify; rewrite IHli in *; clarify.
  inversion H; clarify.
Qed.

Lemma fresh_result : forall Pa t i li Pb
  (Hfresh : fresh_tmps (Pa ++ (t, i :: li) :: Pb)) G v th o c G' f
  (Hresult : instr_result t i (G t) v = Some (th, o, c, G', f)),
  fresh_tmps (Pa ++ (t, li) :: opt_to_list th ++ Pb).
Proof.
  unfold fresh_tmps; intros.
  rewrite Forall_app in *; clarify.
  inversion Hfresh2 as [|?? Hi]; inversion Hi; constructor; auto.
  rewrite Forall_app; clarify.
  destruct th; clarify.
  destruct i; clarify.
  constructor; auto.
  simpl; rewrite Forall_and.
  do 2 rewrite <- (list_fresh_iff); auto.
Qed.  

Lemma safe_result : forall Pa t i li Pb
  (Hsafe : safe_locs (Pa ++ (t, i :: li) :: Pb)) G v th o c G' f
  (Hresult : instr_result t i (G t) v = Some (th, o, c, G', f)),
  safe_locs (Pa ++ (t, li) :: opt_to_list th ++ Pb).
Proof.
  unfold safe_locs; intros.
  rewrite Forall_app in *; clarify.
  inversion Hsafe2 as [|?? Hi]; inversion Hi; constructor; auto.
  rewrite Forall_app; clarify.
  destruct th; clarify.
  destruct i; clarify.
  constructor; auto.
  rewrite safe_instrs in *; auto.
Qed.

Fixpoint instrument_prog P :=
  match P with
  | [] => []
  | (t, li) :: rest => (t, instrument li t) :: instrument_prog rest
  end.

Lemma instrumented : forall P, state_sim P (instrument_prog P).
Proof.
  induction P.
  - constructor.
  - destruct a; simpl; constructor; clarify.
Qed.

Lemma instrumented_iff : forall P1 P2, state_sim P1 P2 <->
  P2 = instrument_prog P1.
Proof.
  split; clarify; [|apply instrumented; auto].
  induction H; clarify.
  destruct x, y; clarify.
Qed.

(* We should be able to prove that most of these well-formedness conditions
   transfer over from the uninstrumented program, though I doubt we can prove
   they hold automatically. *)

Lemma sim_suffix : forall P P', state_sim P P' -> state_suffix P P'.
Proof.
  admit.
(*  intros; induction H; constructor; auto.
  destruct x, y; clarify.
  exists 0; clarify.
  generalize (instrument_length (hd (Assign 0 (I 0)) p) t0); omega.*)
Qed.

Lemma spawn_in_handler' : forall u li i t n
  (Hnth : nth_error (instrument_instr i t) n = Some (Spawn u li)),
  exists li', i = Spawn u li' /\ li = instrument li' u /\
  n = length (instrument_instr i t) - 1.
Proof.
  intros.
  exploit nth_error_in; eauto; intro.
  exploit spawn_in_handler; eauto; clarify.
  repeat eexists; eauto.
  rewrite nth_error_app in Hnth.
  destruct (lt_dec n (length (spawn_handler t u zt))).
  - unfold spawn_handler in Hnth; rewrite nth_error_app in Hnth.
    destruct (lt_dec n (length (max_vc (C + t) (C + u) zt tmp1 tmp2)));
      exploit nth_error_in; eauto; clarify.
    exploit max_vc_instrs; eauto; clarify.
  - rewrite nth_error_single in *; clarify.
    rewrite app_length; simpl; omega.
Qed.

Lemma distinct_threads : forall P P' (Hsuffix : state_suffix P P') t,
  In t (map fst P) <-> In t (map fst P').
Proof.
  intros; induction Hsuffix; [reflexivity|].
  destruct x, y; clarify.
  rewrite IHHsuffix; reflexivity.
Qed.

Lemma distinct_suffix : forall P P' (Hsuffix : state_suffix P P'),
  distinct P <-> distinct P'.
Proof.
  intros; induction Hsuffix; [reflexivity|].
  unfold distinct; destruct x, y; clarify.
  exploit distinct_threads; eauto.
  instantiate (1 := t); intro Hin.
  split; intro H; inversion H; subst; constructor.
  - rewrite <- Hin; auto.
  - rewrite <- IHHsuffix; auto.
  - rewrite Hin; auto.
  - rewrite IHHsuffix; auto.
Qed.
(*
Lemma sim_thread : forall P P1 P2 (Hsim : state_sim P P1)
  (Hdistinct : distinct P1) G1 lo lc G2
  (Hsteps : exec_star (Some P1) G1 lo lc (Some P2) G2) t li
  (Hin : In (t, li) P2),
  (exists li0, In (t, li0) P /\
   In (t, instrument li0 t) P1 /\
   exists n', n' < length (instrument_instr (hd (Assign 0 (I 0)) li0) t) /\
     li = skipn n' (instrument li0 t)) \/
  (exists t0 i rest n', In (t0, instrument_instr i t0 ++ rest) P1 /\
     In (t0, skipn n' rest) P2).
Proof.
  intros.
  exploit in_steps_rev2; eauto; intros [(li1 & ?) | Hspawn].
  - exploit Forall2_in2; eauto; intros ((? & li0) & ? & ? & Heq);
      clarify.
    exploit app_eq_skip; eauto; clarify.
    destruct (le_gt_dec (length (instrument_instr (hd (Assign 0 (I 0)) li0) t))
      (length li1)).
    + right; destruct li0; clarify.
      { rewrite skipn_nil in *.
        destruct li1; clarify; omega. }
      rewrite Heq in H; repeat eexists; eauto.
      rewrite skipn_app, skipn_all in Hin; [eauto | omega].
    + left; rewrite Heq in *; exists li0; clarify.
      repeat eexists; eauto.
  - right; destruct Hspawn as (Hout & ? & ? & ? & ? & t1 & t' & li' & rest &
      li2 & ? & ? & ? & ? & ? & ? & Hspawn & Hsteps' & ?); clarify.
    exploit Forall2_in2; eauto; intros ((?, li1) & ? & ? & Heq).
    destruct li1; clarify.
    { destruct li2; clarify. }
    simpl in *; rewrite Heq in *.
    assert (exists n, rest = skipn n (instrument li1 t1)) as (n' & ?).
    { rewrite split_app in Heq.
      destruct (le_gt_dec (length (li2 ++ [Spawn t' li']))
        (length (instrument_instr i t1))).
      * exploit app_eq_inv_ge; eauto; intros (? & ? & Heq1).
        exploit spawn_in_handler'.
        { setoid_rewrite Heq1.
          rewrite <- app_assoc; simpl; apply nth_error_split. }
        intros (? & ? & ? & Hlen); subst.
        symmetry in Heq1; generalize (app_eq_skip _ _ Heq1).
        rewrite app_length, skipn_all; [exists 0; clarify|].
        rewrite Hlen; simpl; omega.
      * symmetry in Heq; exploit app_eq_inv_ge; try apply Heq; [omega|].
        intros (? & Hrest & ?).
        symmetry in Hrest; generalize (app_eq_skip _ _ Hrest); eauto. }
    subst.
    inversion Hspawn; clarify.
    exploit distinct_steps; eauto; intro.
    exploit distinct_in.
    { eauto. }
    { rewrite in_app; clarify. }
    { eauto. }
    clarify.
    exploit exec_keep; try apply Hsteps'.
    { eapply distinct_step; eauto. }
    { rewrite in_app; right; simpl; left; eauto. }
    clarify; rewrite skipn_skipn in *; repeat eexists; eauto.
Qed.    

Corollary sim_thread1 : forall P P1 P2 (Hsim : state_sim P P1)
  (Hdistinct : distinct P1) G1 lo lc G2
  (Hsteps : exec_star (Some P1) G1 lo lc (Some P2) G2),
  Forall (fun (e : tid * list instr) => let (t, li) := e in
    exists li0, In (t, li0) P /\ exists n,
    n < length (instrument_instr (hd (Assign 0 (I 0)) li0) t) /\
    li = skipn n (instrument li0 t)) P2 \/ exists t i rest n',
    In (t, instrument_instr i t ++ rest) P1 /\ In (t, skipn n' rest) P2.
Proof.
  intros.
  remember P2 as P'.
  assert (Forall (fun (e : tid * list instr) => let (t, li) := e in
    (exists li0, In (t, li0) P /\ In (t, instrument li0 t) P1 /\
     exists n', n' < length (instrument_instr (hd (Assign 0 (I 0)) li0) t)
      /\ li = skipn n' (instrument li0 t)) \/
    (exists t0 i rest n', In (t0, instrument_instr i t0 ++ rest) P1 
      /\ In (t0, skipn n' rest) P2)) P').
  { rewrite Forall_forall; intros (t, li); subst; eapply sim_thread; eauto. }
  setoid_rewrite HeqP' at 2.
  assert (incl P' P2) as Hincl by (subst; apply incl_refl).
  clear Hsteps HeqP'; induction P'; auto.
  inversion H as [|?? Ha]; clear H; clarify.
  generalize (incl_cons_inv Hincl); clarify.
  destruct a as (t, li); destruct Ha as [(li0 & n & Hli0) | ?];
    [|clarify; right; repeat eexists; eauto].
  clarify; left; constructor; eauto.
Qed.

Lemma sim_next_thread : forall P P1 P2 (Hsim : state_sim P P1)
  (Hdistinct : distinct P1) G1 lo lc G2
  (Hsteps : exec_star (Some P1) G1 lo lc (Some P2) G2),
  state_suffix P P2 \/ exists t i rest n',
    In (t, instrument_instr i t ++ rest) P1 /\ In (t, skipn n' rest) P2.
Proof.
  intros.
  exploit sim_thread1; eauto; clarify; left.
  remember (Some P1) as Pa; remember (Some P2) as Pb; generalize dependent P2;
    rewrite exec_rev in Hsteps; induction Hsteps; clarify.
  { apply sim_suffix; auto. }
  rewrite <- exec_rev in Hsteps; specialize (IHHsteps _ eq_refl).
  exploit exec_result; eauto.
  intros (? & i & ? & ? & v & ? & Hresult).
  destruct (instr_result t i (G' t) v) as [((((?, ?), ?), ?), ?)|] eqn: Hi;
    clarify.
  destruct o0; clarify.
  { destruct i; clarify.
    rewrite Forall_app in H; clarify.
    inversion H2 as [|??? Ht0]; clarify.
    inversion Ht0 as [|(?, ?) ? (? & Hin0 & ?)]; clarify.
    contradiction Hresult2222.
    exploit Forall2_in1; try apply Hin0; eauto; intros ((?, ?) & Hin1 & ?);
      clarify.
    exploit exec_keep; eauto; clarify.
    rewrite in_map_iff; repeat eexists; eauto; clarify. }
  rewrite Forall_app in *; clarify.
  inversion H2 as [|?? Ht]; subst.
  destruct Ht as (li0 & ? & n' & ?); clarify.
  use IHHsteps.
  - exploit Forall2_app_inv_r; eauto; intros (? & ? & ? & Hrest & ?); subst.
    inversion Hrest as [|(?, ?)]; clarify.
    apply Forall2_app; auto; constructor; clarify.
    rewrite <- (distinct_suffix (sim_suffix Hsim)) in Hdistinct.
    exploit distinct_in.
    { eauto. }
    { eauto. }
    { rewrite in_app; clarify. }
    clarify; eauto.
  - constructor; auto.
    do 2 eexists; eauto.
    exploit Forall2_in1; eauto; intros ((?, ?) & Hin1 & ?); clarify.
    exploit exec_mono; eauto.
    { rewrite in_app; clarify. }
    intros (n2 & Hskip).
    destruct n'; [exploit skip_cons_neq; eauto; contradiction|].
    exists n'; split; [omega|].
    erewrite (skipn_n n'); eauto.
    assert (n2 = n').
    { assert (length (i :: skipn (S n') (instrument li0 t0)) =
        length (skipn n2 (instrument li0 t0))) by (rewrite Hskip; auto).
      remember (S n') as n0; simpl in *; repeat rewrite skipn_length in *.
      destruct li0; clarify.
      rewrite app_length in *; omega. }
    rewrite <- (plus_O_n n'), <- skipn_nth; subst.
    rewrite <- Hskip; clarify.
Qed.*)

Lemma state_sim_inv' : forall P2a P1 P2b t li'
  (Hsim : state_sim P1 (P2a ++ (t, li') :: P2b))
  (Hdistinct : distinct (P2a ++ (t, li') :: P2b)),
  exists P1a li P1b, P1 = (P1a ++ (t, li) :: P1b) /\
  state_sim P1a P2a /\ state_sim P1b P2b /\ li' = instrument li t.
Proof.
  induction P2a; clarify.
  - inversion Hsim as [|(?, ?)]; clarify.
    exists []; repeat eexists; auto; constructor.
  - inversion Hsim as [|(?, ?) ???? Hrest]; clarify.
    specialize (IHP2a _ _ _ _ Hrest).
    inversion Hdistinct; clarify.
    repeat eexists; eauto; try constructor; eauto; clarify.
Qed.

Lemma state_suffix_inv' : forall P2a P1 P2b t li'
  (Hsuffix : state_suffix P1 (P2a ++ (t, li') :: P2b))
  (Hdistinct : distinct (P2a ++ (t, li') :: P2b)),
  exists P1a li P1b n, P1 = (P1a ++ (t, li) :: P1b) /\
  state_suffix P1a P2a /\ state_suffix P1b P2b /\
  li' = skipn n (instrument li t) /\
  n < length (instrument_instr (hd (Assign 0 (I 0)) li) t).
Proof.
  induction P2a; clarify.
  - inversion Hsuffix as [|(?, ?)]; clarify.
    exists []; repeat eexists; auto; constructor.
  - inversion Hsuffix as [|(?, ?) ???? Hrest]; clarify.
    specialize (IHP2a _ _ _ _ Hrest).
    inversion Hdistinct; clarify.
    repeat eexists; eauto; try constructor; clarify; eauto.
Qed.

Lemma state_suffix_alt : forall P P1, state_suffix P P1 <->
  (forall n t li (Hn : nth_error P n = Some (t, li)),
    exists li1, nth_error P1 n = Some (t, li1) /\ exists n',
    n' < length (instrument_instr (hd (Assign 0 (I 0)) li) t) /\
    li1 = skipn n' (instrument li t)) /\
  (forall n t li1 (Hn : nth_error P1 n = Some (t, li1)), exists li,
    nth_error P n = Some (t, li)).
Proof.
  induction P; intros.
  - split; intro H; [inversion H|]; clarify.
    + split; clarsimp.
    + destruct P1; [constructor | clarify].
      destruct p as (t, li).
      specialize (H2 0 t li); clarify.
  - split; intro H; clarify.
    + inversion H as [|(?, ?) (?, ?) ??? Hsuffix]; clarify.
      rewrite IHP in Hsuffix; clarify.
      split; intros.
      * destruct n; clarify; eauto.
      * destruct n; clarify; eauto.
    + destruct a as (t, li).
      generalize (H1 0 t li); clarify.
      destruct P1; clarify.
      constructor; eauto.
      rewrite IHP; split; clarify.
      * specialize (H1 (S n) t0 li0); clarify; eauto.
      * specialize (H2 (S n) t0 li1); clarify; eauto.
Qed.
(*
(* Next time, consider using a map. *)
Lemma state_suffix_inter : forall P P1 (Hsim : state_suffix P P1)
  (Hdistinct : distinct P1)
  G1 lo1 lc1 P2 G2 (Hsteps1 : exec_star (Some P1) G1 lo1 lc1 (Some P2) G2)
  lo2 lc2 P3 G3 (Hsteps2 : exec_star (Some P2) G2 lo2 lc2 (Some P3) G3)
  (Hsuffix : state_suffix P P3), state_suffix P P2.
Proof.
  intros until G2; intro; remember (Some P1) as Pa; remember (Some P2) as Pb;
    generalize dependent P1; induction Hsteps1; clarify.
  destruct P'; [|inversion Hsteps1].
  assert (state_suffix P s -> state_suffix P P2) as IH.
  { intro; eapply IHHsteps1; eauto.
    eapply distinct_step; eauto. }
  clear IHHsteps1.
  exploit exec_result; eauto; intros (? & i & ? & ? & v & ?); clarify.
  destruct (instr_result t i (G t) v) as [((((?, ?), ?), ?), ?)|] eqn: Hi;
    clarify.
  exploit state_suffix_inv'; eauto; intros (? & li0 & ? & n & ?); clarify.
  destruct li0; [rewrite skipn_nil in *|]; clarify.
  rewrite skipn_app' in *; [|omega].
  destruct (skipn n (instrument_instr i0 t)) eqn: Hskip; clarify.
  { rewrite skipn_all_iff in Hskip; omega. }
  destruct l; clarify.
  - exploit distinct_step; eauto; intro.
    exploit exec_keep; eauto; [apply split_in | clarify].
    exploit distinct_steps; eauto; intro.
    exploit exec_keep; eauto; intros (? & Hin').
    rewrite skipn_skipn in *.
    exploit Forall2_in1; try apply Hsuffix; [apply split_in|].
    intros ((?, ?) & ?); clarify.
    exploit distinct_steps; eauto; intro.
    exploit distinct_in; [eauto | apply Hin' | eauto|].
    rewrite skipn_app'; [|omega].
    intro Hskips.
    pose proof (eq_refl (length (skipn (x0 + x4) (instrument li0 t)))) as Hlen.
    rewrite Hskips in Hlen at 1; rewrite app_length in Hlen;
      repeat rewrite skipn_length in Hlen; omega.
  - apply IH; clear IH.
    destruct o0; clarify.
    { destruct i1; clarify.
      exploit spawn_in_handler'.
      { rewrite <- skipn_nth; setoid_rewrite Hskip.
        instantiate (3 := 0); simpl; eauto. }
      clarify.
      rewrite app_length in Hskip; simpl in Hskip.
      rewrite Nat.add_sub, skipn_app', skipn_length' in Hskip; clarify. }
    apply Forall2_app; [|constructor]; clarify.
    exists (S n); rewrite skipn_app'; [|omega].
    split.
    + eapply nth_error_lt.
      rewrite <- Nat.add_1_l, <- skipn_nth, Hskip; simpl; eauto.
    + erewrite skipn_n in Hskip;
        [|rewrite <- (plus_O_n n), <- skipn_nth, Hskip; simpl; eauto].
      inversion Hskip as [Heq]; simpl; rewrite Heq; auto.
Qed.  
*)
Corollary state_suffix_inv : forall P P1 (Hsim : state_sim P P1)
  (Hdistinct : distinct P1)
  G1 lo1 lc1 P2 G2 (Hsteps1 : exec_star (Some P1) G1 lo1 lc1 (Some P2) G2)
  lo2 lc2 P3 G3 (Hsteps2 : exec_star (Some P2) G2 lo2 lc2 (Some P3) G3)
  (Hsuffix : state_suffix P P3), state_suffix P P2.
Proof.
  admit.
(*  intros; eapply state_suffix_inter with (P3 := P3); try apply sim_suffix, Hsim;
    eauto.*)
Qed.
(*
Lemma upd_overwrite1 : forall A B (A_eq : EqDec_eq A) (f : A -> B) t v1 v2,
  upd (upd f t v1) t v2 = upd f t v2.
Proof.
  intros; extensionality x; unfold upd; clarify.
Qed.

Lemma upd_assoc1 : forall A B (A_eq : EqDec_eq A) (f : A -> B) t1 t2 v1 v2
  (Hdiff : t1 <> t2), upd (upd f t1 v1) t2 v2 = upd (upd f t2 v2) t1 v1.
Proof.
  intros; extensionality x; unfold upd; clarify.
Qed.

Lemma upd_three : forall G t a1 a2 v1 v2 v1' (Hdiff : a1 <> a2),
  upd_env (upd_env (upd_env G t a1 v1) t a2 v2) t a1 v1' =
  upd_env (upd_env G t a1 v1') t a2 v2.
Proof.
  intros; rewrite upd_assoc, upd_overwrite; auto.
Qed.

Lemma hb_check_exec : forall t z P G lo lc P' G' (Hdistinct : distinct P)
  li src tgt
  Pa Pb (HP : P = Pa ++ (t, hb_check src tgt z tmp1 tmp2 ++ li) :: Pb)
  (Ht : exec_star_t t (Some P) G lo lc (Some P') G') (Hin' : In (t, li) P'),
  exists vs1 vs2, lo = events_hb_check src tgt vs1 vs2 t /\
    lc = mops_hb_check src tgt vs1 vs2 z t /\ first_gt vs1 vs2 = None /\
    length vs1 = z /\ length vs2 = z /\ P' = (Pa ++ (t, li) :: Pb) /\
    G' = upd_env (upd_env G t tmp1 (last vs1 (G t tmp1)))
                 t tmp2 (last vs2 (G t tmp2)).
Proof.
  induction z; clarify.
  - exists [], []; clarify.
    do 2 rewrite upd_triv.
    exploit exec_t_maintain; eauto; clarify.
    rewrite in_app; clarify.
  - inversion Ht; clarify.
    { exploit distinct_in; [eauto | rewrite in_app; clarify | apply Hin' |
                            clarify].
      repeat rewrite app_comm_cons in *; exploit app_nil_inv; eauto; clarify. }
    exploit exec_next; eauto; intros (v1 & ?); clarify.
    exploit distinct_step; eauto; intro.
    inversion Hexec'; clarify.
    { exploit distinct_in; [eauto | rewrite in_app; clarify | apply Hin' |
                            clarify].
      repeat rewrite app_comm_cons in *; exploit app_nil_inv; eauto; clarify. }
    exploit exec_next; eauto; intros (v2 & ?); clarify.
    exploit distinct_step; eauto; intro.
    inversion Hexec'0; clarify.
    { exploit distinct_in; [eauto | rewrite in_app; clarify | apply Hin' |
                            clarify].
      repeat rewrite app_comm_cons in *; exploit app_nil_inv; eauto; clarify. }
    exploit exec_next; eauto; simpl; intros (? & ?).
    rewrite upd_same, upd_assoc, upd_same in *; auto.
    destruct (le_dec v1 v2); clarify; [|inversion Hexec'1].
    exploit distinct_step; eauto; intro.
    exploit IHz; eauto.
    rewrite <- leb_le in *.
    Opaque last.
    intros (vs1 & vs2 & ?); exists (v1 :: vs1), (v2 :: vs2); clarify.
    rewrite upd_overwrite, upd_same.
    rewrite upd_three, upd_old, upd_same, upd_assoc; auto.
    do 2 rewrite last_cons'; auto.
Qed.

Lemma move_exec : forall t P G lo lc P' G' (Hdistinct : distinct P)
  li src tgt Pa Pb (HP : P = Pa ++ (t, move src tgt tmp1 ++ li) :: Pb)
  (Ht : exec_star_t t (Some P) G lo lc (Some P') G') (Hin' : In (t, li) P'),
  exists v, lo = events_move (fst src) (fst tgt) t /\
            lc = mops_move src tgt t v /\ P' = Pa ++ (t, li) :: Pb /\
            G' = upd_env G t tmp1 v.
Proof.
  intros; inversion Ht; clear Ht; clarify.
  { exploit distinct_in; [eauto | rewrite in_app; clarify | eauto | clarify].
    exfalso; eapply (cons_app_neq [_]); simpl; eauto. }
  exploit exec_next; eauto; clarify.
  exploit distinct_step; eauto; intro.
  inversion Hexec'; clear Hexec'; clarify.
  { exploit distinct_in.
    { eauto. }
    { rewrite in_app; clarify. }
    { eauto. }
    intro; exploit cons_neq; eauto; contradiction. }
  exploit exec_next; eauto; clarify.
  exploit distinct_step; eauto; intro.
  exploit exec_t_maintain; eauto.
  { rewrite in_app; clarify. }
  clarify.
  repeat eexists; eauto.
  rewrite upd_same; auto.
Qed.
    
Opaque move.
Opaque mops_move.
Opaque events_move.

Lemma hb_check_match : forall C1 C2 t z vs1 vs2 (Hlen1 : length vs1 = z)
  (Hlen2 : length vs2 = z) (Hle : first_gt vs1 vs2 = None)
  m (Hcon : consistent (m ++ mops_hb_check C1 C2 vs1 vs2 z t)) n (Hlt : n < z), 
  exists v, nth_error vs2 n = Some v /\ can_read m (C2, z - n - 1) v.
Proof.
  induction z; clarify; [omega|].
  destruct vs1, vs2; clarify.
  destruct n.
  - do 2 eexists; simpl; eauto.
    rewrite <- minus_n_O.
    rewrite read_noop_SC in Hcon.
    eapply can_read_thread'.
    eapply consistent_app_SC; rewrite <- app_assoc; simpl; eauto.
    { eapply consistent_app_SC; rewrite <- app_assoc; simpl; eauto. }
  - exploit (IHz vs1 vs2); eauto.
    { rewrite read_noop_SC, read_noop_SC in Hcon; auto.
      { eapply consistent_app_SC; rewrite <- app_assoc; simpl; eauto. }
      { eapply consistent_app_SC; rewrite <- app_assoc; simpl; eauto. } }
    { omega. }
Qed.

Lemma mops_hb_check_read : forall C1 C2 t z vs1 vs2,
  Forall (fun c => match c with Read _ _ _ => True | _ => False end)
         (mops_hb_check C1 C2 t z vs1 vs2).
Proof.
  intros.
  rewrite Forall_forall; intros.
  exploit in_mops_hb_check; eauto; destruct x; auto.
Qed.
*)
Corollary hb_check_twice : forall C1 C1' C2 t z vs1 vs1' vs2 vs2'
  (Hlen1 : length vs1 = z) (Hlen1' : length vs1' = z) (Hlen2 : length vs2 = z)
  (Hlen2' : length vs2' = z) (Hle : first_gt vs1 vs2 = None)
  (Hle' : first_gt vs1' vs2' = None)
  m (Hcon : consistent (m ++ mops_hb_check C1 C2 vs1 vs2 z t ++
                             mops_hb_check C1' C2 vs1' vs2' z t))
  (Hinit : forall o, o < z -> initialized m (C2, o)),
  vs2' = vs2.
Proof.
  admit. (*
  intros.
  rewrite app_assoc in Hcon.
  generalize (hb_check_match _ _ _ _ _ Hlen1' Hlen2' Hle' _ Hcon); intro Hvs2'.
  exploit consistent_app_SC; eauto; intro Hcon'.
  generalize (hb_check_match _ _ _ _ _ Hlen1 Hlen2 Hle _ Hcon'); intro Hvs2.
  apply list_ext; intro n; specialize (Hvs2 n); specialize (Hvs2' n).
  destruct (lt_dec n z); clarify.
  - unfold can_read in *; rewrite <- app_assoc in *.
    rewrite reads_noops_SC in Hvs2'2; auto; [|apply mops_hb_check_read].
    exploit consistent_app_SC; eauto; intro.
    exploit can_read_unique.
    { eauto. }
    { specialize (Hinit (length vs1 - n - 1)).
      use Hinit; [eauto | omega]. }
    { apply Hvs22. }
    { apply Hvs2'2. }
    clarsimp.
  - destruct (nth_error vs2 n) eqn: Hnth.
    { exploit nth_error_lt; eauto; omega. }
    destruct (nth_error vs2' n) eqn: Hnth'; auto.
    { exploit nth_error_lt; eauto; omega. }*)
Qed.
(*
Lemma max_vc_exec : forall t z P G lo lc P' G' (Hdistinct : distinct P)
  li src tgt (Hz : z <> 0)
  Pa Pb (HP : P = Pa ++ (t, max_vc src tgt z tmp1 tmp2 ++ li) :: Pb)
  (Ht : exec_star_t t (Some P) G lo lc (Some P') G') (Hin' : In (t, li) P'),
  exists vs1 vs2, lo = events_max_vc src tgt t z /\
    lc = mops_max_vc src tgt vs1 vs2 t z /\
    length vs1 = z /\ length vs2 = z /\ P' = (Pa ++ (t, li) :: Pb) /\
    G' = upd_env (upd_env G t tmp1 (last vs1 0))
                 t tmp2 (Peano.max (last vs1 0) (last vs2 0)).
Proof.
  induction z; clarify.
  inversion Ht; clarify.
  { exploit distinct_in; [eauto | apply split_in | apply Hin' | clarify].
    repeat rewrite app_comm_cons in *; exploit app_nil_inv; eauto; clarify. }
  exploit exec_next; eauto; intros (v1 & ?); clarify.
  exploit distinct_step; eauto; intro.
  inversion Hexec'; clarify.
  { exploit distinct_in; [eauto | apply split_in | apply Hin' | clarify].
    repeat rewrite app_comm_cons in *; exploit app_nil_inv; eauto; clarify. }
  exploit exec_next; eauto; intros (v2 & ?); clarify.
  exploit distinct_step; eauto; intro.
  inversion Hexec'0; clarify.
  { exploit distinct_in; [eauto | apply split_in | apply Hin' | clarify].
    repeat rewrite app_comm_cons in *; exploit app_nil_inv; eauto; clarify. }
  exploit exec_next; eauto; clarify.
  exploit distinct_step; eauto; intro.
  inversion Hexec'1; clarify.
  { exploit distinct_in; [eauto | apply split_in | apply Hin' | clarify].
    repeat rewrite app_comm_cons in *; exploit app_nil_inv; eauto; clarify. }
  exploit exec_next; eauto; clarify.
  repeat rewrite upd_same.
  rewrite upd_old, upd_same; auto.
  exploit distinct_step; eauto; intro.
  destruct (eq_dec z 0).
  { clarify.
    exploit exec_t_maintain; try apply Hexec'2; try apply split_in; eauto;
      clarify.
    exists [v1], [v2]; clarify.
    repeat rewrite upd_same.
    rewrite upd_overwrite.
    rewrite upd_old, upd_same; auto. }
  exploit IHz; eauto.
  intros (vs1 & vs2 & ?); exists (v1 :: vs1), (v2 :: vs2); clarify.
  repeat rewrite upd_same.
  rewrite upd_overwrite.
  repeat rewrite upd_three; auto.
  rewrite last_cons, last_cons; auto; intro; clarify.
Qed.

Transparent move mops_move.

Lemma set_vc_exec : forall t z P G lo lc P' G' (Hdistinct : distinct P)
  li src tgt
  Pa Pb (HP : P = Pa ++ (t, set_vc src tgt z tmp1 ++ li) :: Pb)
  (Ht : exec_star_t t (Some P) G lo lc (Some P') G') (Hin' : In (t, li) P'),
  exists vs, lo = events_set_vc src tgt z t /\
    lc = mops_set_vc src tgt z t vs /\ length vs = z /\
    P' = (Pa ++ (t, li) :: Pb) /\ G' = upd_env G t tmp1 (last vs (G t tmp1)).
Proof.
  induction z; clarify.
  { exists []; clarify.
    exploit exec_t_maintain; eauto; try apply split_in; clarify.
    rewrite last_nil, upd_triv; auto. }
  inversion Ht; clarify.
  { exploit distinct_in; [eauto | apply split_in | apply Hin' | clarify].
    repeat rewrite app_comm_cons in *; exploit app_nil_inv; eauto; clarify. }
  exploit exec_next; eauto; intros (v & ?); clarify.
  exploit distinct_step; eauto; intro.
  inversion Hexec'; clarify.
  { exploit distinct_in; [eauto | apply split_in | apply Hin' | clarify].
    repeat rewrite app_comm_cons in *; exploit app_nil_inv; eauto; clarify. }
  exploit exec_next; eauto; clarify.
  exploit distinct_step; eauto; intro.
  exploit IHz; eauto; intros (vs & ?); exists (v :: vs); clarify.
  repeat rewrite upd_same; clarify.
  rewrite upd_overwrite.
  rewrite last_cons'; auto.
Qed.

Opaque move mops_move.
*)
Lemma exec_t_iexec : forall t P G lo lc P' G' i li (Hdistinct : distinct P)
  (Hin : In (t, instrument_instr i t ++ li) P) (Hlt : t < zt)
  (Hfresh : fresh tmp1 i /\ fresh tmp2 i)
  (Ht : exec_star_t t (Some P) G lo lc (Some P') G') (Hin' : In (t, li) P')
  m (Hcon : consistent (m ++ lc))
  (Hinit : forall t o, t < zt -> o < zt -> initialized m (C + t, o)),
  iexec P G t lo lc P' G'.
Proof.
  admit.
(*  destruct i; try destruct x; clarify.
  - inversion Ht; clarify.
    { generalize (NoDup_id_inj _ _ _ Hdistinct Hin Hin'); clarify.
      exploit cons_neq; eauto; clarify. }
    generalize (in_split _ _ Hin); intros (P1 & P2 & ?); clarify.
    exploit exec_next; eauto; clarify.
    exploit distinct_step; eauto; intro.
    exploit exec_t_maintain; eauto.
    { rewrite in_app; clarify. }
    clarify; apply iexec_assign; auto.
  - exploit distinct_steps; try eapply exec_t_exec; eauto; intro Hdistinct'.
    inversion Ht; clear Ht; clarify.
    { generalize (NoDup_id_inj _ _ _ Hdistinct' Hin Hin'); clarify.
      exploit cons_app_neq; eauto; clarify. }
    generalize (in_split _ _ Hin); clarify.
    exploit exec_next; eauto; intros (i & ?); clarify.
    exploit distinct_step; eauto; intro.
    repeat rewrite <- app_assoc in *.
    exploit exec_t_segment; eauto.
    { rewrite in_app; right.
      unfold In; fold In; left.
      rewrite (app_assoc (move _ _ _)); eauto. }
    intros (Pm & Gm & loc & lcc & lom & lcm & Hcheck & Hinm & Hrest & ?);
      clarify.
    exploit hb_check_exec; try apply Hcheck; eauto; clarify.
    exploit distinct_steps; try (eapply exec_t_exec, Hcheck); auto; intro.
    rewrite <- app_assoc in Hinm; exploit exec_t_segment; eauto.
    intros (? & ? & ? & ? & ? & ? & Hmove & Hin2 & Hrest2 & ?); clarify.
    exploit move_exec; try apply Hmove; eauto; clarify.
    exploit distinct_steps; try eapply exec_t_exec; eauto; intro.
    inversion Hrest2; clear Hrest2; subst.
    { generalize (distinct_in Hdistinct' _ _ _ Hin2 Hin'); intro.
      exfalso; eapply (cons_app_neq [_]); simpl; eauto. }
    generalize (in_split _ _ Hin2); clarify.
    exploit exec_next; eauto; clarify.
    inversion Hexec'0; clear Hexec'0; subst.
    { exploit distinct_in.
      { apply Hdistinct'. }
      { rewrite in_app; clarify. }
      { eauto. }
      intro; exploit cons_neq; eauto; contradiction. }
    exploit distinct_step; eauto; intro.
    exploit exec_next; eauto; clarify.
    exploit distinct_step; eauto; intro.
    exploit exec_t_maintain; eauto; [rewrite in_app|]; clarify.
    rewrite upd_three; auto.
    apply iexec_load; auto.
    exploit distinct_thread; try apply H2; clarify.
    rewrite <- app_assoc; auto.
  - exploit distinct_steps; try eapply exec_t_exec; eauto; intro Hdistinct'.
    inversion Ht; clear Ht; clarify.
    { generalize (NoDup_id_inj _ _ _ Hdistinct' Hin Hin'); clarify.
      exploit cons_app_neq; eauto; clarify. }
    generalize (in_split _ _ Hin); clarify.
    exploit exec_next; eauto; intros (i & ?); clarify.
    exploit distinct_step; eauto; intro.
    repeat rewrite <- app_assoc in *.
    exploit exec_t_segment; eauto.
    { rewrite in_app; right.
      unfold In; fold In; left.
      rewrite (app_assoc (hb_check _ _ _ _ _) (move _ _ _)).
      rewrite (app_assoc (_ ++ _) _); eauto. }
    intros (Pm & Gm & loc & lcc & lom & lcm & Hcheck1 & Hinm & Hrest & ?);
      clarify.
    do 2 rewrite <- app_assoc in Hinm; rewrite (app_assoc (move _ _ _)) in Hinm.
    exploit hb_check_exec; try apply Hcheck1; eauto; clarify.
    exploit distinct_steps; try (eapply exec_t_exec, Hcheck1); auto; intro.
    exploit exec_t_segment; eauto.
    intros (Pm' & Gm' & loc' & lcc' & lom' & lcm' & Hcheck2 & Hinm' & Hrest' &
      ?); clarify.
    exploit hb_check_exec; try apply Hcheck2; eauto; clarify.
    exploit distinct_steps; try (eapply exec_t_exec, Hcheck2); auto; intro.
    rewrite <- app_assoc in Hinm'; exploit exec_t_segment; eauto.
    intros (? & ? & ? & ? & ? & ? & Hmove & Hin2 & Hrest2 & ?); clarify.
    exploit move_exec; try apply Hmove; eauto; clarify.
    exploit distinct_steps; try eapply exec_t_exec; eauto; intro.
    inversion Hrest2; clear Hrest2; subst.
    { generalize (distinct_in Hdistinct' _ _ _ Hin2 Hin'); intro.
      exfalso; eapply (cons_app_neq [_]); simpl; eauto. }
    generalize (in_split _ _ Hin2); clarify.
    exploit exec_next; eauto; clarify.
    inversion Hexec'0; clear Hexec'0; subst.
    { exploit distinct_in.
      { apply Hdistinct'. }
      { rewrite in_app; clarify. }
      { eauto. }
      intro; exploit cons_neq; eauto; contradiction. }
    exploit distinct_step; eauto; intro.
    exploit exec_next; eauto; clarify.
    exploit distinct_step; eauto; intro.
    exploit exec_t_maintain; eauto; [rewrite in_app|]; clarify.
    rewrite upd_three; auto.
    rewrite upd_three; auto.
    rewrite upd_three; auto.
    rewrite upd_same.
    erewrite eval_old'; eauto.
    rewrite split_app, app_assoc, app_assoc in Hcon.
    exploit consistent_app_SC; eauto; intro Hcon'.
    rewrite <- app_assoc in Hcon'.
    exploit hb_check_twice; try apply Hcon'; auto.
    { intros; apply init_step; auto.
      constructor; simpl; auto. }
    intro; subst.
    erewrite last_def; [|intro; clarify].
    apply iexec_store; auto.
    exploit distinct_thread; try apply H3; clarify.
    repeat rewrite <- app_assoc; auto.
  - exploit distinct_steps; try eapply exec_t_exec; eauto; intro Hdistinct'.
    inversion Ht; clear Ht; clarify.
    { generalize (NoDup_id_inj _ _ _ Hdistinct' Hin Hin'); clarify.
      exploit cons_app_neq; eauto; clarify. }
    generalize (in_split _ _ Hin); clarify.
    exploit exec_next; eauto; clarify.
    exploit distinct_step; eauto; intro.
    unfold lock_handler in *; exploit max_vc_exec; eauto; clarify.
    apply iexec_lock; auto.
  - unfold unlock_handler in *; do 2 rewrite <- app_assoc in Hin.
    rewrite (app_assoc _ [_]) in Hin.
    exploit exec_t_segment; eauto.
    intros (? & ? & ? & ? & ? & ? & Hset & Hin1 & Hrest1 & ?); clarify.
    generalize (in_split _ _ Hin); clarify.
    exploit set_vc_exec; try apply Hset; clarify.
    exploit distinct_steps; try eapply exec_t_exec, Hset; eauto; intro.
    exploit distinct_steps; try eapply exec_t_exec; eauto; intro Hdistinct'.
    inversion Hrest1; clear Hrest1; subst.
    { exploit distinct_in; [apply Hdistinct' | apply split_in | eauto | intro].
      exploit cons_app_neq; [|contradiction].
      instantiate (3 := [_; _; _]); simpl; eauto. }
    exploit exec_next; eauto; clarify.
    exploit distinct_step; try apply H; eauto; intro.
    inversion Hexec'; clear Hexec'; subst.
    { exploit distinct_in; [apply Hdistinct' | apply split_in | eauto | intro].
      exploit cons_app_neq; [|contradiction].
      instantiate (3 := [_; _]); simpl; eauto. }
    exploit exec_next; eauto; clarify.
    exploit distinct_step; eauto; intro.
    inversion Hexec'0; clear Hexec'0; subst.
    { exploit distinct_in; [apply Hdistinct' | apply split_in | eauto | intro].
      exploit cons_app_neq; [|contradiction].
      instantiate (3 := [_]); simpl; eauto. }
    exploit exec_next; eauto; clarify.
    exploit distinct_step; eauto; intro.
    inversion Hexec'; clear Hexec'; subst.
    { exploit distinct_in; [apply Hdistinct' | apply split_in | eauto | intro].
      exploit cons_neq; eauto; contradiction. }
    exploit exec_next; eauto; clarify.
    exploit distinct_step; eauto; intro.
    exploit exec_t_maintain; try apply Hexec'0; try apply split_in; eauto;
      clarify.
    repeat rewrite upd_same.
    repeat rewrite upd_overwrite.
    apply iexec_unlock; auto.
    unfold unlock_handler; rewrite <- app_assoc; auto.
  - unfold spawn_handler in *; do 2 rewrite <- app_assoc in Hin.
    rewrite (app_assoc _ [_]) in Hin.
    exploit exec_t_segment; eauto.
    intros (? & ? & ? & ? & ? & ? & Hmax & Hin1 & Hrest1 & ?); clarify.
    generalize (in_split _ _ Hin); clarify.
    exploit max_vc_exec; try apply Hmax; try reflexivity; clarify.
    exploit distinct_steps; try eapply exec_t_exec, Hmax; eauto; intro.
    exploit distinct_steps; try eapply exec_t_exec; eauto; intro Hdistinct'.
    inversion Hrest1; clear Hrest1; subst.
    { exploit distinct_in; [apply Hdistinct' | apply split_in | eauto | intro].
      exploit cons_app_neq; [|contradiction].
      instantiate (3 := [_; _; _]); simpl; eauto. }
    exploit exec_next; eauto; clarify.
    exploit distinct_step; try apply H; eauto; intro.
    inversion Hexec'; clear Hexec'; subst.
    { exploit distinct_in; [apply Hdistinct' | apply split_in | eauto | intro].
      exploit cons_app_neq; [|contradiction].
      instantiate (3 := [_; _]); simpl; eauto. }
    exploit exec_next; eauto; clarify.
    exploit distinct_step; eauto; intro.
    inversion Hexec'0; clear Hexec'0; subst.
    { exploit distinct_in; [apply Hdistinct' | apply split_in | eauto | intro].
      exploit cons_app_neq; [|contradiction].
      instantiate (3 := [_]); simpl; eauto. }
    exploit exec_next; eauto; clarify.
    exploit distinct_step; eauto; intro.
    inversion Hexec'; clear Hexec'; subst.
    { exploit distinct_in; [apply Hdistinct' | apply split_in | eauto | intro].
      exploit cons_neq; eauto; contradiction. }
    exploit exec_next; eauto; clarify.
    exploit distinct_step; eauto; intro.
    exploit exec_t_maintain; try apply Hexec'0; try apply split_in; eauto;
      clarify.
    repeat rewrite upd_same.
    rewrite upd_three; auto.
    rewrite upd_three; auto.
    rewrite upd_assoc; auto.
    apply iexec_spawn; auto.
    unfold spawn_handler; rewrite <- app_assoc; auto.
    { rewrite map_app in *; auto. }
  - exploit distinct_steps; try eapply exec_t_exec; eauto; intro Hdistinct'.
    inversion Ht; clear Ht; clarify.
    { generalize (NoDup_id_inj _ _ _ Hdistinct' Hin Hin'); clarify.
      exploit cons_app_neq; eauto; clarify. }
    generalize (in_split _ _ Hin); clarify.
    exploit exec_next; eauto; clarify.
    exploit distinct_step; eauto; intro.
    unfold wait_handler in *; rewrite <- app_assoc in *.
    exploit exec_t_segment; eauto; try apply split_in.
    intros (? & ? & ? & ? & ? & ? & Hmax & Hin1 & Hrest1 & ?); clarify.
    generalize (in_split _ _ Hin); clarify.
    exploit max_vc_exec; try apply Hmax; try reflexivity; clarify.
    exploit distinct_steps; try eapply exec_t_exec, Hmax; eauto; intro.
    inversion Hrest1; clear Hrest1; subst.
    { exploit distinct_in; [apply Hdistinct' | apply split_in | eauto | intro].
      exploit cons_app_neq; [|contradiction].
      instantiate (3 := [_; _]); simpl; eauto. }
    exploit exec_next; eauto; clarify.
    exploit distinct_step; eauto; intro.
    inversion Hexec'0; clear Hexec'0; subst.
    { exploit distinct_in; [apply Hdistinct' | apply split_in | eauto | intro].
      exploit cons_app_neq; [|contradiction].
      instantiate (3 := [_]); simpl; eauto. }
    exploit exec_next; eauto; clarify.
    exploit distinct_step; eauto; intro.
    inversion Hexec'1; clear Hexec'1; subst.
    { exploit distinct_in; [apply Hdistinct' | apply split_in | eauto | intro].
      exploit cons_neq; eauto; contradiction. }
    exploit exec_next; eauto; clarify.
    exploit distinct_step; eauto; intro.
    exploit exec_t_maintain; try apply Hexec'0; try apply split_in; eauto;
      clarify.
    repeat rewrite upd_same.
    rewrite upd_three; auto.
    rewrite upd_three; auto.
    rewrite upd_assoc; auto.
    apply iexec_wait; auto.
    unfold wait_handler; rewrite <- app_assoc; auto.
  - inversion Ht; clarify.
    { generalize (NoDup_id_inj _ _ _ Hdistinct Hin Hin'); clarify.
      exploit cons_neq; eauto; clarify. }
    generalize (in_split _ _ Hin); clarify.
    exploit exec_next; eauto; clarify.
    destruct (le_dec (eval (G t) e1) (eval (G t) e2)); clarify.
    exploit distinct_step; eauto; intro.
    exploit exec_t_maintain; eauto; try apply split_in.
    clarify; eapply iexec_assert; eauto.
    { inversion Hexec'. }*)
Qed.

Lemma exec_minus_reorder : forall t P G lo lc P1 G1 (Hdistinct : distinct P)
  (Hsteps : exec_star_minus t (Some P) G lo lc (Some P1) G1)
  o c P2 G2 (Hstep : exec P1 G1 t o c (Some P2) G2)
  m (Hcon : consistent (m ++ lc ++ opt_to_list c))
  (Hindep : Forall (fun c' => match c with Some a => loc_of c' <> loc_of a
                              | None => True end) lc)
  (Hno_fork : Forall (fun o => match o with fork _ _ => False | _ => True end)
                     lo)
  (Hno_empty : Forall (fun e => snd e = [] -> In e P) P1),
  exists P1' G1', exec P G t o c (Some P1') G1' /\
    exec_star_minus t (Some P1') G1' lo lc (Some P2) G2.
Proof.
  admit.
(*  intros until G2; remember (Some P) as Pa; remember (Some P1) as Pb;
    generalize dependent P; induction Hsteps; clarify.
  { repeat eexists; eauto; apply exec_refl_m. }
  destruct P'; [|inversion Hsteps].
  exploit distinct_step; eauto; intro.
  specialize (IHHsteps s); clarify.
  rewrite <- app_assoc, app_assoc in Hcon; specialize (IHHsteps _ Hcon).
  rewrite Forall_app in *; clarify.
  assert (t <> t') as Hdiff by auto.
  use IHHsteps; clarify.
  generalize (exec_swap Hdiff Hdistinct Hexec IHHsteps1); intro Hswap.
  use Hswap. use Hswap. use Hswap.
  clarify.
  repeat eexists; eauto.
  eapply exec_step_m; eauto.
  - exploit in_split; eauto; clarify.
    exploit exec_next; eauto; clarify; inversion Hno_fork1; clarify.
  - exploit in_split; eauto; clarify.
    exploit exec_next; eauto; intros (v & ?).
    destruct (instr_result t' i (G t') v) as [((((?, ?), ?), ?), ?)|]; clarify.
    exploit exec_keep; eauto.
    { eapply exec_minus_exec; eauto. }
    { apply split_in. }
    clarify; rewrite skipn_nil in *.
    rewrite Forall_forall in Hno_empty; exploit Hno_empty; eauto; intro.
    exploit distinct_in; [apply Hdistinct | apply split_in | eauto | clarify].
  - intro; exploit in_split; eauto; clarify.
    exploit exec_next; eauto; clarify; inversion Hno_fork1; clarify.
  - eapply Forall_impl; eauto; clarify.
    destruct a; exploit exec_keep.
    { apply Hdistinct. }
    { eapply exec_step; try apply exec_refl; eauto. }
    { eauto. }
    clarify; rewrite skipn_nil in *; auto.*)
Qed.

Lemma state_suffix_stable : forall P P1 (Hsuffix : state_suffix P P1)
  (Hdistinct : distinct P1)
  G1 lo lc P2 G2 (Hsteps : exec_star (Some P1) G1 lo lc (Some P2) G2)
  (Hsuffix2 : state_suffix P P2),
  Forall (fun o => match o with fork _ _ => False | _ => True end) lo /\
  Forall (fun e => snd e = [] -> In e P1) P2.
Proof.
  admit.
(*  intros; remember (Some P1) as Pa; remember (Some P2) as Pb;
    generalize dependent P1; induction Hsteps; clarify.
  { rewrite Forall_forall; auto. }
  destruct P'; [|inversion Hsteps].
  exploit state_suffix_inter; eauto.
  { eapply exec_step; try apply exec_refl; eauto. }
  exploit distinct_step; eauto; intros ? Hsuffix'.
  exploit IHHsteps; eauto; intros (IH1 & IH2).
  rewrite Forall_app; split; clarify.
  - destruct o; clarify.
    constructor; auto.
    destruct o; auto.
    inversion Hexec; clarify.
    exploit Forall2_in2; try apply Hsuffix'.
    { rewrite in_app; right; simpl; right; eauto. }
    intros ((?, ?) & ?); clarify.
    exploit Forall2_in1; eauto; intros ((?, ?) & ?); clarify.
    contradiction Hnew; rewrite in_map_iff; repeat eexists; eauto; auto.
  - rewrite Forall_forall in *; intros (?, ?) ??.
    exploit IH2; eauto; clarify.
    exploit Forall2_in2; eauto; intros ((?, ?) & ? & ? & ? & ? & Heq).
    destruct l; clarify.
    exploit Forall2_in1; try apply Hsuffix; eauto; intros ((?, ?) & ?); clarify.
    rewrite skipn_nil in *; auto.
    { symmetry in Heq; rewrite skipn_all_iff, app_length in Heq; omega. }*)
Qed.  

Opaque removelast.

Hint Resolve Htmp.

Opaque last.

Lemma hb_check_mem_n : forall li t C1 C2 z G n vs lc G' vs' cond
  (Hmem : to_mem' G t (firstn n (hb_check C1 C2 z tmp1 tmp2)) vs =
    Some (lc, G', vs', cond))
  (Hcond : until_last cond (hb_check C1 C2 z tmp1 tmp2 ++ li) n G')
  (Hn : n <= length (hb_check C1 C2 z tmp1 tmp2)),
  (exists vs1 vs2 n', n' <= length (mops_hb_check C1 C2 vs1 vs2 z t) /\
                      lc = firstn n' (mops_hb_check C1 C2 vs1 vs2 z t)) /\
  forall a, a <> tmp1 -> a <> tmp2 -> G' a = G a.
Proof.
  induction z; clarify.
  - rewrite firstn_nil in *; clarify.
    exists [], [], 0; auto.
  - destruct n; clarify.
    { exists [], [], 0; auto. }
    destruct vs; clarify.
    destruct x as (((?, ?), ?), ?); clarify.
    destruct n; clarify.
    { split; [exists [n0], [n0], 1; clarify|].
      unfold upd; clarify. }
    destruct vs; clarify.
    destruct x as (((?, ?), ?), ?); clarify.
    destruct n; clarify.
    { split; [exists [n0], [n1], 2; clarify|].
      intros; rewrite VectorClocks.upd_old; auto.
      apply VectorClocks.upd_old; auto. }
    destruct x as (((?, ?), ?), ?); clarify.
    exploit IHz; eauto.
    { unfold until_last in *; destruct Hcond as [Hcond | Hcond]; clarify.
      { inversion Hcond; clarify. }
      rewrite removelast_firstn_eq in *; simpl in *.
      destruct l2; clarify.
      inversion Hcond221; clarify.
      rewrite upd_new, VectorClocks.upd_old, upd_new in *; auto.
      destruct n; clarify.
      repeat rewrite <- minus_n_O; right; repeat eexists; eauto. }
    { omega. }
    intros ((vs1 & vs2 & n' & ?) & HG); subst.
    split.
    + exists (n0 :: vs1), (n1 :: vs2); simpl.
      destruct (n0 <=? n1) eqn: Hle; [exists (S (S n')) | exists 2]; clarify.
      { omega. }
      unfold until_last in Hcond; destruct Hcond as [Hcond | Hcond].
      { inversion Hcond; clarify.
        rewrite upd_new, VectorClocks.upd_old, upd_new in *; auto.
        rewrite <- leb_le in *; unfold id in *; clarify. }
      clarify.
      destruct n; [clarify | simpl in Hcond1].
      destruct l2.
      * exploit to_mem_conds; eauto; rewrite Forall_forall; intro X; exploit X.
        { eapply nth_error_in; rewrite nth_error_firstn.
          instantiate (2 := n); destruct (lt_dec n (S n)); [|omega].
          rewrite nth_error_app in Hcond1;
            destruct (lt_dec n (length (hb_check C1 C2 z tmp1 tmp2)));
            [eauto |omega]. }
        clarify.
      * rewrite removelast_2 in Hcond221; inversion Hcond221.
        rewrite upd_new, VectorClocks.upd_old, upd_new in *; auto.
        rewrite <- leb_le in *; unfold id in *; clarify.
    + intros; rewrite HG; auto.
      do 2 (rewrite VectorClocks.upd_old; auto).
Qed.

Lemma hb_check_mem : forall li t C1 C2 z G vs lc G' vs' cond
  (Hmem : to_mem' G t (hb_check C1 C2 z tmp1 tmp2) vs =
    Some (lc, G', vs', cond))
  (Hcond : until_last cond (hb_check C1 C2 z tmp1 tmp2 ++ li)
                      (length (hb_check C1 C2 z tmp1 tmp2)) G'),
  (exists vs1 vs2, lc = mops_hb_check C1 C2 vs1 vs2 z t) /\
  forall a, a <> tmp1 -> a <> tmp2 -> G' a = G a.
Proof.
  induction z; clarify.
  - exists [], []; auto.
  - destruct vs; clarify.
    destruct x as (((?, ?), ?), ?); clarify.
    destruct vs; clarify.
    destruct x as (((?, ?), ?), ?); clarify.
    destruct x0 as (((?, ?), ?), ?); clarify.
    exploit IHz; eauto.
    { unfold until_last in *; destruct Hcond as [Hcond | Hcond]; clarify.
      { inversion Hcond; clarify. }
      rewrite removelast_firstn_eq in *; simpl in *.
      destruct l2; clarify.
      inversion Hcond221; clarify.
      rewrite upd_new, VectorClocks.upd_old, upd_new in *; auto.
      destruct (hb_check C1 C2 z tmp1 tmp2); clarify.
      repeat rewrite <- minus_n_O; right; repeat eexists; eauto. }
    intros ((vs1 & vs2 & ?) & HG); subst.
    split.
    + exists (n :: vs1), (n0 :: vs2); simpl.
      destruct (n <=? n0) eqn: Hle; clarify.
      unfold until_last in Hcond; destruct Hcond as [Hcond | Hcond].
      { inversion Hcond; clarify.
        rewrite upd_new, VectorClocks.upd_old, upd_new in *; auto.
        rewrite <- leb_le in *; unfold id in *; clarify. }
      clarify.
      destruct (length (hb_check C1 C2 z tmp1 tmp2)) eqn: Hlen; clarify.
      { destruct z; clarify. }
      destruct l2; clarify.
      * exploit to_mem_conds; eauto; rewrite Forall_forall; intro X; exploit X.
        { eapply nth_error_in.
          rewrite nth_error_app in Hcond1;
            destruct (lt_dec n1 (length (hb_check C1 C2 z tmp1 tmp2)));
            [eauto | omega]. }
        clarify.
      * rewrite removelast_2 in Hcond221; inversion Hcond221.
        rewrite upd_new, VectorClocks.upd_old, upd_new in *; auto.
        rewrite <- leb_le in *; unfold id in *; clarify.
    + intros; rewrite HG; auto.
      do 2 (rewrite VectorClocks.upd_old; auto).
Qed.

Transparent move mops_move.

Lemma move_mem_n : forall t C1 C2 G n vs lc G' vs' cond
  (Hmem : to_mem' G t (firstn n (move C1 C2 tmp1)) vs =
    Some (lc, G', vs', cond)) (Hn : n <= length (move C1 C2 tmp1)),
  exists v n', n' <= length (mops_move C1 C2 t v) /\
    lc = firstn n' (mops_move C1 C2 t v) /\ cond = [] /\
    forall a, a <> tmp1 -> G' a = G a.
Proof.
  intros.
  destruct n; clarify.
  { exists 0, 0; auto. }
  destruct vs; clarify.
  destruct x as (((?, ?), ?), ?); clarify.
  exists n0.
  destruct n; clarify.
  { exists 1; clarify.
    apply VectorClocks.upd_old; auto. }
  destruct x as (((?, ?), ?), ?); clarify.
  rewrite firstn_nil in *; clarify.
  exists 2; rewrite upd_new; clarify.
  apply VectorClocks.upd_old; auto.
Qed.

Lemma move_mem : forall t C1 C2 G vs lc G' vs' cond
  (Hmem : to_mem' G t (move C1 C2 tmp1) vs = Some (lc, G', vs', cond)),
  exists v, lc = mops_move C1 C2 t v /\ cond = [] /\
    forall a, a <> tmp1 -> G' a = G a.
Proof.
  clarify.
  destruct vs; clarify.
  exists n; rewrite upd_new; clarify.
  apply VectorClocks.upd_old; auto.
Qed.

Opaque move mops_move.

Lemma t_steps_load_n : forall P G t lo lc P1 G1 a x o li
  (Hdistinct : distinct P)
  (Hin : In (t, instrument_instr (Load a (x, o)) t ++ li) P)
  n (Hsteps : t_steps P G t n lo lc P1 G1)
  (Hn : n <= length (instrument_instr (Load a (x, o)) t)),
  exists vs1 vs2 vt v n', n' <= length (Acq t (X + x) ::
    mops_hb_check (W + x) (C + t) vs1 vs2 zt t ++
    mops_move (C + t, t) (R + x, t) t vt ++
    [Read t (x, o) v; Rel t (X + x)]) /\
    filter (fun c => beq (thread_of c) t) lc =
    firstn n' (Acq t (X + x) :: mops_hb_check (W + x) (C + t) vs1 vs2 zt t ++
    mops_move (C + t, t) (R + x, t) t vt ++ [Read t (x, o) v; Rel t (X + x)])
.
Proof.
  intros.
  exploit t_steps_mem'; eauto; intros (vs & vs' & cond & Heq & Hcond).
  destruct n; clarify.
  { exists [], [], 0, 0, 0; auto. }
  destruct x10 as (((?, ?), ?), ?); clarify.
  repeat rewrite <- app_assoc in *.
  rewrite firstn_app in Heq1.
  destruct (le_dec n (length (hb_check (W + x) (C + t) zt tmp1 tmp2))).
  { rewrite le_minus_0, app_nil_r in Heq1; auto.
    exploit hb_check_mem_n; eauto.
    { eapply until_last_cons; eauto; simpl; auto. }
    intros ((vs1 & vs2 & n' & ?) & ?); exists vs1, vs2, 0, 0, (S n'); clarify.
    rewrite firstn_app, le_minus_0, app_nil_r; auto.
    split; [rewrite app_length; omega | auto]. }
  rewrite firstn_length' in Heq1; [|omega].
  rewrite to_mem'_app in Heq1.
  rewrite match_false in Heq1;
    destruct Heq1 as ((((?, ?), ?), ?) & Hcheck & Heq1).
  rewrite match_false in Heq1;
    destruct Heq1 as ((((?, ?), ?), ?) & Hrest & Heq1); clarify.
  exploit hb_check_mem; eauto.
  { instantiate (1 := []).
    unfold until_last in *; exploit until_last_app; eauto; clarify.
    rewrite app_nil_r in *; clarify.
    exploit to_mem_conds; eauto; intro Hsafe.
    destruct n; [clarify | simpl in Hcond1].
    rewrite nth_error_app in Hcond1;
      destruct (lt_dec n (length (hb_check (W + x) (C + t) zt tmp1 tmp2)));
      [omega|].
    rewrite Forall_forall in Hsafe; exploit Hsafe.
    { eapply nth_error_in; rewrite nth_error_firstn.
      instantiate (2 := n - length (hb_check (W + x) (C + t) zt tmp1 tmp2)).
      destruct (lt_dec (n - length (hb_check (W + x) (C + t) zt tmp1 tmp2))
        (S n - length (hb_check (W + x) (C + t) zt tmp1 tmp2)));
        [eauto | omega]. }
    clarify. }
  intros ((vs1 & vs2 & ?) & ?); clarify.
  exists vs1, vs2.
  rewrite firstn_app in Hrest.
  destruct (le_dec (n - length (hb_check (W + x) (C + t) zt tmp1 tmp2))
    (length (move (C + t, t) (R + x, t) tmp1))).
  { setoid_rewrite (le_minus_0 l) in Hrest; rewrite app_nil_r in Hrest.
    exploit move_mem_n; eauto; intros (v & n' & ?); clarify.
    exists v, 0, (S (length (mops_hb_check (W + x) (C + t) vs1 vs2 zt t) + n'));
      clarify.
    split.
    { repeat rewrite app_length; simpl.
      apply le_n_S, plus_le_compat_l; etransitivity; eauto.
      apply le_plus_l. }
    { rewrite firstn_app, (firstn_length' (mops_hb_check _ _ _ _ _ _)),
        minus_plus, firstn_app, le_minus_0, app_nil_r; auto; omega. } }
  rewrite firstn_length' in Hrest.
  rewrite to_mem'_app in Hrest.
  rewrite match_false in Hrest;
    destruct Hrest as ((((?, ?), ?), ?) & Hmove & Hrest).
  rewrite match_false in Hrest;
    destruct Hrest as ((((?, ?), ?), ?) & Hrest & ?); clarify.
  exploit move_mem; eauto; intros (v & ?); clarify.
  exists v.
  destruct (n - length (hb_check (W + x) (C + t) zt tmp1 tmp2) -
    (length (move (C + t, t) (R + x, t) tmp1))) eqn: Hn'; [omega|].
  setoid_rewrite Hn' in Hrest; clarify.
  destruct l0; clarify.
  destruct x10 as (((?, ?), ?), ?); clarify.
  exists n5; destruct n4; clarify.
  { exists (S (length (mops_hb_check (W + x) (C + t) vs1 vs2 zt t) +
      (length (mops_move (C + t, t) (R + x, t) t v) + 1))); clarify.
    split; [repeat rewrite app_length; simpl; omega|].
    rewrite firstn_app, firstn_length', minus_plus, firstn_app, firstn_length',
      minus_plus; clarify; omega. }
  destruct x10 as (((?, ?), ?), ?); clarify.
  destruct n4; clarify.
  exists (S (length (mops_hb_check (W + x) (C + t) vs1 vs2 zt t) +
    (length (mops_move (C + t, t) (R + x, t) t v) + 2))); clarify.
  split; [repeat rewrite app_length; simpl; omega|].
  rewrite firstn_app, firstn_length', minus_plus, firstn_app, firstn_length',
     minus_plus; clarify; omega.
  { exfalso; clear - Hn Hn'.
    repeat rewrite app_length in Hn; simpl in Hn.
    apply le_S_n, (minus_le_compat_r _ _ (length (hb_check (W + x) (C + t) zt
      tmp1 tmp2))) in Hn; rewrite minus_plus in Hn.
    apply (minus_le_compat_r _ _ (length (move (C + t, t) (R + x, t) tmp1)))
      in Hn; rewrite minus_plus, Hn' in Hn; omega. }
  { clear - n2.
    destruct (le_gt_dec (n - length (hb_check (W + x) (C + t) zt tmp1 tmp2))
      (length (move (C + t, t) (R + x, t) tmp1))); [contradiction|].
    apply lt_le_weak; auto. }
Qed.

Lemma t_steps_store_n : forall P G t lo lc P1 G1 x o e li
  (Hdistinct : distinct P) (Hfresh : expr_fresh tmp1 e /\ expr_fresh tmp2 e)
  (Hin : In (t, instrument_instr (Store (x, o) e) t ++ li) P)
  n (Hsteps : t_steps P G t n lo lc P1 G1)
  (Hn : n <= length (instrument_instr (Store (x, o) e) t)),
  exists vs1 vs2 vs2' vs3 v n', n' <= length (Acq t (X + x) ::
    mops_hb_check (W + x) (C + t) vs1 vs2 zt t ++
    mops_hb_check (R + x) (C + t) vs3 vs2' zt t ++
    mops_move (C + t, t) (W + x, t) t v ++
    [Write t (x, o) (eval (G t) e); Rel t (X + x)]) /\
    filter (fun c => beq (thread_of c) t) lc =
    firstn n' (Acq t (X + x) :: mops_hb_check (W + x) (C + t) vs1 vs2 zt t ++
    mops_hb_check (R + x) (C + t) vs3 vs2' zt t ++
    mops_move (C + t, t) (W + x, t) t v ++
    [Write t (x, o) (eval (G t) e); Rel t (X + x)]).
Proof.
  intros.
  exploit t_steps_mem'; eauto; intros (vs & vs' & cond & Heq & Hcond).
  destruct n; clarify.
  { exists [], [], [], [], 0, 0; auto. }
  destruct x10 as (((?, ?), ?), ?); clarify.
  repeat rewrite <- app_assoc in *.
  rewrite firstn_app in Heq1.
  destruct (le_dec n (length (hb_check (W + x) (C + t) zt tmp1 tmp2))).
  { rewrite le_minus_0, app_nil_r in Heq1; auto.
    exploit hb_check_mem_n; eauto.
    { eapply until_last_cons; eauto; simpl; auto. }
    intros ((vs1 & vs2 & n' & ?) & ?); exists vs1, vs2, [], [], 0, (S n');
      clarify.
    rewrite firstn_app, le_minus_0, app_nil_r; auto.
    split; [rewrite app_length; omega | auto]. }
  rewrite firstn_length' in Heq1; [|omega].
  rewrite to_mem'_app in Heq1.
  rewrite match_false in Heq1;
    destruct Heq1 as ((((?, ?), ?), ?) & Hcheck1 & Heq1).
  rewrite match_false in Heq1;
    destruct Heq1 as ((((?, ?), ?), ?) & Hrest & ?); clarify.
  exploit hb_check_mem; eauto.
  { instantiate (1 := []).
    unfold until_last in *; exploit until_last_app; eauto; clarify.
    rewrite app_nil_r in *; clarify.
    exploit to_mem_conds; eauto; intro Hsafe.
    destruct n; [clarify | simpl in Hcond1].
    rewrite nth_error_app in Hcond1;
      destruct (lt_dec n (length (hb_check (W + x) (C + t) zt tmp1 tmp2)));
      [omega|].
    rewrite Forall_forall in Hsafe; exploit Hsafe.
    { eapply nth_error_in; rewrite nth_error_firstn.
      instantiate (2 := n - length (hb_check (W + x) (C + t) zt tmp1 tmp2)).
      destruct (lt_dec (n - length (hb_check (W + x) (C + t) zt tmp1 tmp2))
        (S n - length (hb_check (W + x) (C + t) zt tmp1 tmp2)));
        [eauto | omega]. }
    clarify. }
  intros ((vs1 & vs2 & ?) & HG1); exists vs1, vs2; clarify.
  rewrite firstn_app in Hrest.
  destruct (le_dec (n - length (hb_check (W + x) (C + t) zt tmp1 tmp2))
    (length (hb_check (R + x) (C + t) zt tmp1 tmp2))).
  { setoid_rewrite (le_minus_0 l) in Hrest; rewrite app_nil_r in Hrest.
    exploit hb_check_mem_n; eauto.
    { unfold until_last in *; rewrite Forall_app in *; clarify.
      rewrite removelast_app, Forall_app in *.
      destruct n; [clarify | simpl in Hcond1].
      rewrite nth_error_app in Hcond1;
        destruct (lt_dec n (length (hb_check (W + x) (C + t) zt tmp1 tmp2)));
        [omega|].
      rewrite <- minus_Sn_m; [simpl | omega].
      rewrite <- minus_n_O.
      rewrite last_app in *; destruct l5; clarify.
      right; repeat eexists; eauto. }
    intros ((vs3 & vs2' & n' & ?) & ?); clarify.
    exists vs2', vs3, 0,
      (S (length (mops_hb_check (W + x) (C + t) vs1 vs2 zt t) + n')); clarify.
    split; [repeat rewrite app_length; omega|].
    rewrite firstn_app, (firstn_length' _ (le_plus_l _ _)),
      minus_plus, firstn_app, le_minus_0, app_nil_r; auto; omega. }
  rewrite firstn_length' in Hrest; [|omega].
  rewrite to_mem'_app in Hrest.
  rewrite match_false in Hrest;
    destruct Hrest as ((((?, ?), ?), ?) & Hcheck2 & Hrest).
  rewrite match_false in Hrest;
    destruct Hrest as ((((?, ?), ?), ?) & Hrest & ?); clarify.
  exploit hb_check_mem; try apply Hcheck2.
  { instantiate (1 := []).
    rewrite app_assoc in Hcond.
    unfold until_last in *; exploit until_last_app; eauto; clarify.
    repeat rewrite Forall_app in *; clarify.
    rewrite app_nil_r in *; clarify.
    exploit to_mem_conds; eauto; intro Hsafe.
    destruct n; [clarify | simpl in Hcond1].
    rewrite nth_error_app in Hcond1;
      destruct (lt_dec n (length (hb_check (W + x) (C + t) zt tmp1 tmp2)));
      [omega|].
    rewrite nth_error_app in Hcond1;
      destruct (lt_dec (n - length (hb_check (W + x) (C + t) zt tmp1 tmp2))
        (length (hb_check (R + x) (C + t) zt tmp1 tmp2))); [omega|].
    rewrite Forall_forall in Hsafe; exploit Hsafe.
    { eapply nth_error_in; rewrite nth_error_firstn.
      instantiate (2 := n - length (hb_check (W + x) (C + t) zt tmp1 tmp2) -
         length (hb_check (R + x) (C + t) zt tmp1 tmp2)).
      destruct (lt_dec (n - length (hb_check (W + x) (C + t) zt tmp1 tmp2) -
         length (hb_check (R + x) (C + t) zt tmp1 tmp2))
        (S n - length (hb_check (W + x) (C + t) zt tmp1 tmp2) -
         length (hb_check (R + x) (C + t) zt tmp1 tmp2)));
        [eauto | abstract omega]. }
    clarify. }
  intros ((vs3 & vs2' & ?) & HG2); exists vs2', vs3; clarify.
  rewrite firstn_app in Hrest.
  destruct (le_dec (n - length (hb_check (W + x) (C + t) zt tmp1 tmp2) -
    length (hb_check (R + x) (C + t) zt tmp1 tmp2))
    (length (move (C + t, t) (W + x, t) tmp1))).
  { setoid_rewrite (le_minus_0 l) in Hrest; rewrite app_nil_r in Hrest.
    exploit move_mem_n; eauto; intros (v & n' & ?); clarify.
    exists v, (S (length (mops_hb_check (W + x) (C + t) vs1 vs2 zt t) + 
      (length (mops_hb_check (R + x) (C + t) vs3 vs2' zt t) + n'))); clarify.
    split.
    { repeat rewrite app_length; simpl.
      apply le_n_S, plus_le_compat_l, plus_le_compat_l; etransitivity; eauto.
      apply le_plus_l. }
    { rewrite firstn_app, (firstn_length' (mops_hb_check _ _ _ _ _ _)),
        minus_plus, firstn_app, (firstn_length' (mops_hb_check _ _ _ _ _ _)),
        minus_plus, firstn_app, le_minus_0, app_nil_r; auto; abstract omega. } }
  rewrite firstn_length' in Hrest.
  rewrite to_mem'_app in Hrest.
  rewrite match_false in Hrest;
    destruct Hrest as ((((?, ?), ?), ?) & Hmove & Hrest).
  rewrite match_false in Hrest;
    destruct Hrest as ((((?, ?), ?), ?) & Hrest & ?); clarify.
  exploit move_mem; eauto; intros (v & ? & ? & HG3); clarify.
  exists v.
  destruct (n - length (hb_check (W + x) (C + t) zt tmp1 tmp2) -
    length (hb_check (R + x) (C + t) zt tmp1 tmp2) -
    length (move (C + t, t) (W + x, t) tmp1)) eqn: Hn'.
  { rewrite Nat.sub_0_le in Hn'; contradiction. }
  setoid_rewrite Hn' in Hrest; clarify.
  destruct x10 as (((?, ?), ?), ?); clarify.
  destruct n6; clarify.
  { exists (S (length (mops_hb_check (W + x) (C + t) vs1 vs2 zt t) +
      ((length (mops_hb_check (R + x) (C + t) vs3 vs2' zt t) +
       (length (mops_move (C + t, t) (W + x, t) t v) + 1))))); clarify.
    split.
    { repeat rewrite app_length; simpl.
      apply le_n_S, plus_le_compat_l, plus_le_compat_l, plus_le_compat_l; auto.
    }
    { rewrite firstn_app, firstn_length', minus_plus, firstn_app,
        firstn_length', minus_plus, firstn_app, firstn_length', minus_plus;
        try (clear; omega).
      rewrite (eval_sim _ (G t)); auto; intros.
      rewrite HG3, HG2, HG1; try intro; clarify. } }
  destruct x10 as (((?, ?), ?), ?); clarify.
  destruct n6; clarify.
  exists (S (length (mops_hb_check (W + x) (C + t) vs1 vs2 zt t) +
    (length (mops_hb_check (R + x) (C + t) vs3 vs2' zt t) +
    (length (mops_move (C + t, t) (W + x, t) t v) + 2)))); clarify.
  split.
  { repeat rewrite app_length; simpl.
    apply le_n_S, plus_le_compat_l, plus_le_compat_l, plus_le_compat_l; auto. }
  rewrite firstn_app, firstn_length', minus_plus, firstn_app, firstn_length',
     minus_plus, firstn_app, firstn_length', minus_plus; try (clear; omega).
  rewrite (eval_sim _ (G t)); auto; intros.
  rewrite HG3, HG2, HG1; try intro; clarify.
  { exfalso; clear - Hn Hn'.
    repeat rewrite app_length in Hn; simpl in Hn.
    apply le_S_n, (minus_le_compat_r _ _ (length (hb_check (W + x) (C + t) zt
      tmp1 tmp2))) in Hn; rewrite minus_plus in Hn.
    apply (minus_le_compat_r _ _ (length (hb_check (R + x) (C + t) zt
      tmp1 tmp2))) in Hn; rewrite minus_plus in Hn.
    apply (minus_le_compat_r _ _ (length (move (C + t, t) (W + x, t) tmp1)))
      in Hn; rewrite minus_plus, Hn' in Hn; omega. }
  { clear - n4.
    destruct (le_gt_dec (n - length (hb_check (W + x) (C + t) zt tmp1 tmp2) -
      length (hb_check (R + x) (C + t) zt tmp1 tmp2))
      (length (move (C + t, t) (R + x, t) tmp1))); [contradiction|].
    apply lt_le_weak; auto. }
Qed.

Lemma max_vc_mem_n : forall t C1 C2 z G n vs lc G' vs' cond
  (Hmem : to_mem' G t (firstn n (max_vc C1 C2 z tmp1 tmp2)) vs =
    Some (lc, G', vs', cond))
  (Hn : n <= length (max_vc C1 C2 z tmp1 tmp2)),
  (exists vs1 vs2 n', n' <= length (mops_max_vc C1 C2 vs1 vs2 t z) /\
                      lc = firstn n' (mops_max_vc C1 C2 vs1 vs2 t z)) /\
  forall a, a <> tmp1 -> a <> tmp2 -> G' a = G a.
Proof.
  induction z; clarify.
  - rewrite firstn_nil in *; clarify.
    exists [], [], 0; auto.
  - destruct n; clarify.
    { exists [], [], 0; auto. }
    destruct vs; clarify.
    destruct x as (((?, ?), ?), ?); clarify.
    destruct n; clarify.
    { split; [exists [n0], [n0], 1; clarify|].
      unfold upd; clarify. }
    destruct vs; clarify.
    destruct x as (((?, ?), ?), ?); clarify.
    destruct n; clarify.
    { split; [exists [n0], [n1], 2; clarify|].
      intros; rewrite VectorClocks.upd_old; auto.
      apply VectorClocks.upd_old; auto. }
    destruct n; clarify.
    { split; [exists [n0], [n1], 2; clarify|].
      intros; rewrite VectorClocks.upd_old; auto.
      rewrite VectorClocks.upd_old, VectorClocks.upd_old; auto. }
    destruct x as (((?, ?), ?), ?); clarify.
    exploit IHz; eauto.
    { omega. }
    intros ((vs1 & vs2 & n' & ?) & HG); subst.
    repeat rewrite upd_new in *.
    rewrite VectorClocks.upd_old, upd_new in *; auto.
    split.
    + exists (n0 :: vs1), (n1 :: vs2), (S (S (S n'))); clarify; omega.
    + intros; rewrite HG; auto.
      do 3 (rewrite VectorClocks.upd_old; auto).
Qed.

Lemma max_vc_mem : forall t C1 C2 z G vs lc G' vs' cond
  (Hmem : to_mem' G t (max_vc C1 C2 z tmp1 tmp2) vs =
    Some (lc, G', vs', cond)),
  (exists vs1 vs2, lc = mops_max_vc C1 C2 vs1 vs2 t z) /\
  forall a, a <> tmp1 -> a <> tmp2 -> G' a = G a.
Proof.
  induction z; clarify.
  - exists [], []; auto.
  - destruct vs; clarify.
    destruct x as (((?, ?), ?), ?); clarify.
    destruct vs; clarify.
    destruct x as (((?, ?), ?), ?); clarify.
    destruct x0 as (((?, ?), ?), ?); clarify.
    exploit IHz; eauto; intros ((vs1 & vs2 & ?) & HG); subst.
    repeat rewrite upd_new in *.
    rewrite VectorClocks.upd_old, upd_new in *; auto.
    split.
    + exists (n :: vs1), (n0 :: vs2); auto.
    + intros; rewrite HG; auto.
      do 3 (rewrite VectorClocks.upd_old; auto).
Qed.

Transparent move mops_move.

Lemma set_vc_mem_n : forall t C1 C2 z G n vs lc G' vs' cond
  (Hmem : to_mem' G t (firstn n (set_vc C1 C2 z tmp1)) vs =
    Some (lc, G', vs', cond))
  (Hn : n <= length (set_vc C1 C2 z tmp1)),
  (exists vs n', n' <= length (mops_set_vc C1 C2 z t vs) /\
                 lc = firstn n' (mops_set_vc C1 C2 z t vs)) /\
  forall a, a <> tmp1 -> G' a = G a.
Proof.
  induction z; clarify.
  - rewrite firstn_nil in *; clarify.
    exists [], 0; auto.
  - destruct n; clarify.
    { exists [], 0; auto. }
    destruct vs; clarify.
    destruct x as (((?, ?), ?), ?); clarify.
    destruct n; clarify.
    { split; [exists [n0], 1; clarify; omega|].
      unfold upd; clarify. }
    destruct x as (((?, ?), ?), ?); clarify.
    exploit IHz; eauto.
    { omega. }
    intros ((vs1 & n' & ?) & HG); subst.
    rewrite upd_new in *.
    split.
    + exists (n0 :: vs1), (S (S n')); clarify; omega.
    + intros; rewrite HG; auto.
      rewrite VectorClocks.upd_old; auto.
Qed.

Lemma set_vc_mem : forall t C1 C2 z G vs lc G' vs' cond
  (Hmem : to_mem' G t (set_vc C1 C2 z tmp1) vs = Some (lc, G', vs', cond)),
  (exists vs, lc = mops_set_vc C1 C2 z t vs) /\
  forall a, a <> tmp1 -> G' a = G a.
Proof.
  induction z; clarify.
  - exists []; auto.
  - destruct vs; clarify.
    destruct x as (((?, ?), ?), ?); clarify.
    destruct x0 as (((?, ?), ?), ?); clarify.
    exploit IHz; eauto; intros ((vs1 & ?) & HG); subst.
    rewrite upd_new in *.
    split.
    + exists (n :: vs1); auto.
    + intros; rewrite HG; auto.
      rewrite VectorClocks.upd_old; auto.
Qed.

Opaque move mops_move.

Lemma t_steps_lock_n : forall P G t lo lc P1 G1 m li (Hdistinct : distinct P)
  (Hin : In (t, instrument_instr (Lock m) t ++ li) P)
  n (Hsteps : t_steps P G t n lo lc P1 G1)
  (Hn : n <= length (instrument_instr (Lock m) t)),
  exists vs1 vs2 n', n' <= length (Acq t m ::
    mops_max_vc (L + m) (C + t) vs1 vs2 t zt) /\
    filter (fun c => beq (thread_of c) t) lc =
    firstn n' (Acq t m :: mops_max_vc (L + m) (C + t) vs1 vs2 t zt).
Proof.
  intros.
  exploit t_steps_mem'; eauto; intros (vs & vs' & cond & Heq & Hcond).
  destruct n; clarify.
  { exists [], [], 0; auto. }
  destruct x9 as (((?, ?), ?), ?); clarify.
  repeat rewrite <- app_assoc in *.
  unfold lock_handler in *.
  rewrite firstn_app, le_minus_0, app_nil_r in Heq1; [|omega].
  exploit max_vc_mem_n; eauto.
  { omega. }
  intros ((vs1 & vs2 & n' & ?) & ?); exists vs1, vs2, (S n'); clarify; omega.
Qed.

Lemma t_steps_unlock_n : forall P G t lo lc P1 G1 m li (Hdistinct : distinct P)
  (Hin : In (t, instrument_instr (Unlock m) t ++ li) P)
  n (Hsteps : t_steps P G t n lo lc P1 G1)
  (Hn : n <= length (instrument_instr (Unlock m) t)),
  exists vs v n', n' <= length (mops_set_vc (C + t) (L + m) zt t vs ++
    mops_inc_vc (C + t) v t ++ [Rel t m]) /\
    filter (fun c => beq (thread_of c) t) lc =
    firstn n' (mops_set_vc (C + t) (L + m) zt t vs ++
      mops_inc_vc (C + t) v t ++ [Rel t m]).
Proof.
  intros.
  exploit t_steps_mem'; eauto; intros (vs & vs' & cond & Heq & Hcond).
  unfold instrument_instr, unlock_handler in *;
    repeat rewrite <- app_assoc in *.
  rewrite firstn_app in Heq;
    destruct (le_dec n (length (set_vc (C + t) (L + m) zt tmp1))).
  { rewrite le_minus_0, app_nil_r in Heq; auto.
    exploit set_vc_mem_n; eauto; intros ((vs1 & n' & ?) & ?).
    exists vs1, 0, n'; clarify.
    split; [rewrite app_length; omega|].
    rewrite firstn_app, le_minus_0, app_nil_r; auto. }
  rewrite firstn_length', to_mem'_app in Heq; [|omega].
  rewrite match_false in Heq;
    destruct Heq as ((((?, ?), ?), ?) & Hset & Hrest).
  rewrite match_false in Hrest;
    destruct Hrest as ((((?, ?), ?), ?) & Hrest & ?); clarify.
  exploit set_vc_mem; eauto; intros ((vs1 & ?) & ?); exists vs1; clarify.
  destruct (n - length (set_vc (C + t) (L + m) zt tmp1)) eqn: Hn'; clarify.
  { exists 0, (length (mops_set_vc (C + t) (L + m) zt t vs1)).
    rewrite firstn_app, firstn_length, minus_diag; clarify.
    rewrite app_length; omega. }
  destruct l0; clarify.
  destruct x as (((?, ?), ?), ?); clarify.
  exists n3.
  destruct n2; clarify.
  { exists (length (mops_set_vc (C + t) (L + m) zt t vs1) + 1).
    rewrite firstn_app, firstn_length', minus_plus; [clarify | omega].
    rewrite app_length; simpl; omega. }
  destruct n2; clarify.
  { exists (length (mops_set_vc (C + t) (L + m) zt t vs1) + 1).
    rewrite firstn_app, firstn_length', minus_plus; [clarify | omega].
    rewrite app_length; simpl; omega. }
  destruct x as (((?, ?), ?), ?); clarify.
  repeat rewrite upd_overwrite1 in *; repeat rewrite upd_new in *.
  destruct n2; clarify.
  { exists (length (mops_set_vc (C + t) (L + m) zt t vs1) + 2).
    rewrite firstn_app, firstn_length', minus_plus; [clarify | omega].
    rewrite app_length; simpl; omega. }
  destruct x as (((?, ?), ?), ?); clarify.
  destruct n2; clarify.
  exists (length (mops_set_vc (C + t) (L + m) zt t vs1) + 3).
  rewrite firstn_app, firstn_length', minus_plus; [clarify | omega].
  rewrite app_length; simpl; omega.
  { repeat rewrite app_length in Hn; simpl in Hn; omega. }
Qed.

Lemma t_steps_spawn_n : forall P G t lo lc P1 G1 u li' li
  (Hdistinct : distinct P)
  (Hin : In (t, instrument_instr (Spawn u li') t ++ li) P)
  n (Hsteps : t_steps P G t n lo lc P1 G1)
  (Hn : n <= length (instrument_instr (Spawn u li') t)),
  exists vs1 vs2 v n', n' <= length (mops_max_vc (C + t) (C + u) vs1 vs2 t zt 
    ++ mops_inc_vc (C + t) v t) /\
    filter (fun c => beq (thread_of c) t) lc =
    firstn n' (mops_max_vc (C + t) (C + u) vs1 vs2 t zt ++
      mops_inc_vc (C + t) v t).
Proof.
  intros.
  exploit t_steps_mem'; eauto; intros (vs & vs' & cond & Heq & Hcond).
  simpl in *; unfold spawn_handler in *; repeat rewrite <- app_assoc in *.
  rewrite firstn_app in Heq;
    destruct (le_dec n (length (max_vc (C + t) (C + u) zt tmp1 tmp2))).
  { rewrite le_minus_0, app_nil_r in Heq; auto.
    exploit max_vc_mem_n; eauto; intros ((vs1 & vs2 & n' & ?) & ?).
    exists vs1, vs2, 0, n'; clarify.
    split; [rewrite app_length; omega|].
    rewrite firstn_app, le_minus_0, app_nil_r; auto. }
  rewrite firstn_length', to_mem'_app in Heq; [|omega].
  rewrite match_false in Heq;
    destruct Heq as ((((?, ?), ?), ?) & Hmax & Hrest).
  rewrite match_false in Hrest;
    destruct Hrest as ((((?, ?), ?), ?) & Hrest & ?); clarify.
  exploit max_vc_mem; eauto; intros ((vs1 & vs2 & ?) & ?); exists vs1, vs2;
    clarify.
  destruct (n - length (max_vc (C + t) (C + u) zt tmp1 tmp2)) eqn: Hn';
    clarify.
  { exists 0, (length (mops_max_vc (C + t) (C + u) vs1 vs2 t zt)).
    rewrite firstn_app, firstn_length, minus_diag; clarify.
    rewrite app_length; omega. }
  destruct l0; clarify.
  destruct x as (((?, ?), ?), ?); clarify.
  exists n3.
  destruct n2; clarify.
  { exists (length (mops_max_vc (C + t) (C + u) vs1 vs2 t zt) + 1).
    rewrite firstn_app, firstn_length', minus_plus; [clarify | omega].
    rewrite app_length; simpl; omega. }
  destruct n2; clarify.
  { exists (length (mops_max_vc (C + t) (C + u) vs1 vs2 t zt) + 1).
    rewrite firstn_app, firstn_length', minus_plus; [clarify | omega].
    rewrite app_length; simpl; omega. }
  destruct x as (((?, ?), ?), ?); clarify.
  repeat rewrite upd_overwrite1 in *; repeat rewrite upd_new in *.
  destruct n2; clarify.
  { exists (length (mops_max_vc (C + t) (C + u) vs1 vs2 t zt) + 2).
    rewrite firstn_app, firstn_length', minus_plus; [clarify | omega].
    rewrite app_length; simpl; omega. }
  destruct n2; clarify.
  exists (length (mops_max_vc (C + t) (C + u) vs1 vs2 t zt) + 2).
  rewrite firstn_app, firstn_length', minus_plus; [clarify | omega].
  rewrite app_length; simpl; omega.
  { repeat rewrite app_length in Hn; simpl in Hn; omega. }
Qed.

Lemma t_steps_wait_n : forall P G t lo lc P1 G1 u li (Hdistinct : distinct P)
  (Hin : In (t, instrument_instr (Wait u) t ++ li) P)
  n (Hsteps : t_steps P G t n lo lc P1 G1)
  (Hn : n <= length (instrument_instr (Wait u) t)),
  exists vs1 vs2 v n', n' <= length (mops_max_vc (C + u) (C + t) vs1 vs2 t zt ++
    mops_inc_vc' (C + u) v t u) /\
    filter (fun c => beq (thread_of c) t) lc =
    firstn n' (mops_max_vc (C + u) (C + t) vs1 vs2 t zt ++
      mops_inc_vc' (C + u) v t u).
Proof.
  intros.
  exploit t_steps_mem'; eauto; intros (vs & vs' & cond & Heq & Hcond).
  simpl in *; destruct n; clarify.
  { exists [], [], 0, 0; auto. }
  unfold wait_handler in *; rewrite <- app_assoc in *.
  rewrite firstn_app in Heq;
    destruct (le_dec n (length (max_vc (C + u) (C + t) zt tmp1 tmp2))).
  { rewrite le_minus_0, app_nil_r in Heq; auto.
    exploit max_vc_mem_n; eauto; intros ((vs1 & vs2 & n' & ?) & ?).
    exists vs1, vs2, 0, n'; clarify.
    split; [rewrite app_length; simpl; omega|].
    rewrite firstn_app, le_minus_0, app_nil_r; auto. }
  rewrite firstn_length', to_mem'_app in Heq; [|omega].
  rewrite match_false in Heq;
    destruct Heq as ((((?, ?), ?), ?) & Hmax & Hrest).
  rewrite match_false in Hrest;
    destruct Hrest as ((((?, ?), ?), ?) & Hrest & ?); clarify.
  exploit max_vc_mem; eauto; intros ((vs1 & vs2 & ?) & ?); exists vs1, vs2;
    clarify.
  destruct (n - length (max_vc (C + u) (C + t) zt tmp1 tmp2)) eqn: Hn';
    clarify.
  { exists 0, (length (mops_max_vc (C + u) (C + t) vs1 vs2 t zt)).
    rewrite firstn_app, firstn_length, minus_diag; clarify.
    rewrite app_length; omega. }
  destruct l0; clarify.
  destruct x9 as (((?, ?), ?), ?); clarify.
  exists n3.
  destruct n2; clarify.
  { exists (length (mops_max_vc (C + u) (C + t) vs1 vs2 t zt) + 1).
    rewrite firstn_app, firstn_length', minus_plus; [clarify | omega].
    rewrite app_length; simpl; omega. }
  destruct n2; clarify.
  { exists (length (mops_max_vc (C + u) (C + t) vs1 vs2 t zt) + 1).
    rewrite firstn_app, firstn_length', minus_plus; [clarify | omega].
    rewrite app_length; simpl; omega. }
  destruct x9 as (((?, ?), ?), ?); clarify.
  repeat rewrite upd_overwrite1 in *; repeat rewrite upd_new in *.
  destruct n2; clarify.
  exists (length (mops_max_vc (C + u) (C + t) vs1 vs2 t zt) + 2).
  rewrite firstn_app, firstn_length', minus_plus; [clarify | omega].
  rewrite app_length; simpl; omega.
  { repeat rewrite app_length in Hn; simpl in Hn; omega. }
Qed.

(*Lemma instrument_own_thread' : forall t (Ht : t < zt) P G lo lc P1 G1
  (Hsteps : exec_star (Some P) G lo lc (Some P1) G1)
  P0 (Hsafe : safe_locs P0) P0' (Hdistinct : distinct P0')
  (Hspawns : safe_spawns P0') (Hsim : state_sim P0 P0') G0 lo0 lc0
  (Hroot : exec_star (Some P0') G0 lo0 lc0 (Some P) G)
  li (Hin : In (t, li) P) li1 (Hin : In (t, li1) P1) (Hlive : li1 <> [])
  t' o c P' G' (Hstep : exec P1 G1 t' o c P' G'),
  Forall (fun c => fst (loc_of c) <> C + t)
    (filter (fun x => negb (beq (thread_of x) t)) (lc ++ opt_to_list c)).
Proof.
  intros; rewrite filter_app, Forall_app.
  split; [eapply instrument_own_thread; eauto|].
  exploit exec_ops; eauto; intro Ht'.
  destruct c; clarify.
  inversion Ht'; unfold negb, beq in *; clarify.
  eapply own_thread; try apply Hsim; auto.
  - exploit exec_step_m; try apply Hstep; try apply exec_refl_m; eauto.
  - eapply exec_star_trans; eauto.
  - eauto.
  - auto.
  - eapply safe_spawns_steps; eauto.
    eapply exec_star_trans; eauto.
Qed.

Transparent move.

Lemma protect_spawn_step : forall P0 (Hsafe : safe_locs P0)
  (Ht : Forall (fun e => fst e < zt) P0) P0' (Hsim : state_sim P0 P0')
  (Hdistinct : distinct P0') (Hspawns : safe_spawns P0') G0 lo0 lc0 P G
  (Hsteps : exec_star (Some P0') G0 lo0 lc0 (Some P) G)
  u (Hl : u < zt) t li (Hin : In (t, li) P) li' (Hspawn : In (Spawn u li') li)
  t' o c P' G' (Hstep : exec P G t' o c P' G'),
  Forall (fun a => forall o, loc_of a <> (C + u, o))
    (filter (fun x => negb (beq (thread_of x) t)) (opt_to_list c)).
Proof.
  intros.
  exploit safe_spawns_steps; eauto; intros (Hcount & Hrest).
  instantiate (1 := u) in Hcount.
  generalize (in_split _ _ Hin); intros (Pa & Pb & ?); subst.
  rewrite spawn_count_app in *; clarify.
  exploit has_spawn; eauto; intro.
  exploit distinct_steps; eauto; intro.
  exploit exec_ops; eauto; intro Hops.
  destruct (eq_dec t' t).
  { subst; rewrite (filter_negb_none _ Hops); auto. }
  destruct c; clarify.
  constructor; auto.
  repeat intro; exploit instrument_thread''; eauto; intros [? | Hspawn'].
  { subst; exploit exec_result; eauto; intros (? & ? & ? & ? & ? & Heq & ?).
    exploit Hrest; [|omega].
    rewrite Heq; apply split_in. }
  destruct Hspawn' as (? & ? & ? & ? & i' & n' & rest & ? & ? & ? & ? & Hin' &
    ?); clarify.
  destruct i'; try contradiction; clarify.
  - assert (spawn_count t0 (Pa ++ Pb) > 0);
      [|rewrite spawn_count_app in *; omega].
    rewrite app_length in *; simpl in *.
    rewrite skipn_app, le_minus_0 in *; [|omega].
    eapply lt_le_trans; [|apply has_spawn_thread; rewrite in_app in *;
      simpl in Hin'; destruct Hin' as [? | [? | ?]]; clarify; eauto].
    eapply has_spawn; simpl; repeat rewrite in_app; simpl; eauto.
  - exploit Hrest; eauto; omega.
Qed.*)

Lemma instrument_indep_n : forall P0 G0 t o c P G lo lc P1 G1 P2 G2 i rest
  (Hdistinct : distinct P0) P0' (Hsim : state_sim P0' P0)
  (Hsafe : safe_locs P0') (Hfresh : fresh_tmps P0')
  (Ht : Forall (fun e => fst e < zt) P0')
  (Hlocks : forall l, locks l P0 -> good_lock (l, 0) P0)
  (Hlocks2 : forall l, l < zl -> well_locked l P0)
  (HX_locks : forall v, v < zv -> good_lock (X + v, 0) P0)
  (Hvars : forall v, v < zv -> good_var v P0) 
  (Hspawns : safe_spawns P0) (Hwaits : safe_waits P0)
  (Hsafe_i : safe_instr i) (Hfresh_i : fresh tmp1 i /\ fresh tmp2 i)
  lo0 lc0 (Hroot : exec_star (Some P0) G0 lo0 lc0 (Some P1) G1)
  (Ht1 : t < zt) (Hin : In (t, instrument_instr i t ++ rest) P1)
  (Hstep1 : exec P1 G1 t o c (Some P) G)
  (Hsteps : exec_star (Some P) G lo lc (Some P2) G2)
  n (Hn : n < length (instrument_instr i t))
  (Hin' : In (t, skipn n (instrument_instr i t) ++ rest) P2)
  t' o' c' P3 G3 (Hstep' : exec P2 G2 t' o' c' P3 G3)
  m (Hcon : consistent (m ++ lc0 ++ opt_to_list c ++ lc ++ opt_to_list c'))
  (Hinit : forall l, l < zl -> initialized m (l, 0))
  (HX_init : forall v, v < zv -> initialized m (X + v, 0)),
  Forall (fun c1 => Forall (fun c2 => loc_of c2 <> loc_of c1)
    (filter (fun c => beq (thread_of c) t)
            (opt_to_list c ++ lc ++ opt_to_list c')))
    (filter (fun x => negb (beq (thread_of x) t)) (lc ++ opt_to_list c')).
Proof.
  admit.
(*  intros.
  exploit step_thread'; eauto; intros (i' & ? & Hin1 & ?).
  exploit distinct_steps; eauto; intro Hdistinct1.
  exploit distinct_step; eauto; intro Hdistinct'.
  exploit distinct_steps; eauto; intro Hdistinct2.
  exploit distinct_in; [try apply Hdistinct1 | eauto | apply Hin | intro Hi].
  rewrite <- (firstn_skipn n (instrument_instr i t)), <- app_assoc in Hin.
  exploit exec_thread'; try apply Hdistinct1; eauto.
  rewrite List.firstn_length, Min.min_l; [|omega]; intro Ht_steps.
  rewrite app_assoc, firstn_skipn in Hin.
  assert (n <> 0).
  { intro; clarify.
    exploit exec_keep; eauto; clarify.
    exploit distinct_in; [apply Hdistinct1 | apply Hin1 | eauto |
      apply skip_cons_neq]. }
  destruct i; try destruct x0.
  - generalize (in_split _ _ Hin); clarify.
    exploit exec_next; eauto; clarify.
    exploit exec_keep; try apply Hsteps; eauto; clarify.
    destruct n; [|omega].
    exploit distinct_in.
    { apply Hdistinct2. }
    { apply Hin'. }
    { eauto. }
    simpl; intro; exploit skip_cons_neq; eauto; clarify.
  - assert (exists vs1 vs2 vt v0 n', n' <= length (Acq t (X + v) ::
        mops_hb_check (W + v) (C + t) vs1 vs2 zt t ++
        mops_move (C + t, t) (R + v, t) t vt ++
        [Read t (v, n0) v0; Rel t (X + v)]) /\
      filter (fun c0 : conc_op => beq (thread_of c0) t)
             (opt_to_list c ++ lc ++ opt_to_list c') =
      firstn n' (Acq t (X + v) :: mops_hb_check (W + v) (C + t) vs1 vs2 zt t 
        ++ mops_move (C + t, t) (R + v, t) t vt ++
        [Read t (v, n0) v0; Rel t (X + v)]))
      as (vs1 & vs2 & vt & v0 & n' & Hn' & Heq).
    { destruct (eq_dec t' t).
      + subst; exploit t_steps_add_t; try apply Ht_steps; eauto; intro Ht'.
        exploit t_steps_load_n; try apply Ht'; eauto.
        rewrite <- app_assoc; auto.
      + exploit t_steps_add_other; try apply Ht_steps; eauto; intro Ht'.
        exploit t_steps_load_n; try apply Ht'; eauto; [omega|].
        rewrite <- app_assoc; auto. }
    rewrite Heq; clear Heq.
    generalize (in_split _ _ Hin); clarify.
    exploit exec_next; eauto; clarify.
    assert (Forall (fun a0 => ~ v_access (v, n0) a0 /\
                              loc_of a0 <> (X + fst (v, n0), 0))
      (filter (fun x => negb (beq (thread_of x) t)) (lc ++ opt_to_list c')))
      as Haccess.
    { exploit exec_ops; try apply Hstep'; intro Hops.
      assert (Forall (fun a0 : conc_op => a0 <> Rel t (X + fst (v, n0))) lc).
      { rewrite Forall_forall; repeat intro; subst.
        clear Ht_steps; destruct n; clarify.
        exploit rel_inv'; try apply Hsteps; try apply Hin'; eauto.
        { rewrite app_assoc, firstn_skipn; apply split_in. }
        rewrite firstn_app, in_app; intros [? | ?].
        * exploit firstn_in; eauto.
          repeat rewrite in_app; intros [? | ?]; clarify.
          exploit hb_check_instrs; eauto; clarify.
        * destruct (n - length (hb_check (W + v) (C + t) zt tmp1 tmp2 ++
            move (C + t, t) (R + v, t) tmp1)) eqn: Hrest; clarify.
          destruct n1; clarify.
          repeat rewrite app_length in *; simpl in *; omega. }
      destruct (eq_dec t' t).
      + subst; rewrite filter_app, (filter_negb_none _ Hops), app_nil_r.
        eapply protect_held; try apply Hsafe_i1; try apply Hsim;
          try apply Hsteps; auto.
        { eapply exec_step_inv; eauto. }
        { rewrite app_assoc; apply can_read_arwritten.
          eapply consistent_app_SC; do 2 rewrite <- app_assoc; simpl; eauto. }
        { rewrite <- app_assoc; simpl.
          eapply consistent_app_SC; do 2 rewrite <- app_assoc; simpl; eauto. }
      + exploit exec_step_inv; try apply Hsteps; eauto; intro Hsteps'.
        eapply protect_held; try apply Hsafe_i1; try apply Hsim;
          try apply Hsteps'; auto.
        { eapply exec_step_inv; eauto. }
        { rewrite app_assoc; apply can_read_arwritten.
          eapply consistent_app_SC; do 2 rewrite <- app_assoc; simpl; eauto. }
        { rewrite Forall_app; split; auto.
          destruct c'; [|simpl; auto].
          constructor; auto; intro; subst.
          inversion Hstep'; clarify. }
        { rewrite <- app_assoc; simpl; auto. } }
    rewrite Forall_forall in *; intros ? Ha; specialize (Haccess _ Ha).
    apply Forall_firstn.
    constructor; clarify.
    exploit instrument_own_thread'; try apply Hsim; eauto.
    { eapply exec_step_inv; eauto. }
    { intro; exploit app_eq_nil; eauto; intros [? _].
      rewrite skipn_all_iff in *; simpl in *; omega. }
    rewrite Forall_forall; intro Hthread; specialize (Hthread _ Ha).
    rewrite Forall_app; split.
    + rewrite Forall_forall; intros.
      exploit in_mops_hb_check; eauto.
      destruct x2; auto.
      simpl; intros Hx ?; subst.
      destruct Hx as [Hx | ?]; auto.
      contradiction Haccess1.
      unfold v_access; setoid_rewrite <- Hx.
      destruct (loc_of x); eauto.
    + repeat constructor; simpl; intro Heq; rewrite <- Heq in *; clarify.
      * contradiction Haccess1.
        unfold v_access; setoid_rewrite <- Heq; eauto.
      * contradiction Haccess1.
        unfold v_access; setoid_rewrite <- Heq; eauto.
  - simpl in Hfresh_i; destruct Hfresh_i.
    assert (exists vs1 vs2 vs2' vs3 v0 n', n' <= length (Acq t (X + v) ::
        mops_hb_check (W + v) (C + t) vs1 vs2 zt t ++
        mops_hb_check (R + v) (C + t) vs3 vs2' zt t ++
        mops_move (C + t, t) (W + v, t) t v0 ++
        [Write t (v, n0) (eval (G1 t) e); Rel t (X + v)]) /\
      filter (fun c0 : conc_op => beq (thread_of c0) t)
             (opt_to_list c ++ lc ++ opt_to_list c') =
      firstn n' (Acq t (X + v) ::
        mops_hb_check (W + v) (C + t) vs1 vs2 zt t ++
        mops_hb_check (R + v) (C + t) vs3 vs2' zt t ++
        mops_move (C + t, t) (W + v, t) t v0 ++
        [Write t (v, n0) (eval (G1 t) e); Rel t (X + v)]))
      as (vs1 & vs2 & vs2' & vs3 & v0 & n' & Hn' & Heq).
    { destruct (eq_dec t' t).
      + subst; exploit t_steps_add_t; try apply Ht_steps; eauto; intro Ht'.
        exploit t_steps_store_n; try apply Ht'; eauto.
        rewrite <- app_assoc; auto.
      + exploit t_steps_add_other; try apply Ht_steps; eauto; intro Ht'.
        exploit t_steps_store_n; try apply Ht'; eauto; [omega|].
        rewrite <- app_assoc; auto. }
    rewrite Heq; clear Heq.
    generalize (in_split _ _ Hin); clarify.
    exploit exec_next; eauto; clarify.
    assert (Forall (fun a0 => ~ v_access (v, n0) a0 /\
                              loc_of a0 <> (X + fst (v, n0), 0))
      (filter (fun x => negb (beq (thread_of x) t)) (lc ++ opt_to_list c')))
      as Haccess.
    { exploit exec_ops; try apply Hstep'; intro Hops.
      assert (Forall (fun a0 : conc_op => a0 <> Rel t (X + fst (v, n0))) lc).
      { rewrite Forall_forall; repeat intro; subst.
        clear Ht_steps; destruct n; clarify.
        exploit rel_inv'; try apply Hsteps; try apply Hin'; eauto.
        { rewrite app_assoc, firstn_skipn; apply split_in. }
        rewrite firstn_app, in_app; intros [? | ?].
        * exploit firstn_in; eauto.
          repeat rewrite in_app; intros [? | [? | ?]]; clarify;
            exploit hb_check_instrs; eauto; clarify.
        * destruct (n - length (hb_check (W + v) (C + t) zt tmp1 tmp2 ++
            hb_check (R + v) (C + t) zt tmp1 tmp2 ++
            move (C + t, t) (W + v, t) tmp1)) eqn: Hrest; clarify.
          destruct n1; clarify.
          repeat rewrite app_length in *; simpl in *; omega. }
      destruct (eq_dec t' t).
      + subst; rewrite filter_app, (filter_negb_none _ Hops), app_nil_r.
        eapply protect_held; try apply Hsafe_i1; try apply Hsim;
          try apply Hsteps; auto.
        { eapply exec_step_inv; eauto. }
        { rewrite app_assoc; apply can_read_arwritten.
          eapply consistent_app_SC; do 2 rewrite <- app_assoc; simpl; eauto. }
        { rewrite <- app_assoc; simpl.
          eapply consistent_app_SC; do 2 rewrite <- app_assoc; simpl; eauto. }
      + exploit exec_step_inv; try apply Hsteps; eauto; intro Hsteps'.
        eapply protect_held; try apply Hsafe_i1; try apply Hsim;
          try apply Hsteps'; auto.
        { eapply exec_step_inv; eauto. }
        { rewrite app_assoc; apply can_read_arwritten.
          eapply consistent_app_SC; do 2 rewrite <- app_assoc; simpl; eauto. }
        { rewrite Forall_app; split; auto.
          destruct c'; [|simpl; auto].
          constructor; auto; intro; subst.
          inversion Hstep'; clarify. }
        { rewrite <- app_assoc; simpl; auto. } }
    rewrite Forall_forall in *; intros ? Ha; specialize (Haccess _ Ha).
    apply Forall_firstn.
    constructor; clarify.
    exploit instrument_own_thread'; try apply Hsim; eauto.
    { eapply exec_step_inv; eauto. }
    { intro; exploit app_eq_nil; eauto; intros [? _].
      rewrite skipn_all_iff in *; simpl in *; omega. }
    rewrite Forall_forall; intro Hthread; specialize (Hthread _ Ha).
    do 2 rewrite Forall_app; split; [|split].
    + rewrite Forall_forall; intros.
      exploit in_mops_hb_check; eauto.
      destruct x2; auto.
      simpl; intros Hx ?; subst.
      destruct Hx as [Hx | ?]; auto.
      contradiction Haccess1.
      unfold v_access; setoid_rewrite <- Hx.
      destruct (loc_of x); eauto.
    + rewrite Forall_forall; intros.
      exploit in_mops_hb_check; eauto.
      destruct x2; auto.
      simpl; intros Hx ?; subst.
      destruct Hx as [Hx | ?]; auto.
      contradiction Haccess1.
      unfold v_access; setoid_rewrite <- Hx.
      destruct (loc_of x); eauto.
    + repeat constructor; simpl; intro Heq; rewrite <- Heq in *; clarify.
      * contradiction Haccess1.
        unfold v_access; setoid_rewrite <- Heq; eauto.
      * contradiction Haccess1.
        unfold v_access; setoid_rewrite <- Heq; eauto.
  - assert (exists vs1 vs2 n', n' <= length (Acq t m0 ::
        mops_max_vc (L + m0) (C + t) vs1 vs2 t zt) /\
      filter (fun c0 : conc_op => beq (thread_of c0) t)
             (opt_to_list c ++ lc ++ opt_to_list c') =
      firstn n' (Acq t m0 :: mops_max_vc (L + m0) (C + t) vs1 vs2 t zt))
      as (vs1 & vs2 & n' & Hn' & Heq).
    { destruct (eq_dec t' t).
      + subst; exploit t_steps_add_t; try apply Ht_steps; eauto; intro Ht'.
        exploit t_steps_lock_n; try apply Ht'; eauto.
        rewrite <- app_assoc; auto.
      + exploit t_steps_add_other; try apply Ht_steps; eauto; intro Ht'.
        exploit t_steps_lock_n; try apply Ht'; eauto; [omega|].
        rewrite <- app_assoc; auto. }
    rewrite Heq; clear Heq.
    generalize (in_split _ _ Hin); clarify.
    exploit exec_next; eauto; clarify.
    specialize (Hlocks m0); use Hlocks.
    assert (Forall (fun a0 : conc_op => a0 <> Rel t m0) lc).
    { rewrite Forall_forall; repeat intro; subst.
      clear Ht_steps; destruct n; clarify.
      exploit rel_inv'; try apply Hsteps; try apply Hin'; eauto.
      { rewrite app_assoc, firstn_skipn; apply split_in. }
      intro; exploit firstn_in; eauto; intro.
      exploit max_vc_instrs; eauto; clarify. }
    exploit exec_ops; try apply Hstep'; intro Hops.
    assert (Forall (fun a0 => loc_of a0 <> (m0, 0))
      (filter (fun x => negb (beq (thread_of x) t)) (lc ++ opt_to_list c')))
      as Haccess.
    { destruct (eq_dec t' t).
      + subst; rewrite filter_app, (filter_negb_none _ Hops), app_nil_r.
        eapply protect_self; try apply Hsafe_i1; try apply Hsim;
          try apply Hsteps; auto.
        { eapply exec_step_inv; eauto. }
        { rewrite app_assoc; apply can_read_arwritten.
          eapply consistent_app_SC; do 2 rewrite <- app_assoc; simpl; eauto. }
        { rewrite <- app_assoc; simpl.
          eapply consistent_app_SC; do 2 rewrite <- app_assoc; simpl; eauto. }
      + exploit exec_step_inv; try apply Hsteps; eauto; intro Hsteps'.
        eapply protect_self; try apply Hsafe_i1; try apply Hsim;
          try apply Hsteps'; auto.
        { eapply exec_step_inv; eauto. }
        { rewrite app_assoc; apply can_read_arwritten.
          eapply consistent_app_SC; do 2 rewrite <- app_assoc; simpl; eauto. }
        { rewrite Forall_app; split; auto.
          destruct c'; [|simpl; auto].
          constructor; auto; intro; subst.
          inversion Hstep'; clarify. }
        { rewrite <- app_assoc; simpl; auto. } }
    assert (Forall (fun a0 => forall o, loc_of a0 <> (L + m0, o))
      (filter (fun x => negb (beq (thread_of x) t)) (lc ++ opt_to_list c')))
      as HL.
    { destruct (eq_dec t' t).
      + subst; rewrite filter_app, (filter_negb_none _ Hops), app_nil_r.
        eapply protect_lock; try apply Hsafe_i1; try apply Hsim;
          try apply Hsteps; auto.
        { eapply exec_step_inv; eauto. }
        { rewrite app_assoc; apply can_read_arwritten.
          eapply consistent_app_SC; do 2 rewrite <- app_assoc; simpl; eauto. }
        { rewrite <- app_assoc; simpl.
          eapply consistent_app_SC; do 2 rewrite <- app_assoc; simpl; eauto. }
      + exploit exec_step_inv; try apply Hsteps; eauto; intro Hsteps'.
        eapply protect_lock; try apply Hsafe_i1; try apply Hsim;
          try apply Hsteps'; auto.
        { eapply exec_step_inv; eauto. }
        { rewrite app_assoc; apply can_read_arwritten.
          eapply consistent_app_SC; do 2 rewrite <- app_assoc; simpl; eauto. }
        { rewrite Forall_app; split; auto.
          destruct c'; [|simpl; auto].
          constructor; auto; intro; subst.
          inversion Hstep'; clarify. }
        { rewrite <- app_assoc; simpl; auto. } }
    rewrite Forall_forall in *; intros ? Ha; specialize (Haccess _ Ha);
      specialize (HL _ Ha).
    apply Forall_firstn.
    constructor; clarify.
    exploit instrument_own_thread'; try apply Hsim; eauto.
    { eapply exec_step_inv; eauto. }
    { intro; exploit app_eq_nil; eauto; intros (? & _).
      rewrite skipn_all_iff in *; simpl in *; omega. }
    rewrite Forall_forall; intro Hthread; specialize (Hthread _ Ha).
    rewrite Forall_forall; intros.
    exploit in_mops_max_vc'; eauto.
    repeat intro; destruct x2; clarify.
    destruct (loc_of x); eapply HL; eauto.
    { eapply locks_spec; eauto; clarify. }
  - assert (exists vs v n', n' <= length (mops_set_vc (C + t) (L + m0) zt t vs
      ++ mops_inc_vc (C + t) v t ++ [Rel t m0]) /\
      filter (fun c0 : conc_op => beq (thread_of c0) t)
             (opt_to_list c ++ lc ++ opt_to_list c') =
      firstn n' (mops_set_vc (C + t) (L + m0) zt t vs ++
                 mops_inc_vc (C + t) v t ++ [Rel t m0]))
      as (vs & v & n' & Hn' & Heq).
    { destruct (eq_dec t' t).
      + subst; exploit t_steps_add_t; try apply Ht_steps; eauto; intro Ht'.
        exploit t_steps_unlock_n; try apply Ht'; eauto.
        rewrite <- app_assoc; auto.
      + exploit t_steps_add_other; try apply Ht_steps; eauto; intro Ht'.
        exploit t_steps_unlock_n; try apply Ht'; eauto; [omega|].
        rewrite <- app_assoc; auto. }
    rewrite Heq; clear Heq.
    specialize (Hlocks m0); use Hlocks.
    assert (x = tl (unlock_handler t m0 zt tmp1) ++ Unlock m0 :: rest).
    { simpl in Hi; destruct zt; clarify.
      rewrite <- app_assoc; auto. }
    clarify; exploit unlock_locked; try apply Hlocks; try apply Hsim;
      try apply Hsteps; try apply H; auto.
    { eapply exec_step_inv; eauto. }
    { rewrite Forall_forall; intros.
      exploit tl_in; eauto; intro Hi'.
      setoid_rewrite in_app in Hi'; destruct Hi'; clarify.
      exploit set_vc_instrs; eauto; clarify. }
    { eapply consistent_app_SC.
      do 2 rewrite <- app_assoc; eauto. }
    intro Hheld.
    assert (Forall (fun a0 : conc_op => a0 <> Rel t m0) lc).
    { rewrite Forall_forall; repeat intro; subst.
      clear Ht_steps; destruct n; [clarify|].
      exploit rel_inv'; try apply Hsteps; try apply Hin'; eauto.
      { rewrite skipn_S_tl, app_assoc, firstn_skipn.
        rewrite tl_app; [|destruct zt; clarify].
        rewrite <- app_assoc; auto. }
      rewrite tl_app; [|destruct zt; clarify].
      rewrite firstn_app, le_minus_0, app_nil_r.
      intro Hrel; apply firstn_in, tl_in in Hrel.
      setoid_rewrite in_app in Hrel; clear - Hrel; destruct Hrel; clarify.
      exploit set_vc_instrs; eauto; clarify.
      { rewrite app_length in *; simpl in *.
        clear - Hn; destruct zt; clarify; omega. } }
    exploit exec_ops; try apply Hstep'; intro Hops.
    assert (Forall (fun a0 => loc_of a0 <> (m0, 0))
      (filter (fun x => negb (beq (thread_of x) t)) (lc ++ opt_to_list c')))
      as Haccess.
    { destruct (eq_dec t' t).
      + subst; rewrite filter_app, (filter_negb_none _ Hops), app_nil_r.
        eapply protect_self; try apply Hsafe_i1; try apply Hsim;
          try apply Hsteps; auto.
        { eapply exec_step_inv; eauto. }
        { auto. }
        { rewrite <- app_assoc; simpl.
          eapply consistent_app_SC; do 3 rewrite <- app_assoc; simpl; eauto. }
      + exploit exec_step_inv; try apply Hsteps; eauto; intro Hsteps'.
        eapply protect_self; try apply Hsafe_i1; try apply Hsim;
          try apply Hsteps'; auto.
        { eapply exec_step_inv; eauto. }
        { auto. }
        { rewrite Forall_app; split; auto.
          destruct c'; [|simpl; auto].
          constructor; auto; intro; subst.
          inversion Hstep'; clarify. }
        { rewrite <- app_assoc; simpl; auto. } }
    assert (Forall (fun a0 => forall o, loc_of a0 <> (L + m0, o))
      (filter (fun x => negb (beq (thread_of x) t)) (lc ++ opt_to_list c')))
      as HL.
    { destruct (eq_dec t' t).
      + subst; rewrite filter_app, (filter_negb_none _ Hops), app_nil_r.
        eapply protect_lock; try apply Hsafe_i1; try apply Hsim;
          try apply Hsteps; auto.
        { eapply exec_step_inv; eauto. }
        { auto. }
        { rewrite <- app_assoc; simpl.
          eapply consistent_app_SC; do 3 rewrite <- app_assoc; simpl; eauto. }
      + exploit exec_step_inv; try apply Hsteps; eauto; intro Hsteps'.
        eapply protect_lock; try apply Hsafe_i1; try apply Hsim;
          try apply Hsteps'; auto.
        { eapply exec_step_inv; eauto. }
        { auto. }
        { rewrite Forall_app; split; auto.
          destruct c'; [|simpl; auto].
          constructor; auto; intro; subst.
          inversion Hstep'; clarify. }
        { rewrite <- app_assoc; simpl; auto. } }
    rewrite Forall_forall in *; intros ? Ha; specialize (Haccess _ Ha);
      specialize (HL _ Ha).
    apply Forall_firstn.
    exploit instrument_own_thread'; try apply Hsim; eauto.
    { eapply exec_step_inv; eauto. }
    { intro; exploit app_eq_nil; eauto; intros (? & _).
      rewrite skipn_all_iff in *; simpl in *; omega. }
    rewrite Forall_forall; intro Hthread; specialize (Hthread _ Ha).
    rewrite Forall_app; split.
    * rewrite Forall_forall; intros.
      exploit in_mops_set_vc''; eauto.
      repeat intro; destruct x0; clarify; destruct (loc_of x); clarify.
      eapply HL; auto.
    * rewrite Forall_forall; simpl; intros ? [? | [? |?]] ?; clarify;
        destruct (loc_of x); clarify.
    * eapply locks_spec; eauto.
      rewrite Hi; repeat rewrite in_app; simpl; auto.
  - assert (exists vs1 vs2 v n', n' <= length (mops_max_vc (C + t) (C + t0)
      vs1 vs2 t zt ++ mops_inc_vc (C + t) v t) /\
      filter (fun c0 : conc_op => beq (thread_of c0) t)
             (opt_to_list c ++ lc ++ opt_to_list c') =
      firstn n' (mops_max_vc (C + t) (C + t0) vs1 vs2 t zt ++
                 mops_inc_vc (C + t) v t))
      as (vs1 & vs2 & v & n' & Hn' & Heq).
    { destruct (eq_dec t' t).
      + subst; exploit t_steps_add_t; try apply Ht_steps; eauto; intro Ht'.
        exploit t_steps_spawn_n; try apply Ht'; eauto.
        rewrite <- app_assoc; auto.
      + exploit t_steps_add_other; try apply Ht_steps; eauto; intro Ht'.
        exploit t_steps_spawn_n; try apply Ht'; eauto; [omega|].
        rewrite <- app_assoc; auto. }
    rewrite Heq; clear Heq.
    exploit exec_ops; try apply Hstep'; intro Hops; clarify.
    rewrite app_length in Hn; simpl in Hn.
    rewrite skipn_app, le_minus_0 in *; [|omega].
    assert (Forall (fun a0 => forall o, loc_of a0 <> (C + t0, o))
      (filter (fun x => negb (beq (thread_of x) t)) (lc ++ opt_to_list c')))
      as Ht0.
    { rewrite filter_app, Forall_app; split.
      + eapply protect_spawn'; try apply Hsafe_i1; try apply Hsim;
          try apply Hsteps; eauto.
        { eapply exec_step_inv; eauto. }
        { repeat rewrite in_app; simpl; eauto. }
      + eapply protect_spawn_step; try apply Hsafe_i1; try apply Hsim;
          try apply Hstep'; eauto.
        { eapply exec_star_trans; eauto.
          eapply exec_step; eauto. }
        { repeat rewrite in_app; simpl; eauto. } }
    rewrite Forall_forall in *; intros ? Ha; specialize (Ht0 _ Ha).
    apply Forall_firstn.
    exploit instrument_own_thread'; try apply Hsim; eauto.
    { eapply exec_step_inv; eauto. }
    { intro; exploit app_eq_nil; eauto; intros (? & _).
      exploit app_eq_nil; eauto; clarify. }
    rewrite Forall_forall; intro Hthread; specialize (Hthread _ Ha).
    rewrite Forall_app; split.
    * rewrite Forall_forall; intros.
      exploit in_mops_max_vc'; eauto.
      repeat intro; destruct x1; try contradiction; clarify;
        destruct (loc_of x0); clarify; eapply Ht0; eauto.
    * rewrite Forall_forall; simpl; intros ? [? | [? |?]] ?; clarify;
        destruct (loc_of x0); clarify.
  - assert (exists vs1 vs2 v n', n' <= length (mops_max_vc (C + t0) (C + t)
      vs1 vs2 t zt ++ mops_inc_vc' (C + t0) v t t0) /\
      filter (fun c0 : conc_op => beq (thread_of c0) t)
             (opt_to_list c ++ lc ++ opt_to_list c') =
      firstn n' (mops_max_vc (C + t0) (C + t) vs1 vs2 t zt ++
                 mops_inc_vc' (C + t0) v t t0))
      as (vs1 & vs2 & v & n' & Hn' & Heq).
    { destruct (eq_dec t' t).
      + subst; exploit t_steps_add_t; try apply Ht_steps; eauto; intro Ht'.
        exploit t_steps_wait_n; try apply Ht'; eauto.
        rewrite <- app_assoc; auto.
      + exploit t_steps_add_other; try apply Ht_steps; eauto; intro Ht'.
        exploit t_steps_wait_n; try apply Ht'; eauto; [omega|].
        rewrite <- app_assoc; auto. }
    rewrite Heq; clear Heq.
    exploit exec_ops; eauto; intro Hops.
    simpl in Hin; assert (In (t0, []) P1).
    { generalize (in_split _ _ Hin); clarify.
      exploit exec_next; eauto; clarify. }
    exploit protect_wait'; try apply Hsim; try apply Hin; eauto.
    { eapply exec_step; [|eapply exec_step_inv]; eauto. }
    rewrite filter_app, Forall_app; intros (_ & Ht0).
    exploit instrument_own_thread'; try apply Hsim; eauto.
    { eapply exec_step_inv; eauto. }
    { intro; exploit app_eq_nil; eauto; intros (? & _).
      rewrite skipn_all_iff in *; simpl in *; omega. }
    repeat rewrite Forall_forall in *; intros Hthread ? Ha;
      specialize (Hthread _ Ha); specialize (Ht0 _ Ha).
    apply Forall_firstn; rewrite Forall_app; split.
    * rewrite Forall_forall; intros.
      exploit in_mops_max_vc'; eauto.
      destruct x1; try contradiction; repeat intro; clarify;
        destruct (loc_of x0); clarify; eapply Ht0; eauto.
    * rewrite Forall_forall; simpl; intros ? [? | [? | ?]]; clarify.
  - generalize (in_split _ _ Hin); clarify.
    exploit exec_next; eauto; clarify.
    exploit exec_keep; try apply Hsteps; eauto; clarify.
    destruct n; [|omega].
    exploit distinct_in.
    { apply Hdistinct2. }
    { apply Hin'. }
    { eauto. }
    simpl; intro; exploit skip_cons_neq; eauto; clarify.*)
Qed.
(*
Corollary instrument_indep' : forall P0 G0 t o c P G lo lc P1 G1 o' c' P2 G2 i
  rest (Hdistinct : distinct P0) P0' (Hsim : state_sim P0' P0)
  (Hsafe : safe_locs P0') (Hfresh : fresh_tmps P0')
  (Ht : Forall (fun e => fst e < zt) P0')
  (Hlocks : forall l, locks l P0 -> good_lock (l, 0) P0)
  (Hlocks2 : forall l, l < zl -> well_locked l P0)
  (HX_locks : forall v, v < zv -> good_lock (X + v, 0) P0)
  (Hvars : forall v, v < zv -> good_var v P0) 
  (Hspawns : safe_spawns P0) (Hwaits : safe_waits P0)
  (Hsafe_i : safe_instr i) (Hfresh_i : fresh tmp1 i /\ fresh tmp2 i)
  lo0 lc0 (Hroot : exec_star (Some P0) G0 lo0 lc0 (Some P1) G1)
  (Ht1 : t < zt) (Hin : In (t, instrument_instr i t ++ rest) P1)
  (Hstep1 : exec P1 G1 t o c (Some P) G)
  (Hsteps : exec_star (Some P) G lo lc (Some P2) G2)
  P3 G3 (Hstep2 : exec P2 G2 t o' c' (Some P3) G3) (Hin' : In (t, rest) P3)
  m (Hcon : consistent (m ++ lc0 ++ opt_to_list c ++ lc ++ opt_to_list c'))
  (Hinit : forall l, l < zl -> initialized m (l, 0))
  (HX_init : forall v, v < zv -> initialized m (X + v, 0)),
  Forall (fun c1 => Forall (fun c2 => loc_of c2 <> loc_of c1)
    (filter (fun c => beq (thread_of c) t)
            (opt_to_list c ++ lc ++ opt_to_list c')))
    (filter (fun x => negb (beq (thread_of x) t)) lc).
Proof.
  intros.
  exploit distinct_steps; eauto; intro.
  exploit exec_keep; eauto.
  { eapply exec_step; eauto. }
  intros (n & Hin2).
  exploit distinct_step; eauto; intro.
  exploit distinct_steps; eauto; intro.
  exploit step_thread; eauto; intros (? & ? & Hskip & ?).
  exploit distinct_step; eauto; intro.
  exploit distinct_in; [eauto | eauto | apply Hin' | clarify].
  rewrite skipn_app in Hskip.
  destruct (le_gt_dec (length (instrument_instr i t)) n).
  { rewrite skipn_all in Hskip; auto.
    simpl in Hskip; exploit skip_cons_neq; eauto; contradiction. }
  rewrite <- app_nil_r.
  erewrite <- filter_negb_none, <- filter_app.
  eapply instrument_indep_n; try apply Hsim; eauto.
  - rewrite skipn_app, not_le_minus_0 in Hin2; [auto | omega].
  - eapply exec_ops; eauto.
Qed.

Lemma first_mem : forall P G t o c P' G' (Hstep : exec P G t o c P' G')
  (Hdistinct : distinct P)
  i rest (Hinstr : In (t, instrument_instr i t ++ rest) P)
  (Hi : match i with Assign _ _ | Assert_le _ _ => False | _ => True end),
  exists a, o = Some a.
Proof.
  intros.
  exploit exec_result; eauto; intros (? & i1 & ? & ? & v & ?); clarify.
  exploit distinct_in; [eauto | apply split_in | apply Hinstr | intro Heq].
  destruct i; try destruct x2; clarify; eauto.
  - destruct zt; clarify; eauto.
  - destruct zt; clarify; eauto.
Qed.

Lemma bounded_sim' : forall P P' (Hsim : state_sim P P')
  (Hbound : bounded_threads P'), Forall (fun e => fst e < zt) P.
Proof.
  induction P; clarify.
  inversion Hsim; inversion Hbound; clarify.
  constructor; [|eapply IHP; eauto].
  destruct a, y; clarify.
Qed.
*)
Lemma noninterference : forall t P P0 (Hsim0 : state_sim P P0)
  (Hdistinct : distinct P0) (Hsafe0 : safe_locs P) (Hfresh0 : fresh_tmps P)
  (Ht : Forall (fun e => fst e < zt) P)
  (Hlocks : forall l, locks l P0 -> good_lock (l, 0) P0)
  (Hlocks2 : forall l, l < zl -> well_locked l P0)
  (HX_locks : forall v, v < zv -> good_lock (X + v, 0) P0)
  (Hvars : forall v, v < zv -> good_var v P0) 
  (Hspawns : safe_spawns P0) (Hwaits : safe_waits P0)
  P' P0' (Hsim : state_sim P' P0')
  (Hsafe : safe_locs P') (Hfresh : fresh_tmps P')
  G0 lo0 lc0 G0' (Hroot0 : exec_star (Some P0) G0 lo0 lc0 (Some P0') G0')
  lo0' lc0' P1 G1 (Hroot : exec_star_t t (Some P0') G0' lo0' lc0' (Some P1) G1)
  lo lc P2 G2 (Hsteps : exec_star_minus t (Some P1) G1 lo lc (Some P2) G2)
  (Hsuffix2 : state_suffix P' P2) o c P3 G3
  (Hstep : exec P2 G2 t o c P3 G3)
  m (Hcon : consistent (m ++ lc0 ++ lc0' ++ lc ++ opt_to_list c))
  (Hinit : forall l, l < zl -> initialized m (l, 0))
  (HX_init : forall v, v < zv -> initialized m (X + v, 0)),
  Forall (fun c' => match c with Some a => loc_of c' <> loc_of a
      | None => True end) lc. 
Proof.
  admit.
(*  intros.
  exploit distinct_steps; eauto; intro.
  assert (forall t', t' <> t -> Forall (fun c1 =>
    Forall (fun c2 => loc_of c2 <> loc_of c1)
    (filter (fun c => beq (thread_of c) t') lc))
    (filter (fun x => negb (beq (thread_of x) t')) (lc ++ opt_to_list c)))
    as Hindep.
  { exploit state_suffix_inv; try apply Hsim; auto.
    { eapply exec_t_exec; eauto. }
    { eapply exec_minus_exec; eauto. }
    { auto. }
    intro Hsuffix1.
    exploit distinct_steps; eauto.
    { eapply exec_t_exec; eauto. }
    intro; assert (exists P1' G1' lo1' lc1',
      exec_star_t t (Some P0') G0' lo0' lc0' (Some P1') G1' /\
      exec_star_minus t (Some P1') G1' lo1' lc1' (Some P1) G1 /\
      Forall (fun c' => Forall (fun c1 => Forall (fun c2 =>
        loc_of c2 <> loc_of c1)
        (filter (fun c0 => beq (thread_of c0) (VectorClocks.thread_of c')) lc))
        (filter (fun x => negb (beq (thread_of x) (VectorClocks.thread_of c')))
        (lc ++ opt_to_list c))) lo1' /\
      (forall t' li (Hdiff : t' <> t) (Hin : In (t', li) P1)
       (Horig : Forall (fun c' => VectorClocks.thread_of c' <> t') lo1'),
       exists li0, In (t', li0) P' /\ li = instrument li0 t') /\
      consistent (m ++ lc0 ++ lc0' ++ lc1' ++ lc ++ opt_to_list c))
      as (P1' & G1' & lo1' & lc1' & Hroot0' & Hroot' & Hsep & Hinstr & Hcon').
    { do 5 eexists; eauto.
      split; [apply exec_refl_m | clarify].
      exploit Forall2_in2; eauto; intros ((?, ?) & ?); clarify.
      exploit Forall2_in1; try apply Hsim; eauto; intros ((?, ?) & ?); clarify.
      exploit exec_other_threads; eauto.
      { eapply t_minus; eauto. }
      intro; exploit distinct_in; [eauto | apply Hin | eauto | eauto]. }
    clear Hroot Hcon.
    remember (Some P1) as Pa; remember (Some P2) as Pb; generalize dependent P1;
      generalize dependent lc1'; generalize dependent lo1'; induction Hsteps;
      clarify.
    { rewrite Forall_forall; auto. }
    destruct P'0; [|inversion Hsteps].
    exploit exec_ops; eauto; intro Ht'.
    exploit exec_rd_ops; eauto; intro Ho.
    destruct (find (fun x => beq (VectorClocks.thread_of x) t'0) lo1')
      eqn: Hfind.
    { rewrite find_spec in Hfind; clarify.
      exploit nth_error_in; eauto; intro.
      rewrite Forall_forall in Hsep; exploit Hsep; eauto.
      unfold beq in Hfind21; clarify. }
    destruct (find (fun x => beq (VectorClocks.thread_of x) t') lo1')
      eqn: Hfind'.
    - destruct (eq_dec t'0 t'); clarify.
      rewrite find_spec in Hfind'; clarify.
      exploit nth_error_in; eauto; intro.
      rewrite Forall_forall in Hsep; exploit Hsep; eauto; intro Hsep'.
      rewrite <- Forall_forall in Hsep.
      exploit state_suffix_inter.
      { eauto. }
      { auto. }
      { eapply exec_step, exec_refl; eauto. }
      { eapply exec_minus_exec; eauto. }
      { auto. }
      exploit distinct_step; eauto; intros.
      exploit IHHsteps; try (eapply exec_step_inv_m; eauto); eauto.
      { rewrite Forall_app; split.
        + eapply Forall_impl; eauto; intros ? Hx; clarify.
          rewrite <- app_assoc in Hx.
          setoid_rewrite filter_app in Hx at 2.
          rewrite Forall_app in Hx; clarify.
          eapply Forall_impl; eauto; clarify.
          rewrite filter_app, Forall_app in *; clarify.
        + rewrite Forall_forall; intros.
          rewrite Forall_forall in Ho; exploit Ho; eauto; intro.
          rewrite <- app_assoc in Hsep'.
          setoid_rewrite filter_app in Hsep' at 2.
          rewrite Forall_app in Hsep'; clarify.
          unfold beq in *; clarify.
          rewrite <- e; eapply Forall_impl; eauto; clarify.
          rewrite filter_app, Forall_app in *; clarify. }
      { rewrite <- app_assoc in *; auto. }
      { intros.
        exploit in_step_rev; eauto.
        rewrite Forall_app in Horig; intros [? | [? | ?]]; clarify.
        + exploit (Hinstr t'); eauto; intros (li0 & ? & Heq).
          destruct li0; clarify.
          rewrite Heq in *; exploit first_mem; eauto.
          { destruct i; auto; clarify.
            * exploit Forall2_in1; eauto; intros ((?, ?) & ? & ? & n' & ?);
                clarify.
              destruct n'; [|omega].
              exploit distinct_in; [eauto | apply Hin0 | eauto |].
              intro; eapply cons_neq; eauto.
            * exploit Forall2_in1; eauto; intros ((?, ?) & ? & ? & n' & ?);
                clarify.
              destruct n'; [|omega].
              exploit distinct_in; [eauto | apply Hin0 | eauto |].
              intro; eapply cons_neq; eauto. }
          clarify.
          inversion Ho; inversion Horig2; clarify.
        + exploit in_split; eauto; clarify.
          exploit exec_next; eauto; clarify.
          exploit Forall2_in2.
          { eauto. }
          { rewrite in_app; right; simpl; right; eauto. }
          intros ((?, ?) & ?); clarify.
          contradiction H62222; rewrite in_map_iff.
          exploit Forall2_in1; try apply Hsuffix1; eauto.
          intros ((?, ?) & ?); clarify.
          do 2 eexists; eauto; auto. }
      rewrite <- app_assoc; repeat rewrite (filter_app _ (opt_to_list c0)).
      rewrite filter_none with (l := opt_to_list c0).
      rewrite filter_all with (l := opt_to_list c0).
      simpl; rewrite Forall_app; clarify.
      unfold beq in Hfind'21; destruct c0; clarify.
      constructor; auto.
      inversion Ht'; clarify.
      rewrite Forall_forall; intros.
      rewrite filter_In in *; clarify.
      rewrite Forall_forall in Hsep'; exploit Hsep'.
      { rewrite filter_In, in_app; split; eauto 2.
        unfold negb, beq in *; clarify. }
      intro X; inversion X; auto.
      + rewrite Forall_forall in *; intros.
        exploit Ht'; eauto 2; unfold negb, beq; clarify.
      + rewrite Forall_forall in *; intros.
        exploit Ht'; eauto 2; unfold negb, beq; clarify.
    - rewrite find_fail in *.
      exploit exec_result; eauto; intros (? & i & ? & ? & v & ?); clarify.
      exploit Hinstr; try apply split_in; auto.
      { eapply Forall_impl; eauto; unfold beq; clarify. }
      intros (li0 & ? & Heq); rewrite Heq in *.
      destruct li0; clarify.
      exploit instrument_indep_n; try apply Hsim0; try apply Hexec; eauto;
        try apply split_in.
      { setoid_rewrite Forall_forall in Hsafe; exploit Hsafe; eauto.
        intro X; inversion X; auto. }
      { setoid_rewrite Forall_forall in Hfresh; exploit Hfresh; eauto.
        intro X; inversion X; auto. }
      { eapply exec_star_trans; eauto.
        eapply exec_star_trans; [eapply exec_t_exec | eapply exec_minus_exec];
          eauto. }
      { exploit bounded_sim; try apply Hsim0; auto; intro.
        exploit bounded_steps; eauto; intro.
        exploit bounded_sim'; eauto.
        rewrite Forall_forall; intro X; exploit X; eauto. }
      intro X.
      use X; [|eapply exec_minus_exec; eauto].
      exploit Forall2_in1; try apply Hsuffix2; eauto.
      intros ((?, ?) & ?); clarify.
      rewrite skipn_app' in *; [|omega].
      exploit X; eauto.
      { repeat rewrite <- app_assoc in *; auto. }
      rewrite <- app_assoc; intro Hsep'.
      destruct (eq_dec t'0 t').
      + subst; setoid_rewrite filter_app at 2.
        rewrite (filter_negb_none _ Ht'); simpl.
        eapply Forall_impl; eauto; intros ? Hsep''.
        rewrite app_assoc, filter_app, Forall_app in Hsep''; clarify.
      + do 2 rewrite (filter_app _ (opt_to_list c0)).
        rewrite filter_none with (l := opt_to_list c0).
        rewrite filter_all with (l := opt_to_list c0).
        rewrite Forall_app; split.
        * destruct c0; clarify.
          inversion Ht'; clarify.
          constructor; auto.
          rewrite Forall_forall; intros.
          rewrite filter_In in *; clarify.
          rewrite filter_app, filter_app, Forall_app in Hsep'; clarify.
          rewrite Forall_forall in Hsep'1; exploit Hsep'1; eauto.
          { rewrite filter_In; unfold beq in *; clarify. }
          { intro X; inversion X; auto. }
        * exploit state_suffix_inter.
          { eauto. }
          { auto. }
          { eapply exec_step, exec_refl; eauto. }
          { eapply exec_minus_exec; eauto. }
          { auto. }
          exploit distinct_step; eauto; intros.
          eapply IHHsteps; try (eapply exec_step_inv_m; eauto); eauto.
          { rewrite Forall_app; split.
            + eapply Forall_impl; try apply Hsep; intros ? Hx.
              rewrite <- app_assoc in Hx.
              setoid_rewrite filter_app in Hx at 2.
              rewrite Forall_app in Hx; clarify.
              eapply Forall_impl; eauto; clarify.
              rewrite filter_app, Forall_app in *; clarify.
            + rewrite Forall_forall; intros.
              rewrite Forall_forall in Ho; exploit Ho; eauto; intro.
              rewrite Forall_forall; intros.
              rewrite filter_In in *; clarify.
              rewrite Forall_forall in Hsep'; exploit Hsep'.
              { rewrite filter_In; split; eauto. }
              repeat rewrite filter_app, Forall_app; clarify. }
          { rewrite <- app_assoc in *; auto. }
          { intros.
            exploit in_step_rev; eauto.
            rewrite Forall_app in Horig; intros [? | [? | ?]]; clarify.
            + exploit (Hinstr t'); eauto; intros (li' & ? & Heq').
              destruct li'; clarify.
              rewrite Heq' in *; exploit first_mem; eauto.
              { destruct i1; auto; clarify.
                * exploit Forall2_in1; eauto; intros ((?, ?) & ? & ? & n' & ?);
                    clarify.
                  destruct n'; [|omega].
                  exploit distinct_in; [eauto | apply Hin0 | eauto |].
                  intro; eapply cons_neq; eauto.
                * exploit Forall2_in1; eauto; intros ((?, ?) & ? & ? & n' & ?);
                    clarify.
                  destruct n'; [|omega].
                  exploit distinct_in; [eauto | apply Hin0 | eauto |].
                  intro; eapply cons_neq; eauto. }
              clarify.
              inversion Ho; inversion Horig2; clarify.
            + exploit in_split; eauto; clarify.
              exploit exec_next; eauto; clarify.
              exploit Forall2_in2.
              { eauto. }
              { rewrite in_app; right; simpl; right; eauto. }
              intros ((?, ?) & ?); clarify.
              contradiction H72222; rewrite in_map_iff.
              exploit Forall2_in1; try apply Hsuffix1; eauto.
              intros ((?, ?) & ?); clarify.
              do 2 eexists; eauto; auto. }
        * rewrite Forall_forall in *; intros.
          exploit Ht'; eauto 2; unfold negb, beq; clarify.
        * rewrite Forall_forall in *; intros.
          exploit Ht'; eauto 2; unfold negb, beq; clarify. }
  rewrite Forall_forall; intros.
  exploit exec_minus_ops; eauto; intro Hdiff.
  rewrite Forall_forall in Hdiff; exploit Hdiff; eauto; unfold beq; clarify.
  destruct c; auto.
  specialize (Hindep _ n); rewrite Forall_forall in Hindep.
  exploit exec_ops; eauto; intro Hc; inversion Hc; clarify.
  specialize (Hindep c); rewrite filter_In, in_app in Hindep; use Hindep;
    [|unfold negb, beq in *; clarify].
  rewrite Forall_forall in Hindep; apply Hindep.
  rewrite filter_In; unfold beq; clarify.*)
Qed.

Lemma first_finished : forall P P0 (Hsim0 : state_sim P P0)
  (Hdistinct : distinct P0) (Hsafe0 : safe_locs P) (Hfresh0 : fresh_tmps P)
  (Ht : Forall (fun e => fst e < zt) P)
  (Hlocks : forall l, locks l P0 -> good_lock (l, 0) P0)
  (Hlocks2 : forall l, l < zl -> well_locked l P0)
  (HX_locks : forall v, v < zv -> good_lock (X + v, 0) P0)
  (Hvars : forall v, v < zv -> good_var v P0) 
  (Hspawns : safe_spawns P0) (Hwaits : safe_waits P0)
  P' P0' (Hsim : state_sim P' P0')
  (Hsafe : safe_locs P') (Hfresh : fresh_tmps P')
  G0 lo0 lc0 G0' (Hroot : exec_star (Some P0) G0 lo0 lc0 (Some P0') G0')
  t P3 (Hsuffix : state_suffix P' P3) 
  P2 G2 lo' lc' G3 (Hsteps2 : exec_star (Some P2) G2 lo' lc' (Some P3) G3)
  lo0' lc0' P1 G1
  (Hsteps0 : exec_star_t t (Some P0') G0' lo0' lc0' (Some P1) G1)
  lo lc  (Hsteps1 : exec_star_minus t (Some P1) G1 lo lc (Some P2) G2)
  o c P4 G4 i li (Hin0 : In (t, i :: li) P')
  (Hin : In (t, last (instrument_instr i t) (Lock 0) :: instrument li t) P3)
  (Hstep : exec P3 G3 t o c (Some P4) G4)
  m (Hcon : consistent (m ++ lc0 ++ lc0' ++ lc ++ lc' ++ opt_to_list c))
  (Hinit : forall l, l < zl -> initialized m (l, 0))
  (HX_init : forall v, v < zv -> initialized m (X + v, 0))
  (HC_init : forall t o, t < zt -> o < zt -> initialized m (C + t, o)),
  exists lo1 lc1 P' G' lo2 lc2, iexec P0' G0' t lo1 lc1 P' G' /\
    exec_star (Some P') G' lo2 lc2 (Some P4) G4 /\
    mem_ext (m ++ lc0 ++ lc1 ++ lc2)
            (m ++ lc0 ++ lc0' ++ lc ++ lc' ++ opt_to_list c).
Proof.
  admit.
(*  intros until G3; intro.
  remember (Some P2) as Pa; remember (Some P3) as Pb; generalize dependent P2;
    induction Hsteps2; clarify.
  - exploit distinct_steps; eauto; intro.
    exploit state_suffix_inv; try apply Hsim; auto.
    { eapply exec_t_exec; eauto. }
    { eapply exec_minus_exec; eauto. }
    { auto. }
    intro; exploit Forall2_in1; eauto; intros ((?, ?) & ?); clarify.
    exploit distinct_steps; eauto.
    { eapply exec_t_exec; eauto. }
    intro; exploit state_suffix_stable; try eapply exec_minus_exec; eauto.
    exploit noninterference; try apply Hroot; eauto.
    intro X; exploit X; eauto.
    clarify; exploit exec_minus_reorder; try apply Hsteps1; eauto.
    { do 2 rewrite app_assoc in Hcon; eauto. }
    intros (P1' & ?); clarify.
    assert (In (t, instrument li t) P1').
    { exploit Forall2_in1; try apply H; eauto; intros ((?, ?) & ?); clarify.
      exploit exec_other_threads; eauto; intro.
      exploit distinct_steps; eauto.
      { eapply exec_minus_exec; eauto. }
      intro; exploit distinct_in; [eauto | apply Hin | eauto | intro Heq].
      rewrite <- Heq in *.
      exploit exec_result; eauto; intros (? & ? & ? & ? & v & ?); clarify.
      exploit distinct_in; [eauto | apply split_in | eauto | clarify].
      destruct (instr_result t (last (instrument_instr i t) (Lock 0)) (G1 t) v)
        as [((((?, ?), ?), ?), ?)|]; clarify.
      apply split_in. }
    exploit exec_t_iexec; try apply H.
    { exploit Forall2_in1; try apply Hsim; eauto; intros ((?, ?) & ?); clarify;
        eauto. }
    { exploit bounded_sim; try apply Ht; eauto; intro Hbound.
      eapply bounded_steps in Hbound; eauto.
      eapply bounded_steps in Hbound; [|eapply exec_t_exec; eauto].
      setoid_rewrite Forall_forall in Hbound; exploit Hbound; eauto; clarify. }
    { setoid_rewrite Forall_forall in Hfresh; exploit Hfresh; eauto; intro X.
      inversion X; clarify. }
    { eapply exec_step_inv_t; eauto. }
    { auto. }
    { do 2 rewrite app_assoc in Hcon; rewrite <- app_nil_r in Hcon.
      rewrite <- app_assoc, <- (app_assoc lc) in Hcon.
      rewrite <- loc_comm_ops_SC, <- app_assoc in Hcon.
      instantiate (1 := m ++ lc0).
      eapply consistent_app_SC; rewrite <- app_assoc, <- (app_assoc lc0');
        eauto.
      { destruct c; clarify. }
      { eapply prog_step; eauto. }
      { eapply prog_steps, exec_minus_exec; eauto. } }
    { intros; eapply init_steps; eauto.
      eapply prog_steps; eauto. }
    intro; do 7 eexists; eauto.
    split; [eapply exec_minus_exec; eauto|].
    split; intro; repeat rewrite <- app_assoc.
    + do 2 rewrite (app_assoc m), (app_assoc (m ++ lc0)); apply loc_comm_ops_SC.
      { destruct c; clarify. }
      { eapply prog_step; eauto. }
      { eapply prog_steps, exec_minus_exec; eauto. }
    + do 2 rewrite (app_assoc m), (app_assoc (m ++ lc0)); apply init_comm'.
      { eapply prog_step; eauto. }
      { eapply prog_steps, exec_minus_exec; eauto. }
  - exploit distinct_steps; eauto; intro.
    destruct P'0; [|inversion Hsteps2].
    specialize (IHHsteps2 _ eq_refl).
    destruct (eq_dec t0 t).
    + subst.
      exploit state_suffix_inv; try apply Hsim; auto.
      { eapply exec_star_trans; [eapply exec_t_exec | eapply exec_minus_exec];
          eauto. }
      { eapply exec_step; eauto. }
      { auto. }
      intro; exploit state_suffix_inv.
      { eauto. }
      { auto. }
      { eapply exec_t_exec; eauto. }
      { eapply exec_minus_exec; eauto. }
      { auto. }
      exploit distinct_steps; eauto 2.
      { eapply exec_t_exec; eauto. }
      intros; exploit state_suffix_stable; try eapply exec_minus_exec, Hsteps1;
        eauto.
      exploit noninterference; try apply Hroot; eauto 2.
      intro X; exploit X; eauto 2.
      { eapply consistent_app_SC.
        do 4 rewrite <- app_assoc; rewrite <- app_assoc in Hcon; eauto. }
      clarify; exploit exec_minus_reorder; try apply Hsteps1; eauto.
      { eapply consistent_app_SC.
        rewrite <- app_assoc in Hcon.
        do 4 rewrite app_assoc in Hcon.
        rewrite <- (app_assoc _ lc1) in Hcon; eauto. }
      clarify; exploit IHHsteps2.
      { eapply exec_step_inv_t; eauto. }
      { eauto. }
      { eauto. }
      { auto. }
      { eauto. }
      { rewrite <- app_assoc, app_assoc, app_assoc in Hcon.
        rewrite loc_comm_ops_SC in Hcon.
        rewrite <- app_assoc, <- app_assoc, (app_assoc lc0') in Hcon; eauto.
        { eapply Forall_impl; eauto; clarify.
          destruct c; clarify. }
        { eapply prog_steps, exec_minus_exec; eauto. }
        { eapply prog_step; eauto. } }
      { auto. }
      { auto. }
      { auto. }
      clarify; do 7 eexists; eauto.
      split; eauto.
      etransitivity; eauto.
      split; intro; repeat rewrite <- app_assoc.
      * do 2 rewrite (app_assoc m), (app_assoc (m ++ lc0));
          apply loc_comm_ops_SC.
        { destruct c; clarify. }
        { eapply prog_step; eauto. }
        { eapply prog_steps, exec_minus_exec; eauto. }
      * do 2 rewrite (app_assoc m), (app_assoc (m ++ lc0));
          split; apply init_comm.  
        { eapply prog_step; eauto. }
        { eapply prog_steps, exec_minus_exec; eauto. }
    + exploit IHHsteps2; eauto 2.
      { eapply exec_step_inv_m; eauto. }
      { rewrite <- app_assoc in *; auto. }
      intros (? & ? & ? & ? & ? & ? & ? & ? & Hm).
      do 7 eexists; eauto; split; eauto.
      rewrite <- app_assoc in *; auto.*)
Qed.

Corollary first_finished' : forall P P0 (Hsim : state_sim P P0)
  (Hdistinct : distinct P0) (Hsafe0 : safe_locs P) (Hfresh0 : fresh_tmps P)
  (Ht : Forall (fun e => fst e < zt) P)
  (Hlocks : forall l, locks l P0 -> good_lock (l, 0) P0)
  (Hlocks2 : forall l, l < zl -> well_locked l P0)
  (HX_locks : forall v, v < zv -> good_lock (X + v, 0) P0)
  (Hvars : forall v, v < zv -> good_var v P0) 
  (Hspawns : safe_spawns P0) (Hwaits : safe_waits P0)
  P' P1 (Hsim : state_sim P' P1)
  (Hsafe : safe_locs P') (Hfresh : fresh_tmps P')
  G0 lo0 lc0 G1 (Hroot : exec_star (Some P0) G0 lo0 lc0 (Some P1) G1)
  t P3 (Hsuffix : state_suffix P' P3)
  lo' lc' G3 (Hsteps2 : exec_star (Some P1) G1 lo' lc' (Some P3) G3)
  o c P4 G4 i li (Hin0 : In (t, i :: li) P')
  (Hin : In (t, last (instrument_instr i t) (Lock 0) :: instrument li t) P3)
  (Hstep : exec P3 G3 t o c (Some P4) G4)
  m (Hcon : consistent (m ++ lc0 ++ lc' ++ opt_to_list c))
  (Hinit : forall l, l < zl -> initialized m (l, 0))
  (HX_init : forall v, v < zv -> initialized m (X + v, 0))
  (HC_init : forall t o, t < zt -> o < zt -> initialized m (C + t, o)),
  exists lo1 lc1 P' G' lo2 lc2, iexec P1 G1 t lo1 lc1 P' G' /\
    exec_star (Some P') G' lo2 lc2 (Some P4) G4 /\
    mem_ext (m ++ lc0 ++ lc1 ++ lc2) (m ++ lc0 ++ lc' ++ opt_to_list c).
Proof.
  intros; eapply first_finished with (lc0' := [])(lc := []); try apply Hroot;
    eauto; constructor.
Qed.

Lemma sim_next_iexec : forall P P1 P2 (Hsim : state_sim P P1)
  (Hsafe : safe_locs P) (Hfresh : fresh_tmps P)
  P0 P0' (Hsim : state_sim P0 P0') (Hdistinct : distinct P0')
  (Hsafe : safe_locs P0) (Hfresh : fresh_tmps P0)
  (Ht : Forall (fun e => fst e < zt) P0)
  (Hlocks : forall l, locks l P0' -> good_lock (l, 0) P0')
  (Hlocks2 : forall l, l < zl -> well_locked l P0')
  (HX_locks : forall v, v < zv -> good_lock (X + v, 0) P0')
  (Hvars : forall v, v < zv -> good_var v P0')
  (Hspawns : safe_spawns P0') (Hwaits : safe_waits P0')
  G0 lo0 lc0 G1 (Hroot : exec_star (Some P0') G0 lo0 lc0 (Some P1) G1)
  lo lc G2 (Hsteps : exec_star (Some P1) G1 lo lc (Some P2) G2)
  m (Hcon : consistent (m ++ lc0 ++ lc))
  (Hinit : forall l, l < zl -> initialized m (l, 0))
  (HX_init : forall v, v < zv -> initialized m (X + v, 0))
  (HC_init : forall t o, t < zt -> o < zt -> initialized m (C + t, o)),
  state_suffix P P2 \/ exists t lo1 lc1 P' G' lo2 lc2,
    iexec P1 G1 t lo1 lc1 P' G' /\ exec_star (Some P') G' lo2 lc2 (Some P2) G2
    /\ mem_ext (m ++ lc0 ++ lc1 ++ lc2) (m ++ lc0 ++ lc).
Proof.
  admit.
(*  intros; remember (Some P1) as Pa; remember (Some P2) as Pb;
    generalize dependent P2; rewrite exec_rev in Hsteps; induction Hsteps;
    clarify.
  { left; apply sim_suffix; auto. }
  rewrite <- exec_rev in Hsteps.
  use IHHsteps; [|eapply consistent_app_SC; do 2 rewrite <- app_assoc; eauto].
  specialize (IHHsteps _ eq_refl); destruct IHHsteps.
  - exploit exec_result; eauto; intros (? & i & ? & ? & v & ? & Hresult).
    exploit distinct_steps; eauto; intro.
    exploit distinct_steps; eauto; intro.
    subst; exploit state_suffix_inv'; eauto; intros (? & li & ? & n & ?);
      clarify.
    destruct li; [rewrite skipn_nil in *|]; clarify.
    destruct (length (skipn n (instrument_instr i0 t))) eqn: Hlen.
    { rewrite skipn_length in Hlen; omega. }
    destruct (instr_result t i (G' t) v) as [((((?, ?), ?), ?), ?)|] eqn: Hi;
      clarify.
    destruct n0.
    + right; rewrite skipn_app, not_le_minus_0 in *; [|omega].
      destruct (skipn n (instrument_instr i0 t)) eqn: Hlast; clarify.
      destruct l; clarify.
      exploit first_finished'; try apply Hroot; eauto.
      intro X; exploit X; eauto; try apply split_in.
      rewrite <- (app_nil_r (instrument_instr _ _)) in Hlast.
      exploit skipn_last; eauto.
      instantiate (1 := Lock 0); clarify; apply split_in.
    + left; destruct o0.
      { destruct i; clarify.
        assert (nth_error (instrument_instr i0 t) n = Some (Spawn t0 li0)).
        { rewrite <- (plus_O_n n), <- skipn_nth.
          rewrite skipn_app, not_le_minus_0 in *; [|omega].
          destruct (skipn n (instrument_instr i0 t)); clarify. }
        exploit spawn_in_handler'; eauto; intros (? & ? & ? & Hn).
        rewrite skipn_length in Hlen; omega. }
      simpl; apply Forall2_app; [|constructor]; clarify.
      rewrite skipn_length in Hlen; exists (S n); split; [omega|].
      generalize (instrument_nonnil i0 t); destruct (instrument_instr i0 t);
        clarify.
      symmetry; eapply skipn_cons; eauto.
  - clarify; right; do 8 eexists; eauto.
    split; [eapply exec_step_inv; eauto|].
    repeat rewrite app_assoc in *; apply mem_ext_app; auto.*)
Qed.

Definition mem_sim' (m1 m2 : list conc_op) :=
  filter (fun c => if meta_loc_dec (loc_of c) then false else true) m2 = m1.

Definition mem_vals m1 m2 := forall x (Hmeta : ~meta_loc x)
  (Hinit1 : initialized m1 x) v,
  can_read m1 x v <-> can_read m2 x v.

Lemma mem_vals_sim : forall m1 m2 m1' (Hcon1 : consistent m1)
  (Hcon2 : consistent m2) (Hsim : mem_sim' m1 m2),
  mem_vals m1 m1' <-> mem_vals m2 m1'.
Proof.
  intros.
  assert (forall x, ~meta_loc x ->
    find (fun c => writesb c x) (rev (filter (fun c =>
      if meta_loc_dec (loc_of c) then false else true) m2)) =
      find (fun c => writesb c x) (rev m2)) as Heq.
  { intros; rewrite rev_filter; apply find_filter.
    unfold implb; intro c; clarify.
    destruct c; clarify; unfold beq in *; clarify. }
  assert (forall x, ~meta_loc x -> (initialized m1 x <-> initialized m2 x))
    as Hinit.
  { unfold mem_sim' in *; clarify.
    unfold initialized; split; intros (v & ?); exists v;
      rewrite last_write in *; clarify; rewrite Heq in *; eauto. }
  assert (forall x v, ~meta_loc x -> initialized m1 x ->
    (can_read m1 x v <-> can_read m2 x v)) as Hval.
  { unfold mem_sim' in *; clarify.
    rewrite init_read; auto.
    rewrite Heq; auto; symmetry; apply init_read; auto.
    rewrite Hinit in *; auto. }
  split; repeat intro.
  - rewrite <- Hinit in *; auto.
    rewrite <- Hval; auto.
  - rewrite Hval; auto.
    rewrite Hinit in *; auto.
Qed.      
  
Lemma mem_vals_ext : forall m m' m1 (Hext : mem_ext m m'),
  mem_vals m m1 <-> mem_vals m' m1.
Proof.
  intros ??? (Hext & Hinit); unfold mem_vals.
  setoid_rewrite Hinit; setoid_rewrite Hext; reflexivity.
Qed.


Global Instance mem_vals_refl: RelationClasses.Reflexive mem_vals.
Proof.
  intros ?????.
  split; clarify.
Qed.

Lemma mem_vals_cond_trans: forall m1 m2 m3
   (Hinit: forall x, initialized m1 x <-> initialized m2 x)
   (Hmem_vals12: mem_vals m1 m2) (Hmem_vals23: mem_vals m2 m3),
                             mem_vals m1 m3.
Proof.
  intros. unfold mem_vals in *.
  intros.
  rewrite Hmem_vals12; auto. rewrite Hmem_vals23; auto.
  reflexivity.
  rewrite <- Hinit. auto.
Qed.

Lemma mem_vals_cond_symm: forall m1 m2
  (Hinit: forall x, initialized m1 x <-> initialized m2 x)                              
  (Hmem_vals12: mem_vals m1 m2),
                            mem_vals m2 m1.
Proof.
  unfold mem_vals. clarify.
  rewrite <- Hmem_vals12; clarify.
  -reflexivity.
  -rewrite Hinit. auto.
Qed.

Lemma mem_vals_app_meta : forall m1 m2 (Hvals : mem_vals m1 m2)
  (Hinit : forall x, ~meta_loc x -> initialized m1 x)
  lc (Hmeta : Forall (fun a => meta_loc (loc_of a)) lc)
  (Hprog : Forall prog_op lc) (Hcon : consistent (m1 ++ lc)),
  mem_vals (m1 ++ lc) m2.
Proof.
  unfold mem_vals; intros.
  rewrite <- Hvals; auto.
  unfold can_read; rewrite <- app_assoc.
  rewrite loc_valid_ops1_SC; clarify.
  split; clarify.
  { eapply Forall_impl; try apply Hmeta; repeat intro; clarify. }
Qed.  

Lemma mem_vals_sim_app : forall m1 m2 c1 c2
  (Hmem_vals: mem_vals m1 m2) (Hsim: mem_sim c1 c2)
  (Hprog: Forall prog_op (opt_to_list c1)) (Hprog2 : Forall prog_op c2)
  (Hcon1 : consistent (m1 ++ opt_to_list c1)) (Hcon2 : consistent (m2 ++ c2)),
  mem_vals (m1++ opt_to_list c1) (m2 ++ c2).
Proof.
  intros.
  unfold mem_sim, mem_vals in *. clarify.
  destruct c1; clarify.
  - destruct (eq_dec (loc_of c) x).
    + inversion Hprog; destruct c; clarify.
      * rewrite can_read_iff_SC; auto.
        rewrite can_read_iff_SC; auto.
        apply Hmem_vals; auto.
        { exploit init_snoc; eauto; clarify. }
        { rewrite Forall_forall; intros c' ?.
          specialize (Hsim c'); destruct Hsim; clarify.
          destruct (meta_loc_dec (loc_of c')); clarify.
          destruct c'; clarify; intro; clarify. }
      * rewrite can_read_write_SC; simpl; eauto; simpl; unfold beq; clarify.
        generalize (Hsim (Write t x v0)); intros [? _]; clarify.
        symmetry; eapply can_read_write_SC; eauto; simpl; unfold beq; clarify.
        rewrite Forall_forall in *; intros a ?.
        exploit Hprog2; eauto; intro.
        intro; exploit writesb_loc; eauto.
        specialize (Hsim a); destruct Hsim as [_ ?]; clarify.
        rewrite <- H4; auto.
      * rewrite can_read_write_SC; simpl; eauto; simpl; unfold beq; clarify.
        generalize (Hsim (ARW t x v0 v')); intros [? _]; clarify.
        symmetry; eapply can_read_write_SC; eauto; simpl; unfold beq; clarify.
        rewrite Forall_forall in *; intros a ?.
        exploit Hprog2; eauto; intro.
        intro; exploit writesb_loc; eauto.
        specialize (Hsim a); destruct Hsim as [_ ?]; clarify.
        rewrite <- H4; auto.
    + inversion Hprog; subst.
      destruct (writesb c x) eqn: Hwrite.
      { exploit writesb_loc; eauto; clarify. }
      rewrite can_read_iff_SC; auto.
      rewrite can_read_iff_SC; auto.
      apply Hmem_vals; auto.
      { exploit init_snoc; eauto; clarify. }
      { rewrite Forall_forall in *; intros a ?.
        destruct (meta_loc_dec (loc_of a)).
        { destruct a; auto; intro; clarify. }
        specialize (Hsim a); destruct Hsim as [_ ?]; clarify.
        destruct a; clarify. }
      { constructor; auto.
        specialize (Hsim c); destruct Hsim as [? _]; clarify.
        destruct c; clarify. }
  - rewrite app_nil_r in *.
    rewrite can_read_iff_SC; auto.
    rewrite Forall_forall in *; intros a ?.
    specialize (Hsim a); destruct Hsim; clarify.
    destruct a; auto; intro; clarify.
Qed.

Lemma mem_ext_vals : forall m1 m2, mem_ext m1 m2 -> mem_vals m1 m2.
Proof. intros; rewrite mem_vals_ext; eauto; reflexivity. Qed.

Lemma mem_vals_step : forall m1 m2 c (Hmem : mem_vals m1 m2)
  (Hprog : prog_op c) (Hcon1 : consistent (m1 ++ [c]))
  (Hcon2 : consistent (m2 ++ [c])), mem_vals (m1 ++ [c]) (m2 ++ [c]).
Proof.
  repeat intro.
  unfold can_read; do 2 rewrite <- app_assoc; simpl.
  destruct (writesb c x) eqn: Hwrite.
  - exploit writesb_val; eauto; clarify.
    exploit writesb_loc; eauto; clarify.
    rewrite consistent_next_write_iff; eauto; simpl; auto.
    rewrite consistent_next_write_iff; eauto; simpl; auto; reflexivity.
  - destruct (eq_dec (loc_of c) x).
    + subst; exploit no_write_read; eauto; clarify.
      rewrite read_noop_SC; auto.
      rewrite (read_noop_SC m2); auto.
      apply Hmem; auto.
      unfold initialized in *; clarify.
      rewrite lower_app, last_op_app, lower_single in Hinit1; destruct Hinit1;
        [|clarify; eauto].
      destruct H as (i & ?); destruct i; clarify.
      rewrite inth_nil in *; clarify.
    + do 2 (rewrite loc_valid_SC; simpl; auto).
      exploit Hmem; eauto.
      { unfold initialized in *; clarify.
        rewrite lower_app, last_op_app, lower_single in Hinit1; destruct Hinit1;
          [|clarify; eauto].
        destruct H as (i & ?); destruct c; clarify; destruct i; clarify;
          destruct i; clarify; rewrite inth_nil in *; clarify. }
      intro X; setoid_rewrite X; split; clarify.
Qed.

Notation is_tmp a := (if eq_dec a tmp1 then true else if eq_dec a tmp2 then true
  else false).

Definition meta_instr i :=
  match i with
  | Assign a e => is_tmp a
  | Load a p => if meta_loc_dec p then is_tmp a else false
  | Store p _ => if meta_loc_dec p then true else false
  | Lock m | Unlock m => if meta_loc_dec (m, 0) then true else false
  | Assert_le _ _ => true | _ => false
  end.

Lemma meta_instr_ops : forall i (Hmeta : meta_instr i = true) P G t li o c P' G'
  (HP : In (t, i :: li) P) (Hdistinct : distinct P)
  (Hstep : exec P G t o c P' G'),
  Forall (fun c => meta_loc (loc_of c)) (opt_to_list c) /\ env_sim G G'.
Proof.
  intros; exploit in_split; eauto; clarify.
  exploit exec_next; eauto; clarify.
  destruct i; clarify; try apply env_sim_refl.
  - unfold env_sim; intros.
    rewrite upd_old; auto; intro; clarify.
  - unfold env_sim; intros.
    rewrite upd_old; auto; intro; clarify.
  - destruct (le_dec (eval (G t) e1) (eval (G t) e2)); clarify;
      apply env_sim_refl.
Qed.

Global Instance env_sim_trans : RelationClasses.Transitive env_sim.
Proof.
  repeat intro.
  rewrite H; auto.
Qed.

Global Instance env_sim_symm: RelationClasses.Symmetric env_sim.
Proof.
  intros ??? Hsim ???. unfold env_sim in H. symmetry. clarify.
Qed.

(* Alternative approach: a different sim rel, just for failing case, that
   just drops meta ops instead of lining them up. Sim proof is
   -meta->*-real->-meta->*
   But then where do the clocks come in? *)

Transparent move.
Lemma assign_in_handler : forall a e i t
  (Hin : In (Assign a e) (instrument_instr i t)),
  a = tmp1 \/ a = tmp2 \/ i = Assign a e.
Proof.
  destruct i; try destruct x; clarify.
  - repeat rewrite in_app in Hin; destruct Hin as [[? | ?] | ?]; clarify.
    exploit hb_check_instrs; eauto; clarify.
  - repeat rewrite in_app in Hin; destruct Hin as [[? | [? | ?]] | ?]; clarify;
      exploit hb_check_instrs; eauto; clarify.
  - exploit max_vc_instrs; eauto; intros [? | ?]; clarify.
    inversion H; auto.
  - unfold unlock_handler in Hin; repeat rewrite in_app in Hin.
    destruct Hin as [[? | ?] | ?]; clarify.
    exploit set_vc_instrs; eauto; clarify.
    inversion H; auto.
  - unfold spawn_handler in Hin; repeat rewrite in_app in Hin.
    destruct Hin as [[? | ?] | ?]; clarify.
    + exploit max_vc_instrs; eauto; intros [? | Ha]; clarify.
      inversion Ha; auto.
    + inversion H; auto.
  - unfold wait_handler in Hin; repeat rewrite in_app in Hin.
    destruct Hin; clarify.
    + exploit max_vc_instrs; eauto; intros [? | Ha]; clarify.
      inversion Ha; auto.
    + inversion H; auto.
Qed.    

Lemma load_inv : forall i t n a x rest (Hsafe : safe_instr i) (Ht : t < zt)
  (Hn : skipn n (instrument_instr i t) = Load a x :: rest)
  (Hmeta : meta_instr (Load a x) = false),
  i = Load a x /\ n = length (instrument_instr i t) - 2.
Proof.
  destruct i; try destruct x; simpl; intros.
  - destruct n; clarify; rewrite skipn_nil in Hn; clarify.
  - destruct n0; clarify.
    rewrite skipn_app in Hn.
    destruct (skipn n0 (hb_check (W + v) (C + t) zt tmp1 tmp2 ++
      move (C + t, t) (R + v, t) tmp1)) eqn: Hcheck.
    + destruct (n0 - length (hb_check (W + v) (C + t) zt tmp1 tmp2 ++
        move (C + t, t) (R + v, t) tmp1)) eqn: Hn0; clarify.
      rewrite Nat.sub_0_le in Hn0; rewrite skipn_all_iff in Hcheck.
      rewrite app_length; clarify; omega.
      { destruct n1; clarify; rewrite skipn_nil in Hn; clarify. }
    + clarify.
      exploit skipn_in.
      { setoid_rewrite Hcheck; simpl; eauto. }
      rewrite in_app; intros [? | ?].
      * exploit hb_check_instrs; eauto; intros [(? & ? & [? | ?]) | ?]; clarify.
        { inversion H1; clarify.
          contradiction n1; apply W_meta; auto. }
        { inversion H1; clarify.
          destruct (meta_loc_dec (C + t, x0)); clarify.
          contradiction n2; apply C_meta; auto. }
      * clarify.
        inversion H; clarify.
        contradiction n1; apply C_meta; auto.
  - destruct n0; clarify.
    rewrite skipn_app in Hn.
    destruct (skipn n0 (hb_check (W + v) (C + t) zt tmp1 tmp2 ++
      hb_check (R + v) (C + t) zt tmp1 tmp2 ++
      move (C + t, t) (W + v, t) tmp1)) eqn: Hcheck.
    + destruct (n0 - length (hb_check (W + v) (C + t) zt tmp1 tmp2 ++
        hb_check (R + v) (C + t) zt tmp1 tmp2 ++
        move (C + t, t) (W + v, t) tmp1)) eqn: Hn0; clarify.
      destruct n1; clarify; rewrite skipn_nil in Hn; clarify.
    + clarify.
      exploit skipn_in.
      { setoid_rewrite Hcheck; simpl; eauto. }
      repeat rewrite in_app; intros [? | [? | ?]].
      * exploit hb_check_instrs; eauto; intros [(? & ? & [? | ?]) | ?]; clarify.
        { inversion H1; clarify.
          contradiction n1; apply W_meta; auto. }
        { inversion H1; clarify.
          destruct (meta_loc_dec (C + t, x0)); clarify.
          contradiction n2; apply C_meta; auto. }
      * exploit hb_check_instrs; eauto; intros [(? & ? & [? | ?]) | ?]; clarify.
        { inversion H1; clarify.
          contradiction n1; apply R_meta; auto. }
        { inversion H1; clarify.
          destruct (meta_loc_dec (C + t, x0)); clarify.
          contradiction n2; apply C_meta; auto. }
      * clarify.
        inversion H; clarify.
        contradiction n1; apply C_meta; auto.
  - destruct n; clarify.
    exploit skipn_in; [setoid_rewrite Hn; simpl; eauto | intro].
    exploit max_vc_instrs; eauto; intros [(? & ? & [? | ?]) | ?]; clarify.
    + inversion H1; clarify.
      contradiction n0; apply L_meta; auto.
    + inversion H1; clarify.
      destruct (meta_loc_dec (C + t, x)); clarify.
      contradiction n1; apply C_meta; auto.
  - rewrite skipn_app in Hn.
    destruct (skipn n (unlock_handler t m zt tmp1)) eqn: Hcheck.
    + destruct (n - length (unlock_handler t m zt tmp1)); clarify.
      rewrite skipn_nil in Hn; clarify.
    + unfold unlock_handler in Hcheck; clarify.
      exploit skipn_in; [setoid_rewrite Hcheck; simpl; eauto|].
      rewrite in_app; intros [? | ?].
      * exploit set_vc_instrs; eauto; clarify.
        inversion H02; clarify.
        contradiction n0; apply C_meta; auto.
      * simpl in H; destruct H; clarify.
        inversion H; clarify.
        contradiction n1; apply C_meta; auto.
  - rewrite skipn_app in Hn.
    destruct (skipn n (spawn_handler t0 t zt)) eqn: Hcheck.
    + destruct (n - length (spawn_handler t0 t zt)); clarify.
      rewrite skipn_nil in Hn; clarify.
    + unfold spawn_handler in Hcheck; clarify.
      exploit skipn_in; [setoid_rewrite Hcheck; simpl; eauto|].
      rewrite in_app; intros [? | ?].
      * exploit max_vc_instrs; eauto; intros [(? & ? & [? | ?]) | ?]; clarify.
        { inversion H1; clarify.
          contradiction n0; apply C_meta; auto. }
        { inversion H1; clarify.
          destruct (meta_loc_dec (C + t, x)); clarify.
          contradiction n1; apply C_meta; auto. }
      * simpl in H; destruct H; clarify.
        inversion H; clarify.
        contradiction n1; apply C_meta; auto.
  - destruct n; clarify.
    exploit skipn_in; [setoid_rewrite Hn; simpl; eauto|].
    unfold wait_handler; rewrite in_app; intros [? | ?].
    + exploit max_vc_instrs; eauto; intros [(? & ? & [? | ?]) | ?]; clarify.
      { inversion H1; clarify.
        contradiction n0; apply C_meta; auto. }
      { inversion H1; clarify.
        destruct (meta_loc_dec (C + t0, x)); clarify.
        contradiction n1; apply C_meta; auto. }
    + simpl in H; destruct H; clarify.
      inversion H; clarify.
      contradiction n1; apply C_meta; auto.
  - destruct n; clarify; rewrite skipn_nil in Hn; clarify.
Qed.

Lemma store_inv : forall i t n x e rest (Hsafe : safe_instr i) (Ht : t < zt)
  (Hn : skipn n (instrument_instr i t) = Store x e :: rest)
  (Hmeta : meta_instr (Store x e) = false),
  i = Store x e /\ n = length (instrument_instr i t) - 2.
Proof.
  destruct i; try destruct x; simpl; intros.
  - destruct n; clarify; rewrite skipn_nil in Hn; clarify.
  - destruct n0; clarify.
    rewrite skipn_app in Hn.
    destruct (skipn n0 (hb_check (W + v) (C + t) zt tmp1 tmp2 ++
      move (C + t, t) (R + v, t) tmp1)) eqn: Hcheck.
    + destruct (n0 - length (hb_check (W + v) (C + t) zt tmp1 tmp2 ++
        move (C + t, t) (R + v, t) tmp1)) eqn: Hn0; clarify.
      destruct n2; clarify; rewrite skipn_nil in Hn; clarify.
    + clarify.
      exploit skipn_in.
      { setoid_rewrite Hcheck; simpl; eauto. }
      rewrite in_app; intros [? | ?].
      * exploit hb_check_instrs; eauto; intros [(? & ? & [? | ?]) | ?]; clarify.
      * clarify.
        inversion H; clarify.
        contradiction n1; apply R_meta; auto.
  - destruct n0; clarify.
    rewrite skipn_app in Hn.
    destruct (skipn n0 (hb_check (W + v) (C + t) zt tmp1 tmp2 ++
      hb_check (R + v) (C + t) zt tmp1 tmp2 ++
      move (C + t, t) (W + v, t) tmp1)) eqn: Hcheck.
    + destruct (n0 - length (hb_check (W + v) (C + t) zt tmp1 tmp2 ++
        hb_check (R + v) (C + t) zt tmp1 tmp2 ++
        move (C + t, t) (W + v, t) tmp1)) eqn: Hn0; clarify.
      rewrite Nat.sub_0_le in Hn0; rewrite skipn_all_iff in Hcheck.
      rewrite app_length; clarify; omega.
      { destruct n2; clarify; rewrite skipn_nil in Hn; clarify. }
    + clarify.
      exploit skipn_in.
      { setoid_rewrite Hcheck; simpl; eauto. }
      repeat rewrite in_app; intros [? | [? | ?]].
      * exploit hb_check_instrs; eauto; intros [(? & ? & [? | ?]) | ?]; clarify.
      * exploit hb_check_instrs; eauto; intros [(? & ? & [? | ?]) | ?]; clarify.
      * clarify.
        inversion H; clarify.
        contradiction n1; apply W_meta; auto.
  - destruct n; clarify.
    exploit skipn_in; [setoid_rewrite Hn; simpl; eauto | intro].
    exploit max_vc_instrs; eauto; intros [(? & ? & [? | ?]) | ?]; clarify.
    inversion H1; clarify.
    contradiction n1; apply C_meta; auto.
  - rewrite skipn_app in Hn.
    destruct (skipn n (unlock_handler t m zt tmp1)) eqn: Hcheck.
    + destruct (n - length (unlock_handler t m zt tmp1)); clarify.
      rewrite skipn_nil in Hn; clarify.
    + unfold unlock_handler in Hcheck; clarify.
      exploit skipn_in; [setoid_rewrite Hcheck; simpl; eauto|].
      rewrite in_app; intros [? | ?].
      * exploit set_vc_instrs; eauto; clarify.
        inversion H02; clarify.
        contradiction n1; apply L_meta; auto.
      * simpl in H; destruct H; clarify.
        inversion H; clarify.
        contradiction n1; apply C_meta; auto.
  - rewrite skipn_app in Hn.
    destruct (skipn n (spawn_handler t0 t zt)) eqn: Hcheck.
    + destruct (n - length (spawn_handler t0 t zt)); clarify.
      rewrite skipn_nil in Hn; clarify.
    + unfold spawn_handler in Hcheck; clarify.
      exploit skipn_in; [setoid_rewrite Hcheck; simpl; eauto|].
      rewrite in_app; intros [? | ?].
      * exploit max_vc_instrs; eauto; intros [(? & ? & [? | ?]) | ?]; clarify.
        inversion H1; clarify.
        contradiction n1; apply C_meta; auto.
      * simpl in H; destruct H; clarify.
        inversion H; clarify.
        contradiction n1; apply C_meta; auto.
  - destruct n; clarify.
    exploit skipn_in; [setoid_rewrite Hn; simpl; eauto|].
    unfold wait_handler; rewrite in_app; intros [? | ?].
    + exploit max_vc_instrs; eauto; intros [(? & ? & [? | ?]) | ?]; clarify.
      inversion H1; clarify.
      contradiction n1; apply C_meta; auto.
    + simpl in H; destruct H; clarify.
      inversion H; clarify.
      contradiction n1; apply C_meta; auto.
  - destruct n; clarify; rewrite skipn_nil in Hn; clarify.
Qed.

Corollary lock_inv : forall i t n l rest (Hsafe : safe_instr i) (Ht : t < zt)
  (Hn : skipn n (instrument_instr i t) = Lock l :: rest)
  (Hmeta : meta_instr (Lock l) = false),
  i = Lock l /\ n = 0.
Proof.
  intros.
  exploit lock_first; eauto; clarify.
  destruct i; try destruct x; clarify.
  - contradiction n; apply X_meta; auto.
  - contradiction n; apply X_meta; auto.
  - clear - Hn; destruct zt; clarify.
  - clear - Hn; destruct zt; clarify.
Qed.

Lemma state_sim_inv1 : forall P1a P2 P1b t li
  (Hsim : state_sim (P1a ++ (t, li) :: P1b) P2) (Hdistinct : distinct P2),
  exists P2a li' P2b, P2 = (P2a ++ (t, li') :: P2b) /\
  state_sim P1a P2a /\ state_sim P1b P2b /\ li' = instrument li t.
Proof.
  induction P1a; clarify.
  - inversion Hsim as [|(?, ?)]; clarify.
    destruct y.
    exists []; repeat eexists; auto; constructor.
  - inversion Hsim as [|(?, ?) ???? Hrest]; clarify.
    specialize (IHP1a _ _ _ _ Hrest).
    inversion Hdistinct; clarify.
    repeat eexists; eauto; try constructor; eauto; clarify.
Qed.

Lemma hb_check_mem' : forall t C1 C2 z G vs lc G' vs' cond
  (Hmem : to_mem' G t (hb_check C1 C2 z tmp1 tmp2) vs =
    Some (lc, G', vs', cond)) (Hcond : Forall id cond),
  (exists vs1 vs2, length vs1 = z /\ length vs2 = z /\
     lc = mops_hb_check C1 C2 vs1 vs2 z t /\ first_gt vs1 vs2 = None) /\
  forall a, a <> tmp1 -> a <> tmp2 -> G' a = G a.
Proof.
  induction z; clarify.
  - exists [], []; auto.
  - destruct vs; clarify.
    destruct x as (((?, ?), ?), ?); clarify.
    destruct vs; clarify.
    destruct x as (((?, ?), ?), ?); clarify.
    destruct x0 as (((?, ?), ?), ?); clarify.
    inversion Hcond; clarify.
    exploit IHz; eauto.
    intros ((vs1 & vs2 & ?) & HG); clarify.
    split.
    + exists (n :: vs1), (n0 :: vs2); clarify.
      rewrite upd_new, VectorClocks.upd_old, upd_new in *; clarify.
      rewrite <- leb_le in *; unfold id in *; clarify.
    + intros; rewrite HG; auto.
      do 2 (rewrite VectorClocks.upd_old; auto).
Qed.

Transparent mops_move.
Lemma t_steps_load : forall P G t lo lc P1 G1 a x o li
  (Hdistinct : distinct P)
  (Hin : In (t, instrument_instr (Load a (x, o)) t ++ li) P)
  n (Hsteps : t_steps P G t n lo lc (Some P1) G1)
  (Hin' : In (t, Load a (x, o) :: Unlock (X + x) :: li) P1),
  exists vs1 vs2 vt, length vs1 = zt /\ length vs2 = zt /\
    filter (fun c => beq (thread_of c) t) lc =
      Acq t (X + x) :: mops_hb_check (W + x) (C + t) vs1 vs2 zt t ++
      mops_move (C + t, t) (R + x, t) t vt /\ first_gt vs1 vs2 = None.
Proof.
  simpl; intros.
  repeat rewrite <- app_assoc in Hin.
  rewrite <- list_cons_plus_assoc, app_assoc in Hin.
  exploit t_steps_length; eauto; intro.
  exploit t_steps_mem_Some; eauto; intros (vs & vs' & cond & Heq & Hcond).
  clarify.
  destruct x10 as (((?, ?), ?), ?); clarify.
  repeat rewrite <- app_assoc in *.
  rewrite firstn_app in Heq1.
  rewrite app_length in *.
  rewrite firstn_length' in Heq1; [|omega].
  rewrite to_mem'_app in Heq1.
  rewrite match_false in Heq1;
    destruct Heq1 as ((((?, ?), ?), ?) & Hcheck & Heq1).
  rewrite match_false in Heq1;
    destruct Heq1 as ((((?, ?), ?), ?) & Hrest & Heq1); clarify.
  rewrite Forall_app in Hcond; clarify.
  exploit hb_check_mem'; eauto.
  intros ((vs1 & vs2 & ?) & ?); clarify.
  exists vs1, vs2.
  rewrite minus_plus in Hrest; simpl in Hrest.
  destruct l1; clarify.
  exists n0; rewrite upd_new; clarify.
Qed.

(* up *)
Lemma last_skip : forall A (l : list A) d (Hl : l <> []),
  skipn (length l - 1) l = [last l d].
Proof.
  induction l; clarify.
  destruct l; clarify.
  rewrite last_cons; clarify.
  rewrite <- minus_n_O in IHl; erewrite IHl; clarify.
Qed.

(*(* up? *)
Definition prog_op' c := match c with
  ARW t (l, o) _ _ => c = Acq t l \/ c = Rel t l | _ => True end.

Definition mostly_ext P t m1 m2 := forall c (Hprog : prog_op c)
  (Hlock : locks (fst (loc_of c)) P -> snd (loc_of c) = 0 ->
     exists t' l, c = Acq t' l \/ c = Rel t' l /\ t' <> t)
  (Ht : fst (loc_of c) <> C + t),
  consistent (m1 ++ [c]) -> consistent (m2 ++ [c]).

Lemma mostly_ext_step : forall P G lo lc P' G' t o c P'' G'' t0 m1 m2
  (Hroot : exec_star (Some P) G lo lc (Some P') G')
  (Hstep : exec P' G' t o (Some c) P'' G'') (Hext : mostly_ext P t0 m1 m2)
  (Hlock : locks (fst (loc_of c)) P -> snd (loc_of c) = 0 ->
    exists t' l, c = Acq t' l \/ c = Rel t' l /\ t' <> t0)
  (Ht : fst (loc_of c) <> C + t0),
  mostly_ext P t0 (m1 ++ [c]) (m2 ++ [c]).
Proof.
  repeat intro.
  repeat rewrite <- app_assoc; simpl.
  exploit prog_step; eauto; simpl; intro Hprog'; inversion Hprog'; subst.
  generalize (Hext c), (Hext c0); intros Hc Hc0; clarify.
  exploit consistent_app_SC; eauto; clarify.
  rewrite <- app_assoc in H; simpl in H.
  destruct (eq_dec (loc_of c0) (loc_of c)).
  - destruct (writesb c (loc_of c)) eqn: Hwrite.
    + exploit writesb_val; eauto; intros (v & Hv).
      eapply consistent_next_write; eauto.
      rewrite consistent_next_write_iff in H; eauto.
    + exploit no_write_read; eauto; intros (? & ? & v & ?); clarify.
      rewrite read_noop_SC; rewrite read_noop_SC in H; auto.
  - rewrite loc_valid_SC; clarify.
    rewrite loc_valid_SC in H; clarify.
Qed.

Lemma ext_mostly_ext : forall m1 m2 P t, mem_ext m1 m2 -> mostly_ext P t m1 m2.
Proof.
  repeat intro; eapply H; auto.
Qed.

Definition mem_ext_t P t m1 m2 :=
  (forall l (Hl : good_lock (l, 0) P), consistent (m1 ++ [Rel t l]) ->
     consistent (m2 ++ [Rel t l])) /\
  (forall c (Hprog : prog_op c) (Ht : fst (loc_of c) = C + t),
     consistent (m1 ++ [c]) -> consistent (m2 ++ [c])).*)

Lemma unlock_dec : forall i, (exists l, i = Unlock l) \/
  (forall l, i <> Unlock l).
Proof.
  destruct i; eauto; right; clarify.
Qed.

Lemma good_lock_instr : forall x P G lo lc P' G' (Hlock : good_lock (x, 0) P)
  (Hsteps : exec_star (Some P) G lo lc (Some P') G')
  t i li (Hin : In (t, i :: li) P') (Haccess : accesses i = Some (x, 0)),
  i = Lock x \/ i = Unlock x.
Proof.
  intros.
  remember (Some P) as P1; remember (Some P') as P2; generalize dependent P;
    induction Hsteps; clarify.
  - setoid_rewrite Forall_forall in Hlock; specialize (Hlock _ Hin).
    inversion Hlock; destruct i; clarify; unfold instr_forall in *; clarify.
  - destruct P'0; [|inversion Hsteps].
    exploit forall_step; eauto.
Qed.

Lemma iexec_thread : forall t P G lo lc P' G', iexec P G t lo lc P' G' ->
  exists li, In (t, li) P.
Proof.
  intros; inversion H; clarify; eexists; apply split_in.
Qed.

(*(* up? *)
Lemma prog'_step : forall P G t o c P' G', exec P G t o c P' G' ->
  Forall prog_op' (opt_to_list c).
Proof.
  intros; inversion H; clarify; constructor; simpl; auto.
Qed.*)

(*Lemma mostly_complete_t : forall P t m1 m2 c (Hmost : mostly_ext P t m1 m2)
  (Ht : mem_ext_t P t m1 m2) (Hcon : consistent (m1 ++ [c]))
  P1 G1 t1 o P2 G2 (Hexec : exec P1 G1 t1 o (Some c) P2 G2)
  (Ht1 : mem_ext_t P t1 m1 m2)
  G lo lc (Hroot : exec_star (Some P) G lo lc (Some P1) G1)
  (Hlocks : forall l, locks l P -> good_lock (l, 0) P) (Hdistinct : distinct P),
  consistent (m2 ++ [c]).
Proof.
  intros.
  exploit exec_result; eauto; intros (? & i & ? & ? & v & ?).
  destruct (unlock_dec i) as [|Hunlock]; clarify.
  - destruct Ht1 as (Hl & _); apply Hl; auto.
    eapply Hlocks, locks_spec; try apply split_in; eauto; clarify.
  - exploit prog_step; eauto; intro X; inversion X; subst.
    destruct Ht.
    destruct (eq_dec (fst (loc_of c)) (C + t)); auto.
    apply Hmost; auto; intros.
    exploit good_lock_instr; eauto.
    { apply split_in. }
    { rewrite <- exec_accesses; try apply Hexec; clarify.
      { destruct (loc_of c); auto. }
      { eapply distinct_steps; eauto. }
      { apply split_in. } }
    intros [? | ?]; clarify; eauto.
    exploit Hunlock; eauto; contradiction.
Qed.
    
Lemma mostly_complete : forall P t0 t m1 m2 c (Hmost : mostly_ext P t0 m1 m2)
  (Ht : mem_ext_t P t m1 m2) (Hcon : consistent (m1 ++ [c]))
  P1 G1 o P2 G2 (Hexec : exec P1 G1 t o (Some c) P2 G2)
  G lo lc (Hroot : exec_star (Some P) G lo lc (Some P1) G1)
  (Hlocks : forall l, locks l P -> good_lock (l, 0) P) (Hdistinct : distinct P)
  P0 (Hsim : state_sim P0 P) (Ht : Forall (fun e => fst e < zt) P0)
  (Hsafe : safe_locs P0) (Hspawns : safe_spawns P) li (Hin : In (t0, li) P1)
  (Hli : li <> []),
  consistent (m2 ++ [c]).
Proof.
  intros.
  destruct (eq_dec t0 t); [subst; eapply mostly_complete_t; eauto|].
  exploit exec_result; eauto; intros (? & i & ? & ? & v & ?).
  destruct Ht as (Hl & Ht).
  destruct (unlock_dec i) as [|Hunlock]; clarify.
  - apply Hl; auto.
    eapply Hlocks, locks_spec; try apply split_in; eauto; clarify.
  - exploit prog_step; eauto; intro X; inversion X; subst.
    destruct (eq_dec (fst (loc_of c)) (C + t)); auto.
    apply Hmost; auto.
    + intros.
      exploit good_lock_instr; eauto.
      { apply split_in. }
      { rewrite <- exec_accesses; try apply Hexec; clarify.
        { destruct (loc_of c); auto. }
        { eapply distinct_steps; eauto. }
        { apply split_in. } }
      intros [? | ?]; clarify; eauto.
    + exploit bounded_sim; eauto; intro Hbound.
      eapply bounded_steps in Hbound; eauto.
      setoid_rewrite Forall_forall in Hbound.
      exploit Hbound; [eauto | clarify].
      destruct P2; [|inversion Hexec].
      exploit instrument_own_thread; try apply Hsim; auto.
      { eauto. }
      { eapply exec_step'; eauto.
        apply exec_refl. }
      { eauto. }
      { eauto. }
      { destruct (instr_result t i (G1 t) v) as [((((?, ?), ?), ?), ?)|];
          clarify.
        rewrite in_app in *; destruct Hin as [? | [? | ?]]; eauto; clarify.
        rewrite in_app; clarify. }
      { auto. }
      rewrite filter_negb_all.
      intro Hall; inversion Hall; auto.
      { exploit exec_ops; eauto; intro.
        rewrite app_nil_r; eapply Forall_impl; eauto 2; unfold beq; clarify. }
Qed.

Lemma mostly_ext_step' : forall P G lo lc P' G' t o c P'' G'' t0 m1 m2
  (Hroot : exec_star (Some P) G lo lc (Some P') G')
  (Hstep : exec P' G' t o (Some c) P'' G'') (Hext : mostly_ext P t0 m1 m2)
  (Ht : consistent (m2 ++ [c])),
  mostly_ext P t0 (m1 ++ [c]) (m2 ++ [c]).
Proof.
  repeat intro.
  repeat rewrite <- app_assoc; simpl.
  exploit prog_step; eauto; simpl; intro Hprog'; inversion Hprog'; subst.
  generalize (Hext c), (Hext c0); intros Hc Hc0; clarify.
  exploit consistent_app_SC; eauto; clarify.
  rewrite <- app_assoc in H; simpl in H.
  destruct (eq_dec (loc_of c0) (loc_of c)).
  - destruct (writesb c (loc_of c)) eqn: Hwrite.
    + exploit writesb_val; eauto; intros (v & Hv).
      eapply consistent_next_write; eauto.
      rewrite consistent_next_write_iff in H; eauto.
    + exploit no_write_read; eauto; intros (? & ? & v & ?); clarify.
      rewrite read_noop_SC; rewrite read_noop_SC in H; auto.
  - rewrite loc_valid_SC; clarify.
    rewrite loc_valid_SC in H; clarify.
Qed.

Lemma in_cases : forall A (x y : A) l1 l2 l3, In x (l1 ++ y :: l2 ++ l3) ->
  x = y \/ In x l2 \/ In x (l1 ++ l3).
Proof.
  intros; rewrite in_app in *; simpl in *; rewrite in_app in *; clarify.
Qed.

Lemma mem_ext_t_step : forall P t m1 m2 c (Hext : mem_ext_t P t m1 m2)
  (Hcon : consistent (m2 ++ [c])) (Hprog : prog_op c),
  mem_ext_t P t (m1 ++ [c]) (m2 ++ [c]).
Proof.
  intros ????? (Hlock & HC); split; intros.
  - repeat rewrite <- app_assoc in *; simpl in *; eapply consistent_next; eauto.
    constructor; auto.
  - repeat rewrite <- app_assoc in *; simpl in *; eapply consistent_next; eauto.
Qed.

Lemma in_app_cases : forall A (x y : A) l1 l2, In x (l1 ++ y :: l2) ->
  x = y \/ In x (l1 ++ l2).
Proof.
  intros; rewrite in_app in *; clarify.
Qed.

(* !! How much simpler would this be if we just used the memory machine? *)
Definition mem_ext_t_l P t l0 m1 m2 :=
  (forall l (Hnot : l <> l0) (Hl : good_lock (l, 0) P),
     consistent (m1 ++ [Rel t l]) -> consistent (m2 ++ [Rel t l])) /\
  (forall c (Hprog : prog_op c) (Ht : fst (loc_of c) = C + t),
     consistent (m1 ++ [c]) -> consistent (m2 ++ [c])).

Lemma mem_ext_t_l_step : forall P t l m1 m2 c (Hext : mem_ext_t_l P t l m1 m2)
  (Hcon : consistent (m2 ++ [c])) (Hprog : prog_op c),
  mem_ext_t_l P t l (m1 ++ [c]) (m2 ++ [c]).
Proof.
  intros ?????? (Hlock & HC); split; intros.
  - repeat rewrite <- app_assoc in *; simpl in *; eapply consistent_next; eauto.
    constructor; auto.
  - repeat rewrite <- app_assoc in *; simpl in *; eapply consistent_next; eauto.
Qed.*)

(* up! *)
Lemma skipn_cons_nth : forall A n (l : list A) x l',
  skipn n l = x :: l' -> nth_error l n = Some x.
Proof.
  intros.
  rewrite <- (plus_O_n n), <- skipn_nth, H; auto.
Qed.

Lemma max_vc_last : forall src tgt z tmp1 tmp2 (Hz : z <> 0),
  nth_error (max_vc src tgt z tmp1 tmp2)
    (length (max_vc src tgt z tmp1 tmp2) - 1) = Some (Store (tgt, 0) (V tmp2)).
Proof.
  induction z; clarify.
  destruct z; clarify.
Qed.

(* up! *)
Lemma skipn_0 : forall A (l : list A), skipn 0 l = l.
Proof. auto. Qed.

Lemma t_steps_store : forall P G t lo lc P1 G1 x o e li
  (Hdistinct : distinct P)
  (Hin : In (t, instrument_instr (Store (x, o) e) t ++ li) P)
  n (Hsteps : t_steps P G t n lo lc (Some P1) G1)
  (Hin' : In (t, Store (x, o) e :: Unlock (X + x) :: li) P1),
  exists vs1 vs2 vs3 vs2' vt, length vs1 = zt /\ length vs2 = zt /\
    length vs3 = zt /\ length vs2' = zt /\
    filter (fun c => beq (thread_of c) t) lc =
      Acq t (X + x) :: mops_hb_check (W + x) (C + t) vs1 vs2 zt t ++
      mops_hb_check (R + x) (C + t) vs3 vs2' zt t ++
      mops_move (C + t, t) (W + x, t) t vt /\ first_gt vs1 vs2 = None /\
      first_gt vs3 vs2' = None.
Proof.
  simpl; intros.
  repeat rewrite <- app_assoc in Hin.
  rewrite <- list_cons_plus_assoc, app_assoc, app_assoc in Hin.
  exploit t_steps_length; eauto; intro.
  exploit t_steps_mem_Some; eauto; intros (vs & vs' & cond & Heq & Hcond).
  clarify.
  destruct x10 as (((?, ?), ?), ?); clarify.
  repeat rewrite <- app_assoc in *.
  rewrite firstn_app in Heq1.
  rewrite app_length in *.
  rewrite firstn_length' in Heq1; [|omega].
  rewrite to_mem'_app in Heq1.
  rewrite match_false in Heq1;
    destruct Heq1 as ((((?, ?), ?), ?) & Hcheck & Heq1).
  rewrite match_false in Heq1;
    destruct Heq1 as ((((?, ?), ?), ?) & Hrest & Heq1); clarify.
  rewrite Forall_app in Hcond; clarify.
  exploit hb_check_mem'; eauto.
  intros ((vs1 & vs2 & ?) & ?); clarify.
  exists vs1, vs2.
  rewrite minus_plus in Hrest; simpl in Hrest.
  rewrite firstn_app in Hrest.
  rewrite app_length in *.
  rewrite firstn_length' in Hrest; [|omega].
  rewrite to_mem'_app in Hrest.
  rewrite match_false in Hrest;
    destruct Hrest as ((((?, ?), ?), ?) & Hcheck2 & Heq1).
  rewrite match_false in Heq1;
    destruct Heq1 as ((((?, ?), ?), ?) & Hrest & Heq1); clarify.
  rewrite Forall_app in Hcond2; clarify.
  exploit hb_check_mem'; try apply Hcheck2; auto.
  intros ((vs3 & vs2' & ?) & ?); clarify.
  exists vs3, vs2'.
  rewrite minus_plus in Hrest; simpl in Hrest.
  destruct l0; clarify.
  exists n1; rewrite upd_new; clarify.
Qed.

Lemma exec_step_t' : forall P G t o c P' G' rd mops
  (Hstep : exec P G t o c P' G') lo lc P'' G''
  (Hsteps : exec_star_t t P' G' lo lc P'' G''),
  rd = opt_to_list o ++ lo -> mops = opt_to_list c ++ lc ->
  exec_star_t t (Some P) G rd mops P'' G''.
Proof.
  clarify; eapply exec_step_t; eauto.
Qed.

(* up! *)
Lemma last_single : forall A (x d : A), last [x] d = x.
Proof. auto. Qed.

Lemma lock_handler_spec_t : forall n t l P G P1 P2 rest vs1 vs2 v
  (HP : P = P1 ++ (t, lock_handler t l n ++ rest) :: P2)
  (Hlen1 : length vs1 = n) (Hlen2 : length vs2 = n) (Hn : n <> 0),
  exec_star_t t (Some P) G (events_max_vc (L + l) (C + t) t n)
    (mops_max_vc (L + l) (C + t) vs1 vs2 t n) (Some (P1 ++ (t, rest) :: P2))
    (upd_env (upd_env G t tmp1 (last vs1 0)) t tmp2
       (Peano.max (last vs1 v) (last vs2 v))).
Proof.
  induction n; clarify.
  destruct vs1, vs2; clarify.
  eapply exec_step_t'; eauto.
  { apply exec_load; eauto. }
  eapply exec_step_t'; eauto.
  { apply exec_load; eauto. }
  eapply exec_step_t'; eauto.
  { apply exec_assign; eauto. }
  eapply exec_step_t'; eauto.
  { apply exec_store; eauto. }
  instantiate (1 := mops_max_vc (L + l) (C + t) vs1 vs2 t n).
  instantiate (1 := events_max_vc (L + l) (C + t) t n).
  rewrite upd_overwrite.
  destruct (eq_dec n 0).
  - clarify.
    destruct vs1; clarify.
    repeat rewrite last_single.
    rewrite upd_old, upd_same, upd_same; auto.
    apply exec_refl_t.
  - repeat rewrite last_cons; try solve [intro; clarify; omega].
    exploit IHn.
    { eauto. }
    { instantiate (1 := vs1); auto. }
    { instantiate (1 := vs2); auto. }
    { auto. }
    instantiate (5 := upd_env (upd_env G t tmp1 n0) t tmp2
        (eval (upd_env (upd_env G t tmp1 n0) t tmp2 n1 t)
           (Max (V tmp1) (V tmp2)))).
    setoid_rewrite upd_assoc at 2; auto.
    rewrite upd_overwrite.
    setoid_rewrite upd_assoc at 2; auto.
    rewrite upd_overwrite; eauto.
  - auto.
  - simpl.
    rewrite upd_overwrite, upd_same, upd_same.
    rewrite upd_assoc, upd_same; auto.
Qed.  

Lemma can_max : forall t src tgt z (Hz : z <= zt) m (Hcon : consistent m)
  (Hinit1 : forall o, o < z -> initialized m (src, o))
  (Hinit2 : forall o, o < z -> initialized m (tgt, o)),
  exists vs1 vs2, length vs1 = z /\ length vs2 = z /\
    consistent (m ++ mops_max_vc src tgt vs1 vs2 t z).
Proof.
  induction z; clarify.
  - exists [], []; clarify.
    rewrite app_nil_r; auto.
  - use IHz; [|omega].
    generalize (Hinit1 z); clarify.
    exploit init_can_read; eauto; intros (v1 & Hv1).
    generalize (Hinit2 z); clarify.
    exploit init_can_read; eauto; intros (v2 & Hv2).
    specialize (IHz (m ++ [Read t (src, z) v1; Read t (tgt, z) v2;
      Write t (tgt, z) (Peano.max v1 v2)])); use IHz. use IHz. use IHz.
    destruct IHz as (vs1 & vs2 & ? & ? & ?).
    exists (v1 :: vs1), (v2 :: vs2); clarify.
    rewrite <- app_assoc in *; auto.
    + apply init_steps; auto.
      repeat constructor; auto.
    + apply init_steps; auto.
      repeat constructor; auto.
    + rewrite read_noop_SC, read_noop_SC.
      * apply can_write_thread, init_can_write; auto.
      * apply can_read_thread; auto.
      * apply can_read_thread; auto.
Qed.    
    
Lemma finish_handler : forall P0'
  (HX_locks : forall v, v < zv -> good_lock (X + v, 0) P0')
  i l i0 t (Hsafe : safe_instr i0) (Ht : t < zt)
  n (Hskip : skipn n (instrument_instr i0 t) = i :: l)
  (Hmeta : meta_instr i = false) li Pa Pb G o c G'
  (Hstep : exec (Pa ++ (t, i :: l ++ instrument li t) :: Pb) G t o (Some c)
     (Some (Pa ++ (t, l ++ instrument li t) :: Pb)) G') m lc
  (Hinit : forall p, initialized m p)
  G0 lo0 lc0 P1 G1 (Hroot : exec_star (Some P0') G0 lo0 lc0 (Some P1) G1)
  (Hcon : consistent (m ++ lc0 ++ lc ++ [c]))
  P0a P0b (Hsim : state_sim (P0a ++ (t, i0 :: li) :: P0b) P1)
  (Hdistinct : distinct P1)
  lo (Hsteps : exec_star (Some P1) G1 lo lc
             (Some (Pa ++ (t, i :: l ++ instrument li t) :: Pb)) G),
  exists lo2 lc2 G2,
    exec_star_t t (Some (Pa ++ (t, l ++ instrument li t) :: Pb)) G' lo2 lc2
                (Some (Pa ++ (t, instrument li t) :: Pb)) G2 /\
    consistent (m ++ lc0 ++ lc ++ c :: lc2) /\
    Forall (fun c => meta_loc (loc_of c)) lc2 /\ env_sim G' G2.
Proof.
  intros.
  exploit exec_result; eauto; intros (? & ? & ? & ? & v & ? & Hresult).
  exploit distinct_steps; eauto; intro.
  exploit distinct_thread; eauto; clarify.
  destruct (instr_result t i (G t) v) as [((((?, ?), ?), ?), ?)|] eqn: Hi;
    clarify.
  destruct i; try destruct x; simpl in Hi; inversion Hi; clarify.
  - exploit load_inv; eauto; clarify.
    exploit state_sim_inv1; eauto; clarify.
    exploit exec_t_steps; eauto.
    intros (? & ? & lc1' & ? & ? & ? & lc2 & ? & ? & ? & ?); subst.
    assert (l = [Unlock (X + v0)]).
    { destruct (length ((hb_check (W + v0) (C + t) zt tmp1 tmp2 ++
                  move (C + t, t) (R + v0, t) tmp1) ++
                  [Load a (v0, n0); Unlock (X + v0)]) - 1) eqn: Hminus;
        clarify.
      rewrite skipn_app, skipn_all in Hskip.
      destruct (n1 - length ((hb_check (W + v0) (C + t) zt tmp1 tmp2 ++
                       move (C + t, t) (R + v0, t) tmp1))) eqn: Hminus';
        clarify.
      destruct n2; clarify; rewrite skipn_nil in Hskip; clarify.
      { clear - Hminus.
        rewrite app_length in Hminus; simpl in Hminus.
        rewrite <- plus_n_Sm in Hminus; simpl in Hminus.
        rewrite <- plus_n_Sm in Hminus; simpl in Hminus.
        rewrite plus_0_r in Hminus; inversion Hminus; auto. } }
    exploit exec_other_threads; eauto.
    { apply split_in. }
    exploit distinct_steps; try eapply exec_minus_exec; eauto; intro.
    subst; intro Hint; exploit t_steps_load; try apply Hint; eauto.
    { apply split_in. }
    intros (vs1 & vs2 & vt & ? & ? & Heq & Hgt).
    do 4 eexists.
    { eapply exec_step_t; [|apply exec_refl_t].
      generalize (result_exec Pa t (Unlock (X + v0)) (instrument li t)
        Pb (upd_env G t a v) 0 eq_refl); eauto. }
    simpl; apply conjI1; [|intro Hcon'; split].
    + assert (In (Acq t (X + v0)) lc2).
      { eapply filter_In; setoid_rewrite Heq; simpl; auto. }
      exploit in_split; eauto; intros (lc1 & lc2' & ?); subst.
      repeat rewrite <- app_assoc; simpl.
      rewrite split_app; repeat rewrite app_assoc; rewrite read_noop_SC.
      rewrite <- app_assoc; apply delay_rel'.
      * apply can_release_SC.
        repeat rewrite app_assoc in Hcon; apply consistent_app_SC in Hcon.
        rewrite split_app in Hcon; eapply consistent_app_SC; eauto.
      * exploit good_lock_ops.
        { eauto. }
        { eapply exec_star_trans; eauto. }
        simpl; repeat rewrite Forall_app; intro Hl; clarify.
        inversion Hl222; auto.
      * eapply Forall_app, Forall_filter_impl.
        rewrite split_app in Heq; setoid_rewrite Heq.
        clear; constructor; clarify.
        rewrite Forall_app; split.
        { eapply Forall_impl; [|apply mops_hb_check_read].
          destruct a; clarify. }
        { unfold mops_move; repeat constructor; clarify. }
        { unfold beq; repeat intro; clarify. }
      * repeat rewrite app_assoc in Hcon; apply consistent_app_SC in Hcon.
        repeat rewrite <- app_assoc in *; auto.
      * eapply Forall_app, prog_steps, t_steps_exec.
        rewrite split_app in *; eauto.
      * apply init_write; simpl; auto.
        clear; unfold beq; clarify.
      * repeat rewrite <- app_assoc in *; auto.
    + constructor; simpl; auto; apply X_meta; auto.
    + apply env_sim_refl.
  - exploit store_inv; eauto; clarify.
    exploit state_sim_inv1; eauto; clarify.
    exploit exec_t_steps; eauto.
    intros (? & ? & lc1' & ? & ? & ? & lc2 & ? & ? & ? & ?); subst.
    assert (l = [Unlock (X + v0)]).
    { destruct (length ((hb_check (W + v0) (C + t) zt tmp1 tmp2 ++
                  hb_check (R + v0) (C + t) zt tmp1 tmp2 ++
                  move (C + t, t) (W + v0, t) tmp1) ++
                  [Store (v0, n0) e; Unlock (X + v0)]) - 1) eqn: Hminus;
        clarify.
      rewrite skipn_app, skipn_all in Hskip.
      destruct (n - length ((hb_check (W + v0) (C + t) zt tmp1 tmp2 ++
                      hb_check (R + v0) (C + t) zt tmp1 tmp2 ++
                      move (C + t, t) (W + v0, t) tmp1))) eqn: Hminus';
        clarify.
      destruct n2; clarify; rewrite skipn_nil in Hskip; clarify.
      { clear - Hminus.
        rewrite app_length in Hminus; simpl in Hminus.
        rewrite <- plus_n_Sm in Hminus; simpl in Hminus.
        rewrite <- plus_n_Sm in Hminus; simpl in Hminus.
        rewrite plus_0_r in Hminus; inversion Hminus; auto. } }
    exploit exec_other_threads; eauto.
    { apply split_in. }
    exploit distinct_steps; try eapply exec_minus_exec; eauto; intro.
    subst; intro Hint; exploit t_steps_store; try apply Hint; eauto.
    { apply split_in. }
    intros (vs1 & vs2 & vs3 & vs2' & vt & ? & ? & ? & ? & Heq & Hgt1 & Hgt2).
    do 4 eexists.
    { eapply exec_step_t; [|apply exec_refl_t].
      generalize (result_exec Pa t (Unlock (X + v0)) (instrument li t)
        Pb G 0 eq_refl); eauto. }
    simpl; apply conjI1; [|intro Hcon'; split].
    + assert (In (Acq t (X + v0)) lc2).
      { eapply filter_In; setoid_rewrite Heq; simpl; auto. }
      exploit in_split; eauto; intros (lc1 & lc2' & ?); subst.
      repeat rewrite <- app_assoc; simpl.
      rewrite split_app; do 3 rewrite app_assoc.
      rewrite (split_app _ _ (Write _ _ _)); apply delay_rel'.
      * rewrite app_assoc; apply can_release_SC.
        repeat rewrite app_assoc in Hcon; apply consistent_app_SC in Hcon.
        rewrite split_app in Hcon; eapply consistent_app_SC; eauto.
      * exploit good_lock_ops.
        { eauto. }
        { eapply exec_star_trans; [|eapply exec_step_inv]; eauto. }
        simpl; repeat rewrite Forall_app; intro Hl; clarify.
        inversion Hl2122; auto.
      * rewrite Forall_app; split; [|constructor; clarify].
        eapply Forall_app, Forall_filter_impl.
        rewrite split_app in Heq; setoid_rewrite Heq.
        clear; constructor; clarify.
        do 2 rewrite Forall_app; split; [|split].
        { eapply Forall_impl; [|apply mops_hb_check_read].
          destruct a; clarify. }
        { eapply Forall_impl; [|apply mops_hb_check_read].
          destruct a; clarify. }
        { unfold mops_move; repeat constructor; clarify. }
        { unfold beq; repeat intro; clarify. }
      * repeat rewrite <- app_assoc in *; auto.
      * rewrite Forall_app; split; [|constructor; simpl; auto].
        eapply Forall_app, prog_steps, t_steps_exec.
        rewrite split_app in *; eauto.
      * rewrite app_assoc; apply init_write; simpl; auto.
        clear; unfold beq; clarify.
    + constructor; simpl; auto; apply X_meta; auto.
    + apply env_sim_refl.
  - exploit lock_inv; eauto 2; clarify.
    exploit can_max.
    { reflexivity. }
    { apply Hcon. }
    { intros; eapply init_steps, prog_steps, exec_star_trans, exec_step_inv;
        eauto. }
    { intros; eapply init_steps, prog_steps, exec_star_trans, exec_step_inv;
        eauto. }
    clarify; do 3 rewrite <- app_assoc in *.
    do 4 eexists; [|split; [eauto | split]].
    + apply lock_handler_spec_t; eauto.
    + rewrite Forall_forall; intros; eapply mops_max_vc_meta; eauto.
    + instantiate (1 := 0).
      repeat intro; unfold upd_env, upd; clarify.
      destruct (eq_dec tmp2 v); clarify.
  - exploit unlock_last; eauto; clarify.
    do 4 eexists; [apply exec_refl_t|].
    clarify.
    apply env_sim_refl.
Qed.

Opaque skipn.

Lemma rest_meta : forall i n i0 t (Hsafe : safe_instr i0) (Ht : t < zt)
  (Hn : nth_error (instrument_instr i0 t) n = Some i)
  (Hmeta : meta_instr i = false),
  forallb meta_instr (skipn (S n) (instrument_instr i0 t)) = true.
Proof.
  destruct i0; try destruct x; clarify.
  - rewrite skipn_S_tl, skipn_nil; auto.
  - rewrite skipn_S_tl; simpl.
    destruct n; clarify.
    { contradiction n; apply X_meta; auto. }
    exploit nth_error_app'; [eauto|]; intros [? | ?]; clarify.
    { exploit nth_error_in; eauto 2; rewrite in_app; intros [? | ?]; clarify.
      + exploit hb_check_instrs; eauto 2; intros [(? & ? & [? | ?]) | ?];
          clarify.
        * contradiction n1; apply W_meta; auto.
        * contradiction n2; apply C_meta; auto.
      + destruct H; clarify.
        * contradiction n1; apply C_meta; auto.
        * contradiction n1; apply R_meta; auto. }
    rewrite skipn_app, skipn_all; [|omega].
    rewrite <- minus_Sn_m; [|omega].
    rewrite nth_error_two in H2; destruct H2 as [(Hn' & ?) | ]; clarify.
    rewrite Hn', skipn_S_tl, skipn_0; clarify.
    contradiction n2; apply X_meta; auto.
    { contradiction n1; apply X_meta; auto. }
  - rewrite skipn_S_tl; simpl.
    destruct n; clarify.
    { contradiction n; apply X_meta; auto. }
    exploit nth_error_app'; [eauto|]; intros [? | ?]; clarify.
    { exploit nth_error_in; eauto 2; do 2 rewrite in_app; intros [? | [? | ?]];
        clarify.
      + exploit hb_check_instrs; eauto 2; intros [(? & ? & [? | ?]) | ?];
          clarify.
        * contradiction n1; apply W_meta; auto.
        * contradiction n2; apply C_meta; auto.
      + exploit hb_check_instrs; eauto 2; intros [(? & ? & [? | ?]) | ?];
          clarify.
        * contradiction n1; apply R_meta; auto.
        * contradiction n2; apply C_meta; auto.
      + destruct H; clarify.
        * contradiction n1; apply C_meta; auto.
        * contradiction n1; apply W_meta; auto. }
    rewrite skipn_app, skipn_all; [|omega].
    rewrite <- minus_Sn_m; [|omega].
    rewrite nth_error_two in H2; destruct H2 as [(Hn' & ?) | ]; clarify.
    rewrite Hn', skipn_S_tl, skipn_0; clarify.
    contradiction n2; apply X_meta; auto.
    { contradiction n1; apply X_meta; auto. }
  - assert (forall x, In x (lock_handler t m zt) -> meta_instr x = true).
    { intros; exploit max_vc_instrs; eauto; intros [(? & ? & ?) | ?]; clarify.
      destruct H1 as [? | [? | ?]]; clarify.
      + contradiction n0; apply L_meta; auto.
      + contradiction n1; apply C_meta; auto.
      + contradiction n0; apply C_meta; auto. }
    rewrite skipn_S_tl; destruct n; clarify.
    + rewrite forallb_forall; auto.
    + exploit nth_error_in; [eauto | intro].
      exploit H; eauto 2; clarify.
  - exploit nth_error_app'; [eauto|]; intros [? | ?]; clarify.
    { exploit nth_error_in; eauto 2; setoid_rewrite in_app;
        intros [? | ?]; clarify.
      + exploit set_vc_instrs; eauto 2; intros (? & ? & [? | ?]);
          clarify.
        * contradiction n0; apply C_meta; auto.
        * contradiction n0; apply L_meta; auto.
      + destruct H as [? | [? | ?]]; clarify.
        * contradiction n0; apply C_meta; auto.
        * contradiction n0; apply C_meta; auto. }
    rewrite nth_error_single in *; clarify.
    rewrite skipn_app, skipn_all; [|omega].
    rewrite <- minus_Sn_m; [|omega].
    rewrite skipn_S_tl, skipn_nil; auto.
  - exploit nth_error_app'; [eauto|]; intros [? | ?]; clarify.
    { exploit nth_error_in; eauto 2; setoid_rewrite in_app;
        intros [? | ?]; clarify.
      + exploit max_vc_instrs; eauto 2; intros [(? & ? & [? | [? | ?]]) | ?];
          clarify.
        * contradiction n0; apply C_meta; auto.
        * contradiction n1; apply C_meta; auto.
        * contradiction n0; apply C_meta; auto.
      + destruct H as [? | [? | ?]]; clarify.
        * contradiction n0; apply C_meta; auto.
        * contradiction n0; apply C_meta; auto. }
    rewrite nth_error_single in *; clarify.
    rewrite skipn_app, skipn_all; [|omega].
    rewrite <- minus_Sn_m; [|omega].
    rewrite skipn_S_tl, skipn_nil; auto.
  - assert (forall x, In x (wait_handler t0 t zt) -> meta_instr x = true).
    { setoid_rewrite in_app_iff; intros ? [? | ?].
      + exploit max_vc_instrs; eauto; intros [(? & ? & [? | [? | ?]]) | ?];
          clarify.
        * contradiction n0; apply C_meta; auto.
        * contradiction n1; apply C_meta; auto.
        * contradiction n0; apply C_meta; auto.
      + destruct H as [? | [? | ?]]; clarify.
        * contradiction n0; apply C_meta; auto.
        * contradiction n0; apply C_meta; auto. }
    rewrite skipn_S_tl; destruct n; clarify.
    + rewrite forallb_forall; auto.
    + exploit nth_error_in; [eauto | intro].
      exploit H; eauto 2; clarify.
  - rewrite nth_error_single in Hn; clarify.
Qed.


(* Like sim_next_iexec, but finishes any handler that has had an effect on
   the non-metadata state. *)
(*
Lemma sim_next_iexec' : forall P P1 P2 (Hsim : state_sim P P1)
  (Hsafe : safe_locs P) (Hfresh : fresh_tmps P)
  P0 P0' (Hsim : state_sim P0 P0') (Hdistinct : distinct P0')
  (Hsafe : safe_locs P0) (Hfresh : fresh_tmps P0)
  (Ht : Forall (fun e => fst e < zt) P0)
  (Hlocks : forall l, locks l P0' -> good_lock (l, 0) P0')
  (Hlocks2 : forall l, l < zl -> well_locked l P0')
  (HX_locks : forall v, v < zv -> good_lock (X + v, 0) P0')
  (Hvars : forall v, v < zv -> good_var v P0')
  (Hspawns : safe_spawns P0') (Hwaits : safe_waits P0')
  G0 lo0 lc0 G1 (Hroot : exec_star (Some P0') G0 lo0 lc0 (Some P1) G1)
  lo lc G2 (Hsteps : exec_star (Some P1) G1 lo lc (Some P2) G2)
  m (Hcon : consistent (m ++ lc0 ++ lc)) (Hinit : forall p, initialized m p),
  (state_suffix P P2 /\ Forall (fun c => meta_loc (loc_of c)) lc /\
   env_sim G1 G2) \/ exists t lo1 lc1 P' G',
     iexec P1 G1 t lo1 lc1 P' G' /\ exists lo2 lc2 P2' G2',
     exec_star (Some P') G' lo2 lc2 (Some P2') G2' /\
     consistent (m ++ lc0 ++ lc1 ++ lc2) /\
     mem_vals (m ++ lc0 ++ lc) (m ++ lc0 ++ lc1 ++ lc2) /\
     env_sim G2 G2' /\ (forall t', t' <> t -> G2 t' = G2' t') /\
     exists Pa li Pb n i,
       P2 = Pa ++ (t, skipn n (instrument_instr i t) ++ li) :: Pb /\
       P2' = Pa ++ (t, li) :: Pb /\
       forallb meta_instr (skipn n (instrument_instr i t)) = true /\
       exists lo2' lc2', exec_star_t t (Some P2) G2 lo2' lc2' (Some P2') G2' /\
         mem_ext (m ++ lc0 ++ lc ++ lc2') (m ++ lc0 ++ lc1 ++ lc2).
Proof.
  intros; remember (Some P1) as Pa; remember (Some P2) as Pb;
    generalize dependent P2; rewrite exec_rev in Hsteps; induction Hsteps;
    clarify.
  { left; split; [apply sim_suffix; auto | clarify; apply env_sim_refl]. }
  rewrite <- exec_rev in Hsteps.
  use IHHsteps; [|eapply consistent_app_SC; do 2 rewrite <- app_assoc; eauto].
  specialize (IHHsteps _ eq_refl); destruct IHHsteps.
  - clarify.
    exploit exec_result; eauto; intros (? & i & ? & ? & v & ? & Hresult).
    exploit distinct_steps; eauto; intro.
    exploit distinct_steps; eauto; intro.
    subst; exploit state_suffix_inv'; eauto; intros (? & li & ? & n & ? & ? & ? 
      & Hn & ?).
    destruct li; [rewrite skipn_nil in *|]; clarify.
    destruct (length (skipn n (instrument_instr i0 t))) eqn: Hlen.
    { rewrite skipn_length in Hlen; omega. }
    rewrite skipn_app in *.
    assert (nth_error (instrument_instr i0 t) n = Some i).
    { rewrite <- (plus_O_n n), <- skipn_nth.
      destruct (skipn n (instrument_instr i0 t)); clarify. }
    destruct (instr_result t i (G' t) v) as [((((?, ?), ?), ?), ?)|] eqn: Hi;
      clarify.
    destruct n0.
    + right; rewrite not_le_minus_0 in *; [|omega].
      destruct (skipn n (instrument_instr i0 t)) eqn: Hlast; clarify.
      destruct l; clarify.
      exploit first_finished'; try apply Hroot; eauto.
      intro X; exploit X; eauto; try apply split_in.
      { rewrite <- (app_nil_r (instrument_instr _ _)) in Hlast.
        exploit skipn_last; eauto.
        instantiate (1 := Lock 0); clarify; apply split_in. }
      intros (? & ? & ? & ? & ? & ? & ? & ? & Hext).
      do 6 eexists; eauto.
      do 5 eexists; eauto.
      split.
      { destruct Hext as (Hext & ?); specialize (Hext []).
        do 2 rewrite app_nil_r in Hext; rewrite Hext; auto. }
      split; [apply mem_ext_vals; symmetry; auto|].
      split; [apply env_sim_refl | clarify].
      do 4 eexists; exists (Lock 0); split.
      { rewrite skipn_all; simpl; eauto. }
      split; auto.
      split; [rewrite skipn_all; auto|].
      do 3 eexists; [apply exec_refl_t|].
      rewrite app_nil_r; symmetry; auto.
    + destruct (meta_instr i) eqn: Hmeta.
      * left; destruct o0.
        { destruct i; simpl in Hi; inversion Hi; clarify. }
        split.
        { simpl; apply Forall2_app; [|constructor]; clarify.
          rewrite skipn_length in Hlen; exists (S n); split; [omega|].
          rewrite <- Nat.add_1_r, <- skipn_skipn, skipn_app, <- Hn; auto. }
        exploit meta_instr_ops; eauto.
        { apply split_in. }
        rewrite Forall_app; clarify.
        etransitivity; eauto.
      * destruct c; [right | left].
        rewrite le_minus_0 in Hn; [|omega].
        destruct o0; [destruct i; clarify | simpl in *].
        destruct (skipn n (instrument_instr i0 t)) eqn: Hskip; clarify.
        assert (safe_instr i0).
        { setoid_rewrite Forall_app in Hsafe; destruct Hsafe as (_ & Hsafe).
          inversion Hsafe as [|?? Hsafei]; inversion Hsafei; auto. }
        assert (t < zt).
        { exploit bounded_sim; try apply Hsim0; auto; intro Hbound.
          do 2 (eapply bounded_steps in Hbound; eauto).
          setoid_rewrite Forall_app in Hbound; destruct Hbound as (_ & Hbound).
          inversion Hbound; clarify. }
        exploit finish_handler; eauto.
        intros (lo2 & lc2 & G2 & Hfinish & Hcon' & Hmeta' & HG2).
        exploit exec_t_rev_inv; eauto.
        exploit distinct_step; eauto; intro.
        intros [(HP & ?) | Hrest].
        { inversion HP as [Heq].
          exploit distinct_thread; [eauto | symmetry; apply Heq | clarify].
          destruct (skipn n (instrument_instr i0 t)) as [|? [|?]]; clarify.
          exploit cons_app_neq; eauto; contradiction. }
        destruct Hrest as (Pl & Gl & ? & ? & ? & ? & Hrest & Hlast & ? & ?);
          subst.
        assert (Pl = x ++ (t, last (instrument_instr i0 t) (Lock 0) ::
          instrument li t) :: x1).
        { exploit exec_result; eauto; intros (? & il & ? & ? & vl & ? &
            Hresultl); clarify.
          destruct (instr_result t il (Gl t) vl) as [((((?, ?), ?), ?), ?)|]
            eqn: Hil; clarify.
          exploit distinct_steps; [eauto | eapply exec_t_exec; eauto | intro].
          exploit distinct_thread; eauto; clarify.
          destruct o0.
          { destruct il; simpl in Hil; inversion Hil; clarify.
            exploit exec_keep; try eapply exec_t_exec, Hrest; auto.
            { rewrite in_app; simpl; right; right; eauto. }
            clarify; contradiction Hresultl2222.
            rewrite in_map_iff; do 2 eexists; eauto; auto. }
          simpl in *.
          exploit exec_mono; try eapply exec_t_exec, Hrest; try apply split_in;
            auto.
          intros (? & Heq).
          assert (last (instrument_instr i0 t) (Lock 0) = last l (Lock 0))
             as Hlast_eq.
          { rewrite <- (firstn_skipn n (instrument_instr i0 t)), Hskip.
            rewrite last_app; apply last_cons.
            intro; clarify. }
          rewrite Hlast_eq.
          exploit skipn_last; eauto; intros (? & Heq').
          rewrite Heq'; eauto. }
        subst.
        exploit exec_step_t; try apply Hrest; eauto; intro.
        exploit exec_t_exec; eauto; intro.
        exploit exec_star_trans; [apply Hsteps | eauto | intro Hsteps'].
        exploit first_finished'; try apply Hroot; try apply Hsteps'; eauto.
        { apply Forall2_app; auto.
          constructor; auto; clarify.
          clear; generalize (instrument_nonnil i0 t); intro.
          eexists; erewrite skipn_app, last_skip; auto.
          rewrite (le_minus_0(n := _ - _)); [clarify | omega].
          destruct (instrument_instr i0 t); clarify; omega. }
        intro X; exploit X; clear X; try apply split_in; eauto.
        { rewrite <- app_assoc; auto. }
        intros (? & ? & ? & ? & ? & ? & ? & ? & (Hext & Hiext)); do 6 eexists;
          eauto.
        do 5 eexists; eauto.
        split.
        { specialize (Hext []).
          repeat rewrite app_nil_r in Hext; rewrite Hext.
          rewrite <- app_assoc in *; auto. }
        split.
        { repeat intro.
          unfold can_read; rewrite Hext.
          repeat rewrite <- app_assoc.
          setoid_rewrite (app_assoc _ (opt_to_list _)) at 2.
          setoid_rewrite (app_assoc m _) at 2.
          rewrite (app_assoc (m ++ _)), (app_assoc ((m ++ _) ++ _)).
          rewrite loc_valid_ops1_SC.
          repeat rewrite <- app_assoc; split; clarify.
          * eapply Forall_impl; eauto.
            repeat intro; clarify.
          * simpl; auto.
          * eapply prog_steps, exec_t_exec; eauto. }
        split; auto.
        split.
        { intros; symmetry; eapply exec_minus_env, t_minus; eauto. }
        erewrite skipn_n in Hskip; [|eapply skipn_cons_nth; eauto]; clarify.
        do 6 eexists; eauto.
        split; auto.
        split; [eapply rest_meta; eauto|].
        rewrite <- app_assoc in Hext, Hiext; simpl in *.
        do 3 eexists; eauto.
        symmetry; rewrite <- app_assoc; split; auto.
        { rewrite app_nil_r.
          exploit nth_error_in; eauto; intro.
          destruct i; simpl in Hi; inversion Hi; clarify.
          * exploit assign_in_handler; eauto; intros [? | [? | ?]]; clarify.
            rewrite skipn_length in Hlen; simpl in Hlen; destruct n; clarify.
          * exploit spawn_in_handler'; eauto; clarify.
            rewrite app_length in Hlen; simpl in Hlen.
            rewrite Nat.add_sub, skipn_app, skipn_all, minus_diag in Hlen;
              clarify.
          * apply Forall2_app; auto; constructor; clarify.
            exists (S n).
            rewrite <- Nat.add_1_r, <- skipn_skipn, skipn_app, <- Hn; clarify.
            rewrite skipn_length in Hlen; omega. }
    - right; destruct H as (t0 & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?
        & ? & HG & Pa & li1 & Pb & n & i1 & ? & ? & ? & ? & ? & Hfinish &
        (Hext & ?)); clarify.
      do 6 eexists; eauto.
      exploit exec_result; eauto; intros (? & i & li & ? & v & HP & Hresult).
      destruct (instr_result t i (G' t) v) as [((((?, ?), ?), ?), ?)|] eqn: Hi;
        clarify.
      exploit prog_step; eauto; intro Hprog.
      exploit distinct_steps; [eauto | eapply exec_star_trans; eauto | intro].
      destruct (eq_dec t0 t).
      + subst; exploit distinct_thread; eauto; intros (? & ? & Hinstr); clarify.
        destruct (skipn n (instrument_instr i1 t)) eqn: Hskip; clarify.
        * exploit exec_t_maintain; eauto; try apply split_in; clarify.
          do 5 eexists.
          { eapply exec_step_inv; eauto. }
          apply conjI1.
          { repeat rewrite app_assoc in *; rewrite <- Hext, app_nil_r; auto. }
          split.
          { destruct c; [|repeat rewrite app_nil_r; auto].
            repeat rewrite app_assoc in *; apply mem_vals_step; auto.
            inversion Hprog; auto. }
          split; [apply env_sim_refl|].
          split; auto.
          do 4 eexists; exists (Lock 0); split.
          { rewrite skipn_all; simpl; eauto. }
          split; auto.
          split; [rewrite skipn_all; auto|].
          do 3 eexists; [apply exec_refl_t|].
          rewrite app_nil_r in *; repeat rewrite app_assoc in *;
            apply mem_ext_app; split; auto.
        * rewrite andb_true_iff in *; clarify.
          do 5 eexists; eauto; split; auto.
          exploit meta_instr_ops; try apply Hexec'; eauto.
          { apply split_in. }
          intros (? & ?); split.
          { repeat rewrite app_assoc in *; apply mem_vals_app_meta; auto.
            intros; repeat rewrite <- app_assoc; eapply init_steps, prog_steps, 
              exec_star_trans; eauto. }
          split.
          { etransitivity; eauto.
            symmetry; auto. }
          split.
          { destruct o3 as [(?, ?)|]; eauto.
            intros; unfold upd_env; rewrite VectorClocks.upd_old; auto. }
          erewrite skipn_n in Hskip; [|eapply skipn_cons_nth; eauto]; clarify.
          do 6 eexists; eauto.
          destruct o0; [destruct i0; simpl in Hi; inversion Hi; clarify|].
          split; auto.
          inversion Hfinish; clarify.
          { exploit distinct_thread; eauto; intros (? & ? & ?).
            exploit cons_app_neq; eauto; contradiction. }
          exploit exec_det.
          { eauto. }
          { eauto. }
          { apply Hexec'. }
          { specialize (Hext []); repeat rewrite app_nil_r in Hext.
            destruct Hext as (_ & Hcon'); use Hcon'.
            repeat rewrite app_assoc in Hcon'; eapply consistent_app_SC; eauto.
          }
          { repeat rewrite <- app_assoc; auto. }
          { destruct c0; auto.
            rewrite <- app_assoc; eapply init_steps, prog_steps,
              exec_star_trans; eauto. }
          clarify.
          do 3 eexists; eauto.
          rewrite <- app_assoc; split; auto.
      + assert (In (t, i :: li) (Pa ++ (t0, li1) :: Pb)).
        { assert (In (t, i :: li)
            (Pa ++ (t0, skipn n (instrument_instr i1 t0) ++ li1) :: Pb))
            as Hin by (rewrite HP; apply split_in).
          rewrite in_app in Hin; rewrite in_app; clarify. }
        exploit in_split; eauto; intros (Pa' & Pb' & HP').
        assert (P2 (Pa ++ (t0, li1) :: Pb)).
        { destruct i; simpl in Hi; inversion Hi; auto; clarify.
          * intro Hin; contradiction Hresult2222.
            rewrite map_app in *; auto.
          * rewrite in_app_iff in Hresult2222; rewrite in_app; clarify.
            exploit app_eq_nil; eauto; intros (Hnil & ?); subst.
            rewrite Hnil; auto. }
        do 5 eexists.
        { eapply exec_step_inv; eauto.
          exploit result_exec; eauto.
          rewrite <- HG; auto.
          setoid_rewrite Hi; intro Hstep; apply Hstep; auto. }
        apply conjI1.
        { repeat rewrite app_assoc in *; rewrite <- Hext.
          (* We need a noninterference here. *) admit. }
        intro; split.
        { destruct c; [|repeat rewrite app_nil_r; auto].
          repeat rewrite app_assoc in *; apply mem_vals_step; auto.
          inversion Hprog; auto. }
        split.
        { destruct o3 as [(?, ?)|]; auto.
          repeat intro; unfold upd_env, upd; clarify. }
        split.
        { intros; destruct o3 as [(?, ?)|]; auto.
          unfold upd_env, upd.
          destruct (eq_dec t t'); clarify.
          apply functional_extensionality; clarify.
          rewrite HG; auto. }
        exploit exec_other_thread; try apply Hexec'.
        { apply split_in. }
        { auto. }
        intro; exploit in_split; eauto; intros (? & ? & HP2').
        do 6 eexists; eauto.
        split.
        { destruct (le_dec (length Pa) (length Pa')).
          * exploit app_eq_inv_ge; try apply l; eauto.
            intros (l' & ?); clarify.
            rewrite <- app_assoc in HP'; exploit app_inv_head; eauto.
            destruct l'; clarify.
            rewrite split_app, app_assoc in HP.
            exploit distinct_thread; try apply HP.
            { repeat rewrite <- app_assoc; auto. }
            intros (? & ? & _); subst.
            repeat rewrite <- app_assoc in *.
            exploit distinct_thread; try apply HP2'.
            { eapply distinct_step; eauto. }
            intros (? & ? & ?); subst; auto.
          * symmetry in HP'; exploit app_eq_inv_ge; try apply HP'.
            { omega. }
            intros (l' & ?); clarify.
            destruct l'; clarify.
            rewrite <- app_assoc in *; exploit distinct_thread; try apply HP;
              auto.
            intros (? & ? & _); subst.
            rewrite (split_app _ _ (t, li)) in HP2', Hexec'.
            repeat rewrite app_assoc in *.
            exploit distinct_thread; try apply HP2'.
            { eapply distinct_step; eauto. }
            intros (? & ? & ?); subst.
            repeat rewrite <- app_assoc; auto. }
        split; auto.
        admit. (* Here we need to be able to transfer exec_star_t, and then
          we need noninterference. *)
Qed.

(* Like sim_next_iexec, but finishes any handler that has had an effect on
   the non-metadata state. *)
Lemma sim_next_iexec' : forall P P1 P2 (Hsim : state_sim P P1)
  (Hsafe : safe_locs P) (Hfresh : fresh_tmps P)
  P0 P0' (Hsim : state_sim P0 P0') (Hdistinct : distinct P0')
  (Hsafe : safe_locs P0) (Hfresh : fresh_tmps P0)
  (Ht : Forall (fun e => fst e < zt) P0)
  (Hlocks : forall l, locks l P0' -> good_lock (l, 0) P0')
  (Hlocks2 : forall l, l < zl -> well_locked l P0')
  (HX_locks : forall v, v < zv -> good_lock (X + v, 0) P0')
  (Hvars : forall v, v < zv -> good_var v P0')
  (Hspawns : safe_spawns P0') (Hwaits : safe_waits P0')
  G0 lo0 lc0 G1 (Hroot : exec_star (Some P0') G0 lo0 lc0 (Some P1) G1)
  lo lc G2 (Hsteps : exec_star (Some P1) G1 lo lc (Some P2) G2)
  m (Hcon : consistent (m ++ lc0 ++ lc)) (Hinit : forall p, initialized m p),
  (state_suffix P P2 /\ Forall (fun c => meta_loc (loc_of c)) lc /\
   env_sim G1 G2) \/ exists t lo1 lc1 P' G' lo2 lc2 P2' G2',
     iexec P1 G1 t lo1 lc1 P' G' /\
     exec_star (Some P') G' lo2 lc2 (Some P2') G2' /\
     consistent (m ++ lc0 ++ lc1 ++ lc2) /\
     mem_vals (m ++ lc0 ++ lc) (m ++ lc0 ++ lc1 ++ lc2) /\ 
     mostly_ext P0' t (m ++ lc0 ++ lc) (m ++ lc0 ++ lc1 ++ lc2) /\
     env_sim G2 G2' /\
     (forall t' li (Hin : In (t', li) P2), In (t', li) P2' /\ G2' t' = G2 t' /\
       ((li <> [] \/ t' = t) ->
        mem_ext_t P0' t' (m ++ lc0 ++ lc) (m ++ lc0 ++ lc1 ++ lc2))
  \/ t' = t /\ match li with [] => False | i :: li => In (t', li) P2' /\
       exists v, v < zv /\ i = Unlock (X + v) /\ G2' t' = G2 t' /\
         mem_ext_t_l P0' t' (X + v) (m ++ lc0 ++ lc) (m ++ lc0 ++ lc1 ++ lc2) /\
         consistent (m ++ lc0 ++ lc1 ++ lc2 ++ [Acq t (X + v)]) end
  \/ t' = t /\ exists n l, n < length (lock_handler t' l zt) /\ l < zl /\
     (forall l, good_lock (l, 0) P0' ->
        consistent (m ++ lc0 ++ lc ++ [Rel t l]) ->
        consistent (m ++ lc0 ++ lc1 ++ lc2 ++ [Rel t l])) /\
     exists li', li = skipn n (lock_handler t' l zt) ++ li' /\ In (t', li') P2'
     /\ forall lo' lc' P' G', exec_star_t t (Some P2) G2 lo' lc' (Some P') G' ->
          In (t', li') P' -> G' t = G2' t /\ forall o (Ho : o < zt) v,
          can_read (m ++ lc0 ++ lc ++ lc') (C + t, o) v <->
          can_read (m ++ lc0 ++ lc1 ++ lc2) (C + t, o) v)
 /\ forall t' li' (Hin : In (t', li') P2'), exists li, In (t', li) P2.
Proof.
  intros; remember (Some P1) as Pa; remember (Some P2) as Pb;
    generalize dependent P2; rewrite exec_rev in Hsteps; induction Hsteps;
    clarify.
  { left; split; [apply sim_suffix; auto | clarify; apply env_sim_refl]. }
  rewrite <- exec_rev in Hsteps.
  use IHHsteps; [|eapply consistent_app_SC; do 2 rewrite <- app_assoc; eauto].
  specialize (IHHsteps _ eq_refl); destruct IHHsteps.
  - clarify.
    exploit exec_result; eauto; intros (? & i & ? & ? & v & ? & Hresult).
    exploit distinct_steps; eauto; intro.
    exploit distinct_steps; eauto; intro.
    subst; exploit state_suffix_inv'; eauto; intros (? & li & ? & n & ? & ? & ? 
      & Hn & ?).
    destruct li; [rewrite skipn_nil in *|]; clarify.
    destruct (length (skipn n (instrument_instr i0 t))) eqn: Hlen.
    { rewrite skipn_length in Hlen; omega. }
    rewrite skipn_app in *.
    assert (nth_error (instrument_instr i0 t) n = Some i).
    { rewrite <- (plus_O_n n), <- skipn_nth.
      destruct (skipn n (instrument_instr i0 t)); clarify. }
    destruct (instr_result t i (G' t) v) as [((((?, ?), ?), ?), ?)|] eqn: Hi;
      clarify.
    destruct n0.
    + right; rewrite not_le_minus_0 in *; [|omega].
      destruct (skipn n (instrument_instr i0 t)) eqn: Hlast; clarify.
      destruct l; clarify.
      exploit first_finished'; try apply Hroot; eauto.
      intro X; exploit X; eauto; try apply split_in.
      { rewrite <- (app_nil_r (instrument_instr _ _)) in Hlast.
        exploit skipn_last; eauto.
        instantiate (1 := Lock 0); clarify; apply split_in. }
      intros (? & ? & ? & ? & ? & ? & ? & ? & Hext).
      do 10 eexists; eauto; split; eauto.
      split.
      { destruct Hext as (Hext & ?); specialize (Hext []).
        do 2 rewrite app_nil_r in Hext; rewrite Hext; auto. }
      split; [apply mem_ext_vals; symmetry; auto|].
      split; [apply ext_mostly_ext; symmetry; auto|].
      split; [apply env_sim_refl | clarify].
      split; eauto; left; clarify.
      destruct Hext as (Hext & ?); split; intros;
        repeat rewrite app_assoc in *; rewrite Hext; auto.
    + destruct (meta_instr i) eqn: Hmeta.
      * left; destruct o0.
        { destruct i; simpl in Hi; inversion Hi; clarify. }
        split.
        { simpl; apply Forall2_app; [|constructor]; clarify.
          rewrite skipn_length in Hlen; exists (S n); split; [omega|].
          rewrite <- Nat.add_1_r, <- skipn_skipn, skipn_app, <- Hn; auto. }
        exploit meta_instr_ops; eauto.
        { apply split_in. }
        rewrite Forall_app; clarify.
        etransitivity; eauto.
      * destruct c; [right | left].
        destruct o0; [destruct i; clarify | simpl in *].
        assert (exists lo2 lc2 G2,
           exec_star_t t (Some (x ++ (t, x0) :: x1))
           match o3 with Some (a, v0) => upd_env G' t a v0 | None => G' end
           lo2 lc2 (Some (x ++ (t, instrument li t) :: x1)) G2 /\
           consistent (m ++ lc0 ++ lc ++ c :: lc2) /\
           Forall (fun c => meta_loc (loc_of c)) lc2 /\
           mostly_ext P0' t (m ++ lc0 ++ lc ++ [c])
             (m ++ lc0 ++ lc ++ c :: lc2) /\
           env_sim match o3 with Some (a, v0) => upd_env G' t a v0
             | None => G' end G2 /\
           ((exists v, v < zv /\ x0 = Unlock (X + v) :: instrument li t /\
               G2 t = match o3 with Some (a, v0) => upd_env G' t a v0
               | None => G' end t /\
               mem_ext_t_l P0' t (X + v) (m ++ lc0 ++ lc ++ [c])
                                         (m ++ lc0 ++ lc ++ c :: lc2) /\
               consistent (m ++ lc0 ++ lc ++ c :: lc2 ++ [Acq t (X + v)])) \/
            (forall l, good_lock (l, 0) P0' ->
               consistent (m ++ lc0 ++ lc ++ [c] ++ [Rel t l]) ->
               consistent (m ++ lc0 ++ lc ++ c :: lc2 ++ [Rel t l])) /\
            exists l, l < zl /\ x0 = lock_handler t l zt ++ instrument li t /\
              forall lo' lc' P' G1, exec_star_t t (Some (x ++ (t, x0) :: x1))
              match o3 with Some (a, v0) => upd_env G' t a v0 | None => G' end
              lo' lc' (Some P') G1 -> In (t, instrument li t) P' ->
              G1 t = G2 t /\ forall o (Ho : o < zt) v,
              can_read (m ++ lc0 ++ lc ++ [c] ++ lc') (C + t, o) v <->
              can_read (m ++ lc0 ++ lc ++ c :: lc2) (C + t, o) v))
           as (lo2 & lc2 & G2 & Hfinish & Hcon' & Hmeta' & ? & HG2 & HP2).
        { setoid_rewrite Forall_app in Hsafe; clarify.
          inversion Hsafe2 as [|?? Hsafei]; inversion Hsafei; subst.
          exploit bounded_sim; try apply Ht; eauto; intro Hbound.
          eapply bounded_steps in Hbound; eauto.
          eapply bounded_steps in Hbound; eauto.
          setoid_rewrite Forall_app in Hbound; clarify.
          inversion Hbound2; subst.
          destruct (skipn n (instrument_instr i0 t)) eqn: Hskip;
            [rewrite skipn_all_iff in Hskip; omega | clarify].
          assert (n <= length (instrument_instr i0 t)) as Hle
            by (apply lt_le_weak; auto).
          rewrite (le_minus_0 Hle) in *.
          destruct i1; try destruct x0; simpl in Hi; inversion Hi; clarify.
          { exploit load_inv; eauto; clarify.
            exploit state_sim_inv1; eauto; clarify.
            exploit exec_t_steps; eauto.
            intros (? & ? & lc1' & ? & ? & ? & lc2 & ? & ? & ? & ?); subst.
            assert (l = [Unlock (X + v0)]).
            { destruct (length ((hb_check (W + v0) (C + t) zt tmp1 tmp2 ++
                move (C + t, t) (R + v0, t) tmp1) ++
                [Load a (v0, n1); Unlock (X + v0)]) - 1) eqn: Hminus;
                setoid_rewrite Hminus in Hskip; clarify.
              rewrite skipn_app, skipn_all in Hskip.
              destruct (n2 - length ((hb_check (W + v0) (C + t) zt tmp1 tmp2 ++
                move (C + t, t) (R + v0, t) tmp1))) eqn: Hminus';
                setoid_rewrite Hminus' in Hskip; clarify.
              destruct n3; clarify; rewrite skipn_nil in Hskip; clarify.
              { clear - Hminus.
                rewrite app_length in Hminus; simpl in Hminus.
                rewrite <- plus_n_Sm in Hminus; simpl in Hminus.
                rewrite <- plus_n_Sm in Hminus; simpl in Hminus.
                rewrite plus_0_r in Hminus; inversion Hminus; auto. } }
            exploit exec_other_threads; eauto.
            { apply split_in. }
            exploit distinct_steps; try eapply exec_minus_exec; eauto; intro.
            subst; intro Hint; exploit t_steps_load; try apply Hint; eauto.
            { apply split_in. }
            intros (vs1 & vs2 & vt & ? & ? & Heq & Hgt).
            do 4 eexists.
            { eapply exec_step_t; [|apply exec_refl_t].
              generalize (result_exec x t (Unlock (X + v0)) (instrument li t)
                x1 (upd_env G' t a v) 0 eq_refl); eauto. }
            simpl; apply conjI1; [|intro Hcon'; split; [|split; [|split]]].
            * assert (In (Acq t (X + v0)) lc2).
              { eapply filter_In; setoid_rewrite Heq; simpl; auto. }
              exploit in_split; eauto; intros (lc1 & lc2' & ?); subst.
              repeat rewrite <- app_assoc; simpl.
              rewrite (split_app _ _ (Read _ _ _)); rewrite split_app;
                repeat rewrite app_assoc; apply can_arw_SC.
              { exploit lock_hold2.
                { do 3 (rewrite <- app_assoc in * ); simpl in *; eauto. }
                { rewrite Forall_app; split; [|constructor; simpl; auto].
                  exploit prog_steps; [eapply t_steps_exec; eauto|].
                  rewrite Forall_app; intros (_ & Hprog); inversion Hprog; auto.
                }
                { rewrite Forall_app; split.
                  { exploit good_lock_ops; [|eapply t_steps_exec; eauto|].
                    { eapply forall_steps; [|eapply exec_minus_exec; eauto].
                      eapply forall_steps; eauto.
                      apply HX_locks; eauto. }
                    rewrite Forall_app; intros (_ & Hlock); inversion Hlock;
                      auto. }
                  { constructor; auto; simpl.
                    intro Heq'; contradiction n.
                    inversion Heq'; apply X_meta; auto. } }
                { repeat rewrite <- app_assoc; intros [? | Hrel]; auto.
                  rewrite in_app in Hrel; clarify.
                  exploit rel_inv'; try (eapply t_steps_exec; eauto); auto.
                  { do 2 rewrite <- list_cons_plus_assoc in Hint.
                    rewrite <- app_assoc in Hint; eauto. }
                  { apply split_in. }
                  { rewrite in_app; right; simpl; eauto. }
                  intro Hin; clear - Hin; clarify.
                  rewrite in_app in Hin; destruct Hin.
                  { exploit hb_check_instrs; eauto; clarify. }
                  { Transparent move. clarify. Opaque move. } } }
              { do 2 rewrite <- app_assoc.
                apply can_write_SC.
                * rewrite (split_app _ _ (Acq _ _)) in Hcon.
                  repeat rewrite app_assoc in Hcon.
                  exploit consistent_app_SC; eauto; intro.
                  exploit consistent_app_SC; eauto; intro Hcon'.
                  rewrite can_arw_SC_iff' in Hcon'; clarify.
                * repeat rewrite <- app_assoc in *; auto.
                * rewrite app_assoc, Forall_app; split;
                    [|constructor; simpl; auto].
                  exploit prog_steps; [eapply t_steps_exec; eauto|].
                  rewrite Forall_app; intros (_ & Hprog); inversion Hprog; auto.
              }
            * constructor; simpl; auto; apply X_meta; auto.
            * intros ???? Hcon''.
              destruct (eq_dec (loc_of c) (X + v0, 0)).
              { use Hlock; [clear - Hlock e Hcon' Hcon'' Hinit Hroot Hsteps
                  Hexec'|]; clarify.
                rewrite e in Hlock; clarify.
                destruct Hlock; clarify.
                repeat rewrite <- app_assoc; simpl.
                rewrite split_app in *; repeat rewrite app_assoc in *;
                  apply can_acquire_SC; auto.
                * rewrite split_app in Hcon'; repeat rewrite app_assoc in *.
                  rewrite can_arw_SC_iff' in Hcon', Hcon''; clarify.
                  exploit can_read_unique; [| apply Hcon'1 | apply Hcon''1|].
                  { repeat rewrite <- app_assoc; apply init_steps; eauto.
                    eapply prog_steps, exec_star_trans; eauto.
                    rewrite app_assoc; eapply exec_star_trans; eauto.
                    eapply exec_step'; try apply exec_refl; eauto. }
                  intro Heq; inversion Heq; clarify.
                * eapply locks_spec; eauto.
                  { apply split_in. }
                  { rewrite e; simpl; auto. } }
              { repeat rewrite <- app_assoc; simpl.
                rewrite (split_app _ _ (Read _ _ _)).
                repeat rewrite app_assoc in *; rewrite loc_valid_SC; clarify.
                repeat rewrite <- app_assoc in *; auto. }
            * apply env_sim_refl.
            * left; do 2 eexists; eauto; clarify.
              split.
              { split; intros.
                { repeat rewrite <- app_assoc in *; simpl in *.
                  rewrite split_app in *; repeat rewrite app_assoc in *;
                    rewrite loc_valid_SC; clarify.
                  intro; clarify. }
                { repeat rewrite <- app_assoc in *; simpl in *.
                  rewrite split_app in *; repeat rewrite app_assoc in *;
                    rewrite loc_valid_SC; clarify.
                  intro; destruct (loc_of c); clarify.
                  exploit Hmetalocs_disjoint_CX; eauto. } }
              { rewrite split_app in *; repeat rewrite app_assoc in *;
                  apply can_acquire_SC; auto. } }
        { admit. }
        { admit. }
        { destruct (skipn n (instrument_instr i0 t)) eqn: Hskip'; clarify.
          exploit unlock_last; eauto; clarify. } }
        exploit exec_t_rev_inv; eauto.
        exploit distinct_step; eauto; intro.
        rewrite le_minus_0 in Hn; [|omega].
        intros [(HP & ?) | Hrest].
        { inversion HP as [Heq].
          exploit distinct_thread; [eauto | symmetry; apply Heq | clarify].
          destruct (skipn n (instrument_instr i0 t)) as [|? [|?]]; clarify.
          exploit cons_app_neq; eauto; contradiction. }
        destruct Hrest as (Pl & Gl & ? & ? & ? & ? & Hrest & Hlast & ? & ?);
          subst.
        assert (Pl = x ++ (t, last (instrument_instr i0 t) (Lock 0) ::
          instrument li t) :: x1).
        { exploit exec_result; eauto; intros (? & il & ? & ? & vl & ? &
            Hresultl); clarify.
          destruct (instr_result t il (Gl t) vl) as [((((?, ?), ?), ?), ?)|]
            eqn: Hil; clarify.
          exploit distinct_steps; [eauto | eapply exec_t_exec; eauto | intro].
          exploit distinct_thread; eauto; clarify.
          destruct o0.
          { destruct il; simpl in Hil; inversion Hil; clarify.
            exploit exec_keep; try eapply exec_t_exec, Hrest; auto.
            { rewrite in_app; simpl; right; right; eauto. }
            clarify; contradiction Hresultl2222.
            rewrite in_map_iff; do 2 eexists; eauto; auto. }
          simpl in *.
          exploit exec_mono; try eapply exec_t_exec, Hrest; try apply split_in;
            auto.
          intros (? & Heq).
          destruct (skipn n (instrument_instr i0 t)) eqn: Hskip; clarify.
          assert (last (instrument_instr i0 t) (Lock 0) = last l (Lock 0))
             as Hlast_eq.
          { rewrite <- (firstn_skipn n (instrument_instr i0 t)), Hskip.
            rewrite last_app; apply last_cons.
            intro; clarify. }
          rewrite Hlast_eq.
          exploit skipn_last; eauto; intros (? & Heq').
          rewrite Heq'; eauto. }
        subst.
        exploit exec_step_t; try apply Hrest; eauto; intro.
        exploit exec_t_exec; eauto; intro.
        exploit exec_star_trans; [apply Hsteps | eauto | intro Hsteps'].
        exploit first_finished'; try apply Hroot; try apply Hsteps'; eauto.
        { apply Forall2_app; auto.
          constructor; auto; clarify.
          clear; generalize (instrument_nonnil i0 t); intro.
          eexists; erewrite skipn_app, last_skip; auto.
          rewrite (le_minus_0(n := _ - _)); [clarify | omega].
          destruct (instrument_instr i0 t); clarify; omega. }
        intro X; exploit X; clear X; try apply split_in; eauto.
        { rewrite <- app_assoc; auto. }
        intros (? & ? & ? & ? & ? & ? & ? & ? & (Hext & ?)); do 10 eexists;
          eauto.
        split; eauto.
        split.
        { specialize (Hext []).
          repeat rewrite app_nil_r in Hext; rewrite Hext.
          rewrite <- app_assoc in *; auto. }
        split.
        { repeat intro.
          unfold can_read; rewrite Hext.
          repeat rewrite <- app_assoc.
          setoid_rewrite (app_assoc _ (opt_to_list _)) at 2.
          setoid_rewrite (app_assoc m _) at 2.
          rewrite (app_assoc (m ++ _)), (app_assoc ((m ++ _) ++ _)).
          rewrite loc_valid_ops1_SC.
          repeat rewrite <- app_assoc; split; clarify.
          * eapply Forall_impl; eauto.
            repeat intro; clarify.
          * simpl; auto.
          * eapply prog_steps, exec_t_exec; eauto. }
        split.
        { admit. }
        split; auto.
        split.
        { intros.
          destruct (eq_dec t' t).
          * subst; exploit distinct_in; [eauto | apply Hin | apply split_in|].
            intro; subst.
            right; destruct HP2 as [Hcase | Hcase]; [left | right].
            { destruct Hcase as (? & ? & ? & ? & (Hl & Hc) & ?); clarify.
              split; [apply split_in|].
              do 2 eexists; eauto; clarify.
              split.
              { repeat intro; split; intros; repeat rewrite app_assoc in *;
                  rewrite Hext.
                { rewrite (split_app (_ ++ _) (_ ++ _) c), app_assoc in Hl.
                  rewrite (split_app _ _ c); apply Hl; auto. }
                { rewrite (split_app (_ ++ _) (_ ++ _) c), app_assoc in Hc.
                  rewrite (split_app _ _ c); apply Hc; auto. } }
              { repeat rewrite app_assoc in *; rewrite Hext.
                repeat rewrite <- app_assoc in *; auto. } }
            { destruct Hcase as (Hmem & ? & ? & ? & Hlock); clarify.
              exists 0; eexists; split.
              { clear; generalize zt_non_zero; destruct zt; clarify. }
              split; eauto.
              split.
              { intros; specialize (Hmem l).
                repeat rewrite app_assoc in *; rewrite Hext.
                repeat rewrite <- app_assoc in *; auto. }
              do 2 eexists; eauto.
              split; [apply split_in|].
              intros; exploit Hlock; eauto; intros (? & Hmem').
              split; auto; intros.
              unfold can_read in *; rewrite Hext.
              repeat rewrite <- (app_assoc lc); auto. }
          * assert (t' < zt) as Ht0.
            { exploit bounded_sim; try apply Hsim0; auto; intro Hbound.
              eapply bounded_steps in Hbound; eauto.
              eapply bounded_steps in Hbound; try apply Hsteps; eauto.
              eapply bounded_step in Hbound; eauto.
              setoid_rewrite Forall_forall in Hbound; specialize (Hbound _ Hin);
                clear - Hbound; clarify. }
            left; clear - Hin n1 Hfinish Hext Hcon' Hinit Hroot Hsteps Hexec'
              Hsim0 Hsafe0 Hdistinct Hspawns Ht0.
            exploit exec_t_env; eauto; rewrite in_app in *; split; clarify.
            split; intros.
            { specialize (Hext [Rel t' l]).
              repeat rewrite <- app_assoc in *; simpl in *; rewrite Hext.
              rewrite split_app; do 2 rewrite app_assoc.
              rewrite (app_assoc _ _ [Rel t' l]); apply delay_rel.
              { repeat rewrite <- app_assoc; auto. }
              { exploit good_lock_ops.
                { eauto. }
                { eapply exec_star_trans; [eauto|].
                  eapply exec_star_trans, exec_t_exec; eauto.
                  eapply exec_step_t; eauto. }
                do 3 rewrite Forall_app; clarify. }
              { eapply Forall_impl, exec_star_ops; eauto; unfold beq; clarify. }
              { repeat rewrite <- app_assoc; auto. }
              { eapply prog_steps, exec_t_exec; eauto. }
              { rewrite <- app_assoc; apply init_steps; auto.
                eapply prog_steps, exec_star_trans; eauto.
                eapply exec_step_inv; eauto. } }
            { destruct H0; clarify.
              specialize (Hext [c0]).
              repeat rewrite <- app_assoc in *; simpl in *; rewrite Hext.
              rewrite split_app; do 2 rewrite app_assoc.
              rewrite (app_assoc _ _ [c0]); rewrite loc_valid_ops1_SC; auto.
              repeat rewrite <- app_assoc; clarify.
              { exploit instrument_own_thread;
                  try (eapply exec_t_exec, Hfinish);
                  try (eapply exec_star_trans; [apply Hroot|]); eauto.
                { eapply exec_step_inv; eauto. }
                { rewrite in_app; eauto. }
                { rewrite in_app; simpl; destruct Hin; eauto; clarify. }
                rewrite filter_negb_all.
                intro; eapply Forall_impl; eauto.
                intros; simpl in *.
                intro Heq; rewrite Heq in *; clarify.
                { exploit exec_star_ops; eauto.
                  intro; eapply Forall_impl; eauto 2; unfold beq; clarify. } }
              { eapply prog_steps, exec_t_exec; eauto. } } }
        { clear; intros; rewrite in_app in Hin; setoid_rewrite in_app.
          simpl in *; destruct Hin as [? | [? | ?]]; clarify; eauto. }
        { rewrite app_nil_r.
          exploit nth_error_in; eauto; intro.
          destruct i; simpl in Hi; inversion Hi; clarify.
          * exploit assign_in_handler; eauto; intros [? | [? | ?]]; clarify.
            rewrite skipn_length in Hlen; simpl in Hlen; destruct n; clarify.
          * exploit spawn_in_handler'; eauto; clarify.
            rewrite app_length in Hlen; simpl in Hlen.
            rewrite Nat.add_sub, skipn_app, skipn_all, minus_diag in Hlen;
              clarify.
          * apply Forall2_app; auto; constructor; clarify.
            exists (S n).
            rewrite <- Nat.add_1_r, <- skipn_skipn, skipn_app, <- Hn; clarify.
            rewrite skipn_length in Hlen; omega. }
  - destruct H as (? & ? & ? & ? & ? & ? & ? & P2' & ? & ? & ? & ? & ? & Hnext &
      ? & HP2' & Hthreads).
    exploit exec_result; eauto; intros (? & i & ? & ? & v & ? & Hresult).
    right; destruct (instr_result t i (G' t) v) as [((((?, ?), ?), ?), ?)|]
      eqn: Hr; clarify.
    subst; exploit HP2'; [apply split_in |
      intros [Hcase | [(? & Hcase) | (? & Hcase)]]]; subst.
    + destruct Hcase as (? & Henv & Hrel).
      assert (P2 P2').
      { destruct i; simpl in Hr; inversion Hr; clarify.
        * rewrite in_map_iff in *; intros ((?, ?) & ?); clarify.
          exploit Hthreads; eauto; clarify.
          contradiction Hresult2222; do 2 eexists; eauto; auto.
        * exploit HP2'; eauto; clarify.
          exploit app_eq_nil; eauto; clarify. }
      exploit in_split; eauto; clarify.
      rewrite <- Henv in Hr; exploit result_exec; eauto; setoid_rewrite Hr;
        intro Hstep'.
      use Hstep'; eauto.
      do 10 eexists; eauto.
      split; [eapply exec_step_inv; eauto|].
      exploit prog_step; eauto; intro Hprog.
      use Hrel.
      apply conjI1; [|split; [|split; [|split; [|split]]]].
      * destruct c; [|rewrite app_nil_r; auto].
        exploit iexec_thread; eauto; intros (li & Hin1).
        exploit exec_keep; try apply Hin1; eauto.
        { eapply distinct_steps; eauto. }
        intros (n & Hin); specialize (HP2' _ _ Hin).
        destruct (nil_dec (skipn n li)).
        { destruct HP2' as [? | [? | ?]]; clarify; try rewrite e in *.
          repeat rewrite app_assoc in *; eapply mostly_complete_t with (t := x);
            try apply Hexec'; eauto.
          * eapply exec_star_trans; eauto.
          * contradiction.
          * exploit app_eq_nil; eauto; clarify.
            rewrite skipn_all_iff in *; simpl in *; omega. }
        repeat rewrite app_assoc in *; eapply mostly_complete; try apply Hexec';
          eauto.
        { eapply exec_star_trans; eauto. }
      * destruct c; [|do 2 rewrite app_nil_r; auto].
        repeat rewrite app_assoc in *; apply mem_vals_step; auto.
        exploit prog_step; eauto; intro X; inversion X; auto.
      * destruct c; [|do 2 rewrite app_nil_r; auto].
        repeat rewrite app_assoc in *; eapply mostly_ext_step';
          try apply Hexec'; auto.
        eapply exec_star_trans; eauto.
      * destruct o3 as [(?, ?)|]; clarify.
        repeat intro; unfold upd_env, upd; clarify.
      * intros.
        generalize (in_cases _ _ _ _ _ Hin); intros [? | [? | ?]]; clarify.
        { left.
          split; [apply split_in|].
          split.
          { destruct o3 as [(?, ?)|]; auto.
            unfold upd_env; repeat rewrite upd_new.
            unfold upd; rewrite Henv; auto. }
          intro; destruct c; [|repeat rewrite app_nil_r; auto].
          repeat rewrite app_assoc in *; apply mem_ext_t_step; auto.
          inversion Hprog; auto. }
        { left.
          split; [rewrite in_app; simpl; rewrite in_app; clarify|].
          destruct o0; [|clarify].
          destruct i; simpl in Hr; inversion Hr; clarify.
          split.
          { admit. }
          intro; repeat rewrite app_nil_r.
          admit. }
        assert (t' <> t).
        { intro; subst.
          exploit distinct_steps; eauto; intro.
          exploit distinct_steps; eauto; intro Hdistinct'.
          unfold distinct in Hdistinct'; rewrite map_app in Hdistinct';
            simpl in Hdistinct'.
          exploit NoDup_remove_2; try apply Hdistinct'; auto.
          rewrite <- map_app, in_map_iff.
          do 2 eexists; eauto; auto. }
        specialize (HP2' t' li); use HP2'.
        destruct HP2' as [Hcase | [(? & Hcase) | (? & Hcase)]];
          [left | right; left | right; right]; subst.
        { admit. }
        { destruct li; auto; destruct Hcase as (Hin' & v' & ? & ? & ? & ? & ?).
          split; auto; split.
          { rewrite in_app in Hin'; rewrite in_app; clarify; rewrite in_app;
              clarify. }
          do 2 eexists; eauto; split; auto.
          split.
          { destruct o3 as [(?, ?)|]; auto.
            unfold upd_env, upd; clarify. }
          destruct c; [|repeat rewrite app_nil_r in *; auto].
          inversion Hprog; subst.
          split.
          { repeat rewrite app_assoc in *; apply mem_ext_t_l_step; auto. }
          destruct (eq_dec (loc_of c) (X + v', 0)).
          { (* By Hcon and unlock_locked, c can only be Rel. *) admit. }
          { rewrite <- app_assoc; simpl.
            repeat rewrite app_assoc in *; rewrite loc_valid_SC; auto.
            { simpl; auto. } } }
        { destruct Hcase as (? & ? & ? & ? & Hmem & ? & ? & Hin' & Hrest).
          split; auto; do 3 eexists; eauto.
          split; auto; split; [|do 2 eexists; eauto].
          { intros; specialize (Hmem l).
            destruct c; [|rewrite app_nil_r in *; auto].
            rewrite <- app_assoc in *; simpl in *.
            repeat rewrite app_assoc in *; eapply consistent_next; eauto.
            { inversion Hprog; auto. }
            { simpl; auto. } }
          split.
          { rewrite in_app in Hin'; rewrite in_app; clarify; rewrite in_app;
              clarify. }
          intros.
          exploit Hrest.
          { eapply exec_step_t; eauto.
 }
        { rewrite in_app in *; clarify. }
      * intros.
        setoid_rewrite in_app; simpl; setoid_rewrite in_app.
        generalize (in_cases _ _ _ _ _ Hin); intros [? | [? | ?]]; eauto.
        exploit Hthreads; [apply list_in_insert; eauto|].
        intros (? & Hin'); rewrite in_app in Hin'; simpl in Hin'.
        destruct Hin' as [? | [? | ?]]; eauto; clarify; eauto.
      * clear; left; intro; clarify.
    + destruct Hcase as (? & v' & ? & ? & ? & (Hl & Hc) & Hcon').
      do 10 eexists; eauto.
      split; eauto; clarify.
      split; [|split; [|split; [|split]]]; auto.
      * repeat rewrite app_assoc in *; apply mem_vals_app_meta; auto.
        { intros; rewrite <- app_assoc; eapply init_steps, prog_steps; auto.
          eapply exec_star_trans; eauto. }
        { constructor; auto; apply X_meta; auto. }
        { constructor; simpl; auto. }
      * intros ???? Hcon''.
        destruct (eq_dec (loc_of c) (X + v', 0)).
        { rewrite e in Hlock; use Hlock; clarify.
          destruct Hlock; clarify.
          { repeat rewrite app_assoc in *; rewrite can_arw_SC_iff' in Hcon'.
            rewrite can_arw_SC_iff'; auto. }
          { repeat rewrite <- app_assoc in Hcon''; simpl in Hcon''.
            repeat rewrite app_assoc in Hcon''; eapply rel_rel in Hcon'';
              contradiction. }
          { eapply locks_spec; try apply split_in.
            { eapply exec_star_trans; eauto. }
            { simpl; auto. } } }
        { apply Hnext; auto.
          repeat rewrite <- app_assoc in Hcon''; simpl in Hcon''.
          repeat rewrite app_assoc in *; rewrite loc_valid_SC in Hcon'';
            clarify. }
      * intros.
        apply in_app_cases in Hin; destruct Hin as [? | Hin].
        { clarify.
          left; clarify.
          split.
          * intros ?? Hcon''; destruct (eq_dec l (X + v')).
            { repeat rewrite <- app_assoc in Hcon''; simpl in Hcon''.
              subst; repeat rewrite app_assoc in Hcon'';
                eapply rel_rel in Hcon''; contradiction. }
            { apply Hl; simpl; auto.
              repeat rewrite <- app_assoc in Hcon''; simpl in Hcon''.
              repeat rewrite app_assoc in *; rewrite loc_valid_SC in Hcon'';
                clarify.
              intro; clarify. }
          * intros ??? Hcon''; apply Hc; auto.
            repeat rewrite <- app_assoc in Hcon''; simpl in Hcon''.
            repeat rewrite app_assoc in *; rewrite loc_valid_SC in Hcon'';
              clarify.
            intro; destruct (loc_of c); clarify.
            exploit Hmetalocs_disjoint_CX; eauto.
            exploit bounded_sim; eauto; intro Hbound.
            eapply bounded_steps in Hbound; eauto.
            eapply bounded_steps in Hbound; eauto.
            setoid_rewrite Forall_app in Hbound;
              destruct Hbound as (_ & Hbound); inversion Hbound as [|?? Hbt].
            inversion Hbt; auto. }
        assert (t' <> x).
        { intro; subst.
          exploit distinct_steps; eauto; intro.
          exploit distinct_steps; eauto; intro Hdistinct'.
          unfold distinct in Hdistinct'; rewrite map_app in Hdistinct';
            simpl in Hdistinct'.
          exploit NoDup_remove_2; try apply Hdistinct'; auto.
          rewrite <- map_app, in_map_iff.
          do 2 eexists; eauto; auto. }
        specialize (HP2' t' li); use HP2'.
        destruct HP2' as [Hcase | [Hcase | Hcase]]; left; clarify.
        admit.
        { rewrite in_app in *; clarify. } 
      * intros.
        exploit Hthreads; eauto; intros (? & Hin').
        setoid_rewrite in_app; simpl.
        rewrite in_app in Hin'; simpl in Hin'; destruct Hin' as [? | [? | ?]];
          eauto; clarify; eauto.
    + destruct Hcase as (n & l & ? & ? & Hmem & ? & ? & ?).
      do 10 eexists; eauto.
      split; eauto; clarify.
      destruct (skipn n (lock_handler x l zt)) eqn: Hskip.
      { rewrite skipn_all_iff in Hskip; exfalso; omega. }
      clarify.
      exploit skipn_cons_nth; eauto; intro Hn.
      exploit nth_error_in; eauto; intro.
      assert (x < zt).
      { exploit bounded_sim; eauto; intro Hbound.
        do 2 (eapply bounded_steps in Hbound; eauto).
        setoid_rewrite Forall_app in Hbound; destruct Hbound as (_ & Hbound);
          inversion Hbound as [|?? Ht1]; inversion Ht1; auto. }
      assert (meta_instr i0 = true) as Hmeta.
      { exploit max_vc_instrs; eauto; intros [(? & ? & [? | [? | ?]]) | ?];
          clarify.
        * contradiction n0; apply L_meta; auto.
        * contradiction n1; apply C_meta; auto.
        * contradiction n0; apply C_meta; auto. }
      exploit distinct_steps; eauto; intro.
      exploit distinct_steps; eauto; intro Hdistinct'.
      exploit meta_instr_ops; try apply Hexec'; eauto.
      { apply split_in. }
      intros (Hc & Henv').
      exploit prog_step; eauto; intro Hprog.
      destruct o0.
      { destruct i0; simpl in Hr; inversion Hr; clarify. }
      split; [|split; [|split; [|split]]]; auto.
      * repeat rewrite app_assoc in *; apply mem_vals_app_meta; auto.
        intros; repeat rewrite <- app_assoc; eapply init_steps, prog_steps;
          eauto.
        eapply exec_star_trans; eauto.
      * destruct c; [|rewrite app_nil_r; auto].
        inversion Hprog; subst.
        assert ((exists t p v, c = Read t p v) \/ fst (loc_of c) = C + x)
          as [(? & ? & ? & ?) | ?].
        { exploit max_vc_instrs; eauto; intros [(? & ? & [? | [? | ?]]) | ?];
            clarify; eauto. }
        { subst; intros ???? Hcon'.
          repeat rewrite <- app_assoc in Hcon'; simpl in Hcon'.
          repeat rewrite app_assoc in Hcon'; exploit consistent_drop; eauto;
            intro; rewrite read_noop_SC in Hcon'; auto.
          apply Hnext; auto.
          rewrite app_assoc; auto. }
        { intros ???? Hcon'.
          repeat rewrite <- app_assoc in Hcon'; simpl in Hcon'.
          repeat rewrite app_assoc in Hcon'; rewrite loc_valid_SC in Hcon';
            auto.
          destruct Hcon'; apply Hnext; auto.
          rewrite app_assoc; auto.
          { destruct (loc_of c), (loc_of c0); clarify.
            intro; clarify. } }
      * etransitivity; eauto.
        symmetry; auto.
      * intros.
        simpl in Hin; apply in_app_cases in Hin; destruct Hin as [? | Hin].
        { clarify.
          destruct (eq_dec n (length (lock_handler x l zt) - 1)).
          + left; subst; erewrite skipn_but_one in Hskip; eauto; clarify.
            unfold lock_handler in Hn; rewrite max_vc_last in Hn; clarify.
            split; [|split].
            * (* We need to carry enough info to know that the env is exactly
                 equal once the handler finishes. *) admit.
            * intros ?? Hcon''; destruct (eq_dec l0 (C + x)).
              { subst; exploit good_lock_instr; try eapply exec_star_trans;
                  eauto.
                { apply split_in. }
                { auto. }
                clear; clarify. }
              { repeat rewrite <- app_assoc in *; apply Hmem; simpl; auto.
                simpl in Hcon''; repeat rewrite app_assoc in *;
                  rewrite loc_valid_SC in Hcon''; clarify.
                intro; clarify. }
            * admit. (* Also enough info to know that C + t will be in the same
                state once the handler finishes. *)
          + right; right; split; auto.
            exists (S n), l; split; [omega|].
            split; auto; split.
            * admit.
            * erewrite skipn_n in Hskip; eauto; clarify; eauto. }
        assert (t' <> x).
        { intro; subst.
          unfold distinct in Hdistinct'; rewrite map_app in Hdistinct';
            simpl in Hdistinct'.
          exploit NoDup_remove_2; try apply Hdistinct'; auto.
          rewrite <- map_app, in_map_iff.
          do 2 eexists; eauto; auto. }
        specialize (HP2' t' li); use HP2'.
        destruct HP2' as [Hcase | [Hcase | Hcase]]; left; clarify.
        admit.
        { rewrite in_app in *; clarify. } 
      * intros.
        exploit Hthreads; eauto; intros (? & Hin').
        setoid_rewrite in_app; simpl.
        rewrite in_app in Hin'; simpl in Hin'; destruct Hin' as [? | [? | ?]];
          eauto; clarify; eauto.
Qed.
*)
Lemma part_complete : forall P0 P (Hsim : state_sim P0 P)
  (Ht : Forall (fun e => fst e < zt) P0)
  (Hsafe : safe_locs P0) (Hfresh : fresh_tmps P0) (Hdistinct : distinct P)
  G lo lc P' G' (Hexec : exec_star (Some P) G lo lc (Some P') G')
  (Hsuffix : state_suffix P0 P') m (Hcon : consistent (m ++ lc))
  (Hinit : forall p, initialized m p),
  exists lo1 lc1 P1 G1 P1' lo2 lc2 P2, iexec_star P G lo1 lc1 P1 G1 /\
    mem_vals (m ++ lc) (m ++ lc1) /\ env_sim G' G1 /\
    state_sim P1' P1 /\ safe_locs P1' /\ fresh_tmps P1' /\
    exec_star (Some P1) G1 lo2 lc2 (Some P2) G' /\ state_suffix P1' P2 /\
    consistent (m ++ lc1 ++ lc2) /\
    (forall c (Hprog : prog_op c) (Hlock : locks (fst (loc_of c)) P ->
       exists t, c = Acq t (fst (loc_of c))),
       consistent (m ++ lc1 ++ lc2 ++ [c]) <->
       consistent (m ++ lc ++ [c])) /\
    forall t li (Hin : In (t, li) P'), In (t, li) P2 /\
      (forall li0, In (t, li0) P1' <-> In (t, li0) P0) \/
    match li with [] => False | i :: li => In (t, li) P2 /\
      exists l, i = Unlock l /\ meta_loc (l, 0) end \/
    exists n l, n < length (instrument_instr (Lock l) t) /\
      exists li', li = skipn n (instrument_instr (Lock l) t) ++ li' /\
      In (t, li') P2.
Proof.
  admit.
(*  intros; remember (Some P) as Pa; remember (Some P') as Pb;
    generalize dependent P'; rewrite exec_rev in Hexec; induction Hexec;
    clarify.
  { do 9 eexists; [apply iexec_refl|].
    split; [reflexivity|].
    split; [apply env_sim_refl|].
    split; eauto; clarify.
    split; [apply exec_refl|].
    split; [apply sim_suffix; auto | clarify].
    split; [reflexivity|].
    left; clarify; reflexivity. }
  rewrite <- exec_rev in Hexec.
  rewrite app_assoc in Hcon; exploit consistent_app_SC; eauto; clarify.
  specialize (IHHexec _ eq_refl).
  exploit state_suffix_inv; eauto.
  { eapply exec_step, exec_refl; eauto. }
  intro Hsuffix0; use IHHexec.
  destruct IHHexec as (? & ? & ? & ? & ? & ? & ? & P2 & Hiexec & Hmem &
    Henv & Hsim' & Hsafe' & ? & Htail & Hsuffix' & ? & Hext & HP2); clarify.
  exploit exec_result; eauto; intros (? & i & rest & ? & v & Hresult); clarify.
  exploit HP2; [apply split_in|]; intros [[? Hiff] | [? | ?]].
  - destruct (instr_result t i (G' t) v) as [((((?, ?), ?), ?), ?)|] eqn: Hi;
      clarify.
    assert (P1 P2).
    { destruct i; clarify.
      + contradiction Hresult22222.
        rewrite (suffix_threads Hsuffix0 Hsuffix).
        rewrite map_app, in_app; simpl; auto.
      + exploit HP2; eauto; clarify.
        exploit app_eq_nil; eauto; clarify. }
    exploit in_split; eauto; clarify.
    exploit result_exec; eauto; setoid_rewrite Hi; intro X.
    exploit X; clear X; eauto; intro Hexec2.
    destruct (find (fun c => if meta_loc_dec (loc_of c) then false else true)
      (opt_to_list c)) eqn: Hfind.
    + destruct c; clarify.
      exploit distinct_steps.
      { eauto. }
      { eapply exec_star_trans; [eapply iexec_execs; eauto | eauto]. }
      intro Hdistinct1; exploit state_suffix_inv'; eauto.
      intros (? & li & ? & n0 & ?); clarify.
      destruct li; [rewrite skipn_nil in *; clarify | simpl in *].
      rewrite skipn_app, le_minus_0 in *; [|omega].
      destruct (skipn n0 (instrument_instr i0 t)) eqn: Hskip.
      { rewrite skipn_all_iff in Hskip; omega. }
      clarify.
      destruct (eq_dec n0 (length (instrument_instr i0 t) - 1)).
      { exploit distinct_steps; try apply Hexec; auto; intro.
        assert (l = []).
        { assert (length (skipn n0 (instrument_instr i0 t)) = length (i1 :: l))
            as Hlen by (rewrite Hskip; auto).
          clarify; rewrite skipn_length in Hlen.
          destruct l; auto; simpl in Hlen; omega. }
        subst; exploit state_suffix_inv'; try apply Hsuffix0; auto.
        intros (? & li0 & ?); clarify.
        assert (li0 = i0 :: li).
        { specialize (Hiff li0); destruct Hiff as [_ Hiff].
          rewrite in_app in Hiff; clarify.
          rewrite <- distinct_suffix in Hdistinct1; eauto.
          eapply distinct_in; eauto; apply split_in. }
        subst; exploit state_suffix_inv'; try apply Hsuffix.
        { eapply distinct_step; eauto. }
        intros (? & ? & ? & n' & Heq & ? & ? & Hskip' & ?); clarify.
        exploit distinct_thread; try apply Heq; auto.
        { rewrite (distinct_suffix Hsuffix0); auto. }
        clarify.
        rewrite skipn_app, le_minus_0 in Hskip'; [|omega].
        destruct (skipn n' (instrument_instr i0 t)) eqn: H';
          [rewrite skipn_all_iff in H'; omega|].
        simpl in *; exploit cons_app_neq; eauto; contradiction. }
      assert (t < zt).
      { rewrite Forall_forall in Ht; exploit Ht.
        { rewrite <- Hiff; apply split_in. }
        auto. }
      assert (accesses i1 = Some (loc_of c0)).
      { rewrite <- exec_accesses; eauto; simpl; auto. }
      exploit instr_access; eauto.
      { rewrite <- skipn_nth; setoid_rewrite Hskip.
        instantiate (1 := 0); auto. }
      { setoid_rewrite Forall_app in Hsafe'; clarify.
        inversion Hsafe'2 as [|?? Hsafei]; inversion Hsafei; auto. }
      { destruct i0; auto.
        destruct n0; clarify.
        admit. }
      intros [? ?]; subst.
      destruct i0; try destruct x3; clarify.
      * exploit Forall2_app_inv_l; try apply Hsim'.
        intros (? & ? & ? & Hrest & ?); inversion Hrest; subst.
        destruct y; clarify.
        


        (* H1 gives us the values for a successful execution of the
           instrumentation.
        exploit iexec_load.
        { eauto. }*)
        admit.
      * admit.
      * exploit Forall2_app_inv_l; try apply Hsim'.
        intros (? & ? & ? & Hrest & ?); inversion Hrest; subst.
        destruct y; clarify.
        (* Here we want to provide whatever values can be read, i.e.,
           whatever vals will make m ++ x0 ++ vals consistent.
        exploit iexec_lock.
        { eauto. }*)
        admit.
    + exploit exec_step_inv; eauto; intro Hsteps2.
      do 9 eexists; eauto.
      split.
      { rewrite app_assoc; apply mem_vals_app_meta; auto.
        * intros; eapply init_steps, prog_steps; eauto.
        * destruct c; clarify.
        * eapply prog_step; eauto. }
      split.
      { admit. }
      do 5 (split; eauto).
      { admit. }
      split.
      { destruct c; [clarify | rewrite app_nil_r; auto].
        rewrite <- app_assoc in *; rewrite Hext; auto.
        { exploit prog_step; eauto; intro X; inversion X; auto. }
        { admit. } }
      split.
      * intros.
        admit.
      * intros.
        exploit distinct_steps; eauto; intro.
        exploit in_step_rev; try apply Hin; eauto; intros [? | [? | ?]].
        { destruct (eq_dec t0 t).
          { subst; exploit distinct_in;
              [eauto | apply split_in | eauto | clarify].
            exploit distinct_step; eauto; intro.
            exploit distinct_in;
              [eauto | apply split_in | eauto | clarify].
            exploit cons_neq; eauto; contradiction. }
          exploit HP2; eauto; intros [Hin' | Hin'].
          * left; rewrite in_app; simpl.
            rewrite in_app; rewrite in_app in Hin'; clarify.
          * right; destruct li; clarify.
            split; eauto.
            rewrite in_app; simpl.
            rewrite in_app; rewrite in_app in Hin'1; clarify. }
        { clarify.
          exploit distinct_step; eauto; intro.
          exploit distinct_in; [eauto | apply split_in | eauto | clarify].
          rewrite in_app; simpl; auto. }
        { clarify.
          exploit distinct_in; [eauto | apply split_in | eauto | clarify].
          rewrite in_app; simpl; auto. }
  - clarify.
    do 9 eexists; eauto.
    split.
    { rewrite app_assoc; apply mem_vals_app_meta; auto.
      * intros; eapply init_steps, prog_steps; eauto.
      * constructor; simpl; auto. }
    split; auto.
    repeat (split; eauto).
    intros.
    destruct (eq_dec t0 t).
    + exploit distinct_steps; eauto; intro.
      exploit distinct_step; eauto; intro.
      subst; exploit distinct_in; [eauto | apply split_in | eauto | clarify].
    + apply HP2; rewrite in_app in *; clarify.*)
Qed.

Definition no_asserts := state_forall
  (fun i => match i with Assert_le _ _ => False | _ => True end).

Inductive fail_iexec P (*G*) t :
  list operation -> list conc_op -> (*state -> env -> *)Prop :=
  | fail_raw P1 P2 a x o v1 v2 rest vs1 vs2
    (Hload: P=P1++(t, load_handler t x zt ++
                                   Load a (x, o) :: Unlock (X + x) :: rest) :: P2)
      (Hgt : first_gt vs1 vs2 = Some (v1,v2) )  (Hlen1: length vs1 <=zt) (Hlen2: length vs2 <=zt):
      fail_iexec P (*G*) t (acq t (X + x) :: events_hb_check (W + x) (C + t) vs1 vs2 t )
                  (Acq t (X + x) ::
                   mops_hb_check (W + x) (C + t) vs1 vs2 zt t)
  | fail_waw P1 P2 x o e v1 v2 rest vs1 vs2
      (Hstore : P = P1 ++ (t, store_handler t x zt ++
                              Store (x, o) e :: Unlock (X + x) :: rest) :: P2)
      (Hgt : first_gt vs1 vs2 = Some (v1,v2) ) (Hlen1: length vs1 <=zt) (Hlen2: length vs2 <=zt)  :
      fail_iexec P (*G*) t (acq t (X + x) :: events_hb_check (W + x) (C + t) vs1 vs2 t )
                  (Acq t (X + x) ::
                   mops_hb_check (W + x) (C + t) vs1 vs2 zt t )
  | fail_war P1 P2 x o e v1 v2 rest vs1 vs2 vs3
      (Hstore : P = P1 ++ (t, store_handler t x zt ++
                              Store (x, o) e :: Unlock (X + x) :: rest) :: P2)
      (Hle : first_gt vs1 vs2 = None ) (Hgt: first_gt vs3 vs2 = Some (v1, v2) )
      (Hlen1 : length vs1 = zt) (Hlen3: length vs3 = zt)
      (Hlen2: length vs2 = zt):
      fail_iexec P (*G*) t (acq t (X + x) :: events_hb_check (W + x) (C + t) vs1 vs2 t ++
                       events_hb_check (R + x) (C + t) vs3 vs2 t)
                  (Acq t (X + x) ::
                       mops_hb_check (W + x) (C + t) vs1 vs2 zt t ++
                  mops_hb_check (R+x) (C + t) vs3 vs2 zt t ).

Lemma fail_safe : forall Pa P (Hsim : state_sim Pa P) (Hsafe : safe_locs Pa)
  (Hfresh : fresh_tmps Pa) (Hno : no_asserts Pa)
  G lo lc P' G' (Hexec : exec_star (Some P) G lo lc (Some P') G')
  (Hsuffix : state_suffix Pa P') t o c G'' (Hfail : exec P' G' t o c None G'')
  P0 (Hdistinct0 : distinct P0) P0' (Hsim0 : state_sim P0' P0)
  (Hsafe0 : safe_locs P0') (Hfresh0 : fresh_tmps P0')
  (Ht : Forall (fun e => fst e < zt) P0')
  (Hlocks : forall l, locks l P0 -> good_lock (l, 0) P0)
  (Hlocks2 : forall l, l < zl -> well_locked l P0)
  (HX_locks : forall v, v < zv -> good_lock (X + v, 0) P0)
  (Hvars : forall v, v < zv -> good_var v P0)
  (Hspawns : safe_spawns P0) (Hwaits : safe_waits P0)
  G0 lo0 lc0 (Hroot : exec_star (Some P0) G0 lo0 lc0 (Some P) G)
  m (Hcon : consistent (m ++ lc0 ++ lc ++ opt_to_list c))
  (Hinit_l : forall l, l < zl -> initialized m (l, 0))
  (Hinit_v : forall v, v < zv -> initialized m (X + v, 0))
  (HC_init : forall t o, t < zt -> o < zt -> initialized m (C + t, o)),
  exists lo1 lc1 P1 G1 lo2 lc2, iexec_star P G lo1 lc1 P1 G1 /\
    mem_vals (m ++ lc0 ++ lc) (m ++ lc0 ++ lc1) /\ env_sim G' G1 /\
    fail_iexec P1 t lo2 lc2 /\ consistent (m ++ lc0 ++ lc1 ++ lc2).
Proof.
  intros.
  inversion Hfail; subst; rewrite app_nil_r in *.
  exploit part_complete; try apply Hsim; eauto.
  { admit. }
  { admit. }
  { rewrite app_assoc in Hcon; eauto. }
  { admit. }
  intros (? & ? & ? & ? & ? & ? & ? & P4 & Hiexec & ? & ? & ? & ? & ? & Hrest &
    ? & ? & HP4).
  repeat rewrite <- app_assoc in *.
  admit.
(*  assert (exec P4 G'' t None None None G'').
  { exploit HP4.
    { apply split_in. }
    intros [? | Hlock].
    * clarify.
      exploit in_split; eauto 2; clarify.
      eapply exec_assert_fail; eauto.
    * destruct Hlock as [? | (n & l & ?)]; clarify.
      destruct (skipn n (Lock l :: lock_handler t l zt)) eqn: Hskip; clarify.
      { rewrite skipn_all_iff in Hskip; simpl in Hskip; omega. }
      exploit skipn_in.
      { setoid_rewrite Hskip; simpl; eauto. }
      clarify.
      exploit max_vc_instrs; eauto; clarify. }
  exploit exec_star_trans; try apply Hroot.
  { eapply iexec_execs; eauto. }
  intro Hroot'.
  exploit first_fail'; try apply Hroot'; eauto.
  { admit. }
  intro X; exploit X; clear X; eauto.
  { rewrite app_nil_r, <- app_assoc; auto. }
  clarify; do 7 eexists; eauto.
  do 2 (split; auto).
  split; eauto.
  rewrite <- app_assoc in *; auto.*)
Qed.

Lemma iexec_trans : forall P G lo lc P' G' lo' lc' P'' G''
  (Hiexec1 : iexec_star P G lo lc P' G')
  (Hiexec2 : iexec_star P' G' lo' lc' P'' G''),
  iexec_star P G (lo ++ lo') (lc ++ lc') P'' G''.
Proof.
  intros ???????????; induction Hiexec1; clarify.
  repeat rewrite <- app_assoc; eapply iexec_step; eauto.
Qed.
  
End Reordering.