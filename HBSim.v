Require Import Util.
Require Import VectorClocks.
Require Import block_model.
Require Import conc_model.
Require Import Lang.
Require Import FunctionalExtensionality.
Require Import HBRaceDetector.
Set Implicit Arguments.

Section Sim_Proofs.

Context (ML : @Memory_Layout var nat _).

Context (meta : metadata).

Hypothesis Hmetalocs_disjoint: forall t l x y z, 
  (t<zt -> x< zv -> C+t <> X+x )/\ 
  (z<zv -> x< zv -> R+z <> X+x )/\ 
  (y<zv -> x< zv -> W + y<> X+x) /\ 
  (l<zl -> x< zv -> L+l <> X+x )/\
  (l<zl -> t< zt -> C+t <> L+l ).

Notation C' := C.
Notation L' := L.
Notation R' := R.
Notation W' := W.
Notation X' := X.

Hypothesis Hs_x : forall (x0 : nat) m ,
         x0 < zv -> can_read m (X + x0, 0) 0 /\ can_write m (X + x0, 0).


Hypothesis Hmetalocs_disjoint_CX: forall t x, (t < zt -> x < zv -> C' + t <> X' + x).
Hypothesis Hmetalocs_disjoint_RX: forall z x,   (z < zv -> x < zv -> R' + z <> X' + x).
Hypothesis Hmetalocs_disjoint_CR: forall t x, (t < zt -> x < zv -> C' + t <> R' + x).
Hypothesis Hmetalocs_disjoint_CW: forall t x, (t < zt -> x < zv -> C' + t <> W' +x ).
Hypothesis Hmetalocs_disjoint_LR: forall l x, (l < zl -> x < zv -> L' +l  <> R' + x).
Hypothesis Hmetalocs_disjoint_LW: forall l x, (l < zl -> x < zv -> L' + l <> W' + x).
Hypothesis Hmetalocs_disjoint_WX: forall y x,  (y < zv -> x < zv -> W' + y <> X' + x).
Hypothesis Hmetalocs_disjoint_WR: forall y x, (y < zv -> x < zv -> W' + y <> R' + x).
Hypothesis Hmetalocs_disjoint_LX: forall l x,  (l < zl -> x < zv -> L' + l <> X' + x).
Hypothesis Hmetalocs_disjoint_CL: forall l t,  (l < zl -> t < zt -> C' + t <> L' + l).

Hint Resolve Htmp.
Hint Resolve Hnonoverlap.

Lemma can_read_thread' : forall m p v t,   consistent (m ++ [Read t p v]) ->
     can_read m p v .
Proof.
  unfold can_read, consistent, SC; setoid_rewrite lower_app; clarify.
Qed.

Lemma write_any_SC: forall t v m p
 (Hcon: consistent (m++[Write t p v ])),  can_write m p. 
Proof.
  intros. 
  unfold can_write, consistent, SC in *.  intros. rewrite lower_app in *. 
  rewrite lower_app in Hcon. rewrite lower_single in *. rewrite lower_single in Hcon.
  simpl. simpl in Hcon. rewrite write_any_value. eauto.
Qed.

Lemma acq_con: forall m t0 x 
 (Hcon: consistent m ) (Hx2: x < zv), consistent (m ++[Acq t0 (X+x)]).
Proof.
  intros.
  specialize(Hs_x m Hx2); inversion Hs_x; clarify;
  apply can_arw_SC; auto.
Qed.

Lemma clocks_sim_acq : forall m t0 x s
 (Hcon: consistent m) (Hx2: x < zv) (Hs: clocks_sim m s), clocks_sim (m ++ [Acq t0 (X+x)]) s.
Proof.
  intros.
  inversion Hs as [ Hs_c (Hs_l, Hs_rw)]; clarify.
  unfold clocks_sim. split;[|split;[|split]]; intros.
  exploit acq_con; eauto.
  intro Hacq_con.
  instantiate (1:=t0) in Hacq_con.
  -unfold clock_match. intros. 
   destruct (lt_dec t zt); clarify.
   specialize(Hs_c t H). unfold clock_match in Hs_c. specialize(Hs_c t1). 
   destruct (lt_dec t1 zt); clarify.
   split; auto.
   +apply can_read_SC; auto.
    { constructor; clarify. }
    { constructor; clarify.  specialize(Hmetalocs_disjoint_CX H Hx2). intro Heq. inversion Heq; clarify. }
    
   +apply can_write_SC; auto.
    { constructor; clarify. }
  -unfold clock_match. intros.
   destruct (lt_dec t zt); simpl.
   specialize(Hs_l l H). unfold clock_match in Hs_l. specialize(Hs_l t).
   split; auto.
   +apply can_read_SC; clarify.
    apply acq_con; auto.
    { constructor; clarify. }
    { constructor; clarify. specialize(Hmetalocs_disjoint_LX H Hx2). intro Heq; inversion Heq; clarify. }
   +apply can_write_SC; clarify.
    apply acq_con; auto.
    constructor; clarify.
   +specialize(Hs_l l H). unfold clock_match in Hs_l. specialize(Hs_l t). clarify.
  -unfold clock_match. intros; destruct (lt_dec t zt); clarify;
   specialize(Hs_rw v H); unfold clock_match in Hs_rw; inversion Hs_rw.
   +clarify. specialize(Hs_rw1 t). clarify. split; auto.
    *apply can_read_SC; auto.
     apply acq_con; auto.
     { constructor; clarify. }
     { constructor; clarify. specialize(Hmetalocs_disjoint_RX H Hx2). intro Heq; inversion Heq; clarify. }
     
    *apply can_write_SC; auto.
     apply acq_con; auto.
     constructor; clarify.
   +specialize(H0 t). clarify.
  
   -unfold clock_match. intros; destruct (lt_dec t zt); clarify;
    specialize(Hs_rw v H); unfold clock_match in Hs_rw; inversion Hs_rw.
    +clarify. specialize(Hs_rw2 t). clarify. split; auto.
    *apply can_read_SC; auto.
     apply acq_con; auto.
     { constructor; clarify. }
     { constructor; clarify. specialize(Hmetalocs_disjoint_WX H Hx2). intro Heq; inversion Heq; clarify. }
     
    *apply can_write_SC; auto.
     apply acq_con; auto.
     constructor; clarify.
   +specialize(H1 t). clarify.
Qed.

Hypothesis zt_non_zero : zt <> 0.

Lemma map_fst : forall (X Y: Type) l1 l2, Forall2 (fun (x y: X*Y) => fst x =fst y) l1 l2 -> map fst l1 = map fst l2.
Proof.
  intros A B l1.
  induction l1; clarify.
  -inversion H; clarify. 
  -destruct l2; clarify.
   +inversion H; clarify.
   +inversion H; clarify.
    specialize(IHl1 l2 H5). clarify.
    rewrite IHl1, H3.
    auto.
Qed.


Lemma in_mops_max_vc': forall n c vc1 vc2 vs1 vs2 t
   (Hin: In c (mops_max_vc vc1 vc2 vs1 vs2 t n)),
  match c with 
  | Write tc p _ => fst p = vc2
  | Read tc p _  => fst p = vc1 \/ fst p = vc2
  | _ => False
  end.
Proof.
  induction n; intros; destruct vs1; clarify; destruct vs2; clarify.
  destruct c; clarify; exploit IHn; eauto.
Qed.

Lemma in_mops_max_vcn: forall n c vc1 vc2 vs1 vs2 t
   (Hin: In c (mops_max_vc vc1 vc2 vs1 vs2 t n)),
  match c with 
  | Write tc (a,b) _ => a = vc2 /\ b < n
  | Read tc (a,b) _  => (a = vc1 \/ a = vc2) /\ b < n
  | _ => False
  end.
Proof.
  induction n; intros; destruct vs1; clarify; destruct vs2; clarify.
  destruct c; clarify; exploit IHn; eauto; destruct x; clarify.
Qed.

Check mops_max_vc_con_cc.
Lemma mops_inc_vc'_con : forall m ops u t v
  (Hu: u < zt) (Ht: t < zt) (Hprog: Forall prog_op ops)
  (Hcan_read: can_read (m++ops) (C'+u,u) v ) (Hcan_write: can_write m (C'+u, u)),
                           consistent (m ++ ops++ mops_inc_vc' (C' + u) v t u).
Proof.
  clarify.
  unfold mops_inc_vc'.
  rewrite split_app, app_assoc. apply can_write_thread. apply can_write_SC; clarify.
  -rewrite app_assoc. apply can_read_thread; auto. 
  -rewrite Forall_app; split; clarify.
   rewrite Forall_forall. intros c Hin. inversion Hin; clarify.
Qed.   
  
(*  
Lemma instrument_sim_safe : forall P P1 P2 G1 G2 t h
  (Hfresh : fresh_tmps P1) (Hlocs : safe_locs P1) (Hdistinct : distinct P2)
  (Ht : Forall (fun e => fst e < zt) P1) 
  (Ht_spawn: Forall (fun p =>  match p with
                                 | (t0,Spawn u li::rest) => u <> t0
                                 | (t0,Wait u ::rest) => u <> t0
                                 | _ => True
                               end) P1)
  (HPsim : state_sim P1 P2) (HGsim : env_sim G1 G2)
  m (Hroot : exec_star (Some (init_state P)) init_env h m (Some P1) G1)
  o c P1' G1' (Hstep : exec P1 G1 t o c (Some P1') G1')
  (Hcon : consistent (m ++ opt_to_list c))
  s (Hs : clocks_sim m s) s' (Hsafe : step_star s (opt_to_list o) s'),
  exists lo lc P2' G2', exec_star (Some P2) G2 lo lc (Some P2') G2' /\
    consistent (m ++ lc) /\ state_sim P1' P2' /\ env_sim G1' G2' /\
    mem_sim c lc.
Proof.
  intros.
  inversion Hs as [ Hs_c (Hs_l,Hs_rw)]; clarify.
  assert (exists lo lc P2' G2', iexec P2 G2 t lo lc P2' G2' /\
    consistent (m ++ lc) /\ mem_sim c lc).
  inversion Hstep; clarify; exploit Forall2_app_inv_l; eauto 2;
  intros (P0' & P3' & HP0 & Hrest & ?);
  inversion Hrest as [|? (?, ?) ? ? ? HP3]; clarify.
  - do 5 eexists; [|split].
    + apply iexec_assign; eauto.
    + auto.
    + unfold mem_sim; repeat split; clarify.
  - admit. (*destruct x as (x, o).
    inversion Hsafe; clarify.
    inversion Hstep0; clarify.
    rewrite <- app_assoc; simpl; do 5 eexists; [|split].
    + apply iexec_load; eauto.
      * clarify.
      * instantiate (1 := map (W x) (rev (interval 0 zt))).
        rewrite map_length, rev_length, interval_length; omega.
      * instantiate (1 := map (C t0) (rev (interval 0 zt))).
        rewrite map_length, rev_length, interval_length; omega.
      * apply vc_le_first_gt; auto.
    + instantiate (1 := v).
      instantiate (1 := C t0 t0).
      
      setoid_rewrite Forall_app in Hlocs; clarify.
      inversion Hlocs2 as [|?? Hi ?]; clarify.
      inversion Hi as [|?? Hx ?]; clarify.
      rewrite Forall_app in Ht; clarify.
      inversion Ht2; clarify.
      rewrite app_comm_cons.
      rewrite split_app.
      simpl.
      rewrite app_comm_cons. rewrite app_comm_cons. 
      rewrite app_assoc. rewrite app_assoc. 
      rewrite <- (app_assoc _ [Read t0 (C'+t0, t0) (C t0 t0)]). 
      exploit acq_con.
      {instantiate (1:=m). eapply consistent_app_SC; eauto. }
      {instantiate (1:=x).  auto. }
      instantiate (1:= t0). intro Hacq_con.
      assert(Hs_acq: clocks_sim (m ++ [Acq t0 (X+x)]) (C,L,R,W)).
      {
         apply clocks_sim_acq; auto.
         eapply consistent_app_SC; eauto.
      }
      
      assert(Hcon0: consistent (m ++
         Acq t0 (X + x)
         :: mops_hb_check (W' + x) (C' + t0) (map (W x) (rev (interval 0 zt)))
              (map (C t0) (rev (interval 0 zt))) zt t0)).
      {
        rewrite split_app.
        apply (mops_hb_check_con Hs_acq); auto.
      }

      rewrite reads_noops_SC.
      do 2 rewrite split_app. Check split_app. Check loc_valid_ops_SC.
      specialize(Hs_rw x Hx2). inversion Hs_rw as [Hs_rw1 Hs_rw2].
      unfold clock_match in Hs_rw1, Hs_rw2. specialize(Hs_rw1 t0). specialize(Hs_rw2 t0).
      assert(Hcon1:  consistent ((m ++
         Acq t0 (X' + x)
         :: mops_hb_check (W' + x) (C' + t0) (map (W x) (rev (interval 0 zt)))
              (map (C t0) (rev (interval 0 zt))) zt t0) ++[Write t0 (R'+x, t0) (C t0 t0)])).
            apply can_write_thread.
            apply can_write_SC;auto.
            clarify.
            { clear; constructor; clarify. }
      rewrite <- (app_assoc m).
      rewrite <- app_assoc.
      rewrite loc_valid_ops1_SC; clarify.
      * split; clarify.
        { rewrite <- app_assoc. simpl. rewrite <-app_assoc. rewrite split_app.
          assert (Hlist_silly : forall (X:Type) (l1 l2 l3 l4: list X), 
               l1++l2++l3++l4=l1++(l2++l3)++l4).
            intros. repeat rewrite app_assoc. auto.
          rewrite Hlist_silly. 
          specialize(Hmetalocs_disjoint t0 x x x x).
            inversion Hmetalocs_disjoint; clarify.
          
          eapply loc_valid_ops_SC; auto.
          -rewrite Forall_app. split; rewrite Forall_forall; clarify.
           +rewrite Forall_forall. intros. intro Heq. clarify. 
            contradiction Hx1. setoid_rewrite Heq. eapply mops_hb_check_meta; eauto.
           +rewrite Forall_forall. intros. intro Heq. inversion H2; clarify. contradiction Hx1.  rewrite H3,H5. unfold meta_loc; clarify. right. right. left. omega.
           
          -rewrite Forall_app; split; auto.
           constructor; clarify.
          -constructor; clarify.
          -split; auto.
           +rewrite app_assoc. rewrite <- split_app. auto.
           +apply can_read_thread. apply can_read_SC; auto.
            *apply can_read_thread' with (t:=t0). auto.
            *constructor; clarify.
            * rewrite Forall_forall; intros. inversion H2; clarify. intro Heq. contradiction Hx1. setoid_rewrite Heq. 
             unfold meta_loc; simpl. repeat right. omega.
        }
        { rewrite <- app_assoc. 
          assert( Hlist_silly: forall (X:Type) (l1 l2 l3: list X) (a:X),
                   l1++a::l2++l3=(l1++[a])++l2++l3).
            intros. rewrite split_app. auto.
          setoid_rewrite Hlist_silly. 
          apply loc_valid_ops_SC.
          -rewrite Forall_forall; intros. rewrite Forall_forall; intros.
           rewrite in_app in H.
           inversion H; clarify. apply in_mops_hb_check in H3. 
           destruct x0; clarify. destruct x0; clarify. 
           inversion H3; clarify. 
           specialize(Hmetalocs_disjoint t x x x x).
           inversion Hmetalocs_disjoint; clarify. intro Heq. inversion Heq; clarify.
           specialize(Hmetalocs_disjoint t0 x x x x).
           inversion Hmetalocs_disjoint; clarify. intro Heq. inversion Heq; clarify.
           specialize(Hmetalocs_disjoint t0 x x x x).
           inversion Hmetalocs_disjoint; clarify. intro Heq. inversion Heq; clarify.
          
          -rewrite Forall_app; split; auto.
           constructor; clarify.
          -constructor; clarify.
          -split; auto.
           +rewrite <- app_assoc in Hcon1. setoid_rewrite Hlist_silly in Hcon1. auto.
           +apply can_release_SC; auto.
            specialize(Hs_x m Hx2). inversion Hs_x; clarify.
        }
        
      * constructor; [|constructor]; auto; intro; contradiction Hx1; clarify.
        unfold meta_loc; clarify. repeat right. omega.
      * constructor; clarify.
      *apply can_read_thread.
       apply can_read_SC.
       
       { specialize(Hs_c t0 H3).
       unfold clock_match in Hs_c. 
       specialize(Hs_c t0). clarify. 
       }

       { auto. }
       { constructor; clarify. }
       { apply Forall_cons.
         -intro Heq.
          specialize(Hmetalocs_disjoint t0 x x x x ).
          inversion Hmetalocs_disjoint; clarify.
         - exploit mops_hb_check_read.
           intro Hread.
           rewrite Forall_forall in Hread. rewrite Forall_forall. intros.
           specialize(Hread x0 ). apply Hread in H. destruct x0; clarify.
       }
      * rewrite Forall_forall. intros. inversion H. clarify. inversion H2.
    + setoid_rewrite Forall_app in Hlocs; clarify. (*mem_sim*)
      inversion Hlocs2 as [|?? Hi ?]; clarify.
      inversion Hi; clarify.
      unfold mem_sim in *. split; clarify; repeat rewrite in_app in *; clarify.
      auto.
      *right; right; right;right; left. auto.
      *destruct (eq_dec c (Read t0 (x, o) v)); clarify.
     contradiction H2.
      rewrite Forall_app in Ht; clarify.
      inversion Ht2; clarify.
      destruct H1. symmetry in H; rewrite H. unfold meta_loc; clarify.
      repeat right. omega.
      destruct H. 
      eapply mops_hb_check_meta; eauto.
      destruct H.  symmetry in H; rewrite H. unfold meta_loc; clarify. left. omega.
      destruct H. symmetry in H; rewrite H. unfold meta_loc; clarify. right. right. left. omega.
      destruct H; clarify. contradiction n. auto.
      unfold meta_loc. clarify. repeat right. omega. *)
  -admit. (*destruct x as (x,o). (* store *)
   inversion Hsafe; clarify.
   inversion Hstep0; clarify.
   exploit store_tmps_fresh.
   { eauto. }
   intro Hfresh_tmps.
   rewrite <- app_assoc; clarify; do 5 eexists; [|split].
   + apply iexec_store; eauto.  (*exec_star*)
     clarify; eauto.
    { instantiate (1 := map (W x) (rev (interval 0 zt))).
      rewrite map_length, rev_length, interval_length; omega. }
    { instantiate (1 := map (C t0) (rev (interval 0 zt))).
      rewrite map_length, rev_length, interval_length; omega. }
    { instantiate (1 := map (R x) (rev (interval 0 zt))).
      rewrite map_length, rev_length, interval_length; omega. }
    { apply vc_le_first_gt; auto. }
    { apply vc_le_first_gt; auto. }
   +instantiate (1 := C t0 t0). (*consistent*)
      setoid_rewrite Forall_app in Hlocs; clarify.
      inversion Hlocs2 as [|?? Hi ?]; clarify.
      inversion Hi as [|?? Hx ?]; clarify.
      rewrite Forall_app in Ht; clarify.
      inversion Ht2; clarify. rewrite app_assoc. 
      assert( forall (X:Type) (a b c d:X), [a;b;c;d]=[a]++[b;c;d]) as Hlist_silly.
        intros. auto.
      assert ( consistent (m++[Acq t0 (X + x)])) as Hcan_acq.
        apply can_arw_SC; specialize(Hs_x m Hx2);
          inversion Hx2; clarify.
      assert(Hs_acq: clocks_sim (m ++ [Acq t0 (X+x)]) (C,L,R,W)).
      {
         apply clocks_sim_acq; auto.
         eapply consistent_app_SC; eauto.
      }
      assert (   consistent
     ((m ++ [Acq t0 (X + x)]) ++
      mops_hb_check (W' + x) (C' + t0) (map (W x) (rev (interval 0 zt)))
        (map (C t0) (rev (interval 0 zt))) zt t0)) as Hcon_checkW.
     {
       apply (mops_hb_check_con Hs_acq); auto.
     }
     assert (consistent ((m++ [Acq t0 (X+x)])++
      mops_hb_check (R' + x) (C' + t0) (map (R x) (rev (interval 0 zt)))
        (map (C t0) (rev (interval 0 zt))) zt t0)) as Hcon_checkR.
      {
        apply (mops_hb_check_conR Hs_acq); auto.
      }
      assert (consistent ((m++ [Acq t0 (X+x)])++
  mops_hb_check (W' + x) (C' + t0) (map (W x) (rev (interval 0 zt)))
        (map (C t0) (rev (interval 0 zt))) zt t0 ++
      mops_hb_check (R' + x) (C' + t0) (map (R x) (rev (interval 0 zt)))
        (map (C t0) (rev (interval 0 zt))) zt t0)) as Hcon_checks.
      {
        setoid_rewrite reads_noops_SC; auto.
        apply mops_hb_check_read.
      }   
      setoid_rewrite Hlist_silly. rewrite split_app. rewrite app_assoc.
      setoid_rewrite reads_noops_SC.
      assert(forall (X:Type) (a b c :X), [a;b;c]=[a;b]++[c]) as Hlist_silly2.
        simpl. auto.
      

      *setoid_rewrite Hlist_silly2.
       apply loc_valid_ops1_SC.
        {
          rewrite Forall_forall. intros x0 Hx0. inversion Hx0; clarify. intro Heq.
          specialize(Hmetalocs_disjoint t0 x x x x). inversion Hmetalocs_disjoint;clarify. simpl. intro Heq. contradiction Hx1. setoid_rewrite Heq.
          unfold meta_loc. simpl. repeat right. omega.
      
         }
        { clarify. }
        { repeat constructor; clarify. }
        { split; clarify.
          -rewrite split_app. repeat rewrite <- app_assoc. rewrite app_assoc. 
           assert (forall (X:Type) (l1 l2 l3 l4 l5:list X), l1++l2++l3++l4++l5=l1++(l2++l3++l4)++l5) as Hlist_silly3.
             intros. repeat rewrite app_assoc. auto.
           setoid_rewrite Hlist_silly3.
           apply loc_valid_ops_SC.
           +rewrite Forall_forall. intros. rewrite Forall_forall. intros x1 Hx1_in. inversion Hx1_in. 
            clarify;repeat rewrite in_app in H;
            destruct H as [?|[?|?]]; clarify; intro Heq.
            contradiction Hx1. setoid_rewrite Heq. eapply mops_hb_check_meta; eauto.
            contradiction Hx1. setoid_rewrite Heq. eapply mops_hb_check_meta; eauto.
            contradiction Hx1. setoid_rewrite Heq. unfold meta_loc; simpl. right. right. right. left. omega.
            inversion H2; clarify.
           + repeat rewrite Forall_app; repeat split; auto.
             constructor; clarify.
           + constructor; clarify.
           +split.
            *{ (*checks& updates to VC's are consistent*)
              repeat rewrite app_assoc.
              apply can_write_thread. apply can_write_SC; auto.
              -apply can_write_SC; auto.
               +apply can_write_SC; auto.
                specialize(Hs_rw x Hx2). inversion Hs_rw; clarify. 
                unfold clock_match in Hs_rw2. specialize(Hs_rw2 t0). clarify. 
                constructor; clarify.
              -rewrite <- app_assoc. eauto.
              }
            *{
              (*can release after acquire*)
              apply can_write_thread.
              apply can_write_SC; auto.

              eapply write_any_SC. eauto.
              constructor; simpl; auto.
              }

          
          -rewrite <- app_assoc. apply loc_valid_ops1_SC.
           +rewrite Forall_forall.  intros x0 Hx0. rewrite in_app in Hx0. clarify.
            intro Heq. symmetry in Heq. destruct Hx0; clarify;
            specialize(Hmetalocs_disjoint t0 x x x x). inversion Hmetalocs_disjoint; clarify. auto.
            apply in_mops_hb_check in H; destruct x0; clarify; inversion H; clarify. 
           apply in_mops_hb_check in H.  destruct x0; clarify; inversion H; clarify.
           +simpl; auto.
           +rewrite Forall_app; auto.
           +split; clarify.
            apply can_release_SC. auto.
            specialize(Hs_x m Hx2). inversion Hs_x; clarify.
      }
      *apply can_read_thread. apply can_read_SC.
       {apply can_read_SC.
        - specialize(Hs_c t0 H3).
          unfold clock_match in Hs_c. 
          specialize(Hs_c t0). clarify.
        -apply can_arw_SC; specialize(Hs_x m Hx2);
          inversion Hx2; clarify.
        -constructor; simpl; auto.
        -rewrite Forall_forall; intros; clarify.
         specialize(Hmetalocs_disjoint t0 x x x x ). inversion Hmetalocs_disjoint; clarify.
         intro Heq. inversion Heq. clarify.
       }
       { auto. }
       { rewrite Forall_app; auto. }
       { rewrite Forall_app. split; rewrite Forall_forall; intros; destruct x0; clarify;
         apply in_mops_hb_check in H; clarify.    
       }
      *rewrite Forall_forall; intros. destruct x0; clarify.

   + setoid_rewrite Forall_app in Hlocs; clarify. (*mem_sim*)
      inversion Hlocs2 as [|?? Hi ?]; clarify.
      inversion Hi; clarify.
      rewrite Forall_app in Ht; clarify.
      inversion Ht2; clarify.
      erewrite eval_sim; [|intros; apply HGsim; intro; clarify].
      unfold mem_sim in *; split; clarify; repeat rewrite in_app in *; clarify.
      * do 5 right;left. auto.
      * left.
        destruct H1 as [? | [? | [? | [?|[?|[?|?]]]]]]; clarify.
        { simpl. contradiction H5.
          unfold meta_loc; clarify. repeat right. omega.
        }
        { contradiction H5.
          eapply mops_hb_check_meta; eauto. }
        { contradiction H5. eapply mops_hb_check_meta; eauto. }
        { contradiction H5.
          unfold meta_loc; clarify.  omega.
        }        
        { contradiction H5.
          unfold meta_loc; clarify. omega.
        }
        { contradiction H5.
          unfold meta_loc; clarify. omega.
        }  *)
 -(*lock*) admit. (*
  inversion Hsafe; clarify.
   inversion Hstep0; clarify.
   do 5 eexists; [|split].
   + apply iexec_lock; eauto.
     { instantiate(1 := map (L m0) (rev (interval 0 zt))). 
       rewrite map_length, rev_length, interval_length; omega. }
     { instantiate(1:= map (C t0) (rev (interval 0 zt))).
       rewrite map_length, rev_length, interval_length.
       omega.  }
     { rewrite Forall_app in Ht. clarify. inversion Ht2; clarify. }
   +(*consistent*)
      setoid_rewrite Forall_app in Hlocs; clarify.
      inversion Hlocs2 as [|?? Hi ?]; clarify.
      inversion Hi as [|?? Hm ?]; clarify.
      rewrite Forall_app in Ht; clarify.
      inversion Ht2; clarify.
      rewrite loc_valid_ops2_SC; clarify.
      * eapply (mops_max_vc_con_lc Hs); eauto.
        eapply consistent_app_SC; eauto.
      * rewrite Forall_forall; intros ?? Heq.
        contradiction Hm1.
        setoid_rewrite <- Heq; eapply mops_max_vc_meta; eauto.
  +(*mem_sim*)
    simpl. 
    setoid_rewrite Forall_app in Hlocs; clarify.
      inversion Hlocs2 as [|?? Hi ?]; clarify.
      inversion Hi; clarify.
      unfold mem_sim in *; split; clarify; repeat rewrite in_app in *; clarify.
      simpl. 
      contradiction H2.
      rewrite Forall_app in Ht; clarify.
      inversion Ht2; clarify.
      eapply mops_max_vc_meta; eauto. *)
 -(*unlock*) admit. (*
   inversion Hsafe; clarify.
   inversion Hstep0; clarify.
   do 5 eexists; [|split].
   +(*iexec*)
    apply iexec_unlock; eauto.
    { rewrite <- split_app. eauto. }

    {
      instantiate(1:= map (C t0) (rev (interval 0 zt))). 
       rewrite map_length, rev_length, interval_length; omega. 
      
    }

   +(*consistent*)
    setoid_rewrite Forall_app in Hlocs; clarify.
    inversion Hlocs2 as [|?? Hi ?]; clarify.
    inversion Hi ; clarify.
    rewrite Forall_app in Ht; clarify.
    inversion Ht2; clarify.
    instantiate (1:=(C t0 t0)).
    unfold mops_inc_vc. clarify.
    assert(m ++
      mops_set_vc (C' + t0) (L' + m0) zt t0
        (map (C t0) (rev (interval 0 zt))) ++
      [Read t0 (C' + t0, t0) (C t0 t0); Write t0 (C' + t0, t0) (C t0 t0 + 1);
      Rel t0 m0] =m ++
      (mops_set_vc (C' + t0) (L' + m0) zt t0
        (map (C t0) (rev (interval 0 zt))) ++
      [Read t0 (C' + t0, t0) (C t0 t0); Write t0 (C' + t0, t0) (C t0 t0 + 1)])++[
      Rel t0 m0]) as Hsilly.
      rewrite <-app_assoc. clarsimp.
    setoid_rewrite Hsilly.
    rewrite loc_valid_ops_SC.
    *split; auto.
     rewrite split_app. rewrite app_assoc.
     apply can_write_thread.
     specialize(Hs_c t0 H2). unfold clock_match in Hs_c. 
     specialize(Hs_c t0).
     apply can_write_SC;clarify.
     rewrite app_assoc. apply can_read_thread. 
     apply can_read_SC; auto.
     { simpl.
       apply (mops_set_vc_con_cl Hs); eauto.
       eapply consistent_app_SC; eauto.
     }
     { rewrite Forall_forall. intros x Hin. apply in_mops_set_vc in Hin.
       destruct x; clarify.
       apply Hmetalocs_disjoint_CL; auto.
     }
     {rewrite Forall_app; split; auto; constructor; simpl; auto. }
    *rewrite Forall_app; split; rewrite Forall_forall; clarify; rewrite Forall_forall; clarify.
     {apply mops_set_vc_meta_cl in H; auto.
      intro Heq. rewrite <- Heq in H. clarify. }
     {destruct H as [Hx | Hx]; clarify; intro Heq; contradiction H21; rewrite Heq; unfold meta_loc; simpl; omega. }
    *rewrite Forall_app; split; auto; constructor; simpl; auto. constructor; simpl; auto.
    *constructor; simpl; auto.
   +(*mem_sim*)
          setoid_rewrite Forall_app in Hlocs; clarify.
     inversion Hlocs2; clarify.
     inversion H1. clarify. rewrite Forall_forall in H1.
     rewrite Forall_app in Ht; clarify. 
     inversion Ht2; clarify.
     unfold mem_sim in *; clarify.
     split; clarify; repeat rewrite in_app in *; simpl in *.
     do 3 right. left. auto.
      left.
     destruct H0 as [? | [? | [? | ?]]]; clarify; contradiction H6.
     *apply (mops_set_vc_meta_cl (map (C t0) (rev (interval 0 zt))) zt c H32 H3). auto.
     *left; simpl; abstract omega.
     *left; simpl; abstract omega.
*)
 -(*spawn*)  
   inversion Hsafe; clarify.
   inversion Hstep0; clarify.
   rewrite <- app_assoc; simpl; do 5 eexists; [|split].
   +apply iexec_spawn; eauto.
    { inversion Hstep.  
      intro Hin. 
      unfold state_sim in HPsim. clarify.
      contradiction Hnew. 
      assert(forall (X Y: Type) l1 l2, Forall2 (fun (x y: X*Y) => fst x =fst y) l1 l2 -> map fst l1 = map fst l2) as Hmap_fst.
      {
        intros A B l1.
        induction l1; clarify.
        -inversion H0; clarify. 
        -destruct l2; clarify.
         +inversion H0; clarify.
         +inversion H0; clarify.
          specialize(IHl1 l2 H6). clarify.
          rewrite IHl1, H4.
          auto.
      }
      assert (forall a b, (fun t1 t2 : tid * prog =>
                             fst t1 = fst t2 /\ snd t2 = instrument (snd t1) (fst t1)) a b -> (fun t1 t2: tid * prog => fst t1 = fst t2) a b) as Htrivial.
      {
        intros ? ? H0. inversion H0; clarify.
      }  
      apply Forall2_impl with (Q:= (fun t1 t2: tid * prog => fst t1 = fst t2)) in HPsim.
      specialize(Hmap_fst _ _ _ _ HPsim).
      clarify.
      setoid_rewrite Hmap_fst. auto. rewrite <- app_assoc. apply Hin.
      intros ? ? H0. inversion H0; clarify.
    }
    { instantiate(1:=map (C t0) (rev (interval 0 zt))).
      rewrite map_length, rev_length, interval_length.
      omega.
    }
    { instantiate(1:=map (C u) (rev (interval 0 zt))).
      rewrite map_length, rev_length, interval_length.
      omega.
    }
   +(*consistent*)
    setoid_rewrite Forall_app in Hlocs; clarify.
    inversion Hlocs2 as [|?? Hi ?]; clarify.
    inversion Hi; clarify.
    rewrite Forall_app in Ht; clarify.
    inversion Ht2; clarify.
    instantiate(1:=C t0 t0).
    unfold mops_inc_vc. clarify.
    rewrite split_app. rewrite app_assoc.
    apply can_write_thread.
    apply can_write_SC.
    *specialize(Hs_c t0 H2). unfold clock_match in Hs_c. 
     specialize(Hs_c t0). clarify.
    *rewrite app_assoc. apply can_read_thread. 
     apply can_read_SC; auto.
     { specialize(Hs_c t0 H2). unfold clock_match in Hs_c.
       specialize(Hs_c t0). clarify.
     }
     { simpl.
       apply (mops_max_vc_con_cc' Hs); eauto.
       rewrite app_nil_r in Hcon. auto.
     }
     { rewrite Forall_forall. intros x Hin. apply in_mops_max_vc' in Hin.
       destruct x; clarify.
       destruct x; clarify.
       intro Heq. inversion Heq; clarify.
       assert(Hnu : n = u).
         rewrite <- minus_plus with (n:=C').
         rewrite <- H1. rewrite minus_plus. auto.
       rewrite Forall_app in Ht_spawn. 
       inversion Ht_spawn; clarify. apply Forall_inv in Ht_spawn2. 
       clarify.
     }
    * rewrite Forall_app; split; auto; constructor; simpl; auto.
   +(*mem_sim*)
     setoid_rewrite Forall_app in Hlocs; clarify.
     inversion Hlocs2; clarify.
     inversion H1. clarify. rewrite Forall_forall in H1.
     rewrite Forall_app in Ht; clarify. 
     inversion Ht2; clarify.
     unfold mem_sim in *; clarify.
     split; clarify; repeat rewrite in_app in *; simpl in *.
     contradiction H6; destruct H0 as [? | [? | ?]]; clarify.
     *apply (mops_max_vc_meta_cc (map (C t0) (rev (interval 0 zt))) (map (C u) (rev (interval 0 zt))) zt c H31 H3). auto.
     *left; simpl; abstract omega.
     *left; simpl; abstract omega. 
 -(*wait*)
   inversion Hsafe; clarify.
   inversion Hstep0; clarify.
   apply in_split in Hdone. inversion Hdone; clarify.

   assert( u < zt ) as Hu.
     rewrite H in Ht. rewrite Forall_app in Ht; clarify.
     inversion Ht2; clarify.
   do 5 eexists; [|split].
   +(*iexec*)
    apply iexec_wait; eauto.
    { 
      unfold state_sim in HPsim.
      rewrite H in HPsim. Check Forall2_app_inv_l.
      apply Forall2_app_inv_l in HPsim.
      inversion HPsim; clarify.
      inversion HPsim21; clarify.
      rewrite HPsim22.
      rewrite HPsim22 in Hdistinct.
      rewrite in_app.
      right.
      destruct y; clarify.
    }
    { instantiate(1 := map (C u) (rev (interval 0 zt))). 
       rewrite map_length, rev_length, interval_length; omega. }
    { instantiate(1:= map (C t0) (rev (interval 0 zt))).
       rewrite map_length, rev_length, interval_length.
       omega.  }
   +(*consistent*)
    setoid_rewrite Forall_app in Hlocs; clarify.
    inversion Hlocs2 as [|?? Hi ?]; clarify.
    inversion Hi ; clarify.
    rewrite Forall_app in Ht; clarify.
    inversion Ht2; clarify.
    unfold clock_match in Hs_c. specialize (Hs_c u Hu u). clarify.
    eapply mops_inc_vc'_con; eauto.
    apply can_read_SC; eauto.
    *eapply (mops_max_vc_con_cc Hs); eauto.
     rewrite <- app_nil_end in Hcon. auto.
    *rewrite Forall_forall. intros c Hin. apply in_mops_max_vc' in Hin. destruct c; clarify.
     destruct x3; clarify.
     intro Heq. inversion Heq; clarify. apply plus_reg_l in H2.
     rewrite Forall_app in Ht_spawn. inversion Ht_spawn; clarify. apply Forall_inv in Ht_spawn2. clarify.
   +(*mem_sim*) 
     
     unfold mem_sim. intros. clarify. split; intros; clarify.
     contradiction H02.
    rewrite Forall_app in Ht; clarify.
    inversion Ht2; clarify.
    rewrite in_app in H01. destruct H01 as [Hin1| Hin2]; clarify.
    *apply (mops_max_vc_meta_cc (map (C u) (rev (interval 0 zt)))
                                (map (C t0) (rev (interval 0 zt)))
                                zt c Hu H2); eauto.
    *inversion Hin2; unfold meta_loc; clarify; omega.
 -(*assert_le*)
   clarify. do 5 eexists.
   +eapply iexec_assert; eauto.
    Check eval_sim.
    unfold fresh_tmps in Hfresh. rewrite Forall_app in Hfresh.
    inversion Hfresh; clarify. rewrite Forall_forall in Hfresh2.
    specialize(Hfresh2 (t0, Assert_le e1 e2 :: rest)). clarify.
    inversion Hfresh2. clarify.
    assert( eval (G2 t0) e1= eval (G1' t0) e1) as Heval_e1.
      symmetry. apply eval_sim. intros. eapply HGsim; eauto; intro Heq;
      clarify.
    assert( eval (G2 t0) e2= eval (G1' t0) e2) as Heval_e2.
      symmetry. apply eval_sim. intros. eapply HGsim; eauto; intro Heq;
      clarify.
    rewrite Heval_e1, Heval_e2. auto.
   +(*consistent & mem_sim*)
    clarify.
    unfold mem_sim. intros. clarify. split; intros; clarify.
 
 -
   clarify; do 5 eexists; [eapply iexec_exec; eauto|];

   exploit sim_step; eauto; clarify.
Qed.
*)
Definition bounded V z := forall t, ~t < z -> V t = 0.

Lemma clock_match_bounded : forall m V x, clock_match m V x -> bounded V zt.
Proof.
  unfold clock_match, bounded; intros.
  specialize (H t); clarify.
Qed.




Lemma bounded_le_dec : forall z V V', bounded V z -> vc_le V V' \/
  exists t, t < z /\ V t > V' t /\ forall t', t < t' -> V t' <= V' t'.
Proof.
  induction z; intros.
  - left; intro; rewrite H; omega.
  - destruct (le_dec (V z) (V' z)).
    specialize (IHz (upd V z 0) V'); use IHz.
    destruct IHz as [IHz | IHz]; [left | right].
    + intro t; unfold upd in IHz; specialize (IHz t); clarify.
    + unfold upd in IHz; destruct IHz as (t & ? & IHz); exists t.
      destruct (eq_dec z t); [exfalso; omega | clarify].
      specialize (IHz2 t'); clarify.
    + repeat intro; specialize (H t); unfold upd; clarify; omega.
    + right; exists z; split; [omega | split; [omega | clarify]].
      specialize (H t'); omega.
Qed.

Lemma first_gt_spec : forall vs1 vs2 v1 v2, first_gt vs1 vs2 = Some (v1, v2)
  <-> v1 > v2 /\
    exists i, nth_error vs1 i = Some v1 /\ nth_error vs2 i = Some v2 /\
    forall j v1' v2', j < i -> nth_error vs1 j = Some v1' ->
      nth_error vs2 j = Some v2' -> v1' <= v2'.
Proof.
  induction vs1; clarify.
  { split; clarsimp. }
  destruct vs2; clarify.
  { split; clarsimp. }
  destruct (a <=? n) eqn: Hle.
  - rewrite leb_le in Hle.
    rewrite IHvs1; split; clarify.
    + exists (S x); clarify.
      destruct j; clarify.
      exploit lt_S_n; eauto.
    + destruct x; clarify; try omega.
      exists x; clarify.
      specialize (H222 (S j)); clarify.
  - assert (~a <= n) by (intro; rewrite <- leb_le in *; clarify).
    split; clarify.
    + split; [omega|].
      exists 0; clarify; omega.
    + destruct x; clarify.
      specialize (H0222 0); clarify.
      exploit H0222; auto; omega.
Qed.

(*
Lemma instrument_sim_race : forall P P1 P2 G1 G2 t h
  (Hfresh : fresh_tmps P1) (Hlocs : safe_locs P1)
  (Ht : Forall (fun e => fst e < zt) P1)  (Hdistinct : distinct P2)
 
  (Ht_spawn: Forall (fun p =>  match p with
                                 | (t0,Spawn u li::rest) => u <> t0
                                 | _ => True
                               end) P1)
  (HPsim : state_sim P1 P2) (HGsim : env_sim G1 G2)
  m (Hroot : exec_star (Some (init_state P)) init_env h m (Some P1) G1)
  o c P1' G1' (Hstep : exec P1 G1 t o c (Some P1') G1')
  (Hcon : consistent (m ++ opt_to_list c)) s (Hs : clocks_sim m s)
  (Hrace : forall s', ~step_star s (opt_to_list o) s'),
  exists lo lc G2', exec_star (Some P2) G2 lo lc None G2'.
Proof.
  intros.
  inversion Hstep; clarify; exploit Forall2_app_inv_l; eauto 2;
    intros (P0' & P3' & HP0 & Hrest & ?);
    inversion Hrest as [|? (?, ?) ? ? ? HP3]; clarify.
  - specialize (Hrace s); contradiction Hrace; apply ss_refl. Check ss_refl.
  - destruct x as (x, o).
    destruct Hs as (HC & HL & HRW).
    generalize (HRW x); intro HRWx.
    setoid_rewrite Forall_app in Hlocs; clarify.
    inversion Hlocs2 as [|?? Hi ?]; clarify.
    inversion Hi; clarify.
    generalize (clock_match_bounded HRWx2); intro Hbound.
    destruct (bounded_le_dec (clock_of s t0) Hbound) as [? | (t & Hgt)].
    { destruct s as (((?, ?), ?), ?); exploit Hrace; [|clarify].
      econstructor; [constructor; auto | apply ss_refl]. }
    { 
      exploit load_handler_race_spec.
      { eauto. }
      { eauto. }
      { instantiate (2 := map (clock_of s t0) (rev (interval 0 zt))).
        rewrite map_length, rev_length, interval_length.
        rewrite <- minus_n_O, plus_0_r; eauto. 
        instantiate (1 := map (write_of s x) (rev (interval 0 zt))).
        rewrite map_length, rev_length, interval_length. omega. }
      { rewrite first_gt_spec.
        destruct Hgt as (Hgt1 & Hgt2 & Hclock); split; [apply Hgt2|].
        repeat rewrite map_rev;
          exists (length (map (write_of s x) (interval 0 zt)) - t - 1).
        split.
        { apply nth_error_rev; erewrite map_nth_error; eauto.
          rewrite nth_error_interval; clarify; omega. }
        split.
        { assert (length (map (write_of s x) (interval 0 zt)) =
                  length (map (clock_of s t0) (interval 0 zt))) as Heq
                                                                  by (repeat rewrite map_length; auto).
          rewrite Heq; apply nth_error_rev; erewrite map_nth_error; eauto.
          rewrite nth_error_interval; clarify; omega. }
        intros ??? Hlt Hj1 Hj2.
        generalize (nth_error_rev' _ _ Hj1), (nth_error_rev' _ _ Hj2);
          intros Hj1' Hj2'.
        rewrite map_length, interval_length in *.
        generalize (nth_error_interval (zt - 0 - j - 1) 0 zt); intro Hnth.
        rewrite <- minus_n_O in *; destruct (lt_dec (zt - j - 1) zt); [|omega].
        rewrite (map_nth_error _ _ _ Hnth) in Hj1';
          rewrite (map_nth_error _ _ _ Hnth) in Hj2'; clarify.
        apply Hclock; omega. 
      }
      rewrite plus_0_r; intro Hload.
      instantiate(1:=t0) in Hload.
      instantiate(1:=G2) in Hload. instantiate(1:=x) in Hload. 
      instantiate(1:= l') in Hload.
      instantiate(1:=[Load a (x, o); Unlock (X' + x)] ++ instrument rest t0) in Hload.
      instantiate(1:=P0') in Hload.
      do 3 eexists.
      rewrite <- app_assoc. unfold load_handler in Hload.
      rewrite map_length, rev_length, interval_length, <- minus_n_O in Hload.
      simpl in Hload. simpl. eapply Hload.
    }
    -(*store*)
     destruct x as (x, o).
     destruct Hs as (HC & HL & HRW).
     generalize (HRW x); intro HRWx.
     setoid_rewrite Forall_app in Hlocs; clarify.
     inversion Hlocs2 as [|?? Hi ?]; clarify.
     inversion Hi; clarify.
     generalize (clock_match_bounded HRWx1); intro HboundR.
     generalize (clock_match_bounded HRWx2); intro HboundW.
     destruct (bounded_le_dec (clock_of s t0) HboundW) as [? | (tW & HgtW)];
     destruct (bounded_le_dec (clock_of s t0) HboundR) as [? | (tR & HgtR)].
     { (*RF*)
       destruct s as (((?, ?), ?), ?); exploit Hrace; [|clarify].
       econstructor; [constructor; auto | apply ss_refl]. }
     { (*WAR*)
      exploit store_handler_race_war_spec.
      { eauto. }
      { eauto. }
      { instantiate (2 := map (clock_of s t0) (rev (interval 0 zt))).
        rewrite map_length, rev_length, interval_length.
        rewrite <- minus_n_O, plus_0_r; eauto. 
        instantiate (1 := map (write_of s x) (rev (interval 0 zt))).
        rewrite map_length, rev_length, interval_length. omega. }
      {   instantiate (1 := map (read_of s x) (rev (interval 0 zt))).
        repeat rewrite map_length, rev_length, interval_length. 
        rewrite <- minus_n_O, plus_0_r; eauto.  }
      { 
        apply vc_le_first_gt; auto.
      }
      {
        rewrite first_gt_spec.
        destruct HgtR as (Hgt1 & Hgt2 & Hclock); split; [apply Hgt2|].
        repeat rewrite map_rev;
          exists (length (map (read_of s x) (interval 0 zt)) - tR - 1).
        split.
        { apply nth_error_rev; erewrite map_nth_error; eauto.
          rewrite nth_error_interval; clarify; omega. }
        split.
        { assert (length (map (read_of s x) (interval 0 zt)) =
                  length (map (clock_of s t0) (interval 0 zt))) as Heq
                                                                  by (repeat rewrite map_length; auto).
          rewrite Heq; apply nth_error_rev; erewrite map_nth_error; eauto.
          rewrite nth_error_interval; clarify; omega. }
        intros ??? Hlt Hj1 Hj2.
        generalize (nth_error_rev' _ _ Hj1), (nth_error_rev' _ _ Hj2);
          intros Hj1' Hj2'.
        rewrite map_length, interval_length in *.
        generalize (nth_error_interval (zt - 0 - j - 1) 0 zt); intro Hnth.
        rewrite <- minus_n_O in *; destruct (lt_dec (zt - j - 1) zt); [|omega].
        rewrite (map_nth_error _ _ _ Hnth) in Hj1';
          rewrite (map_nth_error _ _ _ Hnth) in Hj2'; clarify.
        apply Hclock; omega. 
      }
      rewrite plus_0_r; intro Hstore.
      instantiate(1:=t0) in Hstore.
      instantiate(1:=G2) in Hstore. instantiate(1:=x) in Hstore. 
      instantiate(1:= l') in Hstore.
      instantiate(1:=[Store (x, o) e; Unlock (X' + x)] ++ instrument rest t0) in Hstore.
      instantiate(1:=P0') in Hstore.
      do 3 eexists.
      rewrite <- app_assoc. unfold store_handler in Hstore.
      rewrite map_length, rev_length, interval_length, <- minus_n_O in Hstore.
      simpl in Hstore. simpl. eapply Hstore.
    }
    {(*WAW*)
      exploit store_handler_race_waw_spec.
      { eauto. }
      { eauto. }
      { instantiate (2 := map (clock_of s t0) (rev (interval 0 zt))).
        rewrite map_length, rev_length, interval_length.
        rewrite <- minus_n_O, plus_0_r; eauto. 
        instantiate (1 := map (write_of s x) (rev (interval 0 zt))).
        rewrite map_length, rev_length, interval_length. omega. }
      { rewrite first_gt_spec.
        destruct HgtW as (Hgt1 & Hgt2 & Hclock); split; [apply Hgt2|].
        repeat rewrite map_rev;
          exists (length (map (write_of s x) (interval 0 zt)) - tW - 1).
        split.
        { apply nth_error_rev; erewrite map_nth_error; eauto.
          rewrite nth_error_interval; clarify; omega. }
        split.
        { assert (length (map (write_of s x) (interval 0 zt)) =
                  length (map (clock_of s t0) (interval 0 zt))) as Heq
                                                                  by (repeat rewrite map_length; auto).
          rewrite Heq; apply nth_error_rev; erewrite map_nth_error; eauto.
          rewrite nth_error_interval; clarify; omega. }
        intros ??? Hlt Hj1 Hj2.
        generalize (nth_error_rev' _ _ Hj1), (nth_error_rev' _ _ Hj2);
          intros Hj1' Hj2'.
        rewrite map_length, interval_length in *.
        generalize (nth_error_interval (zt - 0 - j - 1) 0 zt); intro Hnth.
        rewrite <- minus_n_O in *; destruct (lt_dec (zt - j - 1) zt); [|omega].
        rewrite (map_nth_error _ _ _ Hnth) in Hj1';
          rewrite (map_nth_error _ _ _ Hnth) in Hj2'; clarify.
        apply Hclock; omega. 
      }
      rewrite plus_0_r; intro Hstore.
      instantiate(1:=t0) in Hstore.
      instantiate(1:=G2) in Hstore. instantiate(1:=x) in Hstore. 
      instantiate(1:= l') in Hstore.
      instantiate(1:=[Store (x, o) e; Unlock (X' + x)] ++ instrument rest t0) in Hstore.
      instantiate(1:=P0') in Hstore.
      do 3 eexists.
      rewrite <- app_assoc. unfold store_handler in Hstore.
      rewrite map_length, rev_length, interval_length, <- minus_n_O in Hstore.
      simpl in Hstore. simpl. eapply Hstore.
     }
    {(*both WAW&WAR, equilvalent to WAW*)
      exploit store_handler_race_waw_spec.
      { eauto. }
      { eauto. }
      { instantiate (2 := map (clock_of s t0) (rev (interval 0 zt))).
        rewrite map_length, rev_length, interval_length.
        rewrite <- minus_n_O, plus_0_r; eauto. 
        instantiate (1 := map (write_of s x) (rev (interval 0 zt))).
        rewrite map_length, rev_length, interval_length. omega. }
      { rewrite first_gt_spec.
        destruct HgtW as (Hgt1 & Hgt2 & Hclock); split; [apply Hgt2|].
        repeat rewrite map_rev;
          exists (length (map (write_of s x) (interval 0 zt)) - tW - 1).
        split.
        { apply nth_error_rev; erewrite map_nth_error; eauto.
          rewrite nth_error_interval; clarify; omega. }
        split.
        { assert (length (map (write_of s x) (interval 0 zt)) =
                  length (map (clock_of s t0) (interval 0 zt))) as Heq
                                                                  by (repeat rewrite map_length; auto).
          rewrite Heq; apply nth_error_rev; erewrite map_nth_error; eauto.
          rewrite nth_error_interval; clarify; omega. }
        intros ??? Hlt Hj1 Hj2.
        generalize (nth_error_rev' _ _ Hj1), (nth_error_rev' _ _ Hj2);
          intros Hj1' Hj2'.
        rewrite map_length, interval_length in *.
        generalize (nth_error_interval (zt - 0 - j - 1) 0 zt); intro Hnth.
        rewrite <- minus_n_O in *; destruct (lt_dec (zt - j - 1) zt); [|omega].
        rewrite (map_nth_error _ _ _ Hnth) in Hj1';
          rewrite (map_nth_error _ _ _ Hnth) in Hj2'; clarify.
        apply Hclock; omega. 
      }
      rewrite plus_0_r; intro Hstore.
      instantiate(1:=t0) in Hstore.
      instantiate(1:=G2) in Hstore. instantiate(1:=x) in Hstore. 
      instantiate(1:= l') in Hstore.
      instantiate(1:=[Store (x, o) e; Unlock (X' + x)] ++ instrument rest t0) in Hstore.
      instantiate(1:=P0') in Hstore.
      do 3 eexists.
      rewrite <- app_assoc. unfold store_handler in Hstore.
      rewrite map_length, rev_length, interval_length, <- minus_n_O in Hstore.
      simpl in Hstore. simpl. eapply Hstore.
     }
    - destruct s as (((vc, vl), vr), vw); exploit Hrace; [|clarify].
      econstructor; [constructor; auto | apply ss_refl].
    -destruct s as (((vc, vl), vr), vw); exploit Hrace; [|clarify].
      econstructor; [constructor; auto | apply ss_refl].
    -destruct s as (((vc, vl), vr), vw); exploit Hrace; [|clarify].
      econstructor; [constructor; auto | apply ss_refl].
    -destruct s as (((vc, vl), vr), vw); exploit Hrace; [|clarify].
      econstructor; [constructor; auto | apply ss_refl].
    -specialize(Hrace s). contradiction Hrace; apply ss_refl.
Qed.
*)

(* There's no escape from fine-grained interleaving. We can either:
   - use a messy simulation relation with cases for intermediate states; or
   - prove that for any interleaving, there's an equivalent reordering of the
     steps via iexec (true only with sufficient synchronization). *)


Definition add_lock li l := Lock l :: li ++ [Unlock l].

Lemma lock_stuck : forall P P1 P2 t l rest
  (HP : P = P1 ++ (t, Lock l :: rest) :: P2) (Hdistinct : distinct P)
  m (Hlocked : ~can_read m (l, 0) 0) G lo lc P' G'
  (Hexec : exec P G t lo lc P' G'), ~consistent (m ++ opt_to_list lc).
Proof.
  intros; inversion Hexec; clarify; exploit distinct_thread; eauto; clarify.
  unfold can_read, consistent, SC in *; intro Hcon.
  rewrite lower_app, lower_cons in Hlocked, Hcon; clarify.
  contradiction Hlocked.
  rewrite split_app in Hcon; eapply consistent_app; eauto.
Qed.

Definition mods_loc i x :=
  match i with
  | Store y _ => y = x
  | Lock y => x = (y, 0)
  | Unlock y => x = (y, 0)
  | _ => False
  end.

Lemma can_read_step : forall P P1 P2 t i rest x v (Hdistinct : distinct P)
  (HP : P = P1 ++ (t, i :: rest) :: P2) (Hnot_mods : ~mods_loc i x) m
  G o c P' G' (Hstep : exec P G t o c P' G')
  (Hcon : consistent (m ++ opt_to_list c)),
  can_read (m ++ opt_to_list c) x v <-> can_read m x v.
Proof.
  intros.
  inversion Hstep; clarify; exploit distinct_thread; eauto; clarify;
    try (rewrite app_nil_r; reflexivity).
  - unfold can_read; rewrite <- app_assoc; apply read_noop_SC; auto.
  - unfold can_read; rewrite <- app_assoc; simpl.
    rewrite loc_valid_SC; auto; split; clarify.
  - unfold can_read; rewrite <- app_assoc; simpl.
    rewrite loc_valid_SC; auto; split; clarify.
  - unfold can_read; rewrite <- app_assoc; simpl.
    rewrite loc_valid_SC; auto; split; clarify.
Qed.

Lemma exec_other_thread : forall P t li (Hin : In (t, li) P) t' (Ht' : t' <> t)
  G o c P' G' (Hstep : exec P G t' o c (Some P') G'), In (t, li) P'.
Proof.
  intros; inversion Hstep; clarify; rewrite in_app in *; clarify.
Qed.

Fixpoint instr_size i :=
  let instr_list_size := fix f l :=
    match l with
    | [] => 0
    | i :: rest => instr_size i + f rest
    end
  in match i with
  | Spawn _ li => S (instr_list_size li)
  | _ => 1
  end.

Fixpoint instr_list_size l :=
  match l with
  | [] => 0
  | i :: rest => instr_size i + instr_list_size rest
  end.

Fixpoint size (P : state) :=
  match P with
  | [] => 0
  | (_, l) :: rest =>  instr_list_size l + size rest
  end.

Lemma size_app : forall P1 P2, size (P1 ++ P2) = size P1 + size P2.
Proof.
  induction P1; clarify.
  rewrite IHP1; destruct a; omega.
Qed.

Lemma size_decr : forall P G t o c P' G' (Hstep : exec P G t o c (Some P') G'),
  size P' < size P.
Proof.
  intros; inversion Hstep; clarify; repeat rewrite size_app; clarify; try omega.
  rewrite (plus_assoc (instr_list_size rest)),
    (plus_comm (instr_list_size rest)).
  unfold instr_list_size at 1; omega.
Qed.

Lemma size_steps : forall P G o c P' G'
  (Hsteps : exec_star (Some P) G o c (Some P') G'), size P' <= size P.
Proof.
  intros.
  remember (Some P) as S; remember (Some P') as S'; generalize dependent P';
    generalize dependent P; induction Hsteps; clarify.
  destruct P'; [|inversion Hsteps; clarify].
  exploit size_decr; eauto.
  specialize (IHHsteps _ eq_refl _ eq_refl); omega.
Qed.

Lemma iexec_step' : forall P G t lo lc P' G' rd mops
  (Hstep : iexec P G t lo lc P' G') lo' lc' P'' G''
  (Hsteps : iexec_star P' G' lo' lc' P'' G'')
  (Hrd : rd = lo ++ lo') (Hmops : mops = lc ++ lc'),
  iexec_star P G rd mops P'' G''.
Proof.
  clarify; eapply iexec_step; eauto.
Qed.

Lemma step_thread : forall P G t o c P' G'
  (Hstep : exec P G t o c (Some P') G') (Hdistinct : distinct P)
  li (Ht : In (t, li) P),
  exists i li', li = i :: li' /\ In (t, li') P'.
Proof.
  intros.
  exploit in_split; eauto; clarify.
  intros; inversion Hstep; clarify; exploit distinct_thread; eauto; clarify;
    do 3 eexists; eauto; rewrite in_app; clarify.
Qed.

Lemma step_invariant : forall P G lo lc P' G' (I : state -> Prop)
  (Hsteps : exec_star (Some P) G lo lc (Some P') G') (HI : I P')
  t li1 li2 (Ht : In (t, li1 ++ li2) P) (Hdistinct : distinct P)
  (HnotI : forall P n (Hn : n < length li1) (Ht : In (t, skipn n li1 ++ li2) P),
     ~I P),
  exists P'' G'' lo1 lc1 lo2 lc2, exec_star (Some P) G lo1 lc1 (Some P'') G'' /\
    In (t, li2) P'' /\ exec_star (Some P'') G'' lo2 lc2 (Some P') G' /\
    lo = lo1 ++ lo2 /\ lc = lc1 ++ lc2.
Proof.
  intros; destruct li1.
  { exists P, G, [], [], lo, lc; repeat split; clarify; apply exec_refl. }
  remember (Some P) as S; remember (Some P') as S';
    generalize dependent li2; generalize dependent li1; revert i;
    generalize dependent P'; generalize dependent P; induction Hsteps; clarify.
  { specialize (HnotI P' 0); clarify. }
  destruct P'; [|inversion Hsteps; clarify].
  exploit distinct_step; eauto; intro Hdistinct'.
  specialize (IHHsteps _ eq_refl Hdistinct' _ eq_refl); clarify.
  destruct (eq_dec t t0); subst.
  - exploit step_thread; eauto; intros (? & ? & ? & Ht'); clarify.
    destruct li1; clarify.
    + exists s, G', (opt_to_list o), (opt_to_list c), lo, lc; clarify.
      eapply exec_step'; [eauto | apply exec_refl | clarsimp | clarsimp].
    + specialize (IHHsteps _ _ _ Ht'); use IHHsteps.
      destruct IHHsteps as (Pa & Ga & lo1 & lc1 & lo2 & lc2 & ?).
      exists Pa, Ga, (opt_to_list o ++ lo1), (opt_to_list c ++ lc1), lo2, lc2;
        clarsimp.
      eapply exec_step; eauto.
      { apply (HnotI _ (S n)); auto. }
  - exploit exec_other_thread; eauto; intro Hin.
    specialize (IHHsteps _ _ _ Hin HnotI);
      destruct IHHsteps as (Pa & Ga & lo1 & lc1 & lo2 & lc2 & ?).
    exists Pa, Ga, (opt_to_list o ++ lo1), (opt_to_list c ++ lc1), lo2, lc2;
      clarsimp.
    eapply exec_step; eauto.
Qed.

Corollary step_all : forall P G lo lc P' G'
  (Hsteps : exec_star (Some P) G lo lc (Some P') G')
  (Hfinal : final_state (Some P'))
  t li1 li2 (Ht : In (t, li1 ++ li2) P) (Hdistinct : distinct P),
  exists P'' G'' lo1 lc1 lo2 lc2, exec_star (Some P) G lo1 lc1 (Some P'') G'' /\
    In (t, li2) P'' /\ exec_star (Some P'') G'' lo2 lc2 (Some P') G' /\
    lo = lo1 ++ lo2 /\ lc = lc1 ++ lc2.
Proof.
  intros; eapply step_invariant; eauto.
  repeat intro.
  rewrite Forall_forall in H; specialize (H _ Ht0); clarify.
  generalize (skipn_length n li1); intro.
  destruct (skipn n li1) eqn: Hskip; clarify; omega.
Qed.

Inductive exec_star_minus t : option state -> env ->
  list operation -> list conc_op -> option state -> env -> Prop :=
| exec_refl_m P G : exec_star_minus t P G [] [] P G
| exec_step_m P G t' o c P' G' (Hin : t' <> t)
    (Hexec : exec P G t' o c P' G') lo lc P'' G''
    (Hexec' : exec_star_minus t P' G' lo lc P'' G'') :
    exec_star_minus t (Some P) G (opt_to_list o ++ lo) (opt_to_list c ++ lc)
                P'' G''.

Lemma NoDup_id_inj : forall A B l (x y : A * B) (Hids : NoDup (map fst l))
 (Hx : In x l) (Hy : In y l) (Heq : fst x = fst y), x = y.
Proof.
  intros.
  exploit in_split; eauto; clarify.
  rewrite map_app in Hids; clarify.
  generalize (NoDup_remove_2 _ _ _ Hids); rewrite in_app in *; intro H.
  destruct Hx; clarify; contradiction H; repeat rewrite in_map_iff; eauto.
Qed.

Lemma cons_neq : forall A (x : A) l, x :: l <> l.
Proof.
  repeat intro.
  assert (length (x :: l) = length l) by (rewrite H; auto); clarify.
  exploit n_Sn; eauto.
Qed.

Lemma exec_mono : forall P G lo lc P' G' t (Hdistinct : distinct P)
  (Hsteps : exec_star (Some P) G lo lc (Some P') G')
  li (Hin : In (t, li) P) li' (Hin' : In (t, li') P'),
  exists n, li' = skipn n li.
Proof.
  intros ?????????.
  remember (Some P) as S; remember (Some P') as S'; generalize dependent P';
    generalize dependent P; induction Hsteps; clarify.
  - generalize (NoDup_id_inj _ _ _ Hdistinct Hin Hin'); clarify.
    exists 0; auto.
  - destruct P'; [|inversion Hsteps; clarify].
    exploit distinct_step; eauto; intro.
    specialize (IHHsteps s); clarify.
    specialize (IHHsteps _ eq_refl).
    destruct (eq_dec t0 t); clarify.
    + exploit step_thread; eauto; clarify.
      specialize (IHHsteps _ H02 _ Hin'); destruct IHHsteps as [n ?].
      exists (S n); clarify.
    + exploit exec_other_thread; try apply Hexec; eauto.
Qed.

Lemma skip_cons_neq : forall A (x : A) l n, x :: l <> skipn n l.
Proof.
  repeat intro.
  assert (length (x :: l) = length (skipn n l)) by (rewrite H; auto).
  rewrite skipn_length in *; clarify; omega.
Qed.

Lemma exec_maintain : forall P G lo lc P' G' t li (Hdistinct : distinct P)
  (Hin : In (t, li) P)
  (Hsteps : exec_star (Some P) G lo lc (Some P') G') (Hin' : In (t, li) P'),
  exec_star_minus t (Some P) G lo lc (Some P') G'.
Proof.
  intros.
  remember (Some P) as S; remember (Some P') as S'; generalize dependent P';
    generalize dependent P; induction Hsteps; clarify.
  - apply exec_refl_m.
  - destruct P'; [|inversion Hsteps; clarify].
    exploit distinct_step; eauto; intro.
    specialize (IHHsteps s); clarify.
    destruct (eq_dec t0 t); clarify.
    { exploit step_thread; eauto; clarify.
      exploit exec_mono; eauto; intros (n & Hmono).
      exploit skip_cons_neq; eauto; clarify. }
    exploit exec_other_thread; try apply Hexec; eauto; clarify.
    specialize (IHHsteps _ eq_refl); clarify.
    eapply exec_step_m; eauto.
Qed.      

Fixpoint t_steps P G t n lo lc P' G' :=
  match n with
  | 0 => lo = [] /\ lc = [] /\ P' = Some P /\ G' = G
  | S n' => exists o c P1 G1, exec P G t o c P1 G1 /\
      exists lo1 lc1 P2 G2 lo2 lc2, exec_star_minus t P1 G1 lo1 lc1 P2 G2 /\
      match P2 with
      | Some P2 => t_steps P2 G2 t n' lo2 lc2 P' G' /\
          lo = opt_to_list o ++ lo1 ++ lo2 /\ lc = opt_to_list c ++ lc1 ++ lc2
      | None => lo = opt_to_list o ++ lo1 /\ lc = opt_to_list c ++ lc1 /\
          P' = None /\ G' = G2
      end
  end.

Lemma exec_minus_exec : forall t P G lo lc P' G'
  (Hminus : exec_star_minus t P G lo lc P' G'),
  exec_star P G lo lc P' G'.
Proof.
  intros; induction Hminus; clarify;
    [apply exec_refl | eapply exec_step; eauto].
Qed.

Lemma exec_other_threads : forall P t li (Hin : In (t, li) P)
  G o c P' G' (Hsteps : exec_star_minus t (Some P) G o c (Some P') G'),
  In (t, li) P'.
Proof.
  intros.
  remember (Some P) as S; remember (Some P') as S'; generalize dependent P';
    generalize dependent P; induction Hsteps; clarify.
  destruct P'; [|inversion Hsteps; clarify].
  exploit exec_other_thread; eauto.
Qed.

Lemma t_steps_exec : forall t n P G lo lc P' G'
  (Ht_steps : t_steps P G t n lo lc P' G'),
  exec_star (Some P) G lo lc P' G'.
Proof.
  induction n; simpl; intros.
  - clarify; apply exec_refl.
  - destruct Ht_steps as (o & c & P1 & G1 & Htstep & lo1 & lc1 & P2 & G2 & lo2 &
      lc2 & Hminus & Hrest).
    destruct P2; clarify.
    + repeat rewrite app_assoc; eapply exec_star_trans; [|apply IHn; eauto].
      eapply exec_step; eauto.
      eapply exec_minus_exec; eauto.
    + eapply exec_step; eauto.
      eapply exec_minus_exec; eauto.
Qed.

Lemma t_steps_length : forall t n P G lo lc P' G' (Hdistinct : distinct P)
  (Ht_steps : t_steps P G t n lo lc (Some P') G') li1 li2
  (Hin : In (t, li1 ++ li2) P) (Hin' : In (t, li2) P'), n = length li1.
Proof.
  induction n; simpl; intros.
  - clarify.
    generalize (NoDup_id_inj _ _ _ Hdistinct Hin Hin'); clarify.
    destruct li1; clarify.
    assert (length (i :: li1 ++ li2) = length li2) by (rewrite H1; auto).
    simpl in *; rewrite app_length in *; omega.
  - destruct Ht_steps as (o & c & P1 & G1 & Htstep & lo1 & lc1 & P2 & G2 & lo2 &
      lc2 & Hminus & Hrest).
    destruct P2; clarify.
    destruct P1; [|inversion Hminus; clarify].
    exploit distinct_step; eauto; intro Hdistinct1.
    exploit distinct_steps; eauto.
    { eapply exec_minus_exec; eauto. }
    intro Hdistinct'.
    specialize (IHn _ _ _ _ _ _ Hdistinct' Hrest1).
    exploit step_thread; eauto; clarify.
    destruct li1; clarify.
    { exploit exec_mono.
      { apply Hdistinct1. }
      { eapply exec_star_trans; [eapply exec_minus_exec | eapply t_steps_exec];
          eauto. }
      { eauto. }
      { eauto. }
      clarify; exploit skip_cons_neq; eauto; clarify. }
    erewrite IHn; eauto.
    eapply exec_other_threads; eauto.
Qed.

Lemma exec_step_inv_m : forall t P G lo lc P' G'
  (Hsteps : exec_star_minus t P G lo lc (Some P') G') o c P'' G'' t'
  (Hstep : exec P' G' t' o c P'' G'') (Hdiff : t' <> t),
  exec_star_minus t P G (lo ++ opt_to_list o) (lc ++ opt_to_list c) P'' G''.
Proof.
  intros ????????.
  remember (Some P') as S; generalize dependent P'; induction Hsteps; clarify.
  - generalize (exec_step_m Hdiff Hstep (exec_refl_m _ _ _)); clarsimp.
  - specialize (IHHsteps _ eq_refl _ _ _ _ _ Hstep Hdiff).
    repeat rewrite <- app_assoc; eapply exec_step_m; try apply Hexec; eauto.
Qed.

Lemma t_steps_add_t : forall t n P G lo lc P' G' (Hdistinct : distinct P)
  (Ht_steps : t_steps P G t n lo lc (Some P') G')
  o c P'' G'' (Hexec : exec P' G' t o c P'' G''),
  t_steps P G t (S n) (lo ++ opt_to_list o) (lc ++ opt_to_list c) P'' G''.
Proof.
  induction n; simpl; intros.
  - clarify.
    repeat eexists; eauto.
    + apply exec_refl_m.
    + destruct P''; clarsimp.
  - destruct Ht_steps as (o' & c' & P1 & G1 & Htstep & lo1 & lc1 & P2 & G2 & lo2
      & lc2 & Hminus & Hrest).
    do 5 eexists; eauto.
    do 7 eexists; eauto.
    destruct P2; clarify.
    destruct P1; [|inversion Hminus; clarify].
    generalize (distinct_step Hdistinct Htstep); intro.
    exploit distinct_steps; eauto.
    { eapply exec_minus_exec; eauto. }
    intro Hdistinct'.
    specialize (IHn _ _ _ _ _ _ Hdistinct' Hrest1 _ _ _ _ Hexec); clarify.
    split.
    + repeat eexists; eauto.
    + clarsimp.
Qed.

Lemma t_steps_add_other : forall t n P G lo lc P' G' (Hdistinct : distinct P)
  (Ht_steps : t_steps P G t n lo lc (Some P') G')
  t' o c P'' G'' (Hexec : exec P' G' t' o c P'' G'') (Hdiff : t' <> t)
  (Hnz : n <> 0),
  t_steps P G t n (lo ++ opt_to_list o) (lc ++ opt_to_list c) P'' G''.
Proof.
  induction n; [clarify | simpl; intros].
  destruct Ht_steps as (o' & c' & P1 & G1 & Htstep & lo1 & lc1 & P2 & G2 & lo2
    & lc2 & Hminus & Hrest).
  destruct P2; clarify.
  destruct P1; [|inversion Hminus; clarify].
  generalize (distinct_step Hdistinct Htstep); intro.
  exploit distinct_steps; eauto.
  { eapply exec_minus_exec; eauto. }
  intro Hdistinct'.
  specialize (IHn _ _ _ _ _ _ Hdistinct' Hrest1 _ _ _ _ _ Hexec); clarify.
  do 5 eexists; eauto.
  destruct n.
  - clarify; do 7 eexists; [eapply exec_step_inv_m; eauto|].
    destruct P''; clarsimp.
  - do 7 eexists; eauto.
    split; [apply IHn; auto|].
    clarsimp.
Qed.

Lemma t_steps_extend : forall P' G' lo lc P'' G''
  (Hsteps : exec_star (Some P') G' lo lc (Some P'') G'')
  P G t n lo0 lc0 (Hdistinct : distinct P)
  (Ht_steps : t_steps P G t n lo0 lc0 (Some P') G')
  li1 li2 (Hin : In (t, li1 ++ li2) P) (Hlen : length li1 <> 0) (Hn : n <> 0)
  (Hin'' : In (t, li2) P''),
  t_steps P G t (length li1) (lo0 ++ lo) (lc0 ++ lc) (Some P'') G''.
Proof.
  intros ???????.
  remember (Some P') as S; remember (Some P'') as S'; generalize dependent P'';
    generalize dependent P'; induction Hsteps; clarify.
  { clarsimp.
    erewrite <- t_steps_length; eauto. }
  destruct P'; [|inversion Hsteps; clarify].
  specialize (IHHsteps _ eq_refl _ eq_refl).
  destruct (eq_dec t0 t); clarify.
  - exploit t_steps_add_t; eauto; intro Ht_steps'.
    specialize (IHHsteps _ _ _ _ _ _ Hdistinct Ht_steps' _ _ Hin);
      do 2 use IHHsteps.
    repeat rewrite <- app_assoc in *; auto.
  - exploit t_steps_add_other; eauto; intro Ht_steps'.
    specialize (IHHsteps _ _ _ _ _ _ Hdistinct Ht_steps' _ _ Hin);
      do 2 use IHHsteps.
    repeat rewrite <- app_assoc in *; auto.
Qed.

Corollary exec_thread : forall P G t o c P' G' (Hdistinct : distinct P)
  (Hstep : exec P G t o c (Some P') G') lo lc P'' G''
  (Hsteps : exec_star (Some P') G' lo lc (Some P'') G'')
  li1 li2 (Hin : In (t, li1 ++ li2) P) (Hlen : length li1 <> 0)
  (Hin'' : In (t, li2) P''),
  t_steps P G t (length li1) (opt_to_list o ++ lo) (opt_to_list c ++ lc)
    (Some P'') G''.
Proof.
  intros; eapply t_steps_extend with (n := 1); eauto.
  simpl; repeat eexists; eauto.
  - apply exec_refl_m.
  - clarsimp.
Qed.

(*
(* Fundamentally, what does "reordering steps" mean? How can we represent
   the steps so they can be reordered? *)
Definition same_state (P1 P2 : option state) :=
  match (P1, P2) with
  | (Some P1, Some P2) => set_of P1 = set_of P2
  | (None, None) => True
  | _ => False
  end.

Lemma Union_spec : forall A S1 S2 (x : A), Union _ S1 S2 x <-> S1 x \/ S2 x.
Proof.
  split; intro.
  - inversion H; auto.
  - destruct H; [apply Union_introl | apply Union_intror]; auto.
Qed.

Lemma set_of_app : forall A (l1 l2 : list A), set_of (l1 ++ l2) =
  Union _ (set_of l1) (set_of l2).
Proof.
  intros; apply set_ext; intro.
  unfold set_of; rewrite Union_spec, in_app; reflexivity.
Qed.

Lemma same_upd : forall P1 t li P2 P1' P2'
  (Hdistinct : distinct (P1 ++ (t, li) :: P2))
  (Hdistinct' : distinct (P1' ++ (t, li) :: P2'))
  (Hsame : same_state (Some (P1 ++ (t, li) :: P2))
                      (Some (P1' ++ (t, li) :: P2'))) li',
  same_state (Some (P1 ++ (t, li') :: P2)) (Some (P1' ++ (t, li') :: P2')).
Proof.
  unfold same_state; clarify.
  assert (distinct (P1 ++ (t, li') :: P2)) as Hdistinct1.
  { unfold distinct in *; rewrite map_app, NoDup_app in *; clarify. }
  assert (distinct (P1' ++ (t, li') :: P2')) as Hdistinct1'.
  { unfold distinct in *; rewrite map_app, NoDup_app in *; clarify. }
  apply set_ext; intro.
  repeat rewrite set_of_app in *; repeat rewrite Union_spec; split; clarify.
  - destruct H; clarify.
    + assert (Union _ (set_of P1) (set_of ((t, li) :: P2)) e)
        by (rewrite Union_spec; auto).
      rewrite Hsame, Union_spec in *; clarify.
      generalize (NoDup_id_inj _ (t, li) (t, li') Hdistinct1);
        setoid_rewrite in_app; clarify.
    + assert (Union _ (set_of P1) (set_of ((t, li) :: P2)) e)
        by (rewrite Union_spec; clarify).
      rewrite Hsame, Union_spec in *; clarify.
      generalize (NoDup_id_inj _ (t, li) (t, li') Hdistinct1);
        setoid_rewrite in_app; clarify.
  - destruct H; clarify.
    + assert (Union _ (set_of P1') (set_of ((t, li) :: P2')) e)
        by (rewrite Union_spec; auto).
      rewrite <- Hsame, Union_spec in *; clarify.
      generalize (NoDup_id_inj _ (t, li) (t, li') Hdistinct1');
        setoid_rewrite in_app; clarify.
    + assert (Union _ (set_of P1') (set_of ((t, li) :: P2')) e)
        by (rewrite Union_spec; clarify).
      rewrite <- Hsame, Union_spec in *; clarify.
      generalize (NoDup_id_inj _ (t, li) (t, li') Hdistinct1');
        setoid_rewrite in_app; clarify.
Qed.    

Lemma same_upd2 : forall P1 t li P2 P1' P2'
  (Hdistinct : distinct (P1 ++ (t, li) :: P2))
  (Hdistinct' : distinct (P1' ++ (t, li) :: P2'))
  (Hsame : same_state (Some (P1 ++ (t, li) :: P2))
                      (Some (P1' ++ (t, li) :: P2'))) t2 li' li2',
  same_state (Some (P1 ++ (t, li') :: (t2, li2') :: P2))
             (Some (P1' ++ (t, li') :: (t2, li2') :: P2')).
Proof.
  unfold same_state; clarify.
  assert (distinct (P1 ++ (t, li') :: P2)) as Hdistinct1.
  { unfold distinct in *; rewrite map_app, NoDup_app in *; clarify. }
  assert (distinct (P1' ++ (t, li') :: P2')) as Hdistinct1'.
  { unfold distinct in *; rewrite map_app, NoDup_app in *; clarify. }
  apply set_ext; intro.
  repeat rewrite set_of_app in *; repeat rewrite Union_spec; split; clarify.
  - destruct H; clarify.
    + assert (Union _ (set_of P1) (set_of ((t, li) :: P2)) e)
        by (rewrite Union_spec; auto).
      rewrite Hsame, Union_spec in *; clarify.
      generalize (NoDup_id_inj _ (t, li) (t, li') Hdistinct1);
        setoid_rewrite in_app; clarify.
    + assert (Union _ (set_of P1) (set_of ((t, li) :: P2)) e)
        by (rewrite Union_spec; clarify).
      rewrite Hsame, Union_spec in *; clarify.
      generalize (NoDup_id_inj _ (t, li) (t, li') Hdistinct1);
        setoid_rewrite in_app; clarify.
  - destruct H; clarify.
    + assert (Union _ (set_of P1') (set_of ((t, li) :: P2')) e)
        by (rewrite Union_spec; auto).
      rewrite <- Hsame, Union_spec in *; clarify.
      generalize (NoDup_id_inj _ (t, li) (t, li') Hdistinct1');
        setoid_rewrite in_app; clarify.
    + assert (Union _ (set_of P1') (set_of ((t, li) :: P2')) e)
        by (rewrite Union_spec; clarify).
      rewrite <- Hsame, Union_spec in *; clarify.
      generalize (NoDup_id_inj _ (t, li) (t, li') Hdistinct1');
        setoid_rewrite in_app; clarify.
Qed.    

Lemma exec_same : forall t P G o c P' G'
  (Hexec : exec P G t o c P' G') P2 (Hsame : same_state (Some P) (Some P2))
  (Hdistinct : distinct P) (Hdistinct2 : distinct P2),
  exists P2', exec P2 G t o c P2' G' /\ same_state P' P2'.
Proof.
  unfold same_state; intros; inversion Hexec; clarify.
  - assert (set_of P2 (t, Assign a e :: rest)) as Hin.
    { rewrite <- Hsame; setoid_rewrite in_app; clarify. }
    generalize (in_split _ _ Hin); clarify.
    eexists; split.
    + apply exec_assign; eauto.
    + eapply same_upd; eauto.
  - assert (set_of P2 (t, Load a x :: rest)) as Hin.
    { rewrite <- Hsame; setoid_rewrite in_app; clarify. }
    generalize (in_split _ _ Hin); clarify.
    eexists; split.
    + apply exec_load; eauto.
    + eapply same_upd; eauto.
  - assert (set_of P2 (t, Store x e :: rest)) as Hin.
    { rewrite <- Hsame; setoid_rewrite in_app; clarify. }
    generalize (in_split _ _ Hin); clarify.
    eexists; split.
    + apply exec_store; eauto.
    + eapply same_upd; eauto.
  - assert (set_of P2 (t, Lock m :: rest)) as Hin.
    { rewrite <- Hsame; setoid_rewrite in_app; clarify. }
    generalize (in_split _ _ Hin); clarify.
    eexists; split.
    + apply exec_lock; eauto.
    + eapply same_upd; eauto.
  - assert (set_of P2 (t, Unlock m :: rest)) as Hin.
    { rewrite <- Hsame; setoid_rewrite in_app; clarify. }
    generalize (in_split _ _ Hin); clarify.
    eexists; split.
    + apply exec_unlock; eauto.
    + eapply same_upd; eauto.
  - assert (set_of P2 (t, Spawn u li :: rest)) as Hin.
    { rewrite <- Hsame; setoid_rewrite in_app; clarify. }
    generalize (in_split _ _ Hin); clarify.
    eexists; split.
    + apply exec_spawn; eauto.
      intro Hin'; contradiction Hnew.
      rewrite in_map_iff in *; destruct Hin' as (e & ? & Hin'); clarify.
      assert (set_of (P1 ++ (t, Spawn (fst e) li :: rest) :: P0) e)
        by (rewrite Hsame; auto); eauto.
    + eapply same_upd2; eauto.
  - assert (set_of P2 (t, Wait u :: rest)) as Hin.
    { rewrite <- Hsame; setoid_rewrite in_app; clarify. }
    generalize (in_split _ _ Hin); clarify.
    eexists; split.
    + apply exec_wait; eauto.
      assert (set_of (P1 ++ (t, Wait u :: rest) :: P0) (u, []))
        by auto; rewrite Hsame in *; auto.
    + eapply same_upd; eauto.
  - assert (set_of P2 (t, Assert_le e1 e2 :: rest)) as Hin.
    { rewrite <- Hsame; setoid_rewrite in_app; clarify. }
    generalize (in_split _ _ Hin); clarify.
    eexists; split.
    + eapply exec_assert_pass; eauto.
    + eapply same_upd; eauto.
  - assert (set_of P2 (t, Assert_le e1 e2 :: rest)) as Hin.
    { rewrite <- Hsame; setoid_rewrite in_app; clarify. }
    generalize (in_split _ _ Hin); clarify.
    eexists; split.
    + eapply exec_assert_fail; eauto.
    + clarify.
Qed.

Lemma exec_minus_same : forall t P G lo lc P' G' (Hdistinct : distinct P)
  (Hexec : exec_star_minus t (Some P) G lo lc P' G')
  P2 (Hsame : same_state (Some P) (Some P2)) (Hdistinct2 : distinct P2),
  exists P2', exec_star_minus t (Some P2) G lo lc P2' G' /\ same_state P' P2'.
Proof.
  intros ?????????.
  remember (Some P) as S; generalize dependent P; induction Hexec; clarify.
  - exists (Some P2); clarify; apply exec_refl_m.
  - exploit exec_same; eauto; intros (P2' & Hexec2 & ?).
    destruct P'.
    + exploit distinct_step; try (apply Hexec); auto; intro.
      specialize (IHHexec s); clarify.
      destruct P2'; clarify.
      specialize (IHHexec s0); clarify.
      exploit distinct_step; try (apply Hexec2); auto; clarify.
      eexists; split; eauto; eapply exec_step_m; eauto.
    + destruct P2'; clarify.
      inversion Hexec0; clarify.
      exists None; clarify; eapply exec_step_m; eauto.
Qed.*)

(* up *)
Lemma NoDup_filter : forall A f (l : list A) (Hnodup : NoDup l),
  NoDup (filter f l).
Proof.
  induction l; clarify.
  inversion Hnodup; clarify.
  constructor; auto.
  rewrite filter_In; intro; clarify.
Qed.

Inductive exec_star_t t : option state -> env ->
  list operation -> list conc_op -> option state -> env -> Prop :=
| exec_refl_t P G : exec_star_t t P G [] [] P G
| exec_step_t P G o c P' G' (Hexec : exec P G t o c P' G') lo lc P'' G''
    (Hexec' : exec_star_t t P' G' lo lc P'' G'') :
    exec_star_t t (Some P) G (opt_to_list o ++ lo) (opt_to_list c ++ lc)
                  P'' G''.

(*Lemma t_steps_app : forall t n li li2 P G lo lc P' G'
  (Ht_steps : t_steps P G t (li ++ li') li2 lo lc P' G'),
  exists P'' G'' lo1 lc1 lo2 lc2, t_steps P G t li (li' ++ li2) lo1 lc1 P'' G''
   /\ t_steps P'' G'' t li' li2 lo2 lc2 P' G' /\
   lo = lo1 ++ lo2 /\ lc = lc1 ++ lc2.
Proof.
  induction li; intros.
  - clarify.
    repeat eexists; eauto.
    + apply exec_refl_m.
    + auto.
    + auto.
  - simpl in Ht_steps.
    destruct Ht_steps as (P1 & G1 & lo1 & lc1 & o & c & P2 & G2 & lo2 & lc2 &
      Hnott & HP1 & Htstep & Hrest); clarify.
    specialize (IHli _ _ _ _ _ _ _ Hrest1);
      destruct IHli as (P'' & G'' & lo1' & lc1' & lo2' & lc2' & Ht1 & Ht2 & ?);
      clarify.
    do 6 eexists; split; [|split; try apply Ht2].
    + do 10 eexists; split; eauto.
      split; [clarsimp | eauto].
    + clarsimp.
Qed.

Corollary t_steps_snoc : forall li i li2 P G t lo lc P' G'
  (Ht_steps : t_steps P G t (li ++ [i]) li2 lo lc P' G'),
  exists lo1 lc1 P1 G1 lo2 lc2 P2 G2 o c P3 G3 lo3 lc3,
   t_steps P G t li (i :: li2) lo1 lc1 P1 G1 /\
   exec_star_minus t P1 G1 lo2 lc2 (Some P2) G2 /\
   In (t, i :: li2) P2 /\ exec P2 G2 t o c P3 G3 /\
   exec_star_minus t P3 G3 lo3 lc3 P' G' /\
   lo = lo1 ++ lo2 ++ opt_to_list o ++ lo3 /\
   lc = lc1 ++ lc2 ++ opt_to_list c ++ lc3.
Proof.
  intros.
  exploit t_steps_app; eauto; clarify.
  repeat eexists; eauto.
Qed.*)

Lemma exec_minus_trans : forall t P G P' S G' G'' e1 m1 e2 m2,
  exec_star_minus t (Some P) G e1 m1 (Some P') G' ->
  exec_star_minus t (Some P') G' e2 m2 S G''->
  exec_star_minus t (Some P) G (e1++e2) (m1++m2) S G''.
Proof.
  intros ??????????? Hexec; induction Hexec; clarify.
  repeat rewrite <- app_assoc; eapply exec_step_m; eauto.
Qed.

Definition instr_result t i G v :=
  match i with
  | Assign a e => Some (None, None, None, @upd local _ _ G a (eval G e),
      fun (P : state) => True)
  | Load a x => Some (None, Some (rd t (fst x)), Some (Read t x v), (upd G a v),
      fun P => True)
  | Store x e => Some (None, Some (wr t (fst x)), Some (Write t x (eval G e)),
      G, fun P => True)
  | Lock m => Some (None, Some (acq t m), Some (Acq t m), G, fun P => True)
  | Unlock m => Some (None, Some (rel t m), Some (Rel t m), G, fun P => True)
  | Spawn u li => Some (Some (u, li), Some (fork t u), None, G,
      fun P => ~In u (map fst P))
  | Wait u => Some (None, Some (join t u), None, G, fun P => In (u, []) P)
  | Assert_le e1 e2 => if le_dec (eval G e1) (eval G e2) then
      Some (None, None, None, G, fun P => True) else None
  end.

Lemma upd_triv1 : forall (G : env) t, upd G t (G t) = G.
Proof.
  intros; extensionality x; apply VectorClocks.upd_triv.
Qed.

Lemma exec_result : forall P G t o c P' G'
  (Hexec : exec P G t o c P' G'),
  exists P1 i li P2 v, P = P1 ++ (t, i :: li) :: P2 /\
    match instr_result t i (G t) v with
    | Some (th, o1, c1, G1, f) => G' = upd G t G1 /\ o1 = o /\ c1 = c /\
        P' = Some (P1 ++ (t, li) :: opt_to_list th ++ P2) /\ f P
    | None => G' = G /\ P' = None
    end.
Proof.
  intros; inversion Hexec; clarify; do 4 eexists; try (exists v);
    try (exists 0); repeat eexists; eauto; clarify; rewrite upd_triv1; auto.
Qed.

Lemma result_exec : forall P P1 t i li P2 G v
  (HP : P = P1 ++ (t, i :: li) :: P2),
  match instr_result t i (G t) v with
  | Some (th, o, c, G1, f) => f P -> exec P G t o c
      (Some (P1 ++ (t, li) :: opt_to_list th ++ P2)) (upd G t G1)
  | None => exec P G t None None None G
  end.
Proof.
  destruct i; clarify.
  - apply exec_assign; auto.
  - apply exec_load; auto.
  - rewrite upd_triv1; apply exec_store; auto.
  - rewrite upd_triv1; apply exec_lock; auto.
  - rewrite upd_triv1; apply exec_unlock; auto.
  - rewrite upd_triv1; apply exec_spawn; auto.
  - rewrite upd_triv1; apply exec_wait; auto.
  - destruct (le_dec (eval (G t) e1) (eval (G t) e2)); intros;
      [rewrite upd_triv1; eapply exec_assert_pass | eapply exec_assert_fail];
      eauto.
Qed.

Lemma exec_minus_env : forall t P G lo lc P' G'
  (Hminus : exec_star_minus t P G lo lc P' G'), G' t = G t.
Proof.
  intros; induction Hminus; auto.
  rewrite IHHminus.
  exploit exec_result; eauto; intros (? & i & li & ? & v & ?); clarify.
  destruct (instr_result t' i (G t') v) as [((((?, ?), ?), ?), ?)|]; clarify.
  unfold upd; clarify.
Qed.

Lemma upd_comm : forall (G : env) t t' Gt Gt' (Hdiff : t' <> t),
  upd (upd G t Gt) t' Gt' = upd (upd G t' Gt') t Gt.
Proof.
  intros; extensionality a; unfold upd; clarify.
Qed.

Lemma exec_swap : forall t P G o c P' G' t' o' c' P'' G''
  (Hdiff : t' <> t) (Hdistinct : distinct P)
  (Hstep : exec P G t o c (Some P') G')
  (Hstep' : exec P' G' t' o' c' (Some P'') G'')
  (Hspawn : forall li rest, ~In (t, Spawn t' li :: rest) P)
  (Hwait : forall i rest, In (t, [i]) P -> ~In (t', Wait t :: rest) P)
  (Hjoin : forall u rest rest', In (t, Spawn u [] :: rest) P ->
     ~In (t', Wait u :: rest') P),
  exists P1 G1, exec P G t' o' c' (Some P1) G1 /\
                exec P1 G1 t o c (Some P'') G''.
Proof.
  intros.
  exploit distinct_step; eauto; intro Hdistinct'.
  exploit distinct_step; eauto; intro Hdistinct''.
  exploit exec_result; eauto; intros (P'a & i' & li' & P'b & v' & HP' & ?);
    clarify.
  destruct (instr_result t' i' (G' t') v') as [((((?, ?), ?), ?), ?)|]
    eqn: Hresult'; clarify.
  exploit exec_result; [apply Hstep|]; intros (Pa & i & li & Pb & v & HP & ?);
    clarify.
  destruct (instr_result t i (G t) v) as [((((?, ?), ?), ?), ?)|]
    eqn: Hresult; clarify.
  rewrite VectorClocks.upd_old in Hresult'; auto.
  assert (~In (t', i' :: li') (opt_to_list o1)) as Hout.
  { specialize (Hspawn (i' :: li') li); rewrite in_app in Hspawn; clarify.
    intro; destruct i; clarify. }
  assert (In (t', i' :: li') (Pa ++ (t, i :: li) :: Pb)).
  { assert (In (t', i' :: li') (P'a ++ (t', i' :: li') :: P'b)) as Hin
      by (rewrite in_app; clarify).
    rewrite H2 in Hin; rewrite in_app in *; clarify.
    rewrite in_app in *; destruct Hin; clarify. }
  exploit in_split; eauto; intros (P1a & P1b & HP').
  exploit (result_exec(P := Pa ++ (t, i :: li) :: Pb));
    [apply HP' | setoid_rewrite Hresult'; intro Hstep'1].
  use Hstep'1.
  do 3 eexists; eauto.
  rewrite <- (VectorClocks.upd_old(x := t') _ G n) in Hresult; auto.
  rewrite upd_comm; auto.
  assert (In (t, i :: li) (P1a ++ (t', li') :: opt_to_list o0 ++ P1b)).
  { assert (In (t, i :: li) (Pa ++ (t, i :: li) :: Pb)) as Hin
      by (rewrite in_app; clarify).
    rewrite HP' in Hin; rewrite in_app in *; clarify.
    rewrite in_app; destruct Hin; clarify. }
  exploit in_split; eauto; intros (P1'a & P1'b & HP1').
  exploit result_exec; [apply HP1' | setoid_rewrite Hresult; intro Hstep1].
  assert (~In (t, i :: li) (opt_to_list o0)) as Hout'.
  { intro; destruct i'; clarify.
    contradiction H2222.
    assert (In (t, li) (P'a ++ (t', Spawn t (i :: li) :: li') :: P'b)) as Hin
      by (rewrite H2, in_app; clarify).
    rewrite in_map_iff; setoid_rewrite in_app; rewrite in_app in Hin;
      destruct Hin; clarify.
    - do 2 eexists; [|left; eauto]; auto.
    - do 2 eexists; [|right; right; eauto]; auto. }
  assert (P'a ++ (t', li') :: opt_to_list o0 ++ P'b =
    P1'a ++ (t, li) :: opt_to_list o1 ++ P1'b) as Heq.
  { clear - H2 HP' HP1' Hdiff Hdistinct Hdistinct'' Hout Hout'.
    destruct (le_dec (length P1a) (length P1'a)).
    - exploit app_eq_inv_ge; eauto; intros (l1' & ?); clarify; clear HP1' l.
      destruct l1'; clarify.
      assert (length (opt_to_list o0) <= length l1').
      { destruct o0; clarify.
        destruct l1'; clarify; [|omega].
        contradiction Hout'; auto. }
      exploit app_eq_inv_ge; eauto; clarify.
      exploit NoDup_inj.
      { eauto. }
      { rewrite map_app; apply nth_error_split. }
      { rewrite HP', map_app, nth_error_plus; instantiate (1 := S _); simpl.
        rewrite map_app; apply nth_error_split. }
      rewrite (split_app P1a), app_assoc in HP'; intro.
      exploit app_eq_inv; try apply HP'; clarsimp.
      destruct (le_dec (length P'a) (length P1a)).
      + exploit app_eq_inv_ge; eauto; intros (l' & ?); clarify;
          clear H2 l.
        destruct l'; clarsimp.
        exploit NoDup_inj.
        { eauto. }
        { rewrite map_app; apply nth_error_split. }
        { rewrite map_app, nth_error_plus; instantiate (1 := S _); simpl.
          rewrite map_app; apply nth_error_split. }
        omega.
      + symmetry in H2; exploit app_eq_inv_ge; eauto; [omega |
          intros (l' & ?); clarify; clear H2 n].
        destruct l'; clarsimp.
        exploit NoDup_inj.
        { eauto. }
        { rewrite map_app; apply nth_error_split. }
        { rewrite map_app, nth_error_plus; instantiate (1 := S _); simpl.
          rewrite map_app; apply nth_error_split. }
        omega.
    - symmetry in HP1'; exploit app_eq_inv_ge; eauto; [omega |
        intros (l1' & ?); clarify; clear HP1' n].
      destruct l1'; clarify.
      rewrite <- app_assoc in HP'.
      exploit NoDup_inj.
      { eauto. }
      { rewrite map_app; apply nth_error_split. }
      { rewrite HP', map_app; apply nth_error_split. }
      repeat rewrite map_length; intro; exploit app_eq_inv; eauto; clarify.
      rewrite (split_app P1'a), app_assoc, app_assoc in H2.
      destruct (le_dec (length P'a)
        (length (((P1'a ++ [(t, li)]) ++ opt_to_list o1) ++ l1'))).
      + exploit app_eq_inv_ge; eauto; intros (l' & ?); clarify.
        destruct l'; clarsimp.
        exploit NoDup_inj.
        { eauto. }
        { rewrite map_app; apply nth_error_split. }
        { rewrite map_app, nth_error_plus; instantiate (1 := S _); simpl.
          rewrite app_assoc, map_app; apply nth_error_split. }
        omega.
      + symmetry in H2; exploit app_eq_inv_ge; eauto; [omega |
          intros (l' & ?); clarify; clear H2 n].
        destruct l'; clarsimp.
        exploit NoDup_inj.
        { eauto. }
        { rewrite map_app, nth_error_plus; instantiate (2 := S _); simpl.
          rewrite app_assoc, map_app; apply nth_error_split. }
        { rewrite map_app, nth_error_plus; instantiate (1 := S _); simpl.
          rewrite app_assoc, map_app, nth_error_plus;
            instantiate (1 := S _); simpl.
          rewrite map_app; apply nth_error_split. }
        omega. }
  rewrite Heq; apply Hstep1.
  - destruct i; clarify.
    + intro Hin; contradiction H0.
      rewrite HP'; rewrite map_app, in_app.
      do 2 (rewrite map_app, in_app in Hin; clarify).
      destruct i'; clarify.
      contradiction H2222; rewrite H2, map_app, in_app; clarify.
    + rewrite HP', in_app in *; clarify.
      rewrite in_app; auto.
  - destruct i'; clarify.
    + intro Hin; contradiction H2222.
      rewrite H2; rewrite map_app, in_app in *; clarify.
      rewrite map_app, in_app; auto.
    + rewrite H2, in_app in H2222; rewrite in_app; clarify.
      rewrite in_app in H2222; destruct H2222; clarify.
      * specialize (Hwait i li'); rewrite in_app in Hwait; clarify.
      * destruct i; clarify.
        specialize (Hjoin t0 li li'); rewrite in_app in Hjoin; clarify.
Qed.

Lemma exec_later_t : forall t P' G' lo lc P'' G''
  (Hrest : exec_star_minus t P' G' lo lc (Some P'') G'')
  P G o c (Htstep : exec P G t o c P' G') (Hdistinct : distinct P)
  (Hspawn : forall u li rest, ~In (t, Spawn u li :: rest) P)
  (Hlast : forall i, ~In (t, [i]) P),
  exists P1 G1, exec_star_minus t (Some P) G lo lc (Some P1) G1 /\
    exec P1 G1 t o c (Some P'') G''.
Proof.
  intros ????????.
  remember (Some P'') as S; generalize dependent P'';
    induction Hrest; clarify.
  { do 3 eexists; eauto; apply exec_refl_m. }
  specialize (IHHrest _ eq_refl).
  destruct P'; clarify; [|inversion Hrest; clarify].
  exploit exec_swap; eauto.
  { intros; exploit Hlast; eauto. }
  { intros; exploit Hspawn; eauto. }
  intros (P1 & G1 & Ht' & Ht).
  exploit distinct_step; eauto; intro Hdistinct1.
  specialize (IHHrest _ _ _ _ Ht Hdistinct1).
  assert (exists li, In (t, li) P0) as (li & ?).
  { generalize (exec_result Htstep); clarify.
    eexists; rewrite in_app; clarify. }
  exploit exec_other_thread; eauto; intro.
  use IHHrest.
  use IHHrest.
  clarify; repeat eexists; eauto.
  eapply exec_step_m; eauto.
  - intro Hin1; generalize (NoDup_id_inj _ _ (t, li) Hdistinct1 Hin1); clarify.
    exploit Hlast; eauto.
  - intro Hin1; generalize (NoDup_id_inj _ _ (t, li) Hdistinct1 Hin1); clarify.
    exploit Hspawn; eauto.
Qed.

Lemma exec_sooner_t : forall t P G lo lc P' G'
  (Hrest : exec_star_minus t (Some P) G lo lc (Some P') G')
  P'' G'' o c (Htstep : exec P' G' t o c (Some P'') G'')
  (Hdistinct : distinct P)
  (Hwait : forall u rest, ~In (t, Wait u :: rest) P)
  li (Ht_start : In (t, li) P),
  exists P1 G1, exec P G t o c P1 G1 /\
    exec_star_minus t P1 G1 lo lc (Some P'') G''.
Proof.
  intros ????????.
  remember (Some P) as S; remember (Some P') as S'; generalize dependent P';
    generalize dependent P; induction Hrest; clarify.
  { do 3 eexists; eauto; apply exec_refl_m. }
  destruct P'; clarify; [|inversion Hrest; clarify].
  specialize (IHHrest _ eq_refl _ eq_refl).
  exploit distinct_step; eauto; intro Hdistinct'.
  exploit exec_other_thread; eauto; intro Ht_start'.
  specialize (IHHrest _ _ _ _ Htstep Hdistinct').
  use IHHrest.
  specialize (IHHrest _ Ht_start').
  destruct IHHrest as (P1 & G1 & Htstep' & Hrest').
  destruct P1; clarify; [|inversion Hrest'; clarify].
  assert (t <> t') by auto.
  exploit exec_swap; try (apply Hdistinct); eauto.
  { intros ?? Hspawn.
    generalize (exec_result Hexec); intros (P1 & i' & li' & Hresult); clarify.
    generalize (NoDup_id_inj _ _ (t', i' :: li') Hdistinct Hspawn);
      rewrite in_app; clarify.
    contradiction Hresult22222; rewrite in_map_iff; exists (t, li); auto. }
  clarify; repeat eexists; eauto.
  eapply exec_step_m; eauto.
  - intro Hin'; generalize (NoDup_id_inj _ _ (t, li) Hdistinct' Hin'); clarify.
    exploit Hwait; eauto.
Qed.

Lemma exec_t_exec : forall t P G lo lc P' G'
  (Hsteps : exec_star_t t P G lo lc P' G'),
  exec_star P G lo lc P' G'.
Proof.
  intros; induction Hsteps; clarify;
    [apply exec_refl | eapply exec_step; eauto].
Qed.

Definition protected m x l := forall i c (Hi : nth_error m i = Some c)
  (Hx : loc_of c = x),
    exists j, j < i /\ nth_error m j = Some (Acq (thread_of c) l) /\
      forall k, j < k < i -> nth_error m k <> Some (Rel (thread_of c) l).

(*Lemma loc_comm_sync : forall lc1 lc2 m1 m2 t l
  (Hindep : Forall (fun c => Forall (fun c' => loc_of c' <> loc_of c) lc2) lc1*)


Lemma exec_step_inv_t : forall t P G lo lc P' G'
  (Hsteps : exec_star_t t P G lo lc (Some P') G') o c P'' G''
  (Hstep : exec P' G' t o c P'' G''),
  exec_star_t t P G (lo ++ opt_to_list o) (lc ++ opt_to_list c) P'' G''.
Proof.
  intros ????????.
  remember (Some P') as S; generalize dependent P'; induction Hsteps; clarify.
  - generalize (exec_step_t Hstep (exec_refl_t _ _ _)); clarsimp.
  - specialize (IHHsteps _ eq_refl _ _ _ _ Hstep).
    repeat rewrite <- app_assoc; eapply exec_step_t; eauto.
Qed.

(* up *)
Lemma partition_filter : forall A f (l : list A),
  partition f l = (filter f l, filter (fun x => negb (f x)) l).
Proof.
  induction l; clarsimp.
Qed.

Lemma exec_minus_ops : forall t P G lo lc P' G'
  (Hsteps : exec_star_minus t P G lo lc P' G'),
  Forall (fun c => beq (thread_of c) t = false) lc.
Proof.
  intros; induction Hsteps; clarify.
  rewrite Forall_app; clarify.
  inversion Hexec; constructor; auto; unfold beq; clarify.
Qed.

Lemma t_steps_plus : forall t n1 n2 P G lo lc P' G'
  (Ht_steps : t_steps P G t (n1 + n2) lo lc (Some P') G'),
  exists lo1 lc1 P1 G1 lo2 lc2, t_steps P G t n1 lo1 lc1 (Some P1) G1 /\
    t_steps P1 G1 t n2 lo2 lc2 (Some P') G' /\
    lo = lo1 ++ lo2 /\ lc = lc1 ++ lc2.
Proof.
  induction n1; simpl; intros.
  - repeat eexists; auto.
  - destruct Ht_steps as (o & c & P1 & G1 & Hstep & lo1 & lc1 & P2 & G2 & lo2 & 
      lc2 & Hminus & Hrest).
    destruct P2; clarify.
    specialize (IHn1 _ _ _ _ _ _ _ Hrest1);
      destruct IHn1 as (lo1' & lc1' & P1' & G1' & lo2' & lc2' & Hsteps1 &
      Hsteps2 & ?); clarify.
    exists (opt_to_list o ++ lo1 ++ lo1'), (opt_to_list c ++ lc1 ++ lc1'),
      P1', G1', lo2', lc2'; clarsimp.
    repeat eexists; eauto; clarify.
Qed.

Lemma loc_split : forall t lc m1 m2 m3
  (Hcon : consistent (m1 ++ lc ++ m2 ++ m3))
  lct lcr (Hpart : partition (fun c => beq (thread_of c) t) lc = (lct, lcr))
  (Hindep : Forall (fun c => Forall (fun c' => loc_of c' <> loc_of c) m2 /\
     Forall (fun c' => loc_of c' <> loc_of c) lct) lcr)
  (Hlc : Forall prog_op lc) (Hm2 : Forall prog_op m2),
  consistent (m1 ++ lct ++ m2 ++ lcr ++ m3).
Proof.
  setoid_rewrite partition_filter.
  induction lc using rev_ind; clarify.
  repeat rewrite filter_app in *; clarify.
  rewrite Forall_app in *; clarify.
  inversion Hlc2; clarify.
  destruct (beq (thread_of x) t) eqn: Ht; unfold beq in Ht; clarify.
  - specialize (IHlc m1 (x :: m2) m3); clarsimp.
    apply IHlc; auto.
    rewrite Forall_forall in *; intros ? Hin.
    specialize (Hindep1 _ Hin); rewrite Forall_app in *; clarify.
    inversion Hindep122; clarify.
  - inversion Hindep2; specialize (IHlc m1 m2 (x :: m3)); clarsimp.
    apply IHlc; auto.
    rewrite app_assoc, loc_comm_ops1_SC, <- app_assoc in H; auto.
Qed.

(* up *)
Lemma filter_negb_all : forall A f (l : list A)
  (Hall : Forall (fun x => f x = false) l),
  filter (fun x => negb (f x)) l = l.
Proof.
  intros; rewrite filter_all; auto.
  eapply Forall_impl; eauto 2; unfold negb; clarify.
Qed.

Lemma filter_negb_none : forall A f (l : list A)
  (Hall : Forall (fun x => f x = true) l),
  filter (fun x => negb (f x)) l = [].
Proof.
  intros; rewrite filter_none; auto.
  eapply Forall_impl; eauto 2; unfold negb; clarify.
Qed.

Lemma exec_ops : forall P G t o c P' G' (Hexec : exec P G t o c P' G'),
  Forall (fun x => beq (thread_of x) t = true) (opt_to_list c).
Proof.
  intros; inversion Hexec; constructor; auto; unfold beq; clarify.
Qed.

Lemma prog_step : forall P G t o c P' G' (Hstep : exec P G t o c P' G'),
  Forall prog_op (opt_to_list c).
Proof.
  intros; inversion Hstep; clarify; constructor; simpl; auto.
Qed.

Lemma prog_steps : forall P G lo lc P' G' (Hsteps : exec_star P G lo lc P' G'),
  Forall prog_op lc.
Proof.
  intros; induction Hsteps; clarify.
  rewrite Forall_app; clarify; eapply prog_step; eauto.
Qed.

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
    - clarsimp. }
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
Qed.

Hint Rewrite nth_error_single : util.

Lemma hb_check_no_wait : forall C1 C2 z tmp1 tmp2 j u,
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
Qed.

Lemma component_decr : forall P G o c P' G'
  (Hsteps : exec_star (Some P) G o c (Some P') G') (Hdistinct : distinct P)
  t li (Hin : In (t, li) P) li' (Hin' : In (t, li') P')
  (Hlt : length li' < length li), size P' < size P.
Proof.
  intros.
  inversion Hsteps; clarify.
  - exploit (NoDup_id_inj _ _ _ Hdistinct Hin Hin'); clarify; omega.
  - destruct P'0; [|inversion Hexec'; clarify].
    exploit size_decr; eauto; intro.
    generalize (size_steps Hexec'); omega.
Qed.

Lemma step_segment : forall P G lo lc P' G'
  (Hsteps : exec_star (Some P) G lo lc (Some P') G')
  (Hfinal : final_state (Some P')) (Hdistinct : distinct P)
  t li1 li2 (Ht : In (t, li1 ++ li2) P) (Hli1 : li1 <> []),
  exists P'' G'' lo1 lc1 Pt Gt o c lo2 lc2,
    exec_star (Some P) G lo1 lc1 (Some P'') G'' /\
    exec P'' G'' t o c (Some Pt) Gt /\ In (t, li2) Pt /\
    exec_star (Some Pt) Gt lo2 lc2 (Some P') G' /\
    lo = lo1 ++ opt_to_list o ++ lo2 /\ lc = lc1 ++ opt_to_list c ++ lc2.
Proof.
  intros ???????.
  remember (Some P) as S; remember (Some P') as S'; generalize dependent P';
    generalize dependent P; induction Hsteps; clarify.
  { rewrite Forall_forall in Hfinal; specialize (Hfinal _ Ht); clarify.
    destruct li1; clarify. }
  destruct P'; [|inversion Hsteps; clarify].
  specialize (IHHsteps _ eq_refl _ eq_refl); clarify.
  exploit distinct_step; eauto; clarify.
  destruct (eq_dec t0 t); subst.
  - exploit step_thread; eauto; clarify.
    destruct li1; clarify.
    destruct (nil_dec li1); clarify.
    + repeat eexists; eauto.
      { apply exec_refl. }
      { auto. }
      { auto. }
    + specialize (IHHsteps t li1 li2); clarify.
      repeat eexists; eauto.
      { eapply exec_step; eauto. }
      { rewrite <- app_assoc; auto. }
      { rewrite <- app_assoc; auto. }
  - exploit exec_other_thread; eauto; intro.
    specialize (IHHsteps t0 li1 li2); clarify.
    repeat eexists; eauto.
    { eapply exec_step; eauto. }
    { rewrite <- app_assoc; auto. }
    { rewrite <- app_assoc; auto. }
Qed.

Lemma exec_keep : forall P G lo lc P' G' (Hdistinct : distinct P)
  (Hsteps : exec_star (Some P) G lo lc (Some P') G')
  t li (Hin : In (t, li) P), exists n, In (t, skipn n li) P'.
Proof.
  intros ????????.
  remember (Some P) as S; remember (Some P') as S'; generalize dependent P';
    generalize dependent P; induction Hsteps; clarify.
  { exists 0; auto. }
  destruct P'; [|inversion Hsteps; clarify].
  exploit distinct_step; eauto; intro Hdistinct'.
  specialize (IHHsteps _ Hdistinct' eq_refl _ eq_refl).
  destruct (eq_dec t0 t); subst.
  - exploit step_thread; eauto; intros (? & ? & ? & Hin').
    specialize (IHHsteps _ _ Hin'); destruct IHHsteps as (n & ?); clarify.
    exists (S n); auto.
  - exploit exec_other_thread; eauto.
Qed.

Lemma instrument_single : forall i t i', instrument_instr i t = [i'] ->
  match i with Assign _ _ => True | Assert_le _ _ => True | _ => False end.
Proof.
  destruct i; clarify; try destruct x; destruct zt; clarify.
Qed.

Lemma Forall2_nth : forall A (l1 l2 : list A) P (Hforall : Forall2 P l1 l2)
  i x (Hi : nth_error l1 i = Some x),
  exists x', nth_error l2 i = Some x' /\ P x x'.
Proof.
  induction l1; clarsimp.
  inversion Hforall; clarify.
  destruct i; clarify; eauto.
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

Lemma app_nil_inv : forall A (l1 l2 : list A), l1 ++ l2 = l2 -> l1 = []. 
Proof.
  intros; assert (length (l1 ++ l2) = length l2) by (rewrite H; auto).
  rewrite app_length in *; destruct l1; clarify; omega.
Qed.

Lemma removelast_length : forall A (l : list A) (Hnnil : l <> []),
  length (removelast l) = length l - 1.
Proof.
  induction l; auto.
  intro; simpl.
  destruct (nil_dec l); clarify.
Qed.

Lemma removelast_nth : forall A (l : list A) i x,
  nth_error (removelast l) i = Some x <->
  nth_error l i = Some x /\ i < length l - 1.
Proof.
  intros; destruct (nil_dec l); clarify.
  { split; clarsimp. }
  rewrite (app_removelast_last x n) at 2; rewrite nth_error_app.
  rewrite removelast_length; auto.
  destruct (lt_dec i (length l - 1)); split; clarify.
  exploit nth_error_lt; eauto; rewrite removelast_length; clarify.
Qed.

Lemma beq_negb : forall A (A_eq : EqDec_eq A) B (a : A) (b c : B),
  (if negb (beq a a) then b else c) = c.
Proof.
  unfold negb, beq; clarify.
Qed.

Lemma Forall_locs : forall l1 l2,
  Forall (fun c1 => Forall (fun c2 => loc_of c2 <> loc_of c1) l2) l1 <->
  Forall (fun l => ~In l (map loc_of l2)) (map loc_of l1).
Proof.
  induction l1; clarify.
  { split; clarify. }
  split; intro H; inversion H; clarify; constructor; try rewrite IHl1 in *;
    auto.
  - rewrite Forall_forall in H2; rewrite in_map_iff; intro Hin; clarify.
    specialize (H2 _ Hin2); auto.
  - rewrite Forall_forall; rewrite in_map_iff in H2; eauto.
Qed.

Definition touches_loc i x :=
  match i with
  | Load _ y => y = x
  | Store y _ => y = x
  | Lock y => x = (y, 0)
  | Unlock y => x = (y, 0)
  | _ => False
  end.

Definition wf_lock (P : state) l := Forall (fun e => Forall (fun i =>
  touches_loc i (l, 0) -> i = Lock l \/ i = Unlock l) (snd e)) P.

Variable (is_lock : state -> nat -> bool).
(* This could be provided by an analysis. *)
Hypothesis is_lock_spec : forall P x, if is_lock P x then wf_lock P x else
  Forall (fun e => Forall (fun i => i <> Lock x /\ i <> Unlock x) (snd e)) P.

Definition is_lock' P p := match p with (x, 0) => is_lock P x | _ => false end.

(*Lemma exec_safe_locs : forall P G t o c P' G' (Hstep : exec P G t o c P' G')
  m (Hcon : consistent (m ++ opt_to_list c)) (Hdistinct : distinct P)
  i li (Hin : In (t, i :: li) P) (Hsafe : safe_instr i),
  Forall (fun l => ~meta_loc l /\
          if is_lock' P l then can_read m l 0 \/ can_read m l (S t) else
          (* not currently true *) can_read m (X + fst l, 0) (S t))
    (map loc_of (opt_to_list c)).
Proof.
  intros.
  exploit in_split; eauto; intros (Pa & Pb & ?); subst.
  inversion Hstep; subst; exploit distinct_thread; eauto; clarify;
    constructor; clarify.
  - destruct (is_lock' (Pa ++ (t, Load a x :: li) :: Pb) x) eqn: Hlock.
    { unfold is_lock' in Hlock; destruct x; clarify.
      exploit is_lock_spec; setoid_rewrite Hlock.
      setoid_rewrite Forall_app; intros [_ Hwf].
      inversion Hwf; clarify.
      inversion H1; clarify. }
    admit.
  - admit.
  - destruct (is_lock (Pa ++ (t, Lock m0 :: li) :: Pb) m0) eqn: Hlock.
    rewrite can_arw_SC_iff in Hcon; specialize (Hcon 0).
    left; eapply can_read_thread', consistent_app_SC; eauto.
    { exploit is_lock_spec; setoid_rewrite Hlock.
      rewrite Forall_app; intros [_ Hwf].
      inversion Hwf; clarify.
      inversion H1; clarify. }
  - destruct (is_lock (Pa ++ (t, Unlock m0 :: li) :: Pb) m0) eqn: Hlock.
    rewrite can_arw_SC_iff in Hcon; specialize (Hcon 0).
    right; eapply can_read_thread', consistent_app_SC; eauto.
    { exploit is_lock_spec; setoid_rewrite Hlock.
      rewrite Forall_app; intros [_ Hwf].
      inversion Hwf; clarify.
      inversion H1; clarify. }
Qed.*)

Lemma exec_instr_locs : forall P G t o c P' G' (Hstep : exec P G t o c P' G')
  m (Hcon : consistent (m ++ opt_to_list c)) (Hdistinct : distinct P)
  i li (Hin : In (t, i :: li) P) i' (Hsafe : In i (instrument_instr i' t)),
  Forall (fun l => (forall x, x < zv -> l = (X + x, 0) \/
    (forall o, l = (R + x, o) \/ l = (W + x, o) \/ l = (x, o) /\
       is_lock' P (x, o) = false) ->
       can_read m (X + x, 0) 0 \/ can_read m (X + x, 0) (S t)) /\
    (forall t' o, t' < zt -> l = (C + t', o) -> t' = t) /\
    (forall k, k < zl -> l = (k, 0) -> is_lock P k = true ->
       can_read m (L + k, 0) 0 \/ can_read m (L + k, 0) (S t)))
    (map loc_of (opt_to_list c)).
Proof.
Abort.

(* safe_locs *)
(*Lemma untouched_locs : forall t P G lo lc P' G'
  (Hminus : exec_star_minus t P G lo lc P' G')
  m (Hcon : consistent (m ++ lc)),
  Forall (fun l =>
    (forall x, x < zv -> (l = (X + x, 0) \/ (exists o, l = (R + x, o) \/
       l = (W + x, o) \/ l = (x, o))) -> ~can_read m (X + x, 0) (S t)) /\
    (forall o, l <> (C + t, o)) /\
    (forall k, k < zl -> l = (k, 0) -> ~can_read m (L + k, 0) (S t)))
    (map loc_of lc).
Proof.
  intros ????????; induction Hminus; clarify.
  rewrite app_assoc in Hcon; specialize (IHHminus _ Hcon).
  rewrite map_app, Forall_app; split.
  - *)

(* Do we want a failing iexec as well? *)


Lemma t_steps_length' : forall t P' G' li1 P G lo lc (Hdistinct : distinct P)
  (Ht_steps : t_steps P G t (length li1) lo lc (Some P') G')
  li2 (Hin : In (t, li1 ++ li2) P), In (t, li2) P'.
Proof.
  induction li1; [clarify | simpl; intros].
  destruct Ht_steps as (o & c & P1 & G1 & Htstep & lo1 & lc1 & [P2|] & G2 & lo2 
    & lc2 & Hminus & Hrest); clarify.
  destruct P1; [|inversion Hminus; clarify].
  exploit distinct_step; eauto; intro.
  exploit distinct_steps; eauto.
  { eapply exec_minus_exec; eauto. }
  exploit step_thread; eauto; clarify.
  eapply IHli1; eauto.
  eapply exec_other_threads; eauto.
Qed.
  
Lemma t_steps_hb_check : forall t P' G' C1 C2 z P G lo lc li
  (Hdistinct : distinct P)
  (Hin : In (t, hb_check C1 C2 z tmp1 tmp2 ++ li) P)
  (Hsteps : t_steps P G t (length (hb_check C1 C2 z tmp1 tmp2)) lo lc
     (Some P') G'),
  (exists vs1 vs2, filter (fun c => beq (thread_of c) t) lc =
    mops_hb_check C1 C2 vs1 vs2 z t) /\ forall a, a <> tmp1 -> a <> tmp2 ->
  G' t a = G t a.
Proof.
  induction z; [clarify | intros].
  { exists [], []; auto. }
  unfold hb_check in Hsteps; fold hb_check in Hsteps.
  rewrite app_length in Hsteps; exploit t_steps_plus; eauto.
  intros (los & lcs & P'' & G'' & lor & lcr & Hstep & Hrest & ? & ?); subst.
  clear Hsteps; exploit IHz; try apply Hrest.
  { eapply distinct_steps; eauto.
    eapply t_steps_exec; eauto. }
  { eapply t_steps_length'; eauto.
    simpl in *; eauto. }
  intros ((vs1 & vs2 & Hlcr) & HG).
  rewrite filter_app, Hlcr.
  simpl in Hstep.
  destruct Hstep as (o0 & c0 & P0 & G0 & Hstep0 & lo1 & lc1 & [P1|] & G1 &
    lo2 & lc2 & Hminus0 & Hstep & ?); [|clarify].
  destruct Hstep as (o1 & c1 & P2 & G2 & Hstep1 & lo3 & lc3 & [P3|] & G3 &
    lo4 & lc4 & Hminus1 & Hstep & ?); [|clarify].
  destruct Hstep as (o2 & c2 & P4 & G4 & Hstep2 & lo5 & lc5 & [P5|] & G5 &
    lo6 & lc6 & Hminus2 & Hstep & ?); clarify.
  exploit in_split; eauto; intros (Pa & Pb & ?); subst.
  inversion Hstep0; subst; exploit distinct_thread; eauto 2;
    intros (? & ? & Hi); inversion Hi; subst; clear Hi.
  exploit exec_other_threads; try apply Hminus0.
  { rewrite in_app; clarify. }
  intro; exploit in_split; eauto; intros (P1a & P1b & ?); subst.
  exploit distinct_step; eauto; intro Hdistinct1.
  exploit distinct_steps; eauto.
  { eapply exec_minus_exec; eauto. }
  intro; inversion Hstep1; subst; exploit distinct_thread; eauto 2;
    intros (? & ? & Hi); inversion Hi; subst; clear Hi.
  exploit exec_other_threads; try apply Hminus1.
  { rewrite in_app; clarify. }
  intro; exploit in_split; eauto; intros (P3a & P3b & ?); subst.
  exploit distinct_step; eauto; intro Hdistinct3.
  exploit distinct_steps; eauto.
  { eapply exec_minus_exec; eauto. }
  intro; inversion Hstep2; subst; exploit distinct_thread; eauto 2;
    intros (? & ? & Hi); inversion Hi; subst; clear Hi;
    [|inversion Hminus2; clarify].
  repeat rewrite filter_app; simpl.
  repeat rewrite beq_refl; simpl.
  split.
  - exists (v :: vs1), (v0 :: vs2); simpl.
    generalize (exec_minus_ops Hminus0), (exec_minus_ops Hminus1),
      (exec_minus_ops Hminus2); intros Hall0 Hall1 Hall2.
    rewrite (filter_none _ Hall0), (filter_none _ Hall1),
      (filter_none _ Hall2); simpl.
    assert (v <=? v0 = true) as Hle; [rewrite leb_le | rewrite Hle; auto].
    simpl in Hpass.
    erewrite exec_minus_env in Hpass; eauto.
    unfold upd_env, upd in Hpass; clarify.
    destruct (eq_dec tmp2 tmp1); clarify.
    { contradiction Htmp; auto. }
    erewrite exec_minus_env in Hpass; eauto.
    unfold upd_env, upd in Hpass; clarify.
  - intros; rewrite HG; auto.
    erewrite exec_minus_env; [|eauto].
    erewrite exec_minus_env; [|eauto].
    unfold upd_env, upd; clarify.
    destruct (eq_dec tmp2 a); clarify.
    erewrite exec_minus_env; [|eauto].
    unfold upd_env, upd; clarify.
Qed.  

Lemma t_steps_load : forall P G t lo lc P1 G1 a x o li
  (Hdistinct : distinct P)
  (Hin : In (t, instrument_instr (Load a (x, o)) t ++ li) P)
  (Hsteps : t_steps P G t (length (instrument_instr (Load a (x, o)) t) - 1) lo
                    lc (Some P1) G1) o' c' P2 G2
  (Hend : exec P1 G1 t o' c' (Some P2) G2) (Hin' : In (t, li) P2),
  exists vs1 vs2 vt v,
    filter (fun c => beq (thread_of c) t) (lc ++ opt_to_list c') =
    Acq t (X + x) :: mops_hb_check (W' + x) (C' + t) vs1 vs2 zt t ++
    mops_move (C' + t, t) (R' + x, t) t vt ++ [Read t (x, o) v; Rel t (X' + x)].
Proof.
  intros.
  unfold instrument_instr in Hsteps.
  rewrite app_length in Hsteps; simpl in Hsteps.
  rewrite <- minus_n_O, <- plus_n_Sm in Hsteps; simpl in Hsteps.
  destruct Hsteps as (o0 & c0 & P0 & G0 & Hstep0 & lo1 & lc1 & [P'|] & G' &
    lo2 & lc2 & Hminus0 & Hrest); clarify.
  generalize (in_split _ _ Hin); intros (Pa & Pb & ?); subst.
  inversion Hstep0; subst; exploit distinct_thread; eauto 2;
    intros (? & ? & Hi); inversion Hi; subst.
  exploit exec_other_threads; try apply Hminus0.
  { rewrite in_app; clarify. }
  intro; exploit in_split; eauto; intros (P'a & P'b & ?); subst.
  rewrite app_length, <- plus_assoc in Hrest1; exploit t_steps_plus; eauto.
  intros (lo3 & lc3 & P3 & G3 & lo4 & lc4 & Hcheck & Hrest' & ? & ?); subst.
  exploit distinct_step; eauto; intro Hdistinct1.
  exploit distinct_steps; eauto.
  { eapply exec_minus_exec; eauto. }
  intro; exploit t_steps_length'; try apply Hcheck; auto.
  { rewrite in_app; right; simpl; left.
    do 2 rewrite <- app_assoc; eauto. }
  intro; exploit in_split; eauto; intros (P3a & P3b & ?); subst.
  exploit distinct_steps; eauto.
  { eapply t_steps_exec; eauto. }
  intro; simpl in Hrest'.
  destruct Hrest' as (o1 & c1 & P4 & G4 & Hstep1 & lo5 & lc5 & [P5|] & G5 &
    lo6 & lc6 & Hminus1 & Hrest2 & ? & ?); [subst | clarify].
  destruct Hrest2 as (o2 & c2 & P6 & G6 & Hstep2 & lo7 & lc7 & [P7|] & G7 &
    lo8 & lc8 & Hminus2 & Hrest3 & ? & ?); [subst | clarify].
  destruct Hrest3 as (o3 & c3 & P8 & G8 & Hstep3 & lo9 & lc9 & [P9|] & G9 &
    lo10 & lc10 & Hminus3 & Hrest4 & ? & ?); clarify.
  inversion Hstep1; subst; exploit distinct_thread; eauto 2;
    intros (? & ? & Hi); inversion Hi; subst; clear Hi.
  exploit exec_other_threads; try apply Hminus1.
  { rewrite in_app; clarify. }
  intro; exploit in_split; eauto; intros (P5a & P5b & ?); subst.
  exploit distinct_step; eauto; intro.
  exploit distinct_steps; eauto.
  { eapply exec_minus_exec; eauto. }
  intro; inversion Hstep2; subst; exploit distinct_thread; eauto 2;
    intros (? & ? & Hi); inversion Hi; subst; clear Hi.
  exploit exec_other_threads; try apply Hminus2.
  { rewrite in_app; clarify. }
  intro; exploit in_split; eauto; intros (P7a & P7b & ?); subst.
  exploit distinct_step; eauto; intro.
  exploit distinct_steps; eauto.
  { eapply exec_minus_exec; eauto. }
  intro; inversion Hstep3; subst; exploit distinct_thread; eauto 2;
    intros (? & ? & Hi); inversion Hi; subst; clear Hi.
  exploit exec_other_threads; try apply Hminus3.
  { rewrite in_app; clarify. }
  intro; exploit in_split; eauto; intros (P9a & P9b & ?); subst.
  exploit distinct_step; eauto; intro.
  exploit distinct_steps; eauto.
  { eapply exec_minus_exec; eauto. }
  intro; inversion Hend; subst; exploit distinct_thread; eauto 2;
    intros (? & ? & Hi); inversion Hi; subst; clear Hi.
  repeat rewrite filter_app; simpl.
  repeat rewrite beq_refl.
  exploit t_steps_hb_check; try apply Hcheck; auto.
  { rewrite in_app; right; simpl; left.
    do 2 rewrite <- app_assoc; eauto. }
  intros ((vs1 & vs2 & Hlc3) & HG); exists vs1, vs2, v, v0; rewrite Hlc3.
  generalize (exec_minus_ops Hminus0), (exec_minus_ops Hminus1),
    (exec_minus_ops Hminus2), (exec_minus_ops Hminus3);
    intros Hall0 Hall1 Hall2 Hall3.
  rewrite (filter_none _ Hall0), (filter_none _ Hall1),
    (filter_none _ Hall2), (filter_none _ Hall3); simpl.
  rewrite (exec_minus_env Hminus1), upd_same.
  clear; clarsimp.
Qed.

Typeclasses eauto := 2.

(* up *)
Lemma read_last : forall (m : list mem_op) p v (Hm : seq_con ML m)
  (Hlast : last_op m (Ptr p) (MWrite p v)) v',
  seq_con ML (m ++ [MRead p v']) <-> v' = v.
Proof.
  split; intro; subst.
  - destruct Hlast as (i & ? & ?).
    symmetry; eapply read_last_val; eauto.
    + rewrite inth_nth_error; apply nth_error_split.
    + rewrite itake_firstn, firstn_app, firstn_length, minus_diag, app_nil_r;
        eauto.
    + rewrite inth_nth_error in *; exploit nth_error_lt; eauto;
        rewrite nth_error_app; clarify.
  - induction m using rev_ind.
    + generalize (last_nil Hlast); clarify.
    + generalize (consistent_app _ _ Hm); clarify.
      rewrite <- app_assoc.
      rewrite last_op_app in Hlast; destruct Hlast as [Hlast | [Hlast Hx]].
      * destruct Hlast as (i & ?); destruct i; clarsimp.
        apply read_written; auto.
      * inversion Hx; clarify.
        destruct H2.
        { destruct x; clarify.
          rewrite read_noop_single; auto. }
        { apply loc_valid; auto. }
Qed.

Definition initialized m p :=
  exists v, last_op (lower(MM_base := Base) m) (Ptr p) (MWrite p v).

Lemma can_read_unique : forall m p v v' (Hcon : consistent m)
  (Hinit : initialized m p) (Hv : can_read m p v) (Hv' : can_read m p v'),
  v' = v.
Proof.
  unfold can_read; intros.
  unfold consistent, SC, lower in *.
  rewrite map_app, flatten_app in *; clarify.
  destruct Hinit.
  rewrite read_last in Hv, Hv'; eauto; clarify.
Qed.

Instance ptr_dec : EqDec_eq ptr.
Proof. eq_dec_inst. Qed.

Lemma last_single : forall (a : @mem_op var nat) l a',
  last_op (icons a inil) l a' <->
  a' = a /\ ~independent (block_model.loc_of a) l /\ not_read a = true.
Proof.
  split; clarify.
  - destruct H as (? & Hlast & ?).
    destruct x; clarsimp.
    inversion Hlast; clarify.
  - exists 0; clarify.
    econstructor; simpl; eauto 2; clarify.
    destruct j; clarsimp.
Qed.

Lemma init_step : forall m p a (Hinit : initialized m p) (Hprog : prog_op a),
  initialized (m ++ [a]) p.
Proof.
  unfold initialized; clarify.
  rewrite lower_app, lower_single; destruct a; clarify.
  - exists x; rewrite last_op_app; right; clarify.
  - destruct (eq_dec x0 p).
    + subst; exists v; rewrite last_op_app; left.
      setoid_rewrite last_single; clarify.
    + exists x; rewrite last_op_app; right; clarify.
  - destruct (eq_dec x0 p).
    + subst; exists v'; rewrite last_op_app; left.
      exists 1; clarify.
      econstructor; simpl; eauto.
      destruct j; clarify.
      destruct j; clarsimp.
    + exists x; rewrite last_op_app; right; clarify.
Qed.

Lemma init_steps : forall m p s (Hinit : initialized m p) (Hprog : Forall prog_op s),
  initialized (m ++ s) p.
Proof.
  intros. generalize dependent m. induction s. 
  -intros. rewrite app_nil_r. auto.
  -intros. rewrite split_app. apply IHs.
   +rewrite Forall_forall in *. intros. clarify.
   +apply init_step; auto.
    eapply Forall_inv. eauto.
Qed.


Lemma t_steps_store : forall P G t lo lc P1 G1 x o e li
  (Hdistinct : distinct P)
  (Hfresh1 : expr_fresh tmp1 e) (Hfresh2 : expr_fresh tmp2 e)
  (Hin : In (t, instrument_instr (Store (x, o) e) t ++ li) P)
  (Hsteps : t_steps P G t (length (instrument_instr (Store (x, o) e) t) - 1) lo
                    lc (Some P1) G1) o' c' P2 G2
  (Hend : exec P1 G1 t o' c' (Some P2) G2) (Hin' : In (t, li) P2),
  exists vs1 vs2 vs3 v,
    filter (fun c => beq (thread_of c) t) (lc ++ opt_to_list c') =
    Acq t (X + x) :: mops_hb_check (W' + x) (C' + t) vs1 vs2 zt t ++
    mops_hb_check (R' + x) (C' + t) vs3 vs2 zt t ++
    mops_move (C' + t, t) (W' + x, t) t v ++
    [Write t (x, o) (eval (G t) e); Rel t (X' + x)].
Proof.
  intros.
  unfold instrument_instr in Hsteps.
  rewrite app_length in Hsteps; simpl in Hsteps.
  rewrite <- minus_n_O, <- plus_n_Sm in Hsteps; simpl in Hsteps.
  destruct Hsteps as (o0 & c0 & P0 & G0 & Hstep0 & lo1 & lc1 & [P'|] & G' &
    lo2 & lc2 & Hminus0 & Hrest); clarify.
  generalize (in_split _ _ Hin); intros (Pa & Pb & ?); subst.
  inversion Hstep0; subst; exploit distinct_thread; eauto 2;
    intros (? & ? & Hi); inversion Hi; subst.
  exploit exec_other_threads; try apply Hminus0.
  { rewrite in_app; clarify. }
  intro; exploit in_split; eauto; intros (P'a & P'b & ?); subst.
  rewrite app_length, <- plus_assoc in Hrest1; exploit t_steps_plus; eauto.
  intros (lo3 & lc3 & P3 & G3 & lo4 & lc4 & Hcheck & Hrest' & ? & ?); subst.
  clear Hrest1.
  exploit distinct_step; eauto; intro Hdistinct1.
  exploit distinct_steps; eauto.
  { eapply exec_minus_exec; eauto. }
  intro; exploit t_steps_length'; try apply Hcheck; auto.
  { rewrite in_app; right; simpl; left.
    do 2 rewrite <- app_assoc; eauto. }
  intro; exploit in_split; eauto; intros (P3a & P3b & ?); subst.
  exploit distinct_steps; eauto.
  { eapply t_steps_exec; eauto. }
  intro; rewrite app_length, <- plus_assoc in Hrest'; exploit t_steps_plus;
    eauto; clear Hrest'.
  intros (lo3' & lc3' & P3' & G3' & lo4' & lc4' & Hcheck' & Hrest' & ? & ?);
    subst.
  exploit t_steps_length'; try apply Hcheck'; auto.
  { rewrite in_app; right; simpl; left.
    rewrite <- app_assoc; eauto. }
  intro; exploit in_split; eauto; intros (P3'a & P3'b & ?); subst.
  exploit distinct_steps; eauto.
  { eapply t_steps_exec; eauto. }
  intro; simpl in Hrest'.
  destruct Hrest' as (o1 & c1 & P4 & G4 & Hstep1 & lo5 & lc5 & [P5|] & G5 &
    lo6 & lc6 & Hminus1 & Hrest2 & ? & ?); [subst | clarify].
  destruct Hrest2 as (o2 & c2 & P6 & G6 & Hstep2 & lo7 & lc7 & [P7|] & G7 &
    lo8 & lc8 & Hminus2 & Hrest3 & ? & ?); [subst | clarify].
  destruct Hrest3 as (o3 & c3 & P8 & G8 & Hstep3 & lo9 & lc9 & [P9|] & G9 &
    lo10 & lc10 & Hminus3 & Hrest4 & ? & ?); clarify.
  inversion Hstep1; subst; exploit distinct_thread; eauto 2;
    intros (? & ? & Hi); inversion Hi; subst; clear Hi.
  exploit exec_other_threads; try apply Hminus1.
  { rewrite in_app; clarify. }
  intro; exploit in_split; eauto; intros (P5a & P5b & ?); subst.
  exploit distinct_step; eauto; intro.
  exploit distinct_steps; eauto.
  { eapply exec_minus_exec; eauto. }
  intro; inversion Hstep2; subst; exploit distinct_thread; eauto 2;
    intros (? & ? & Hi); inversion Hi; subst; clear Hi.
  exploit exec_other_threads; try apply Hminus2.
  { rewrite in_app; clarify. }
  intro; exploit in_split; eauto; intros (P7a & P7b & ?); subst.
  exploit distinct_step; eauto; intro.
  exploit distinct_steps; eauto.
  { eapply exec_minus_exec; eauto. }
  intro; inversion Hstep3; subst; exploit distinct_thread; eauto 2;
    intros (? & ? & Hi); inversion Hi; subst; clear Hi.
  exploit exec_other_threads; try apply Hminus3.
  { rewrite in_app; clarify. }
  intro; exploit in_split; eauto; intros (P9a & P9b & ?); subst.
  exploit distinct_step; eauto; intro.
  exploit distinct_steps; eauto.
  { eapply exec_minus_exec; eauto. }
  intro; inversion Hend; subst; exploit distinct_thread; eauto 2;
    intros (? & ? & Hi); inversion Hi; subst; clear Hi.
  repeat rewrite filter_app; simpl.
  repeat rewrite beq_refl.
  exploit t_steps_hb_check; try apply Hcheck; auto.
  { rewrite in_app; right; simpl; left.
    do 2 rewrite <- app_assoc; eauto. }
  intros ((vs1 & vs2 & Hlc3) & HG).
  exploit t_steps_hb_check; try apply Hcheck'; auto.
  { rewrite in_app; right; simpl; left.
    rewrite <- app_assoc; eauto. }
  intros ((vs3 & vs2' & Hlc3') & HG').
  exists vs1, vs2, vs3, v; rewrite Hlc3, Hlc3'.
  generalize (exec_minus_ops Hminus0), (exec_minus_ops Hminus1),
    (exec_minus_ops Hminus2), (exec_minus_ops Hminus3);
    intros Hall0 Hall1 Hall2 Hall3.
  rewrite (filter_none _ Hall0), (filter_none _ Hall1),
    (filter_none _ Hall2), (filter_none _ Hall3); simpl.
  rewrite (exec_minus_env Hminus2).
  rewrite (exec_minus_env Hminus1), upd_same.
  unfold upd_env; rewrite upd_new.
  rewrite eval_sim with (G2 := G0 t).
  assert (vs2' = vs2) as Hvs2; [|rewrite Hvs2; clear; clarsimp].
  - (* We should be able to prove that we can only read (at most) one value
       at a location. *) admit.
  - intros.
    unfold upd; destruct (eq_dec tmp1 v0); clarify.
    destruct (eq_dec tmp2 v0); clarify.
    rewrite HG', HG; auto.
    erewrite exec_minus_env; eauto.
Qed.

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

(*(* up *)
Require Import Ensembles.
Require Import List.

Definition set_of A (l : list A) x := In x l.
Lemma set_ext : forall A (S1 S2 : Ensemble A)
  (Hext : forall e, S1 e <-> S2 e), S1 = S2.
Proof.
  intros; apply Extensionality_Ensembles; split; repeat intro;
    rewrite Hext in *; auto.
Qed.
*)

Lemma t_steps_max_vc : forall t P' G' src tgt z P G lo lc li
  (Hdistinct : distinct P)
  (Hin : In (t, max_vc src tgt z tmp1 tmp2 ++ li) P)
  (Hsteps : t_steps P G t (length (max_vc src tgt z tmp1 tmp2)) lo lc
     (Some P') G'),
  exists vs1 vs2, filter (fun c => beq (thread_of c) t) lc =
    mops_max_vc src tgt vs1 vs2 t z.
Proof.
  induction z; [clarify | intros].
  { exists [], []; auto. }
  unfold max_vc in Hsteps; fold max_vc in Hsteps.
  rewrite app_length in Hsteps; exploit t_steps_plus; eauto.
  intros (los & lcs & P'' & G'' & lor & lcr & Hstep & Hrest & ? & ?); subst.
  clear Hsteps; exploit IHz; try apply Hrest.
  { eapply distinct_steps; eauto.
    eapply t_steps_exec; eauto. }
  { eapply t_steps_length'; eauto.
    simpl in *; eauto. }
  intros (vs1 & vs2 & Hlcr).
  rewrite filter_app, Hlcr.
  simpl in Hstep.
  destruct Hstep as (o0 & c0 & P0 & G0 & Hstep0 & lo1 & lc1 & [P1|] & G1 &
    lo2 & lc2 & Hminus0 & Hstep & ?); [|clarify].
  destruct Hstep as (o1 & c1 & P2 & G2 & Hstep1 & lo3 & lc3 & [P3|] & G3 &
    lo4 & lc4 & Hminus1 & Hstep & ?); [|clarify].
  destruct Hstep as (o2 & c2 & P4 & G4 & Hstep2 & lo5 & lc5 & [P5|] & G5 &
    lo6 & lc6 & Hminus2 & Hstep & ?); [|clarify].
  destruct Hstep as (o3 & c3 & P6 & G6 & Hstep3 & lo7 & lc7 & [P7|] & G7 &
    lo8 & lc8 & Hminus3 & Hstep & ?); clarify.
  exploit in_split; eauto; intros (Pa & Pb & ?); subst.
  inversion Hstep0; subst; exploit distinct_thread; eauto 2;
    intros (? & ? & Hi); inversion Hi; subst; clear Hi.
  exploit exec_other_threads; try apply Hminus0.
  { rewrite in_app; clarify. }
  intro; exploit in_split; eauto; intros (P1a & P1b & ?); subst.
  exploit distinct_step; eauto; intro Hdistinct1.
  exploit distinct_steps; eauto.
  { eapply exec_minus_exec; eauto. }
  intro; inversion Hstep1; subst; exploit distinct_thread; eauto 2;
    intros (? & ? & Hi); inversion Hi; subst; clear Hi.
  exploit exec_other_threads; try apply Hminus1.
  { rewrite in_app; clarify. }
  intro; exploit in_split; eauto; intros (P3a & P3b & ?); subst.
  exploit distinct_step; eauto; intro Hdistinct3.
  exploit distinct_steps; eauto.
  { eapply exec_minus_exec; eauto. }
  intro; inversion Hstep2; subst; exploit distinct_thread; eauto 2;
    intros (? & ? & Hi); inversion Hi; subst; clear Hi.
  exploit exec_other_threads; try apply Hminus2.
  { rewrite in_app; clarify. }
  intro; exploit in_split; eauto; intros (P5a & P5b & ?); subst.
  exploit distinct_step; eauto; intro Hdistinct5.
  exploit distinct_steps; eauto.
  { eapply exec_minus_exec; eauto. }
  intro; inversion Hstep3; subst; exploit distinct_thread; eauto 2;
    intros (? & ? & Hi); inversion Hi; subst; clear Hi.
  repeat rewrite filter_app; simpl.
  repeat rewrite beq_refl; simpl.
  exists (v :: vs1), (v0 :: vs2); simpl.
  generalize (exec_minus_ops Hminus0), (exec_minus_ops Hminus1),
    (exec_minus_ops Hminus2), (exec_minus_ops Hminus3);
    intros Hall0 Hall1 Hall2 Hall3.
  rewrite (filter_none _ Hall0), (filter_none _ Hall1),
    (filter_none _ Hall2), (filter_none _ Hall3); simpl.
  erewrite exec_minus_env; eauto.
  unfold upd_env, upd; clarify.
  rewrite (exec_minus_env Hminus1); unfold upd_env, upd; clarify.
  destruct (eq_dec tmp2 tmp1); clarify.
  { contradiction Htmp; auto. }
  rewrite (exec_minus_env Hminus0); unfold upd_env, upd; clarify.
Qed.  

(*Lemma t_steps_lock : forall P G t lo lc P1 G1 m li
  (Hdistinct : distinct P)
  (Hin : In (t, instrument_instr (Lock m) t ++ li) P)
  (Hsteps : t_steps P G t (length (instrument_instr (Lock m) t) - 1) lo
                    lc (Some P1) G1) o' c' P2 G2
  (Hend : exec P1 G1 t o' c' (Some P2) G2) (Hin' : In (t, li) P2),
  exists vs1 vs2,
    filter (fun c => beq (thread_of c) t) (lc ++ opt_to_list c') =
    Acq t m :: mops_max_vc (L' + m) (C' + t) vs1 vs2 t zt.
Proof.
  intros.
  unfold instrument_instr in Hsteps.
  rewrite app_length in Hsteps; simpl in Hsteps.
  rewrite <- minus_n_O in Hsteps.
  admit. (* This is a bit awkward since the lock is first. *)
Qed.*)

Lemma t_steps_inc_vc : forall t P' G' tgt tmp P G lo lc li
  (Hdistinct : distinct P)
  (Hin : In (t, inc_vc t tgt tmp ++ li) P)
  (Hsteps : t_steps P G t (length (inc_vc t tgt tmp)) lo lc
     (Some P') G'),
  exists v, filter (fun c => beq (thread_of c) t) lc =
    mops_inc_vc tgt v t.
Proof.
  intros; simpl in Hsteps.
  destruct Hsteps as (o0 & c0 & P0 & G0 & Hstep0 & lo1 & lc1 & [P1|] & G1 &
    lo2 & lc2 & Hminus0 & Hstep & ?); [|clarify].
  destruct Hstep as (o1 & c1 & P2 & G2 & Hstep1 & lo3 & lc3 & [P3|] & G3 &
    lo4 & lc4 & Hminus1 & Hstep & ?); [|clarify].
  destruct Hstep as (o2 & c2 & P4 & G4 & Hstep2 & lo5 & lc5 & [P5|] & G5 &
    lo6 & lc6 & Hminus2 & Hstep & ?); clarify.
  exploit in_split; eauto; intros (Pa & Pb & ?); subst.
  inversion Hstep0; subst; exploit distinct_thread; eauto 2;
    intros (? & ? & Hi); inversion Hi; subst; clear Hi.
  exploit exec_other_threads; try apply Hminus0.
  { rewrite in_app; clarify. }
  intro; exploit in_split; eauto; intros (P1a & P1b & ?); subst.
  exploit distinct_step; eauto; intro Hdistinct1.
  exploit distinct_steps; eauto.
  { eapply exec_minus_exec; eauto. }
  intro; inversion Hstep1; subst; exploit distinct_thread; eauto 2;
    intros (? & ? & Hi); inversion Hi; subst; clear Hi.
  exploit exec_other_threads; try apply Hminus1.
  { rewrite in_app; clarify. }
  intro; exploit in_split; eauto; intros (P3a & P3b & ?); subst.
  exploit distinct_step; eauto; intro Hdistinct3.
  exploit distinct_steps; eauto.
  { eapply exec_minus_exec; eauto. }
  intro; inversion Hstep2; subst; exploit distinct_thread; eauto 2;
    intros (? & ? & Hi); inversion Hi; subst; clear Hi.
  repeat rewrite filter_app; simpl.
  repeat rewrite beq_refl; simpl.
  exists v.
  generalize (exec_minus_ops Hminus0), (exec_minus_ops Hminus1),
    (exec_minus_ops Hminus2); intros Hall0 Hall1 Hall2.
  rewrite (filter_none _ Hall0), (filter_none _ Hall1),
    (filter_none _ Hall2); simpl.
  erewrite exec_minus_env; eauto.
  unfold upd_env, upd; clarify.
  rewrite (exec_minus_env Hminus0); unfold upd_env, upd; clarify.
Qed.  


Lemma t_steps_set_vc : forall t P' G' src tgt z tmp P G lo lc li
  (Hdistinct : distinct P)
  (Hin : In (t, set_vc src tgt z tmp ++ li) P)
  (Hsteps : t_steps P G t (length (set_vc src tgt z tmp)) lo lc
     (Some P') G'),
  exists vs, filter (fun c => beq (thread_of c) t) lc =
    mops_set_vc src tgt z t vs.
Proof.
  induction z; [clarify | intros].
  { exists []; auto. }
  unfold set_vc in Hsteps; fold set_vc in Hsteps.
  rewrite app_length in Hsteps; exploit t_steps_plus; eauto.
  intros (los & lcs & P'' & G'' & lor & lcr & Hstep & Hrest & ? & ?); subst.
  clear Hsteps; exploit IHz; try apply Hrest.
  { eapply distinct_steps; eauto.
    eapply t_steps_exec; eauto. }
  { eapply t_steps_length'; eauto.
    simpl in *; eauto. }
  intros (vs & Hlcr).
  rewrite filter_app, Hlcr.
  simpl in Hstep.
  destruct Hstep as (o0 & c0 & P0 & G0 & Hstep0 & lo1 & lc1 & [P1|] & G1 &
    lo2 & lc2 & Hminus0 & Hstep & ?); [|clarify].
  destruct Hstep as (o1 & c1 & P2 & G2 & Hstep1 & lo3 & lc3 & [P3|] & G3 &
    lo4 & lc4 & Hminus1 & Hstep & ?); clarify.
  exploit in_split; eauto; intros (Pa & Pb & ?); subst.
  inversion Hstep0; subst; exploit distinct_thread; eauto 2;
    intros (? & ? & Hi); inversion Hi; subst; clear Hi.
  exploit exec_other_threads; try apply Hminus0.
  { rewrite in_app; clarify. }
  intro; exploit in_split; eauto; intros (P1a & P1b & ?); subst.
  exploit distinct_step; eauto; intro Hdistinct1.
  exploit distinct_steps; eauto.
  { eapply exec_minus_exec; eauto. }
  intro; inversion Hstep1; subst; exploit distinct_thread; eauto 2;
    intros (? & ? & Hi); inversion Hi; subst; clear Hi.
  repeat rewrite filter_app; simpl.
  repeat rewrite beq_refl; simpl.
  exists (v :: vs); simpl.
  generalize (exec_minus_ops Hminus0), (exec_minus_ops Hminus1);
    intros Hall0 Hall1.
  rewrite (filter_none _ Hall0), (filter_none _ Hall1); simpl.
  erewrite exec_minus_env; eauto.
  unfold upd_env, upd; clarify.
Qed.

Lemma t_steps_spawn : forall P G t lo lc P1 G1 m li' li
  (Hdistinct : distinct P)
  (Hin : In (t, instrument_instr (Spawn m li') t ++ li) P)
  (Hsteps : t_steps P G t (length (instrument_instr (Spawn m li') t) - 1) lo
                    lc (Some P1) G1) o' c' P2 G2
  (Hend : exec P1 G1 t o' c' (Some P2) G2) (Hin' : In (t, li) P2),
  exists vs1 vs2 v,
    filter (fun c => beq (thread_of c) t) (lc ++ opt_to_list c') =
    mops_max_vc (C' + t) (C' + m) vs1 vs2 t zt ++
    mops_inc_vc (C' + t) v t .
Proof.
  intros.
  unfold instrument_instr in Hsteps.
  rewrite app_length in Hsteps; simpl in Hsteps.
  rewrite Nat.add_sub in Hsteps; unfold spawn_handler in Hsteps.
  rewrite app_length in Hsteps; exploit t_steps_plus; eauto.
  intros (lo1 & lc1 & P3 & G3 & lo2 & lc2 & Hmax & Hrest & ? & ?); subst.
  exploit t_steps_max_vc; eauto.
  { unfold instrument_instr, spawn_handler in Hin;
      repeat rewrite <- app_assoc in Hin; eauto. }
  intros (vs1 & vs2 & Hlc1); exists vs1, vs2.
  exploit distinct_steps; eauto.
  { eapply t_steps_exec, Hmax; eauto. }
  intro; exploit t_steps_length'; try apply Hmax; auto.
  { unfold instrument_instr, spawn_handler in Hin;
      repeat rewrite <- app_assoc in Hin; eauto. }
  intro; exploit in_split; eauto; intros (P3a & P3b & ?); subst.
  exploit t_steps_inc_vc; eauto; intros (v & Hlc2); exists v.
  repeat rewrite filter_app; rewrite Hlc1, Hlc2.
  exploit t_steps_length'; try apply Hrest; auto.
  { rewrite in_app; clarify. }
  intro; exploit in_split; eauto; intros (P1a & P1b & ?); subst.
  exploit distinct_steps; eauto.
  { eapply t_steps_exec, Hrest; eauto. }
  intro; inversion Hend; subst; exploit distinct_thread; eauto 2;
    intros (? & ? & Hi); inversion Hi; subst; clear Hi.
  rewrite <- app_assoc; clarify. 
Qed.  


Lemma t_steps_unlock : forall P G t lo lc P1 G1 m li
  (Hdistinct : distinct P)
  (Hin : In (t, instrument_instr (Unlock m) t ++ li) P)
  (Hsteps : t_steps P G t (length (instrument_instr (Unlock m) t) - 1) lo
                    lc (Some P1) G1) o' c' P2 G2
  (Hend : exec P1 G1 t o' c' (Some P2) G2) (Hin' : In (t, li) P2),
  exists vs v,
    filter (fun c => beq (thread_of c) t) (lc ++ opt_to_list c') =
    mops_set_vc (C' + t) (L' + m) zt t vs ++
    mops_inc_vc (C' + t) v t ++ [Rel t m].
Proof.
  intros.
  simpl in *.
  rewrite app_length in Hsteps; simpl in Hsteps.
  rewrite Nat.add_sub in Hsteps; unfold unlock_handler in Hsteps.
  rewrite app_length in Hsteps; exploit t_steps_plus; eauto.
  intros (lo1 & lc1 & P3 & G3 & lo2 & lc2 & Hset & Hrest & ? & ?); subst.
  exploit t_steps_set_vc; eauto.
  { unfold unlock_handler in Hin; repeat rewrite <- app_assoc in Hin; eauto. }
  intros (vs & Hlc1); exists vs.
  exploit distinct_steps; eauto.
  { eapply t_steps_exec, Hset; eauto. }
  intro; exploit t_steps_length'; try apply Hset; auto.
  { unfold unlock_handler in Hin; repeat rewrite <- app_assoc in Hin; eauto. }
  intro; exploit in_split; eauto; intros (P3a & P3b & ?); subst.
  exploit t_steps_inc_vc; eauto; intros (v & Hlc2); exists v.
  repeat rewrite filter_app; rewrite Hlc1, Hlc2.
  exploit t_steps_length'; try apply Hrest; auto.
  { rewrite in_app; clarify. }
  intro; exploit in_split; eauto; intros (P1a & P1b & ?); subst.
  exploit distinct_steps; eauto.
  { eapply t_steps_exec, Hrest; eauto. }
  intro; inversion Hend; subst; exploit distinct_thread; eauto 2;
    intros (? & ? & Hi); inversion Hi; subst; clear Hi.
  rewrite <- app_assoc; clarify.
Qed.

(*Lemma t_steps_wait : forall P G t lo lc P1 G1 u li
  (Hdistinct : distinct P)
  (Hin : In (t, instrument_instr (Wait u) t ++ li) P)
  (Hsteps : t_steps P G t (length (instrument_instr (Wait u) t) - 1) lo
                    lc (Some P1) G1) o' c' P2 G2
  (Hend : exec P1 G1 t o' c' (Some P2) G2) (Hin' : In (t, li) P2),
  exists vs1 vs2,
    filter (fun c => beq (thread_of c) t) (lc ++ opt_to_list c') =
    mops_max_vc (C' + u) (C' + t) vs1 vs2 t zt.
Proof.
  admit.
Qed.*)

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

Definition accesses i := match i with
| Load _ p => Some p
| Store p _ => Some p
| Lock m => Some (m, 0)
| Unlock m => Some (m, 0)
| _ => None
end.

Lemma exec_accesses : forall P G t (Hdistinct : distinct P) o c P' G'
  (Hexec : exec P G t o c P' G') i rest (Hi : In (t, i :: rest) P) l,
  (match c with Some c => loc_of c = l | None => False end) <->
  accesses i = Some l.
Proof.
  intros.
  exploit in_split; eauto; clarify.
  inversion Hexec; exploit distinct_thread; eauto; clarify; split; clarify.
Qed.

Typeclasses eauto := 5.

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

(* We should replace Hnonoverlap and Hmetalocs_disjoint with a single one that
   actually covers all the pairs. *)
Lemma instrument_own : forall li (Hsafe : Forall safe_instr li)
  t i (Hi : In i (instrument li t)) t' (Ht' : t' < zt) n
  (Haccess : accesses i = Some (C' + t', n)), t' = t \/
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
      * (*exploit Hmetalocs_disjoint_WC; eauto; clarify.*) admit.
      * eapply plus_reg_l; eauto.
    + destruct H as [H | H]; clarify.
      * eapply plus_reg_l; eauto.
      * admit.
    + contradiction Hsafe'1; unfold meta_loc; left; simpl; omega.
    + exploit Hmetalocs_disjoint_CX; eauto; clarify.
  - left.
    repeat rewrite in_app in H; simpl in H.
    destruct H as [H | [[H | [H | [H | H]]] | [H | H]]]; clarify.
    + exploit Hmetalocs_disjoint_CX; eauto; clarify.
    + exploit hb_check_instr; eauto; intros (? & ? & [? | ?]); clarify.
      * admit.
      * eapply plus_reg_l; eauto.
    + exploit hb_check_instr; eauto; intros (? & ? & [? | ?]); clarify.
      * admit.
      * eapply plus_reg_l; eauto.
    + eapply plus_reg_l; eauto.
    + admit.
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

Definition state_suffix P1 P2 := Forall2 (fun t1 t2 => fst t1 = fst t2 /\
  exists n, snd t2 = skipn n (instrument (snd t1) (fst t1))) P1 P2.

(* up *)
Lemma skipn_in : forall A n (l : list A) x, In x (skipn n l) -> In x l.
Proof.
  intros; exploit in_nth_error; eauto; clarify.
  rewrite skipn_nth in *; eapply nth_error_in; eauto.
Qed.

Lemma instrument_thread : forall P (Hsafe : safe_locs P) P1
  (Hsim : state_suffix P P1) t li i (Hin : In (t, li) P1) (Hi : In i li)
  t' (Ht' : t' < zt) n (Haccess : accesses i = Some (C' + t', n)), t' = t \/
  (exists i', In i' (flatten (map snd P)) /\ In i (instrument_instr i' t) /\
   match i' with Spawn u _ | Wait u => t' = u | _ => False end).
Proof.
  induction P; clarify.
  - inversion Hsim; clarify.
  - inversion Hsim; clarify.
    inversion Hsafe; clarify.
    setoid_rewrite in_app.
    destruct Hin; clarify.
    + exploit instrument_own; eauto.
      { eapply skipn_in; eauto. }
      clarify; right; eauto.
    + exploit IHP; eauto; clarify; right; eauto.
Qed.

Inductive exec_star_rev : option state -> env ->
  list operation -> list conc_op -> option state -> env -> Prop :=
| exec_refl_rev P G : exec_star_rev P G [] [] P G
| exec_step_rev P G lo lc P' G' (Hexec : exec_star_rev P G lo lc (Some P') G')
    t o c P'' G'' (Hexec' : exec P' G' t o c P'' G'') :
    exec_star_rev P G (lo ++ opt_to_list o) (lc ++ opt_to_list c) P'' G''.

Lemma exec_rev_trans : forall P G P' S G' G'' e1 m1 e2 m2,
  exec_star_rev P G e1 m1 P' G' ->
  exec_star_rev P' G' e2 m2 S G'' ->
  exec_star_rev P G (e1++e2) (m1++m2) S G''.
Proof.
  intros ?????????? Hexec Hexec'; revert Hexec; induction Hexec'; clarify.
  - clarsimp.
  - repeat rewrite app_assoc; eapply exec_step_rev; eauto.
Qed.

Lemma exec_rev_some : forall P G lo lc P' G'
  (Hrev : exec_star_rev P G lo lc (Some P') G'), exists P0, P = Some P0.
Proof.
  intros; remember (Some P') as P1; generalize dependent P';
    induction Hrev; clarify; eauto.
Qed.

Lemma exec_rev : forall P G lo lc P' G',
  exec_star P G lo lc P' G' <-> exec_star_rev P G lo lc P' G'.
Proof.
  split; intros; induction H.
  - apply exec_refl_rev.
  - eapply exec_rev_trans; eauto.
    apply (exec_step_rev (exec_refl_rev _ _) Hexec).
  - apply exec_refl.
  - exploit exec_rev_some; eauto; clarify.
    eapply exec_step_inv; eauto.
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

Lemma instrument_nonnil : forall i t, instrument_instr i t <> [].
Proof.
  destruct i; repeat intro; clarify.
  - destruct x, zt; clarify.
  - destruct x, zt; clarify.
  - destruct zt; clarify.
  - destruct zt; clarify.
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

(* up *)
Lemma instrument_thread' : forall P (Hsafe : safe_locs P) P1
  (Hsim : state_sim P P1) (Hdistinct : distinct P1)
  P1' G1 lo lc G1' (Hroot : exec_star (Some P1) G1 lo lc (Some P1') G1')
  t o c t' n P1'' G' (Hstep : exec P1' G1' t o (Some c) P1'' G')
  (Hloc : loc_of c = (C' + t', n)) (Ht' : t' < zt),
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

Fixpoint spawns t i :=
  let fix spawns_list l :=
    match l with
    | [] => 0
    | i :: rest => spawns t i + spawns_list rest
    end in
  match i with
  | Spawn u li' => if eq_dec u t then S (spawns_list li') else spawns_list li'
  | _ => 0
  end.

Fixpoint spawns_list t li :=
  match li with
  | [] => 0
  | i :: rest => spawns t i + spawns_list t rest
  end.
Lemma spawns_list_def : forall t li,
  (fix spawns_list l :=
    match l with
    | [] => 0
    | i :: rest => spawns t i + spawns_list rest
    end) li = spawns_list t li.
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
  intros; intro t'; specialize (Hspawns t'); inversion Hstep; clarify;
    rewrite spawn_count_app in *; clarify;
    try solve [generalize (Hspawns2 li); rewrite in_app in *; clarify;
    eapply Hspawns2; rewrite in_app; clarify].
  rewrite (spawns_list_def t') in *.
  destruct (eq_dec u t'); [split; intros; omega|].
  split; [omega | intros].
  destruct (eq_dec t' t).
  - subst; exploit Hspawns2.
    { rewrite in_app; clarify. }
    omega.
  - rewrite <- (Hspawns2 li0); [omega|].
    rewrite in_app in *; simpl in *.
    destruct H as [? | [? | [? | ?]]]; clarify.
Qed.

Lemma step_instr : forall t i li P (Hin : In (t, i :: li) P)
  (Hdistinct : distinct P) G lo lc P' G'
  (Hsteps : exec_star (Some P) G lo lc (Some P') G')
  n (Hin' : In (t, skipn n li) P'),
  exists P1 G1 lo1 lc1 o c P1' G1' lo2 lc2,
    exec_star_minus t (Some P) G lo1 lc1 (Some P1) G1 /\
    exec P1 G1 t o c (Some P1') G1' /\
    exec_star (Some P1') G1' lo2 lc2 (Some P') G' /\
    lo = lo1 ++ opt_to_list o ++ lo2 /\ lc = lc1 ++ opt_to_list c ++ lc2.
Proof.
  intros; remember (Some P) as P0; remember (Some P') as Pf;
    generalize dependent P'; generalize dependent P; induction Hsteps;
    clarify.
  - generalize (NoDup_id_inj _ _ _ Hdistinct Hin Hin'); clarify.
    exploit skip_cons_neq; eauto; clarify.
  - destruct P'; [|inversion Hsteps; clarify].
    destruct (eq_dec t0 t).
    + subst.
      repeat eexists; eauto.
      * apply exec_refl_m.
      * auto.
      * auto.
    + exploit exec_other_thread; try apply Hin; eauto; intro.
      exploit distinct_step; eauto; intro.
      exploit IHHsteps; eauto; clarify.
      repeat eexists; eauto.
      * eapply exec_step_m; eauto.
      * clarsimp.
      * clarsimp.
Qed.

Lemma skipn_app' : forall A n (l1 l2 : list A) (Hn : n <= length l1),
  skipn n (l1 ++ l2) = skipn n l1 ++ l2.
Proof.
  intros; rewrite skipn_app.
  rewrite <- Nat.sub_0_le in Hn; rewrite Hn; auto.
Qed.

Lemma spawns_list_app : forall t P1 P2, spawns_list t (P1 ++ P2) =
  spawns_list t P1 + spawns_list t P2.
Proof.
  induction P1; clarify.
  rewrite IHP1; omega.
Qed.

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
      destruct (n' - length (spawn_handler t' t0 zt )) eqn: Hminus;
        [clarify|]; omega.
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

Lemma step_thread' : forall P G t o c P' G'
   (Hstep : exec P G t o c (Some P') G'),
  exists i li', In (t, i :: li') P /\ In (t, li') P'.
Proof.
  intros; inversion Hstep; clarify; repeat eexists; eauto; rewrite in_app;
    clarify.
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

Lemma own_thread_t_steps : forall t n P G lo lc P1 G1 (Ht : t < zt)
  (Hsteps : t_steps P G t n lo lc (Some P1) G1)
  P0 (Hsafe : safe_locs P0) P0' (Hsim : state_sim P0 P0')
  (Hdistinct : distinct P0') G0 lo0 lc0
  (Hroot : exec_star (Some P0') G0 lo0 lc0 (Some P) G)
  li (Hlive : In (t, li) P1) (Hli : li <> []) (Hspawns : safe_spawns P0'),
  Forall (fun c => fst (loc_of c) <> C' + t)
    (filter (fun x => negb (beq (thread_of x) t)) lc).
Proof.
  induction n; [clarify | simpl; intros].
  destruct Hsteps as (o1 & c1 & P' & G' & Hstep & lo1 & lc1 & [P2'|] & G2' & lo2
    & lc2 & Hminus & Hrest & ?); clarify.
  repeat rewrite filter_app, Forall_app; repeat split.
  - rewrite filter_negb_none; clarify.
    eapply exec_ops; eauto.
  - destruct P'; [|inversion Hminus].
    apply Forall_filter.
    exploit step_thread'; eauto; clarify.
    eapply own_thread; try apply Hminus; eauto.
    + eapply exec_step_inv; eauto.
    + exploit distinct_steps; eauto; intro.
      exploit distinct_step; eauto; intro.
      exploit exec_mono.
      { eauto. }
      { eapply exec_star_trans; [eapply exec_minus_exec | eapply t_steps_exec]; 
          eauto. }
      { eauto. }
      { eauto. }
      repeat intro; clarify.
      rewrite skipn_nil in *; clarify.
    + eapply safe_spawns_step; try apply Hstep.
      eapply safe_spawns_steps; eauto.
  - eapply IHn; try apply Hrest; eauto.
    eapply exec_star_trans; eauto.
    eapply exec_step; eauto.
    eapply exec_minus_exec; eauto.
Qed.  

Corollary instrument_own_thread : forall t (Ht : t < zt) P G lo lc P1 G1 i li
  (Hin : In (t, instrument_instr i t ++ li) P)
  (Hsteps : t_steps P G t (length (instrument_instr i t) - 1) lo lc
                    (Some P1) G1) o c P2 G2
  (Hend : exec P1 G1 t o c (Some P2) G2)
  P0 (Hsafe : safe_locs P0) P0' (Hdistinct : distinct P0')
  (Hspawns : safe_spawns P0') (Hsim : state_sim P0 P0') G0 lo0 lc0
  (Hroot : exec_star (Some P0') G0 lo0 lc0 (Some P) G),
  Forall (fun c => fst (loc_of c) <> C' + t)
    (filter (fun x => negb (beq (thread_of x) t)) lc).
Proof.
  intros.
  exploit step_thread'; eauto; clarify.
  eapply own_thread_t_steps; eauto; clarify.
Qed.  

(* up *)
Lemma C_meta : forall t (Ht : t < zt) o, meta_loc (C + t, o).
Proof. intros; unfold meta_loc; simpl; omega. Qed.

Fixpoint lock_only x i :=
  let fix lock_only_list l :=
    match l with
    | [] => True
    | i :: rest => lock_only x i /\ lock_only_list rest
    end in
  match i with
  | Store p _ => p <> x
  | Spawn u li => lock_only_list li
  | _ => True
  end.

Fixpoint lock_only_list x li :=
  match li with
  | [] => True
  | i :: rest => lock_only x i /\ lock_only_list x rest
  end.
Lemma lock_only_list_iff : forall x li,
  (fix lock_only_list l :=
    match l with
    | [] => True
    | i :: rest => lock_only x i /\ lock_only_list rest
    end) li <-> lock_only_list x li.
Proof.
  induction li; split; clarify; rewrite IHli in *; auto.
Qed.  

Fixpoint good_lock x (P : state) :=
  match P with
  | [] => True
  | (_, li) :: rest => lock_only_list x li /\ good_lock x rest
  end.

Lemma good_lock_app : forall x P1 P2, good_lock x (P1 ++ P2) <->
  good_lock x P1 /\ good_lock x P2.
Proof.
  induction P1; [split|]; clarify.
  destruct a; rewrite IHP1; split; clarify.
Qed.

Lemma good_lock_step : forall x P G t o c P' G' (Hlock : good_lock x P)
  (Hstep : exec P G t o c (Some P') G'), good_lock x P'.
Proof.
  intros; inversion Hstep; clarify; rewrite good_lock_app in *; clarify.
  rewrite (lock_only_list_iff x) in *; auto.
Qed.

Corollary good_lock_steps : forall x P G o c P' G' (Hlock : good_lock x P)
  (Hsteps : exec_star (Some P) G o c (Some P') G'), good_lock x P'.
Proof.
  intros; remember (Some P) as P1; remember (Some P') as P2;
    generalize dependent P; induction Hsteps; clarify.
  destruct P'0; [|inversion Hsteps].
  apply (IHHsteps s); auto.
  eapply good_lock_step; eauto.
Qed.

Definition lock_op x a := exists t, (exists v, a = Read t (x, 0) v) \/
  a = Acq t x \/ a = Rel t x.

Lemma good_lock_ops : forall x P G lo lc P' G' (Hlock : good_lock (x, 0) P)
  (Hsteps : exec_star (Some P) G lo lc P' G'),
  Forall (fun a => loc_of a = (x, 0) -> lock_op x a) lc.
Proof.
  intros.
  remember (Some P) as P1; generalize dependent P; induction Hsteps; clarify.
  rewrite Forall_app; split.
  - rewrite Forall_forall; intros.
    inversion Hexec; clarify; unfold lock_op; eauto.
    rewrite good_lock_app in Hlock; clarify.
  - clarify.
    destruct P'; [|inversion Hsteps; clarify].
    exploit good_lock_step; eauto.
Qed.
(*
Lemma init_steps : forall m p ops (Hinit : initialized m p)
  (Hops : Forall prog_op ops), initialized (m ++ ops) p.
Proof.
  induction ops using rev_ind; clarsimp.
  rewrite Forall_app in Hops; clarify.
  inversion Hops2; clarify.
  rewrite app_assoc; apply init_step; auto.
Qed.
*)
Lemma lock_hold : forall m l t ops (Hinit : initialized m (l, 0))
  (Hheld : can_read m (l, 0) (S t)) (Hcon : consistent (m ++ ops))
  (Hprog : Forall prog_op ops) (Hlock : Forall (fun a => loc_of a = (l, 0) ->
     lock_op l a) ops),
  can_read (m ++ ops) (l, 0) (S t) \/ In (Rel t l) ops.
Proof.
  induction ops using rev_ind; clarsimp.
  rewrite app_assoc in Hcon; exploit consistent_app_SC; eauto.
  rewrite Forall_app in *; clarify.
  inversion Hlock2 as [|?? Hx]; inversion Hprog2; rewrite in_app; clarify.
  unfold can_read in *.
  repeat rewrite <- app_assoc in *; simpl.
  destruct (eq_dec (loc_of x) (l, 0)).
  - unfold lock_op in Hx; clarify.
    destruct Hx as [? | [? | ?]]; clarify.
    + rewrite app_assoc, read_noop_SC; rewrite <- app_assoc; auto.
    + rewrite app_assoc, can_arw_SC_iff in Hcon.
      specialize (Hcon 0); exploit consistent_app_SC; eauto; intro.
      exploit can_read_thread'; eauto; intro.
      rewrite app_assoc in IHops.
      generalize (init_steps Hinit Hprog1); intro.
      generalize (can_read_unique(m := m ++ ops)(p := (l, 0)) (S t) 0); clarify.
    + rewrite app_assoc, can_arw_SC_iff in Hcon.
      specialize (Hcon 0); exploit consistent_app_SC; eauto; intro.
      exploit can_read_thread'; eauto; intro.
      rewrite app_assoc in IHops.
      generalize (init_steps Hinit Hprog1); intro.
      generalize (can_read_unique(m := m ++ ops)(p := (l, 0)) (S t) (S x0));
        intro Heq; clarify.
      inversion Heq; auto.
  - rewrite app_assoc, loc_valid_SC; clarify.
    repeat rewrite <- app_assoc in *; clarify.
Qed.

Lemma ARW_can_read : forall p m v v' t, consistent (m ++ [ARW t p v v']) ->
  can_read m p v.
Proof.
  intros; rewrite can_arw_SC_iff in H; specialize (H 0).
  exploit consistent_app_SC; eauto; intro.
  eapply can_read_thread'; eauto.
Qed.

Lemma can_read_arwritten : forall m p u v t, consistent (m ++ [ARW t p u v]) ->
  can_read (m ++ [ARW t p u v]) p v.
Proof.
  intros.
  apply (can_read_thread' _ _ _ t).
  rewrite read_arwritten_SC; auto.
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
    eapply good_lock_steps; eauto.
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

Lemma exec_t_steps : forall P G lo lc P' G'
  (Hexec : exec_star P G lo lc (Some P') G') t,
  exists n lo1 lc1 P1 G1 lo2 lc2, exec_star_minus t P G lo1 lc1 (Some P1) G1 /\
    t_steps P1 G1 t n lo2 lc2 (Some P') G'.
Proof.
  intros; remember (Some P') as P2; generalize dependent P'; induction Hexec;
    clarify.
  - exists 0; repeat eexists; apply exec_refl_m.
  - specialize (IHHexec _ eq_refl); destruct IHHexec as (n & ?); clarify.
    destruct (eq_dec t0 t).
    + subst; exists (S n); repeat eexists; eauto; [apply exec_refl_m|].
      simpl; eauto.
    + repeat eexists; eauto.
      eapply exec_step_m; eauto.
Qed.
      
(* up *)
Lemma X_meta : forall v (Ht : v < zv) o, meta_loc (X + v, o).
Proof. intros; unfold meta_loc; simpl; omega. Qed.

(*Definition touches_var (v p : ptr) := p = v \/
  exists off, p = (R' + fst v, off) \/ p = (W' + fst v, off) \/
              p = (X' + fst v, off).

Lemma X_touches : forall v1 v2 (Hv1 : fst v1 < zv) (Hv2 : v2 < zv)
  (Hmeta : ~meta_loc v1), touches_var v1 (X + v2, 0) -> fst v1 = v2.
Proof.
  intros ????? [? | [off [? | [? | ?]]]]; clarify.
  - contradiction Hmeta; apply X_meta; auto.
  - exploit Hmetalocs_disjoint_RX; try (symmetry; apply H1); clarify.
  - exploit Hmetalocs_disjoint_WX; try (symmetry; apply H1); clarify.
  - rewrite Nat.add_cancel_l in *; auto.
Qed.*)

Lemma distinct_in : forall P (Hdistinct : distinct P) t li1 li2
  (Hin1 : In (t, li1) P) (Hin2 : In (t, li2) P), li1 = li2.
Proof.
  intros.
  generalize (in_split _ _ Hin1), (in_split _ _ Hin2); clarify.
  exploit distinct_thread; eauto; clarify.
Qed.

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

Lemma R_meta : forall v (Ht : v < zv) o, meta_loc (R + v, o).
Proof. intros; unfold meta_loc; simpl; omega. Qed.

Lemma W_meta : forall v (Ht : v < zv) o, meta_loc (W + v, o).
Proof. intros; unfold meta_loc; simpl; omega. Qed.

Lemma v_not_C : forall t (Ht : t < zt) (o1 : nat) v (Hv : ~meta_loc v)
  (Hv2 : fst v < zv) (Haccess : Some (C + t, o1) = Some v \/
    (exists o, Some (C + t, o1) = Some (R + fst v, o)) \/
    (exists o, Some (C + t, o1) = Some (W + fst v, o))), False.
Proof.
  intros; destruct Haccess as [? | [? | ?]]; clarify.
  - contradiction Hv; apply C_meta; auto.
  - eapply Hmetalocs_disjoint_CR; eauto.
  - (*eapply Hmetalocs_disjoint_CW; eauto.*) admit.
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
  - (*eapply Hmetalocs_disjoint_RW; try (symmetry; apply H1); eauto.*)admit.
  - eapply plus_reg_l; eauto.
Qed.

Lemma unlock_last : forall i t n l rest, skipn n (instrument_instr i t) =
  Unlock l :: rest -> rest = [].
Proof.
  intros.
  assert (nth_error (skipn n (instrument_instr i t)) 0 = Some (Unlock l))
    by clarsimp.
  rewrite skipn_nth in *; clarify.
  destruct i; try destruct x; clarsimp.
  - destruct n; clarify.
    rewrite nth_error_app in *;
      destruct (lt_dec n (length (hb_check (W' + v) (C' + t) zt tmp1 tmp2))).
    + exploit nth_error_in; eauto; intro.
      exploit hb_check_instrs; eauto; clarify.
    + destruct (n - length (hb_check (W' + v) (C' + t) zt tmp1 tmp2))
        eqn: Hminus; clarify.
      destruct n2; clarify.
      destruct n2; clarsimp.
      rewrite skipn_all in H; clarify; omega.
  - destruct n; clarify.
    repeat rewrite nth_error_app in *;
      destruct (lt_dec n (length (hb_check (W' + v) (C' + t) zt tmp1 tmp2)));
      [|destruct (lt_dec (n - length (hb_check (W' + v) (C' + t) zt tmp1 tmp2))
             (length (hb_check (R' + v) (C' + t) zt tmp1 tmp2)))].
    + exploit nth_error_in; eauto; intro.
      exploit hb_check_instrs; eauto; clarify.
    + exploit nth_error_in; eauto; intro.
      exploit hb_check_instrs; eauto; clarify.
    + destruct (n - length (hb_check (W' + v) (C' + t) zt tmp1 tmp2) -
        length (hb_check (R' + v) (C' + t) zt tmp1 tmp2)) eqn: Hminus; clarify.
      destruct n3; clarify.
      destruct n3; clarsimp.
      rewrite skipn_all in H; clarify; [|omega].
      rewrite skipn_all in H; clarify; omega.
  - destruct n; clarify.
    exploit nth_error_in; eauto; intro.
    exploit max_vc_instrs; eauto; clarify.
  - unfold unlock_handler in *; rewrite <- app_assoc in *.
    repeat rewrite nth_error_app in *;
      destruct (lt_dec n (length (set_vc (C' + t) (L' + m) zt tmp1 )));
      [|destruct (lt_dec (n - length (set_vc (C' + t) (L' + m) zt tmp1 ))
             (length (inc_vc t (C' + t) tmp1)))].
    + exploit nth_error_in; eauto; intro.
      exploit set_vc_instrs; eauto; clarify.
    + destruct (n - length (set_vc (C' + t) (L' + m) zt tmp1)); clarify.
      destruct n1; clarsimp.
    + clarsimp.
      rewrite skipn_all in H; clarify; [|omega].
      rewrite skipn_all in H; clarify; [|omega].
      destruct (n - (length (set_vc (C' + t) (L' + l) zt tmp1) + 3));
        clarsimp.
  - unfold spawn_handler in *; rewrite <- app_assoc in *.
    repeat rewrite nth_error_app in *;
      destruct (lt_dec n (length (max_vc (C' + t) (C' + t0) zt tmp1 tmp2)));
      [|destruct (lt_dec (n - length (max_vc (C' + t) (C' + t0) zt tmp1 tmp2))
             (length (inc_vc t (C' + t) tmp1)))].
    + exploit nth_error_in; eauto; intro.
      exploit max_vc_instrs; eauto; clarify.
    + destruct (n - length (max_vc (C' + t) (C' + t0) zt tmp1 tmp2)); clarify.
      destruct n1; clarsimp.
    + clarsimp.
  - destruct n; clarify.
    exploit nth_error_in; eauto; intro.
    unfold wait_handler in *; rewrite in_app in H1; destruct H1 as [?|[?|[?|?]]]; clarify.
    exploit max_vc_instrs; eauto; clarify.
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
      destruct (lt_dec n (length (hb_check (W' + v) (C' + t) zt tmp1 tmp2))).
    + exploit nth_error_in; eauto; intro.
      exploit hb_check_instrs; eauto; clarify.
    + destruct (n - length (hb_check (W' + v) (C' + t) zt tmp1 tmp2))
        eqn: Hminus; clarify.
      destruct n2; clarify.
      destruct n2; clarsimp.
  - destruct n; clarify.
    repeat rewrite nth_error_app in *;
      destruct (lt_dec n (length (hb_check (W' + v) (C' + t) zt tmp1 tmp2)));
      [|destruct (lt_dec (n - length (hb_check (W' + v) (C' + t) zt tmp1 tmp2))
             (length (hb_check (R' + v) (C' + t) zt tmp1 tmp2)))].
    + exploit nth_error_in; eauto; intro.
      exploit hb_check_instrs; eauto; clarify.
    + exploit nth_error_in; eauto; intro.
      exploit hb_check_instrs; eauto; clarify.
    + destruct (n - length (hb_check (W' + v) (C' + t) zt tmp1 tmp2) -
        length (hb_check (R' + v) (C' + t) zt tmp1 tmp2)) eqn: Hminus; clarify.
      destruct n3; clarify.
      destruct n3; clarsimp.
  - destruct n; clarify.
    exploit nth_error_in; eauto; intro.
    exploit max_vc_instrs; eauto; clarify.
  - unfold unlock_handler in *; rewrite <- app_assoc in *.
    repeat rewrite nth_error_app in *;
      destruct (lt_dec n (length (set_vc (C' + t) (L' + m) zt tmp1 )));
      [|destruct (lt_dec (n - length (set_vc (C' + t) (L' + m) zt tmp1))
             (length (inc_vc t (C' + t) tmp1)))].
    + exploit nth_error_in; eauto; intro.
      exploit set_vc_instrs; eauto; clarify.
    + destruct (n - length (set_vc (C' + t) (L' + m) zt tmp1)); clarify.
      destruct n1; clarsimp.
    + clarsimp.
  - unfold spawn_handler in *; rewrite <- app_assoc in *.
    repeat rewrite nth_error_app in *;
      destruct (lt_dec n (length (max_vc (C' + t) (C' + t0) zt tmp1 tmp2)));
      [|destruct (lt_dec (n - length (max_vc (C' + t) (C' + t0) zt tmp1 tmp2))
             (length (inc_vc t (C' + t) tmp1)))].
    + exploit nth_error_in; eauto; intro.
      exploit max_vc_instrs; eauto; clarify.
    + destruct (n - length (max_vc (C' + t) (C' + t0) zt tmp1 tmp2)); clarify.
      destruct n1; clarsimp.
    + clarsimp.
  - destruct n; clarify.
    exploit nth_error_in; eauto; intro.
    unfold wait_handler in *; rewrite in_app in H1; destruct H1 as [?|[?|[?|?]]]; clarify.
    exploit max_vc_instrs; eauto; clarify.
Qed.  

Lemma L_meta : forall l (Ht : l < zl) o, meta_loc (L + l, o).
Proof. intros; unfold meta_loc; simpl; omega. Qed.

Lemma v_not_L : forall l (Hl : l < zl) (o1 : nat) v (Hv : ~meta_loc v)
  (Hv2 : fst v < zv) (Haccess : Some (L + l, o1) = Some v \/
    (exists o, Some (L + l, o1) = Some (R + fst v, o)) \/
    (exists o, Some (L + l, o1) = Some (W + fst v, o))), False.
Proof.
  intros; destruct Haccess as [? | [? | ?]]; clarify.
  - contradiction Hv; apply L_meta; auto.
  - eapply Hmetalocs_disjoint_LR; eauto.
  - (*eapply Hmetalocs_disjoint_LW; eauto.*)admit.
Qed.

Lemma previous_access : forall i1 i2 i t (Ht : t < zt) n rest
  (Hsafe : safe_instr i) (Hi : match i with Wait u => u < zt | _ => True end)
  (His : skipn n (instrument_instr i t) = i1 :: i2 :: rest)
  v (Hv : fst v < zv) (Hv2 : ~meta_loc v) (Hi2 : i2 <> Unlock (fst v))
  (Haccess : accesses i2 = Some v \/
    (exists o, accesses i2 = Some (R + fst v, o)) \/
    (exists o, accesses i2 = Some (W + fst v, o))),
  i1 = Lock (X + fst v) \/ (match i with Load _ p => p = v | Store p _ => p = v
    | _ => False end) /\ (accesses i1 = Some v \/
    (exists o, accesses i1 = Some (R + fst v, o)) \/
    (exists o, accesses i1 = Some (W + fst v, o))).
Proof.
  destruct i; try destruct x; clarify.
  - destruct n; clarsimp.
  - destruct n0; clarify.
    + left.
      destruct zt; clarify.
      exploit v_W; try apply Haccess; auto.
    + right.
      admit.
  - destruct n0; clarify.
    + left.
      destruct zt; clarify.
      exploit v_W; try apply Haccess; auto.
    + right.
      admit.
  - unfold lock_handler in His.
    exploit max_vc_instrs.
    { instantiate (6 := i2).
      destruct n; clarify.
      + setoid_rewrite H1; clarify.
      + eapply skipn_in.
        setoid_rewrite His; clarify. }
    intros [[? [? Hcases]] | ?]; clarify.
    destruct Hcases as [? | [? | ?]]; clarify.
    + exploit v_not_L; eauto; clarify.
    + exploit v_not_C; try apply Haccess; clarify.
    + exploit v_not_C; try apply Haccess; clarify.
  - unfold unlock_handler in His.
    assert (In i2 (set_vc (C' + t) (L' + m) zt tmp1 ++
      inc_vc t (C' + t) tmp1)) as Hin.
    { assert (nth_error (skipn n ((set_vc (C' + t) (L' + m) zt tmp1 ++
        inc_vc t (C' + t) tmp1) ++ [Unlock m])) 1 = Some i2) by clarsimp.
      rewrite skipn_nth, nth_error_app in *.
      destruct (lt_dec (1 + n) (length (set_vc (C' + t) (L' + m) zt tmp1 ++
        inc_vc t (C' + t) tmp1))).
      + eapply nth_error_in; eauto.
      + rewrite nth_error_single in *; clarify.
        destruct Haccess as [? | [? | ?]]; clarify.
        * contradiction Hsafe1; apply R_meta; auto.
        * contradiction Hsafe1; apply W_meta; auto. }
    rewrite in_app in Hin; destruct Hin as [Hin | Hin].
    + exploit set_vc_instrs; eauto. intros [? Hcases]; clarify.
      destruct Hcases2 as [? | ?]; clarify.
      * exploit v_not_C; try apply Haccess; clarify.
      * exploit v_not_L; try apply Haccess; clarify.
    + unfold inc_vc in Hin; simpl in Hin;
        destruct Hin as [? | [? | ?]]; clarify;
        exploit v_not_C; try apply Haccess; clarify.
  - unfold spawn_handler in His.
    assert (In i2 (max_vc (C' + t0) (C' + t) zt tmp1 tmp2 ++
      inc_vc t0 (C' + t0) tmp1)) as Hin.
    { assert (nth_error (i1 :: i2 :: rest) 1 = Some i2) as Hnth by auto.
      rewrite <- His, skipn_nth, nth_error_app in Hnth.
      destruct (lt_dec (1 + n) (length (max_vc (C' + t0) (C' + t) zt tmp1 tmp2++
        inc_vc t0 (C' + t0) tmp1))).
      + eapply nth_error_in; eauto.
      + rewrite nth_error_single in *; clarify. }
    rewrite in_app in Hin; destruct Hin as [Hin | Hin].
    + exploit max_vc_instrs; eauto. intros [[? [? [? | [? | ?]]]]| ?]; clarify;
        exploit v_not_C; try apply Haccess; clarify.
    + unfold inc_vc in Hin; simpl in Hin;
        destruct Hin as [? | [? | ?]]; clarify;
        exploit v_not_C; try apply Haccess; clarify.
  -unfold wait_handler in His. 
    assert (In i2 (max_vc (C' + t) (C' + t0) zt tmp1 tmp2 ++
      inc_vc t (C' + t) tmp1)) as Hin.
    { assert (Wait t
           :: max_vc (C' + t) (C' + t0) zt tmp1 tmp2 ++
           inc_vc t (C' + t) tmp1 = [Wait t] ++ max_vc (C' + t) (C' + t0) zt tmp1 tmp2 ++ inc_vc t (C' + t) tmp1) as Hsilly by clarsimp.
      rewrite Hsilly in His.
      assert (nth_error (i1 :: i2 :: rest) 1 = Some i2) as Hnth by auto.
      rewrite <- His, skipn_nth, nth_error_app in Hnth.
      clarify.
      eapply nth_error_in; eauto. }
    rewrite in_app in Hin; destruct Hin as [Hin | Hin ].
    +exploit max_vc_instrs; eauto. intros [[? [? [? | [? | ?]]]]| ?]; clarify;
        exploit v_not_C; try apply Haccess; clarify.
    + unfold inc_vc in Hin; simpl in Hin;
        destruct Hin as [? | [? | ?]]; clarify;
        exploit v_not_C; try apply Haccess; clarify.
  - destruct n; clarsimp.
Qed.

Fixpoint bounded_instr i :=
  let fix bounded_list l :=
    match l with
    | [] => True
    | i :: rest => bounded_instr i /\ bounded_list rest
    end in
  match i with
  | Spawn u li => u < zt /\ bounded_list li
  | _ => True
  end.

Definition bounded_threads (P : state) := Forall (fun e => fst e < zt /\
  Forall bounded_instr (snd e)) P.

Lemma bounded_list : forall li, (fix bounded_list l :=
    match l with
    | [] => True
    | i :: rest => bounded_instr i /\ bounded_list rest
    end) li <-> Forall bounded_instr li.
Proof.
  induction li; split; clarify.
  - constructor; [|rewrite IHli in *]; auto.
  - inversion H; clarify.
    rewrite IHli; auto.
Qed.

Lemma bounded_step : forall P (Hbounded : bounded_threads P)
  G t o c P' G' (Hstep : exec P G t o c (Some P') G'), bounded_threads P'.
Proof.
  intros; inversion Hstep; clarify; unfold bounded_threads in *;
    rewrite Forall_app in *; clarify; inversion Hbounded2 as [|?? [? Hbound]];
    inversion Hbound; clarify.
  repeat constructor; auto.
  rewrite bounded_list in *; auto.
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

Fixpoint instr_ind' (P : instr -> Prop) (Q : list instr -> Prop)
  (Hbase : forall i, match i with Spawn _ _ => True | _ => P i end)
  (IHi : forall u li (IHli : Q li), P (Spawn u li)) (Hnil : Q nil)
  (Hcons : forall i li (IHi : P i) (IHli : Q li), Q (i :: li)) i : P i :=
  match i as i0 return (P i0) with
    | Assign a e => Hbase (Assign a e)
    | Load a x => Hbase (Load a x)
    | Store x e => Hbase (Store x e)
    | Lock m => Hbase (Lock m)
    | Unlock m => Hbase (Unlock m)
    | Spawn u li => IHi u li (list_rect Q Hnil (fun u r => Hcons u r
        (instr_ind' P Q Hbase IHi Hnil Hcons u)) li)
    | Wait u => Hbase (Wait u)
    | Assert_le e1 e2 => Hbase (Assert_le e1 e2)
  end.

Lemma no_spawn_bounded : forall l (Hout : Forall (fun i =>
  match i with Spawn _ _ => False | _ => True end) l),
  Forall bounded_instr l.
Proof.
  intros; rewrite Forall_forall in *; clarify.
  specialize (Hout x); destruct x; clarify.
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
      rewrite bounded_list, safe_instrs in *; auto.
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

Lemma skipn_cons : forall A l (x y : A) l' n, skipn n (x :: l) = y :: l' ->
  skipn n l = l'.
Proof.
  induction l; clarify.
  - destruct n; simpl in *; [|rewrite skipn_nil in *]; clarify.
  - destruct n; clarify; eauto.
Qed.

Lemma protect_v : forall P0 (Hsafe : safe_locs P0)
  (Ht : Forall (fun e => fst e < zt) P0) P0' (Hsim : state_sim P0 P0')
  (Hdistinct : distinct P0') G0 lo lc P G
  (Hsteps : exec_star (Some P0') G0 lo lc (Some P) G)
  v (Hv : fst v < zv) (Hmeta : ~meta_loc v)
  (Hlock : good_lock (X + fst v, 0) P0')
  m (Hinit : initialized m (X + fst v, 0)) (Hcon : consistent (m ++ lc))
  t i li (Hin : In (t, i :: li) P) (Hlock : i <> Lock (fst v))
  (Hunlock : i <> Unlock (fst v)) (Haccess : accesses i = Some v \/
    (exists o, accesses i = Some (R + fst v, o)) \/
    (exists o, accesses i = Some (W + fst v, o))),
  can_read (m ++ lc) (X + fst v, 0) (S t).
Proof.
  intros until m; intros ??; rewrite exec_rev in Hsteps.
  remember (Some P0') as P1; remember (Some P) as P2; generalize dependent P;
    generalize dependent P0'; induction Hsteps; clarify.
  - exploit in_split; eauto; clarify.
    exploit Forall2_app_inv_r; eauto; intros (? & ? & ? & Hrest & ?).
    inversion Hrest as [|(?, li') Hi]; inversion Hi; clarify.
    destruct li'; clarify.
    destruct (accesses i) as [(?, ?)|] eqn: Hi; [|clarify].
    setoid_rewrite Forall_app in Hsafe; clarify.
    inversion Hsafe2 as [|?? Hsafe_i]; inversion Hsafe_i as [|?? Hsafei ?];
      clarify.
    exploit instrument_access; eauto; intros [[? ?] | [? [? | ?]]]; clarify.
    + exploit v_not_C; eauto; clarify.
      rewrite Forall_app in Ht; clarify.
      inversion Ht2; clarify.
    + destruct Haccess as [? | [? | ?]]; clarify.
      * contradiction Hsafei1; apply R_meta; auto.
      * contradiction Hsafei1; apply W_meta; auto.
    + exploit v_not_X; try apply Haccess; clarify.
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
      exploit distinct_steps; eauto; intro.
      exploit step_thread; eauto.
      { rewrite in_app; clarify. }
      clarify.
      exploit distinct_step; eauto; intro.
      exploit distinct_in.
      { eauto. }
      { apply Hin. }
      { eauto. }
      intro Hli.
      exploit bounded_sim; eauto; intro.
      exploit bounded_steps; eauto; setoid_rewrite Forall_app.
      intros [? Ht']; inversion Ht'; clarify.
      destruct li2; clarify.
      { destruct rest; clarify.
        inversion Hsafe_i as [|?? Hsafei]; subst.
        destruct (accesses i) as [(?, ?)|] eqn: Hi; [|clarify].
        exploit instrument_access; eauto; intros [[? ?] | [? [? | ?]]]; clarify.
        + exploit v_not_C; eauto; clarify.
        + destruct Haccess as [? | [? | ?]]; clarify.
          * contradiction Hsafei1; apply R_meta; auto.
          * contradiction Hsafei1; apply W_meta; auto.
        + exploit v_not_X; try apply Haccess; clarify. }
      exploit previous_access; eauto.
      { destruct i2; auto.
        assert (distinct x).
        { eapply distinct_steps; [|eauto]; auto. }
        exploit step_instr; try apply Hi2.
        { auto. }
        { eapply exec_step_inv; eauto. }
        { instantiate (1 := n'); rewrite skipn_app.
          destruct (n' - length (wait_handler t t0 zt)) eqn: Hminus.
          simpl; erewrite skipn_cons; [|apply H2]; auto.
          { rewrite skipn_all in H2; [inversion H2 | simpl; omega]. } }
        intros (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Hwait & ?).
        exploit exec_other_threads; try apply Hi2; eauto; intro.
        exploit distinct_steps; [|eapply exec_minus_exec; eauto|]; auto.
        exploit in_split; eauto; clarify.
        inversion Hwait; subst; exploit distinct_thread; eauto; clarify.
        exploit bounded_steps; try apply H1; auto; intro.
        exploit bounded_steps; [|eapply exec_minus_exec; eauto|]; auto.
        setoid_rewrite Forall_forall; intro Hbound; exploit Hbound; eauto;
          clarify. }
      intros [? | [Hi2' Haccess2]].
      { subst.
        exploit lock_first; eauto; clarify.
        rewrite app_assoc; apply can_read_arwritten; auto. }
      exploit IHHsteps.
      { rewrite in_app; clarify. }
      { intro; subst.
        exploit lock_first; eauto; clarify.
        destruct i2; try destruct x5; clarify.
        * contradiction H41; rewrite <- H8; apply X_meta; auto.
        * contradiction H41; rewrite <- H8; apply X_meta; auto. }
      { intro; subst.
        exploit unlock_last; eauto; clarify. }
      { auto. }
      intro.
      exploit lock_hold; try apply Hcon; try apply Hhold.
      { eapply init_steps, prog_steps; eauto. }
      { eauto. }
      { eapply prog_step; eauto. }
      { eapply good_lock_ops.
        * eapply good_lock_steps; eauto.
        * eapply exec_step'; try apply exec_refl; eauto; clarsimp. }
      rewrite <- app_assoc; clarify.
      destruct c; clarify.
      inversion Hexec'; clarify.
      exploit distinct_thread; try apply Hunlock0; clarify.
      exploit unlock_last; eauto; clarify.
    + destruct (instr_result t i' (G' t) v') as [((((?, ?), ?), ?), ?)|]
        eqn: Hi'; clarify.
      assert (In (t0, i :: li) (Pa ++ (t, i' :: li') :: Pb) ->
        can_read (m ++ lc ++ opt_to_list c) (X' + fst v, 0) (S t0)).
      { intro; exploit IHHsteps; eauto; intro Hhold.
        exploit lock_hold; try apply Hcon; try apply Hhold.
        { eapply init_steps, prog_steps; eauto. }
        { eapply prog_step; eauto. }
        { eapply good_lock_ops.
          * eapply good_lock_steps; eauto.
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
      destruct x; clarify.
      inversion Hsafe_i as [|?? Hsafei]; subst.
      destruct (accesses i) as [(?, ?)|] eqn: Hi; [|clarify].
      exploit instrument_access; eauto; intros [[? ?] | [? [? | ?]]]; clarify.
      * exploit v_not_C; eauto; clarify.
        exploit bounded_sim; eauto; intro.
        exploit bounded_steps; eauto.
        setoid_rewrite Forall_app; intros [_ Ht'].
        inversion Ht' as [|?? [? Hi1]]; subst.
        inversion Hi1; clarify.
      * destruct Haccess as [? | [? | ?]]; clarify.
        { contradiction Hsafei1; apply R_meta; auto. }
        { contradiction Hsafei1; apply W_meta; auto. }
      * exploit v_not_X; try apply Haccess; clarify.
Qed.
(*!!*)

(*Lemma exec_load : forall P G t lo lc P1 G1 a x o li
  (Hdistinct : distinct P)
  (Hin : In (t, instrument_instr (Load a (x, o)) t ++ li) P)
  (Hsteps : t_steps P G t (length (instrument_instr (Load a (x, o)) t) - 1) lo
                    lc (Some P1) G1) o' c' P2 G2
  (Hend : exec P1 G1 t o' c' (Some P2) G2) (Hin' : In (t, li) P2),
  exists vs1 vs2 vt v,
    filter (fun c => beq (thread_of c) t) (lc ++ opt_to_list c') =
    Acq t (X + x) :: mops_hb_check (W' + x) (C' + t) vs1 vs2 zt t ++
    mops_move (C' + t, t) (R' + x, t) t vt ++ [Read t (x, o) v; Rel t (X' + x)].
Proof.
  intros.
  unfold instrument_instr in Hsteps.
  rewrite app_length in Hsteps; simpl in Hsteps.
  rewrite <- minus_n_O, <- plus_n_Sm in Hsteps; simpl in Hsteps.
  destruct Hsteps as (o0 & c0 & P0 & G0 & Hstep0 & lo1 & lc1 & [P'|] & G' &
    lo2 & lc2 & Hminus0 & Hrest); clarify.
  generalize (in_split _ _ Hin); intros (Pa & Pb & ?); subst.
  inversion Hstep0; subst; exploit distinct_thread; eauto 2;
    intros (? & ? & Hi); inversion Hi; subst.
  exploit exec_other_threads; try apply Hminus0.
  { rewrite in_app; clarify. }
  intro; exploit in_split; eauto; intros (P'a & P'b & ?); subst.
  rewrite app_length, <- plus_assoc in Hrest1; exploit t_steps_plus; eauto.
  intros (lo3 & lc3 & P3 & G3 & lo4 & lc4 & Hcheck & Hrest' & ? & ?); subst.
  exploit distinct_step; eauto; intro Hdistinct1.
  exploit distinct_steps; eauto.
  { eapply exec_minus_exec; eauto. }
  intro; exploit t_steps_length'; try apply Hcheck; auto.
  { rewrite in_app; right; simpl; left.
    do 2 rewrite <- app_assoc; eauto. }
  intro; exploit in_split; eauto; intros (P3a & P3b & ?); subst.
  exploit distinct_steps; eauto.
  { eapply t_steps_exec; eauto. }
  intro; simpl in Hrest'.
  destruct Hrest' as (o1 & c1 & P4 & G4 & Hstep1 & lo5 & lc5 & [P5|] & G5 &
    lo6 & lc6 & Hminus1 & Hrest2 & ? & ?); [subst | clarify].
  destruct Hrest2 as (o2 & c2 & P6 & G6 & Hstep2 & lo7 & lc7 & [P7|] & G7 &
    lo8 & lc8 & Hminus2 & Hrest3 & ? & ?); [subst | clarify].
  destruct Hrest3 as (o3 & c3 & P8 & G8 & Hstep3 & lo9 & lc9 & [P9|] & G9 &
    lo10 & lc10 & Hminus3 & Hrest4 & ? & ?); clarify.
  inversion Hstep1; subst; exploit distinct_thread; eauto 2;
    intros (? & ? & Hi); inversion Hi; subst; clear Hi.
  exploit exec_other_threads; try apply Hminus1.
  { rewrite in_app; clarify. }
  intro; exploit in_split; eauto; intros (P5a & P5b & ?); subst.
  exploit distinct_step; eauto; intro.
  exploit distinct_steps; eauto.
  { eapply exec_minus_exec; eauto. }
  intro; inversion Hstep2; subst; exploit distinct_thread; eauto 2;
    intros (? & ? & Hi); inversion Hi; subst; clear Hi.
  exploit exec_other_threads; try apply Hminus2.
  { rewrite in_app; clarify. }
  intro; exploit in_split; eauto; intros (P7a & P7b & ?); subst.
  exploit distinct_step; eauto; intro.
  exploit distinct_steps; eauto.
  { eapply exec_minus_exec; eauto. }
  intro; inversion Hstep3; subst; exploit distinct_thread; eauto 2;
    intros (? & ? & Hi); inversion Hi; subst; clear Hi.
  exploit exec_other_threads; try apply Hminus3.
  { rewrite in_app; clarify. }
  intro; exploit in_split; eauto; intros (P9a & P9b & ?); subst.
  exploit distinct_step; eauto; intro.
  exploit distinct_steps; eauto.
  { eapply exec_minus_exec; eauto. }
  intro; inversion Hend; subst; exploit distinct_thread; eauto 2;
    intros (? & ? & Hi); inversion Hi; subst; clear Hi.
  repeat rewrite filter_app; simpl.
  repeat rewrite beq_refl.
  exploit t_steps_hb_check; try apply Hcheck; auto.
  { rewrite in_app; right; simpl; left.
    do 2 rewrite <- app_assoc; eauto. }
  intros ((vs1 & vs2 & Hlc3) & HG); exists vs1, vs2, v, v0; rewrite Hlc3.
  generalize (exec_minus_ops Hminus0), (exec_minus_ops Hminus1),
    (exec_minus_ops Hminus2), (exec_minus_ops Hminus3);
    intros Hall0 Hall1 Hall2 Hall3.
  rewrite (filter_none _ Hall0), (filter_none _ Hall1),
    (filter_none _ Hall2), (filter_none _ Hall3); simpl.
  rewrite (exec_minus_env Hminus1), upd_same.
  clear; clarsimp.
Qed.*)

Lemma instrument_length : forall i t, length (instrument_instr i t) <> 0.
Proof.
  repeat intro.
  destruct (instrument_instr i t) eqn: Hi; clarify.
  exploit instrument_nonnil; eauto.
Qed.

(* replace the previous version with this *)
Lemma t_steps_extend' : forall P' G' lo lc P'' G''
  (Hsteps : exec_star (Some P') G' lo lc (Some P'') G'')
  P G t n lo0 lc0 (Hdistinct : distinct P)
  (Ht_steps : t_steps P G t n lo0 lc0 (Some P') G')
  li1 li2 (Hin : In (t, li1 ++ li2) P) (Hn : n <> 0)
  (Hin'' : In (t, li2) P''),
  t_steps P G t (length li1) (lo0 ++ lo) (lc0 ++ lc) (Some P'') G''.
Proof.
  intros ???????.
  remember (Some P') as S; remember (Some P'') as S'; generalize dependent P'';
    generalize dependent P'; induction Hsteps; clarify.
  { clarsimp.
    erewrite <- t_steps_length; eauto. }
  destruct P'; [|inversion Hsteps; clarify].
  specialize (IHHsteps _ eq_refl _ eq_refl).
  destruct (eq_dec t0 t); clarify.
  - exploit t_steps_add_t; eauto; intro Ht_steps'.
    specialize (IHHsteps _ _ _ _ _ _ Hdistinct Ht_steps' _ _ Hin);
      do 2 use IHHsteps.
    repeat rewrite <- app_assoc in *; auto.
  - exploit t_steps_add_other; eauto; intro Ht_steps'.
    specialize (IHHsteps _ _ _ _ _ _ Hdistinct Ht_steps' _ _ Hin);
      do 2 use IHHsteps.
    repeat rewrite <- app_assoc in *; auto.
Qed.

Lemma exec_thread' : forall P G t o c P' G' (Hdistinct : distinct P)
  (Hstep : exec P G t o c (Some P') G') lo lc P'' G''
  (Hsteps : exec_star (Some P') G' lo lc (Some P'') G'')
  li1 li2 (Hin : In (t, li1 ++ li2) P) (Hin'' : In (t, li2) P''),
  t_steps P G t (length li1) (opt_to_list o ++ lo) (opt_to_list c ++ lc)
    (Some P'') G''.
Proof.
  intros; eapply t_steps_extend' with (n := 1); eauto.
  simpl; repeat eexists; eauto.
  - apply exec_refl_m.
  - clarsimp.
Qed.

Lemma app_neq : forall A (l l' : list A) a, a :: l ++ l' <> l'.
Proof.
  repeat intro.
  assert (length (a :: l ++ l') = length l') by (rewrite H; auto).
  simpl in *; rewrite app_length in *; omega.
Qed.

Lemma last_cons : forall A (x d : A) l (Hnonnil : l <> []), last (x :: l) d =
  last l d.
Proof. clarify. Qed.

Opaque last.
Lemma skipn_last : forall A (l l' : list A) x d n,
  skipn n (l ++ l') = x :: l' -> n = length l - 1 /\ x = last l d.
Proof.
  induction l; clarify.
  { exploit skip_cons_neq; eauto; clarify. }
  destruct (nil_dec l).
  - subst; destruct n; simpl in *.
    + clarify.
    + exploit skip_cons_neq; eauto; clarify.
  - rewrite last_cons; auto.
    destruct n; clarify.
    { destruct l; clarify.
      exploit app_neq; eauto; clarify. }
    exploit IHl; eauto; clarify.
    split; [|eauto].
    assert (length l <> 0) by (destruct l; clarify); omega.
Qed.    
 (* 
Lemma instrument_indep : forall P0 G0 t o c P G lo lc P1 G1 o' c' P2 G2 i rest
  (Hdistinct : distinct P0) P0' (Hsim : state_sim P0' P0)
  (Hin : In (t, instrument_instr i t ++ rest) P0)
  (Hstep1 : exec P0 G0 t o c (Some P) G)
  (Hsteps : exec_star (Some P) G lo lc (Some P1) G1)
  (Hstep2 : exec P1 G1 t o' c' (Some P2) G2) (Hin' : In (t, rest) P2)
  m (Hcon : consistent (m ++ opt_to_list c ++ lc ++ opt_to_list c')),
  Forall (fun c1 => Forall (fun c2 => loc_of c2 <> loc_of c1)
    (filter (fun c => beq (thread_of c) t)
            (opt_to_list c ++ lc ++ opt_to_list c')))
    (filter (fun x => negb (beq (thread_of x) t)) lc).
Proof.
  intros.
  exploit step_thread'; eauto; intros (i' & ? & Hin1 & ?).
  exploit distinct_step; eauto; intro Hdistinct'.
  exploit distinct_steps; eauto; intro Hdistinct1.
  exploit distinct_step; eauto; intro Hdistinct2.
  exploit distinct_in.
  { eauto. }
  { eauto. }
  { apply Hin'. }
  intro; subst.
  exploit exec_thread'.
  { apply Hdistinct. }
  { eauto. }
  { eauto. }
  { rewrite (app_removelast_last (Lock 0) (instrument_nonnil i t)) in Hin.
    rewrite <- app_assoc in Hin; eauto. }
  { exploit exec_mono; try apply Hdistinct.
    { eapply exec_step; eauto. }
    { eauto. }
    { eauto. }
    intros (n & Heq).
    exploit skipn_last; eauto.
    intros (_ & Hi'); rewrite Hi' in *; eauto. }
  intro Ht_steps.
  intros; rewrite Forall_locs; destruct i; try destruct x.
  - exploit step_thread; try apply Hstep1; eauto; clarify.
    exploit distinct_step; eauto; intro.
    exploit exec_keep; eauto; clarify.
    exploit distinct_steps; eauto; intro.
    exploit step_thread; eauto; clarify.
    exploit distinct_step; eauto; intro.
    exploit distinct_in.
    { eauto. }
    { apply Hin'. }
    { eauto. }
    clarify; exploit skip_cons_neq; eauto; clarify.
  - 
    generalize (in_split _ _ Hin); clarify.
    inversion Hstep1; subst; exploit distinct_thread; eauto; clarify.
    
    (* Something like t_steps_load can tell us what's in lc ++ opt_to_list c'.
     *)
    (* Then we need mutex. *)
(*    
    destruct x; exploit t_steps_load; simpl; eauto.
    intros (vs1 & vs2 & vt & v' & Hlct); rewrite Hlct.
    simpl; rewrite map_app; simpl.
    simpl in Hsteps; rewrite app_length in Hsteps; simpl in Hsteps.
    rewrite Forall_forall; repeat intro.
    
    (* Other threads can't touch:
       X, R, or W for v, or v, because the lock is held
       C for t, because they aren't t. *)
    
    *)
Abort.*)


Lemma exec_t_maintain : forall P G lo lc P' G' t li (Hdistinct : distinct P)
  (Hin : In (t, li) P) (Hsteps : exec_star_t t (Some P) G lo lc (Some P') G')
  (Hin' : In (t, li) P'), P' = P /\ G' = G /\ lo = [] /\ lc = [].
Proof.
  intros; inversion Hsteps; clarify.
  destruct P'0; [|inversion Hexec'; clarify].
  exploit step_thread; eauto; clarify.
  exploit distinct_step; eauto; intro.
  exploit exec_mono; eauto.
  { eapply exec_t_exec; eauto. }
  clarify.
  exploit skip_cons_neq; eauto; clarify.
Qed.

Lemma cons_app_neq : forall A (x : A) l1 l2, x :: l1 ++ l2 <> l2.
Proof.
  repeat intro.
  assert (length (x :: l1 ++ l2) = length l2) by (rewrite H; auto).
  simpl in *; rewrite app_length in *; omega.
Qed.

Lemma exec_t_iexec : forall t P G lo lc P' G' i li (Hdistinct : distinct P)
  (Hin : In (t, instrument_instr i t ++ li) P)
  (Ht : exec_star_t t (Some P) G lo lc (Some P') G') (Hin' : In (t, li) P'),
  iexec P G t lo lc P' G'.
Proof.
  destruct i; clarify.
  - inversion Ht; clarify.
    { generalize (NoDup_id_inj _ _ _ Hdistinct Hin Hin'); clarify.
      exploit cons_neq; eauto; clarify. }
    generalize (in_split _ _ Hin); intros (P1 & P2 & ?); clarify.
    inversion Hexec; clarify; exploit distinct_thread; eauto; clarify.
    exploit distinct_step; eauto; intro.
    exploit exec_t_maintain; eauto.
    { rewrite in_app; clarify. }
    clarify; apply iexec_assign; auto.
  - destruct x.
    inversion Ht; clarify.
    { generalize (NoDup_id_inj _ _ _ Hdistinct Hin Hin'); clarify.
      exploit cons_app_neq; eauto; clarify. }
    generalize (in_split _ _ Hin); intros (P1 & P2 & ?); clarify.
    inversion Hexec; clarify; exploit distinct_thread; eauto; clarify.
    
    (* ... *)
    (* We need the reverse specs, that tell us that if we step a handler,
       then it produces the expected shape. *)
Admitted.

Lemma exec_iexec : forall P P' (Hfinal : final_state (Some P')) G' G lo lc
  (Hexec : exec_star (Some P) G lo lc (Some P') G') (Hdistinct : distinct P)
  P1 (HP : state_sim P1 P) 
  m (Hcon : consistent (m ++ lc)),
  exists lo' lc', iexec_star P G lo' lc' P' G' /\ consistent (m ++ lc').
  (* And not just an arbitrary lc'. *)
Proof.
  intros ????.
  remember (size P) as z; generalize dependent P;
    induction z using lt_wf_ind; clarify.
  inversion Hexec; clarify.
  { exists [], []; clarify; apply iexec_refl. }
  destruct P'0; [|inversion Hexec'; clarify].
  exploit distinct_step; eauto; intro Hdistinct'.
  assert (exists Pa Pb i li P1a P1b, P = Pa ++ (t, instrument_instr i t ++
            instrument li t) :: Pb /\ P1 = P1a ++ (t, i :: li) :: P1b)
    as (Pa & Pb & i & li & P1a & P1b & Ht & HP1).
  { unfold state_sim in HP; inversion Hexec0; clarify;
      exploit Forall2_app_inv_r; try apply HP;
      intros (P0' & P3' & HP0 & Hrest & ?);
      inversion Hrest as [|(?, [|i l]) (?, ?) ? ? [? Hieq] HP3]; clarify;
      rewrite Hieq; repeat eexists; eauto. }
  subst; exploit state_sim_inv; eauto; clarify.
  assert (In (t, instrument_instr i t ++ instrument li t)
    (Pa ++ (t, instrument_instr i t ++ instrument li t) :: Pb))
    as Hin by (rewrite in_app; clarify).
  exploit step_thread; eauto; intros (i0 & li' & Heq & Hs).
  generalize (instrument_nonnil i t); intro Hnonnil.
  assert (exists li1, instrument_instr i t = i0 :: li1 /\
    li' = li1 ++ instrument li t) as (li1 & Hinstr & ?); clarify.
  { destruct (instrument_instr i t); clarify; eauto. }
  destruct (nil_dec li1).
  { clarify.
    exploit size_decr; eauto; intro Hlt.
    specialize (H _ Hlt _ eq_refl _ _ _ Hexec' Hdistinct').
    specialize (H (P1a ++ (t, li) :: P1b)); use H.
    rewrite app_assoc in Hcon; specialize (H _ Hcon); clarify.
    rewrite <- app_assoc in *; repeat eexists; [eapply iexec_step|]; eauto.
    exploit instrument_single; eauto; destruct i; clarify;
      inversion Hexec0; exploit distinct_thread; eauto; clarify.
    - apply iexec_assign; auto.
    - eapply iexec_assert; auto.
    - exploit Forall2_app_inv_l; eauto; clarify.
      exploit instrument_single; eauto; destruct i; clarify;
        inversion Hexec0; exploit distinct_thread; eauto; clarify;
        apply Forall2_app; auto. }
  exploit step_segment; try apply Hexec'; eauto.
  intros (P'' & G'' & lo1 & lc1 & Pt & Gt & o' & c' & lo2 & lc2 & Hsegment &
    Hlast & HPt & Hrest & Hlo & Hlc); subst.
  exploit exec_keep; try apply Hsegment; eauto; intros (? & HP'').
  exploit distinct_steps; try apply Hsegment; eauto; intro Hdistinct''.
  exploit step_thread; eauto; intros (i' & ? & Heqt & Hin2); clarify.
  exploit distinct_step; eauto; intro Hdistinctt.
  generalize (NoDup_id_inj _ _ _  Hdistinctt Hin2 HPt); clarify.
  assert (skipn x li1 = [last (instrument_instr i t) (Lock 0)] /\
          x - length li1 = 0) as (Hskip & Hx).
  { assert (length (skipn x (li1 ++ instrument li t)) =
      length (i' :: instrument li t)) by (rewrite Heqt; auto).
    rewrite skipn_length, app_length, skipn_app in *.
    simpl in *; split; [|omega].
    destruct (skipn x li1) eqn: Hskip; clarify.
    { exploit skip_cons_neq; eauto; clarify. }
    rewrite not_le_minus_0 in H3; [|omega].
    clarify; exploit app_nil_inv; eauto; clarify.
    erewrite (app_removelast_last (Lock 0) n) in Hskip.
    rewrite skipn_app, skipn_all in Hskip; clarify.
    destruct (x - length (removelast li1)); clarify.
    rewrite Hinstr; destruct li1; clarify.
    { destruct n0; clarify. }
    { rewrite removelast_length; auto; omega. } }
  rewrite skipn_app, Hskip, Hx in *; clear dependent x; clear dependent i'.
  rewrite (app_removelast_last (Lock 0) Hnonnil) in Hin at 1.
  rewrite <- app_assoc in Hin.
  exploit exec_thread; try apply Hexec0; try apply Hsegment; eauto.
  { rewrite removelast_length, Hinstr; clarify.
    destruct li1; clarify. }
  intro Htsteps.
  exploit t_steps_add_t; try apply Htsteps; eauto; intro Histeps.
  rewrite removelast_length in Histeps; auto.
  rewrite minus_Sn_m in Histeps; [|rewrite Hinstr; simpl; omega].
  simpl in Histeps; rewrite <- minus_n_O in Histeps.
  rewrite app_assoc, <- app_removelast_last in Hin; auto.
  exploit t_steps_indep; try apply Histeps.
  { auto. }
  { eauto. }
  { intros; eapply instrument_wait; eauto. }
  { repeat rewrite app_assoc in *; eapply consistent_app_SC; eauto. }
  { rewrite partition_filter; eauto. }
  { repeat rewrite filter_app.
    generalize (exec_ops Hexec0), (exec_ops Hlast); intros Hallt Hallt'.
    rewrite (filter_all _ Hallt), (filter_negb_none _ Hallt),
      (filter_all _ Hallt'), (filter_negb_none _ Hallt'), app_nil_r; simpl.
    rewrite <- app_assoc.
    admit. }
  intros (lot & P1 & G1 & lor & Hi & HP1 & Hrest' & Hcon').
  exploit exec_t_iexec; try apply Hi; eauto; intro.
  exploit distinct_steps; try eapply exec_t_exec, Hi; auto; intro.
  specialize (H (size P1)); use H.
  specialize (H _ eq_refl).
  exploit exec_star_trans; [eapply exec_minus_exec; eauto | eauto|].
  intro Hrests; specialize (H _ _ _ Hrests); clarify.
  assert (exists P1', state_sim P1' P1) as (P1' & HPsim').
  { admit. }
  specialize (H _ HPsim'); clarify.
  specialize (H (m ++ filter (fun c0 => beq (thread_of c0) t)
    ((opt_to_list c ++ lc1) ++ opt_to_list c'))); use H.
  destruct H as (lo' & lc' & ? & ?).
  repeat eexists; [eapply iexec_step; eauto|].
  repeat rewrite <- app_assoc in *; auto.
  - repeat rewrite filter_app.
    generalize (exec_ops Hexec0), (exec_ops Hlast); intros Hallt Hallt'.
    rewrite (filter_all _ Hallt), (filter_negb_none _ Hallt),
      (filter_all _ Hallt'), (filter_negb_none _ Hallt'), app_nil_r; simpl.
    repeat rewrite <- app_assoc; rewrite app_assoc.
    eapply loc_split; try (rewrite partition_filter; eauto).
    rewrite <- app_assoc; auto.
    (* As above. *) admit. admit. admit.
  - eapply component_decr; eauto.
    { eapply exec_t_exec; eauto. }
    rewrite app_length, Hinstr; simpl; omega.
Qed.


Lemma list_part_diff : forall (X:Type) (l1 l2 l3 l4: list X)
 (Hlen: length l1 = length l2) (Hdiff: l3<>l4), l1++l3<> l2++l4.
Proof.
  induction l1; intros.
  -destruct l2; clarify.
  -destruct l2; clarify.
   intro Heq; inversion Heq; clarify. inversion Hlen. 
   specialize(IHl1 l2 l3 l4 H0 Hdiff). clarify.
Qed.

Lemma list_part_same : forall (X:Type) (l1 l2 l3 l4: list X)
  (Hlen: length l1 = length l2) (Hsame: l1++l3=l2++l4), 
  l1=l2.
Proof.
  induction l1; intros.
  -destruct l2; clarify.
  -destruct l2; clarify. inversion Hlen.
   specialize(IHl1 l2 l3 l4 H0 H1). clarify.
Qed.

Lemma length_hb_check : forall C1 C2 z t1 t2,
  length (hb_check C1 C2 z t1 t2) = z+z+z.
Proof.
  induction z; intros.
  -clarify.
  -simpl. specialize(IHz t1 t2). rewrite IHz. omega.
Qed.

Lemma instrument_incom : forall i i' l l' t,
  instrument_instr i t ++ l = instrument_instr i' t ++ l' -> i' = i /\ l' = l.
Proof.
  intro.
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

Lemma Forall2_cons_inv (X:Type) l1 l2 (x1 x2: X) P:
  Forall2 P (x1 :: l1) (x2 :: l2)-> P x1 x2 /\ Forall2 P l1 l2.
Proof.
  intros. inversion H. clarify. Qed.

Lemma first_gt_vc : forall (V1 V2: tid->nat) l
  (Hgt: first_gt (map V1 l) (map V2 l) = None) i (Hi : In i l), V1 i <= V2 i.
Proof.
  induction l; clarify.
  rewrite leb_le in *; clarify.
Qed.

Lemma first_gt_vc_le : forall (V1 V2: tid->nat) m x1 x2
  (Hgt: first_gt (map V1 (rev (interval 0 zt))) (map V2 (rev (interval 0 zt))) =
     None)
  (Hmatch1 : clock_match m V1 x1) (Hmatch2 : clock_match m V2 x2),
  vc_le V1 V2.
Proof.
  repeat intro.
  specialize (Hmatch1 t); specialize (Hmatch2 t).
  destruct (lt_dec t zt); clarsimp.
  eapply first_gt_vc; eauto.
  rewrite <- in_rev, interval_in_iff; auto.
Qed.

Lemma mops_max_vc_off' : forall src tgt vs1 vs2 t n
  (Hvs1: length vs1 = n) (Hvs2: length vs2 = n),
  Forall (fun c' => match loc_of c' with (x, o) => o < n end)
     (mops_max_vc src tgt vs1 vs2 t n).
Proof.
  intros. generalize dependent vs1. generalize dependent vs2.
  induction n; clarify.
  -apply empty_list in Hvs1. apply empty_list in Hvs2. clarify.
  -apply nonempty_list in Hvs1. apply nonempty_list in Hvs2.
   inversion Hvs1. inversion H. inversion Hvs2. inversion H1.
   inversion H0. inversion H2. rewrite H3, H5.
   rewrite mops_max_vc_step. rewrite Forall_app. split.
   +unfold mops_max. rewrite Forall_forall. intros c Hin.
    inversion Hin; clarify. destruct Hin as [Hc|[Hc|[Hc|Hc]]]; clarify.
   +assert( forall c ,
              (fun c' : conc_op => let (_, o) := loc_of c' in o < n) c ->
              (fun c' : conc_op => let (_, o) := loc_of c' in o < S n) c) as Himpl.
      intros. destruct (loc_of c); clarify.
    eapply Forall_impl; eauto.
Qed.

Lemma max_vc_vals1: forall m C1 C2 z vs1 vs2 t V1 V2
  (Hinit1: forall z, z < zt -> initialized m (C1, z))
  (Hinit2: forall z, z < zt -> initialized m (C2, z))
  (Hcon: consistent (m ++mops_max_vc C1 C2 vs1 vs2  t z))
  (Hvs1: length vs1 =z) (Hvs2: length vs2 = z) (Hz : z <= zt)
  (Hmatch1 : clock_match m V1 C1) (Hmatch2 : clock_match m V2 C2),
  vs1 = map V1 (rev (interval 0 z)) /\ vs2 = map V2 (rev (interval 0 z)).
Proof.
  induction z; destruct vs1, vs2; clarify.
  rewrite rev_app_distr; clarify.
  assert ( consistent (m++ [Read t (C1, z) n])) as Hn.
  { eapply consistent_app_SC; rewrite <- app_assoc; simpl; eauto. }
  assert ( consistent (m++ [Read t (C2, z) n0])) as Hn0.
  { rewrite read_noop_SC in Hcon; auto.
    eapply consistent_app_SC; rewrite <- app_assoc; simpl; eauto. }
  assert ( consistent (m++ [Write t (C2, z) (Peano.max n n0)])) as Hwn0.
  { do 2 (rewrite read_noop_SC in Hcon; auto).
    eapply consistent_app_SC; rewrite <- app_assoc; simpl; eauto. }
  exploit (IHz vs1 vs2); eauto.
  {do 2 (rewrite read_noop_SC in Hcon; eauto).
   rewrite loc_valid_ops2_SC in Hcon; eauto.
   -clarify. eauto.
   -rewrite Forall_forall. intros c Hin. simpl.
    inversion Hvs1. inversion Hvs2.
    exploit mops_max_vc_off'.
    { apply H0. }
    { apply H1. }
    instantiate(1:= t). instantiate (1:= C2). instantiate (1:= C1).
    intro Hcltz. rewrite Forall_forall in Hcltz. apply Hcltz in Hin.
    intro Heq. destruct (loc_of c); clarify.
    eapply lt_irrefl. eauto.
   -clarify.
  }
  { apply le_Sn_le. auto. }
  {
    intros (IH1 & IH2); rewrite IH1, IH2.
    specialize (Hmatch1 z); specialize (Hmatch2 z).
    destruct (lt_dec z zt); [| omega ].
    generalize (can_read_thread' _ _ _ _ Hn), (can_read_thread' _ _ _ _ Hn0); clarify.
    generalize ( consistent_app_SC _ _ Hn); intro.
    generalize (can_read_unique(m:=m) (p:= (C1, z)) n (V1 z)); clarify.
    generalize (can_read_unique(m:=m) (p:= (C2, z)) n0 (V2 z)); clarify.
  }
Qed.

Corollary max_vc_vals : forall m C1 C2 vs1 vs2 t V1 V2
  (Hinit1 : forall z, z < zt -> initialized m (C1, z))
  (Hinit2 : forall z, z < zt -> initialized m (C2, z))
  (Hcon : consistent (m ++ mops_max_vc C1 C2 vs1 vs2 t zt))
  (Hvs1 : length vs1 = zt) (Hvs2 : length vs2 = zt)
  (Hmatch1 : clock_match m V1 C1) (Hmatch2 : clock_match m V2 C2),
  vs1 = map V1 (rev (interval 0 zt)) /\ vs2 = map V2 (rev (interval 0 zt)).
Proof.
  intros; eapply max_vc_vals1 with (C1 := C1); eauto.
Qed.


Lemma mops_set_vc_off':
  forall (src tgt : var) (vs: list nat) (t : tid) (n : nat),
  length vs = n ->
  Forall (fun c' : conc_op => let (_, o) := loc_of c' in o < n)
         (mops_set_vc src tgt n t vs).
Proof.
  clarify.
  rewrite Forall_forall. induction vs; clarify.
  destruct H as [Hx|[Hx|Hin]]; clarify.
  apply IHvs in Hin. destruct (loc_of x); clarify.
Qed.
   
Lemma set_vc_vals1: forall m C1 C2 z vs t V1
  (Hinit1: forall z, z < zt -> initialized m (C1, z))
  (Hcon: consistent (m ++mops_set_vc C1 C2 z t vs ))
  (Hvs: length vs =z) (Hz : z <= zt)
  (Hmatch1 : clock_match m V1 C1) ,
  vs = map V1 (rev (interval 0 z)) .
Proof.
  induction z; destruct vs; clarify.
  rewrite rev_app_distr; clarify.
  assert ( consistent (m++ [Read t (C1, z) n])) as Hn.
  { eapply consistent_app_SC; rewrite <- app_assoc; simpl; eauto. }

  exploit (IHz vs); eauto.
  {rewrite read_noop_SC in Hcon; eauto.
   rewrite loc_valid_ops2_SC in Hcon; eauto.
   -clarify. eauto.
   -rewrite Forall_forall. intros c Hin. simpl.
    inversion Hvs.  
    exploit mops_set_vc_off'.
    instantiate(1:= z). instantiate (1:= vs). auto. 
    intro Hcltz. rewrite Forall_forall in Hcltz. apply Hcltz in Hin.
    intro Heq. destruct (loc_of c); clarify.
    eapply lt_irrefl. eauto.
   -clarify.
  }
  { apply le_Sn_le. auto. }
  { 
    intros IH1; rewrite IH1.
    destruct (lt_dec z zt); [| omega ].
    generalize (can_read_thread' _ _ _ _ Hn); clarify.
    generalize ( consistent_app_SC _ _ Hn); intro.
    generalize (can_read_unique(m:=m) (p:= (C1, z)) n (V1 z)); clarify.
    specialize (Hmatch1 z); clarify.
  }
Qed.



Corollary set_vc_vals : forall m C1 C2 vs t V1
  (Hinit1 : forall z, z < zt -> initialized m (C1, z))
  (Hcon : consistent (m ++ mops_set_vc C1 C2 zt t vs))
  (Hvs : length vs = zt)
  (Hmatch1 : clock_match m V1 C1) ,
  vs = map V1 (rev (interval 0 zt)).
Proof.
  intros; eapply set_vc_vals1 with (C1 := C1); eauto.
Qed.

Lemma hb_check_vals1 : forall m C1 C2 z vs1 vs2 t V1 V2
  (Hinit1 : forall z, z < zt -> initialized m (C1, z))
  (Hinit2 : forall z, z < zt -> initialized m (C2, z))
  (Hcon : consistent (m ++ mops_hb_check C1 C2 vs1 vs2 z t))
  (Hvs1 : length vs1 = z) (Hvs2 : length vs2 = z) (Hz : z <= zt)
  (Hmatch1 : clock_match m V1 C1) (Hmatch2 : clock_match m V2 C2)
  (Hle : first_gt vs1 vs2 = None),
  vs1 = map V1 (rev (interval 0 z)) /\ vs2 = map V2 (rev (interval 0 z)).
Proof.
  induction z; destruct vs1, vs2; clarify.
  rewrite rev_app_distr; clarify.
  assert (consistent (m ++ [Read t (C1, z) n])) as Hn.
  { eapply consistent_app_SC; rewrite <- app_assoc; simpl; eauto. }
  assert (consistent (m ++ [Read t (C2, z) n0])) as Hn0.
  { rewrite read_noop_SC in Hcon; auto.
    eapply consistent_app_SC; rewrite <- app_assoc; simpl; eauto. }
  exploit (IHz vs1 vs2); eauto.
  { do 2 (rewrite read_noop_SC in Hcon; eauto). }
  { omega. }
  intros (IH1 & IH2); rewrite IH1, IH2.
  specialize (Hmatch1 z); specialize (Hmatch2 z).
  destruct (lt_dec z zt); [|omega].
  generalize (can_read_thread' _ _ _ _ Hn), (can_read_thread' _ _ _ _ Hn0);
    clarify.
  generalize (consistent_app_SC _ _ Hn); intro.
  generalize (can_read_unique(m := m)(p := (C1, z)) n (V1 z)); clarify.
  generalize (can_read_unique(m := m)(p := (C2, z)) n0 (V2 z)); clarify.
Qed.  

Corollary hb_check_vals : forall m C1 C2 vs1 vs2 t V1 V2
  (Hinit1 : forall z, z < zt -> initialized m (C1, z))
  (Hinit2 : forall z, z < zt -> initialized m (C2, z))
  (Hcon : consistent (m ++ mops_hb_check C1 C2 vs1 vs2 zt t))
  (Hvs1 : length vs1 = zt) (Hvs2 : length vs2 = zt)
  (Hmatch1 : clock_match m V1 C1) (Hmatch2 : clock_match m V2 C2)
  (Hle : first_gt vs1 vs2 = None),
  vs1 = map V1 (rev (interval 0 zt)) /\ vs2 = map V2 (rev (interval 0 zt)).
Proof.
  intros; eapply hb_check_vals1 with (C1 := C1); eauto.
Qed.
  
Typeclasses eauto := 5.

Lemma clock_match_value: forall m vct ct t v x
  (Hmatch: clock_match (m++[Read t (ct, x) v]) vct ct) (Hinit: initialized m (ct,x))
  (Hx : x < zt),                         v = vct x.
Proof.
  intros.
  unfold clock_match in *. specialize (Hmatch x). clarify.
  assert(Hcon: consistent (m ++ [Read t (ct, x) v])).
    eapply consistent_app_SC. eauto.
  assert(Hcan_read1: can_read m (ct, x) v).
    unfold can_read, consistent, SC in *. setoid_rewrite lower_app in Hcon. rewrite lower_single in Hcon. unfold can_read, consistent, SC.  setoid_rewrite lower_app. rewrite lower_single.
    clarify. 
  assert(Hcan_read2: can_read m (ct, x) (vct x)).
    unfold can_read in Hmatch1. rewrite <- app_assoc in Hmatch1.
    setoid_rewrite reads_noops_SC in Hmatch1; auto.
  apply can_read_unique with (m:= m) (p:=(ct,x)); auto.
  eapply consistent_app_SC; eauto.
Qed.

Lemma clock_match_nomod: forall m1 m2 vct ct
  (Hmatch_m1: clock_match m1 vct ct) (Hcon: consistent (m1++m2) ) (Hprog: Forall prog_op m2)
   (Hnmods: Forall (fun c => match c with | Write _ (x,o) _ => ct <> x
     | ARW _ (x,o) _ _=> ct <> x | _ => True end)  m2),     clock_match (m1++m2) vct ct.
Proof.
  induction m2; intros; auto.
  -rewrite app_nil_r in *. auto.
  -unfold clock_match. intros.
   inversion Hnmods; clarify.
   assert(Hcon_a : consistent (m1++[a])).
   eapply consistent_app_SC. rewrite <- split_app. eauto.
   assert(Himpl: forall x,  (fun x0 : conc_op =>
          match x0 with
          | Write _ (p, _) _ => ct <> p
          | ARW _ (p, _) _ _ => ct <> p
          | _ => True
          end) x -> (forall t, (fun x0 : conc_op => 
          match x0 with
          | Write _ x _ => (ct, t) <> x
          | ARW _ x _ _ => (ct, t) <> x
          | _ => True
          end) x) ).
     intros x0 Himpl0. destruct x0; clarify; intro Heq; clarify.
     
   destruct (lt_dec t zt); clarify.
   unfold clock_match in Hmatch_m1. specialize(Hmatch_m1 t).  
   +split.
    *apply can_read_SC;clarify.
     apply Forall_cons.
       destruct a; clarify;
       intro Heq; clarify.
       eapply Forall_impl.
       {intros. apply Himpl. apply H.  }
       {auto. }
    *apply can_write_SC;clarify.
   +unfold clock_match in Hmatch_m1. specialize(Hmatch_m1 t).
    clarify.
Qed.



Lemma can_read_written_SC: forall m t p v (Hcon: consistent (m++[Write t p v])),
                             can_read (m++[Write t p v]) p v.
Proof.
  intros.
  unfold can_read. rewrite <- app_assoc. unfold consistent, SC, seq_con in *. repeat rewrite lower_app in *. repeat rewrite lower_single in *. clarify. rewrite read_written; auto.
  rewrite lower_app, lower_single in Hcon. clarify.
Qed.


Lemma clock_match_mods: forall m vr r t t' v x (Hclock_match_m: clock_match m (vr x) (r+x))
                              (Hcon: consistent (m++[Write t' (r+x,t ) v])) (Ht: t < zt),
                          clock_match (m++[Write t' (r+x,t) v]) (upd vr x (upd (vr x) t v) x) (r+x).
Proof.
  intros.
  unfold clock_match in *. intros t0. specialize (Hclock_match_m t0).
  destruct (lt_dec t0 zt); clarify.
  -split.
   +destruct (eq_dec t t0) eqn: Heq; clarify.
    *unfold upd. clarify.
     apply can_read_written_SC; auto.
    *unfold upd. clarify.
     apply can_read_SC; eauto.
     { rewrite Forall_forall. intros c Hin. clarify. }
     { rewrite Forall_forall. intros c Hin. clarify.  intro Heq'.
       inversion Heq'; clarify. }
   +apply can_write_SC; auto.
    rewrite Forall_forall; intros x0 Hin; inversion Hin; clarify.
  -unfold upd; clarify.
Qed.



Definition clock_match_z m V x z:= forall t,
  if lt_dec t z then can_read m (x, t) (V t) /\ can_write m (x, t)
  else True.

   
Lemma clock_match_mods_z: forall m vr r t t' v x f z (Hclock_match_m: clock_match_z m (vr x) (r+x) z)
                              (Hcon: consistent (m++[Write t' (r+x,t ) v])) (Ht: t < z)
                          (* (Hbounded: bounded f z)*)
                           (Hf: forall y, y< z -> f y = (upd vr x (upd (vr x) t v) x) y),
                           clock_match_z (m++[Write t' (r+x,t) v]) f (r+x) z.
Proof.
  intros.
  unfold clock_match in *. intros t0. specialize (Hclock_match_m t0).
  destruct (lt_dec t0 z); clarify.
  -split.
   +destruct (eq_dec t t0) eqn: Heq; clarify.
    *rewrite Hf; auto.
     unfold upd. clarify.
     apply can_read_written_SC; auto.
    *rewrite Hf; auto.
     unfold upd. clarify.
     apply can_read_SC; eauto.
     { rewrite Forall_forall. intros c Hin. clarify. }
     { rewrite Forall_forall. intros c Hin. clarify.  intro Heq'.
       inversion Heq'; clarify. }
   +apply can_write_SC; auto.
    rewrite Forall_forall; intros x0 Hin; inversion Hin; clarify.
Qed.


Lemma clock_match_nomod_z: forall m1 m2 vct ct z
  (Hmatch_m1: clock_match_z m1 vct ct z) (Hcon: consistent (m1++m2) ) (Hprog: Forall prog_op m2) (Hz: z <> 0)
   (Hnmods: Forall (fun c => match c with | Write _ (x,o) _ => ct <> x
     | ARW _ (x,o) _ _=> ct <> x | _ => True end)  m2),     clock_match_z (m1++m2) vct ct z.
Proof.
  induction m2; intros; auto.
  -rewrite app_nil_r in *. auto.
  -unfold clock_match_z. intros.
   inversion Hnmods; clarify.
   assert(Hcon_a : consistent (m1++[a])).
   eapply consistent_app_SC. rewrite <- split_app. eauto.
   assert(Himpl: forall x,  (fun x0 : conc_op =>
          match x0 with
          | Write _ (p, _) _ => ct <> p
          | ARW _ (p, _) _ _ => ct <> p
          | _ => True
          end) x -> (forall t, (fun x0 : conc_op => 
          match x0 with
          | Write _ x _ => (ct, t) <> x
          | ARW _ x _ _ => (ct, t) <> x
          | _ => True
          end) x) ).
     intros x0 Himpl0. destruct x0; clarify; intro Heq; clarify.
     
   destruct (lt_dec t z); clarify.
   unfold clock_match_z in Hmatch_m1. specialize(Hmatch_m1 t).  
   +split.
    *apply can_read_SC;clarify.
     apply Forall_cons.
       destruct a; clarify;
       intro Heq; clarify.
       eapply Forall_impl.
       {intros. apply Himpl. apply H.  }
       {auto. }
    *apply can_write_SC;clarify.
Qed.

Lemma clock_match_Sz_z : forall m V x z, clock_match_z m V x (S z)-> clock_match_z m V x z.
Proof.
  unfold clock_match_z, bounded; intros.
  specialize (H t); clarify.
  assert(Hlt:= l). apply lt_S in Hlt. clarify.
Qed.

Lemma clock_match_z_Sz: forall m V x z, can_read m (x, z) (V z) -> can_write m (x, z)-> clock_match_z m V x z -> clock_match_z m V x (S z).
Proof.
  unfold clock_match_z. clarify.
  specialize(H1 t).
  destruct (lt_dec t z); clarify.
  assert(Htz: t=z).
    omega.
  rewrite Htz.
  split; auto.
Qed.

Lemma clock_match_decompose: forall m V x z, z <= zt-> clock_match m V x -> clock_match_z m V x z /\ bounded V zt.
Proof.
  unfold clock_match, clock_match_z, bounded. clarify.
  split; clarify;
  specialize(H0 t); clarify. assert(Hlt:=l). apply lt_le_trans with (p:=zt) in Hlt; clarify.
Qed.

Lemma bounded_z_le: forall V z1 z2, z1 <=z2 -> bounded V z1 -> bounded V z2.
Proof.
  unfold bounded. clarify.
  specialize(H0 t). destruct (lt_dec t z1); clarify.
  apply lt_le_trans with (p:=z2) in l; clarify.
Qed.
(*
Lemma clock_match_max : forall m VC1 VC2 vc1 vc2 t1 t2 t z
  (Hmatch1: clock_match_z m (vc1 t1) (VC1 + t1) (S z) ) (Hmatch2: clock_match_z m (vc2 t2) (VC2 + t2) (S z))  (Hcon: consistent (m ++ mops_max (VC1+t1, z) (VC2+t2, z) (vc1 t1 z) (vc2 t2 z) t)), 
  clock_match_z (m ++ mops_max (VC1+t1, z) (VC2+t2, z) (vc1 t1 z) (vc2 t2 z) t) (upd vc2 t2 (vc_join (vc2 t2) (vc1 t1)) t2) 
                (VC2 + t2) (S z) .
Proof.
  unfold mops_max. clarify.
  do 2 rewrite split_app.
  eapply clock_match_mods_z; eauto.
  instantiate(1:=vc2).
  -rewrite <- app_assoc.
   apply clock_match_nomod_z; auto.
   +eapply consistent_app_SC; eauto.
    do 2 rewrite <- app_assoc. simpl. eauto.
   +rewrite Forall_forall. intros c Hin. inversion Hin; clarify.
   +rewrite Forall_forall. intros c Hin. inversion Hin; clarify.
  -do 2 rewrite <- app_assoc. simpl. eauto.
  -apply clock_match_z_bounded in Hmatch2.
   unfold bounded, upd, vc_join in *. clarify.
   specialize (Hmatch2 t0 H). apply clock_match_z_bounded in Hmatch1.
   specialize (Hmatch1 t0 H). rewrite Hmatch2, Hmatch1. auto.
  -unfold vc_join, upd. clarify.
   destruct y eqn:Hy; clarify.
   destruct (le_dec (vc2 t2 0) (vc1 t1 0)); clarify.
   rewrite max_r, max_l; auto.
   apply not_le in n. apply gt_le_S in n.  apply le_Sn_le in n.
   rewrite max_l, max_r; auto.
   inversion H. clarify. apply le_n_0_eq in H1.  inversion H1. *)
Lemma map_same_bounded : forall (X:Type) (f g: nat -> X ) z
  (Hsame_bounded : forall x, x < z -> f x = g x), map f (interval 0 z) = map g (interval 0 z ).                                
Proof.
  induction z; clarify.
  do 2 rewrite map_app. clarify.
  rewrite IHz, Hsame_bounded; auto.
Qed.

Lemma max_comm: forall  a b, Peano.max a b = Peano.max b a.
Proof.
  clarify. destruct (le_dec a b); clarify.
  rewrite max_r; auto. rewrite max_l; auto.
  apply not_le in n. rewrite max_l; try omega. rewrite max_r; omega.
Qed.

Lemma clock_match_iff_z : forall m v V ,
  clock_match m v V <-> clock_match_z m v V zt /\ bounded v zt.                           
Proof.
  clarify.
  split; clarify.
  -split; auto.
   +unfold clock_match_z, clock_match in *.
    clarify. specialize(H t). clarify.
   +eapply clock_match_bounded. eauto.
  -unfold clock_match, clock_match_z in *. clarify.
   specialize(H1 t). clarify.
Qed.


Lemma clock_match_z_max_vc : forall m VC1 VC2 vc1 vc2 t1 t2 t z
  (Hmatch1: clock_match_z m (vc1 t1) (VC1+ t1) z)
  (Hmatch2: clock_match_z m (vc2 t2) (VC2 + t2) z)
  (Hdistinct:  VC1 + t1 <> VC2 + t2)
  (*(Hbounded1: bounded (vc1 t1) z) (Hbounded2: bounded (vc2 t2) z)*)
  (Hcon: consistent (m ++ mops_max_vc (VC1+t1) (VC2 + t2) (map (vc1 t1) (rev (interval 0 z))) (map (vc2 t2) (rev (interval 0 z ))) t z )) (* (Hz: z <> 0)  (Ht2: t2 < z)*),
                             clock_match_z (m ++ mops_max_vc (VC1+t1) (VC2+t2) (map (vc1 t1) (rev (interval 0 z))) (map (vc2 t2) (rev (interval 0 z))) t z) (upd vc2 t2 (vc_join (vc2 t2) (vc1 t1)) t2) (VC2+t2) z.
Proof.
  intros. generalize dependent m. generalize dependent vc1. generalize dependent vc2. 
  induction z; clarify.
  rewrite rev_unit in *. clarify.
  do 3 rewrite split_app in *.
  assert( consistent (m ++ Read t (VC1 + t1, z) (vc1 t1 z)
            :: Read t (VC2 + t2, z) (vc2 t2 z)
            :: [Write t (VC2 + t2, z) (Peano.max (vc1 t1 z) (vc2 t2 z))])) as Hcon1.
    apply consistent_app_SC in Hcon.
    do 2 rewrite <- app_assoc in Hcon. clarify.
  assert(  clock_match_z
     (((m ++ [Read t (VC1 + t1, z) (vc1 t1 z)]) ++
       [Read t (VC2 + t2, z) (vc2 t2 z)]) ++
      [Write t (VC2 + t2, z) (Peano.max (vc1 t1 z) (vc2 t2 z))] )
     (vc1 t1) (VC1 + t1) 
     (S z)) as Hm1.
  {
    do 2 rewrite <-app_assoc.  simpl.
    eapply clock_match_nomod_z; eauto.
    rewrite Forall_forall. intros c Hin. destruct Hin as [?|[?|?]]; clarify.
  }
  assert(  clock_match_z
     (((m ++ [Read t (VC1 + t1, z) (vc1 t1 z)]) ++
       [Read t (VC2 + t2, z) (vc2 t2 z)]) ++
      [Write t (VC2 + t2, z) (Peano.max (vc1 t1 z) (vc2 t2 z))] )
     (upd vc2 t2 (upd (vc2 t2) z (Peano.max (vc1 t1 z) (vc2 t2 z))) t2) (VC2 + t2) 
     (S z)) as Hm2.
  {
    eapply clock_match_mods_z; eauto.
    -rewrite <-app_assoc. simpl.
     apply clock_match_nomod_z; eauto.
     +eapply consistent_app_SC; eauto.
      instantiate(1:=[Write t (VC2 + t2, z) (Peano.max (vc1 t1 z) (vc2 t2 z))]).
      rewrite <- app_assoc. clarify.
     +rewrite Forall_forall. intros c Hin. inversion Hin; clarify.
    -do 2 rewrite <- app_assoc. clarify.
    
  }
  assert(Hm2z:=Hm2). assert(Hm1z:=Hm1).
  apply clock_match_Sz_z in Hm2z. apply clock_match_Sz_z in Hm1z.
 
  assert(  map (vc2 t2) (rev (interval 0 z)) = map
                (upd vc2 t2
                   (upd (vc2 t2) z (Peano.max (vc1 t1 z) (vc2 t2 z))) t2)
                (rev (interval 0 z))) as Hmap.
  {
    do 2 rewrite map_rev.
    rewrite map_same_bounded with (g:=(upd vc2 t2 (upd (vc2 t2) z (Peano.max (vc1 t1 z) (vc2 t2 z))) t2)); clarify.
    unfold upd. clarify. apply lt_irrefl in H. clarify.
  }
  rewrite Hmap in Hcon. 
  specialize(IHz _ _ _ Hm1z Hm2z Hcon). rewrite <- Hmap in IHz.
  assert((upd
             (upd vc2 t2 (upd (vc2 t2) z (Peano.max (vc1 t1 z) (vc2 t2 z))))
             t2
             (vc_join
                (upd vc2 t2
                   (upd (vc2 t2) z (Peano.max (vc1 t1 z) (vc2 t2 z))) t2)
                (vc1 t1)) t2) = upd vc2 t2 (vc_join (vc2 t2) (vc1 t1)) t2) as Hfun.
  {
    unfold upd, vc_join. clarify. apply functional_extensionality. clarify.
    destruct (le_dec (vc1 t1 x) (vc2 t2 x)); clarify.
    -rewrite max_r with (m:=(vc2 t2 x)); auto.
    -apply not_le in n. rewrite max_r; auto.
     +rewrite max_r; auto. omega.
     +rewrite max_l; auto. omega.
  }
  setoid_rewrite Hfun in IHz.
  apply clock_match_z_Sz; auto.
  -apply can_read_SC; auto.
   +unfold vc_join, upd. clarify.
    rewrite max_comm.
    apply can_read_written_SC; auto.
    rewrite max_comm. do 2 rewrite <- split_app. auto.
   +rewrite Hmap; auto.
   +rewrite Forall_forall. clarify. apply in_mops_max_vcn in H.
    destruct x; clarify.
    destruct x; clarify.
    intro Heq. inversion Heq; clarify. apply (lt_irrefl n). auto.
  -do 3 rewrite <- split_app.  
   apply can_write_SC; auto.
   +unfold clock_match_z in Hmatch2. specialize(Hmatch2 z). clarify.
    contradiction n. omega.
   +do 3 rewrite split_app.  rewrite Hmap . auto.
   +rewrite Forall_forall. intros c Hin. 
    destruct Hin as [Hin | [Hin|[Hin|Hin]]]; clarify.
    apply in_mops_max_vc in Hin. destruct c; clarify. auto.
Qed.



Lemma clock_match_max_vc : forall m VC1 VC2 vc1 vc2 t1 t2 t 
  (Hmatch1: clock_match m (vc1 t1) (VC1+ t1) )
  (Hmatch2: clock_match m (vc2 t2) (VC2 + t2) )
  (Hdistinct:  VC1 + t1 <> VC2 + t2)
  (Hcon: consistent (m ++ mops_max_vc (VC1+t1) (VC2 + t2) (map (vc1 t1) (rev (interval 0 zt))) (map (vc2 t2) (rev (interval 0 zt ))) t zt )) ,
                             clock_match (m ++ mops_max_vc (VC1+t1) (VC2+t2) (map (vc1 t1) (rev (interval 0 zt))) (map (vc2 t2) (rev (interval 0 zt))) t zt) (upd vc2 t2 (vc_join (vc2 t2) (vc1 t1)) t2) (VC2+t2).
Proof.
  clarify. rewrite clock_match_iff_z in *. split; clarify.
  -apply clock_match_z_max_vc; auto.
  -unfold bounded, upd, vc_join in *; clarify.
   rewrite Hmatch12, Hmatch22; auto.
Qed.
  
Lemma in_mops_set_vc': forall n c vc1 vc2 vs t
  (Hin: In c (mops_set_vc vc1 vc2 n t vs)) ,
match c with
    | Read _ _ _ => True
    | Write _ (x,o) _ => x=vc2 /\ o < n 
    | _ => False
  end.
Proof.
  induction n; intros; destruct vs; clarify; destruct c; clarify;
    try solve [exploit IHn; eauto].
  exploit IHn; eauto.
  destruct x; clarify.
Qed.

Lemma clock_match_inc_vc : forall m VC1 vc1 t1 t v
  (Hmatch: clock_match m (vc1 t1) (VC1 + t1)) (Hinit: initialized m (VC1+ t1,t))
  (Ht: t < zt)
  (Hcon: consistent (m ++ mops_inc_vc (VC1 + t1) v t )),
                               clock_match (m ++ mops_inc_vc (VC1 + t1) v t) (upd  vc1 t1 (vc_inc t (vc1 t1)) t1)  (VC1 + t1).
Proof.
  intros. unfold mops_inc_vc; clarify.
  rewrite split_app.
  assert( clock_match (m ++ [Read t (VC1 + t1, t) v]) (vc1 t1) (VC1 + t1)) as Hcmr.
  {
    apply clock_match_nomod; auto.
    -unfold mops_inc_vc in *; clarify.
     eapply consistent_app_SC; eauto. rewrite <- app_assoc. simpl. eapply Hcon.
    -rewrite Forall_forall. clarify.
  }
  assert( v= vc1 t1 t) as Hv.
  {
    eapply clock_match_value; eauto.
  } 
  assert( vc_inc t (vc1 t1) = upd (vc1 t1) t (v+1) ) as Hvc1.
  {
    unfold vc_inc, upd; clarify.
    apply functional_extensionality. clarify. destruct (eq_dec x t); clarify.
    omega.
  }
  rewrite Hvc1.
  apply clock_match_mods; auto.
  rewrite <- app_assoc. clarify.
Qed.
  


Lemma clock_match_inc_vc' : forall m VC1 vc1 t1 t t' v
  (Hmatch: clock_match m (vc1 t1) (VC1 + t1)) (Hinit: initialized m (VC1+ t1,t))
  (Ht: t < zt)
  (Hcon: consistent (m ++ mops_inc_vc' (VC1 + t1) v t' t )),
                               clock_match (m ++ mops_inc_vc' (VC1 + t1) v t' t) (upd  vc1 t1 (vc_inc t (vc1 t1)) t1)  (VC1 + t1).
Proof.
  intros. unfold mops_inc_vc'; clarify.
  rewrite split_app.
  assert( clock_match (m ++ [Read t' (VC1 + t1, t) v]) (vc1 t1) (VC1 + t1)) as Hcmr.
  {
    apply clock_match_nomod; auto.
    -unfold mops_inc_vc' in *; clarify.
     eapply consistent_app_SC; eauto. rewrite <- app_assoc. simpl. eapply Hcon.
    -rewrite Forall_forall. clarify.
  }
  assert( v= vc1 t1 t) as Hv.
  {
    eapply clock_match_value; eauto.
  } 
  assert( vc_inc t (vc1 t1) = upd (vc1 t1) t (v+1) ) as Hvc1.
  {
    unfold vc_inc, upd; clarify.
    apply functional_extensionality. clarify. destruct (eq_dec x t); clarify.
    omega.
  }
  rewrite Hvc1.
  apply clock_match_mods; auto.
  rewrite <- app_assoc. clarify.
Qed.

Lemma clock_match_z_set_vc : forall m VC1 VC2 vc1 vc2 t1 t2 t z
  (Hmatch1: clock_match_z m (vc1 t1) (VC1+ t1) z)
  (Hmatch2: clock_match_z m (vc2 t2) (VC2+ t2) z)
  (Hcon: consistent (m ++ mops_set_vc (VC1+t1) (VC2 + t2) z t (map (vc1 t1) (rev (interval 0 z))) )) (Hdistinct: VC1 + t1 <> VC2 + t2),  
                             clock_match_z (m ++ mops_set_vc (VC1+t1) (VC2+t2) z t (map (vc1 t1) (rev (interval 0 z)))) (upd vc2 t2 (vc1 t1) t2) (VC2+t2) z.
Proof.
  intros. generalize dependent m. generalize dependent vc1. generalize dependent vc2. 
  induction z; clarify.
  rewrite rev_unit in *. clarify.
  do 2 rewrite split_app in *.
  assert( consistent (m ++ Read t (VC1 + t1, z) (vc1 t1 z)
            :: [Write t (VC2 + t2, z) (vc1 t1 z)])) as Hcon1.
    apply consistent_app_SC in Hcon.
    rewrite <- app_assoc in Hcon. clarify.
  assert(  clock_match_z
     ((m ++ [Read t (VC1 + t1, z) (vc1 t1 z)]) ++
      [Write t (VC2 + t2, z) (vc1 t1 z)] )
     (vc1 t1) (VC1 + t1) 
     (S z)) as Hm1.
  {
    rewrite <-app_assoc.  simpl.
    eapply clock_match_nomod_z; eauto.
    rewrite Forall_forall. intros c Hin. destruct Hin as [?|[?|?]]; clarify.
  }
  assert(  clock_match_z
     ((m ++ [Read t (VC1 + t1, z) (vc1 t1 z)]) ++
      [Write t (VC2 + t2, z) (vc1 t1 z) ] )
     (upd vc2 t2 (upd (vc2 t2) z (vc1 t1 z) ) t2) (VC2 + t2) 
     (S z)) as Hm2.
  {
    eapply clock_match_mods_z; eauto.
    -apply clock_match_nomod_z; eauto.
     +eapply consistent_app_SC; eauto.
      instantiate(1:=[Write t (VC2 + t2, z) (vc1 t1 z) ]).
      rewrite <- app_assoc. clarify.
     +rewrite Forall_forall. intros c Hin. inversion Hin; clarify.
    -rewrite <- app_assoc. clarify.
    
  }
  assert(Hm2z:=Hm2). assert(Hm1z:=Hm1).
  apply clock_match_Sz_z in Hm2z. apply clock_match_Sz_z in Hm1z.
  specialize(IHz _ _ _ Hm1z Hm2z Hcon). unfold upd in *; clarify.

  apply clock_match_z_Sz; auto.
  -apply can_read_SC; auto.
   +apply can_read_written_SC; auto.
    rewrite <- split_app. auto.
   +rewrite Forall_forall. clarify. apply in_mops_set_vc' in H.
    destruct x; clarify.
    destruct x; clarify.
    intro Heq. inversion Heq; clarify. apply (lt_irrefl n). auto.
  -do 2 rewrite <- split_app.  
   apply can_write_SC; auto.
   +unfold clock_match_z in Hmatch2. specialize(Hmatch2 z). clarify.
    contradiction n. omega.
   +do 2 rewrite split_app.   auto.
   +rewrite Forall_forall. intros c Hin. 
    destruct Hin as [Hin | [Hin|Hin]]; clarify.
    apply in_mops_set_vc' in Hin. destruct c; clarify. 
Qed.


Lemma clock_match_set_vc : forall m VC1 VC2 vc1 vc2 t1 t2 t 
  (Hmatch1: clock_match m (vc1 t1) (VC1+ t1) )
  (Hmatch2: clock_match m (vc2 t2) (VC2+ t2) )
  (Hcon: consistent (m ++ mops_set_vc (VC1+t1) (VC2 + t2) zt t (map (vc1 t1) (rev (interval 0 zt))) )) (Hdistinct: VC1 + t1 <> VC2 + t2),  
                             clock_match (m ++ mops_set_vc (VC1+t1) (VC2+t2) zt t (map (vc1 t1) (rev (interval 0 zt)))) (upd vc2 t2 (vc1 t1) t2) (VC2+t2).
Proof.
  clarify. rewrite clock_match_iff_z in *; split; clarify.
  -apply clock_match_z_set_vc; auto.
  -unfold bounded, upd in *; clarify.
Qed.
(*
Lemma instrument_sim_safe2 : forall (*P*) P1 P2 G1 G2 t (*h*)
  (Hfresh : fresh_tmps P1) (Hlocs : safe_locs P1)
  (Ht : Forall (fun e => fst e < zt) P1) (Hdistinct: distinct P2)
  (HPsim : state_sim P1 P2) (HGsim : env_sim G1 G2)
  m (*(Hroot : exec_star (Some (init_state P)) init_env h m (Some P1) G1)*)
  (Hinit : forall p, meta_loc p -> initialized m p)
  o2 c2 P2' G2' (Hstep : iexec P2 G2 t o2 c2 P2' G2')
  (Hcon : consistent (m ++ c2)) s (Hs : clocks_sim m s),
  exists o c P1' G1', exec P1 G1 t o c (Some P1') G1' /\
    state_sim P1' P2' /\ env_sim G1' G2' /\ consistent (m ++ opt_to_list c) /\
    mem_sim c c2 /\
        exists s', step_star s (opt_to_list o) s' /\
                   clocks_sim (m ++ c2) s'.
Proof.
  intros.
  destruct s as (((vc, vl), vr), vw);clarify.
  destruct Hs as [ Hs_c (Hs_l,Hs_rw)].
  assert (Hemc: exists o c P1' G1', exec P1 G1 t o c (Some P1') G1' /\mem_sim c c2 /\ consistent (m ++ opt_to_list c)  /\ exists s', step_star (vc,vl,vr,vw) (opt_to_list o) s' /\
                   clocks_sim (m ++ c2) s').
   inversion Hstep; clarify; exploit Forall2_app_inv_r; eauto;
   intros (P0' & P3' & HP0 & Hrest & HP1);
   inversion Hrest as [|(tx, [|i ?]) ? ? ? [? Hi] HP3]; clarify.
   - (*assign*)
     exploit (instrument_incom (Assign a e)); simpl; eauto; clarify.
     do 4 eexists. split;[|split;[|split]].
     +apply exec_assign. eauto.
     +unfold mem_sim. intros. simpl. split; clarify.
     +simpl. auto.
     +exists (vc,vl,vr,vw). simpl. split.
      *apply ss_refl.
      *rewrite app_nil_r. unfold clocks_sim. clarify.
     
   -(*load*) 
     exploit (instrument_incom (Load a (x, o))).
     { simpl; rewrite <- app_assoc; simpl; eauto. }
     clarify.
     do 4 eexists. split;[|split;[|split]].
     +apply exec_load. eauto.
     +unfold mem_sim. intros. simpl. split; clarify.
      { split.
        - right.
          rewrite in_app; right; simpl; eauto.
        - setoid_rewrite Forall_app in Hlocs. clarify. inversion Hlocs2; clarify. inversion H2; clarify.
      }  
      { left.
        setoid_rewrite Forall_app in Hlocs. clarify. inversion Hlocs2; clarify. 
        inversion H4; clarify.
        rewrite Forall_app in Ht. clarify. inversion Ht2; clarify.
        rewrite in_app in H1; simpl in H1.
        destruct H1 as [? | [? | [? | [? | [? | ?]]]]]; clarify.
        - contradiction H2. unfold meta_loc. simpl. repeat right. omega.
        - contradiction H2. eapply mops_hb_check_meta; eauto.
        - contradiction H2. unfold meta_loc. simpl. omega.
        - contradiction H2. unfold meta_loc. simpl. right; right; left; omega.
        - contradiction H2. unfold meta_loc. simpl. repeat right. omega. }
     + 
      assert(Hlist_silly1: forall (X:Type) (a b c d e: X) (l1 l2 l3 l4: list X), 
               l1++a::l2++[b;c;d;e]=(l1++[a])++(l2++[b;c])++[d;e]).
        intros. simpl. do  2 rewrite app_assoc. clarify. 
        rewrite split_app. rewrite app_assoc. do 2 rewrite split_app. 
        repeat rewrite <- app_assoc. simpl. auto.
      rewrite Hlist_silly1 in Hcon; auto. rewrite loc_valid_ops_SC in Hcon.
      {
        inversion Hcon; clarify. 
        rewrite loc_valid_ops2_SC in Hcon2.
        -inversion Hcon2; clarify. rewrite <- app_assoc in Hcon22. rewrite loc_valid_ops_SC in Hcon22.
         +inversion Hcon22; clarify.
         +rewrite Forall_forall; clarify.
          rewrite Forall_forall; clarify.
          intro Heq. setoid_rewrite Forall_app in Hlocs. clarify. inversion Hlocs2; clarify. inversion H4; clarify.
          contradiction H81; repeat right.
          rewrite H1; clarify; omega.
         + constructor; clarify.
         + constructor; clarify.
        -rewrite Forall_forall; clarify.
         intros Heq. setoid_rewrite Forall_app in Hlocs. clarify. inversion Hlocs2; clarify. inversion H4; clarify.
          contradiction H81; repeat right; simpl.
          rewrite <- H1; omega.
        - simpl; auto.
        - constructor; clarify.
      }
      { rewrite Forall_forall; intros ? Hin; clarify.
        rewrite Forall_forall; intros ? Hin2; clarify.
        setoid_rewrite Forall_app in Hlocs. clarify. inversion Hlocs2; clarify. inversion H2; clarify.
        rewrite Forall_app in Ht. inversion Ht; clarify. inversion Ht2; clarify.
        destruct Hin2.
        - subst; simpl; intro; contradiction H41; rewrite H.
          rewrite in_app in Hin; destruct Hin as [? | [? | ?]]; clarify.
          + eapply mops_hb_check_meta; eauto.
          + left; simpl; omega.
          + right; right; left; simpl; omega.
        - subst; simpl; intro.
          rewrite in_app in Hin; destruct Hin as [? | [? | ?]]; clarify.
          + apply in_mops_hb_check in H1. destruct x0; clarify. 
            destruct H1.
            * exploit Hmetalocs_disjoint_WX; eauto.
            * exploit Hmetalocs_disjoint_CX; eauto.
          + exploit Hmetalocs_disjoint_CX; eauto.
          + exploit Hmetalocs_disjoint_RX; eauto. }
     { rewrite Forall_app; split; auto; repeat constructor; simpl; auto. }
     { repeat constructor; simpl; auto. }
     + setoid_rewrite Forall_app in Hlocs; destruct Hlocs as (_ & Hlocs).
       inversion Hlocs as [|?? Hi ?]; inversion Hi; clarify.
       rewrite Forall_app in Ht; destruct Ht as (_ & Ht).
       inversion Ht; clarify.
       assert(Hsilly: (m ++
            Acq t (X' + x)
            :: mops_hb_check (W' + x) (C' + t) vs1 vs2 zt t ++
               [Read t (C' + t, t) vt; Write t (R' + x, t) vt;
               Read t (x, o) v; Rel t (X' + x)]) = (m ++
            Acq t (X' + x)
            :: mops_hb_check (W' + x) (C' + t) vs1 vs2 zt t ++
               [Read t (C' + t, t) vt; Write t (R' + x, t) vt;
                Read t (x, o) v])++ [Rel t (X' + x)] ).
         symmetry. rewrite <- app_assoc. clarify. rewrite split_app. rewrite app_assoc. rewrite app_assoc.  symmetry.
         rewrite split_app; rewrite app_assoc. do 3 rewrite split_app. repeat rewrite <- app_assoc. clarify.
         assert(Hhb : consistent (m ++ mops_hb_check (W' + x) (C' + t) vs1 vs2 zt t)).
         {
         setoid_rewrite Hsilly in Hcon. apply consistent_app_SC in Hcon.
         rewrite loc_valid_ops2_SC in Hcon; clarify.
         rewrite app_assoc in Hcon1; generalize (consistent_app_SC _ _ Hcon1); auto.
         rewrite Forall_app. split; rewrite Forall_forall; clarify.
         apply in_mops_hb_check in H. destruct x0; clarify. destruct x0; clarify.
         destruct H.
           rewrite H. intro Hwrong. inversion Hwrong. specialize (Hmetalocs_disjoint_WX H52 H52). clarify.
           rewrite H. intro Hwrong. inversion Hwrong. specialize (Hmetalocs_disjoint_CX H3 H52). clarify.
         destruct H as [?|[?|[?|?]]]; clarify.
           intro Hwrong. inversion Hwrong. specialize (Hmetalocs_disjoint_CX H3 H52). clarify.
           intro Hwrong. inversion Hwrong. specialize (Hmetalocs_disjoint_RX H52 H52). clarify.
           intro Hwrong. inversion Hwrong. clarify. contradiction H51. unfold meta_loc. clarify. rewrite H2. repeat right. omega.
           rewrite Forall_forall. intros. rewrite in_app in H. inversion H; clarify. 
           apply in_mops_hb_check in H2. destruct x0; clarify.
           destruct H2 as [? |[?|?]]; clarify.
         }
       assert(Hs_rw':= Hs_rw).
       specialize (Hs_rw x); clarify.
       exploit hb_check_vals; try apply Hhb; eauto.
       { intros; apply Hinit; unfold meta_loc; simpl; omega. }
       { intros; apply Hinit; unfold meta_loc; simpl; omega. }
       clarify; eexists; simpl; split. 
       * eapply ss_step; eauto.
         eapply read_upd; eauto.
         eapply first_gt_vc_le; eauto.
         apply ss_refl.
       * unfold clocks_sim. split;[|split;[|split]]; intros;clarify.
        {apply clock_match_nomod; auto.
         rewrite Forall_forall. intros ? Hin. inversion Hin; clarify. 
         rewrite in_app in H2. destruct H2 as [Hin1 | Hin2]; clarify.
         -apply in_mops_hb_check in Hin1. destruct x0; clarify.
         -destruct Hin2 as [?|[?|[?|?]]]; clarify.
         -rewrite Forall_forall. intros x0 Hin. destruct x0; clarify.
          +rewrite in_app in Hin. destruct Hin as [Hin | [Hin | [Hin |Hin]]]; clarify.
           *apply in_mops_hb_check in Hin. clarify.
           *inversion Hin; clarify.
          +destruct Hin as [Hin | Hin]; clarify.
           *inversion Hin; clarify.
           *rewrite in_app in Hin. destruct Hin as [Hin | [Hin | [Hin | Hin ]]]; clarify.
            {apply in_mops_hb_check in Hin. clarify. }
            {inversion Hin; clarify. }
            
         }
        {apply clock_match_nomod; auto.
         rewrite Forall_forall. intros ? Hin. inversion Hin; clarify.
         rewrite in_app in H2. destruct H2 as [Hin1 | Hin2]; clarify.
         -apply in_mops_hb_check in Hin1. destruct x0; clarify.
         -destruct Hin2 as [? | [? | [?|?]]]; clarify.
         -rewrite Forall_forall. intros x0 Hin. destruct x0; clarify.
          +rewrite in_app in Hin. destruct Hin as [Hin | [Hin | [Hin |Hin]]]; clarify.
           *apply in_mops_hb_check in Hin. clarify.
           *inversion Hin; clarify.
          +destruct Hin as [Hin | Hin]; clarify.
           *inversion Hin; clarify.
           *rewrite in_app in Hin. destruct Hin as [Hin | [Hin | [Hin | Hin ]]]; clarify.
            {apply in_mops_hb_check in Hin. clarify. }
            {inversion Hin; clarify. }
        }
        { rewrite split_app, app_assoc. do 2 rewrite split_app. 
          apply clock_match_nomod; auto.
          -destruct (eq_dec x v0); clarify.
           +assert(Hvt_vctt : vt= vc t t ).
            {
              apply clock_match_value with (m:= m ++
           Acq t (X' + v0)
           :: mops_hb_check (W' + v0) (C' + t)
                (map (vw v0) (rev (interval 0 zt)))
                (map (vc t) (rev (interval 0 zt))) zt t) (ct:=C'+t) (t:=t).
              apply clock_match_nomod; auto.
              -apply clock_match_nomod; auto.
               +apply (consistent_app_SC _  ([Read t (C' + t, t) vt; Write t (R' + v0, t) vt;
                                              Read t (v0, o) v; Rel t (X' + v0)])).
                rewrite <- app_assoc.  rewrite <- app_comm_cons. auto.
               +rewrite Forall_forall. intros ? Hin. inversion Hin; clarify.
                apply in_mops_hb_check in H2; destruct x; clarify.
               +rewrite Forall_forall. intros ? Hin. inversion Hin; clarify.
                apply in_mops_hb_check in Hin; destruct x; clarify.
              -apply (consistent_app_SC _ ([Write t (R'+v0,t) vt; Read t (v0, o) v; Rel t (X'+v0)])).
               rewrite <- split_app. rewrite <- app_assoc,  <- app_comm_cons. auto.
              -rewrite Forall_forall. intros x Hin. inversion Hin; clarify.
              -apply init_steps.
               +apply Hinit. unfold meta_loc. clarify. left. omega.
               +rewrite Forall_forall. intros x Hin. inversion Hin; clarify.
                apply in_mops_hb_check in H2. destruct x; clarify.
              -auto.
             }
            rewrite <- Hvt_vctt.
            apply clock_match_mods; auto.
            *rewrite <- split_app, <- app_assoc.
             apply clock_match_nomod; auto.
             { eapply consistent_app_SC; eauto.
               instantiate(1:=[Write t (R' + v0, t) vt;
               Read t (v0, o) v; Rel t (X' + v0)]). rewrite <- app_comm_cons.
               rewrite <- app_assoc. rewrite <- app_comm_cons. rewrite <- app_assoc.
               simpl. auto.
             }
             { rewrite Forall_forall. intros x Hin. inversion Hin; clarify.
               rewrite in_app in H2. destruct H2 as [Hin2 | Hin2]; clarify.
               apply in_mops_hb_check in Hin2. destruct x; clarify.
             }
             { rewrite Forall_forall. intros x Hin. rewrite in_app in Hin.
               destruct Hin as [Hin | Hin]; clarify.
               apply in_mops_hb_check in Hin. destruct x; clarify.
             }
            *rewrite <- app_assoc. simpl. rewrite <- app_assoc. rewrite <- split_app.
             eapply consistent_app_SC; eauto.
             instantiate(1:=[Read t (v0, o) v; Rel t (X' + v0)]).
             rewrite <- app_assoc.  rewrite <- app_comm_cons. rewrite <- app_assoc. simpl.
             auto.
           +assert(Hv0: upd vr x (upd (vr x) t (vc t t )) v0 =vr v0).
              unfold upd. clarify.
            setoid_rewrite Hv0.
            do 2 rewrite <- app_assoc. simpl.  rewrite <- split_app.  
            apply clock_match_nomod; auto.
            *specialize(Hs_rw' v0). clarify.
            *eapply consistent_app_SC; eauto.
             instantiate(1:=[Read t (x, o) v; Rel t (X' + x)]).
             rewrite <- app_assoc. rewrite <- app_comm_cons. rewrite <- app_assoc.
             simpl. auto.
            *rewrite Forall_forall. intros c Hin. inversion Hin; clarify.
             rewrite in_app in H2. destruct H2 as [Hin2| Hin2]; clarify.
             apply in_mops_hb_check in Hin2. destruct c; clarify.
             destruct Hin2; clarify.
            *rewrite Forall_forall. intros c Hin. inversion Hin; clarify.
             rewrite in_app in Hin. destruct Hin as [Hin | Hin].
             apply in_mops_hb_check in Hin. destruct c; clarify.
             inversion Hin; clarify. intro Heq. clarify. apply plus_reg_l in Heq. clarify.
            
            
          -repeat rewrite <- app_assoc. simpl. auto.
          -rewrite Forall_forall. intros c Hin. inversion Hin; clarify.
        }
        {
          specialize (Hs_rw' v0 H). 
          apply clock_match_nomod; clarify;
          rewrite Forall_forall; intros c Hin; inversion Hin; clarify.
          -rewrite in_app in H2; destruct H2 as [Hin2 | Hin2 ]; clarify.
           +apply in_mops_hb_check in Hin2. destruct c; clarify.
           + destruct Hin2 as [? | [?|[?|[?|?]]]]; clarify.
          -rewrite in_app in Hin; destruct Hin as [Hin | Hin]; clarify.
           apply in_mops_hb_check in Hin. destruct c; clarify.
          
        }
   -(*store*) (* see above *) 
    exploit (instrument_incom (Store (x, o) e)).
    { simpl; rewrite <- app_assoc; simpl. eauto. }
    clarify.
    do 4 eexists. split;[|split;[|split]].
    +apply exec_store. eauto.
    +unfold mem_sim. intros. simpl. split; clarify.
     { split.
       - right.
         rewrite in_app; right; simpl; eauto.
         rewrite in_app. right. simpl. do 2 right; left. clarify.
         exploit eval_sim.
         {instantiate(1:=G2 t). instantiate(1:=G1 t).  instantiate(1:=e). 
          intros. apply HGsim; intro Heq; clarify. }
         intro Heval. auto.
       - setoid_rewrite Forall_app in Hlocs. clarify. inversion Hlocs2; clarify. inversion H2; clarify.
     }  
     { left.
       setoid_rewrite Forall_app in Hlocs. clarify. inversion Hlocs2; clarify. 
       inversion H4; clarify.
       rewrite Forall_app in Ht. clarify. inversion Ht2; clarify.
       do 2 rewrite in_app in H1. simpl in H1.
       destruct H1 as [? | [? | [? | [? | [? | [? | ?]]]]]]; clarify.
       - contradiction H2. unfold meta_loc. simpl. repeat right. omega.
       - contradiction H2. eapply mops_hb_check_meta; eauto.
       - contradiction H2. eapply mops_hb_check_meta; eauto.
       - contradiction H2. unfold meta_loc. left. simpl. omega.
       - contradiction H2. unfold meta_loc. simpl. do 3 right. left. omega. 
       - exploit eval_sim.
         {instantiate(1:=G2 t). instantiate(1:=G1 t). instantiate(1:=e).
          intros. apply HGsim; intro Heq; clarify. }
         intro Heval. auto.
       - contradiction H2. unfold meta_loc. repeat right. simpl. omega.         
     }
    +assert(Hlist_silly1: forall (X:Type) (a b c d e: X) (l1 l2 l3 l4: list X), 
                             l1++a::l2++l3++[b;c;d;e]=(l1++[a])++(l2++l3++[b;c])++[d;e]).
      intros. simpl. do  2 rewrite app_assoc. clarify. 
      rewrite split_app. rewrite app_assoc. do 2 rewrite split_app. 
      repeat rewrite <- app_assoc. simpl. auto.
     rewrite Hlist_silly1 in Hcon; auto. rewrite loc_valid_ops_SC in Hcon.
     {
        inversion Hcon; clarify. 
        rewrite loc_valid_ops2_SC in Hcon2.
        -inversion Hcon2; clarify. rewrite <- app_assoc in Hcon22. rewrite loc_valid_ops_SC in Hcon22.
         +inversion Hcon22; clarify.
          exploit eval_sim.
          {instantiate(1:=G2 t). instantiate(1:=G1 t). instantiate(1:=e). intros. apply HGsim; intro Heq; clarify. }
          intro Heval. rewrite Heval. auto.
         
         +rewrite Forall_forall; clarify.
          rewrite Forall_forall; clarify.
          intro Heq. setoid_rewrite Forall_app in Hlocs. clarify. inversion Hlocs2; clarify. inversion H4; clarify.
          contradiction H81; repeat right.
          rewrite H1; clarify; omega.
         + constructor; clarify.
         + constructor; clarify.
         
        -rewrite Forall_forall; clarify.
         intros Heq. setoid_rewrite Forall_app in Hlocs. clarify. inversion Hlocs2; clarify. inversion H4; clarify.
         contradiction H81; repeat right; simpl.
         rewrite <- H1; omega.
        - simpl; auto.
        - constructor; clarify.
      }
      { rewrite Forall_forall; intros ? Hin; clarify.
        rewrite Forall_forall; intros ? Hin2; clarify.
        setoid_rewrite Forall_app in Hlocs. clarify. inversion Hlocs2; clarify. inversion H2; clarify.
        rewrite Forall_app in Ht. inversion Ht; clarify. inversion Ht2; clarify.
        destruct Hin2.
        - subst; simpl; intro; contradiction H41; rewrite H.
          do 2 rewrite in_app in Hin. destruct Hin as [? | [? | [?|?]]]; clarify.
          + eapply mops_hb_check_meta; eauto.
          + eapply mops_hb_check_meta; eauto.  
          + left; simpl; omega.
          + rewrite <- H7. unfold meta_loc. do 3 right; left; simpl. omega.
        - subst; simpl; intro.
          do 2 rewrite in_app in Hin; destruct Hin as [? | [? | [?|?]]]; clarify.
          + apply in_mops_hb_check in H1. destruct x0; clarify. 
            destruct H1.
            * exploit Hmetalocs_disjoint_WX; eauto.
            * exploit Hmetalocs_disjoint_CX; eauto.
          + apply in_mops_hb_check in H1. destruct x0; clarify.
            destruct H1.
            * exploit Hmetalocs_disjoint_RX; eauto.
            * exploit Hmetalocs_disjoint_CX; eauto.
          + exploit Hmetalocs_disjoint_CX; eauto.
          + exploit Hmetalocs_disjoint_WX; eauto. }

      { do  2 rewrite Forall_app; split; auto; repeat constructor; simpl; auto. }
      { repeat constructor; simpl; auto. }
     +setoid_rewrite Forall_app in Hlocs; destruct Hlocs as (_ & Hlocs).
      inversion Hlocs as [|?? Hi ?]; inversion Hi; clarify.
      rewrite Forall_app in Ht; destruct Ht as (_ & Ht).
      inversion Ht; clarify.
      assert(Hsilly: (
                        [Read t (C' + t, t) v; Write t (W' + x, t) v;
                         Write t (x, o) (eval (G2 t) e); Rel t (X' + x)]) = (
                                                                [Read t (C' + t, t) v; Write t (W' + x, t) v;
                                                                 Write t (x, o) (eval (G2 t) e)])++ [Rel t (X' + x)] ).
      { clarify. }
      
      assert(Hhbs : consistent (m ++ mops_hb_check (W' + x) (C' + t) vs1 vs2 zt t ++ mops_hb_check (R' + x) (C' + t) vs3 vs2 zt t )).
      {
        rewrite app_comm_cons in Hcon. do 2 rewrite app_assoc in Hcon.
        apply consistent_app_SC in Hcon.
        rewrite <- app_assoc in Hcon. rewrite <- app_comm_cons in Hcon. 
        rewrite loc_valid_ops2_SC in Hcon; clarify.
        -rewrite Forall_forall.  intros c Hin. rewrite in_app in Hin.
         destruct Hin as [Hin | Hin]; clarify; apply in_mops_hb_check in Hin; destruct c; clarify; destruct x0 as (x0,off); intro Heq; inversion Heq; clarify.
         +specialize(Hmetalocs_disjoint_WX H52 H52). specialize (Hmetalocs_disjoint_CX H3 H52). destruct Hin; clarify.
         +specialize(Hmetalocs_disjoint_RX H52 H52). specialize (Hmetalocs_disjoint_CX H3 H52). destruct Hin; clarify.
        -rewrite Forall_forall. intros c Hin. rewrite in_app in Hin.
         destruct Hin as [Hin | Hin]; clarify; apply in_mops_hb_check in Hin; destruct c; clarify.
      }
      assert(Hs_rw':= Hs_rw).
      specialize (Hs_rw x); clarify.
      assert(Hhb1: consistent ( m++ mops_hb_check (W'+x) (C'+t) vs1 vs2 zt t )).
        eapply consistent_app_SC; eauto. rewrite <- app_assoc. eauto.
      assert(Hhb2: consistent ( m ++ mops_hb_check (R'+x) (C'+t) vs3 vs2 zt t)).
        apply reads_noops_SC in Hhbs; auto.
        apply mops_hb_check_read.
      exploit hb_check_vals; try apply Hhb1; eauto.
      { intros; apply Hinit; unfold meta_loc; simpl; omega. }
      { intros; apply Hinit; unfold meta_loc; simpl; omega. }
      exploit hb_check_vals; try apply Hhb2; eauto.
      { intros; apply Hinit; unfold meta_loc; simpl; omega. }
      { intros; apply Hinit; unfold meta_loc; simpl; omega. }
      clarify; eexists; simpl; split. 
      *eapply ss_step; eauto.
       eapply write_upd; eauto.
       eapply first_gt_vc_le; eauto.
       eapply first_gt_vc_le; eauto.
       apply ss_refl.
      *unfold clocks_sim. split;[|split;[|split]]; intros;clarify.
       {apply clock_match_nomod; auto.
        rewrite Forall_forall. intros ? Hin. inversion Hin; clarify. 
        rewrite in_app in H2. destruct H2 as [Hin1 | Hin2]; clarify.
        -apply in_mops_hb_check in Hin1. destruct x0; clarify.
        -rewrite in_app in Hin2. destruct Hin2 as [Hin2 | Hin2]; clarify.
         +apply in_mops_hb_check in Hin2. destruct x0; clarify.
         +destruct Hin2 as [?|[?|[?|?]]]; clarify.
        -rewrite Forall_forall. intros x0 Hin. destruct x0; clarify;
         do 2 rewrite in_app in Hin; destruct Hin as [Hin | [Hin | [Hin |[Hin | [Hin | [Hin | Hin]]]]]]; try apply in_mops_hb_check in Hin; clarify.
          *inversion Hin; clarify. 
          *inversion Hin; clarify. intro Heq. contradiction H51.
           rewrite <- Heq. unfold meta_loc. left. simpl. omega.
          *inversion Hin; clarify.
          *inversion H2; clarify.
           
       }
       {apply clock_match_nomod; auto.
        rewrite Forall_forall. intros ? Hin. inversion Hin; clarify. 
        rewrite in_app in H2. destruct H2 as [Hin1 | Hin2]; clarify.
        -apply in_mops_hb_check in Hin1. destruct x0; clarify.
        -rewrite in_app in Hin2. destruct Hin2 as [Hin2 | Hin2]; clarify.
         +apply in_mops_hb_check in Hin2. destruct x0; clarify.
         +destruct Hin2 as [?|[?|[?|?]]]; clarify.
        -rewrite Forall_forall. intros x0 Hin. destruct x0; clarify;
         do 2 rewrite in_app in Hin; destruct Hin as [Hin | [Hin | [Hin |[Hin | [Hin | [Hin | Hin]]]]]]; try apply in_mops_hb_check in Hin; clarify.
          *inversion Hin; clarify. 
          *inversion Hin; clarify. intro Heq. contradiction H51.
           rewrite <- Heq. unfold meta_loc. right. left. simpl. omega.
          *inversion Hin; clarify.
          *inversion H2; clarify.
           
       }
       {
          specialize (Hs_rw' v0 H). 
          apply clock_match_nomod; clarify;
          rewrite Forall_forall; intros c Hin; inversion Hin; clarify.
          -do 2 rewrite in_app in H2; destruct H2 as [Hin2 | Hin2 ]; clarify.
           +apply in_mops_hb_check in Hin2. destruct c; clarify.
           + destruct Hin2 as [Hin2 | [?|[?|[?|[?|?]]]]]; clarify.
             apply in_mops_hb_check in Hin2. destruct c; clarify.
          -do 2 rewrite in_app in Hin; destruct Hin as [Hin | [Hin|[?|[?|[?|?]]]]]; clarify.
           +apply in_mops_hb_check in Hin. destruct c; clarify.
           +apply in_mops_hb_check in Hin. destruct c; clarify.
           +specialize(Hmetalocs_disjoint_WR H52 H). clarify.
           +intro Heq. contradiction H51. rewrite <- Heq. unfold meta_loc.  do 2 right. left. simpl. omega.
       }
       { rewrite split_app, app_assoc, app_assoc. do 2 rewrite split_app. 
         apply clock_match_nomod; auto.
         -destruct (eq_dec x v0); clarify.
          +assert(Hvt_vctt : v= vc t t ).
           {
             apply clock_match_value with (m:= m ++
                                                 Acq t (X' + v0)
                                                 :: mops_hb_check (W' + v0) (C' + t)
                                                 (map (vw v0) (rev (interval 0 zt)))
                                                 (map (vc t) (rev (interval 0 zt))) zt t ++
                                                 mops_hb_check (R' + v0) (C' + t)
                                                 (map (vr v0) (rev (interval 0 zt)))
                                                 (map (vc t) (rev (interval 0 zt))) zt t) (ct:=C'+t) (t:=t); auto.
             apply clock_match_nomod; auto.
             -apply clock_match_nomod; auto.
              +apply (consistent_app_SC _  ([Read t (C' + t, t) v; Write t (W' + v0, t) v;
                                             Write t (v0, o) (eval (G2 t) e); Rel t (X' + v0)])); auto.
               rewrite <- app_assoc.  rewrite <- app_comm_cons. rewrite <- app_assoc. auto.
              +rewrite Forall_forall. intros ? Hin. inversion Hin; clarify.
               rewrite in_app in H2. destruct H2 as [Hin2 | Hin2]; clarify;
               apply in_mops_hb_check in Hin2; destruct x; clarify.
              +rewrite Forall_forall. intros ? Hin. inversion Hin; clarify.
               rewrite in_app in Hin. destruct Hin as [Hin | Hin]; clarify;
               apply in_mops_hb_check in Hin; destruct x; clarify.
             -apply (consistent_app_SC _ ([Write t (W'+v0,t) v; Write t (v0, o) (eval (G2 t) e); Rel t (X'+v0)])); auto.
              rewrite <- split_app. rewrite <- app_assoc,  <- app_comm_cons, <- app_assoc. auto. 
             -rewrite Forall_forall. intros x Hin. inversion Hin; clarify.
             -apply init_steps.
              +apply Hinit. unfold meta_loc. clarify. left. omega.
              +rewrite Forall_forall. intros x Hin. inversion Hin; clarify.
               rewrite in_app in H2. destruct H2 as [Hin2 | Hin2]; clarify;
               apply in_mops_hb_check in Hin2; destruct x; clarify.
           }
           rewrite <- Hvt_vctt.
           apply clock_match_mods; auto.
           *rewrite <- split_app, <- app_assoc, <- app_assoc.
            apply clock_match_nomod; auto.
            { eapply consistent_app_SC; eauto.
              instantiate(1:=[Write t (W' + v0, t) v;
                               Write t (v0, o) (eval (G2 t) e); Rel t (X' + v0)]). rewrite <- app_comm_cons.
              rewrite <- app_assoc. rewrite <- app_comm_cons. do 2 rewrite <- app_assoc.
              auto.
            }
            { rewrite Forall_forall. intros x Hin. inversion Hin; clarify.
              do 2 rewrite in_app in H2. destruct H2 as [Hin2 | [Hin2 |Hin2]]; clarify;
              apply in_mops_hb_check in Hin2; destruct x; clarify.
            }
            { rewrite Forall_forall. intros x Hin. do 2 rewrite in_app in Hin.
              destruct Hin as [Hin | [Hin |Hin]]; clarify;
              apply in_mops_hb_check in Hin; destruct x; clarify.
            }
           *rewrite <- app_assoc. simpl. rewrite <- app_assoc. rewrite <- split_app.
            rewrite <- app_assoc.
            eapply consistent_app_SC; eauto.
            instantiate(1:=[Write t (v0, o) (eval (G2 t) e); Rel t (X' + v0)]).
            do 2 rewrite <- app_assoc.  rewrite <- app_comm_cons. rewrite <- app_assoc. 
            auto.
          +assert(Hv0: upd vw x (upd (vw x) t (vc t t )) v0 =vw v0).
             unfold upd. clarify.
           setoid_rewrite Hv0.
           do 3 rewrite <- app_assoc. simpl.  rewrite <- split_app.  
           apply clock_match_nomod; auto.
           *specialize(Hs_rw' v0). clarify.
           *eapply consistent_app_SC; eauto.
            instantiate(1:=[Write t (x, o) (eval (G2 t) e); Rel t (X' + x)]).
            rewrite <- app_assoc. rewrite <- app_comm_cons. do 2 rewrite <- app_assoc.
            auto.
           *rewrite Forall_forall. intros c Hin. inversion Hin; clarify.
            do 2 rewrite in_app in H2. destruct H2 as [Hin2| [Hin2 |Hin2]]; clarify;
            try apply in_mops_hb_check in Hin2; try destruct c; clarify.
           *rewrite Forall_forall. intros c Hin. inversion Hin; clarify.
            do 2 rewrite in_app in Hin. destruct Hin as [Hin | [Hin | Hin]];clarify;
            try apply in_mops_hb_check in Hin; try destruct c; clarify.
            intro Heq. clarify. apply plus_reg_l in Heq. clarify.
              
         -repeat rewrite <- app_assoc. auto.
         -rewrite Forall_forall. intros c Hin. inversion Hin; clarify.
         -rewrite Forall_forall. intros c Hin. inversion Hin; clarify.
          intro Heq. contradiction H51. unfold meta_loc. simpl. do 3 right. left. omega.
       }
   -(*lock*) 
     exploit (instrument_incom (Lock m0)).
     { simpl;  eauto. }
     clarify.
     do 4 eexists. split;[|split;[|split]].
     +apply exec_lock. eauto.
     +unfold mem_sim. intros. simpl.
      setoid_rewrite Forall_app in Hlocs. clarify. inversion Hlocs2; clarify. 
      split; clarify.
      { inversion H1; clarify. }
      { left.
        inversion H1; clarify.
        rewrite Forall_app in Ht. clarify. inversion Ht2; clarify.
        contradiction H3. eapply mops_max_vc_meta; eauto.
      }
     +rewrite split_app in Hcon.
      simpl. eapply consistent_app_SC; eauto.
     +setoid_rewrite Forall_app in Hlocs; destruct Hlocs as (_ & Hlocs).
      inversion Hlocs as [|?? Hi ?]; inversion Hi; clarify.
      rewrite Forall_app in Ht; destruct Ht as (_ & Ht).
      inversion Ht; clarify.
      assert(Hhbs : consistent (m ++ mops_max_vc (L' + m0) (C' + t) vs1 vs2 t zt)).
      { 
        rewrite loc_valid_ops2_SC in Hcon; clarify.

        rewrite Forall_forall.  intros c Hin. apply in_mops_max_vc' in Hin.
        destruct c; clarify;
        intro Heq; contradiction H41; unfold meta_loc.
        -destruct Hin; clarify; try rewrite H; try omega.
        -rewrite <- Heq, Hin. left. omega. 
      }
      exploit max_vc_vals; try apply Hhbs; eauto.
      { intros; apply Hinit; unfold meta_loc; simpl; omega. }
      { intros; apply Hinit; unfold meta_loc; simpl; omega. }
      clarify; eexists; simpl; split. 
      *eapply ss_step; eauto.
       eapply acquire; eauto.
       apply ss_refl.
      *assert(Hcon_acq: consistent (m ++[Acq t m0])).
       {
         eapply consistent_app_SC; eauto.
         instantiate (1:=mops_max_vc (L' + m0) (C' + t)
                 (map (vl m0) (rev (interval 0 zt)))
                 (map (vc t) (rev (interval 0 zt))) t zt).
         rewrite <- split_app. auto.
        }
       unfold clocks_sim. split;[|split;[|split]]; intros;clarify.
       {
         destruct (eq_dec t t0); clarify.
         -rewrite clock_match_iff_z.
          split; auto.
          +rewrite split_app. apply clock_match_z_max_vc; auto.
           {apply clock_match_nomod_z; auto.
            -specialize (Hs_l m0 H42). rewrite clock_match_iff_z in Hs_l. clarify.
            -rewrite Forall_forall. clarify.
            -rewrite Forall_forall. clarify.
             intro Heq. contradiction H41. rewrite <- Heq. unfold meta_loc.
             simpl. omega.
            }
           {apply clock_match_nomod_z; auto.
            -specialize (Hs_c t0 H). rewrite clock_match_iff_z in Hs_c. clarify.
            -rewrite Forall_forall. clarify.
            -rewrite Forall_forall. clarify.
             intro Heq. contradiction H41. rewrite <- Heq. unfold meta_loc.
             simpl. omega.
            }
           {specialize (Hmetalocs_disjoint_CL H42 H). clarify. }
           {rewrite <- split_app. auto. }
          +specialize(Hs_l m0 H42). apply clock_match_bounded in Hs_l.
           specialize (Hs_c t0 H). apply clock_match_bounded in Hs_c.
           unfold bounded,upd, vc_join in *. clarify.
           rewrite Hs_l; auto. rewrite Hs_c; auto.
         -assert( upd vc t ( vc_join (vc t) (vl m0)) t0 = vc t0) as Hvct0.
          {
            unfold upd. clarify.
          }
          rewrite Hvct0.
          apply clock_match_nomod; auto.
          rewrite Forall_forall. intros ? Hin. inversion Hin; clarify.
          apply in_mops_max_vc in H1. destruct x; clarify.
          specialize(Hmetalocs_disjoint_CL H42 Hlt). clarify.
          rewrite Forall_forall.  intros c Hin. destruct Hin as [Hin | Hin]; clarify.
          intros Heq. contradiction H41. rewrite <- Heq.  unfold meta_loc. simpl. omega.
          apply in_mops_max_vc' in Hin. destruct c; clarify.
          destruct x; clarify. intros Heq. contradiction n.
          apply plus_minus in Heq .  rewrite minus_plus in Heq. auto.
       }
       {apply clock_match_nomod; auto.
        rewrite Forall_forall. intros ? Hin. inversion Hin; clarify. 
        apply in_mops_max_vc in H1. destruct x; clarify.
        specialize(Hmetalocs_disjoint_CL H42 Hlt). clarify.
        rewrite Forall_forall.  intros c Hin. destruct Hin as [Hin | Hin]; clarify.
        intros Heq. contradiction H41. rewrite <- Heq.  unfold meta_loc. simpl. omega.
        apply in_mops_max_vc' in Hin. destruct c; clarify.
        destruct x; clarify. specialize(Hmetalocs_disjoint_CL H Hlt). clarify.
       }
       {
        assert(Hs_rw':=Hs_rw).
        specialize (Hs_rw' v H). 
        apply clock_match_nomod; clarify;
        rewrite Forall_forall; intros c Hin; inversion Hin; clarify.
        -exploit max_vc_prog. intro Hmax_prog. rewrite Forall_forall in Hmax_prog.
         apply Hmax_prog. eauto.
        -intro Heq. contradiction H41. rewrite <- Heq. unfold meta_loc. simpl. omega.
        -apply in_mops_max_vc' in H1.  destruct c; clarify.
         destruct x; clarify. specialize(Hmetalocs_disjoint_CR Hlt H). clarify.
       }
       {
        assert(Hs_rw':=Hs_rw).
        specialize (Hs_rw' v H). 
        apply clock_match_nomod; clarify;
        rewrite Forall_forall; intros c Hin; inversion Hin; clarify.
        -exploit max_vc_prog. intro Hmax_prog. rewrite Forall_forall in Hmax_prog.
         apply Hmax_prog. eauto.
        -intro Heq. contradiction H41. rewrite <- Heq. unfold meta_loc. simpl. omega.
        -apply in_mops_max_vc' in H1.  destruct c; clarify.
         destruct x; clarify. specialize(Hmetalocs_disjoint_CW Hlt H). clarify.
       }
    -(*unlock-nil*) symmetry in Hi. apply app_cons_not_nil in Hi. clarify.
    -(*unlock*) 
      exploit (instrument_incom (Unlock m0)).
      {simpl. rewrite <- split_app. eauto. }
      clarify.
      do 4 eexists. split; [|split;[|split]].
      +apply exec_unlock. eauto.
      +unfold mem_sim. intros. simpl.
       setoid_rewrite Forall_app in Hlocs. clarify. inversion Hlocs2; clarify. 
       inversion H1; clarify.
       split; clarify.
       {rewrite in_app. simpl. auto. }
       {left. rewrite Forall_app in Ht. clarify. inversion Ht2; clarify.
        rewrite in_app in H0. simpl in H0. destruct H0 as [? | [? | [?|?]]]; clarify.
        -contradiction H3. eapply mops_set_vc_meta_cl; eauto.
        -contradiction H3. unfold meta_loc. left. simpl. omega.
        -contradiction H3. unfold meta_loc. left. simpl. omega.
       }
      +simpl. 
       do 2 rewrite split_app in Hcon. 
       rewrite loc_valid_ops_SC in Hcon.  
       {
         inversion Hcon; clarify.
       }  
       { rewrite Forall_forall; intros ? Hin; clarify.
        rewrite Forall_forall; intros ? Hin2; clarify.
        setoid_rewrite Forall_app in Hlocs. clarify. inversion Hlocs2; clarify.
        inversion H1; clarify.
        rewrite Forall_app in Ht. clarify. inversion Ht2; clarify.
        repeat rewrite in_app in Hin. destruct Hin as [[?|?]|?]; clarify; intro Heq.
        -contradiction H31. setoid_rewrite Heq. eapply mops_set_vc_meta_cl; eauto.
        -contradiction H31. setoid_rewrite Heq. unfold meta_loc. left. simpl. omega.
        -contradiction H31. setoid_rewrite Heq. unfold meta_loc. left. simpl. omega.
       }
       { repeat rewrite Forall_app; split; auto; repeat constructor; simpl; auto. }
       { repeat constructor; simpl; auto. }
      +setoid_rewrite Forall_app in Hlocs. inversion Hlocs; clarify.
       inversion Hlocs2 as [| ?? Hloci ?]. clarify. inversion Hloci; clarify.
       rewrite Forall_app in Ht; destruct Ht as (_ & Ht).
       inversion Ht; clarify.
       assert(Hs_rw':= Hs_rw). 
       assert(Hhb:  consistent (m ++ mops_set_vc (C' + t) (L' + m0) zt t vs)).
       {
         rewrite app_assoc in Hcon.
         eapply consistent_app_SC; eauto.
         
       }
       exploit set_vc_vals; try apply Hhb; eauto.
       { intros; apply Hinit; unfold meta_loc; simpl; omega. }
       clarify; eexists; simpl; split. 
       * eapply ss_step; eauto.
         eapply release; eauto.
         apply ss_refl.
       * unfold clocks_sim. split;[|split;[|split]]; intros;clarify.
         { rewrite split_app. rewrite split_app. rewrite app_assoc.
           apply clock_match_nomod; auto.
           assert(forall t', t'< zt ->clock_match
                    (m ++
                       mops_set_vc (C' + t) (L' + m0) zt t (map (vc t) (rev (interval 0 zt)))
                                     ++ 
                                    [Read t (C' + t, t) v]) (vc t') (C' + t') ) as Hcm1.
           {
             clarify.
             apply clock_match_nomod; clarify.
             -eapply consistent_app_SC. rewrite <- app_assoc. rewrite <- app_assoc.
              simpl. eauto.
             -rewrite Forall_app. split; clarify.
              rewrite Forall_forall. clarify.
             -rewrite Forall_app. split; clarify.
              rewrite Forall_forall. intros c Hin; clarify.
              apply in_mops_set_vc' in Hin. destruct c; clarify.
              destruct x; clarify. 
           }
           assert( v= vc t t) as Hv.
           {
             apply clock_match_value with (m:=m ++
            mops_set_vc (C' + t) (L' + m0) zt t (map (vc t) (rev (interval 0 zt)))
     ) (ct:=C'+t) (t:=t).
             - rewrite <- app_assoc. auto.
             -apply init_steps; clarify.
              apply Hinit.
              unfold meta_loc. simpl.  left. auto. omega.
             -auto.
             
           }
           +rewrite app_assoc.
            destruct (eq_dec t0 t); clarify.
            *assert(upd vc t (vc_inc t (vc t)) t = upd vc t (upd (vc t) t (vc t t +1)) t )  as Hv1.
             {
               unfold upd, vc_inc; clarify.
               apply functional_extensionality.
               clarify.
               destruct (eq_dec x t); clarify.
               omega.
             }
             rewrite Hv1. 
             apply clock_match_mods; auto.
             eapply consistent_app_SC. do 2 rewrite <- app_assoc.  simpl.
             rewrite <- app_assoc. eauto. eapply Hcon.
            *apply clock_match_nomod; clarify.
             assert(upd vc t (vc_inc t (vc t)) t0 = vc t0) as Hvct0.
             {
               unfold upd, vc_inc; clarify.
             }
             rewrite Hvct0.
             apply Hcm1. auto.
             do 2 rewrite <- app_assoc.  simpl.
             eapply consistent_app_SC. do 2 rewrite <-app_assoc. simpl. eapply Hcon.
             rewrite Forall_forall; clarify. rewrite Forall_forall. intros c Hin; clarify.
             intros Heq. contradiction n. apply plus_minus in Heq.
             rewrite minus_plus in Heq. clarify.
           +do 3 rewrite <- app_assoc.  simpl. apply Hcon.
           +rewrite Forall_forall. clarify.
           +rewrite Forall_forall. clarify.
            intros Heq. contradiction H21.  unfold meta_loc. simpl.  rewrite <- Heq.
            left. omega.
         }
         {
           rewrite app_assoc.
           apply clock_match_nomod; auto.
           assert(Hs_l':=Hs_l).
           specialize(Hs_c t H2).
           rewrite clock_match_iff_z in Hs_c. 
           specialize(Hs_l m0 H22).
           rewrite clock_match_iff_z in Hs_l. 
           -destruct (eq_dec l1 m0); clarify.
            +apply clock_match_iff_z; auto.
             split; clarify.
             *apply clock_match_z_set_vc; clarify.
             *unfold bounded,upd in *. clarify.
            +unfold upd; clarify. simpl. apply not_eq_sym in n. clarify.
             apply clock_match_nomod; auto.
             *specialize(Hs_l' l1 H).
              clarify.
             *rewrite Forall_forall. intros c Hin. apply in_mops_set_vc' in Hin.
              destruct c; clarify. destruct x; clarify.
              intros Heq. apply plus_minus in Heq. rewrite minus_plus in Heq.
              clarify.
           -rewrite <- app_assoc. auto.
           -rewrite Forall_forall. intros c Hin.  destruct Hin as [Hin |[Hin|Hin]]; clarify.
           -rewrite Forall_forall. intros c Hin. destruct Hin as [Hin | [Hin | Hin]]; destruct c; clarify.
            +inversion Hin; destruct x; clarify. apply not_eq_sym. apply Hmetalocs_disjoint_CL; auto.
            +inversion H1; clarify. intro Heq. contradiction H21. rewrite <- Heq. unfold meta_loc. simpl. omega.
         }  
        {
          specialize (Hs_rw v0 H). 
          apply clock_match_nomod; clarify;
          rewrite Forall_forall; intros c Hin; rewrite in_app in Hin; destruct Hin as [Hin | Hin]; clarify.
          -apply in_mops_set_vc in Hin. destruct c; clarify. apply Hmetalocs_disjoint_CL; auto.
          -destruct Hin as [?|[?|[?|?]]]; clarify.
          -apply in_mops_set_vc' in Hin. destruct c; clarify. destruct x; clarify. apply not_eq_sym. apply Hmetalocs_disjoint_LR; auto.
          -destruct Hin as [?|?]; clarify.
           +apply not_eq_sym. apply Hmetalocs_disjoint_CR; auto.
           +intro Heq. contradiction H21. rewrite <- Heq. unfold meta_loc. simpl. omega.
          
        }
        {
          specialize (Hs_rw v0 H). 
          apply clock_match_nomod; clarify;
          rewrite Forall_forall; intros c Hin; rewrite in_app in Hin; destruct Hin as [Hin | Hin]; clarify.
          -apply in_mops_set_vc in Hin. destruct c; clarify. apply Hmetalocs_disjoint_CL; auto.
          -destruct Hin as [?|[?|[?|?]]]; clarify.
          -apply in_mops_set_vc' in Hin. destruct c; clarify. destruct x; clarify. apply not_eq_sym. apply Hmetalocs_disjoint_LW; auto.
          -destruct Hin as [?|?]; clarify.
           +apply not_eq_sym. apply Hmetalocs_disjoint_CW; auto.
           +intro Heq. contradiction H21. rewrite <- Heq. unfold meta_loc. simpl. omega.
          
        }

    -(*spawn-nil*) symmetry in Hi. apply app_cons_not_nil in Hi. clarify.
    -(*spawn*) 
     destruct i; destruct zt; clarify.
     +destruct x; clarify.
     +destruct x; clarify.
     +destruct zt; clarify.
     +destruct zt eqn:Hzt; clarify.
      apply plus_minus in H1. rewrite minus_plus in H1. clarify.
      rewrite <-Hzt in *; clarify.
      do 4 eexists. split; [|split;[|split]].
      *apply exec_spawn; eauto.
       intro Hin. 
       apply Forall2_impl with (Q:= (fun t1 t2: tid * prog => fst t1 = fst t2)) in HPsim. 
       setoid_rewrite (map_fst HPsim) in Hin. clarify.
       intros. clarify.
      *unfold mem_sim. intros. simpl.
       setoid_rewrite Forall_app in Hlocs. clarify. inversion Hlocs2; clarify. 
       inversion H1; clarify.
       rewrite Forall_app in Ht. clarify. inversion Ht2; clarify.
       split; clarify.
       rewrite in_app in H0. contradiction H7.
       inversion H0.
       { 
        apply (mops_max_vc_meta_cc vs1 vs2 zt _  H31 H3); eauto. 
       } 
       {
        inversion H; clarify; unfold meta_loc; left; simpl; omega.
       }
      *simpl. rewrite app_nil_r.
       eapply consistent_app_SC; eauto.
      *setoid_rewrite Forall_app in Hlocs. inversion Hlocs; clarify.
       inversion Hlocs2 as [| ?? Hloci ?]. clarify. inversion Hloci; clarify.
       rewrite Forall_app in Ht; destruct Ht as (_ & Ht).
       inversion Ht; clarify.
       assert(Hs_rw':= Hs_rw). 
       assert(Hhb:  consistent (m ++ mops_max_vc (C' + t) (C' + u) vs1 vs2 t zt)).
       {
         rewrite app_assoc in Hcon.
         eapply consistent_app_SC; eauto.
       }
       exploit max_vc_vals; try apply Hhb; eauto.
       { intros; apply Hinit; unfold meta_loc; simpl; omega. }
       { intros; apply Hinit; unfold meta_loc; simpl; omega. }
       clarify; eexists; simpl. split. 
       { eapply ss_step; eauto.
         eapply fork_step; eauto.
         apply ss_refl. }
       unfold clocks_sim.
       assert(u <> t) as Hut.
       {
         intro Heq. clarify. contradiction Hnew.
         rewrite map_app, in_app. clarify.
       }
       split;[|split;[|split]]; intros;clarify.
       {
         destruct (eq_dec t t0); clarify.
         -rewrite app_assoc.
          assert((upd (upd vc u (vc_join (vc u) (vc t0))) t0 (vc_inc t0 (vc t0)) t0)=
                 upd vc t0 (vc_inc t0 (vc t0)) t0) as Hupd.
          {
            unfold upd. clarify. }
          setoid_rewrite Hupd.
          eapply clock_match_inc_vc; eauto.
          +apply clock_match_nomod; auto.
           rewrite Forall_forall. intros c Hin. apply in_mops_max_vc' in Hin.
           destruct c; clarify.
           destruct x; clarify. intro Heq. apply plus_reg_l in Heq. clarify.
          +apply init_steps; auto.
           apply Hinit; auto. unfold meta_loc. simpl. omega.
          +rewrite <- app_assoc. auto.
         -destruct (eq_dec u t0); clarify.
          *assert ((upd (upd vc t0 (vc_join (vc t0) (vc t))) t (vc_inc t (vc t)) t0) = (upd vc t0 (vc_join (vc t0) (vc t)))  t0) as Hupd.
           { unfold upd; clarify. }
           rewrite Hupd. rewrite app_assoc. apply clock_match_nomod; auto.
           { 
             apply clock_match_max_vc; auto.
             intro Heq. apply plus_reg_l in Heq; auto.
           }
           {rewrite <- app_assoc. auto. }
           { rewrite Forall_forall. intros c Hin; inversion Hin; clarify. }
           { rewrite Forall_forall. intros c Hin; inversion Hin; clarify.
             intro Heq. apply plus_reg_l in Heq; auto. }
          *apply clock_match_nomod; auto.
           { unfold upd; destruct (eq_dec t t0); clarify.  }
           { rewrite Forall_app. split; clarify.
             rewrite Forall_forall. intros c Hin; inversion Hin; clarify. }
           { rewrite Forall_app. split; rewrite Forall_forall; intros c Hin.
             -apply in_mops_max_vc' in Hin. destruct c; clarify. destruct x; clarify.
              intro Heq. apply plus_reg_l in Heq. auto.
             -inversion Hin; destruct c; clarify. destruct x; inversion H1; clarify.
              intro Heq. apply plus_reg_l in Heq. auto.
           }
       }
       {
         apply clock_match_nomod; auto.
         - rewrite Forall_app; split; clarify. rewrite Forall_forall.
           intros c Hin; inversion Hin; clarify.
         - rewrite Forall_app; split; rewrite Forall_forall; intros c Hin.
           +apply in_mops_max_vc' in Hin. destruct c; clarify.
            destruct x; clarify. apply not_eq_sym. apply Hmetalocs_disjoint_CL; auto.
           +inversion Hin; destruct c; clarify. destruct x; inversion H1; clarify.
            apply not_eq_sym. apply Hmetalocs_disjoint_CL; auto.  
       }
       {
         specialize(Hs_rw v0); clarify.
         apply clock_match_nomod; auto.
         -rewrite Forall_app; clarify.
          rewrite Forall_forall; intros c Hin;inversion Hin; clarify.
         -rewrite Forall_app; split; rewrite Forall_forall; intros c Hin.
          +apply in_mops_max_vc' in Hin. destruct c; clarify.
           destruct x; clarify. apply not_eq_sym. apply Hmetalocs_disjoint_CR; auto.
          +inversion Hin; destruct c; clarify.
           destruct x; clarify. apply not_eq_sym. inversion H1; clarify.
       }
       {
         specialize(Hs_rw v0); clarify.
         apply clock_match_nomod; auto.
         -rewrite Forall_app; clarify.
          rewrite Forall_forall; intros c Hin;inversion Hin; clarify.
         -rewrite Forall_app; split; rewrite Forall_forall; intros c Hin.
          +apply in_mops_max_vc' in Hin. destruct c; clarify.
           destruct x; clarify. apply not_eq_sym. apply Hmetalocs_disjoint_CW; auto.
          +inversion Hin; destruct c; clarify.
           destruct x; clarify. apply not_eq_sym. inversion H1; clarify.
       } 
    -(*wait*)
     exploit (instrument_incom (Wait u)).
     { simpl;  eauto. }
     clarify.
     assert(u < zt) as Huzt.
     {
       apply in_split in Hdone. inversion Hdone; clarify.
       setoid_rewrite H in HPsim. unfold state_sim in HPsim. 
       apply Forall2_app_inv_r in HPsim. inversion HPsim. clarify.
       inversion H021; clarify.
       destruct x7. clarify. rewrite H022 in Ht.
       setoid_rewrite Forall_app in Ht; clarify. inversion Ht2; clarify.
     }
     assert (t < zt) as Htzt.
     {
       setoid_rewrite Forall_app in Hlocs; destruct Hlocs as (_ & Hlocs).
       inversion Hlocs as [|?? Hi ?]; inversion Hi; clarify.
       rewrite Forall_app in Ht; destruct Ht as (_ & Ht).
       inversion Ht; clarify.
     }
     assert (u <> t) as Hut.
     {
       intros Heq.
       rewrite in_app in Hdone. destruct Hdone as [Huin | [Huin |Huin]]; clarify;
       unfold distinct in *;  apply in_split in Huin; inversion Huin; clarify.
       -do 2 rewrite map_app in Hdistinct; clarify; apply NoDup_remove_2 in Hdistinct;
        contradiction Hdistinct;
        rewrite in_app. left. rewrite in_app. right. clarify.
       -rewrite map_app in Hdistinct. clarify. rewrite map_app in Hdistinct. clarify.
        apply NoDup_remove_2 in Hdistinct. contradiction Hdistinct.
        rewrite in_app. right. rewrite in_app. clarify.
     }
     do 4 eexists. split;[|split;[|split]].
     +apply exec_wait. eauto. auto. Print state_sim. 
      apply in_split in Hdone. inversion Hdone; clarify.
      setoid_rewrite H in HPsim. unfold state_sim in HPsim. 
      apply Forall2_app_inv_r in HPsim. inversion HPsim. clarify.
      inversion H021; clarify.
      destruct x7. clarify. inversion H021. clarify.
      apply Forall2_cons_inv in H021. inversion H021; clarify.
      destruct p; clarify.
      *rewrite H022. rewrite in_app_iff. clarify. 
      *exploit instrument_nonnil.
       { instantiate(1:=t0). instantiate(1:=i).
         symmetry in H32. apply app_eq_nil in H32. inversion H32. clarify. 
       }
       intros. clarify.
     +unfold mem_sim. intros. simpl. 
      split; clarify.
      {
        contradiction H2. apply in_app in H1. inversion H1; clarify.
        -eapply (mops_max_vc_meta_cc _ _ _ _ Huzt Htzt) ; eauto.
        -destruct H; unfold meta_loc; clarify; left; omega.
      }
     +simpl. rewrite app_nil_r.
      eapply consistent_app_SC; eauto.
     +exploit max_vc_vals; try apply Hcon; auto.
      { instantiate(1:=C'+u). intros. apply Hinit. unfold meta_loc; simpl; omega. }
      { instantiate(1:=C'+t). intros; apply Hinit; unfold meta_loc; simpl; omega. }
      { eapply consistent_app_SC; rewrite <- app_assoc. eauto. }
      { auto. }
      { auto. }
      { instantiate (1:=vc u). apply Hs_c; auto. }
      { instantiate (1:=vc t). apply Hs_c; auto. }
      clarify; eexists; simpl; split. 
      *eapply ss_step; eauto.
       eapply join_step; eauto.
       apply ss_refl.
      *unfold clocks_sim. split;[|split;[|split]]; intros;clarify.
       {
         destruct (eq_dec t0 u); clarify.
         -assert ((upd (upd vc t (vc_join (vc t) (vc u))) u (vc_inc u (vc u)) u) = upd vc u (vc_inc u (vc u)) u) as Hupd.
          { unfold upd; clarify. }
          rewrite Hupd.
          rewrite app_assoc. apply clock_match_inc_vc'; auto.
          +apply clock_match_nomod; auto.
           *eapply consistent_app_SC; rewrite <- app_assoc; eauto.
           *rewrite Forall_forall. intros c Hin. apply in_mops_max_vc' in Hin. destruct c; clarify.
            destruct x; clarify. intro Heq. apply plus_reg_l in Heq. clarify.
          +apply init_steps; clarify. apply Hinit. unfold meta_loc. simpl. omega.
          +rewrite <- app_assoc. auto.
         -destruct (eq_dec t0 t); clarify.
          +assert((upd (upd vc t (vc_join (vc t) (vc u))) u (vc_inc u (vc u)) t) = upd vc t (vc_join (vc t) (vc u)) t) as Hupd.
           { unfold upd. clarify. }
           rewrite Hupd, app_assoc.
           apply clock_match_nomod; auto.
           *apply clock_match_max_vc; auto.
           { intro Heq. apply plus_reg_l in Heq. clarify. }
           { eapply consistent_app_SC; rewrite <- app_assoc. eauto. }
           *rewrite <- app_assoc. auto.
           *rewrite Forall_forall. intros c Hin. inversion Hin; clarify.
           *rewrite Forall_forall. intros c Hin. inversion Hin; clarify.
            intro Heq. apply plus_reg_l in Heq. clarify.
          +apply clock_match_nomod; auto.
           *unfold upd; destruct (eq_dec u t0); destruct (eq_dec t t0); clarify.
           *rewrite Forall_forall. intros c Hin. rewrite in_app in Hin. destruct Hin as [Hin| [?|?]]; clarify.
            apply in_mops_max_vc' in Hin.
            destruct c; clarify.
           *rewrite Forall_forall. intros c Hin. rewrite in_app in Hin. destruct Hin as [Hin | [?|?]]; clarify.
            { apply in_mops_max_vc' in Hin.
              destruct c; clarify. destruct x; clarify. intro Heq.  apply plus_reg_l in Heq. clarify. }
            { intro Heq. apply plus_reg_l in Heq. clarify. }
     }
     {
       apply clock_match_nomod; auto.
       -rewrite Forall_forall. intros c Hin. rewrite in_app in Hin. destruct Hin as [Hin | [Hin | Hin]]; clarify.
        apply in_mops_max_vc' in Hin. destruct c; clarify.
       -rewrite Forall_forall. intros c Hin. rewrite in_app in Hin. destruct Hin as [Hin | [? | ? ]]; clarify.
        +apply in_mops_max_vc' in Hin. destruct c; clarify.
         destruct x; clarify. apply not_eq_sym. apply Hmetalocs_disjoint_CL; auto.
        +apply not_eq_sym. apply Hmetalocs_disjoint_CL; auto.
     }
     {
       specialize(Hs_rw v0 H); clarify.
       apply clock_match_nomod; auto.
       -rewrite Forall_forall. intros c Hin. rewrite in_app in Hin. destruct Hin as [Hin | [Hin | Hin]]; clarify.
        apply in_mops_max_vc' in Hin. destruct c; clarify.
       -rewrite Forall_forall. intros c Hin. rewrite in_app in Hin. destruct Hin as [Hin | [? | ? ]]; clarify.
        +apply in_mops_max_vc' in Hin. destruct c; clarify.
         destruct x; clarify. apply not_eq_sym. apply Hmetalocs_disjoint_CR; auto.
        +apply not_eq_sym. apply Hmetalocs_disjoint_CR; auto.
     }
     {
       specialize(Hs_rw v0 H); clarify.
       apply clock_match_nomod; auto.
       -rewrite Forall_forall. intros c Hin. rewrite in_app in Hin. destruct Hin as [Hin | [Hin | Hin]]; clarify.
        apply in_mops_max_vc' in Hin. destruct c; clarify.
       -rewrite Forall_forall. intros c Hin. rewrite in_app in Hin. destruct Hin as [Hin | [? | ? ]]; clarify.
        +apply in_mops_max_vc' in Hin. destruct c; clarify.
         destruct x; clarify. apply not_eq_sym. apply Hmetalocs_disjoint_CW; auto.
        +apply not_eq_sym. apply Hmetalocs_disjoint_CW; auto.
     }         
   -(*assert_le*)
     exploit (instrument_incom (Assert_le e1 e2)).
     { simpl;  eauto. }
     clarify.
     do 4 eexists. split;[|split;[|split]].
     +apply exec_assert_pass with (e1:=e1) (e2:=e2). eauto.
      rewrite eval_sim with (G2:=G2' t);  try rewrite eval_sim with (G1:=G1 t) (G2:=G2' t);
      auto;  intros; apply HGsim; intro Heq; clarify;unfold fresh_tmps in Hfresh; rewrite Forall_app in Hfresh;
      inversion Hfresh; clarify; inversion Hfresh2; clarify; inversion H2; clarify.
     +unfold mem_sim. intros. clarify. split; clarify.
     +simpl. rewrite app_nil_r. eapply consistent_app_SC; eauto.
     +exists (vc, vl, vr, vw). simpl. split; clarify.
      *apply ss_refl.
      *rewrite app_nil_r. unfold clocks_sim; clarify.
    -inversion Hemc; clarify.
     clarify; do 5 eexists; [eauto|];
     exploit sim_step; eauto; clarify.
     eexists. split; eauto. 
Qed. 
*)



Lemma hb_check_vals1' : forall m C1 C2 z vs1 vs2 t V1 V2 v1 v2
  (Hinit1 : forall z, z < zt -> initialized m (C1, z))
  (Hinit2 : forall z, z < zt -> initialized m (C2, z))
  (Hcon : consistent (m ++ mops_hb_check C1 C2 vs1 vs2 z t))
  (Hvs1 : length vs1 <= z) (Hvs2 : length vs2 <= z) (*(Hlens: length vs1 = length vs2)*) (Hz : z <= zt)
  (Hmatch1 : clock_match m V1 C1) (Hmatch2 : clock_match m V2 C2)
  (Hgt : first_gt  vs1 vs2 = Some (v1, v2)),
   ~ vc_le V1 V2         
  (*vs1 = map V1 (rev (interval 0 z)) /\ vs2 = map V2 (rev (interval 0 z))*).
Proof.
  induction z; destruct vs1, vs2; clarify.
  inversion Hvs1.
  assert (consistent (m ++ [Read t (C1, z) n])) as Hn.
  { eapply consistent_app_SC; rewrite <- app_assoc; simpl; eauto. }
  assert (consistent (m ++ [Read t (C2, z) n0])) as Hn0.
  { rewrite read_noop_SC in Hcon; auto.
    eapply consistent_app_SC; rewrite <- app_assoc; simpl; eauto. } 
  destruct (leb n n0) eqn:Hle; clarify.
  -eapply (IHz vs1 vs2); eauto.
   { do 2 (rewrite read_noop_SC in Hcon; eauto). }
   { omega. }
   { omega. }
   { omega. }
  -assert(v2 = V2 z) as Hv2.
   {
     apply clock_match_value with (m:=m) (ct:=C2) (t:=t); auto.
     apply clock_match_nomod; auto.
     rewrite Forall_forall. clarify.
   }
   assert(v1 = V1 z) as Hv1.
   {
     apply clock_match_value with (m:=m) (ct:=C1) (t:=t); auto.
     apply clock_match_nomod; auto.
     rewrite Forall_forall. clarify.
   }
   intro Hvc_le. clarify.
   unfold vc_le in Hvc_le. specialize (Hvc_le z); clarify. rewrite <- leb_le in Hvc_le. clarify.
Qed.
     

Corollary hb_check_vals' : forall m C1 C2 vs1 vs2 t V1 V2 v1 v2
  (Hinit1 : forall z, z < zt -> initialized m (C1, z))
  (Hinit2 : forall z, z < zt -> initialized m (C2, z))
  (Hcon : consistent (m ++ mops_hb_check C1 C2 vs1 vs2 zt t))
  (Hvs1 : length vs1 <= zt) (Hvs2 : length vs2 <= zt)
  (Hmatch1 : clock_match m V1 C1) (Hmatch2 : clock_match m V2 C2)
  (Hle : first_gt vs1 vs2 = Some (v1, v2)),
  ~ vc_le V1 V2.
Proof.
  intros; eapply hb_check_vals1' with (C1 := C1); eauto.
Qed.



Inductive fail_iexec P G t :
  list operation -> list conc_op -> (*state -> env -> *)Prop :=
  | fail_raw P1 P2 a x o v1 v2 rest vs1 vs2
    (Hload: P=P1++(t, load_handler t x zt ++
                                   Load a (x, o) :: Unlock (X + x) :: rest) :: P2)
      (Hgt : first_gt vs1 vs2 = Some (v1,v2) )  (Hlen1: length vs1 <=zt) (Hlen2: length vs2 <=zt):
      fail_iexec P G t (acq t (X + x) :: events_hb_check (W + x) (C + t) vs1 vs2 t )
                  (Acq t (X + x) ::
                   mops_hb_check (W + x) (C + t) vs1 vs2 zt t)
        (*[]
        (upd_env (upd_env G t tmp1 v1) t tmp2 v2)*)
  | fail_waw P1 P2 x o e v1 v2 rest vs1 vs2
      (Hstore : P = P1 ++ (t, store_handler t x zt ++
                              Store (x, o) e :: Unlock (X + x) :: rest) :: P2)
      (Hgt : first_gt vs1 vs2 = Some (v1,v2) ) (Hlen1: length vs1 <=zt) (Hlen2: length vs2 <=zt)  :
      fail_iexec P G t (acq t (X + x) :: events_hb_check (W + x) (C + t) vs1 vs2 t )
                  (Acq t (X + x) ::
                   mops_hb_check (W + x) (C + t) vs1 vs2 zt t )
        (*[]
        (upd_env (upd_env G t tmp1 v1) t tmp2 v2)*)
  | fail_war P1 P2 x o e v1 v2 rest vs1 vs2 vs3
      (Hstore : P = P1 ++ (t, store_handler t x zt ++
                              Store (x, o) e :: Unlock (X + x) :: rest) :: P2)
      (Hle : first_gt vs1 vs2 = None ) (Hgt: first_gt vs3 vs2 = Some (v1, v2) )
      (Hlen3: length vs3 <=zt) (Hlen2: length vs2 <=zt):
      fail_iexec P G t (acq t (X + x) :: events_hb_check (W + x) (C + t) vs1 vs2 t ++
                       events_hb_check (R + x) (C + t) vs3 vs2 t)
                  (Acq t (X + x) ::
                       mops_hb_check (W + x) (C + t) vs1 vs2 zt t ++
                  mops_hb_check (R+x) (C + t) vs3 vs2 zt t )
        (*[]
        (upd_env (upd_env G t tmp1 v1) t tmp2 v2) *)
  | fail_assert P1 P2 e1 e2 rest
      (Hassert : P = P1 ++ (t, Assert_le e1 e2 :: rest) :: P2)
      (Hfail : eval (G t) e1 > eval (G t) e2) :
      fail_iexec P G t [] [] (*[] G*).

Lemma instrument_sim_race2 : forall (*P*) P1 P2 G1 G2 t (*h*)
  (Hfresh : fresh_tmps P1) (Hlocs : safe_locs P1)
  (Ht : Forall (fun e => fst e < zt) P1) (Hdistinct: distinct P2)
  (HPsim : state_sim P1 P2) (HGsim : env_sim G1 G2)
  m (*(Hroot : exec_star (Some (init_state P)) init_env h m (Some P1) G1)*)
  (Hinit : forall p, meta_loc p -> initialized m p)
  o2 c2 (Hstep : fail_iexec P2 G2 t o2 c2)
  (Hcon : consistent (m ++ c2)) s (Hs : clocks_sim m s),
  exists o c P1' G1', exec P1 G1 t o c (Some P1') G1' /\
    forall s', ~step_star s (opt_to_list o) s'.
Proof.
  clarify.
  inversion Hstep; clarify; exploit Forall2_app_inv_r; eauto;
  intros (P0' & P3' & HP0 & Hrest & HP1);
  inversion Hrest as [|(tx, [|i ?]) ? ? ? [? Hi] HP3]; clarify.
  -exploit (instrument_incom (Load a (x,o))).
   { instantiate(1:= instrument l t). instantiate (1:= t). instantiate (1:= i). instantiate (1:=rest).  simpl. rewrite <- app_assoc. clarify. }
   clarify.
   do 4 eexists. split; clarify.
   +eapply exec_load; eauto.
   +clarify. intro Hss. inversion Hss; 
    setoid_rewrite Forall_app in Hlocs; clarify.
    inversion Hlocs2 as [|?? Hi ?]; clarify.
    inversion Hi; clarify.
    setoid_rewrite Forall_app in Ht; clarify.
    inversion Ht2; clarify.
    inversion Hstep0; clarify. unfold clocks_sim in Hs; clarify.
    specialize (Hs22 x H32). clarify.
    exploit hb_check_vals'.
    { clarify. specialize (Hinit (W'+x, z)).  apply Hinit.
      unfold meta_loc. simpl. omega. }
    { clarify. specialize (Hinit (C'+t, z)).  apply Hinit.
      unfold meta_loc. simpl. omega. }
    {
      exploit loc_valid_ops_SC.
      {instantiate (1:=[Acq t (X'+x)]). instantiate(1:=mops_hb_check (W'+x ) (C'+t) vs1 vs2 zt t).
       rewrite Forall_forall. clarify. rewrite Forall_forall. intros c Hin.
       apply in_mops_hb_check in Hin. intro Heq; destruct c; clarify.
       destruct Hin as [Hin | Hin]; clarify.
       +specialize(Hmetalocs_disjoint_WX H32 H32); clarify.
       +specialize(Hmetalocs_disjoint_CX H3 H32); clarify.
      }
      {rewrite Forall_forall. clarify. }
      {clarify. }
      intro Hcon_iff.
      instantiate (1:=m) in Hcon_iff. clarify. rewrite Hcon_iff in Hcon.
      clarify. eapply Hcon2.
    }
    { eauto. }
    { eauto.  }
    { apply Hs222. }
    { specialize (Hs1 t H3). apply Hs1. }
    { eauto. }
    { auto. }
    clarify.
   -exploit (instrument_incom (Store (x,o) e)).
   { instantiate(1:= instrument l t). instantiate (1:= t). instantiate (1:= i). instantiate (1:=rest).  simpl. rewrite <- app_assoc. clarify. }
   clarify.
   do 4 eexists. split; clarify.
   +eapply exec_store; eauto.
   +clarify. intro Hss. inversion Hss; 
    setoid_rewrite Forall_app in Hlocs; clarify.
    inversion Hlocs2 as [|?? Hi ?]; clarify.
    inversion Hi; clarify.
    setoid_rewrite Forall_app in Ht; clarify.
    inversion Ht2; clarify.
    inversion Hstep0; clarify. unfold clocks_sim in Hs; clarify.
    specialize (Hs22 x H32). clarify.
    exploit hb_check_vals'.
    { clarify. specialize (Hinit (W'+x, z)).  apply Hinit.
      unfold meta_loc. simpl. omega. }
    { clarify. specialize (Hinit (C'+t, z)).  apply Hinit.
      unfold meta_loc. simpl. omega. }
    {
      exploit loc_valid_ops_SC.
      {instantiate (1:=[Acq t (X'+x)]). instantiate(1:=mops_hb_check (W'+x ) (C'+t) vs1 vs2 zt t).
       rewrite Forall_forall. clarify. rewrite Forall_forall. intros c Hin.
       apply in_mops_hb_check in Hin. intro Heq; destruct c; clarify.
       destruct Hin as [Hin | Hin]; clarify.
       +specialize(Hmetalocs_disjoint_WX H32 H32); clarify.
       +specialize(Hmetalocs_disjoint_CX H3 H32); clarify.
      }
      {rewrite Forall_forall. clarify. }
      {clarify. }
      intro Hcon_iff.
      instantiate (1:=m) in Hcon_iff. clarify. rewrite Hcon_iff in Hcon.
      clarify. eapply Hcon2.
    }
    { eauto. }
    { eauto.  }
    { apply Hs222. }
    { specialize (Hs1 t H3). apply Hs1. }
    { eauto. }
    { auto. }
    clarify.
   -exploit (instrument_incom (Store (x,o) e)).
   { instantiate(1:= instrument l t). instantiate (1:= t). instantiate (1:= i). instantiate (1:=rest).  simpl. rewrite <- app_assoc. clarify. }
   clarify.
   do 4 eexists. split; clarify.
   +eapply exec_store; eauto.
   +clarify. intro Hss. inversion Hss; 
    setoid_rewrite Forall_app in Hlocs; clarify.
    inversion Hlocs2 as [|?? Hi ?]; clarify.
    inversion Hi; clarify.
    setoid_rewrite Forall_app in Ht; clarify.
    inversion Ht2; clarify.
    inversion Hstep0; clarify. unfold clocks_sim in Hs; clarify.
    specialize (Hs22 x H32). clarify.
    exploit hb_check_vals'.
    { clarify. specialize (Hinit (R'+x, z)).  apply Hinit.
      unfold meta_loc. simpl. omega. }
    { clarify. specialize (Hinit (C'+t, z)).  apply Hinit.
      unfold meta_loc. simpl. omega. }
    {
      (*
      assert(Hcon_acq: consistent (m ++ [Acq t (X' +x)])).
      {
        eapply consistent_app_SC.
        instantiate(1:= mops_hb_check (W'+x ) (C'+t) vs1 vs2 zt t ++ mops_hb_check (R'+x ) (C'+t) vs3 vs2 zt t). rewrite <-app_assoc. clarify.
      }*)
      rewrite split_app, <- app_assoc in Hcon.
      apply loc_valid_ops_SC in Hcon; clarify.
      -eapply reads_noops_SC.
       { instantiate (1:=mops_hb_check (W'+x ) (C'+t) vs1 vs2 zt t).
         eapply consistent_app_SC;rewrite <- app_assoc; eauto. }
       { rewrite Forall_forall. intros c Hin. apply in_mops_hb_check in Hin.
         destruct c; clarify. }
       { eauto. }
      -rewrite Forall_forall. intros c Hin. inversion Hin. clarify.
       rewrite Forall_forall. intros c Hin. rewrite in_app in Hin.
       intro Heq. destruct Hin as [Hin | Hin]; apply in_mops_hb_check in Hin; destruct c; clarify;
       destruct Hin as [Hin | Hin]; clarify.
       +specialize(Hmetalocs_disjoint_WX H32 H32). clarify.
       +specialize(Hmetalocs_disjoint_CX H3 H32). clarify.
       +specialize(Hmetalocs_disjoint_RX H32 H32). clarify.
       +specialize(Hmetalocs_disjoint_CX H3 H32). clarify.
       +inversion H; clarify.
      -rewrite Forall_forall. clarify.
      -rewrite Forall_app. clarify.
    } 
    { auto. }
    { auto. }
    { apply Hs221. }
    { specialize (Hs1 t H3). apply Hs1. }
    { eauto. }
    { auto. }
    clarify.
   - 
Abort.

Theorem instrument_correct : forall P h m P' G'
  (HP : exec_star (Some (init_state P)) init_env h m (Some P') G'),
  (exists h2 m2 P2' G2', exec_star
     (Some (init_state (instrument C L  P 0))) init_env h2 m2
     (Some P2') G2') <-> exists s, step_star s0 h s.
Proof.
Abort.

End Sim_Proofs.