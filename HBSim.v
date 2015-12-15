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
Hypothesis Hmetalocs_disjoint_WX: forall y x,  (y < zv -> x < zv -> W' + y <> X' + x).
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
    rewrite Forall_forall. intros. inversion H0. clarify.
    *specialize(Hmetalocs_disjoint t x x x x ). inversion Hmetalocs_disjoint; clarify.
     intro Heq. inversion Heq; clarify.
    *inversion H1.
   +apply can_write_SC; auto.
    constructor; clarify.
  -unfold clock_match. intros.
   destruct (lt_dec t zt); simpl.
   specialize(Hs_l l H). unfold clock_match in Hs_l. specialize(Hs_l t).
   split; auto.
   +apply can_read_SC; clarify.
    apply acq_con; auto.
    { constructor; clarify. }
    rewrite Forall_forall. intros.  inversion H0. clarify.
    *specialize(Hmetalocs_disjoint t l x x x). inversion Hmetalocs_disjoint; clarify.
     intro Heq. inversion Heq; clarify.
    *inversion H1.
   +apply can_write_SC; clarify.
    apply acq_con; auto.
    { constructor; clarify. }
   +specialize(Hs_l l H). unfold clock_match in Hs_l. specialize(Hs_l t). clarify.
  -unfold clock_match. intros; destruct (lt_dec t zt); clarify;
   specialize(Hs_rw v H); unfold clock_match in Hs_rw; inversion Hs_rw.
   +clarify. specialize(Hs_rw1 t). clarify. split; auto.
    *apply can_read_SC; auto.
     apply acq_con; auto.
     { constructor; clarify. }
     rewrite Forall_forall. intros. inversion H0. clarify.
     {
       specialize(Hmetalocs_disjoint t x x x v). inversion Hmetalocs_disjoint; clarify.
       intro Heq. inversion Heq; clarify.
     } 
     { inversion H1. }
    *apply can_write_SC; auto.
     apply acq_con; auto.
     { constructor; clarify. }
   +specialize(H0 t). clarify.
  
   -unfold clock_match. intros; destruct (lt_dec t zt); clarify;
    specialize(Hs_rw v H); unfold clock_match in Hs_rw; inversion Hs_rw.
    +clarify. specialize(Hs_rw2 t). clarify. split; auto.
    *apply can_read_SC; auto.
     apply acq_con; auto.
     { constructor; clarify. }
     rewrite Forall_forall. intros. inversion H0. clarify.
     {
       specialize(Hmetalocs_disjoint t x x v v). inversion Hmetalocs_disjoint; clarify.
       intro Heq. inversion Heq; clarify.
     } 
     { inversion H1. }
    *apply can_write_SC; auto.
     apply acq_con; auto.
     { constructor; clarify. }
   +specialize(H1 t). clarify.
Qed.

Hypothesis zt_non_zero : zt <> 0.
(*
Lemma instrument_sim_safe : forall P P1 P2 G1 G2 t h
  (Hfresh : fresh_tmps P1) (Hlocs : safe_locs P1) (Hdistinct : distinct P2)
  (Ht : Forall (fun e => fst e < zt) P1) 
  (Ht_spawn: Forall (fun p =>  match p with
                                 | (t0,Spawn u li::rest) => u <> t0
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
  - destruct x as (x, o).
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
      unfold meta_loc. clarify. repeat right. omega.
  -destruct x as (x,o). (* store *)
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
        } 
 -(*lock*)
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
      eapply mops_max_vc_meta; eauto.
 -(*unlock*)
   inversion Hsafe; clarify.
   inversion Hstep0; clarify.
   rewrite <- app_assoc; simpl; do 5 eexists; [|split].
   + apply iexec_unlock; eauto.
     { instantiate(1:=map (C t0) (rev (interval 0 zt))).
       rewrite map_length, rev_length, interval_length.
       omega.
     }
     { instantiate(1:=map (L m0) (rev (interval 0 zt))).
       rewrite map_length, rev_length, interval_length.
       omega.
     }
   +(*consistent*)
      setoid_rewrite Forall_app in Hlocs; clarify.
      inversion Hlocs2 as [|?? Hi ?]; clarify.
      inversion Hi; clarify.
      rewrite Forall_app in Ht; clarify.
      inversion Ht2; clarify.
      assert(Htrivial: forall (X:Type) (a b c:X), [a;b;c]=[a]++[b;c]).
        intros. auto.
      instantiate(1:=C t0 t0).
      rewrite Htrivial.
      rewrite app_assoc. rewrite app_assoc.
      assert ((C' + t0, t0) <> (m0, 0)).
      { assert(HCt0: meta_loc(C'+t0,t0)).
          unfold meta_loc. clarify. omega.
        intro; clarify. }
      rewrite loc_valid_SC; auto.
      assert (consistent ((m ++
        mops_max_vc (C' + t0) (L' + m0) (map (C t0) (rev (interval 0 zt)))
        (map (L m0) (rev (interval 0 zt))) t0 zt) ++
        [Read t0 (C' + t0, t0) (C t0 t0)])) as Hcon0.
      { 
        apply can_read_thread.
       
        apply can_read_SC; auto.
        +inversion Hs; clarify. 
         specialize(Hs_c t0 H2); clarify. unfold clock_match in Hs_c; clarify.
         specialize(Hs_c t0); clarify.
        +eapply (mops_max_vc_con_cl Hs); eauto.
         eapply consistent_app_SC. eauto.
        +rewrite Forall_forall; clarify.
         destruct x; clarify.
         apply in_mops_max_vc in H1.
          *intro Heq. clarify.
          *specialize(Hmetalocs_disjoint t0 m0 t0 t0 t0). 
           inversion Hmetalocs_disjoint; clarify.
          *apply in_mops_max_vc in H1; auto.
           specialize(Hmetalocs_disjoint t0 m0 t0 t0 t0).
           inversion Hmetalocs_disjoint; clarify.
         
      }
      split; clarify.
      *apply can_write_thread.
       apply can_write_SC.
       { unfold can_write; clarify.
         apply can_write_SC; auto.
         -unfold can_write; clarify.
          inversion Hs; clarify. simpl.
          specialize(Hs_c _ H2); unfold clock_match in Hs_c; clarify.
          specialize(Hs_c t0); clarify.
         -eapply consistent_app_SC; eauto.
       }
       { auto. }
       { constructor; simpl; auto. }
     *rewrite <- app_assoc. rewrite <- app_assoc. 
      assert (Hlist_silly : forall (X:Type) (l1 l2 l3 l4: list X), 
               l1++l2++l3++l4=l1++(l2++l3)++l4).
        intros. rewrite <-app_assoc. clarify.
     
      setoid_rewrite Hlist_silly.
      
      setoid_rewrite loc_valid_ops_SC.
      split; clarify.
      rewrite app_assoc. clarify.
      rewrite Forall_forall.  intros. rewrite Forall_forall. clarify. simpl.
      rewrite in_app in H1. inversion H1; clarify. 
      intro Heq. contradiction H21. setoid_rewrite Heq.  eapply mops_max_vc_meta; eauto.
      rewrite Forall_app; split; auto; constructor; simpl; auto.
      constructor; simpl; auto.
     *simpl; auto.
     *simpl; auto.
    +(*mem_sim*)
     setoid_rewrite Forall_app in Hlocs; clarify.
     inversion Hlocs2; clarify.
     inversion H1. clarify. rewrite Forall_forall in H1.
     rewrite Forall_app in Ht; clarify. 
     inversion Ht2; clarify.
     unfold mem_sim in *; clarify. split; clarify; repeat rewrite in_app in *; clarify.
     left.
     destruct H0 as [? | [? | [? | ?]]]; clarify; contradiction H6.
     *eapply mops_max_vc_meta; eauto.
     *left; simpl; abstract omega.
     *left; simpl; abstract omega.
 -(*spawn*)
   inversion Hsafe; clarify.
   inversion Hstep0; clarify.
   do 5 eexists; [|split].
   +(*iexec*)
    apply iexec_spawn; eauto. Check iexec_spawn.
    { rewrite <- split_app. eauto. }
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
      setoid_rewrite Hmap_fst. auto.
      intros ? ? H0. inversion H0; clarify.
    }
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
       apply (mops_set_vc_con_cc Hs); eauto.
       rewrite app_nil_r in Hcon. auto.
     }
     { rewrite Forall_forall. intros x Hin. apply in_mops_set_vc in Hin.
       destruct x; clarify.
       intro Heq. 
       assert(Ht0u : t0 = u).
         rewrite <- minus_plus with (n:=C').
         rewrite <- Heq. rewrite minus_plus. auto.
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
     *apply (mops_set_vc_meta_cc (map (C t0) (rev (interval 0 zt))) zt c H31 H3). auto.
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

    eapply (mops_max_vc_con_cc Hs); eauto.
    rewrite <- app_nil_end in Hcon. auto.
   +(*mem_sim*) 
     
     unfold mem_sim. intros. clarify. split; intros; clarify.
     contradiction H02.
    rewrite Forall_app in Ht; clarify.
    inversion Ht2; clarify.    
     apply (mops_max_vc_meta_cc (map (C u) (rev (interval 0 zt)))
                                (map (C t0) (rev (interval 0 zt)))
              zt c Hu H2); eauto.
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

(*
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

Lemma instrument_nonnil : forall i t, instrument_instr i t <> [].
Proof.
  destruct i; repeat intro; clarify.
  - destruct x, zt; clarify.
  - destruct x, zt; clarify.
  - destruct zt; clarify.
  - destruct zt; clarify.
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
Qed.
*)
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
(*
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


(*
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
      destruct (lt_dec j (length (max_vc (C + t) (L + m) zt tmp1 tmp2)));
      [exploit max_vc_no_wait; eauto; clarify|].
    destruct (j - length (max_vc (C + t) (L + m) zt tmp1 tmp2)); clarify.
    do 4 (destruct n0; clarify).
  - unfold spawn_handler in Hnth.
    rewrite <- app_assoc, nth_error_app in Hnth;
      destruct (lt_dec j (length (set_vc (C + t0) (C + t) zt tmp1)));
      [exploit set_vc_no_wait; eauto; clarify|].
    destruct (j - length (set_vc (C + t0) (C + t) zt tmp1)); clarify.
    do 4 (destruct n0; clarify).
  - destruct j; clarify.
    exploit max_vc_no_wait; eauto; clarify.
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
  length (load_handler t x z) = 3 * z + 4.
Proof.
  unfold load_handler; clarify.
  rewrite app_length, hb_check_len; simpl; omega.
Qed.

Lemma store_handler_len : forall t x z,
  length (store_handler t x z) = 6 * z + 4.
Proof.
  unfold store_handler; clarify.
  repeat rewrite app_length, hb_check_len; simpl; omega.
Qed.

Lemma lock_handler_len : forall t l z,
  length (lock_handler t l z) = 4 * z.
Proof.
  intros; apply max_vc_len.
Qed.

Lemma unlock_handler_len : forall t l z,
  length (unlock_handler t l z) = 4 * z + 3.
Proof.
  unfold unlock_handler; clarify.
  rewrite app_length, max_vc_len; simpl; omega.
Qed.

Lemma spawn_handler_len : forall t u z tmp,
  length (spawn_handler t u z tmp) = 2 * z + 3.
Proof.
  unfold spawn_handler; clarify.
  rewrite app_length, set_vc_len; simpl; omega.
Qed.

Lemma wait_handler_len : forall t u z,
  length (wait_handler t u z) = 4 * z.
Proof.
  intros; apply max_vc_len.
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

Lemma t_steps_lock : forall P G t lo lc P1 G1 m li
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
Qed.

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
(*
Lemma t_steps_unlock : forall P G t lo lc P1 G1 m li
  (Hdistinct : distinct P)
  (Hin : In (t, instrument_instr (Unlock m) t ++ li) P)
  (Hsteps : t_steps P G t (length (instrument_instr (Unlock m) t) - 1) lo
                    lc (Some P1) G1) o' c' P2 G2
  (Hend : exec P1 G1 t o' c' (Some P2) G2) (Hin' : In (t, li) P2),
  exists vs1 vs2 v,
    filter (fun c => beq (thread_of c) t) (lc ++ opt_to_list c') =
    mops_max_vc (C' + t) (L' + m) vs1 vs2 t zt ++
    mops_inc_vc (C' + t) v t ++ [Rel t m].
Proof.
  intros.
  unfold instrument_instr in Hsteps.
  rewrite app_length in Hsteps; simpl in Hsteps.
  rewrite Nat.add_sub in Hsteps; unfold unlock_handler in Hsteps.
  rewrite app_length in Hsteps; exploit t_steps_plus; eauto.
  intros (lo1 & lc1 & P3 & G3 & lo2 & lc2 & Hmax & Hrest & ? & ?); subst.
  exploit t_steps_max_vc; eauto.
  { unfold instrument_instr, unlock_handler in Hin;
      repeat rewrite <- app_assoc in Hin; eauto. }
  intros (vs1 & vs2 & Hlc1); exists vs1, vs2.
  exploit distinct_steps; eauto.
  { eapply t_steps_exec, Hmax; eauto. }
  intro; exploit t_steps_length'; try apply Hmax; auto.
  { unfold instrument_instr, unlock_handler in Hin;
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

Lemma t_steps_spawn : forall P G t lo lc P1 G1 u li' li
  (Hdistinct : distinct P)
  (Hin : In (t, instrument_instr (Spawn u li') t ++ li) P)
  (Hsteps : t_steps P G t (length (instrument_instr (Spawn u li') t) - 1) lo
                    lc (Some P1) G1) o' c' P2 G2
  (Hend : exec P1 G1 t o' c' (Some P2) G2) (Hin' : In (t, li) P2),
  exists vs v,
    filter (fun c => beq (thread_of c) t) (lc ++ opt_to_list c') =
    mops_set_vc (C' + t) (C' + u) zt t vs ++
    mops_inc_vc (C' + t) v t.
Proof.
  intros.
  simpl in *.
  rewrite app_length in Hsteps; simpl in Hsteps.
  rewrite Nat.add_sub in Hsteps; unfold spawn_handler in Hsteps.
  rewrite app_length in Hsteps; exploit t_steps_plus; eauto.
  intros (lo1 & lc1 & P3 & G3 & lo2 & lc2 & Hset & Hrest & ? & ?); subst.
  exploit t_steps_set_vc; eauto.
  { unfold spawn_handler in Hin; repeat rewrite <- app_assoc in Hin; eauto. }
  intros (vs & Hlc1); exists vs.
  exploit distinct_steps; eauto.
  { eapply t_steps_exec, Hset; eauto. }
  intro; exploit t_steps_length'; try apply Hset; auto.
  { unfold spawn_handler in Hin; repeat rewrite <- app_assoc in Hin; eauto. }
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

Lemma t_steps_wait : forall P G t lo lc P1 G1 u li
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

Definition accesses i p := match i with
| Load _ p' => p' = p
| Store p' _ => p' = p
| Lock m => p = (m, 0)
| Unlock m => p = (m, 0)
| _ => False
end.

Lemma exec_accesses : forall P G t (Hdistinct : distinct P) o c P' G'
  (Hexec : exec P G t o c P' G') i rest (Hi : In (t, i :: rest) P) l,
  (match c with Some c => loc_of c = l | None => False end) <-> accesses i l.
Proof.
  intros.
  exploit in_split; eauto; clarify.
  inversion Hexec; exploit distinct_thread; eauto; clarify; split; clarify.
Qed.

Typeclasses eauto := 5.

Lemma hb_check_instr : forall C1 C2 z tmp1 tmp2 i
  (Hi : In i (hb_check C1 C2 z tmp1 tmp2)) l (Haccess : accesses i l),
  exists n, n < z /\ (l = (C1, n) \/ l = (C2, n)).
Proof.
  induction z; clarify.
  destruct Hi as [? | [? | ?]]; clarify; eauto.
  exploit IHz; eauto; intros (n & ?); exists n; clarify.
Qed.  

Lemma max_vc_instr : forall src tgt z tmp1 tmp2 i
  (Hi : In i (max_vc src tgt z tmp1 tmp2)) l (Haccess : accesses i l),
  exists n, n < z /\ (l = (src, n) \/ l = (tgt, n)).
Proof.
  induction z; clarify.
  destruct Hi as [? | [? | [? | [? | ?]]]]; clarify; eauto.
  exploit IHz; eauto; intros (n & ?); exists n; clarify.
Qed.  

Lemma set_vc_instr : forall src tgt z tmp i
  (Hi : In i (set_vc src tgt z tmp)) l (Haccess : accesses i l),
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
  (Haccess : accesses i (C' + t', n)), t' = t \/
  (exists i', In i' li /\ In i (instrument_instr i' t) /\
   match i' with Spawn u _ | Wait u => t' = u
   | _ => False end).
Proof.
  induction li; clarify.
  inversion Hsafe as [|?? Hsafe' ?]; clarify.
  rewrite in_app in Hi; destruct Hi.
  destruct a; clarify.
  - left; destruct x; clarify.
    repeat rewrite in_app in H; simpl in H.
    generalize (Hmetalocs_disjoint t' 0 v v v).
    destruct H as [? | [[? | ?] | [? | ?]]]; clarify.
    + exploit hb_check_instr; eauto; intros (? & ? & [? | ?]); clarify.
      * admit.
      * eapply plus_reg_l; eauto.
    + destruct H; clarify.
      * eapply plus_reg_l; eauto.
      * admit.
    + contradiction Hsafe'1; unfold meta_loc; left; simpl; omega.
  - left; destruct x; clarify.
    repeat rewrite in_app in H; simpl in H.
    generalize (Hmetalocs_disjoint t' 0 v v v).
    destruct H as [? | [[? | [? | [? | ?]]] | [? | ?]]]; clarify.
    + exploit hb_check_instr; eauto; intros (? & ? & [? | ?]); clarify.
      * admit.
      * eapply plus_reg_l; eauto.
    + exploit hb_check_instr; eauto; intros (? & ? & [? | ?]); clarify.
      * admit.
      * eapply plus_reg_l; eauto.
    + eapply plus_reg_l; eauto.
    + admit.
    + contradiction Hsafe'1; unfold meta_loc; left; simpl; omega.
  - left; unfold lock_handler in H.
    generalize (Hmetalocs_disjoint t' m 0 0 0).
    destruct H; clarify.
    + contradiction Hsafe'1; left; simpl; omega.
    + exploit max_vc_instr; eauto; intros (? & ? & [? | ?]); clarify.
      eapply plus_reg_l; eauto.
  - left; unfold unlock_handler in H; repeat rewrite in_app in H.
    generalize (Hmetalocs_disjoint t' m 0 0 0).
    destruct H as [[? | ?] | ?]; clarify.
    + exploit max_vc_instr; eauto; intros (? & ? & [? | ?]); clarify.
      eapply plus_reg_l; eauto.
    + destruct H as [? | [? | ?]]; clarify; eapply plus_reg_l; eauto.
    + contradiction Hsafe'1; left; simpl; omega.
  - unfold spawn_handler in H; repeat rewrite in_app in H.
    destruct H as [[? | ?] | ?]; clarify.
    + exploit set_vc_instr; eauto; intros (? & ? & [? | ?]); clarify.
      * left; eapply plus_reg_l; eauto.
      * right; eexists; split; eauto; simpl.
        split; [|eapply plus_reg_l; eauto].
        unfold spawn_handler; repeat rewrite in_app; auto.
    + left; destruct H as [? | [? | ?]]; clarify; eapply plus_reg_l; eauto.
  - unfold wait_handler in H.
    exploit max_vc_instr; eauto; intros (? & ? & [? | ?]); clarify.
    + right; eexists; split; eauto; clarify.
      eapply plus_reg_l; eauto.
    + left; eapply plus_reg_l; eauto.
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
  t' (Ht' : t' < zt) n (Haccess : accesses i (C' + t', n)), t' = t \/
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
    exploit max_vc_instrs; eauto; clarify.
  - repeat setoid_rewrite in_app in H.
    destruct H as [[? | ?] | ?]; clarify.
    + exploit set_vc_instrs; eauto; clarify.
    + inversion H.
      do 2 eexists; eauto.
  - exploit max_vc_instrs; eauto; clarify.
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
  exists P2 lo2 lc2 G2 n' i' li' rest lo2' lc2',
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
    repeat eexists; try apply exec_refl.
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
    destruct Ht as [? | [? | [? | ?]]]; try solve [
      exploit IHHsteps; eauto; clarify; repeat eexists; eauto;
      eapply exec_step_inv; eauto].
    + clarify.
      exploit IHHsteps; eauto; intros (? & ? & ? & ? & n' & i' & li' & rest & ? 
        & ? & ? & ? & Hli' & Hli & ? & Hrest & ?); clarify.
      destruct li'; clarify.
      * destruct rest; clarify.
        inversion Hrest; clarify.
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
      * repeat eexists; eauto.
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
Qed.

(* up *)
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
  intros (? & ? & ? & ? & n' & i' & ? & ? & ? & ? & ? & ? & Hi' & ?); clarify.
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

Fixpoint no_spawn t i :=
  let fix no_spawn_list l :=
    match l with
    | [] => True
    | i :: rest => no_spawn t i /\ no_spawn_list rest
    end in
  match i with
  | Spawn u li' => u <> t /\ no_spawn_list li'
  | _ => False
  end.

Lemma no_spawns : forall t l, (fix f l := match l with [] => True |
  i :: rest => no_spawn t i /\ f rest end) l <->
  Forall (no_spawn t) l.
Proof.
  induction l; split; clarify; rewrite IHl in *; clarify.
  inversion H; clarify.
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

Lemma own_thread : forall t P1 G lo lc P1' G' (Ht : t < zt)
  (Hsteps : exec_star_minus t (Some P1) G lo lc P1' G')
  P (Hsafe : safe_locs P) P0 (Hsim : state_sim P P0)
  (Hdistinct : distinct P0) G0 lo0 lc0
  (Hroot : exec_star (Some P0) G0 lo0 lc0 (Some P1) G)
  li (Hlive : In (t, li) P1) (Hli : li <> [])
  (Hspawns : Forall (fun p => Forall (no_spawn t) (snd p)) P1),
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
    + rewrite Forall_app in Hspawns; clarify.
      inversion Hspawns2 as [|?? Hspawn]; clarify.
      rewrite <- Hli' in Hspawn.
      rewrite skipn_app in *; repeat rewrite Forall_app in *;
        rewrite app_length in *; clarify.
      destruct (n' - length (spawn_handler t' t0 zt tmp1)) eqn: Hminus;
        [clarify | omega].
      inversion Hspawn12; clarify.
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
    destruct th; simpl in *.
    + destruct i; clarify.
      eapply IHHsteps; eauto.
      * eapply exec_step_inv; eauto.
      * eapply exec_other_thread; eauto.
      * rewrite Forall_app in *; clarify.
        inversion Hspawns2 as [|?? Hspawn]; inversion Hspawn; clarify;
          repeat constructor; clarify.
        rewrite (no_spawns t) in *; auto.
    + eapply IHHsteps; eauto.
      * eapply exec_step_inv; eauto.
      * eapply exec_other_thread; eauto.
      * rewrite Forall_app in *; clarify.
        inversion Hspawns2 as [|?? Hspawn]; inversion Hspawn; clarify;
          constructor; clarify.
Qed.

Lemma instrument_indep : forall P G t lo lc P1 G1 i li
  (Hdistinct : distinct P) (Hin : In (t, instrument_instr i t ++ li) P)
  (Hsteps : t_steps P G t (length (instrument_instr i t) - 1) lo lc
                    (Some P1) G1) o c P2 G2
  (Hend : exec P1 G1 t o c (Some P2) G2) (Hin' : In (t, li) P2)
  m (Hcon : consistent (m ++ lc ++ opt_to_list c)),
  Forall (fun c1 => Forall (fun c2 => loc_of c2 <> loc_of c1)
    (filter (fun c => beq (thread_of c) t) (lc ++ opt_to_list c)))
    (filter (fun x => negb (beq (thread_of x) t)) lc).
Proof.
  intros; destruct i; clarify; rewrite Forall_locs.
  - destruct x; exploit t_steps_load; simpl; eauto.
    intros (vs1 & vs2 & vt & v' & Hlct); rewrite Hlct.
    simpl; rewrite map_app; simpl.
    simpl in Hsteps; rewrite app_length in Hsteps; simpl in Hsteps.
    
    rewrite Forall_forall; repeat intro.
    (* Other threads can't touch:
       X, R, or W for v, or v, because the lock is held
       C for t, because they aren't t. *)
    
    
Abort.


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
    (* As above. *) admit.
  - eapply component_decr; eauto.
    { eapply exec_t_exec; eauto. }
    rewrite app_length, Hinstr; simpl; omega.
Qed.
*) *)
*)

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



Lemma hb_check_C_diff : forall x C1 C2 y z t1 t2
  (Hnonzero : z <> 0) (Hdist: C1 <> C2), 
  hb_check (x+C1) y z t1 t2 <> hb_check (x+C2) y z t1 t2.
Admitted.

 
Lemma instrument_sim_safe2 : forall P P1 P2 G1 G2 t h
  (Hfresh : fresh_tmps P1) (Hlocs : safe_locs P1)
  (Ht : Forall (fun e => fst e < zt) P1)
  (HPsim : state_sim P1 P2) (HGsim : env_sim G1 G2)
  m (Hroot : exec_star (Some (init_state P)) init_env h m (Some P1) G1)
  o2 c2 P2' G2' (Hstep : iexec P2 G2 t o2 c2 P2' G2')
  (Hcon : consistent (m ++ c2)) s (Hs : clocks_sim m s),
  exists o c P1' G1', exec P1 G1 t o c (Some P1') G1' /\
    state_sim P1' P2' /\ env_sim G1' G2' /\ consistent (m ++ opt_to_list c) /\
    mem_sim c c2 /\
        exists s', step_star s (opt_to_list o) s' /\
                   clocks_sim (m ++ c2) s'.
Proof.
  intros.
  inversion Hs as [ Hs_c (Hs_l,Hs_rw)]; clarify.
  assert (Hemc: exists o c P1' G1', exec P1 G1 t o c (Some P1') G1' /\mem_sim c c2 /\ consistent (m ++ opt_to_list c) ).
   inversion Hstep; clarify;  exploit Forall2_app_inv_r; eauto ;
   intros (P0' & P3' & HP0 & Hrest & HP1);
   inversion Hrest as [|? (?, ?) ? ? ? HP3]; clarify.
   -(*assign*)destruct x as (tx,ix); destruct ix; clarify.
    unfold instrument_instr in H12; clarify. destruct i; clarify.
    +do 4 eexists. split;[|split].
     *apply exec_assign. eauto.
     *unfold mem_sim. intros. simpl. split; clarify.
     *simpl. auto.
    +
     destruct x as (x0,o). simpl in H12.  do 2 rewrite <- app_assoc in H12. inversion H12.  
    + destruct x as (x0,o). simpl in H12.  do 2 rewrite <- app_assoc in H12. inversion H12.
    +destruct zt; clarify.
    +destruct zt; clarify.
   -(*load*) 
    destruct x0 as (tx, ix); destruct ix; clarify.
    unfold instrument_instr in H12; clarify. destruct i; clarify.
    +do 4 eexists. split;[|split].
     *apply exec_load. eauto.
     *unfold mem_sim. intros. simpl. split; clarify.
      { split.
        -right.
         destruct x0; clarify. 
         do 2 rewrite split_app in H1. do 5 rewrite <- app_assoc in H1. simpl in H1.
         destruct (eq_dec x v0); destruct (eq_dec n o); clarify.
         +apply in_app. right. unfold In. eauto.
         +apply app_inv_head in H1. clarify.
         +apply (hb_check_C_diff W' (C'+tx) tmp1 tmp2 zt_non_zero) in n0. apply list_part_same in H1. clarify. do 2 rewrite length_hb_check. auto.
         +apply (hb_check_C_diff W' (C'+tx) tmp1 tmp2 zt_non_zero) in n0. apply list_part_same in H1. clarify. do 2 rewrite length_hb_check. auto.
        -setoid_rewrite Forall_app in Hlocs. clarify. inversion Hlocs2; clarify. inversion H1. 
         unfold safe_instr in H3. clarify. 
      }  
      {left.
       setoid_rewrite Forall_app in Hlocs. clarify. inversion Hlocs2; clarify. inversion H3; clarify.
       rewrite Forall_app in Ht. clarify. inversion Ht2; clarify.
       destruct x0; destruct (eq_dec x v0); destruct (eq_dec n o); clarify.
       -inversion H1; clarify. 
        +contradiction H2. unfold meta_loc. simpl. repeat right. omega.
        +rewrite in_app in H. inversion H; clarify.
         *apply in_mops_hb_check in H8. destruct c; clarify. inversion H8; destruct x; clarify.
          contradiction H2. unfold meta_loc. simpl. omega.
          contradiction H2. unfold meta_loc. simpl. left.  omega.
         *inversion H8; clarify.
          contradiction H2. unfold meta_loc. simpl. left. omega.
          inversion H9; clarify. contradiction H2. unfold meta_loc. simpl. do 2 right. left. omega.
          contradiction H2. unfold meta_loc. simpl. repeat right. omega.
       -repeat rewrite <-app_assoc in H0.  do 2 apply app_inv_head in H0.
        inversion H0; clarify.
       -apply plus_reg_l in H0. clarify.
       -apply plus_reg_l in H0. clarify.
      }
     *
assert(Hlist_silly1: forall (X:Type) (a b c d e: X) (l1 l2 l3 l4: list X), 
               l1++a::l2++[b;c;d;e]=(l1++[a])++(l2++[b;c])++[d;e]).
       intros. simpl. do  2 rewrite app_assoc. clarify. rewrite split_app. rewrite app_assoc. do 2 rewrite split_app. repeat rewrite <- app_assoc. simpl. auto.
      rewrite Hlist_silly1 in Hcon; auto. rewrite loc_valid_ops_SC in Hcon.
      {
        inversion Hcon; clarify. 
        assert(Hacq_con: consistent (m ++ [Acq tx (X'+x)])).
         eapply consistent_app_SC. eauto.
        rewrite loc_valid_ops2_SC in Hcon2.
        -inversion Hcon2; clarify. rewrite <- app_assoc in Hcon22. rewrite loc_valid_ops_SC in Hcon22.
         +inversion Hcon22; clarify.
          destruct x0; destruct (eq_dec x v0); destruct (eq_dec n o); clarify.
          *simpl in H0. repeat rewrite <- app_assoc in H0. simpl in H0.
           eapply app_inv_head in H0. inversion H0. clarify.
          *apply plus_reg_l in H0. clarify.
          *apply plus_reg_l in H0. clarify.
         +rewrite Forall_forall. intros x1 Hin. inversion Hin; clarify.
          rewrite Forall_forall. intros x1 Hin. inversion Hin; clarify.
          intro Heq.  setoid_rewrite Forall_app in Hlocs. clarify. inversion Hlocs2; clarify. inversion H3; clarify.
          destruct x0. destruct (eq_dec x v0); clarify.
          *contradiction H71. rewrite H0. unfold meta_loc. simpl. repeat right. omega.
          *apply plus_reg_l in H9. clarify.
         +rewrite Forall_forall. intros. inversion H; clarify.
         +rewrite Forall_forall. intros. inversion H; clarify.
        -rewrite Forall_forall. intros x1 Hin. inversion Hin; clarify.
         intros Heq. inversion Heq; clarify.  setoid_rewrite Forall_app in Hlocs. clarify. inversion Hlocs2; clarify. inversion H3; clarify.
         destruct x0. destruct (eq_dec x v0); clarify.
         +simpl. contradiction H71.  rewrite <- H0. unfold meta_loc. simpl. repeat right. omega.
         +apply plus_reg_l in H9. clarify.
        -unfold prog_op. clarify.
        -rewrite Forall_forall. intros. inversion H; clarify.
      }
      {
        rewrite Forall_forall. intros x1 Hin. rewrite Forall_forall. intros x2 Hin2.
        setoid_rewrite Forall_app in Hlocs. clarify. inversion Hlocs2; clarify. inversion H1; clarify.
        rewrite Forall_app in Ht. inversion Ht; clarify. inversion Ht2; clarify.
        inversion Hin2;rewrite in_app in Hin; clarify. 
        -inversion Hin; clarify.
         +apply in_mops_hb_check in H. destruct x1; clarify. 
          destruct x0.  destruct (eq_dec x v1); destruct (eq_dec n o); clarify. 
          *intro Heq. clarify. contradiction H31; inversion H; unfold meta_loc; clarify. 
           rewrite H0. do 3 right. left. omega.
           left. omega.
          *intro Heq. clarify. contradiction H31; inversion H; unfold meta_loc; clarify.
            rewrite H0. do 3 right. left. omega.
           left. omega.
          *apply plus_reg_l in H6. clarify.  
          *apply plus_reg_l in H6. clarify.
         +inversion H; destruct x0; destruct (eq_dec x v0); destruct (eq_dec n o);  clarify.  
          *intros Heq. clarify. contradiction H31; unfold meta_loc. left. simpl. omega.
          *intro Heq. clarify. contradiction H31; unfold meta_loc. simpl. left. omega.
          *apply plus_reg_l in H6. clarify.
          *apply plus_reg_l in H6. clarify.
          *intro Heq. clarify. contradiction H31; unfold meta_loc. simpl. do 2 right. left. omega.
          *do 3 rewrite <- app_assoc in H6. do 2 apply app_inv_head in H6. simpl in H6. clarify.
          *apply plus_reg_l in H6. clarify.
          *apply plus_reg_l in H6. clarify.
        -inversion Hin; clarify.
         +apply in_mops_hb_check in H. destruct x1; clarify. 
          destruct x0.  destruct (eq_dec x v1); destruct (eq_dec n o); clarify. 
          *intro Heq. clarify. inversion H; clarify.
           specialize(Hmetalocs_disjoint_WX H32 H32). clarify.
           specialize(Hmetalocs_disjoint_CX H3 H32). clarify.
          *intro Heq. clarify. inversion H; clarify.
           specialize(Hmetalocs_disjoint_WX H32 H32). clarify.
           specialize(Hmetalocs_disjoint_CX H3 H32). clarify.
          *apply plus_reg_l in H6. clarify.
          *apply plus_reg_l in H6. clarify.
         +inversion H; destruct x0; destruct (eq_dec x v0); destruct (eq_dec n o);  clarify.  
          *intros Heq. clarify. specialize(Hmetalocs_disjoint_CX H3 H32). clarify.
           
          *intro Heq. clarify.  specialize(Hmetalocs_disjoint_CX H3 H32). clarify.
          *apply plus_reg_l in H6. clarify.
          *apply plus_reg_l in H6. clarify.
          *intro Heq. clarify. specialize(Hmetalocs_disjoint_RX H32 H32). clarify.
          *do 3 rewrite <- app_assoc in H6. do 2 apply app_inv_head in H6. clarify.
          *apply plus_reg_l in H6. clarify.
          *apply plus_reg_l in H6. clarify.
      }  
     {
       rewrite Forall_app. do 2 rewrite Forall_forall. split; intros.
       apply in_mops_hb_check in H. destruct x1; clarify.
       inversion H; unfold prog_op; clarify.
     }
     {
       rewrite Forall_forall. intros. inversion H; clarify.
     }
    +rewrite <- app_assoc in H12. rewrite app_comm_cons in H12.
     destruct x0; clarify. rewrite <- app_assoc in H1. rewrite <- app_assoc in H1. 
     destruct (eq_dec x v0); clarify.
     *apply app_inv_head in H1. destruct zt; clarify.
     *destruct zt; clarify. apply app_inv_head in H3. inversion H3.
    +destruct zt; clarify.
    +destruct zt; clarify.
    +destruct zt; clarify.
   -(*store*)
    destruct x0 as (tx, ix); destruct ix; clarify.
    unfold instrument_instr in H12; clarify. destruct i; clarify.
    +destruct zt; clarify.
     destruct x0; clarify. rewrite <- app_assoc in H2. rewrite app_comm_cons in H2.
     do 2 rewrite <- app_assoc in H2. apply app_inv_head in H2. clarify.
    + do 4 eexists. split;[|split].
     *apply exec_store. eauto.
     *unfold mem_sim. intros. simpl. split; clarify.
      { split.
        -right.
         destruct x0; clarify. 
         do 2 rewrite split_app in H1. do 7 rewrite <- app_assoc in H1. simpl in H1.
         destruct (eq_dec x v0); destruct (eq_dec n o); clarify.
         +apply in_app. right. apply in_app. right. unfold In; clarify. 
          do 2 apply app_inv_head in H1. clarify. do 2 right. left. unfold env_sim in HGsim. Check eval_sim.
          rewrite eval_sim with(G2:=(G1 tx)). auto. 
          intros. symmetry. eapply HGsim; intros Heq; clarify.
         +do 2 apply app_inv_head in H1. clarify.
         +apply plus_reg_l in H0. clarify.
         +apply plus_reg_l in H0. clarify.
        -setoid_rewrite Forall_app in Hlocs. clarify. inversion Hlocs2; clarify. inversion H1. 
         unfold safe_instr in H3. clarify. 
      }  
      {left.
       setoid_rewrite Forall_app in Hlocs. clarify. inversion Hlocs2; clarify. inversion H3; clarify.
       rewrite Forall_app in Ht. clarify. inversion Ht2; clarify.
       destruct x0; destruct (eq_dec x v0); destruct (eq_dec n o); clarify.
       -inversion H1; clarify. 
        +contradiction H2. unfold meta_loc. simpl. repeat right. omega.
        +rewrite in_app in H. inversion H; clarify.
         *apply in_mops_hb_check in H8. destruct c; clarify. inversion H8; destruct x; clarify.
          contradiction H2. unfold meta_loc. simpl. omega.
          contradiction H2. unfold meta_loc. simpl. left.  omega.
         *inversion H8; clarify.
          contradiction H2. unfold meta_loc. simpl. left. omega.
          inversion H9; clarify. contradiction H2. unfold meta_loc. simpl. do 2 right. left. omega.
          contradiction H2. unfold meta_loc. simpl. repeat right. omega.
       -eapply hb_check_C_diff in n0. contradiction n0; eauto.  eapply zt_non_zero.
       -eapply hb_check_C_diff in n0. contradiction n0. eauto. eapply zt_non_zero.
       -eapply hb_check_C_diff in n0. contradiction n0. eauto. eapply zt_non_zero.
      }
     *simpl.
assert(Hlist_silly1: forall (X:Type) (a b c d e: X) (l1 l2 l3 l4: list X), 
               l1++a::l2++[b;c;d;e]=(l1++[a])++(l2++[b;c])++[d;e]).
       intros. simpl. do  2 rewrite app_assoc. clarify. rewrite split_app. rewrite app_assoc. do 2 rewrite split_app. repeat rewrite <- app_assoc. simpl. auto.
      rewrite Hlist_silly1 in Hcon; auto. rewrite loc_valid_ops_SC in Hcon.
      {
        inversion Hcon; clarify. 
        assert(Hacq_con: consistent (m ++ [Acq tx (X'+x)])).
         eapply consistent_app_SC. eauto.
        rewrite loc_valid_ops2_SC in Hcon2.
        -inversion Hcon2; clarify. rewrite <- app_assoc in Hcon22. rewrite loc_valid_ops_SC in Hcon22.
         +inversion Hcon22; clarify.
          destruct x0; destruct (eq_dec x v0); destruct (eq_dec n o); clarify.
          *simpl in H0. repeat rewrite <- app_assoc in H0. simpl in H0.
           eapply app_inv_head in H0. inversion H0. clarify.
          *eapply hb_check_C_diff in n0. contradiction n0; eauto. eapply zt_non_zero.
          *simpl. eapply hb_check_C_diff in n0. contradiction n0; eauto. eapply zt_non_zero.
         +rewrite Forall_forall. intros x1 Hin. inversion Hin; clarify.
          rewrite Forall_forall. intros x1 Hin. inversion Hin; clarify.
          intro Heq.  setoid_rewrite Forall_app in Hlocs. clarify. inversion Hlocs2; clarify. inversion H3; clarify.
          destruct x0. destruct (eq_dec x v0); clarify.
          *contradiction H71. rewrite H0. unfold meta_loc. simpl. repeat right. omega.
          *eapply hb_check_C_diff in n0. contradiction n0; eauto. eapply zt_non_zero.
        -rewrite Forall_forall. intros x1 Hin. inversion Hin; clarify.
         intros Heq. inversion Heq; clarify.  setoid_rewrite Forall_app in Hlocs. clarify. inversion Hlocs2; clarify. inversion H3; clarify.
         destruct x0. destruct (eq_dec x v0); clarify.
         +simpl. contradiction H71.  rewrite <- H0. unfold meta_loc. simpl. repeat right. omega.
         +eapply hb_check_C_diff in n0. contradiction n0; eauto. eapply zt_non_zero.
        
      }
      {
        rewrite Forall_forall. intros x1 Hin. rewrite Forall_forall. intros x2 Hin2.
        setoid_rewrite Forall_app in Hlocs. clarify. inversion Hlocs2; clarify. inversion H1; clarify.
        rewrite Forall_app in Ht. inversion Ht; clarify. inversion Ht2; clarify.
        inversion Hin2;rewrite in_app in Hin; clarify. 
        -inversion Hin; clarify.
         +apply in_mops_hb_check in H. destruct x1; clarify. 
          destruct x0.  destruct (eq_dec x v1); destruct (eq_dec n o); clarify. 
          *intro Heq. clarify. contradiction H31; inversion H; unfold meta_loc; clarify. 
           rewrite H0. do 3 right. left. omega.
           left. omega.
          *intro Heq. clarify. contradiction H31; inversion H; unfold meta_loc; clarify.
            rewrite H0. do 3 right. left. omega.
           left. omega.
          *eapply hb_check_C_diff in n0. contradiction n0; eauto. eapply zt_non_zero.
          *eapply hb_check_C_diff in n0. contradiction n0; eauto. eapply zt_non_zero. 
         +inversion H; destruct x0; destruct (eq_dec x v0); destruct (eq_dec n o);  clarify.  
          *intros Heq. clarify. contradiction H31; unfold meta_loc. left. simpl. omega.
          *intro Heq. clarify. contradiction H31; unfold meta_loc. simpl. left. omega.
          *eapply hb_check_C_diff in n0. contradiction n0; eauto. eapply zt_non_zero.
          *eapply hb_check_C_diff in n0. contradiction n0; eauto. eapply zt_non_zero.
          *intro Heq. clarify. contradiction H31; unfold meta_loc. simpl. do 2 right. left. omega.
          *eapply hb_check_C_diff in n0. contradiction n0; eauto. eapply zt_non_zero.
          *eapply hb_check_C_diff in n0. contradiction n0; eauto. eapply zt_non_zero.
          *eapply hb_check_C_diff in n0. contradiction n0; eauto. eapply zt_non_zero.
        -inversion Hin; clarify.
         +apply in_mops_hb_check in H. destruct x1; clarify. 
          destruct x0.  destruct (eq_dec x v1); destruct (eq_dec n o); clarify. 
          *intro Heq. clarify. inversion H; clarify.
           specialize(Hmetalocs_disjoint_WX H32 H32). clarify.
           specialize(Hmetalocs_disjoint_CX H3 H32). clarify.
          *intro Heq. clarify. inversion H; clarify.
           specialize(Hmetalocs_disjoint_WX H32 H32). clarify.
           specialize(Hmetalocs_disjoint_CX H3 H32). clarify.
          *eapply hb_check_C_diff in n0. contradiction n0; eauto. eapply zt_non_zero.
          *eapply hb_check_C_diff in n0. contradiction n0; eauto. eapply zt_non_zero. 
         +inversion H; destruct x0; destruct (eq_dec x v0); destruct (eq_dec n o);  clarify.  
          *intros Heq. clarify. specialize(Hmetalocs_disjoint_CX H3 H32). clarify.
           
          *intro Heq. clarify.  specialize(Hmetalocs_disjoint_CX H3 H32). clarify.
          *eapply hb_check_C_diff in n0. contradiction n0; eauto. eapply zt_non_zero.
          *eapply hb_check_C_diff in n0. contradiction n0; eauto. eapply zt_non_zero.
          *intro Heq. clarify. specialize(Hmetalocs_disjoint_RX H32 H32). clarify.
          *eapply hb_check_C_diff in n0. contradiction n0; eauto. eapply zt_non_zero.
          *eapply hb_check_C_diff in n0. contradiction n0; eauto. eapply zt_non_zero.
          *eapply hb_check_C_diff in n0. contradiction n0; eauto. eapply zt_non_zero.
          
      }  
     
    +rewrite <- app_assoc in H12. rewrite app_comm_cons in H12.
     destruct x0; clarify. rewrite <- app_assoc in H1. rewrite <- app_assoc in H1. 
     destruct (eq_dec x v0); clarify.
     *apply app_inv_head in H1. destruct zt; clarify.
     *destruct zt; clarify. apply app_inv_head in H3. inversion H3.
    +destruct zt; clarify.
    +destruct zt; clarify.
    +destruct zt; clarify.
    

Theorem instrument_correct : forall P h m P' G'
  (HP : exec_star (Some (init_state P)) init_env h m (Some P') G'),
  (exists h2 m2 P2' G2', exec_star
     (Some (init_state (instrument C L  P 0))) init_env h2 m2
     (Some P2') G2') <-> exists s, step_star s0 h s.
Proof.
Abort.

End Sim_Proofs.