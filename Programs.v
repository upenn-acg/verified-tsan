Require Import Lang.
Require Import Util.
Set Implicit Arguments.
Definition x :=1.
Definition y :=2.
Definition z :=3.
Definition a :=1.
Definition b :=2.
Definition c :=3.
Definition t0 :=0.
Definition t1 :=1.
Definition t2 :=2.
Definition l1 :=1.
Definition l2 :=2.
Definition p1_t1 (l : lock) :=
[
    Lock l;
    Assign a (I 0);
    Assign a (Plus (V a) (I 1)); 
    Store (x, 0) (V a);
    
    Unlock l
].

Definition p1_t2 (l : lock):=
[
    Lock l;
    Load b (x, 0);
    Assign b (Plus (V b) (I 2));
    Store (x, 0) (V b);
    Unlock l
].

Definition p1 t1 t2:=
[
    Spawn t1 (p1_t1 l1);
    Spawn t2 (p1_t2 l1);
    Wait t1;
    Wait t2
].

(* a racy program*)

Definition p2 t1 t2:=
[
    Spawn t1 (p1_t1 l1);
    Spawn t2 (p1_t2 l2);  (* x is protected by different locks*)
    Wait t1;
    Wait t2
].

(*Definition handler (cop : conc_op):=
match cop with
| Read t x v =>  [
                     Load 0 x (* race detection code here?*)
]
| _ => []
end.*)

Definition move src tgt tmp := [Load tmp src; Store tgt (V tmp)].

Fixpoint set_vc (tgt : var (* loc of target VC *))
  (src : var (* loc of source VC *)) (z : nat (* thread bound/size of VCs *))
  (tmp : local (* a local to use as temp *)) :=
(* Move all z of the timestamps in src into tgt. *)
match z with
| O => []
| S n => move (src, n) (tgt, n) tmp ++ set_vc tgt src n tmp
end.

Definition inc_vc t tgt tmp := [
  Load tmp (tgt, t);
  Assign tmp (Plus (V tmp) (I 1));
  Store (tgt, t) (V tmp)
].

Fixpoint max_vc tgt src z tmp1 tmp2 :=
match z with
| 0 => []
| S n => [
    Load tmp1 (src,n); 
    Load tmp2 (tgt,n);
    Assign tmp2 (Max (V tmp1) (V tmp2));
    Store (tgt,n) (V tmp2)
]++ max_vc tgt src n tmp1 tmp2
end.



(* TODO: load & store handlers*)
(* Since everything is a nat, we can use C + t as the t component of C. *)
Definition load_handler t x C R (W : var) tmp := move (C + t, t) (R + x, t) tmp.
Definition store_handler t x C (R:var) W tmp := move (C + t, t) (W + x, t) tmp.
Definition lock_handler t l C L z tmp1 tmp2 :=
  max_vc (C+t) (L+l) z tmp1 tmp2.
  
Definition unlock_handler t l (C : var (* start of thread VCs *))
  (L : var (* start of lock VCs *)) z tmp1 tmp2 :=
  max_vc (L + l) (C + t) z tmp1 tmp2 ++ inc_vc t (C + t) tmp1.
Definition spawn_handler t a C z tmp :=
  set_vc (C + a) (C + t) z tmp ++ inc_vc t (C + t) tmp.
Definition wait_handler t a C z tmp1 tmp2 :=
  max_vc (C + t) (C + a) z tmp1 tmp2.
(* The instrumentation pass is provided locations to store each of the
   race detection state components. *)
Definition instrument_instr (C L R W : var) z tmp1 tmp2 (ins : instr) (t : tid)
  : prog :=
(match ins with
 | Load a (x, 0)   => load_handler t x C R W tmp1 ++ [ins]
 | Store (x, 0) e  => store_handler t x C R W tmp1 ++ [ins]
 | Lock l          =>  lock_handler t l C L z tmp1 tmp2 ++ [ins]
 | Unlock l   => unlock_handler t l C L z tmp1 tmp2 ++ [ins]
 | Spawn a li =>  spawn_handler t a C z tmp1 ++ [ins] 
 | Wait a     => [ins] ++ wait_handler t a C z tmp1 tmp2  (* the wait_handler should be called after the wait returns*)
 | _          => [ins]
end).

Fixpoint instrument C L R W z tmp1 tmp2 (p: prog) (t: tid) : prog:=
match p with
| [] => []
| ins::inss => (instrument_instr C L R W z tmp1 tmp2 ins t)++(instrument C L R W z tmp1 tmp2 inss t)
end.

Definition C_base := 16.
Definition L_base := 32.
Definition R_base := 48.
Definition W_base := 64.
Definition local_base := 0.

Definition instrumented_p1 :=instrument C_base L_base R_base W_base 3 local_base (local_base+1) (p1 1 2) t0.
Definition instrumented_p1_t1 := instrument C_base L_base R_base W_base 3 local_base (local_base+1) (p1_t1 l1) t1.
Definition instrumented_p1_t2 := instrument C_base L_base R_base W_base 3 local_base (local_base+1) (p1_t2 l1) t2.

Theorem dummy: instrumented_p1 = instrumented_p1.
Proof.
  unfold instrumented_p1,t0.
  simpl.
  
  reflexivity.
Qed.
