Require Import Lang.
Require Import Util.
Set Implicit Arguments.

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

Fixpoint hb_check C1 C2 z tmp1 tmp2 :=
match z with
| 0 => []
| S n => [
    Load tmp1 (C1, n);
    Load tmp2 (C2, n);
    Assert_le (V tmp1) (V tmp2)
]++ hb_check C1 C2 n tmp1 tmp2
end.

(* Since everything is a nat, we can use C + t as the t component of C. *)
Definition load_handler t x C R (W : var) z tmp1 tmp2 := 
  hb_check W C z tmp1 tmp2 ++
  move (C + t, t) (R + x, t) tmp1.
  
Definition store_handler t x C (R:var) W z tmp1 tmp2 := 
  hb_check W C z tmp1 tmp2 ++
  hb_check R C z tmp1 tmp2 ++
  move (C + t, t) (W + x, t) tmp1.
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
 | Load a (x, 0)   => load_handler t x C R W z tmp1 tmp2 ++ [ins]
 | Store (x, 0) e  => store_handler t x C R W z tmp1 tmp2 ++ [ins]
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