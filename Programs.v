Require Import Lang.
Require Import Util.
Set Implicit Arguments.
Definition x :=1.
Definition y :=2.
Definition z :=3.
Definition a :=1.
Definition b :=2.
Definition c :=3.
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

Definition p1 :=
[
    Spawn t1 (p1_t1 l1);
    Spawn t2 (p1_t2 l1);
    Wait(t1);
    Wait(t2)
].

(* a racy program*)

Definition p2 :=
[
    Spawn t1 (p1_t1 l1);
    Spawn t2 (p1_t2 l2);  (* x is protected by different locks*)
    Wait(t1);
    Wait(t2)
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

(* Since everything is a nat, we can use C + t as the t component of C. *)
Definition load_handler t x C R tmp := move (C + t, t) (R + x, t) tmp.

Definition unlock_handler t l (C : var (* start of thread VCs *))
  (L : var (* start of lock VCs *)) z tmp :=
  set_vc (L + l) (C + t) z tmp ++ inc_vc t (C + t) tmp.

(* The instrumentation pass is provided locations to store each of the
   race detection state components. *)
Definition instrument_instr (C L R W : var) z tmp (ins : instr) (t : tid)
  : prog :=
(match ins with
 | Load a (x, 0)   => load_handler t x C R tmp
 (* | ... *)
 | Unlock l   => unlock_handler t l C L z tmp
 | _          => []
end) ++ [ins].

Fixpoint instrument C L R W z tmp (p: prog) (t: tid) : prog:=
match p with
| [] => []
| ins::inss => (instrument_instr C L R W z tmp ins t)++(instrument C L R W z tmp inss t)
end.