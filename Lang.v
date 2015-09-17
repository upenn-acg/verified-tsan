(* Lang.v *)
(* A simple concurrent language that can be instrumented for race detection. *)
Require Import Util.
Require Import VectorClocks.
Require Import block_model.
Require Import conc_model. (* Make this lightweight? *)

Set Implicit Arguments.

(* Syntax *)
Definition var := nat.
Definition local := nat.
Definition lock := nat.
Definition tid := nat.

Inductive expr : Set :=
| N (n : nat)
| V (a : local)
| Plus (e1 e2 : expr).

Inductive instr : Set :=
| Assign (a : local) (e : expr)
| Load (a : local) (x : var)
| Store (x : var) (e : expr)
| Lock (m : lock)
| Unlock (m : lock)
| Spawn (a : local) (li : list instr)
| Wait (a : local).

Definition prog := list instr.

Section Semantics.
  Variable (tid_eq : EqDec_eq tid).

  Definition state := list (list instr).
  Definition env := tid -> local -> nat.

  Definition init_state (P : prog) := [P].
  Definition init_env (t : tid) (a : local) := 0.

  Fixpoint eval G e := match e with
  | N n => n
  | V a => G a
  | Plus e1 e2 => eval G e1 + eval G e2
  end.

  Definition operation := @operation tid var lock.

  Inductive conc_op : Type :=
  | Read (t : tid) (x : var) (v : nat)
  | Write (t : tid) (x : var) (v : nat)
  | ARW (t : tid) (x : var) (v : nat) (v' : nat).

  Definition thread_of c :=
    match c with
    | Read t _ _ => t
    | Write t _ _ => t
    | ARW t _ _ _ => t
    end.

  Definition to_seq c :=
    match c with
    | Read _ x v => [MRead (x, 0) v]
    | Write _ x v => [MWrite (x, 0) v]
    | ARW _ x v v' => [MRead (x, 0) v; MWrite (x, 0) v']
    end.

  Definition var_of c :=
    match c with
    | Read _ x _ => x
    | Write _ x _ => x
    | ARW _ x _ _ => x
    end.

  Definition synchronizes_with c1 c2 := var_of c1 = var_of c2 /\
    exists t x v v', c1 = ARW t x v v' \/ c2 = ARW t x v v'.

  Instance Base : MM_base conc_op := { thread_of := thread_of;
    to_seq := to_seq; synchronizes_with := synchronizes_with }.

  Inductive exec P G :
    option operation -> option conc_op -> state -> env -> Prop :=
  | exec_assign t a e rest
      (Hassign : nth_error P t = Some (Assign a e :: rest)) :
      exec P G None None
        (replace P t rest) (upd G t (upd (G t) a (eval (G t) e)))
  | exec_load t a x v rest
      (Hload : nth_error P t = Some (Load a x :: rest)) :
      exec P G (Some (rd t x)) (Some (Read t x v))
        (replace P t rest) (upd G t (upd (G t) a v))
  | exec_store t x e rest
      (Hstore : nth_error P t = Some (Store x e :: rest)) :
      exec P G (Some (wr t x)) (Some (Write t x (eval (G t) e)))
        (replace P t rest) G
  | exec_lock t m rest
      (Hlock : nth_error P t = Some (Lock m :: rest)) :
      exec P G (Some (acq t m)) (Some (ARW t m 0 (S t)))
        (replace P t rest) G
  | exec_unlock t m rest
      (Hlock : nth_error P t = Some (Unlock m :: rest)) :
      exec P G (Some (rel t m)) (Some (ARW t m (S t) 0))
        (replace P t rest) G
  | exec_spawn t a li rest
      (Hspawn : nth_error P t = Some (Spawn a li :: rest)) :
      exec P G (Some (fork t (length P))) None
        (replace P t rest ++ [li]) (upd G t (upd (G t) a (length P)))
  | exec_wait t a rest
      (Hwait : nth_error P t = Some (Wait a :: rest))
      (Hdone : nth_error P (G t a) = Some []) :
      exec P G (Some (join t (G t a))) None (replace P t rest) G.

  Definition opt_to_list A (x : option A) :=
    match x with
    | Some a => [a]
    | None => []
    end.

  Inductive exec_star P G :
    list operation -> list conc_op -> state -> env -> Prop :=
  | exec_refl : exec_star P G [] [] P G
  | exec_step o c P' G' (Hexec : exec P G o c P' G') lo lc P'' G''
      (Hexec' : exec_star P' G' lo lc P'' G'') :
      exec_star P G (opt_to_list o ++ lo) (opt_to_list c ++ lc) P'' G''.

  Instance var_eq : EqDec_eq var. eq_dec_inst. Qed.
  
  Context (ML : Memory_Layout nat var_eq) (MM : @Memory_Model _ _ _ _ _ _ Base).

  Definition result P lo lc := exists P' G',
    exec_star (init_state P) init_env lo lc P' G' /\
      Forall (fun li => li = []) P' /\ consistent lc.

End Semantics.
