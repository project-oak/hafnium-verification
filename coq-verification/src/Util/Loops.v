Require Import Coq.Lists.List.

Definition continue := false.
Definition break := true.
Definition while_loop
           {state : Type}
           {max_iterations : nat} (* limit # iterations to prove termination *)
           (cond : state -> bool)
           (start : state)
           (body : state -> state * bool)
  : state :=
  fst (
      fold_right
        (fun _ (before : state * bool) =>
           let '(s, loop_done) := before in
           if (loop_done || negb (cond s))%bool
           then (s, break) (* exit loop, keep old state *)
           else body s)
        (start, continue)
        (seq 0 max_iterations)).
