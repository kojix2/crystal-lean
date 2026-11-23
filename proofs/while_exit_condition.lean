-- A reusable lemma for the generic operational model. This does not
-- assert that a loop terminates or completes without an error.
open CrystalLeanIR

-- A generic property of all normally terminating while loops: they cannot
-- fall through unless their condition evaluates to false in the final state.
theorem while_exit_condition (fuel : Nat) (condition : Expr) (body : Stmt)
    (env final : Env) (h : execute fuel (.whileLoop condition body) env = .ok (.next final)) :
    eval final condition = .ok (.bool false) :=
  (while_invariant condition body (fun _ => True) (by intros; trivial)
    fuel env final trivial h).2
