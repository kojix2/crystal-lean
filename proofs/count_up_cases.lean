-- Proofs about the model generated from examples/count_up.cr.
-- These establish the nonpositive branch for every valid input and one
-- concrete positive loop execution. They do not prove the general loop case.
open CrystalLeanIR

theorem count_up_nonpositive (n : Int) (h : minimum ≤ n ∧ n ≤ 0) :
    crystalProgram 20 n = .ok (.i32 0) := by
  have hn : (-2147483648 : Int) ≤ n ∧ n ≤ 2147483647 := by
    simp only [minimum] at h
    omega
  have hnot : ¬(0 : Int) < n := by omega
  simp [crystalProgram, program, run, validEnv, validValue, inRange, execute,
      eval, lookup, update, List.lookup_cons, binary, checked, minimum, maximum, hn, hnot,
      Bind.bind, Pure.pure, Except.bind, Except.pure]

theorem count_up_three : crystalProgram 20 3 = .ok (.i32 3) := by rfl
