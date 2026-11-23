-- This proof is checked against the Lean model generated directly from
-- examples/clamp.cr; it does not redefine the generated program.
-- It proves termination within 20 units of model fuel and the exact result
-- for every Crystal Int32 input. It says nothing about real process memory.
open CrystalLeanIR

theorem clamp_correct (x : Int) (hx : minimum ≤ x ∧ x ≤ maximum) :
    crystalProgram 20 x = .ok (.i32 (if x < 0 then 0 else if x > 100 then 100 else x)) := by
  have hb : (-2147483648 : Int) ≤ x ∧ x ≤ 2147483647 := by
    simpa [minimum, maximum] using hx
  by_cases hneg : x < 0
  · simp [crystalProgram, program, run, validEnv, validValue, inRange, execute,
      eval, lookup, binary, checked, minimum, maximum, hb, hneg,
      Bind.bind, Pure.pure, Except.bind, Except.pure]
  · by_cases hbig : x > 100
    · simp [crystalProgram, program, run, validEnv, validValue, inRange, execute,
        eval, lookup, binary, checked, minimum, maximum, hb, hneg, hbig,
        Bind.bind, Pure.pure, Except.bind, Except.pure]
    · simp [crystalProgram, program, run, validEnv, validValue, inRange, execute,
        eval, lookup, binary, checked, minimum, maximum, hb, hneg, hbig,
        Bind.bind, Pure.pure, Except.bind, Except.pure]
