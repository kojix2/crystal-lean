-- Independent contract for examples/count_up.cr.
-- The chosen bound explicitly excludes outOfFuel and arithmetic overflow.
namespace CountUpContract
def correct : Prop :=
  ∀ n : Int, 0 ≤ n → n ≤ CrystalLeanIR.maximum →
    crystalProgram (n.toNat + 6) n = .ok (.i32 n)
end CountUpContract
