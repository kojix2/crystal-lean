-- This independent contract imports exactly the generated source model.
-- The CLI compiles it separately and prints the statement with the proof.
import CrystalLeanModel

namespace BubbleSortContract

-- Crystal's Array(Int32) has Int32-valued elements and an Int32-sized length.
-- The model does not claim to cover arbitrary Lean arrays outside this domain.
def validInput (xs : Array Int) : Prop :=
  xs.size ≤ 2147483647 ∧
  ∀ value ∈ xs.toList, CrystalLeanIR.minimum ≤ value ∧ value ≤ CrystalLeanIR.maximum

-- The existential fuel is essential: exhaustion is inconclusive, not success.
-- Along with sortedness and permutation, it demands a successful normal return.
def correct : Prop :=
  ∀ xs : Array Int, validInput xs →
    ∃ fuel : Nat, ∃ ys : Array Int,
      crystalProgram fuel xs = .ok (.array ys) ∧
      ys.toList.Pairwise (· ≤ ·) ∧ ys.toList.Perm xs.toList

end BubbleSortContract
