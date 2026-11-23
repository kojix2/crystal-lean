import Lean
import CrystalLeanProof

/-!
The caller compiles CrystalLeanContract against CrystalLeanModel *before*
compiling the user's proof, then appends a `#eval` invocation of `check`.
An expected contract is a non-polymorphic definition of type Prop whose body
mentions the generated `crystalProgram` directly. The direct-reference rule is
intentionally conservative: definitions that hide that reference are rejected.
A contract that mentions the program can still express a vacuous property;
the intended specification must be reviewed independently.
-/

namespace CrystalLeanProofGate
open Lean Elab Command Meta

private def allowedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

private def belongsTo (env : Environment) (name mod : Name) : Bool :=
  (env.getModuleIdxFor? name).any fun idx => env.header.moduleNames[idx.toNat]! == mod

/-- Report the selected proposition and reject an unfinished proof. -/
def report (name : Name) : CommandElabM Unit := do
  let info ← getConstInfo name
  unless (← liftTermElabM <| isProp info.type) do
    throwError "selected declaration does not have a proposition type"
  let axioms ← collectAxioms name
  logInfo m!"{name} : {info.type}"
  if axioms.isEmpty then
    logInfo m!"'{name}' does not depend on any axioms"
  else
    logInfo m!"'{name}' depends on axioms: {axioms.toList}"
  if axioms.contains ``sorryAx then
    throwError "selected declaration depends on sorryAx"

/-- Check an independently compiled contract against a proof's declaration.
The contract definition is elaborated before the user's proof is imported.
Only kernel definitional equality is accepted; no elaborator metavariables or
custom simplification rules are involved. -/
def check (theoremName contractName : Name) : CommandElabM Unit := do
  let env ← getEnv
  unless belongsTo env `crystalProgram `CrystalLeanModel do
    throwError "generated crystalProgram is missing from CrystalLeanModel"
  unless belongsTo env contractName `CrystalLeanContract do
    throwError "contract must be defined in CrystalLeanContract: {contractName}"
  unless belongsTo env theoremName `CrystalLeanProof do
    throwError "theorem must be defined in CrystalLeanProof: {theoremName}"
  let some contractInfo := env.find? contractName
    | throwError "contract not found: {contractName}"
  let some theoremInfo := env.find? theoremName
    | throwError "theorem not found: {theoremName}"
  let .defnInfo contractDef := contractInfo
    | throwError "contract must be a definition of a proposition: {contractName}"
  unless theoremInfo.isTheorem do
    throwError "selected declaration is not a theorem: {theoremName}"
  unless contractInfo.levelParams.isEmpty && theoremInfo.levelParams.isEmpty do
    throwError "universe-polymorphic contracts and theorems are not supported"
  let expected := contractDef.value
  unless expected.getUsedConstants.contains `crystalProgram do
    throwError "contract must directly refer to the generated crystalProgram"
  unless (← liftTermElabM <| isProp expected) do
    throwError "contract definition must have a proposition as its value"
  unless (← liftTermElabM <| isProp theoremInfo.type) do
    throwError "theorem does not state a proposition"
  match Kernel.isDefEq env {} expected theoremInfo.type with
  | .ok true => pure ()
  | .ok false => throwError "theorem does not state the expected contract\nexpected: {expected}\nactual: {theoremInfo.type}"
  | .error _ => throwError "kernel could not compare contract and theorem"
  let theoremAxioms ← collectAxioms theoremName
  let contractAxioms ← collectAxioms contractName
  let axioms := (theoremAxioms.toList ++ contractAxioms.toList).eraseDups
  logInfo m!"Crystal Lean proof gate: {theoremName}\nContract: {contractName}\nStatement: {expected}\nAxioms: {axioms}"
  let extra := axioms.filter fun a => !allowedAxioms.contains a
  unless extra.isEmpty do
    throwError "theorem or contract depends on unapproved axioms: {extra}"
  logInfo "Crystal Lean proof gate: accepted"

end CrystalLeanProofGate
