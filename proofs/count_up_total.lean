-- Proof of the generated count_up function over all nonnegative Int32 inputs.
-- count_up_total provides a concrete sufficient fuel bound, while
-- count_up_while_total applies the generic invariant/termination rule.
-- Crystal-to-IR semantics remains a separately unproved assumption.
open CrystalLeanIR

def countCond : Expr := .binary .lt (.variable "i") (.variable "n")
def countBody : Stmt := .seq [.assign "i" (.binary .add (.variable "i") (.intLit 1))]

theorem count_loop (k : Nat) (i n : Int) (env : Env)
    (hi : 0 ≤ i) (hn : n ≤ maximum) (hk : n = i + Int.ofNat k)
    (ilook : lookup env "i" = .ok (.i32 i))
    (nlook : lookup env "n" = .ok (.i32 n)) :
    ∃ final, execute (k+4) (.whileLoop countCond countBody) env = .ok (.next final) ∧
      lookup final "i" = .ok (.i32 n) ∧ lookup final "n" = .ok (.i32 n) := by
  induction k generalizing i env with
  | zero =>
    change n = i + (0 : Int) at hk
    have eqi : i = n := by omega
    have hc : eval env countCond = .ok (.bool false) := by
      simp [countCond, eval, ilook, nlook, binary, eqi, Bind.bind, Except.bind]
    refine ⟨env, ?_, ?_, nlook⟩
    · simp [execute, hc, Bind.bind, Except.bind, Pure.pure, Except.pure]
    · simpa [eqi] using ilook
  | succ k ih =>
    simp only [Int.ofNat_eq_natCast, Int.natCast_succ] at hk
    have hlt : i < n := by omega
    have ilim : i + 1 ≤ maximum := by omega
    have ilower : minimum ≤ i+1 := by simp [minimum]; omega
    have hchecked : checked (i + 1) = .ok (.i32 (i + 1)) := by
      simp [checked, inRange, ilower, ilim]
    have hc : eval env countCond = .ok (.bool true) := by
      simp [countCond, eval, ilook, nlook, binary, hlt, Bind.bind, Except.bind]
    have new_i : lookup (update env "i" (.i32 (i+1))) "i" = .ok (.i32 (i+1)) := by
      simp
    have new_n : lookup (update env "i" (.i32 (i+1))) "n" = .ok (.i32 n) := by
      simpa using nlook
    have hnext : 0 ≤ i + 1 := by omega
    have hremain : n = (i + 1) + Int.ofNat k := by
      change n = (i + 1) + (k : Int)
      omega
    obtain ⟨final, hf, hfi, hfn⟩ := ih (i+1) (update env "i" (.i32 (i+1))) hnext hremain new_i new_n
    have hone : checked 1 = .ok (.i32 1) := by rfl
    have hb : execute (k+4) countBody env = .ok (.next (update env "i" (.i32 (i+1)))) := by
      simp [countBody, execute, eval, ilook, binary, hchecked, hone,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
    refine ⟨final, ?_, hfi, hfn⟩
    change execute (Nat.succ (k+4)) (.whileLoop countCond countBody) env = _
    rw [execute]
    simp only [hc, hb]
    exact hf

theorem count_up_total (n : Int) (hnonneg : 0 ≤ n) (hmax : n ≤ maximum) :
    crystalProgram (n.toNat + 6) n = .ok (.i32 n) := by
  have hnat : n = Int.ofNat n.toNat := by
    exact (Int.toNat_of_nonneg hnonneg).symm
  have hlo : minimum ≤ n := by simp [minimum]; omega
  have hvalid : inRange n = true := by simp [inRange, hlo, hmax]
  have hbound : n = (0 : Int) + Int.ofNat n.toNat := by simpa using hnat
  have hi : lookup [("i", .i32 0), ("n", .i32 n)] "i" = .ok (.i32 0) := by rfl
  have hnl : lookup [("i", .i32 0), ("n", .i32 n)] "n" = .ok (.i32 n) := by rfl
  obtain ⟨final, hloop, hfi, hfn⟩ := count_loop n.toNat 0 n _ (by omega) hmax hbound hi hnl
  simp only [crystalProgram, program, run, validEnv, validValue, List.all_cons,
    List.all_nil, Bool.and_true, hvalid, ite_true]
  have hfirst : execute (n.toNat + 5) (.assign "i" (.intLit 0)) [("n", .i32 n)] =
      .ok (.next [("i", .i32 0), ("n", .i32 n)]) := by
    simp [execute, eval, update, checked, inRange, minimum, maximum, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have hreturn : execute (n.toNat + 3) (.returnValue (.variable "i")) final = .ok (.returned (.i32 n)) := by
    simp [execute, eval, hfi, Bind.bind, Except.bind, Pure.pure, Except.pure]
  change (do
    let flow ← execute (Nat.succ (n.toNat+5)) (.seq [.assign "i" (.intLit 0), .whileLoop countCond countBody, .returnValue (.variable "i")]) [("n", .i32 n)]
    match flow with
    | .returned value => pure value
    | .next _ => .error .missingReturn) = .ok (.i32 n)
  rw [execute]
  simp only [hfirst, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [execute]
  simp only [hloop, Bind.bind, Except.bind]
  rw [execute]
  simp only [hreturn, Bind.bind, Except.bind, Pure.pure, Except.pure]


#print axioms count_up_total

def CountInv (n : Int) (env : Env) : Prop :=
  ∃ i, 0 ≤ i ∧ i ≤ n ∧ lookup env "i" = .ok (.i32 i) ∧ lookup env "n" = .ok (.i32 n)

def CountMeasure (n : Int) (env : Env) : Nat :=
  match lookup env "i" with
  | .ok (.i32 i) => (n-i).toNat
  | _ => 0

theorem count_up_while_total (n : Int) (hnonneg : 0 ≤ n) (hmax : n ≤ maximum) :
    ∃ fuel final,
      execute fuel (.whileLoop countCond countBody) [("i", .i32 0), ("n", .i32 n)] = .ok (.next final) ∧
      lookup final "i" = .ok (.i32 n) := by
  have hcond : ∀ env, CountInv n env → ∃ b, eval env countCond = .ok (.bool b) := by
    intro env ⟨i, hi, hle, ilook, nlook⟩
    by_cases hlt : i < n
    · refine ⟨true, ?_⟩
      simp [countCond, eval, ilook, nlook, binary, hlt, Bind.bind, Except.bind]
    · refine ⟨false, ?_⟩
      simp [countCond, eval, ilook, nlook, binary, hlt, Bind.bind, Except.bind]
  have hstep : ∀ env, CountInv n env → eval env countCond = .ok (.bool true) →
      ∃ fuel next, execute fuel countBody env = .ok (.next next) ∧
        CountInv n next ∧ CountMeasure n next < CountMeasure n env := by
    intro env ⟨i, hi, hle, ilook, nlook⟩ hc
    have hlt : i < n := by
      by_cases hlt : i < n
      · exact hlt
      · simp [countCond, eval, ilook, nlook, binary, hlt, Bind.bind, Except.bind] at hc
    have ilim : i+1 ≤ maximum := by omega
    have ilower : minimum ≤ i+1 := by simp [minimum]; omega
    have hchecked : checked (i+1) = .ok (.i32 (i+1)) := by simp [checked, inRange, ilower, ilim]
    have hone : checked 1 = .ok (.i32 1) := by rfl
    let next : Env := update env "i" (.i32 (i+1))
    have hb : execute 3 countBody env = .ok (.next next) := by
      simp [next, countBody, execute, eval, ilook, binary, hchecked, hone,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
    have next_i : lookup next "i" = .ok (.i32 (i+1)) := by simp [next]
    have next_n : lookup next "n" = .ok (.i32 n) := by simpa [next] using nlook
    have hinv : CountInv n next := by
      refine ⟨i+1, by omega, by omega, next_i, next_n⟩
    have hless : CountMeasure n next < CountMeasure n env := by
      simp only [CountMeasure, next_i, ilook]
      omega
    exact ⟨3, next, hb, hinv, hless⟩
  let initial : Env := [("i", .i32 0), ("n", .i32 n)]
  have hinv : CountInv n initial := by
    refine ⟨0, by omega, ?_, ?_, ?_⟩
    · exact hnonneg
    · rfl
    · rfl
  obtain ⟨fuel, final, hexec, hfinv, hexit⟩ :=
    while_total countCond countBody (CountInv n) (CountMeasure n) hcond hstep initial hinv
  obtain ⟨i, hi, hle, ilook, nlook⟩ := hfinv
  have hnot : ¬ i < n := by
    intro hlt
    have htrue : eval final countCond = .ok (.bool true) := by
      simp [countCond, eval, ilook, nlook, binary, hlt, Bind.bind, Except.bind]
    rw [htrue] at hexit
    cases hexit
  have heq : i = n := by omega
  exact ⟨fuel, final, hexec, by simpa [heq] using ilook⟩
#print axioms count_up_while_total
