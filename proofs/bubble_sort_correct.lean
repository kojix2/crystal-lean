import CrystalLeanModel
import CrystalLeanContract
import Std

/-!
Mathematical model of adjacent-swap bubble passes. The proof below links
these passes to the generated Crystal program.
-/
namespace BubbleMath

def carry (a : Int) : List Int → List Int × Int
  | [] => ([], a)
  | b :: bs =>
    if a ≤ b then
      let (ys, m) := carry b bs
      (a :: ys, m)
    else
      let (ys, m) := carry a bs
      (b :: ys, m)

def pass : List Int → List Int
  | [] => []
  | a :: bs => let (ys,m) := carry a bs; ys ++ [m]

theorem carry_perm (a : Int) (xs : List Int) : ((carry a xs).1 ++ [(carry a xs).2]).Perm (a :: xs) := by
  induction xs generalizing a with
  | nil => simp [carry]
  | cons b bs ih =>
    by_cases h : a ≤ b
    · simp only [carry, ite_eq_left h]
      cases hc : carry b bs with
      | mk ys m =>
        have hp := ih b
        rw [hc] at hp
        simp only [List.cons_append]
        exact List.Perm.cons a hp
    · simp only [carry, ite_eq_right h]
      cases hc : carry a bs with
      | mk ys m =>
        have hp := ih a
        rw [hc] at hp
        simp only [List.cons_append]
        exact (List.Perm.cons b hp).trans (List.Perm.swap a b bs)

theorem carry_upper (a : Int) (xs : List Int) : ∀ z ∈ a :: xs, z ≤ (carry a xs).2 := by
  induction xs generalizing a with
  | nil => simp [carry]
  | cons b bs ih =>
    by_cases h : a ≤ b
    · simp only [carry, ite_eq_left h]
      cases hc : carry b bs with
      | mk ys m =>
        have hb : ∀ z ∈ b :: bs, z ≤ m := by simpa [hc] using ih b
        intro z hz
        simp only [List.mem_cons] at hz
        rcases hz with hza | hzb | hmem
        · subst z; exact Int.le_trans h (hb b (by simp))
        · subst z; exact hb b (by simp)
        · exact hb z (by simp [hmem])
    · simp only [carry, ite_eq_right h]
      cases hc : carry a bs with
      | mk ys m =>
        have ha : ∀ z ∈ a :: bs, z ≤ m := by simpa [hc] using ih a
        intro z hz
        simp only [List.mem_cons] at hz
        rcases hz with hza | hzb | hmem
        · subst z; exact ha a (by simp)
        · subst z; exact Int.le_trans (Int.le_of_lt (Int.lt_of_not_ge h)) (ha a (by simp))
        · exact ha z (by simp [hmem])

theorem pass_perm (xs : List Int) : (pass xs).Perm xs := by
  cases xs with
  | nil => simp [pass]
  | cons a xs =>
    simp only [pass]
    cases hc : carry a xs with
    | mk ys m =>
      have hp := carry_perm a xs
      rw [hc] at hp
      exact hp

theorem pass_length (xs : List Int) : (pass xs).length = xs.length :=
  (pass_perm xs).length_eq

theorem carry_append_max (a m : Int) (xs : List Int)
    (ha : a ≤ m) (hxs : ∀ z ∈ xs, z ≤ m) :
    carry a (xs ++ [m]) = ((carry a xs).1 ++ [(carry a xs).2], m) := by
  induction xs generalizing a with
  | nil => simp [carry, ha]
  | cons b bs ih =>
    have hb : b ≤ m := hxs b (by simp)
    have hbs : ∀ z ∈ bs, z ≤ m := by intro z hz; exact hxs z (by simp [hz])
    by_cases h : a ≤ b
    · simp only [List.cons_append, carry, ite_eq_left h]
      rw [ih b hb hbs]
    · simp only [List.cons_append, carry, ite_eq_right h]
      rw [ih a ha hbs]

theorem pass_append_max (xs : List Int) (m : Int)
    (hxs : ∀ z ∈ xs, z ≤ m) : pass (xs ++ [m]) = pass xs ++ [m] := by
  cases xs with
  | nil => simp [pass, carry]
  | cons a xs =>
    have ha : a ≤ m := hxs a (by simp)
    have ht : ∀ z ∈ xs, z ≤ m := by intro z hz; exact hxs z (by simp [hz])
    simp only [List.cons_append, pass]
    rw [carry_append_max a m xs ha ht]

def passes : Nat → List Int → List Int
  | 0, xs => xs
  | n + 1, xs => passes n (pass xs)

theorem passes_perm (n : Nat) (xs : List Int) : (passes n xs).Perm xs := by
  induction n generalizing xs with
  | zero => simp [passes]
  | succ n ih => exact (ih (pass xs)).trans (pass_perm xs)

theorem passes_append_max (n : Nat) (xs : List Int) (m : Int)
    (hxs : ∀ z ∈ xs, z ≤ m) : passes n (xs ++ [m]) = passes n xs ++ [m] := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    simp only [passes, pass_append_max xs m hxs]
    apply ih
    intro z hz
    exact hxs z ((pass_perm xs).mem_iff.mp hz)

theorem passes_nil (n : Nat) : passes n [] = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [passes, pass, ih]

theorem passes_sorted (n : Nat) (xs : List Int) (h : xs.length ≤ n) :
    (passes n xs).Pairwise (· ≤ ·) := by
  induction n generalizing xs with
  | zero =>
    have e : xs = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero h)
    subst xs
    simp [passes]
  | succ n ih =>
    cases xs with
    | nil => simp [passes_nil]
    | cons a xs =>
      cases hc : carry a xs with
      | mk ys m =>
        have hperm : (ys ++ [m]).Perm (a :: xs) := by
          have h := carry_perm a xs
          rw [hc] at h
          exact h
        have hlen : ys.length ≤ n := by
          have hl := hperm.length_eq
          simp only [List.length_append, List.length_cons, List.length_nil] at hl h
          omega
        have hm : ∀ z ∈ ys, z ≤ m := by
          have up := carry_upper a xs
          rw [hc] at up
          intro z hz
          apply up z
          apply hperm.mem_iff.mp
          simp [hz]
        have hsorted := ih ys hlen
        have hm' : ∀ z ∈ passes n ys, z ≤ m := by
          intro z hz
          exact hm z ((passes_perm n ys).mem_iff.mp hz)
        have hresult : ((passes n ys) ++ [m]).Pairwise (· ≤ ·) := by
          apply List.pairwise_append.mpr
          constructor
          · exact hsorted
          constructor
          · simp
          · intro z hz v hv
            simp only [List.mem_singleton] at hv
            subst v
            exact hm' z hz
        simpa only [passes, pass, hc, passes_append_max n ys m hm] using hresult


end BubbleMath

namespace BubbleMath

theorem swap_adjacent_list (pre : List Int) (a b : Int) (tail : List Int) :
    ((pre ++ a :: b :: tail).set pre.length b).set (pre.length + 1) a = pre ++ b :: a :: tail := by
  simp [List.set_append_right]

theorem swap_adjacent_array (pre : List Int) (a b : Int) (tail : List Int) :
    (((pre ++ a :: b :: tail).toArray).swap pre.length (pre.length + 1)
      (by simp) (by simp)).toList = pre ++ b :: a :: tail := by
  simp only [Array.toList_swap]
  simp [List.set_append_right]

def arrayPass (xs : Array Int) (i : Nat) : Array Int :=
  if h : i + 1 < xs.size then
    if xs[i] > xs[i + 1] then
      arrayPass (xs.swap i (i+1) (by omega) h) (i+1)
    else
      arrayPass xs (i+1)
  else xs
termination_by xs.size - i
decreasing_by all_goals simp_wf <;> simp_all <;> omega

theorem arrayPass_carry (pre : List Int) (a : Int) (xs : List Int) :
    (arrayPass (pre ++ a :: xs).toArray pre.length).toList =
      pre ++ (carry a xs).1 ++ [(carry a xs).2] := by
  induction xs generalizing pre a with
  | nil => simp [arrayPass, carry]
  | cons b bs ih =>
    have hg : pre.length + 1 < (pre ++ a :: b :: bs).toArray.size := by simp
    have hga : pre.length < (pre ++ a :: b :: bs).toArray.size := by omega
    have ha : (pre ++ a :: b :: bs).toArray[pre.length] = a := by simp
    have hb : (pre ++ a :: b :: bs).toArray[pre.length + 1] = b := by simp
    rw [arrayPass]
    simp only [dite_eq_left hg]
    rw [ha, hb]
    by_cases h : a ≤ b
    · have hn : ¬a > b := by omega
      simp only [hn, ite_false, carry, ite_eq_left h]
      have hr := ih (pre ++ [a]) b
      simp only [List.length_append, List.length_cons, List.length_nil] at hr
      simpa [List.append_assoc] using hr
    · have hn : a > b := by omega
      simp only [hn, ite_true, carry, ite_eq_right h]
      have hswap : ((pre ++ a :: b :: bs).toArray.swap pre.length (pre.length+1) hga hg) =
          (pre ++ b :: a :: bs).toArray := by
        apply Array.toList_inj.mp
        simp
      rw [hswap]
      have hr := ih (pre ++ [b]) a
      simp only [List.length_append, List.length_cons, List.length_nil] at hr
      simpa [List.append_assoc] using hr

theorem arrayPass_list (xs : List Int) : (arrayPass xs.toArray 0).toList = pass xs := by
  cases xs with
  | nil => simp [arrayPass, pass]
  | cons a xs =>
    have h := arrayPass_carry [] a xs
    cases hc : carry a xs with
    | mk ys m => simpa [pass, hc] using h

theorem arrayPass_toList (xs : Array Int) : (arrayPass xs 0).toList = pass xs.toList := by
  have h := arrayPass_list xs.toList
  simpa using h

end BubbleMath

set_option maxRecDepth 4096
namespace BubbleSortProof
open CrystalLeanIR

def xsVar : Expr := .variable "xs"
def posVar : Expr := .variable "position"
def sizeVar : Expr := .variable "size"
def passVar : Expr := .variable "pass"
def posNext : Expr := .binary .add posVar (.intLit 1)
def innerCond : Expr := .binary .lt posNext sizeVar
def currentValue : Expr := .arrayGet xsVar posVar
def nextValue : Expr := .arrayGet xsVar posNext
def swapBranch : Stmt := .seq [
    .assign "temporary" currentValue, .arraySet "xs" posVar nextValue,
    .arraySet "xs" posNext (.variable "temporary")]
def innerBody : Stmt := .seq [
  .ifElse (.binary .gt currentValue nextValue) swapBranch (.seq []),
  .assign "position" posNext]

def SwapCorrect : Prop :=
  ∀ (n i : Nat) (env : Env) (a : Array Int) (p : Int),
  (hcap : n ≤ 2147483647) → (has : a.size = n) → (hi : i+1 < n) →
  lookup env "xs" = .ok (.array a) →
  lookup env "position" = .ok (.i32 (i : Int)) →
  lookup env "size" = .ok (.i32 (n : Int)) →
  lookup env "pass" = .ok (.i32 p) →
    ∃ (f : Nat) (out : Env), execute f swapBranch env = .ok (.next out) ∧
      lookup out "xs" = .ok (.array (a.swap i (i+1) (by omega) (by omega))) ∧
      lookup out "position" = .ok (.i32 (i : Int)) ∧
      lookup out "size" = .ok (.i32 (n : Int)) ∧
      lookup out "pass" = .ok (.i32 p)

def StepCorrect : Prop :=
  ∀ (n i : Nat) (env : Env) (a : Array Int) (p : Int),
  n ≤ 2147483647 → a.size = n → i+1 < n →
  lookup env "xs" = .ok (.array a) →
  lookup env "position" = .ok (.i32 (i : Int)) →
  lookup env "size" = .ok (.i32 (n : Int)) →
  lookup env "pass" = .ok (.i32 p) →
    ∃ (f : Nat) (out : Env) (b : Array Int), execute f innerBody env = .ok (.next out) ∧
      lookup out "xs" = .ok (.array b) ∧
      lookup out "position" = .ok (.i32 ((i+1 : Nat) : Int)) ∧
      lookup out "size" = .ok (.i32 (n : Int)) ∧
      lookup out "pass" = .ok (.i32 p) ∧ b.size = n ∧
      BubbleMath.arrayPass a i = BubbleMath.arrayPass b (i+1)

private theorem eval_binary_add (e : Env) (l r : Expr) (x y : Int)
  (hl : eval e l = .ok (.i32 x)) (hr : eval e r = .ok (.i32 y)) :
  eval e (.binary .add l r) = checked (x+y) := by
  simp only [eval, hl, hr, Bind.bind, Except.bind, binary]
private theorem eval_variable_generic (e : Env) (name : String) :
  eval e (.variable name) = lookup e name := rfl

private theorem inc_eval {env : Env} {i n : Nat}
    (hi : i+1 < n) (hcap : n ≤ 2147483647)
    (hp : lookup env "position" = .ok (.i32 (i : Int))) :
    eval env posNext = .ok (.i32 ((i+1 : Nat) : Int)) := by
  have hlo : minimum ≤ (i : Int) + 1 := by simp [minimum]; omega
  have hhi : (i : Int) + 1 ≤ maximum := by simp [maximum]; omega
  have hone : checked 1 = .ok (.i32 1) := rfl
  have hinc : checked ((i : Int) + 1) = .ok (.i32 ((i+1 : Nat) : Int)) := by
    simp [checked, inRange, hlo, hhi]
  have hp' : eval env posVar = .ok (.i32 (i : Int)) := by
    change eval env (.variable "position") = _
    rw [eval_variable_generic, hp]
  have hl' : eval env (.intLit 1) = .ok (.i32 1) := hone
  change eval env (.binary .add posVar (.intLit 1)) = _
  rw [eval_binary_add _ _ _ _ _ hp' hl', hinc]

private theorem current_eval {env : Env} {a : Array Int} {i : Nat}
    (hi : i < a.size) (ha : lookup env "xs" = .ok (.array a))
    (hp : lookup env "position" = .ok (.i32 (i : Int))) :
    eval env currentValue = .ok (.i32 a[i]) := by
  have nonneg : ¬ (i : Int) < 0 := by omega
  simp only [currentValue, xsVar, posVar, eval, ha, hp, Bind.bind, Except.bind,
    nonneg, ite_false, Int.toNat_natCast, Array.getElem?_eq_getElem hi]

private theorem next_eval {env : Env} {a : Array Int} {i n : Nat}
    (hi : i+1 < n) (has : a.size = n) (hcap : n ≤ 2147483647)
    (ha : lookup env "xs" = .ok (.array a))
    (hp : lookup env "position" = .ok (.i32 (i : Int))) :
    eval env nextValue = .ok (.i32 a[i+1]) := by
  have hidx : i+1 < a.size := by omega
  have nonneg : ¬ (((i+1 : Nat) : Int)) < 0 := by omega
  simp only [nextValue, xsVar, eval, ha, inc_eval hi hcap hp, Bind.bind, Except.bind,
    nonneg, ite_false, Int.toNat_natCast, Array.getElem?_eq_getElem hidx]

private theorem seq_cons_total {s : Stmt} {ss : List Stmt} {e e' : Env}
    {f g : Nat} {result : Flow} (hs : execute f s e = .ok (.next e'))
    (hss : execute g (.seq ss) e' = .ok result) :
    execute (max f g + 1) (.seq (s :: ss)) e = .ok result := by
  have hx := execute_mono (Nat.le_max_left f g) hs
  have hy := execute_mono (Nat.le_max_right f g) hss
  simp only [execute, hx, Bind.bind, Except.bind]
  exact hy

private theorem compare_eval {env : Env} {a : Array Int} {i n : Nat}
    (hi : i+1 < n) (has : a.size = n) (hcap : n ≤ 2147483647)
    (ha : lookup env "xs" = .ok (.array a))
    (hp : lookup env "position" = .ok (.i32 (i : Int))) :
    eval env (.binary .gt currentValue nextValue) =
      .ok (.bool (decide (a[i] > a[i+1]))) := by
  have hc := current_eval (show i < a.size by omega) ha hp
  have hn := next_eval hi has hcap ha hp
  simp [eval, hc, hn, binary, Bind.bind, Except.bind]

private theorem finish_inner {n i : Nat} {env mid : Env} {a b : Array Int} {p : Int}
    (hcap : n ≤ 2147483647) (hi : i+1 < n)
    (f : Nat) (hif : execute f (.ifElse (.binary .gt currentValue nextValue) swapBranch (.seq [])) env = .ok (.next mid))
    (hxs : lookup mid "xs" = .ok (.array b))
    (hpos : lookup mid "position" = .ok (.i32 (i : Int)))
    (hsize : lookup mid "size" = .ok (.i32 (n : Int)))
    (hpass : lookup mid "pass" = .ok (.i32 p))
    (hb : b.size = n) (hpassmath : BubbleMath.arrayPass a i = BubbleMath.arrayPass b (i+1)) :
    ∃ (fuel : Nat) (out : Env) (b : Array Int), execute fuel innerBody env = .ok (.next out) ∧
      lookup out "xs" = .ok (.array b) ∧
      lookup out "position" = .ok (.i32 ((i+1 : Nat) : Int)) ∧
      lookup out "size" = .ok (.i32 (n : Int)) ∧
      lookup out "pass" = .ok (.i32 p) ∧ b.size = n ∧
      BubbleMath.arrayPass a i = BubbleMath.arrayPass b (i+1) := by
  let out : Env := update mid "position" (.i32 ((i+1 : Nat) : Int))
  have hinc : execute 1 (.assign "position" posNext) mid = .ok (.next out) := by
    simp only [execute, inc_eval hi hcap hpos, Bind.bind, Except.bind, Pure.pure, Except.pure, out]
  have hbody := seq_cons_total hif (seq_cons_total hinc
    (show execute 1 (.seq []) out = .ok (.next out) from rfl))
  refine ⟨_, out, b, hbody, ?_, ?_, ?_, ?_, hb, hpassmath⟩
  · simpa [out] using hxs
  · rfl
  · simpa [out] using hsize
  · simpa [out] using hpass

theorem step_from_swap (swap : SwapCorrect) : StepCorrect := by
  intro n i env a p hcap has hi hxs hp hsize hpass
  have hidx : i+1 < a.size := by omega
  have hc := compare_eval hi has hcap hxs hp
  by_cases hgt : a[i] > a[i+1]
  · obtain ⟨f, mid, hswap, hm_xs, hm_pos, hm_size, hm_pass⟩ :=
      swap n i env a p hcap has hi hxs hp hsize hpass
    have hif : execute (f+1) (.ifElse (.binary .gt currentValue nextValue) swapBranch (.seq [])) env = .ok (.next mid) := by
      simpa [execute, hc, hgt, Bind.bind, Except.bind] using hswap
    have hbs : (a.swap i (i+1) (by omega) hidx).size = n := by simpa using has
    have hmath : BubbleMath.arrayPass a i = BubbleMath.arrayPass (a.swap i (i+1) (by omega) hidx) (i+1) := by
      rw [BubbleMath.arrayPass]
      simp [hidx, hgt]
    exact finish_inner hcap hi (f+1) hif hm_xs hm_pos hm_size hm_pass hbs hmath
  · have hif : execute 2 (.ifElse (.binary .gt currentValue nextValue) swapBranch (.seq [])) env = .ok (.next env) := by
      simp [execute, hc, hgt, Bind.bind, Except.bind]
    have hmath : BubbleMath.arrayPass a i = BubbleMath.arrayPass a (i+1) := by
      rw [BubbleMath.arrayPass]
      simp [hidx, hgt]
    exact finish_inner hcap hi 2 hif hxs hp hsize hpass has hmath

theorem swap_correct : SwapCorrect := by
  intro n i env a p hcap has hi hxs hp hsize hpass
  have hidx : i+1 < a.size := by omega
  have hi' : i < a.size := by omega
  let e1 : Env := update env "temporary" (.i32 a[i])
  let a1 := a.set i a[i+1] hi'
  let e2 : Env := update e1 "xs" (.array a1)
  let a2 := a1.set (i+1) a[i] (by simpa [a1] using hidx)
  let out : Env := update e2 "xs" (.array a2)
  have hpos1 : lookup e1 "position" = .ok (.i32 (i:Int)) := by simpa [e1] using hp
  have hxs1 : lookup e1 "xs" = .ok (.array a) := by simpa [e1] using hxs
  have hpos2 : lookup e2 "position" = .ok (.i32 (i:Int)) := by simpa [e2] using hpos1
  have hxs2 : lookup e2 "xs" = .ok (.array a1) := rfl
  have htemp2 : lookup e2 "temporary" = .ok (.i32 a[i]) := by simp [e2, e1]
  have ht : execute 1 (.assign "temporary" currentValue) env = .ok (.next e1) := by
    simp only [execute, current_eval hi' hxs hp, Bind.bind, Except.bind, Pure.pure, Except.pure, e1]
  have hposv1 : eval e1 posVar = .ok (.i32 (i:Int)) := by
    change eval e1 (.variable "position") = _
    rw [eval_variable_generic, hpos1]
  have hnonneg : ¬ (i : Int) < 0 := by omega
  have hnonneg2 : ¬ (((i+1 : Nat) : Int)) < 0 := by omega
  have hfirst : execute 1 (.arraySet "xs" posVar nextValue) e1 = .ok (.next e2) := by
    simp only [execute, hxs1, hposv1, next_eval hi has hcap hxs1 hpos1,
      Bind.bind, Except.bind, hnonneg, ite_false, Int.toNat_natCast, hi', Int.natCast_nonneg, true_and, dite_true,
      Pure.pure, Except.pure, e2, a1, e1]
  have hposv2 : eval e2 posNext = .ok (.i32 ((i+1 : Nat) : Int)) := inc_eval hi hcap hpos2
  have htempv2 : eval e2 (.variable "temporary") = .ok (.i32 a[i]) := by
    rw [eval_variable_generic, htemp2]
  have hsecond : execute 1 (.arraySet "xs" posNext (.variable "temporary")) e2 = .ok (.next out) := by
    have idx : i+1 < a1.size := by simpa [a1] using hidx
    simp only [execute, hxs2, hposv2, htempv2, Bind.bind, Except.bind, hnonneg2,
      ite_false, Int.toNat_natCast, idx, Int.natCast_nonneg, true_and, dite_true, Pure.pure, Except.pure, out, a2]
  have hbody := seq_cons_total ht (seq_cons_total hfirst (seq_cons_total hsecond
    (show execute 1 (.seq []) out = .ok (.next out) from rfl)))
  refine ⟨_, out, hbody, ?_, ?_, ?_, ?_⟩
  · simp [out, a2, a1, Array.swap]
  · simpa [out, e2, e1] using hp
  · simpa [out, e2, e1] using hsize
  · simpa [out, e2, e1] using hpass
end BubbleSortProof


namespace BubbleSortProof
open CrystalLeanIR

def outerCond : Expr := .binary .lt passVar sizeVar
def outerBody : Stmt := .seq [
  .assign "position" (.intLit 0), .whileLoop innerCond innerBody,
  .assign "pass" (.binary .add passVar (.intLit 1))]

def InnerCorrect : Prop :=
  ∀ (n : Nat) (env : Env) (a : Array Int) (p : Int),
  n ≤ 2147483647 → a.size = n →
  lookup env "xs" = .ok (.array a) →
  lookup env "position" = .ok (.i32 0) →
  lookup env "size" = .ok (.i32 (n : Int)) →
  lookup env "pass" = .ok (.i32 p) →
    ∃ (f : Nat) (out : Env) (b : Array Int),
      execute f (.whileLoop innerCond innerBody) env = .ok (.next out) ∧
      lookup out "xs" = .ok (.array b) ∧
      lookup out "size" = .ok (.i32 (n : Int)) ∧
      lookup out "pass" = .ok (.i32 p) ∧ b.toList = BubbleMath.pass a.toList

def outerInv (n : Nat) (target : List Int) (env : Env) : Prop :=
  ∃ (i : Nat) (a : Array Int), i ≤ n ∧ a.size = n ∧
    lookup env "pass" = .ok (.i32 (i : Int)) ∧
    lookup env "size" = .ok (.i32 (n : Int)) ∧
    lookup env "xs" = .ok (.array a) ∧
    BubbleMath.passes (n - i) a.toList = target

def remaining (n : Nat) (env : Env) : Nat :=
  match lookup env "pass" with
  | .ok (.i32 i) => n - i.toNat
  | _ => 0

private theorem outer_cond_eval {env : Env} {i n : Nat}
    (hi : lookup env "pass" = .ok (.i32 (i : Int)))
    (hn : lookup env "size" = .ok (.i32 (n : Int))) :
    eval env outerCond = .ok (.bool (decide (i < n))) := by
  simp [outerCond, passVar, sizeVar, eval, hi, hn, binary, Bind.bind, Except.bind]

theorem execute_assign (k : Nat) {e : Env} {name : String} {x : Expr} {v : Value}
    (h : eval e x = .ok v) :
    execute (k+1) (.assign name x) e = .ok (.next (update e name v)) := by
  simp only [execute, h, Bind.bind, Except.bind]
  rfl

private theorem outer_inc_eval {i n : Nat} {e : Env} (hcap : n ≤ 2147483647)
    (hil : i < n) (hbp : lookup e "pass" = .ok (.i32 (i : Int))) :
    eval e (.binary .add passVar (.intLit 1)) = .ok (.i32 ((i + 1 : Nat) : Int)) := by
  have hmin : minimum ≤ (i : Int) + 1 := by simp [minimum]; omega
  have hmax : (i : Int) + 1 ≤ maximum := by simp only [maximum]; omega
  have hp : eval e passVar = .ok (.i32 (i : Int)) := hbp
  have h1 : eval e (.intLit 1) = .ok (.i32 1) := rfl
  rw [eval_binary_add _ _ _ _ _ hp h1]
  simp [checked, inRange, hmin, hmax]

private theorem outer_step (inner : InnerCorrect) {n : Nat} {target : List Int}
    (hcap : n ≤ 2147483647) {env : Env} (hinv : outerInv n target env)
    (hcond : eval env outerCond = .ok (.bool true)) :
    ∃ f out, execute f outerBody env = .ok (.next out) ∧
      outerInv n target out ∧ remaining n out < remaining n env := by
  obtain ⟨i, a, hil, has, hip, hsz, hxs, htarget⟩ := hinv
  have hil' : i < n := by simpa [outer_cond_eval hip hsz] using hcond
  let start : Env := update env "position" (.i32 0)
  have hstart : execute 1 (.assign "position" (.intLit 0)) env = .ok (.next start) :=
    execute_assign 0 (by rfl)
  obtain ⟨f, e, b, hloop, hbx, hbs, hbp, hpass⟩ :=
    inner n start a i hcap has
      (by simpa only [start, lookup_update_other _ _ _ _ (by decide : "xs" ≠ "position")] using hxs)
      (lookup_update_same _ _ _)
      (by simpa only [start, lookup_update_other _ _ _ _ (by decide : "size" ≠ "position")] using hsz)
      (by simpa only [start, lookup_update_other _ _ _ _ (by decide : "pass" ≠ "position")] using hip)
  let final : Env := update e "pass" (.i32 ((i + 1 : Nat) : Int))
  have hlast : execute 1 (.assign "pass" (.binary .add passVar (.intLit 1))) e = .ok (.next final) :=
    execute_assign 0 (outer_inc_eval hcap hil' hbp)
  have hseq := seq_cons_total hstart (seq_cons_total hloop (seq_cons_total hlast
    (show execute 1 (.seq []) final = .ok (.next final) from rfl)))
  have hlookup : lookup final "pass" = .ok (.i32 ((i + 1 : Nat) : Int)) :=
    lookup_update_same _ _ _
  have hbsize : b.size = n := by
    have := congrArg List.length hpass
    simpa [BubbleMath.pass_length, has] using this
  refine ⟨max 1 (max f (max 1 1 + 1) + 1) + 1, final, ?_,
    ⟨i+1, b, by omega, hbsize, hlookup, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [outerBody] using hseq
  · simpa only [final, lookup_update_other _ _ _ _ (by decide : "size" ≠ "pass")] using hbs
  · simpa only [final, lookup_update_other _ _ _ _ (by decide : "xs" ≠ "pass")] using hbx
  · rw [show n - i = (n - (i + 1)) + 1 by omega] at htarget
    simpa only [BubbleMath.passes, hpass] using htarget
  · simp only [remaining, hlookup, hip, Int.toNat_natCast]
    omega

theorem run_sort_from_pass (inner : InnerCorrect) : BubbleSortContract.correct := by
  intro xs hvalid
  let n := xs.size
  let target := BubbleMath.passes n xs.toList
  have hcap : n ≤ 2147483647 := hvalid.1
  have hv : validEnv [("xs", .array xs)] = true := by
    have hall : xs.toList.all inRange = true := by
      apply List.all_eq_true.mpr
      intro x hx
      exact decide_eq_true (hvalid.2 x hx)
    simp only [validEnv, List.all_cons, List.all_nil, validValue,
      decide_eq_true (show xs.size ≤ 2147483647 from hcap), hall, Bool.and_self]
  let init : Env := [("pass", .i32 0), ("size", .i32 (n : Int)), ("xs", .array xs)]
  have hinv : outerInv n target init := by
    exact ⟨0, xs, Nat.zero_le _, rfl, rfl, rfl, rfl, by simp [target]⟩
  have hcond : ∀ env, outerInv n target env → ∃ b, eval env outerCond = .ok (.bool b) := by
    intro env inv
    obtain ⟨i, a, _, _, hip, hsz, _, _⟩ := inv
    exact ⟨_, outer_cond_eval hip hsz⟩
  obtain ⟨f, final, hloop, hfinal, hexit⟩ :=
    while_total outerCond outerBody (outerInv n target) (remaining n) hcond
      (fun _ inv hc => outer_step inner hcap inv hc) init hinv
  obtain ⟨i, ys, hil, _, hip, hsz, hxs, htarget⟩ := hfinal
  have hnlt : ¬ i < n := by simpa [outer_cond_eval hip hsz] using hexit
  have hz : n - i = 0 := by omega
  have hy : ys.toList = target := by simpa [hz, BubbleMath.passes] using htarget
  have hs : execute 1 (.assign "size" (.arraySize xsVar)) [("xs", .array xs)] =
      .ok (.next [("size", .i32 (n : Int)), ("xs", .array xs)]) := by
    have hl : minimum ≤ (n : Int) := by simp [minimum]
    have hr : (n : Int) ≤ maximum := by simp [maximum]; omega
    simp [execute, eval, xsVar, lookup, update, checked, inRange,
      show minimum ≤ (xs.size : Int) from hl, show (xs.size : Int) ≤ maximum from hr, n,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  have hzero : execute 1 (.assign "pass" (.intLit 0)) [("size", .i32 (n : Int)), ("xs", .array xs)] =
      .ok (.next init) := rfl
  have hret : execute 1 (.returnValue xsVar) final = .ok (.returned (.array ys)) := by
    simp [execute, eval, xsVar, hxs, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have hsingle : execute 2 (.seq [.returnValue xsVar]) final = .ok (.returned (.array ys)) := by
    rw [execute, hret]
    rfl
  have hex := seq_cons_total hs (seq_cons_total hzero (seq_cons_total hloop hsingle))
  refine ⟨max 1 (max 1 (max f 2 + 1) + 1) + 1, ys, ?_, ?_, ?_⟩
  · change run _ (.seq [.assign "size" (.arraySize xsVar), .assign "pass" (.intLit 0),
          .whileLoop outerCond outerBody, .returnValue xsVar]) [("xs", .array xs)] = _
    rw [run, ite_eq_left hv, hex]
    rfl
  · rw [hy]
    exact BubbleMath.passes_sorted n xs.toList (by simp [n])
  · rw [hy]
    exact BubbleMath.passes_perm n xs.toList

end BubbleSortProof


namespace BubbleSortProof
open CrystalLeanIR

private def innerInv (n : Nat) (p : Int) (target : Array Int) (env : Env) : Prop :=
  ∃ (i : Nat) (a : Array Int), (i = 0 ∨ i < n) ∧ a.size = n ∧
    lookup env "xs" = .ok (.array a) ∧
    lookup env "position" = .ok (.i32 (i : Int)) ∧
    lookup env "size" = .ok (.i32 (n : Int)) ∧
    lookup env "pass" = .ok (.i32 p) ∧
    BubbleMath.arrayPass a i = target

private def innerRemaining (n : Nat) (env : Env) : Nat :=
  match lookup env "position" with
  | .ok (.i32 i) => n - i.toNat
  | _ => 0

private theorem eval_lt (env : Env) (l r : Expr) (x y : Int)
    (hl : eval env l = .ok (.i32 x)) (hr : eval env r = .ok (.i32 y)) :
    eval env (.binary .lt l r) = .ok (.bool (decide (x < y))) := by
  simp only [eval, hl, hr, Bind.bind, Except.bind, binary]

private theorem inner_cond_eval {env : Env} {i n : Nat} (hcap : n ≤ 2147483647)
    (hibit : i = 0 ∨ i < n)
    (hp : lookup env "position" = .ok (.i32 (i : Int)))
    (hs : lookup env "size" = .ok (.i32 (n : Int))) :
    eval env innerCond = .ok (.bool (decide (i + 1 < n))) := by
  have hc : checked ((i : Int) + 1) = .ok (.i32 ((i + 1 : Nat) : Int)) := by
    have hlo : minimum ≤ (i : Int) + 1 := by simp [minimum]; omega
    have hhi : (i : Int) + 1 ≤ maximum := by
      unfold maximum
      rcases hibit with h | h <;> omega
    simp [checked, inRange, hlo, hhi]
  have hone : eval env (.intLit 1) = .ok (.i32 1) := rfl
  have hpos : eval env posVar = .ok (.i32 (i : Int)) := hp
  have hsize : eval env sizeVar = .ok (.i32 (n : Int)) := hs
  have hadd : eval env posNext = .ok (.i32 ((i+1 : Nat) : Int)) :=
    (eval_binary_add _ _ _ _ _ hpos hone).trans hc
  change eval env (.binary .lt posNext sizeVar) = _
  rw [eval_lt _ _ _ _ _ hadd hsize]
  simp <;> omega

theorem innerFromStep (step : StepCorrect) : InnerCorrect := by
  intro n env a p hcap ha hxs hpos hsize hpass
  let target := BubbleMath.arrayPass a 0
  have hi : innerInv n p target env := ⟨0, a, Or.inl rfl, ha, hxs, hpos, hsize, hpass, rfl⟩
  have hcond : ∀ e, innerInv n p target e → ∃ b, eval e innerCond = .ok (.bool b) := by
    intro e he
    obtain ⟨i, arr, hb, _, _, hp, hs, _, _⟩ := he
    exact ⟨_, inner_cond_eval hcap hb hp hs⟩
  have hstep : ∀ e, innerInv n p target e → eval e innerCond = .ok (.bool true) →
      ∃ f e', execute f innerBody e = .ok (.next e') ∧
        innerInv n p target e' ∧ innerRemaining n e' < innerRemaining n e := by
    intro e he hgo
    obtain ⟨i, arr, hb, hlen, hx, hp, hs, hpa, ht⟩ := he
    have hgo' : i + 1 < n := by simpa [inner_cond_eval hcap hb hp hs] using hgo
    obtain ⟨f, e', b, hex, hxb, hpb, hsb, hpas, hbs, hmod⟩ :=
      step n i e arr p hcap hlen hgo' hx hp hs hpa
    refine ⟨f, e', hex, ⟨i+1, b, Or.inr hgo', hbs, hxb, hpb, hsb, hpas, hmod.symm.trans ht⟩, ?_⟩
    simp only [innerRemaining, hpb, hp, Int.toNat_natCast]
    omega
  obtain ⟨f, final, hloop, hf, hexit⟩ :=
    while_total innerCond innerBody (innerInv n p target) (innerRemaining n) hcond hstep env hi
  obtain ⟨i, b, hb, hbs, hxb, hpb, hsb, hpas, hmod⟩ := hf
  have hdone : ¬i + 1 < n := by simpa [inner_cond_eval hcap hb hpb hsb] using hexit
  have hpass_done : BubbleMath.arrayPass b i = b := by
    rw [BubbleMath.arrayPass]
    simp [hbs, hdone]
  have hb_target : b = target := hpass_done.symm.trans hmod
  exact ⟨f, final, b, hloop, hxb, hsb, hpas,
    (congrArg Array.toList hb_target).trans (BubbleMath.arrayPass_toList a)⟩

end BubbleSortProof

-- The theorem states the independently compiled contract for the generated model.
theorem bubble_sort_correct : BubbleSortContract.correct :=
  BubbleSortProof.run_sort_from_pass
    (BubbleSortProof.innerFromStep (BubbleSortProof.step_from_swap BubbleSortProof.swap_correct))
