import Std

/-!
A fuel-indexed operational model for a restricted first-order Crystal subset.
Array updates are modeled by replacing the value bound to a variable; this
requires the frontend to reject array aliases and multiple array arguments in
mutating programs. Observable mutation through a caller's reference is not
represented by the returned value. `outOfFuel` is an inconclusive analysis result, not a Crystal exception
or a successful return. Crystal runtime resource exhaustion is not modeled.
The correspondence of these rules to the Crystal compiler/stdlib is a trusted
assumption until proved separately.
-/
namespace CrystalLeanIR

inductive Error where
  | overflow | divisionByZero | argumentError | indexOutOfBounds | unboundVariable
  | typeMismatch | invalidInput | outOfFuel | missingReturn
  deriving Repr, DecidableEq

inductive Value where
  | i32 (n : Int)
  | bool (b : Bool)
  | array (xs : Array Int)
  deriving Repr, DecidableEq

abbrev Env := List (String × Value)

def minimum : Int := -2147483648
def maximum : Int := 2147483647

def inRange (n : Int) : Bool := decide (minimum ≤ n ∧ n ≤ maximum)

def validValue : Value → Bool
  | .i32 n => inRange n
  | .bool _ => true
  | .array xs => decide (xs.size ≤ 2147483647) && xs.toList.all inRange

def validEnv (env : Env) : Bool := env.all fun entry => validValue entry.2

def checked (n : Int) : Except Error Value :=
  if inRange n then .ok (.i32 n) else .error .overflow

inductive BinaryOp where
  | add | sub | mul | floorDiv | mod | eq | ne | lt | le | gt | ge
  deriving Repr, DecidableEq

inductive UnaryOp where
  | neg | not
  deriving Repr, DecidableEq

inductive Expr where
  | intLit (n : Int)
  | boolLit (b : Bool)
  | variable (name : String)
  | binary (op : BinaryOp) (left right : Expr)
  | unary (op : UnaryOp) (value : Expr)
  | arrayGet (array index : Expr)
  | arraySize (array : Expr)
  deriving Repr, DecidableEq

inductive Stmt where
  | assign (name : String) (value : Expr)
  | arraySet (name : String) (index value : Expr)
  | expr (value : Expr)
  | returnValue (value : Expr)
  | ifElse (condition : Expr) (thenBranch elseBranch : Stmt)
  | whileLoop (condition : Expr) (body : Stmt)
  | seq (statements : List Stmt)
  deriving Repr

inductive Flow where
  | next (env : Env)
  | returned (value : Value)
  deriving Repr, DecidableEq

def lookup (env : Env) (name : String) : Except Error Value :=
  match env.lookup name with
  | some value => .ok value
  | none => .error .unboundVariable

/-- Replace the binding and discard the old value, including old array snapshots. -/
def update (env : Env) (name : String) (value : Value) : Env :=
  (name, value) :: env.filter (fun entry => entry.1 != name)

@[simp] theorem lookup_update_same (env : Env) (name : String) (value : Value) :
    lookup (update env name value) name = .ok value := by
  simp [lookup, update]

@[simp] theorem lookup_update_other (env : Env) (name key : String) (value : Value)
    (h : name ≠ key) : lookup (update env key value) name = lookup env name := by
  have hne : (name == key) = false := by simpa using h
  simp only [lookup, update, List.lookup_cons, hne]
  suffices (env.filter (fun entry => entry.1 != key)).lookup name = env.lookup name by rw [this]
  induction env with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨entryKey, entryValue⟩ := entry
    by_cases he : entryKey = key
    · subst entryKey
      simpa [List.lookup_cons, hne] using ih
    · simp [List.lookup_cons, he, ih]

def binary (op : BinaryOp) (left right : Value) : Except Error Value :=
  match op, left, right with
  | .add, .i32 a, .i32 b => checked (a + b)
  | .sub, .i32 a, .i32 b => checked (a - b)
  | .mul, .i32 a, .i32 b => checked (a * b)
  | .floorDiv, .i32 a, .i32 b =>
      if b = 0 then .error .divisionByZero
      else if a = minimum ∧ b = -1 then .error .argumentError
      else checked (a.fdiv b)
  | .mod, .i32 a, .i32 b =>
      if b = 0 then .error .divisionByZero
      else checked (a.fmod b)
  | .eq, .i32 a, .i32 b => .ok (.bool (a == b))
  | .ne, .i32 a, .i32 b => .ok (.bool (a != b))
  | .lt, .i32 a, .i32 b => .ok (.bool (decide (a < b)))
  | .le, .i32 a, .i32 b => .ok (.bool (decide (a ≤ b)))
  | .gt, .i32 a, .i32 b => .ok (.bool (decide (a > b)))
  | .ge, .i32 a, .i32 b => .ok (.bool (decide (a ≥ b)))
  | .eq, .bool a, .bool b => .ok (.bool (a == b))
  | .ne, .bool a, .bool b => .ok (.bool (a != b))
  | _, _, _ => .error .typeMismatch

def unary (op : UnaryOp) (value : Value) : Except Error Value :=
  match op, value with
  | .neg, .i32 n => checked (-n)
  | .not, .bool b => .ok (.bool (!b))
  | _, _ => .error .typeMismatch

-- Evaluation order matches the accepted Crystal subset: receiver/left first,
-- then index/right; errors stop evaluation before subsequent expressions.
def eval (env : Env) : Expr → Except Error Value
  | .intLit n => checked n
  | .boolLit b => .ok (.bool b)
  | .variable name => lookup env name
  | .binary op left right => do
      let x ← eval env left
      let y ← eval env right
      binary op x y
  | .unary op arg => do
      let x ← eval env arg
      unary op x
  | .arraySize array => do
      match ← eval env array with
      | .array xs => checked (Int.ofNat xs.size)
      | _ => .error .typeMismatch
  | .arrayGet array index => do
      let xs ← eval env array
      let i ← eval env index
      match xs, i with
      | .array values, .i32 n =>
        -- Crystal Array#[] accepts negative indices, counted from the end.
        let idx := if n < 0 then Int.ofNat values.size + n else n
        if idx < 0 then .error .indexOutOfBounds
        else match values[idx.toNat]? with
             | some value => .ok (.i32 value)
             | none => .error .indexOutOfBounds
      | _, _ => .error .typeMismatch

def execute : Nat → Stmt → Env → Except Error Flow
  | 0, _, _ => .error .outOfFuel
  | _fuel + 1, .assign name value, env => do
      let result ← eval env value
      pure (.next (update env name result))
  | _fuel + 1, .arraySet name index value, env => do
      let receiver ← lookup env name
      let indexValue ← eval env index
      let newValue ← eval env value
      match receiver, indexValue, newValue with
      | .array values, .i32 i, .i32 n =>
        let idx := if i < 0 then Int.ofNat values.size + i else i
        if h : 0 ≤ idx ∧ idx.toNat < values.size then
          pure (.next (update env name (.array (values.set idx.toNat n h.2))))
        else .error .indexOutOfBounds
      | _, _, _ => .error .typeMismatch
  | _fuel + 1, .expr value, env => do
      let _ ← eval env value
      pure (.next env)
  | _fuel + 1, .returnValue value, env => do
      let result ← eval env value
      pure (.returned result)
  | fuel + 1, .ifElse condition thenBranch elseBranch, env => do
      match ← eval env condition with
      | .bool true => execute fuel thenBranch env
      | .bool false => execute fuel elseBranch env
      | _ => .error .typeMismatch
  | fuel + 1, .whileLoop condition body, env => do
      match ← eval env condition with
      | .bool false => pure (.next env)
      | .bool true =>
        match ← execute fuel body env with
        | .returned value => pure (.returned value)
        | .next nextEnv => execute fuel (.whileLoop condition body) nextEnv
      | _ => .error .typeMismatch
  | _fuel + 1, .seq [], env => .ok (.next env)
  | fuel + 1, .seq (first :: rest), env => do
      match ← execute fuel first env with
      | .returned value => pure (.returned value)
      | .next nextEnv => execute fuel (.seq rest) nextEnv

def run (fuel : Nat) (body : Stmt) (env : Env) : Except Error Value :=
  if validEnv env then do
    match ← execute fuel body env with
    | .returned value => pure value
    | .next _ => .error .missingReturn
  else .error .invalidInput

theorem execute_succ_of_ok (fuel : Nat) (stmt : Stmt) (env : Env) (result : Flow)
    (h : execute fuel stmt env = .ok result) : execute (fuel + 1) stmt env = .ok result := by
  induction fuel generalizing stmt env result with
  | zero => simp [execute] at h
  | succ n ih =>
    cases stmt with
    | assign name value => simpa [execute] using h
    | arraySet name index value => simpa [execute] using h
    | expr value => simpa [execute] using h
    | returnValue value => simpa [execute] using h
    | ifElse condition t e =>
      cases hc : eval env condition with
      | error e => simp [execute, hc, Bind.bind, Except.bind] at h
      | ok v =>
        cases v with
        | i32 n => simp [execute, hc, Bind.bind, Except.bind] at h
        | array xs => simp [execute, hc, Bind.bind, Except.bind] at h
        | bool b =>
          cases b <;> simp only [execute, hc, Bind.bind, Except.bind] at h ⊢ <;> exact ih _ _ _ h
    | whileLoop condition body =>
      cases hc : eval env condition with
      | error e => simp [execute, hc, Bind.bind, Except.bind] at h
      | ok v =>
        cases v with
        | i32 x => simp [execute, hc, Bind.bind, Except.bind] at h
        | array xs => simp [execute, hc, Bind.bind, Except.bind] at h
        | bool b =>
          cases b with
          | false => simpa [execute, hc, Bind.bind, Except.bind] using h
          | true =>
            cases hb : execute n body env with
            | error e => simp [execute, hc, hb, Bind.bind, Except.bind] at h
            | ok f =>
              have hb' := ih body env f hb
              cases f with
              | returned v => simpa [execute, hc, hb, hb', Bind.bind, Except.bind] using h
              | next e =>
                have h' : execute n (.whileLoop condition body) e = .ok result := by
                  simpa [execute, hc, hb, Bind.bind, Except.bind] using h
                have hk := ih (.whileLoop condition body) e result h'
                simpa [execute, hc, hb', Bind.bind, Except.bind] using hk
    | seq stmts =>
      cases stmts with
      | nil => simpa [execute] using h
      | cons first rest =>
        cases hb : execute n first env with
        | error e => simp [execute, hb, Bind.bind, Except.bind] at h
        | ok f =>
          have hb' := ih first env f hb
          cases f with
          | returned v => simpa [execute, hb, hb', Bind.bind, Except.bind] using h
          | next e =>
            have h' : execute n (.seq rest) e = .ok result := by
              simpa [execute, hb, Bind.bind, Except.bind] using h
            have hk := ih (.seq rest) e result h'
            simpa [execute, hb', Bind.bind, Except.bind] using hk

/-- Successful executions remain successful with any greater fuel budget. -/
theorem execute_mono {fuel more : Nat} (hle : fuel ≤ more) {stmt : Stmt} {env : Env}
    {result : Flow} (h : execute fuel stmt env = .ok result) :
    execute more stmt env = .ok result := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  clear hle
  induction d with
  | zero => simpa using h
  | succ d ih => simpa only [Nat.add_succ] using execute_succ_of_ok (fuel + d) stmt env result ih

/-- Invariants are preserved by every normally terminating loop execution. -/
theorem while_invariant (condition : Expr) (body : Stmt) (Inv : Env → Prop)
    (hstep : ∀ fuel env next, Inv env → eval env condition = .ok (.bool true) →
      execute fuel body env = .ok (.next next) → Inv next)
    (fuel : Nat) (env final : Env) (hinv : Inv env)
    (h : execute fuel (.whileLoop condition body) env = .ok (.next final)) :
    Inv final ∧ eval final condition = .ok (.bool false) := by
  induction fuel generalizing env with
  | zero => simp [execute] at h
  | succ fuel ih =>
    cases hc : eval env condition with
    | error e => simp [execute, hc, Bind.bind, Except.bind] at h
    | ok v =>
      cases v with
      | i32 n => simp [execute, hc, Bind.bind, Except.bind] at h
      | array xs => simp [execute, hc, Bind.bind, Except.bind] at h
      | bool b =>
        cases b with
        | false =>
          simp [execute, hc, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
          subst final
          exact ⟨hinv, hc⟩
        | true =>
          cases hb : execute fuel body env with
          | error e => simp [execute, hc, hb, Bind.bind, Except.bind] at h
          | ok result =>
            cases result with
            | returned v => simp [execute, hc, hb, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
            | next nextEnv =>
              have next : execute fuel (.whileLoop condition body) nextEnv = .ok (.next final) := by
                simpa [execute, hc, hb, Bind.bind, Except.bind] using h
              exact ih nextEnv (hstep fuel env nextEnv hinv hc hb) next

/-- If every iteration succeeds, preserves the invariant and decreases a
natural-number measure, the loop terminates normally for some finite fuel.
The hypotheses also rule out errors and early returns inside the body. -/
theorem while_total (condition : Expr) (body : Stmt) (Inv : Env → Prop) (measure : Env → Nat)
    (hcond : ∀ env, Inv env → ∃ b, eval env condition = .ok (.bool b))
    (hstep : ∀ env, Inv env → eval env condition = .ok (.bool true) →
      ∃ fuel next, execute fuel body env = .ok (.next next) ∧ Inv next ∧ measure next < measure env)
    (env : Env) (hinv : Inv env) :
    ∃ fuel final, execute fuel (.whileLoop condition body) env = .ok (.next final) ∧
      Inv final ∧ eval final condition = .ok (.bool false) := by
  have go : ∀ n env, measure env = n → Inv env →
      ∃ fuel final, execute fuel (.whileLoop condition body) env = .ok (.next final) ∧
        Inv final ∧ eval final condition = .ok (.bool false) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro env he hinv
      obtain ⟨b, hb⟩ := hcond env hinv
      cases b with
      | false =>
        refine ⟨1, env, ?_, hinv, hb⟩
        simp [execute, hb, Bind.bind, Except.bind, Pure.pure, Except.pure]
      | true =>
        obtain ⟨f, next, hbody, hnext, hless⟩ := hstep env hinv hb
        obtain ⟨g, final, hloop, hfinal, hexit⟩ :=
          ih (measure next) (by omega) next rfl hnext
        let budget := max f g
        have hbody' : execute budget body env = .ok (.next next) :=
          execute_mono (Nat.le_max_left _ _) hbody
        have hloop' : execute budget (.whileLoop condition body) next = .ok (.next final) :=
          execute_mono (Nat.le_max_right _ _) hloop
        refine ⟨budget + 1, final, ?_, hfinal, hexit⟩
        simpa [execute, hb, hbody', Bind.bind, Except.bind] using hloop'
  exact go (measure env) env rfl hinv

end CrystalLeanIR
