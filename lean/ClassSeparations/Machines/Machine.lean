import ClassSeparations.Basic.Tree

/-!
# Machines over the reals (Blum–Shub–Smale model)

We use real random-access machines: a finite program acting on real registers `R k` and index
registers `I k` (`k : ℕ`); real registers are addressed through index registers.  Each
arithmetic operation and each comparison costs one step; moves of data and operations on index
registers also cost one step.  This model and the BSS machines of [BSS89, BCSS98] simulate
each other with polynomial overhead, so they define the same polynomial-time classes.

An input of a machine consists of a list of block sizes, stored in the index registers
`I 0, I 1, …`, and the concatenated blocks, stored in `R 0, R 1, …`.  All other registers are
`0`.  Outcomes are `Option Bool` as for trees: `some b` = halted with answer `b`, `none` =
division by zero (rejection).

**Unrolling** (§2.1): for inputs of a fixed size, a machine that runs in time `T` unrolls into
a tree of depth `≤ T + 1` whose constants are those of the machine.
-/

noncomputable section

open Classical

namespace ClassSep

/-- Instructions of a real random-access machine. -/
inductive MInstr where
  /-- `R[I d] := R[I a] op R[I b]` -/
  | arith (op : TOp) (d a b : ℕ)
  /-- `R[I d] := c` -/
  | const (d : ℕ) (c : ℝ)
  /-- `R[I d] := R[I a]` -/
  | copy (d a : ℕ)
  /-- if `R[I a] ≥ 0` then go to `target` -/
  | jumpGe (a target : ℕ)
  /-- if `R[I a] = 0` then go to `target` -/
  | jumpEq (a target : ℕ)
  /-- `I k := I k + 1` -/
  | inc (k : ℕ)
  /-- `I k := I k - 1` (truncated at `0`) -/
  | dec (k : ℕ)
  /-- if `I k = I l` then go to `target` -/
  | jumpIdx (k l target : ℕ)
  /-- halt and accept -/
  | accept
  /-- halt and reject -/
  | reject

/-- A machine: a finite program. -/
structure Machine where
  prog : List MInstr

/-- A configuration: program counter, real registers, index registers. -/
structure MConfig where
  pc : ℕ
  R : ℕ → ℝ
  I : ℕ → ℕ

/-- Apply an arithmetic operation (`none` on division by zero). -/
def TOp.apply? : TOp → ℝ → ℝ → Option ℝ
  | .add, x, y => some (x + y)
  | .sub, x, y => some (x - y)
  | .mul, x, y => some (x * y)
  | .div, x, y => if y = 0 then none else some (x / y)

/-- One step of a machine: either the next configuration or a halting outcome.  Falling off
the end of the program rejects. -/
def Machine.step (M : Machine) (c : MConfig) : MConfig ⊕ Option Bool :=
  match M.prog[c.pc]? with
  | none => .inr (some false)
  | some ins =>
    match ins with
    | .arith op d a b =>
        match op.apply? (c.R (c.I a)) (c.R (c.I b)) with
        | none => .inr none
        | some v => .inl { c with pc := c.pc + 1, R := Function.update c.R (c.I d) v }
    | .const d v => .inl { c with pc := c.pc + 1, R := Function.update c.R (c.I d) v }
    | .copy d a => .inl { c with pc := c.pc + 1, R := Function.update c.R (c.I d) (c.R (c.I a)) }
    | .jumpGe a t => .inl { c with pc := if 0 ≤ c.R (c.I a) then t else c.pc + 1 }
    | .jumpEq a t => .inl { c with pc := if c.R (c.I a) = 0 then t else c.pc + 1 }
    | .inc k => .inl { c with pc := c.pc + 1, I := Function.update c.I k (c.I k + 1) }
    | .dec k => .inl { c with pc := c.pc + 1, I := Function.update c.I k (c.I k - 1) }
    | .jumpIdx k l t => .inl { c with pc := if c.I k = c.I l then t else c.pc + 1 }
    | .accept => .inr (some true)
    | .reject => .inr (some false)

/-- Run for at most `n` steps: `some o` if the machine halts with outcome `o`, `none` if it has
not halted. -/
def Machine.run (M : Machine) : ℕ → MConfig → Option (Option Bool)
  | 0, _ => none
  | n + 1, c =>
    match M.step c with
    | .inl c' => M.run n c'
    | .inr o => some o

/-- Run for at most `n` steps, returning also the configuration at which the machine halts. -/
def Machine.runFinal (M : Machine) : ℕ → MConfig → Option (MConfig × Option Bool)
  | 0, _ => none
  | n + 1, c =>
    match M.step c with
    | .inl c' => M.runFinal n c'
    | .inr o => some (c, o)

/-- The registers holding a vector. -/
def vecReg {n : ℕ} (x : Fin n → ℝ) : ℕ → ℝ := fun i => if h : i < n then x ⟨i, h⟩ else 0

/-- The initial configuration for an input with block sizes `sizes` and contents `w`. -/
def initConfig (sizes : List ℕ) (w : ℕ → ℝ) : MConfig :=
  ⟨0, w, fun k => sizes.getD k 0⟩

/-- The set of real constants of a machine. -/
def Machine.consts (M : Machine) : Set ℝ :=
  {c | ∃ d, MInstr.const d c ∈ M.prog}

/-! ### Unrolling: the symbolic construction

Along a path of the tree the program counter and the index registers are concrete, while the
real registers are symbolic operands (`TArg`).  An arithmetic instruction creates a computation
node whose result `.val m` is stored in the destination register; a jump on a real register
creates a test node; all other instructions only change the symbolic configuration.  Registers
that are initially `0` (outside the input) are represented by `.val Z` for an index `Z` that is
never reached by the computed values, so that no constant `0` enters the tree. -/

/-- The symbolic unrolling of a machine with `fuel` steps from program counter `pc`, symbolic
real registers `R`, index registers `I`, and `m` values computed so far. -/
private def unrollAux (M : Machine) (N : ℕ) :
    ℕ → ℕ → (ℕ → TArg (Fin N)) → (ℕ → ℕ) → ℕ → Tree (Fin N)
  | 0, _, _, _, _ => .leaf false
  | fuel + 1, pc, R, I, m =>
    match M.prog[pc]? with
    | none => .leaf false
    | some (.arith op d a b) =>
        .comp op (R (I a)) (R (I b))
          (unrollAux M N fuel (pc + 1) (Function.update R (I d) (.val m)) I (m + 1))
    | some (.const d c) => unrollAux M N fuel (pc + 1) (Function.update R (I d) (.const c)) I m
    | some (.copy d a) => unrollAux M N fuel (pc + 1) (Function.update R (I d) (R (I a))) I m
    | some (.jumpGe a t) =>
        .test .ge (R (I a)) (unrollAux M N fuel t R I m) (unrollAux M N fuel (pc + 1) R I m)
    | some (.jumpEq a t) =>
        .test .eq (R (I a)) (unrollAux M N fuel t R I m) (unrollAux M N fuel (pc + 1) R I m)
    | some (.inc k) => unrollAux M N fuel (pc + 1) R (Function.update I k (I k + 1)) m
    | some (.dec k) => unrollAux M N fuel (pc + 1) R (Function.update I k (I k - 1)) m
    | some (.jumpIdx k l t) => unrollAux M N fuel (if I k = I l then t else pc + 1) R I m
    | some .accept => .leaf true
    | some .reject => .leaf false

private theorem unrollAux_depth (M : Machine) (N : ℕ) (fuel : ℕ) :
    ∀ pc R I m, (unrollAux M N fuel pc R I m).depth ≤ fuel + 1 := by
  induction fuel with
  | zero => intro pc R I m; simp [unrollAux, Tree.depth]
  | succ fuel ih =>
    intro pc R I m
    simp only [unrollAux]
    split
    all_goals try simp only [Tree.depth]
    all_goals first
      | omega
      | exact Nat.succ_le_succ (ih _ _ _ _)
      | exact (ih _ _ _ _).trans (Nat.le_succ _)
      | exact Nat.succ_le_succ (max_le (ih _ _ _ _) (ih _ _ _ _))

private theorem unroll_consts_update {N : ℕ} {S : Set ℝ} (R : ℕ → TArg (Fin N))
    (hR : ∀ i, (R i).consts ⊆ S) (k : ℕ) (t : TArg (Fin N)) (ht : t.consts ⊆ S) :
    ∀ i, (Function.update R k t i).consts ⊆ S := by
  intro i
  by_cases h : i = k
  · subst h; simpa using ht
  · simpa [Function.update_of_ne h] using hR i

private theorem unrollAux_consts (M : Machine) (N : ℕ) (fuel : ℕ) :
    ∀ pc (R : ℕ → TArg (Fin N)) I m, (∀ i, (R i).consts ⊆ M.consts) →
      (unrollAux M N fuel pc R I m).consts ⊆ M.consts := by
  induction fuel with
  | zero => intro pc R I m _; simp [unrollAux, Tree.consts]
  | succ fuel ih =>
    intro pc R I m hR
    rcases hp : M.prog[pc]? with _ | ins
    · simp [unrollAux, hp, Tree.consts]
    · cases ins with
      | arith op d a b =>
        simp only [unrollAux, hp, Tree.consts]
        exact Set.union_subset (Set.union_subset (hR _) (hR _))
          (ih _ _ _ _ (unroll_consts_update R hR _ _ (by simp [TArg.consts])))
      | const d c =>
        simp only [unrollAux, hp]
        refine ih _ _ _ _ (unroll_consts_update R hR _ _ ?_)
        simp only [TArg.consts, Set.singleton_subset_iff]
        exact ⟨d, List.mem_of_getElem? hp⟩
      | copy d a =>
        simp only [unrollAux, hp]
        exact ih _ _ _ _ (unroll_consts_update R hR _ _ (hR _))
      | jumpGe a t =>
        simp only [unrollAux, hp, Tree.consts]
        exact Set.union_subset (Set.union_subset (hR _) (ih _ _ _ _ hR)) (ih _ _ _ _ hR)
      | jumpEq a t =>
        simp only [unrollAux, hp, Tree.consts]
        exact Set.union_subset (Set.union_subset (hR _) (ih _ _ _ _ hR)) (ih _ _ _ _ hR)
      | inc k => simp only [unrollAux, hp]; exact ih _ _ _ _ hR
      | dec k => simp only [unrollAux, hp]; exact ih _ _ _ _ hR
      | jumpIdx k l t => simp only [unrollAux, hp]; exact ih _ _ _ _ hR
      | accept => simp [unrollAux, hp, Tree.consts]
      | reject => simp [unrollAux, hp, Tree.consts]

/-- A computation node, with the four operations treated uniformly. -/
private theorem unroll_runFrom_comp {N : ℕ} (w : Fin N → ℝ) (op : TOp) (a b : TArg (Fin N))
    (next : Tree (Fin N)) (vals : List ℝ) :
    (Tree.comp op a b next).runFrom w vals =
      match op.apply? (a.eval w vals) (b.eval w vals) with
      | none => none
      | some v => next.runFrom w (vals ++ [v]) := by
  cases op <;> simp only [Tree.runFrom, TOp.apply?]
  split_ifs <;> rfl

private theorem unroll_eval_append {N : ℕ} (x : Fin N → ℝ) (vals : List ℝ) (v : ℝ)
    (t : TArg (Fin N)) (ht : ∀ j, t = .val j → j < vals.length ∨ vals.length + 1 ≤ j) :
    t.eval x (vals ++ [v]) = t.eval x vals := by
  cases t with
  | input i => rfl
  | const c => rfl
  | val j =>
    simp only [TArg.eval]
    rcases ht j rfl with h | h
    · exact List.getD_append _ _ _ _ h
    · have h1 : (vals ++ [v]).length ≤ j := by simp; omega
      have h2 : vals.length ≤ j := by omega
      rw [List.getD_eq_default _ _ h1, List.getD_eq_default _ _ h2]

private theorem unrollAux_run (M : Machine) {N : ℕ} (Z : ℕ) (x : Fin N → ℝ) (fuel : ℕ) :
    ∀ (c : MConfig) (R : ℕ → TArg (Fin N)) (vals : List ℝ) (o : Option Bool),
      vals.length + fuel ≤ Z →
      (∀ i, (R i).eval x vals = c.R i) →
      (∀ i j, R i = .val j → j < vals.length ∨ Z ≤ j) →
      M.run fuel c = some o →
      (unrollAux M N fuel c.pc R c.I vals.length).runFrom x vals = o := by
  induction fuel with
  | zero => intro c R vals o _ _ _ h; simp [Machine.run] at h
  | succ fuel ih =>
    intro c R vals o hZ hR hgood h
    simp only [Machine.run, Machine.step] at h
    rcases hp : M.prog[c.pc]? with _ | ins
    · simp only [hp, Option.some_inj] at h
      simp [unrollAux, hp, Tree.runFrom, h]
    · cases ins with
      | arith op d a b =>
        simp only [hp] at h
        simp only [unrollAux, hp]
        rw [unroll_runFrom_comp, hR, hR]
        cases hv : op.apply? (c.R (c.I a)) (c.R (c.I b)) with
        | none => simpa [hv] using h
        | some v =>
          simp only [hv] at h ⊢
          have := ih _ (Function.update R (c.I d) (.val vals.length)) (vals ++ [v]) o
            (by simp; omega) ?_ ?_ h
          · simpa using this
          · intro i
            by_cases hi : i = c.I d
            · subst hi; simp [TArg.eval]
            · simp only [Function.update_of_ne hi]
              rw [unroll_eval_append x vals v _ ?_, hR]
              intro j hj
              rcases hgood i j hj with h' | h'
              · exact Or.inl h'
              · right; omega
          · intro i j hj
            by_cases hi : i = c.I d
            · subst hi; simp at hj; subst hj; simp
            · simp only [Function.update_of_ne hi] at hj
              rcases hgood i j hj with h' | h'
              · left; simp; omega
              · exact Or.inr h'
      | const d k =>
        simp only [hp] at h
        simp only [unrollAux, hp]
        refine ih _ _ vals o (by omega) ?_ ?_ h
        · intro i
          by_cases hi : i = c.I d
          · subst hi; simp [TArg.eval]
          · simp [Function.update_of_ne hi, hR]
        · intro i j hj
          by_cases hi : i = c.I d
          · subst hi; simp at hj
          · simp only [Function.update_of_ne hi] at hj
            exact hgood i j hj
      | copy d a =>
        simp only [hp] at h
        simp only [unrollAux, hp]
        refine ih _ _ vals o (by omega) ?_ ?_ h
        · intro i
          by_cases hi : i = c.I d
          · subst hi; simp [hR]
          · simp [Function.update_of_ne hi, hR]
        · intro i j hj
          by_cases hi : i = c.I d
          · subst hi; simp at hj; exact hgood _ j hj
          · simp only [Function.update_of_ne hi] at hj
            exact hgood i j hj
      | jumpGe a t =>
        simp only [hp] at h
        simp only [unrollAux, hp, Tree.runFrom, TestKind.holds, hR]
        split_ifs with hc
        · rw [ite_eq_left hc] at h
          exact ih { c with pc := t } R vals o (by omega) hR hgood h
        · rw [ite_eq_right hc] at h
          exact ih { c with pc := c.pc + 1 } R vals o (by omega) hR hgood h
      | jumpEq a t =>
        simp only [hp] at h
        simp only [unrollAux, hp, Tree.runFrom, TestKind.holds, hR]
        split_ifs with hc
        · rw [ite_eq_left hc] at h
          exact ih { c with pc := t } R vals o (by omega) hR hgood h
        · rw [ite_eq_right hc] at h
          exact ih { c with pc := c.pc + 1 } R vals o (by omega) hR hgood h
      | inc k =>
        simp only [hp] at h
        simp only [unrollAux, hp]
        exact ih { c with pc := c.pc + 1, I := Function.update c.I k (c.I k + 1) } R vals o
          (by omega) hR hgood h
      | dec k =>
        simp only [hp] at h
        simp only [unrollAux, hp]
        exact ih { c with pc := c.pc + 1, I := Function.update c.I k (c.I k - 1) } R vals o
          (by omega) hR hgood h
      | jumpIdx k l t =>
        simp only [hp] at h
        simp only [unrollAux, hp]
        exact ih { c with pc := if c.I k = c.I l then t else c.pc + 1 } R vals o
          (by omega) hR hgood h
      | accept =>
        simp only [hp, Option.some_inj] at h
        simp [unrollAux, hp, Tree.runFrom, h]
      | reject =>
        simp only [hp, Option.some_inj] at h
        simp [unrollAux, hp, Tree.runFrom, h]

/-- **Unrolling.**  For block sizes `sizes` with total length `N` and a time bound `T`, there is
a tree of depth `≤ T + 1` on `Fin N` with constants among those of the machine, whose outcome
on every input on which the machine halts within `T` steps is the machine's outcome. -/
theorem Machine.unroll (M : Machine) (sizes : List ℕ) (N T : ℕ) :
    ∃ τ : Tree (Fin N), τ.depth ≤ T + 1 ∧ τ.consts ⊆ M.consts ∧
      ∀ (x : Fin N → ℝ) (o : Option Bool),
        M.run T (initConfig sizes (vecReg x)) = some o → τ.run x = o := by
  let R₀ : ℕ → TArg (Fin N) := fun i => if h : i < N then .input ⟨i, h⟩ else .val T
  refine ⟨unrollAux M N T 0 R₀ (fun k => sizes.getD k 0) 0, unrollAux_depth M N T _ _ _ _,
    unrollAux_consts M N T _ _ _ _ ?_, ?_⟩
  · intro i
    by_cases h : i < N <;> simp [R₀, h, TArg.consts]
  · intro x o h
    refine unrollAux_run M T x T _ R₀ [] o (by simp) ?_ ?_ h
    · intro i
      by_cases h : i < N <;> simp [R₀, h, TArg.eval, initConfig, vecReg]
    · intro i j hj
      by_cases h : i < N <;> simp [R₀, h] at hj
      exact Or.inr hj.le

end ClassSep
