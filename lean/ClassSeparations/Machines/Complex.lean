import ClassSeparations.Machines.Classes
import ClassSeparations.Universal.Complex

/-!
# Machines and classes over the complex numbers

Machines over `ℂ` branch only on `v = 0` (§1.1, §2.1).  `NP_C`, `coNP_C` and `PAR_C` are
defined as over `ℝ`; algebraic circuits over `ℂ` have no sign gates (an equality gate gives
`1` if its argument is `0` and `0` otherwise).  A machine over `ℂ` that runs in time `T` unrolls
into a complex tree of depth `≤ T + 1` (§5.6).
-/

noncomputable section

open Classical

namespace ClassSep

/-- Instructions of a complex random-access machine. -/
inductive CMInstr where
  | arith (op : TOp) (d a b : ℕ)
  | const (d : ℕ) (c : ℂ)
  | copy (d a : ℕ)
  /-- if `R[I a] = 0` then go to `target` -/
  | jumpEq (a target : ℕ)
  | inc (k : ℕ)
  | dec (k : ℕ)
  | jumpIdx (k l target : ℕ)
  | accept
  | reject

/-- A complex machine. -/
structure CMachine where
  prog : List CMInstr

/-- A configuration of a complex machine. -/
structure CMConfig where
  pc : ℕ
  R : ℕ → ℂ
  I : ℕ → ℕ

/-- Apply an arithmetic operation over `ℂ` (`none` on division by zero). -/
def TOp.applyC? : TOp → ℂ → ℂ → Option ℂ
  | .add, x, y => some (x + y)
  | .sub, x, y => some (x - y)
  | .mul, x, y => some (x * y)
  | .div, x, y => if y = 0 then none else some (x / y)

/-- One step of a complex machine. -/
def CMachine.step (M : CMachine) (c : CMConfig) : CMConfig ⊕ Option Bool :=
  match M.prog[c.pc]? with
  | none => .inr (some false)
  | some ins =>
    match ins with
    | .arith op d a b =>
        match op.applyC? (c.R (c.I a)) (c.R (c.I b)) with
        | none => .inr none
        | some v => .inl { c with pc := c.pc + 1, R := Function.update c.R (c.I d) v }
    | .const d v => .inl { c with pc := c.pc + 1, R := Function.update c.R (c.I d) v }
    | .copy d a => .inl { c with pc := c.pc + 1, R := Function.update c.R (c.I d) (c.R (c.I a)) }
    | .jumpEq a t => .inl { c with pc := if c.R (c.I a) = 0 then t else c.pc + 1 }
    | .inc k => .inl { c with pc := c.pc + 1, I := Function.update c.I k (c.I k + 1) }
    | .dec k => .inl { c with pc := c.pc + 1, I := Function.update c.I k (c.I k - 1) }
    | .jumpIdx k l t => .inl { c with pc := if c.I k = c.I l then t else c.pc + 1 }
    | .accept => .inr (some true)
    | .reject => .inr (some false)

/-- Run a complex machine for at most `n` steps. -/
def CMachine.run (M : CMachine) : ℕ → CMConfig → Option (Option Bool)
  | 0, _ => none
  | n + 1, c =>
    match M.step c with
    | .inl c' => M.run n c'
    | .inr o => some o

/-- Run, returning also the halting configuration. -/
def CMachine.runFinal (M : CMachine) : ℕ → CMConfig → Option (CMConfig × Option Bool)
  | 0, _ => none
  | n + 1, c =>
    match M.step c with
    | .inl c' => M.runFinal n c'
    | .inr o => some (c, o)

/-- The registers holding a complex vector. -/
def vecRegC {n : ℕ} (x : Fin n → ℂ) : ℕ → ℂ := fun i => if h : i < n then x ⟨i, h⟩ else 0

/-- The initial configuration. -/
def initConfigC (sizes : List ℕ) (w : ℕ → ℂ) : CMConfig := ⟨0, w, fun k => sizes.getD k 0⟩

/-- The constants of a complex machine. -/
def CMachine.consts (M : CMachine) : Set ℂ := {c | ∃ d, CMInstr.const d c ∈ M.prog}

/-- The symbolic unrolling of a complex machine (as `Machine.unroll`): program counter and
index registers are concrete, real registers are symbolic operands, `m` values computed so far. -/
private def cunrollAux (M : CMachine) (N : ℕ) :
    ℕ → ℕ → (ℕ → CArg (Fin N)) → (ℕ → ℕ) → ℕ → CTree (Fin N)
  | 0, _, _, _, _ => .leaf false
  | fuel + 1, pc, R, I, m =>
    match M.prog[pc]? with
    | none => .leaf false
    | some (.arith op d a b) =>
        .comp op (R (I a)) (R (I b))
          (cunrollAux M N fuel (pc + 1) (Function.update R (I d) (.val m)) I (m + 1))
    | some (.const d c) => cunrollAux M N fuel (pc + 1) (Function.update R (I d) (.const c)) I m
    | some (.copy d a) => cunrollAux M N fuel (pc + 1) (Function.update R (I d) (R (I a))) I m
    | some (.jumpEq a t) =>
        .test (R (I a)) (cunrollAux M N fuel t R I m) (cunrollAux M N fuel (pc + 1) R I m)
    | some (.inc k) => cunrollAux M N fuel (pc + 1) R (Function.update I k (I k + 1)) m
    | some (.dec k) => cunrollAux M N fuel (pc + 1) R (Function.update I k (I k - 1)) m
    | some (.jumpIdx k l t) => cunrollAux M N fuel (if I k = I l then t else pc + 1) R I m
    | some .accept => .leaf true
    | some .reject => .leaf false

private theorem cunrollAux_depth (M : CMachine) (N : ℕ) (fuel : ℕ) :
    ∀ pc R I m, (cunrollAux M N fuel pc R I m).depth ≤ fuel + 1 := by
  induction fuel with
  | zero => intro pc R I m; simp [cunrollAux, CTree.depth]
  | succ fuel ih =>
    intro pc R I m
    simp only [cunrollAux]
    split
    all_goals try simp only [CTree.depth]
    all_goals first
      | omega
      | exact Nat.succ_le_succ (ih _ _ _ _)
      | exact (ih _ _ _ _).trans (Nat.le_succ _)
      | exact Nat.succ_le_succ (max_le (ih _ _ _ _) (ih _ _ _ _))

/-- A computation node of a complex tree, with the four operations treated uniformly. -/
private theorem cunroll_runFrom_comp {N : ℕ} (w : Fin N → ℂ) (op : TOp) (a b : CArg (Fin N))
    (next : CTree (Fin N)) (vals : List ℂ) :
    (CTree.comp op a b next).runFrom w vals =
      match op.applyC? (CTree.argEval w vals a) (CTree.argEval w vals b) with
      | none => none
      | some v => next.runFrom w (vals ++ [v]) := by
  cases op <;> simp only [CTree.runFrom, TOp.applyC?]
  split_ifs <;> rfl

private theorem cunroll_eval_append {N : ℕ} (x : Fin N → ℂ) (vals : List ℂ) (v : ℂ)
    (t : CArg (Fin N)) (ht : ∀ j, t = .val j → j < vals.length) :
    CTree.argEval x (vals ++ [v]) t = CTree.argEval x vals t := by
  cases t with
  | input i => rfl
  | const c => rfl
  | val j => exact List.getD_append _ _ _ _ (ht j rfl)

private theorem cunrollAux_run (M : CMachine) {N : ℕ} (x : Fin N → ℂ) (fuel : ℕ) :
    ∀ (c : CMConfig) (R : ℕ → CArg (Fin N)) (vals : List ℂ) (o : Option Bool),
      (∀ i, CTree.argEval x vals (R i) = c.R i) →
      (∀ i j, R i = .val j → j < vals.length) →
      M.run fuel c = some o →
      (cunrollAux M N fuel c.pc R c.I vals.length).runFrom x vals = o := by
  induction fuel with
  | zero => intro c R vals o _ _ h; simp [CMachine.run] at h
  | succ fuel ih =>
    intro c R vals o hR hgood h
    simp only [CMachine.run, CMachine.step] at h
    rcases hp : M.prog[c.pc]? with _ | ins
    · simp only [hp, Option.some_inj] at h
      simp [cunrollAux, hp, CTree.runFrom, h]
    · cases ins with
      | arith op d a b =>
        simp only [hp] at h
        simp only [cunrollAux, hp]
        rw [cunroll_runFrom_comp, hR, hR]
        cases hv : op.applyC? (c.R (c.I a)) (c.R (c.I b)) with
        | none => simpa [hv] using h
        | some v =>
          simp only [hv] at h ⊢
          have := ih _ (Function.update R (c.I d) (.val vals.length)) (vals ++ [v]) o ?_ ?_ h
          · simpa using this
          · intro i
            by_cases hi : i = c.I d
            · subst hi; simp [CTree.argEval]
            · simp only [Function.update_of_ne hi]
              rw [cunroll_eval_append x vals v _ (hgood i), hR]
          · intro i j hj
            by_cases hi : i = c.I d
            · subst hi; simp at hj; subst hj; simp
            · simp only [Function.update_of_ne hi] at hj
              have := hgood i j hj
              simp; omega
      | const d k =>
        simp only [hp] at h
        simp only [cunrollAux, hp]
        refine ih _ _ vals o ?_ ?_ h
        · intro i
          by_cases hi : i = c.I d
          · subst hi; simp [CTree.argEval]
          · simp [Function.update_of_ne hi, hR]
        · intro i j hj
          by_cases hi : i = c.I d
          · subst hi; simp at hj
          · simp only [Function.update_of_ne hi] at hj
            exact hgood i j hj
      | copy d a =>
        simp only [hp] at h
        simp only [cunrollAux, hp]
        refine ih _ _ vals o ?_ ?_ h
        · intro i
          by_cases hi : i = c.I d
          · subst hi; simp [hR]
          · simp [Function.update_of_ne hi, hR]
        · intro i j hj
          by_cases hi : i = c.I d
          · subst hi; simp at hj; exact hgood _ j hj
          · simp only [Function.update_of_ne hi] at hj
            exact hgood i j hj
      | jumpEq a t =>
        simp only [hp] at h
        simp only [cunrollAux, hp, CTree.runFrom, hR]
        split_ifs with hc
        · rw [ite_eq_left hc] at h
          exact ih { c with pc := t } R vals o hR hgood h
        · rw [ite_eq_right hc] at h
          exact ih { c with pc := c.pc + 1 } R vals o hR hgood h
      | inc k =>
        simp only [hp] at h
        simp only [cunrollAux, hp]
        exact ih { c with pc := c.pc + 1, I := Function.update c.I k (c.I k + 1) } R vals o
          hR hgood h
      | dec k =>
        simp only [hp] at h
        simp only [cunrollAux, hp]
        exact ih { c with pc := c.pc + 1, I := Function.update c.I k (c.I k - 1) } R vals o
          hR hgood h
      | jumpIdx k l t =>
        simp only [hp] at h
        simp only [cunrollAux, hp]
        exact ih { c with pc := if c.I k = c.I l then t else c.pc + 1 } R vals o hR hgood h
      | accept =>
        simp only [hp, Option.some_inj] at h
        simp [cunrollAux, hp, CTree.runFrom, h]
      | reject =>
        simp only [hp, Option.some_inj] at h
        simp [cunrollAux, hp, CTree.runFrom, h]

/-- **Unrolling** over `ℂ`. -/
theorem CMachine.unroll (M : CMachine) (sizes : List ℕ) (N T : ℕ) :
    ∃ τ : CTree (Fin N), τ.depth ≤ T + 1 ∧
      ∀ (x : Fin N → ℂ) (o : Option Bool),
        M.run T (initConfigC sizes (vecRegC x)) = some o → τ.runFrom x [] = o := by
  let R₀ : ℕ → CArg (Fin N) := fun i => if h : i < N then .input ⟨i, h⟩ else .const 0
  refine ⟨cunrollAux M N T 0 R₀ (fun k => sizes.getD k 0) 0,
    cunrollAux_depth M N T _ _ _ _, ?_⟩
  intro x o h
  refine cunrollAux_run M x T _ R₀ [] o ?_ ?_ h
  · intro i
    by_cases h : i < N <;> simp [R₀, h, CTree.argEval, initConfigC, vecRegC]
  · intro i j hj
    by_cases h : i < N <;> simp [R₀, h] at hj

/-- A language over `ℂ`. -/
abbrev LangC := ∀ n : ℕ, Set (Fin n → ℂ)

/-- The complement of a language over `ℂ`. -/
def LangC.compl (L : LangC) : LangC := fun n => (L n)ᶜ

/-- `NP_ℂ`. -/
def NP_C : Set LangC :=
  {L | ∃ (M : CMachine) (p q : ℕ → ℕ), PolyBounded p ∧ PolyBounded q ∧ ∀ n (x : Fin n → ℂ),
    (∀ z : Fin (q n) → ℂ,
      ∃ o, M.run (p n) (initConfigC [n, q n] (vecRegC (Fin.append x z))) = some o) ∧
    (x ∈ L n ↔ ∃ z : Fin (q n) → ℂ,
      M.run (p n) (initConfigC [n, q n] (vecRegC (Fin.append x z))) = some (some true))}

/-- `coNP_ℂ`. -/
def coNP_C : Set LangC := {L | L.compl ∈ NP_C}

/-- A gate of an algebraic circuit over `ℂ`. -/
inductive CGate where
  | input (i : ℕ)
  | const (c : ℂ)
  | arith (op : TOp) (j k : ℕ)
  /-- `1` if the value of gate `j` is `0`, else `0` -/
  | isZero (j : ℕ)

/-- An algebraic circuit over `ℂ`. -/
abbrev CCircuit := List CGate

/-- The values of the gates on input `x`. -/
def CCircuit.values (C : CCircuit) (x : ℕ → ℂ) : Option (List ℂ) :=
  C.foldl (fun acc g => acc.bind fun vals =>
    match g with
    | .input i => some (vals ++ [x i])
    | .const c => some (vals ++ [c])
    | .arith op j k =>
        if hj : j < vals.length then if hk : k < vals.length then
          (op.applyC? vals[j] vals[k]).map fun v => vals ++ [v]
        else none else none
    | .isZero j => if hj : j < vals.length then
        some (vals ++ [if vals[j] = 0 then 1 else 0]) else none) (some [])

/-- Depths of the gates. -/
def CCircuit.gateDepths (C : CCircuit) : List ℕ :=
  C.foldl (fun ds g =>
    ds ++ [match g with
      | .input _ => 0
      | .const _ => 0
      | .arith _ j k => max (ds.getD j 0) (ds.getD k 0) + 1
      | .isZero j => ds.getD j 0 + 1]) []

/-- The depth of a complex circuit. -/
def CCircuit.depth (C : CCircuit) : ℕ := C.gateDepths.foldl max 0

/-- The circuit decides `S ⊆ ℂⁿ`. -/
def CCircuit.Decides {n : ℕ} (C : CCircuit) (S : Set (Fin n → ℂ)) : Prop :=
  ∀ x : Fin n → ℂ, ∃ vals, C.values (vecRegC x) = some vals ∧
    vals.getLast? = some (if x ∈ S then 1 else 0)

/-- Type code, operands and constant of a complex gate. -/
def CGate.code : CGate → ℂ
  | .input _ => 0
  | .const _ => 1
  | .arith .add _ _ => 2
  | .arith .sub _ _ => 3
  | .arith .mul _ _ => 4
  | .arith .div _ _ => 5
  | .isZero _ => 6

def CGate.op₁ : CGate → ℕ
  | .input i => i
  | .const _ => 0
  | .arith _ j _ => j
  | .isZero j => j

def CGate.op₂ : CGate → ℕ
  | .arith _ _ k => k
  | _ => 0

def CGate.cst : CGate → ℂ
  | .const c => c
  | _ => 0

/-- The description of a complex gate in registers `R 0, …, R (2b+1)`. -/
def CGate.describe (b : ℕ) (g : CGate) (k : ℕ) : ℂ :=
  if k = 0 then g.code
  else if k ≤ b then (if g.op₁.testBit (k - 1) then 1 else 0)
  else if k ≤ 2 * b then (if g.op₂.testBit (k - 1 - b) then 1 else 0)
  else g.cst

/-- The binary digits of `i` as complex numbers. -/
def bitsOfC (b i : ℕ) : Fin b → ℂ := fun j => if i.testBit j then 1 else 0

/-- `U` describes the complex circuit family `C`. -/
def CMachine.Describes (U : CMachine) (C : ℕ → CCircuit) (b p : ℕ → ℕ) : Prop :=
  ∀ n, ∀ i (hi : i < (C n).length), ∃ cfg : CMConfig,
    U.runFinal (p n) (initConfigC [n, b n] (vecRegC (bitsOfC (b n) i))) =
      some (cfg, some true) ∧
    ∀ k ≤ 2 * b n + 1, cfg.R k = ((C n)[i]'hi).describe (b n) k

/-- `PAR_ℂ`. -/
def PAR_C : Set LangC :=
  {L | ∃ (C : ℕ → CCircuit) (U : CMachine) (b d p : ℕ → ℕ),
    PolyBounded b ∧ PolyBounded d ∧ PolyBounded p ∧ U.Describes C b p ∧
    ∀ n, (C n).length ≤ 2 ^ b n ∧ (∀ g ∈ C n, g.op₁ < 2 ^ b n ∧ g.op₂ < 2 ^ b n) ∧
      (C n).depth ≤ d n ∧ (C n).Decides (L n)}

end ClassSep
