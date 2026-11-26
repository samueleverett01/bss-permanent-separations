import ClassSeparations.Machines.Program
import ClassSeparations.Machines.RyserCircuit

/-!
# The describer of the Ryser circuits

A machine that, on input `(n, i)` (block sizes `[n, b]` with `b = 3m + 5` if `n = m² + 1`,
`m ≥ 1`, and `b = 0` otherwise; contents the bits of the gate index `i`), halts with the
description of gate `i` of the Ryser circuit (`Ryser.gate m i`) in its registers.

The program (`Ryser.descProg`):
1. If `b = 0`: write the description of the gate `const 0` and accept.
2. Setup: compute `m` from `b` and the addresses of all bit fields in index registers.
3. Copy the input bits to the source area `[SRC, SRC + b)`, `SRC = 2b + 2`, and clear the output
   area `[0, 2b + 2)`.
4. Dispatch on the bits `tag`, `kind`, `J₀`, `I₀` of the index and write the description by
   copying/filling bit fields (`FOp`), with three loops: `lookup` (`look m F J`), `signScan`
   (`sgn m F`) and `countUp` (writing `pc(I) · m + pc(J)` in binary).
-/

noncomputable section

open Classical

namespace ClassSep

namespace Ryser

open Prog

/-! ## Registers -/

/-- Index registers: `0` = `n`, `1` = `b`, `2` = zero, `3–8` scratch, `9` setup counter,
`10–40` field addresses and lengths. -/
abbrev rZ : ℕ := 2
abbrev rP : ℕ := 3
abbrev rQ : ℕ := 4
abbrev rC : ℕ := 5
abbrev rC2 : ℕ := 6
abbrev rBQ : ℕ := 7
abbrev rT : ℕ := 9
abbrev rM : ℕ := 10
abbrev rM1 : ℕ := 11
abbrev rM2 : ℕ := 12
abbrev rONE : ℕ := 13
abbrev rO1K1 : ℕ := 14
abbrev rO1J : ℕ := 15
abbrev rO1J1 : ℕ := 16
abbrev rO1I : ℕ := 17
abbrev rO1F : ℕ := 18
abbrev rO1T0 : ℕ := 19
abbrev rO1T1 : ℕ := 20
abbrev rO2K0 : ℕ := 21
abbrev rO2K1 : ℕ := 22
abbrev rO2J : ℕ := 23
abbrev rO2J1 : ℕ := 24
abbrev rO2I : ℕ := 25
abbrev rO2F : ℕ := 26
abbrev rO2T0 : ℕ := 27
abbrev rO2T1 : ℕ := 28
abbrev rCST : ℕ := 29
abbrev rSRC : ℕ := 30
abbrev rSK1 : ℕ := 31
abbrev rSK2 : ℕ := 32
abbrev rSJ : ℕ := 33
abbrev rSJ1 : ℕ := 34
abbrev rSI : ℕ := 35
abbrev rSI1 : ℕ := 36
abbrev rSF : ℕ := 37
abbrev rST0 : ℕ := 38
abbrev rST1 : ℕ := 39
abbrev rSCR : ℕ := 40

/-- Initial values `α` of the setup registers. -/
def initList : List (ℕ × ℕ) :=
  [(rT, 5), (rONE, 1), (rO1K1, 2), (rO1J, 4), (rO1J1, 5), (rO1I, 4), (rO1F, 4), (rO1T0, 4),
   (rO1T1, 5), (rO2K0, 6), (rO2K1, 7), (rO2J, 9), (rO2J1, 10), (rO2I, 9), (rO2F, 9),
   (rO2T0, 9), (rO2T1, 10), (rCST, 11), (rSRC, 12), (rSK1, 13), (rSK2, 14), (rSJ, 15),
   (rSJ1, 16), (rSI, 15), (rSI1, 16), (rSF, 15), (rST0, 15), (rST1, 16), (rSCR, 17)]

/-- Increments `β` per setup iteration (the setup loop runs `m` times). -/
def stepList : List (ℕ × ℕ) :=
  [(rT, 3), (rM, 1), (rM1, 1), (rM2, 2), (rO1I, 1), (rO1F, 2), (rO1T0, 3), (rO1T1, 3),
   (rO2K0, 3), (rO2K1, 3), (rO2J, 3), (rO2J1, 3), (rO2I, 4), (rO2F, 5), (rO2T0, 6),
   (rO2T1, 6), (rCST, 6), (rSRC, 6), (rSK1, 6), (rSK2, 6), (rSJ, 6), (rSJ1, 6), (rSI, 7),
   (rSI1, 7), (rSF, 8), (rST0, 9), (rST1, 9), (rSCR, 9)]

/-- The index registers after the setup, for `b = 3m + 5`. -/
def regs (n m : ℕ) (k : ℕ) : ℕ :=
  if k = 0 then n else if k = 1 then 3 * m + 5 else if k = rM1 then m - 1
  else addAmt initList k + m * addAmt stepList k

section regvals
variable (n m : ℕ)
@[simp] theorem regs_0 : regs n m 0 = n := rfl
@[simp] theorem regs_1 : regs n m 1 = 3 * m + 5 := rfl
@[simp] theorem regs_Z : regs n m rZ = 0 := by simp [regs, addAmt, initList, stepList]
@[simp] theorem regs_P : regs n m rP = 0 := by simp [regs, addAmt, initList, stepList]
@[simp] theorem regs_Q : regs n m rQ = 0 := by simp [regs, addAmt, initList, stepList]
@[simp] theorem regs_C : regs n m rC = 0 := by simp [regs, addAmt, initList, stepList]
@[simp] theorem regs_C2 : regs n m rC2 = 0 := by simp [regs, addAmt, initList, stepList]
@[simp] theorem regs_BQ : regs n m rBQ = 0 := by simp [regs, addAmt, initList, stepList]
@[simp] theorem regs_M : regs n m rM = m := by simp [regs, addAmt, initList, stepList]
@[simp] theorem regs_M1 : regs n m rM1 = m - 1 := by simp [regs]
@[simp] theorem regs_M2 : regs n m rM2 = 2 * m := by simp [regs, addAmt, initList, stepList]; ring
@[simp] theorem regs_ONE : regs n m rONE = 1 := by simp [regs, addAmt, initList, stepList]
@[simp] theorem regs_O1K1 : regs n m rO1K1 = 2 := by simp [regs, addAmt, initList, stepList]
@[simp] theorem regs_O1J : regs n m rO1J = 4 := by simp [regs, addAmt, initList, stepList]
@[simp] theorem regs_O1J1 : regs n m rO1J1 = 5 := by simp [regs, addAmt, initList, stepList]
@[simp] theorem regs_O1I : regs n m rO1I = m + 4 := by
  simp [regs, addAmt, initList, stepList]; ring
@[simp] theorem regs_O1F : regs n m rO1F = 2 * m + 4 := by
  simp [regs, addAmt, initList, stepList]; ring
@[simp] theorem regs_O1T0 : regs n m rO1T0 = 3 * m + 4 := by
  simp [regs, addAmt, initList, stepList]; ring
@[simp] theorem regs_O1T1 : regs n m rO1T1 = 3 * m + 5 := by
  simp [regs, addAmt, initList, stepList]; ring
@[simp] theorem regs_O2K0 : regs n m rO2K0 = 3 * m + 6 := by
  simp [regs, addAmt, initList, stepList]; ring
@[simp] theorem regs_O2K1 : regs n m rO2K1 = 3 * m + 7 := by
  simp [regs, addAmt, initList, stepList]; ring
@[simp] theorem regs_O2J : regs n m rO2J = 3 * m + 9 := by
  simp [regs, addAmt, initList, stepList]; ring
@[simp] theorem regs_O2J1 : regs n m rO2J1 = 3 * m + 10 := by
  simp [regs, addAmt, initList, stepList]; ring
@[simp] theorem regs_O2I : regs n m rO2I = 4 * m + 9 := by
  simp [regs, addAmt, initList, stepList]; ring
@[simp] theorem regs_O2F : regs n m rO2F = 5 * m + 9 := by
  simp [regs, addAmt, initList, stepList]; ring
@[simp] theorem regs_O2T0 : regs n m rO2T0 = 6 * m + 9 := by
  simp [regs, addAmt, initList, stepList]; ring
@[simp] theorem regs_O2T1 : regs n m rO2T1 = 6 * m + 10 := by
  simp [regs, addAmt, initList, stepList]; ring
@[simp] theorem regs_CST : regs n m rCST = 6 * m + 11 := by
  simp [regs, addAmt, initList, stepList]; ring
@[simp] theorem regs_SRC : regs n m rSRC = 6 * m + 12 := by
  simp [regs, addAmt, initList, stepList]; ring
@[simp] theorem regs_SK1 : regs n m rSK1 = 6 * m + 13 := by
  simp [regs, addAmt, initList, stepList]; ring
@[simp] theorem regs_SK2 : regs n m rSK2 = 6 * m + 14 := by
  simp [regs, addAmt, initList, stepList]; ring
@[simp] theorem regs_SJ : regs n m rSJ = 6 * m + 15 := by
  simp [regs, addAmt, initList, stepList]; ring
@[simp] theorem regs_SJ1 : regs n m rSJ1 = 6 * m + 16 := by
  simp [regs, addAmt, initList, stepList]; ring
@[simp] theorem regs_SI : regs n m rSI = 7 * m + 15 := by
  simp [regs, addAmt, initList, stepList]; ring
@[simp] theorem regs_SI1 : regs n m rSI1 = 7 * m + 16 := by
  simp [regs, addAmt, initList, stepList]; ring
@[simp] theorem regs_SF : regs n m rSF = 8 * m + 15 := by
  simp [regs, addAmt, initList, stepList]; ring
@[simp] theorem regs_ST0 : regs n m rST0 = 9 * m + 15 := by
  simp [regs, addAmt, initList, stepList]; ring
@[simp] theorem regs_ST1 : regs n m rST1 = 9 * m + 16 := by
  simp [regs, addAmt, initList, stepList]; ring
@[simp] theorem regs_SCR : regs n m rSCR = 9 * m + 17 := by
  simp [regs, addAmt, initList, stepList]; ring
end regvals

/-! ## The setup -/

/-- Compute `m` from `b = 3m + 5` and the field addresses. -/
def setup : Stmt :=
  .seqs [addConsts initList, .loop (.idxEq rT 1) (addConsts stepList), .op (.dec rM1)]

theorem setup_spec (n m : ℕ) (R : ℕ → ℝ) :
    Runs setup (St.init [n, 3 * m + 5] R) (· = ⟨R, regs n m⟩) (300 + 160 * m) := by
  let I0 : ℕ → ℕ := fun k => [n, 3 * m + 5].getD k 0
  have hI0 : ∀ k, 2 ≤ k → I0 k = 0 := by
    intro k hk
    simp only [I0]
    rw [List.getD_eq_default _ _ (by simp; omega)]
  have hloop : Runs (.loop (.idxEq rT 1) (addConsts stepList))
      ⟨R, fun k => I0 k + addAmt initList k⟩
      (· = ⟨R, fun k => I0 k + addAmt initList k + m * addAmt stepList k⟩)
      (m * ((stepList.map (·.2)).sum + 2) + 1) := by
    refine Spec.loop (fun j st' => st' = ⟨R, fun k => I0 k + addAmt initList k +
      j * addAmt stepList k⟩) m ?_ ?_ ?_ (by simp)
    · rintro st' rfl
      simp [I0, addAmt, initList, stepList]
      ring
    · rintro j hj st' rfl
      simp [I0, addAmt, initList, stepList]
      omega
    · rintro j hj st' rfl
      refine (addConsts_spec stepList _).mono_post ?_
      rintro st'' rfl
      congr 1
      funext k
      simp only
      ring
  have h3 : Runs (Stmt.seqs [.op (.dec rM1)])
      ⟨R, fun k => I0 k + addAmt initList k + m * addAmt stepList k⟩ (· = ⟨R, regs n m⟩)
      (1 + 0) := by
    refine Spec.seq_op rfl (Spec.skip ?_)
    congr 1
    funext k
    simp only [Function.update_apply, regs]
    by_cases h0 : k = 0
    · subst h0; simp [I0, addAmt, initList, stepList]
    by_cases h1 : k = 1
    · subst h1; simp [I0, addAmt, initList, stepList]
    by_cases h11 : k = rM1
    · subst h11; simp [I0, addAmt, initList, stepList]
    · simp [h0, h1, h11, hI0 k (by omega)]
  have := (addConsts_spec initList (St.init [n, 3 * m + 5] R)).seq_eq (hloop.seq_eq h3)
  refine this.mono_time ?_
  simp [initList, stepList]
  omega

/-! ## Copying the input and clearing the output area -/

/-- The real registers after copying the input bits to `[SRC, SRC + b)` and clearing
`[0, SRC)`. -/
def R2 (m i : ℕ) : ℕ → ℝ :=
  fun k => if 6 * m + 12 ≤ k ∧ k < 9 * m + 17 then bitR (i.testBit (k - (6 * m + 12))) else 0

theorem R2_lo {m i k : ℕ} (h : k < 6 * m + 12) : R2 m i k = 0 := ite_eq_right (by omega)

theorem R2_src {m i k : ℕ} (h : 6 * m + 12 ≤ k ∧ k < 9 * m + 17) :
    R2 m i k = bitR (i.testBit (k - (6 * m + 12))) := ite_eq_left h

theorem R2_hi {m i k : ℕ} (h : 9 * m + 17 ≤ k) : R2 m i k = 0 := ite_eq_right (by omega)

theorem update_of_eq' {f : ℕ → ℝ} {a x : ℕ} {v : ℝ} (h : x = a) : Function.update f a v x = v := by
  subst h; simp

/-- The operations of phases 1 and 2. -/
def prepOps : List FOp := [.copy rZ rSRC 1, .fill rZ rSRC 0]

/-- Run a list of field operations with the standard scratch registers. -/
abbrev ops (l : List FOp) : Stmt := FOp.prog rP rQ rC rZ l

theorem ops_spec (n m : ℕ) (R : ℕ → ℝ) (l : List FOp) (hok : ∀ o ∈ l, o.Ok rP rQ rC (regs n m)) :
    Runs (ops l) ⟨R, regs n m⟩ (· = ⟨FOp.evalList (regs n m) l R, regs n m⟩)
      (l.map (FOp.time (regs n m))).sum :=
  FOp.prog_spec (st := ⟨R, regs n m⟩) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (regs_P n m) (regs_Q n m) (regs_C n m) (regs_Z n m) l hok

theorem prep_spec (n m i : ℕ) :
    Runs (ops prepOps) ⟨vecReg (bitsOf (3 * m + 5) i), regs n m⟩ (· = ⟨R2 m i, regs n m⟩)
      (150 * m + 300) := by
  refine (ops_spec n m _ prepOps ?_).mono_time ?_ |>.mono_post ?_
  · simp [prepOps, FOp.Ok]
    omega
  · simp [prepOps, FOp.time]
    omega
  · rintro st rfl
    congr 1
    funext k
    simp only [prepOps, FOp.evalList_cons, FOp.evalList_nil, FOp.eval, regs_Z, regs_SRC, regs_1,
      copyR, fillR, R2, vecReg, bitsOf, bitR]
    split_ifs <;> first | omega | rfl | simp_all

/-! ## Descriptions -/

/-- The registers `0, …, 2b + 1` hold the description of `g`. -/
def DescOK (b : ℕ) (g : AGate) (R : ℕ → ℝ) : Prop := ∀ k ≤ 2 * b + 1, R k = g.describe b k

theorem descOK_of {b : ℕ} {g : AGate} {R : ℕ → ℝ} (h0 : R 0 = g.code)
    (h1 : ∀ q < b, R (1 + q) = bitR (g.op₁.testBit q))
    (h2 : ∀ q < b, R (b + 1 + q) = bitR (g.op₂.testBit q)) (h3 : R (2 * b + 1) = g.cst) :
    DescOK b g R := by
  intro k hk
  unfold AGate.describe
  by_cases ha : k = 0
  · rw [ite_eq_left ha]; subst ha; exact h0
  rw [ite_eq_right ha]
  by_cases hb : k ≤ b
  · rw [ite_eq_left hb]
    have := h1 (k - 1) (by omega)
    rw [show 1 + (k - 1) = k by omega] at this
    exact this
  rw [ite_eq_right hb]
  by_cases hc : k ≤ 2 * b
  · rw [ite_eq_left hc]
    have := h2 (k - 1 - b) (by omega)
    rw [show b + 1 + (k - 1 - b) = k by omega] at this
    exact this
  · rw [ite_eq_right hc, show k = 2 * b + 1 by omega]; exact h3

/-- The bits of a gate index, field by field. -/
theorem bits_idx {R : ℕ → ℝ} {base m t F I J k : ℕ} (hk : k < 8) (hJ : J < 2 ^ m)
    (hI : I < 2 ^ m) (hF : F < 2 ^ m)
    (hK : ∀ q < 3, R (base + q) = bitR (k.testBit q))
    (hJf : ∀ q < m, R (base + 3 + q) = bitR (J.testBit q))
    (hIf : ∀ q < m, R (base + 3 + m + q) = bitR (I.testBit q))
    (hFf : ∀ q < m, R (base + 3 + 2 * m + q) = bitR (F.testBit q))
    (hT : ∀ q < 2, R (base + 3 + 3 * m + q) = bitR (t.testBit q)) :
    ∀ q < 3 * m + 5, R (base + q) = bitR ((idx m t F I J k).testBit q) := by
  intro q hq
  rw [idx_testBit hk hJ hI hF]
  split_ifs with h1 h2 h3 h4
  · exact hK q h1
  · have := hJf (q - 3) (by omega)
    rwa [show base + 3 + (q - 3) = base + q by omega] at this
  · have := hIf (q - (3 + m)) (by omega)
    rwa [show base + 3 + m + (q - (3 + m)) = base + q by omega] at this
  · have := hFf (q - (3 + 2 * m)) (by omega)
    rwa [show base + 3 + 2 * m + (q - (3 + 2 * m)) = base + q by omega] at this
  · have := hT (q - (3 + 3 * m)) (by omega)
    rwa [show base + 3 + 3 * m + (q - (3 + 3 * m)) = base + q by omega] at this

/-- A field holding `0`. -/
theorem bits_zero_of {R : ℕ → ℝ} {base w : ℕ} (h : ∀ q < w, R (base + q) = 0) :
    ∀ q < w, R (base + q) = bitR ((0 : ℕ).testBit q) := by
  intro q hq; simp [h q hq]

/-- A field holding `2^w - 1`. -/
theorem bits_ones_of {R : ℕ → ℝ} {base w : ℕ} (h : ∀ q < w, R (base + q) = 1) :
    ∀ q < w, R (base + q) = bitR ((2 ^ w - 1).testBit q) := by
  intro q hq; simp [h q hq, hq]

theorem two_mul_mod_add_one_lt {m : ℕ} (hm : 1 ≤ m) (J : ℕ) : 2 * J % 2 ^ m + 1 < 2 ^ m := by
  have h1 : 2 ^ m = 2 * 2 ^ (m - 1) := by rw [← pow_succ']; congr 1; omega
  have h2 : 2 * J % 2 ^ m = 2 * (J % 2 ^ (m - 1)) := by rw [h1, Nat.mul_mod_mul_left]
  have h3 := Nat.mod_lt J (Nat.two_pow_pos (m - 1))
  omega

theorem testBit_two_mul' (J q : ℕ) :
    (2 * J).testBit q = (decide (1 ≤ q) && J.testBit (q - 1)) := by
  rw [show 2 * J = 2 ^ 1 * J by ring, Nat.testBit_two_pow_mul]

theorem testBit_two_mul_mod (J m q : ℕ) :
    (2 * J % 2 ^ m).testBit q = (decide (q < m) && (decide (1 ≤ q) && J.testBit (q - 1))) := by
  rw [Nat.testBit_mod_two_pow, show 2 * J = 2 ^ 1 * J by ring, Nat.testBit_two_pow_mul]

theorem testBit_two_mul_mod_add_one {m : ℕ} (hm : 1 ≤ m) (J q : ℕ) :
    (2 * J % 2 ^ m + 1).testBit q =
      (decide (q < m) && (decide (q = 0) || J.testBit (q - 1))) := by
  have h : 2 * J % 2 ^ m = 2 ^ 1 * (J % 2 ^ (m - 1)) := by
    rw [show 2 ^ m = 2 * 2 ^ (m - 1) by rw [← pow_succ']; congr 1; omega, Nat.mul_mod_mul_left]
    ring
  rw [h, Nat.testBit_two_pow_mul_add _ (by norm_num)]
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp; omega
  · rw [ite_eq_right (by omega), Nat.testBit_mod_two_pow,
      show decide (q - 1 < m - 1) = decide (q < m) from decide_eq_decide.mpr (by omega)]
    simp [show q ≠ 0 by omega]

/-- Evaluate the real registers after field operations at a position, deciding all address
comparisons by `omega`. -/
macro "rsimp" : tactic => `(tactic| simp (disch := omega)
  [Function.update_of_ne, update_of_eq', copyR_of_mem, copyR_of_not_mem, fillR_of_mem,
    fillR_of_not_mem, writeBits_of_mem, writeBits_of_not_mem, R2_lo, R2_src, R2_hi, decide_eq_true,
    decide_eq_false, jOf_testBit, iOf_testBit, fOf_testBit, Nat.testBit_div_two,
    testBit_two_mul_mod, testBit_two_mul_mod_add_one, testBit_two_mul', AGate.op₁, AGate.op₂,
    AGate.cst,
    AGate.code])

/-- Finish a goal `bitR (i.testBit a) = bitR (i.testBit b)` with `a = b` by `omega`. -/
macro "bits_eq" : tactic => `(tactic| first | rfl | (congr 2; omega))

set_option hygiene false in
/-- A goal `∀ q < w, R (base + q) = bitR (N.testBit q)` for a field of an output index. -/
macro "fld" : tactic => `(tactic| (intro q hq; first
  | (interval_cases q <;> (try rsimp) <;> (try simp +decide [bitR]) <;> done)
  | ((try rsimp) <;> (try bits_eq) <;> done)
  | (rcases Nat.lt_or_ge (q + 1) m with h | h <;> (try rsimp) <;> (try bits_eq) <;> done)
  | (rcases Nat.eq_zero_or_pos q with h | h <;> (try rsimp) <;> (try bits_eq) <;> done)))

/-- A leaf consisting of field operations. -/
theorem leaf_ops {n m i : ℕ} {l : List FOp} {g : AGate} {T : ℕ}
    (hok : ∀ o ∈ l, o.Ok rP rQ rC (regs n m)) (hT : (l.map (FOp.time (regs n m))).sum ≤ T)
    (hdesc : DescOK (3 * m + 5) g (FOp.evalList (regs n m) l (R2 m i))) :
    Runs (ops l) ⟨R2 m i, regs n m⟩
      (fun st => st.I = regs n m ∧ DescOK (3 * m + 5) g st.R) T :=
  (ops_spec n m _ l hok).mono_time hT |>.mono_post fun _ h => h ▸ ⟨rfl, hdesc⟩

/-! ## The leaves of the dispatch -/

/-- Write the type code. -/
abbrev code (v : ℝ) : FOp := .set rZ v

/-- The gate `const 0`. -/
def leafC0 : Stmt := ops [code 1]

/-- The postcondition of a leaf: index registers restored, description of gate `i` written. -/
def LeafPost (n m i : ℕ) (st : St) : Prop :=
  st.I = regs n m ∧ DescOK (3 * m + 5) (gate m i) st.R

/-- The bound on the running time of a leaf. -/
def leafTime (m : ℕ) : ℕ := 2000 * (m + 1) ^ 3

theorem leafC0_spec (n m i : ℕ) (hg : gate m i = .const 0) :
    Runs leafC0 ⟨R2 m i, regs n m⟩ (LeafPost n m i) 1 := by
  unfold LeafPost; rw [hg]
  refine leaf_ops (by simp [FOp.Ok] <;> omega) (by simp [FOp.time]) (descOK_of ?_ ?_ ?_ ?_)
  · rsimp
  · intro q hq; rsimp
  · intro q hq; rsimp
  · rsimp

/-- Final gate `kind 4`: `mul (fin 2) (fin 3)`. -/
def leafF4 : Stmt :=
  ops [code 4, .set rO1T1 1, .set rO1K1 1, .set rO2T1 1, .set rO2K0 1, .set rO2K1 1]

theorem leafF4_spec (n m i : ℕ) (htag : tagOf m i = 2) (hk : kindOf i = 4) :
    Runs leafF4 ⟨R2 m i, regs n m⟩ (LeafPost n m i) 6 := by
  have hg : gate m i = .arith .mul (fin m 2) (fin m 3) := by simp [gate, htag, hk]
  unfold LeafPost; rw [hg]
  have h2m : 0 < 2 ^ m := Nat.two_pow_pos m
  refine leaf_ops (by simp [FOp.Ok] <;> omega) (by simp [FOp.time]) (descOK_of ?_ ?_ ?_ ?_)
  · rsimp
  · refine bits_idx (by norm_num) h2m h2m h2m ?_ ?_ ?_ ?_ ?_ <;> fld
  · refine bits_idx (by norm_num) h2m h2m h2m ?_ ?_ ?_ ?_ ?_ <;> fld
  · rsimp

/-- Final gate `kind 3`: `sign (fin 1)`. -/
def leafF3 : Stmt := ops [code 6, .set rO1T1 1, .set rONE 1]

theorem leafF3_spec (n m i : ℕ) (htag : tagOf m i = 2) (hk : kindOf i = 3) :
    Runs leafF3 ⟨R2 m i, regs n m⟩ (LeafPost n m i) 3 := by
  have hg : gate m i = .sign (fin m 1) := by simp [gate, htag, hk]
  unfold LeafPost; rw [hg]
  have h2m : 0 < 2 ^ m := Nat.two_pow_pos m
  refine leaf_ops (by simp [FOp.Ok] <;> omega) (by simp [FOp.time]) (descOK_of ?_ ?_ ?_ ?_)
  · rsimp
  · refine bits_idx (by norm_num) h2m h2m h2m ?_ ?_ ?_ ?_ ?_ <;> fld
  · intro q hq; rsimp
  · rsimp

/-- Final gate `kind 2`: `sign (fin 0)`. -/
def leafF2 : Stmt := ops [code 6, .set rO1T1 1]

theorem leafF2_spec (n m i : ℕ) (htag : tagOf m i = 2) (hk : kindOf i = 2) :
    Runs leafF2 ⟨R2 m i, regs n m⟩ (LeafPost n m i) 2 := by
  have hg : gate m i = .sign (fin m 0) := by simp [gate, htag, hk]
  unfold LeafPost; rw [hg]
  have h2m : 0 < 2 ^ m := Nat.two_pow_pos m
  refine leaf_ops (by simp [FOp.Ok] <;> omega) (by simp [FOp.time]) (descOK_of ?_ ?_ ?_ ?_)
  · rsimp
  · refine bits_idx (by norm_num) h2m h2m h2m ?_ ?_ ?_ ?_ ?_ <;> fld
  · intro q hq; rsimp
  · rsimp

/-- Final gate `kind 1`: `sub Y root`. -/
def leafF1 : Stmt := ops [code 3, .fill rO1I rM 1, .set rONE 1, .fill rO2I rM 1, .set rO2T0 1]

theorem leafF1_spec (n m i : ℕ) (htag : tagOf m i = 2) (hk : kindOf i = 1) :
    Runs leafF1 ⟨R2 m i, regs n m⟩ (LeafPost n m i) (100 * m + 100) := by
  have hg : gate m i = .arith .sub (yIdx m) (root m) := by simp [gate, htag, hk]
  unfold LeafPost; rw [hg]
  have h2m : 0 < 2 ^ m := Nat.two_pow_pos m
  refine leaf_ops (by simp [FOp.Ok] <;> omega) (by simp [FOp.time]; omega) (descOK_of ?_ ?_ ?_ ?_)
  · rsimp
  · refine bits_idx (by norm_num) h2m (by omega) h2m ?_ ?_ ?_ ?_ ?_ <;> fld
  · refine bits_idx (by norm_num) h2m (by omega) h2m ?_ ?_ ?_ ?_ ?_ <;> fld
  · rsimp

/-- Final gate `kind 0`: `sub root Y`. -/
def leafF0 : Stmt := ops [code 3, .fill rO1I rM 1, .set rO1T0 1, .fill rO2I rM 1, .set rO2K0 1]

theorem leafF0_spec (n m i : ℕ) (htag : tagOf m i = 2) (hk : kindOf i = 0) :
    Runs leafF0 ⟨R2 m i, regs n m⟩ (LeafPost n m i) (100 * m + 100) := by
  have hg : gate m i = .arith .sub (root m) (yIdx m) := by simp [gate, htag, hk]
  unfold LeafPost; rw [hg]
  have h2m : 0 < 2 ^ m := Nat.two_pow_pos m
  refine leaf_ops (by simp [FOp.Ok] <;> omega) (by simp [FOp.time]; omega) (descOK_of ?_ ?_ ?_ ?_)
  · rsimp
  · refine bits_idx (by norm_num) h2m (by omega) h2m ?_ ?_ ?_ ?_ ?_ <;> fld
  · refine bits_idx (by norm_num) h2m (by omega) h2m ?_ ?_ ?_ ?_ ?_ <;> fld
  · rsimp

/-- Tree gate, level `L` even (leaf of the tree): `add (P(p, 2^m-1, 2^m-1)) 0`. -/
def leafTL : Stmt := ops [code 2, .copy rSJ rO1F rM, .fill rO1J rM2 1, .set rO1K1 1]

theorem leafTL_spec (n m i : ℕ) (htag : tagOf m i = 1) (hL : (iOf m i).testBit 0 = false) :
    Runs leafTL ⟨R2 m i, regs n m⟩ (LeafPost n m i) (200 * m + 200) := by
  have hg : gate m i = .arith .add (idx m 0 (jOf m i) (2 ^ m - 1) (2 ^ m - 1) 2) 0 := by
    simp [gate, htag, hL]
  unfold LeafPost; rw [hg]
  have h2m : 0 < 2 ^ m := Nat.two_pow_pos m
  refine leaf_ops (by simp [FOp.Ok] <;> omega) (by simp [FOp.time]; omega) (descOK_of ?_ ?_ ?_ ?_)
  · rsimp
  · refine bits_idx (by norm_num) (by omega) (by omega) (jOf_lt m i) ?_ ?_ ?_ ?_ ?_ <;> fld
  · intro q hq; rsimp
  · rsimp

/-- Tree gate, level `L` odd: `add T(L/2, 2p+1) T(L/2, 2p)`. -/
def leafTN : Stmt :=
  ops [code 2, .copy rSI1 rO1I rM1, .copy rSJ rO1J1 rM1, .set rO1J 1, .set rO1T0 1,
    .copy rSI1 rO2I rM1, .copy rSJ rO2J1 rM1, .set rO2T0 1]

theorem leafTN_spec (n m i : ℕ) (hm : 1 ≤ m) (htag : tagOf m i = 1)
    (hL : (iOf m i).testBit 0 = true) :
    Runs leafTN ⟨R2 m i, regs n m⟩ (LeafPost n m i) (1000 * m + 1000) := by
  have hg : gate m i = .arith .add (idx m 1 0 (iOf m i / 2) (2 * jOf m i % 2 ^ m + 1) 0)
      (idx m 1 0 (iOf m i / 2) (2 * jOf m i % 2 ^ m) 0) := by
    simp [gate, htag, hL]
  unfold LeafPost; rw [hg]
  have h2m : 0 < 2 ^ m := Nat.two_pow_pos m
  have hI := iOf_lt m i
  refine leaf_ops (by simp [FOp.Ok] <;> omega) (by simp [FOp.time]; omega) (descOK_of ?_ ?_ ?_ ?_)
  · rsimp
  · refine bits_idx (by norm_num) (two_mul_mod_add_one_lt hm _) (by omega) h2m
      ?_ ?_ ?_ ?_ ?_ <;> fld
  · refine bits_idx (by norm_num) (Nat.mod_lt _ h2m) (by omega) h2m ?_ ?_ ?_ ?_ ?_ <;> fld
  · rsimp

/-- Product gate, `I` odd: `mul P(F, I/2, J) A(F, I/2, J)`. -/
def leafPM : Stmt :=
  ops [code 4, .copy rSF rO1F rM, .copy rSI1 rO1I rM1, .copy rSJ rO1J rM, .set rO1K1 1,
    .copy rSF rO2F rM, .copy rSI1 rO2I rM1, .copy rSJ rO2J rM]

theorem leafPM_spec (n m i : ℕ) (htag : tagOf m i = 0) (hk : kindOf i = 2)
    (hI0 : (iOf m i).testBit 0 = true) :
    Runs leafPM ⟨R2 m i, regs n m⟩ (LeafPost n m i) (1000 * m + 1000) := by
  have hg : gate m i = .arith .mul (idx m 0 (fOf m i) (iOf m i / 2) (jOf m i) 2)
      (idx m 0 (fOf m i) (iOf m i / 2) (jOf m i) 0) := by
    simp [gate, htag, hk, hI0]
  unfold LeafPost; rw [hg]
  have hI := iOf_lt m i
  refine leaf_ops (by simp [FOp.Ok] <;> omega) (by simp [FOp.time]; omega) (descOK_of ?_ ?_ ?_ ?_)
  · rsimp
  · refine bits_idx (by norm_num) (jOf_lt m i) (by omega) (fOf_lt m i) ?_ ?_ ?_ ?_ ?_ <;> fld
  · refine bits_idx (by norm_num) (jOf_lt m i) (by omega) (fOf_lt m i) ?_ ?_ ?_ ?_ ?_ <;> fld
  · rsimp

/-! ## The three loops -/

/-- A `forScan` over a field of length `m` with the standard scratch registers. -/
abbrev scan (a b : ℕ) (body : Stmt) : Stmt := forScan a b rM rP rQ rC rZ body

theorem scan_spec {n m : ℕ} {R : ℕ → ℝ} {a b : ℕ} {body : Stmt} (Inv : ℕ → (ℕ → ℝ) → Prop)
    (T : ℕ) (ha : a ≠ rP ∧ a ≠ rQ ∧ a ≠ rC) (hb : b ≠ rP ∧ b ≠ rQ ∧ b ≠ rC)
    (hbody : ∀ j < m, ∀ R', Inv j R' →
      Runs body ⟨R', scanIdx (regs n m) a b rP rQ rC j⟩
        (fun st' => st'.I = scanIdx (regs n m) a b rP rQ rC j ∧ Inv (j + 1) st'.R) T)
    (h0 : Inv 0 R) :
    Runs (scan a b body) ⟨R, regs n m⟩ (fun st' => st'.I = regs n m ∧ Inv m st'.R)
      (6 * regs n m a + 6 * regs n m b + m * (T + 14) + 6) := by
  have := forScan_spec (st := ⟨R, regs n m⟩) (len := rM) (z := rZ) Inv T (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ha hb (by decide) (regs_P n m) (regs_Q n m)
    (regs_C n m) (regs_Z n m) (by simpa using hbody) h0
  simpa using this

/-- `R[SCR] := F` at the highest one of `J` (scanning `J` and `F` in parallel). -/
def lookup : Stmt := scan rSJ rSF (Stmt.unless (.zero rP) (.op (.copy rSCR rQ)))

theorem lookup_spec (n m : ℕ) (R : ℕ → ℝ) (F J : ℕ)
    (hJ : ∀ j < m, R (6 * m + 15 + j) = bitR (J.testBit j))
    (hF : ∀ j < m, R (8 * m + 15 + j) = bitR (F.testBit j)) (hS : R (9 * m + 17) = 0) :
    Runs lookup ⟨R, regs n m⟩
      (· = ⟨Function.update R (9 * m + 17) (bitR (look m F J)), regs n m⟩) (200 * m + 200) := by
  have := scan_spec (n := n) (m := m) (R := R) (a := rSJ) (b := rSF)
    (body := Stmt.unless (.zero rP) (.op (.copy rSCR rQ)))
    (fun j R' => R' = Function.update R (9 * m + 17) (bitR (look j F J))) 3
    (by decide) (by decide) ?_ (by simp [look, ← hS])
  · refine (this.mono_time (by simp; omega)).mono_post ?_
    rintro ⟨R', I'⟩ ⟨hI', hR'⟩
    simp only at hI' hR'
    subst hI' hR'
    rfl
  · intro j hj R' hR'
    subst hR'
    have hJj := hJ j hj
    refine Spec.unless (fun hc => ⟨rfl, ?_⟩) (fun hc => Spec.copy ⟨rfl, ?_⟩ le_rfl)
    · simp only [Cond.holds_zero, scanIdx_p, regs_SJ] at hc
      rw [Function.update_of_ne (by omega), hJj, bitR_eq_zero_iff] at hc
      simp [look, hc]
    · simp only [Cond.holds_zero, scanIdx_p, regs_SJ] at hc
      rw [Function.update_of_ne (by omega), hJj, bitR_eq_zero_iff] at hc
      simp only [Bool.not_eq_false] at hc
      have e1 : scanIdx (regs n m) rSJ rSF rP rQ rC j rSCR = 9 * m + 17 := by simp [scanIdx]
      have e2 : scanIdx (regs n m) rSJ rSF rP rQ rC j rQ = 8 * m + 15 + j := by simp [scanIdx]
      dsimp only
      rw [e1, e2]
      simp only [Function.update_of_ne (show 8 * m + 15 + j ≠ 9 * m + 17 by omega), hF j hj,
        Function.update_idem]
      simp [look, hc]

/-- `R[CST] := sgn m F` (scanning `F`). -/
def signScan : Stmt :=
  .seq (.op (.const rCST 1)) (scan rSF rSF (Stmt.ifThen (.zero rP) (.op (.arith .sub rCST rSCR rCST))))

theorem signScan_spec (n m : ℕ) (R : ℕ → ℝ) (F : ℕ)
    (hF : ∀ j < m, R (8 * m + 15 + j) = bitR (F.testBit j)) (hS : R (9 * m + 17) = 0) :
    Runs signScan ⟨R, regs n m⟩
      (· = ⟨Function.update R (6 * m + 11) (sgn m F), regs n m⟩) (200 * m + 200) := by
  have := scan_spec (n := n) (m := m) (R := Function.update R (6 * m + 11) 1) (a := rSF)
    (b := rSF) (body := Stmt.ifThen (.zero rP) (.op (.arith .sub rCST rSCR rCST)))
    (fun j R' => R' = Function.update R (6 * m + 11) (sgn j F)) 3
    (by decide) (by decide) ?_ (by simp [sgn])
  · refine (Spec.seq_op (st' := ⟨Function.update R (regs n m rCST) 1, regs n m⟩) rfl
      (by rw [regs_CST]; exact this)).mono_time (by simp; omega) |>.mono_post ?_
    rintro ⟨R', I'⟩ ⟨hI', hR'⟩
    simp only at hI' hR'
    subst hI' hR'
    rfl
  · intro j hj R' hR'
    subst hR'
    have hFj := hF j hj
    refine Spec.ifThen (fun hc => Spec.sub ⟨rfl, ?_⟩ le_rfl) (fun hc => ⟨rfl, ?_⟩)
    · simp only [Cond.holds_zero, scanIdx_p, regs_SF] at hc
      rw [Function.update_of_ne (by omega), hFj, bitR_eq_zero_iff] at hc
      have e1 : scanIdx (regs n m) rSF rSF rP rQ rC j rCST = 6 * m + 11 := by simp [scanIdx]
      have e2 : scanIdx (regs n m) rSF rSF rP rQ rC j rSCR = 9 * m + 17 := by simp [scanIdx]
      dsimp only
      rw [e1, e2]
      simp only [Function.update_of_ne (show 9 * m + 17 ≠ 6 * m + 11 by omega), hS,
        Function.update_self, Function.update_idem]
      simp [sgn, hc]
    · simp only [Cond.holds_zero, scanIdx_p, regs_SF] at hc
      rw [Function.update_of_ne (by omega), hFj, bitR_eq_zero_iff] at hc
      simp only [Bool.not_eq_false] at hc
      simp [sgn, hc]

/-- Add `m` to the binary number in the `op₁` field. -/
def innerM : Stmt :=
  .seq (.loop (.idxEq rC2 rM) (.seq (binInc rONE rBQ rZ) (.op (.inc rC2)))) (clearIdx rC2 rZ)

theorem innerM_spec {I : ℕ → ℕ} (m : ℕ) (R : ℕ → ℝ) (v : ℕ) (hC2 : I rC2 = 0)
    (hBQ : I rBQ = 0) (hZ : I rZ = 0) (hONE : I rONE = 1) (hM : I rM = m)
    (hv : v + m < 2 ^ (3 * m + 5)) :
    Runs innerM ⟨writeBits R 1 (3 * m + 5) v, I⟩
      (· = ⟨writeBits R 1 (3 * m + 5) (v + m), I⟩) (m * (30 * m + 60) + 3 * m + 2) := by
  have hloop : Runs (.loop (.idxEq rC2 rM) (.seq (binInc rONE rBQ rZ) (.op (.inc rC2))))
      ⟨writeBits R 1 (3 * m + 5) v, I⟩
      (· = ⟨writeBits R 1 (3 * m + 5) (v + m), Function.update I rC2 m⟩)
      (m * ((6 + 7 * (3 * m + 5) + 4 + 1) + 2) + 1) := by
    refine Spec.loop (fun r st => st = ⟨writeBits R 1 (3 * m + 5) (v + r),
      Function.update I rC2 r⟩) m ?_ ?_ ?_ (by simp only [Nat.add_zero]; rw [← hC2, Function.update_eq_self])
    · rintro st rfl
      simp [Function.update_of_ne (show rM ≠ rC2 by decide), hM]
    · rintro r hr st rfl
      simp [Function.update_of_ne (show rM ≠ rC2 by decide), hM]
      omega
    · rintro r hr st rfl
      have hb := binInc_spec (st := ⟨writeBits R 1 (3 * m + 5) (v + r), Function.update I rC2 r⟩)
        (base := rONE) (q := rBQ) (z := rZ) (w := 3 * m + 5) (v := v + r) (by decide) (by decide)
        (by simp [Function.update_of_ne (show rBQ ≠ rC2 by decide), hBQ])
        (by simp [Function.update_of_ne (show rZ ≠ rC2 by decide), hZ]) ?_ (by omega)
      · refine Spec.seq_eq hb (Spec.inc ?_ le_rfl) |>.mono_time ?_
        · simp only [Function.update_of_ne (show rONE ≠ rC2 by decide), hONE,
            writeBits_writeBits, Function.update_self, Function.update_idem]
          rfl
        · simp [Function.update_of_ne (show rONE ≠ rC2 by decide), hONE]
      · intro j hj
        simp only [Function.update_of_ne (show rONE ≠ rC2 by decide), hONE]
        rw [writeBits_of_mem (by omega)]
        congr 2; omega
  refine Spec.seq_eq hloop (clearIdx_spec (by decide) (by simp [hZ])) |>.mono_time ?_ |>.mono_post ?_
  · simp only [Function.update_self]
    nlinarith
  · rintro st rfl
    simp [← hC2]

/-- Write `pc(I) · m + pc(J)` in binary into the `op₁` field (assumed `0`). -/
def countUp : Stmt :=
  .seq (scan rSI rSI (Stmt.unless (.zero rP) innerM))
    (scan rSJ rSJ (Stmt.unless (.zero rP) (binInc rONE rBQ rZ)))

theorem countUp_spec (n m : ℕ) (hm : 1 ≤ m) (R : ℕ → ℝ) (I J : ℕ)
    (h0 : ∀ q < 3 * m + 5, R (1 + q) = 0)
    (hI : ∀ j < m, R (7 * m + 15 + j) = bitR (I.testBit j))
    (hJ : ∀ j < m, R (6 * m + 15 + j) = bitR (J.testBit j)) :
    Runs countUp ⟨R, regs n m⟩
      (· = ⟨writeBits R 1 (3 * m + 5) (pc m I * m + pc m J), regs n m⟩)
      (300 * (m + 1) ^ 3) := by
  have hmm : m * m + m < 2 ^ (3 * m + 5) := by
    have h1 : m < 2 ^ m := Nat.lt_two_pow_self
    have h2 : 2 ^ m * 2 ^ m ≤ 2 ^ (3 * m + 5) := by
      rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : m * m < 2 ^ m * 2 ^ m := Nat.mul_lt_mul'' h1 h1
    have h4 : m + 1 ≤ 2 ^ m := h1
    nlinarith
  have hpcI : ∀ j, pc j I ≤ j := fun j => pc_le j I
  have hb1 : ∀ j < m, ∀ R', R' = writeBits R 1 (3 * m + 5) (pc j I * m) →
      Runs (Stmt.unless (.zero rP) innerM) ⟨R', scanIdx (regs n m) rSI rSI rP rQ rC j⟩
        (fun st' => st'.I = scanIdx (regs n m) rSI rSI rP rQ rC j ∧
          st'.R = writeBits R 1 (3 * m + 5) (pc (j + 1) I * m))
        (m * (30 * m + 60) + 3 * m + 2 + 2) := by
    intro j hj R' hR'
    subst hR'
    have hIj := hI j hj
    refine Spec.unless (fun hc => ⟨rfl, ?_⟩) (fun hc => ?_)
    · simp only [Cond.holds_zero, scanIdx_p, regs_SI] at hc
      rw [writeBits_of_not_mem (by omega), hIj, bitR_eq_zero_iff] at hc
      simp [pc, hc]
    · simp only [Cond.holds_zero, scanIdx_p, regs_SI] at hc
      rw [writeBits_of_not_mem (by omega), hIj, bitR_eq_zero_iff] at hc
      simp only [Bool.not_eq_false] at hc
      have hpj := hpcI j
      refine (innerM_spec (I := scanIdx (regs n m) rSI rSI rP rQ rC j) m R (pc j I * m)
        (by simp [scanIdx]) (by simp [scanIdx]) (by simp [scanIdx]) (by simp [scanIdx])
        (by simp [scanIdx]) ?_).mono_post ?_
      · have : (pc j I + 1) * m ≤ m * m := Nat.mul_le_mul_right _ (by omega)
        nlinarith
      · rintro st rfl
        refine ⟨rfl, ?_⟩
        simp only [pc, hc, if_true]
        congr 1
        ring
  have s1 := scan_spec (n := n) (m := m) (R := R) (a := rSI) (b := rSI)
    (body := Stmt.unless (.zero rP) innerM)
    (fun j R' => R' = writeBits R 1 (3 * m + 5) (pc j I * m))
    (m * (30 * m + 60) + 3 * m + 2 + 2) (by decide) (by decide) hb1
    (by simp [pc, writeBits_zero_of h0])
  have hb2 : ∀ j < m, ∀ R', R' = writeBits R 1 (3 * m + 5) (pc m I * m + pc j J) →
      Runs (Stmt.unless (.zero rP) (binInc rONE rBQ rZ))
        ⟨R', scanIdx (regs n m) rSJ rSJ rP rQ rC j⟩
        (fun st' => st'.I = scanIdx (regs n m) rSJ rSJ rP rQ rC j ∧
          st'.R = writeBits R 1 (3 * m + 5) (pc m I * m + pc (j + 1) J))
        (6 + 7 * (3 * m + 5) + 4 + 2) := by
    intro j hj R' hR'
    subst hR'
    have hJj := hJ j hj
    refine Spec.unless (fun hc => ⟨rfl, ?_⟩) (fun hc => ?_)
    · simp only [Cond.holds_zero, scanIdx_p, regs_SJ] at hc
      rw [writeBits_of_not_mem (by omega), hJj, bitR_eq_zero_iff] at hc
      simp [pc, hc]
    · simp only [Cond.holds_zero, scanIdx_p, regs_SJ] at hc
      rw [writeBits_of_not_mem (by omega), hJj, bitR_eq_zero_iff] at hc
      simp only [Bool.not_eq_false] at hc
      have hpI := pc_le m I
      have hpJ := pc_le j J
      have hb := binInc_spec
        (st := ⟨writeBits R 1 (3 * m + 5) (pc m I * m + pc j J),
          scanIdx (regs n m) rSJ rSJ rP rQ rC j⟩)
        (base := rONE) (q := rBQ) (z := rZ) (w := 3 * m + 5) (v := pc m I * m + pc j J)
        (by decide) (by decide) (by simp [scanIdx]) (by simp [scanIdx]) ?_ ?_
      · have e : scanIdx (regs n m) rSJ rSJ rP rQ rC j rONE = 1 := by simp [scanIdx]
        refine (hb.mono_time ?_).mono_post ?_
        · dsimp only; rw [e]
        · rintro st rfl
          refine ⟨rfl, ?_⟩
          dsimp only
          rw [e, writeBits_writeBits]
          simp [pc, hc, Nat.add_assoc]
      · intro q hq
        simp only [scanIdx]
        simp only [show rONE ≠ rP by decide, show rONE ≠ rQ by decide,
          show rONE ≠ rC by decide, if_false, regs_ONE]
        rw [writeBits_of_mem (by omega)]
        congr 2; omega
      · have : pc m I * m ≤ m * m := Nat.mul_le_mul_right _ hpI
        omega
  have s2 := scan_spec (n := n) (m := m) (R := writeBits R 1 (3 * m + 5) (pc m I * m))
    (a := rSJ) (b := rSJ) (body := Stmt.unless (.zero rP) (binInc rONE rBQ rZ))
    (fun j R' => R' = writeBits R 1 (3 * m + 5) (pc m I * m + pc j J))
    (6 + 7 * (3 * m + 5) + 4 + 2) (by decide) (by decide) hb2 (by simp [pc])
  refine (s1.seq (T₂ := 6 * regs n m rSJ + 6 * regs n m rSJ +
    m * (6 + 7 * (3 * m + 5) + 4 + 2 + 14) + 6) fun ⟨R', I'⟩ ⟨hI', hR'⟩ => ?_).mono_time ?_
  · simp only at hI' hR'
    subst hI' hR'
    refine s2.mono_post ?_
    rintro ⟨R'', I''⟩ ⟨hI'', hR''⟩
    simp only at hI'' hR''
    subst hI'' hR''
    rfl
  · simp only [regs_SI, regs_SJ]
    nlinarith [sq_nonneg m]

/-! ## The leaves with loops -/

/-- Input gate: `input (pc(I) · m + pc(J))`. -/
def leafIn : Stmt := countUp

theorem leafIn_spec (n m i : ℕ) (hm : 1 ≤ m) (htag : tagOf m i = 0) (hk : kindOf i = 1) :
    Runs leafIn ⟨R2 m i, regs n m⟩ (LeafPost n m i) (300 * (m + 1) ^ 3) := by
  have hg : gate m i = .input (pc m (iOf m i) * m + pc m (jOf m i)) := by
    simp [gate, htag, hk]
  refine (countUp_spec n m hm (R2 m i) (iOf m i) (jOf m i) ?_ ?_ ?_).mono_post ?_
  · intro q hq; rsimp
  · intro j hj; rsimp; bits_eq
  · intro j hj; rsimp; bits_eq
  · rintro st rfl
    refine ⟨rfl, ?_⟩
    rw [hg]
    refine descOK_of ?_ ?_ ?_ ?_
    · rsimp
    · intro q hq; rsimp
    · intro q hq; rsimp
    · rsimp

/-- Product gate, `I` even: `const (sgn m F)`. -/
def leafP0 : Stmt := .seq (ops [code 1]) signScan

theorem leafP0_spec (n m i : ℕ) (htag : tagOf m i = 0) (hk : kindOf i = 2)
    (hI0 : (iOf m i).testBit 0 = false) :
    Runs leafP0 ⟨R2 m i, regs n m⟩ (LeafPost n m i) (200 * m + 202) := by
  have hg : gate m i = .const (sgn m (fOf m i)) := by simp [gate, htag, hk, hI0]
  have s1 := ops_spec n m (R2 m i) [code 1] (by simp [FOp.Ok])
  have s2 := signScan_spec n m (FOp.evalList (regs n m) [code 1] (R2 m i)) (fOf m i)
    (by intro j hj; rsimp; bits_eq) (by rsimp)
  refine (s1.seq_eq s2).mono_time (by simp [FOp.time]; omega) |>.mono_post ?_
  rintro st rfl
  refine ⟨rfl, ?_⟩
  rw [hg]
  refine descOK_of ?_ ?_ ?_ ?_
  · rsimp
  · intro q hq; rsimp
  · intro q hq; rsimp
  · rsimp

/-- Row-sum gate, `J` odd: `add A(F, I, J/2) ([look] In(F, I, J/2))`. -/
def leafAA : Stmt :=
  .seqs [ops [code 2, .copy rSI rO1I rM2, .copy rSJ1 rO1J rM1], lookup,
    Stmt.unless (.zero rSCR) (ops [.copy rSI rO2I rM2, .copy rSJ1 rO2J rM1, .set rO2K0 1])]

theorem leafAA_spec (n m i : ℕ) (htag : tagOf m i = 0) (hk : kindOf i = 0)
    (hJ0 : (jOf m i).testBit 0 = true) :
    Runs leafAA ⟨R2 m i, regs n m⟩ (LeafPost n m i) (2000 * m + 2000) := by
  have hg : gate m i = .arith .add (idx m 0 (fOf m i) (iOf m i) (jOf m i / 2) 0)
      (if look m (fOf m i) (jOf m i) then idx m 0 (fOf m i) (iOf m i) (jOf m i / 2) 1
        else 0) := by
    simp [gate, htag, hk, hJ0]
  have hJ := jOf_lt m i
  have hI := iOf_lt m i
  have hF := fOf_lt m i
  have s1 := ops_spec n m (R2 m i) [code 2, .copy rSI rO1I rM2, .copy rSJ1 rO1J rM1]
    (by simp [FOp.Ok] <;> omega)
  have s2 := lookup_spec n m
    (FOp.evalList (regs n m) [code 2, .copy rSI rO1I rM2, .copy rSJ1 rO1J rM1] (R2 m i))
    (fOf m i) (jOf m i) (by intro j hj; rsimp; bits_eq) (by intro j hj; rsimp; bits_eq)
    (by rsimp)
  have s3 : Runs (Stmt.seqs [Stmt.unless (.zero rSCR)
      (ops [.copy rSI rO2I rM2, .copy rSJ1 rO2J rM1, .set rO2K0 1])])
      ⟨Function.update
        (FOp.evalList (regs n m) [code 2, .copy rSI rO1I rM2, .copy rSJ1 rO1J rM1] (R2 m i))
        (9 * m + 17) (bitR (look m (fOf m i) (jOf m i))), regs n m⟩
      (LeafPost n m i) (1000 * m + 998 + 2 + 0) := by
    refine Spec.seq (Q₁ := LeafPost n m i) ?_ (fun st h => Spec.skip h)
    refine Spec.unless (T := 1000 * m + 998) (fun hc => ?_) (fun hc => ?_)
    · -- no input term
      simp only [Cond.holds_zero, regs_SCR, Function.update_self, bitR_eq_zero_iff] at hc
      refine ⟨rfl, ?_⟩
      rw [hg, hc, if_neg (by simp)]
      refine descOK_of ?_ ?_ ?_ ?_
      · rsimp
      · refine bits_idx (by norm_num) (by omega) hI hF ?_ ?_ ?_ ?_ ?_ <;> fld
      · intro q hq; rsimp
      · rsimp
    · simp only [Cond.holds_zero, regs_SCR, Function.update_self, bitR_eq_zero_iff,
        Bool.not_eq_false] at hc
      refine (ops_spec n m _ _ (by simp [FOp.Ok] <;> omega)).mono_time ?_ |>.mono_post ?_
      · simp [FOp.time]; omega
      rintro st rfl
      refine ⟨rfl, ?_⟩
      rw [hg, hc, if_pos rfl]
      refine descOK_of ?_ ?_ ?_ ?_
      · rsimp
      · refine bits_idx (by norm_num) (by omega) hI hF ?_ ?_ ?_ ?_ ?_ <;> fld
      · refine bits_idx (by norm_num) (by omega) hI hF ?_ ?_ ?_ ?_ ?_ <;> fld
      · rsimp
  refine (s1.seq_eq (s2.seq_eq s3)).mono_time ?_
  simp [FOp.time]
  omega

/-! ## The dispatch -/

def leafA : Stmt := .ite (.zero rSJ) leafC0 leafAA
def leafP : Stmt := .ite (.zero rSI) leafP0 leafPM
def leafT : Stmt := .ite (.zero rSI) leafTL leafTN

/-- Dispatch on the kind bits for `tag = 0`. -/
def block : Stmt :=
  .ite (.zero rSK2)
    (.ite (.zero rSK1) (.ite (.zero rSRC) leafA leafIn) (.ite (.zero rSRC) leafP leafC0))
    leafC0

/-- Dispatch on the kind bits for `tag = 2`. -/
def final : Stmt :=
  .ite (.zero rSK2)
    (.ite (.zero rSK1) (.ite (.zero rSRC) leafF0 leafF1) (.ite (.zero rSRC) leafF2 leafF3))
    (.ite (.zero rSK1) (.ite (.zero rSRC) leafF4 leafC0) leafC0)

/-- Dispatch on the tag bits. -/
def dispatch : Stmt :=
  .ite (.zero rST1) (.ite (.zero rST0) block leafT) (.ite (.zero rST0) final leafC0)

theorem cond_src {n m i k a : ℕ} (hk : k < 3 * m + 5) (ha : regs n m a = 6 * m + 12 + k) :
    (Cond.zero a).holds ⟨R2 m i, regs n m⟩ ↔ i.testBit k = false := by
  simp only [Cond.holds_zero, ha]
  rw [R2_src (by omega), show 6 * m + 12 + k - (6 * m + 12) = k by omega, bitR_eq_zero_iff]

theorem two_bits {t : ℕ} (ht : t < 4) :
    t = (if t.testBit 1 then 2 else 0) + (if t.testBit 0 then 1 else 0) := by
  interval_cases t <;> decide

theorem three_bits {t : ℕ} (ht : t < 8) :
    t = (if t.testBit 2 then 4 else 0) + (if t.testBit 1 then 2 else 0) +
      (if t.testBit 0 then 1 else 0) := by
  interval_cases t <;> decide

theorem leafTime_ge (m : ℕ) (hm : 1 ≤ m) : 2000 * m + 2000 + 20 ≤ leafTime m := by
  unfold leafTime
  nlinarith [sq_nonneg m, sq_nonneg (m + 1)]

theorem leafTime_ge3 (m : ℕ) : 300 * (m + 1) ^ 3 + 20 ≤ leafTime m := by
  unfold leafTime; nlinarith [pow_pos (Nat.succ_pos m) 3]

theorem kind_eq (i : ℕ) : kindOf i = (if i.testBit 2 then 4 else 0) +
    (if i.testBit 1 then 2 else 0) + (if i.testBit 0 then 1 else 0) := by
  have h := three_bits (kindOf_lt i)
  simp only [kindOf_testBit, show decide (2 < 3) = true from rfl,
    show decide (1 < 3) = true from rfl, show decide (0 < 3) = true from rfl,
    Bool.true_and] at h
  exact h

theorem tag_eq {m i : ℕ} (hi : i < 2 ^ (3 * m + 5)) : tagOf m i =
    (if i.testBit (3 * m + 4) then 2 else 0) + (if i.testBit (3 * m + 3) then 1 else 0) := by
  have h := two_bits (tagOf_lt hi)
  simp only [tagOf_testBit] at h
  rw [h, show 3 + 3 * m + 1 = 3 * m + 4 by ring, show 3 + 3 * m + 0 = 3 * m + 3 by ring]

/-- Branch on a source bit. -/
theorem ite_src {n m i k a : ℕ} {s u : Stmt} {Q : St → Prop} {T : ℕ} (hk : k < 3 * m + 5)
    (ha : regs n m a = 6 * m + 12 + k)
    (h0 : i.testBit k = false → Runs s ⟨R2 m i, regs n m⟩ Q T)
    (h1 : i.testBit k = true → Runs u ⟨R2 m i, regs n m⟩ Q T) :
    Runs (.ite (.zero a) s u) ⟨R2 m i, regs n m⟩ Q (T + 2) :=
  Spec.ite (fun h => h0 ((cond_src hk ha).mp h))
    (fun h => h1 (by simpa [cond_src hk ha] using h))

theorem leafA_spec (n m i : ℕ) (hm : 1 ≤ m) (htag : tagOf m i = 0) (hk : kindOf i = 0) :
    Runs leafA ⟨R2 m i, regs n m⟩ (LeafPost n m i) (leafTime m + 2) := by
  have hT := leafTime_ge m hm
  have hJ0 : (jOf m i).testBit 0 = i.testBit 3 := by
    rw [jOf_testBit]; simp only [decide_eq_true (show 0 < m by omega), Bool.true_and, Nat.add_zero]
  refine ite_src (k := 3) (by omega) (by simp) (fun h => ?_) (fun h => ?_)
  · exact (leafC0_spec n m i (by simp [gate, htag, hk, hJ0, h])).mono_time (by omega)
  · exact (leafAA_spec n m i htag hk (hJ0.trans h)).mono_time (by omega)

theorem leafP_spec (n m i : ℕ) (hm : 1 ≤ m) (htag : tagOf m i = 0) (hk : kindOf i = 2) :
    Runs leafP ⟨R2 m i, regs n m⟩ (LeafPost n m i) (leafTime m + 2) := by
  have hT := leafTime_ge m hm
  have hI0 : (iOf m i).testBit 0 = i.testBit (3 + m) := by
    rw [iOf_testBit]; simp only [decide_eq_true (show 0 < m by omega), Bool.true_and, Nat.add_zero]
  refine ite_src (k := 3 + m) (by omega) (by simp; ring) (fun h => ?_) (fun h => ?_)
  · exact (leafP0_spec n m i htag hk (hI0.trans h)).mono_time (by omega)
  · exact (leafPM_spec n m i htag hk (hI0.trans h)).mono_time (by omega)

theorem leafT_spec (n m i : ℕ) (hm : 1 ≤ m) (htag : tagOf m i = 1) :
    Runs leafT ⟨R2 m i, regs n m⟩ (LeafPost n m i) (leafTime m + 2) := by
  have hT := leafTime_ge m hm
  have hI0 : (iOf m i).testBit 0 = i.testBit (3 + m) := by
    rw [iOf_testBit]; simp only [decide_eq_true (show 0 < m by omega), Bool.true_and, Nat.add_zero]
  refine ite_src (k := 3 + m) (by omega) (by simp; ring) (fun h => ?_) (fun h => ?_)
  · exact (leafTL_spec n m i htag (hI0.trans h)).mono_time (by omega)
  · exact (leafTN_spec n m i hm htag (hI0.trans h)).mono_time (by omega)

theorem block_spec (n m i : ℕ) (hm : 1 ≤ m) (htag : tagOf m i = 0) :
    Runs block ⟨R2 m i, regs n m⟩ (LeafPost n m i) (leafTime m + 8) := by
  have hT := leafTime_ge m hm
  have hT3 := leafTime_ge3 m
  have hk := kind_eq i
  refine ite_src (k := 2) (by omega) (by simp) (fun h2 => ?_) (fun h2 => ?_)
  · refine ite_src (k := 1) (by omega) (by simp) (fun h1 => ?_) (fun h1 => ?_)
    · refine ite_src (k := 0) (by omega) (by simp) (fun h0 => ?_) (fun h0 => ?_)
      · exact leafA_spec n m i hm htag (by simp [hk, h0, h1, h2])
      · exact (leafIn_spec n m i hm htag (by simp [hk, h0, h1, h2])).mono_time (by omega)
    · refine ite_src (k := 0) (by omega) (by simp) (fun h0 => ?_) (fun h0 => ?_)
      · exact leafP_spec n m i hm htag (by simp [hk, h0, h1, h2])
      · refine (leafC0_spec n m i ?_).mono_time (by omega)
        have : kindOf i = 3 := by simp [hk, h0, h1, h2]
        simp [gate, htag, this]
  · refine (leafC0_spec n m i ?_).mono_time (by omega)
    have : 4 ≤ kindOf i := by rw [hk, h2]; simp only [if_true]; split_ifs <;> omega
    simp [gate, htag, show kindOf i ≠ 0 by omega, show kindOf i ≠ 1 by omega,
      show kindOf i ≠ 2 by omega]

theorem final_spec (n m i : ℕ) (hm : 1 ≤ m) (htag : tagOf m i = 2) :
    Runs final ⟨R2 m i, regs n m⟩ (LeafPost n m i) (leafTime m + 6) := by
  have hT := leafTime_ge m hm
  have hk := kind_eq i
  refine ite_src (k := 2) (by omega) (by simp) (fun h2 => ?_) (fun h2 => ?_)
  · refine ite_src (k := 1) (by omega) (by simp) (fun h1 => ?_) (fun h1 => ?_)
    · refine ite_src (k := 0) (by omega) (by simp) (fun h0 => ?_) (fun h0 => ?_)
      · exact (leafF0_spec n m i htag (by simp [hk, h0, h1, h2])).mono_time (by omega)
      · exact (leafF1_spec n m i htag (by simp [hk, h0, h1, h2])).mono_time (by omega)
    · refine ite_src (k := 0) (by omega) (by simp) (fun h0 => ?_) (fun h0 => ?_)
      · exact (leafF2_spec n m i htag (by simp [hk, h0, h1, h2])).mono_time (by omega)
      · exact (leafF3_spec n m i htag (by simp [hk, h0, h1, h2])).mono_time (by omega)
  · refine ite_src (k := 1) (by omega) (by simp) (fun h1 => ?_) (fun h1 => ?_)
    · refine ite_src (k := 0) (by omega) (by simp) (fun h0 => ?_) (fun h0 => ?_)
      · exact (leafF4_spec n m i htag (by simp [hk, h0, h1, h2])).mono_time (by omega)
      · refine (leafC0_spec n m i ?_).mono_time (by omega)
        have : kindOf i = 5 := by simp [hk, h0, h1, h2]
        simp [gate, htag, this]
    · refine (leafC0_spec n m i ?_).mono_time (by omega)
      have : 6 ≤ kindOf i := by rw [hk, h1, h2]; simp only [if_true]; split_ifs <;> omega
      simp [gate, htag, show kindOf i ≠ 0 by omega, show kindOf i ≠ 1 by omega,
        show kindOf i ≠ 2 by omega, show kindOf i ≠ 3 by omega, show kindOf i ≠ 4 by omega]

theorem dispatch_spec (n m i : ℕ) (hm : 1 ≤ m) (hi : i < 2 ^ (3 * m + 5)) :
    Runs dispatch ⟨R2 m i, regs n m⟩ (LeafPost n m i) (leafTime m + 12) := by
  have hT := leafTime_ge m hm
  have ht := tag_eq hi
  refine ite_src (k := 3 * m + 4) (by omega) (by simp; ring) (fun h1 => ?_) (fun h1 => ?_)
  · refine ite_src (k := 3 * m + 3) (by omega) (by simp; ring) (fun h0 => ?_) (fun h0 => ?_)
    · exact (block_spec n m i hm (by simp [ht, h0, h1])).mono_time (by omega)
    · exact (leafT_spec n m i hm (by simp [ht, h0, h1])).mono_time (by omega)
  · refine ite_src (k := 3 * m + 3) (by omega) (by simp; ring) (fun h0 => ?_) (fun h0 => ?_)
    · exact (final_spec n m i hm (by simp [ht, h0, h1])).mono_time (by omega)
    · refine (leafC0_spec n m i ?_).mono_time (by omega)
      have : tagOf m i = 3 := by simp [ht, h0, h1]
      simp [gate, this]

/-! ## The describer -/

/-- The describer program. -/
def descProg : Stmt :=
  .ite (.idxEq 1 rZ) (.seqs [.op (.const rZ 1), .halt true])
    (.seqs [setup, ops prepOps, dispatch, .halt true])

/-- The running time bound of the describer for `b = 3m + 5`. -/
def descTime (m : ℕ) : ℕ := leafTime m + 1000 * m + 1000

theorem descProg_spec (n m i : ℕ) (hm : 1 ≤ m) (hi : i < 2 ^ (3 * m + 5)) :
    Halts descProg (St.init [n, 3 * m + 5] (vecReg (bitsOf (3 * m + 5) i)))
      (fun st r => r = some true ∧ DescOK (3 * m + 5) (gate m i) st.R) (descTime m) := by
  refine (Spec.ite_neg (T := 300 + 160 * m + (150 * m + 300 + (leafTime m + 12 + (0 + 0))))
    (by simp [St.init]) ?_).mono_time ?_
  · refine (setup_spec n m (vecReg (bitsOf (3 * m + 5) i))).of_runs.seq_eq
      ((prep_spec n m i).of_runs.seq_eq ((dispatch_spec n m i hm hi).of_runs.seq fun st h => ?_))
    exact Spec.seq (Q₁ := fun _ => False) (Spec.halt ⟨rfl, h.2⟩) fun _ h' => h'.elim
  · unfold descTime
    omega

theorem descProg_spec0 (n i : ℕ) :
    Halts descProg (St.init [n, 0] (vecReg (bitsOf 0 i)))
      (fun st r => r = some true ∧ DescOK 0 (.const 0) st.R) 3 := by
  have h1 : Halts (Stmt.seqs [.op (.const rZ 1), .halt true])
      (St.init [n, 0] (vecReg (bitsOf 0 i)))
      (fun st r => r = some true ∧ DescOK 0 (.const 0) st.R) (1 + (0 + 0)) := by
    refine Spec.seq_op (st' := ⟨Function.update (vecReg (bitsOf 0 i)) 0 1,
      fun k => [n, 0].getD k 0⟩) rfl ?_
    refine Spec.seq (Q₁ := fun _ => False) (Spec.halt ⟨rfl, ?_⟩) (fun _ h' => h'.elim)
    intro k hk
    interval_cases k
    · simp [AGate.describe, AGate.code]
    · simp [AGate.describe, AGate.cst, vecReg]
  exact (Spec.ite_pos (by simp [St.init]) h1).mono_time (by norm_num)

end Ryser

end ClassSep
