import ClassSeparations.Machines.RyserMachine
import ClassSeparations.Machines.RyserEval
import ClassSeparations.Machines.ProgramComplex

/-!
# The Ryser circuit families (Lemma 4.6)

The circuit families over `ℝ` and `ℂ` (for inputs of length `n = m² + 1`, `m ≥ 1`: the Ryser
circuits; otherwise the one-gate circuit `const 0`), their describer machines, and their
properties as required by `PAR_R` and `PAR_C`.
-/

noncomputable section

open Classical MvPolynomial

namespace ClassSep

namespace Ryser

open Prog

/-! ## The input length -/

/-- `m` for inputs of length `n = m² + 1`. -/
def mOf (n : ℕ) : ℕ := Nat.sqrt (n - 1)

/-- The input length is `m² + 1` with `m ≥ 1`. -/
def Valid (n : ℕ) : Prop := 1 ≤ mOf n ∧ n = mOf n * mOf n + 1

theorem valid_iff (n : ℕ) : Valid n ↔ ∃ m, 1 ≤ m ∧ n = m * m + 1 := by
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨mOf n, h1, h2⟩
  · rintro ⟨m, hm, rfl⟩
    have : mOf (m * m + 1) = m := by simp [mOf, Nat.sqrt_eq]
    rw [Valid, this]
    exact ⟨hm, rfl⟩

theorem mOf_le (n : ℕ) : mOf n ≤ n := (Nat.sqrt_le_self _).trans (Nat.sub_le _ _)

/-! ## The families -/

/-- The circuit family ending with the final gate of kind `last`. -/
def family (last n : ℕ) : ACircuit := if Valid n then circ (mOf n) last else [.const 0]

/-- The index length. -/
def bLen (n : ℕ) : ℕ := if Valid n then 3 * mOf n + 5 else 0

/-- The describer machine. -/
def describer : Machine := descProg.toMachine

/-- The running time bound of the describer. -/
def pBound (n : ℕ) : ℕ := descTime n + 4

theorem descTime_mono {m n : ℕ} (h : m ≤ n) : descTime m ≤ descTime n := by
  unfold descTime leafTime
  have : (m + 1) ^ 3 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  omega

theorem fin_lt {m last : ℕ} (hl : last < 8) : fin m last < 2 ^ (3 * m + 5) :=
  idx_lt_two_pow hl (Nat.two_pow_pos m) (Nat.two_pow_pos m) (Nat.two_pow_pos m) (by norm_num)

theorem length_circ (m last : ℕ) : (circ m last).length = fin m last + 1 := by
  simp [circ]

theorem family_length {last : ℕ} (hl : last < 8) (n : ℕ) :
    (family last n).length ≤ 2 ^ bLen n := by
  unfold family bLen
  split_ifs
  · rw [length_circ]; exact fin_lt hl
  · simp

theorem mm_lt (m : ℕ) : m * m + m < 2 ^ (3 * m + 5) := by
  have h1 : m < 2 ^ m := Nat.lt_two_pow_self
  have h2 : 2 ^ m * 2 ^ m ≤ 2 ^ (3 * m + 5) := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : m * m < 2 ^ m * 2 ^ m := Nat.mul_lt_mul'' h1 h1
  have h4 : m + 1 ≤ 2 ^ m := h1
  nlinarith

theorem gate_input_le {m i t : ℕ} (h : gate m i = .input t) : t ≤ m * m + m := by
  unfold gate at h
  split_ifs at h <;> first | (simp only [reduceCtorEq] at h) | skip
  injection h with h
  subst h
  have := pc_le m (iOf m i)
  have := pc_le m (jOf m i)
  have : pc m (iOf m i) * m ≤ m * m := Nat.mul_le_mul_right _ (pc_le m (iOf m i))
  omega

theorem gate_ops_lt {m i : ℕ} (hm : 1 ≤ m) (hi : i < 2 ^ (3 * m + 5)) :
    (gate m i).op₁ < 2 ^ (3 * m + 5) ∧ (gate m i).op₂ < 2 ^ (3 * m + 5) := by
  have hv := gate_valid hm hi
  have hpos := Nat.two_pow_pos (3 * m + 5)
  rcases hg : gate m i with t | c | ⟨op, j, k⟩ | j <;> rw [hg] at hv
  · have := gate_input_le hg
    have := mm_lt m
    simp only [AGate.op₁, AGate.op₂]; omega
  · simp only [AGate.op₁, AGate.op₂]; omega
  · obtain ⟨-, hj, hk⟩ := hv
    simp only [AGate.op₁, AGate.op₂]; omega
  · have hj : j < i := hv
    simp only [AGate.op₁, AGate.op₂]; omega

theorem family_ops {last : ℕ} (hl : last < 8) (n : ℕ) :
    ∀ g ∈ family last n, g.op₁ < 2 ^ bLen n ∧ g.op₂ < 2 ^ bLen n := by
  intro g hg
  unfold family bLen at *
  split_ifs at hg ⊢ with hv
  · simp only [circ, List.mem_map, List.mem_range] at hg
    obtain ⟨i, hi, rfl⟩ := hg
    exact gate_ops_lt hv.1 (lt_of_lt_of_le hi (fin_lt hl))
  · simp at hg
    subst hg
    simp [AGate.op₁, AGate.op₂]

theorem family_depth {last : ℕ} (hl : last < 8) (n : ℕ) :
    (family last n).depth ≤ 3 * n + 4 := by
  unfold family
  split_ifs with hv
  · have hm := mOf_le n
    refine (ACircuit.depth_range_le _ _ (3 * mOf n + 4) fun i hi =>
      dp_le hv.1 (lt_of_lt_of_le hi (fin_lt hl))).trans (by omega)
  · simp [ACircuit.depth, ACircuit.gateDepths]

/-- **The describer describes the family** (in time `pBound n`). -/
theorem describer_describes {last : ℕ} (hl : last < 8) :
    describer.Describes (family last) bLen pBound := by
  intro n i hi
  by_cases hv : Valid n
  · have hb : bLen n = 3 * mOf n + 5 := if_pos hv
    have hiN : i < fin (mOf n) last + 1 := by
      have := hi; simp only [family, if_pos hv, length_circ] at this; exact this
    have hi2 : i < 2 ^ (3 * mOf n + 5) := lt_of_lt_of_le hiN (fin_lt hl)
    obtain ⟨st', r, pc, ⟨hr, hdesc⟩, hrun⟩ := (descProg_spec n (mOf n) i hv.1 hi2).runFinal
    have hget : (family last n)[i]'hi = gate (mOf n) i := by
      simp only [family, if_pos hv, circ, List.getElem_map, List.getElem_range]
    refine ⟨st'.at pc, ?_, ?_⟩
    · rw [hb]
      have hT : pBound n = descTime (mOf n) + 1 + (pBound n - (descTime (mOf n) + 1)) := by
        have := descTime_mono (mOf_le n)
        unfold pBound; omega
      rw [hT, ← hr]
      exact hrun _
    · rw [hget, hb]
      exact hdesc
  · have hb : bLen n = 0 := if_neg hv
    have hC : family last n = [.const 0] := if_neg hv
    have hi0 : i = 0 := by
      have := hi; simp only [hC, List.length_singleton] at this; omega
    obtain ⟨st', r, pc, ⟨hr, hdesc⟩, hrun⟩ := (descProg_spec0 n i).runFinal
    have hget : (family last n)[i]'hi = .const 0 := by
      simp only [hC, hi0, List.getElem_singleton]
    refine ⟨st'.at pc, ?_, ?_⟩
    · rw [hb]
      have hT : pBound n = 3 + 1 + (pBound n - 4) := by unfold pBound; omega
      rw [hT, ← hr]
      exact hrun _
    · rw [hget, hb]
      exact hdesc

/-! ## Deciding the languages over `ℝ` -/

/-- The last gate kind for each relation. -/
def lastOf : PerRel → ℕ
  | .le => 2
  | .ge => 3
  | _ => 4

theorem lastOf_lt (r : PerRel) : lastOf r < 8 := by cases r <;> simp [lastOf]

theorem values_family_valid {last : ℕ} (hl : last < 8) {n : ℕ} (hv : Valid n) (x : ℕ → ℝ) :
    ∃ vals, (family last n).values x = some vals ∧
      vals.getLast? = some (GateEval.val id signTest x (gate (mOf n)) (fin (mOf n) last)) := by
  refine ⟨_, ?_, GateEval.vlist_getLast _ _ _ _ _⟩
  rw [family, if_pos hv, circ]
  exact ACircuit.values_range _ _ _ fun i hi =>
    gate_valid hv.1 (lt_of_lt_of_le hi (fin_lt hl))

/-- **The value of the last gate over `ℝ`**: for an input `x`, the indicator of
`Y r per_m(X)` with `X_{ij} = x (i m + j)`, `Y = x (m²)`. -/
theorem family_last_real (r : PerRel) (hr : r = .eq ∨ r = .le ∨ r = .ge) {n : ℕ}
    (hv : Valid n) (x : ℕ → ℝ) :
    ∃ vals, (family (lastOf r) n).values x = some vals ∧
      vals.getLast? = some (if r.holds (x (mOf n * mOf n))
        (eval (fun p : Fin (mOf n) × Fin (mOf n) => x (p.1 * mOf n + p.2)) (per (mOf n)))
        then 1 else 0) := by
  obtain ⟨vals, hvals, hlast⟩ := values_family_valid (lastOf_lt r) hv x
  refine ⟨vals, hvals, ?_⟩
  rw [hlast]
  congr 1
  set m := mOf n
  have hm := hv.1
  have hP : GateEval.val id signTest x (gate m) (root m) =
      eval (fun p : Fin m × Fin m => x (p.1 * m + p.2)) (per m) := by
    rw [V_root_eq (K := ℝ) (fun c => by simp) hm, Algebra.algebraMap_self, map_id]
  have hY : GateEval.val id signTest x (gate m) (yIdx m) = x (m * m) := V_yIdx
  set P := eval (fun p : Fin m × Fin m => x (p.1 * m + p.2)) (per m)
  set Y := x (m * m)
  rcases hr with rfl | rfl | rfl
  · simp only [lastOf]
    rw [V_fin4, V_fin2, V_fin3, V_fin0 hm, V_fin1 hm, hP, hY]
    simp only [signTest, PerRel.holds]
    rcases lt_trichotomy Y P with h | h | h
    · have h1 : 0 ≤ P - Y := by linarith
      have h2 : ¬ 0 ≤ Y - P := by linarith
      simp [h1, h2, h.ne]
    · simp [h]
    · have h1 : ¬ 0 ≤ P - Y := by linarith
      have h2 : 0 ≤ Y - P := by linarith
      simp [h1, h2, h.ne']
  · simp only [lastOf]
    rw [V_fin2, V_fin0 hm, hP, hY]
    simp only [signTest, PerRel.holds, sub_nonneg]
    by_cases h : Y ≤ P <;> simp [h]
  · simp only [lastOf]
    rw [V_fin3, V_fin1 hm, hP, hY]
    simp only [signTest, PerRel.holds, sub_nonneg]
    by_cases h : P ≤ Y <;> simp [h]

theorem family_invalid {last n : ℕ} (hv : ¬ Valid n) (x : ℕ → ℝ) :
    (family last n).values x = some [0] := by
  rw [family, if_neg hv]; rfl

/-! ## Over `ℂ` -/

/-- The complex circuit family (the comparison `Y = per` with zero tests). -/
def familyC (n : ℕ) : CCircuit := (family 4 n).map AGate.toC

/-- The complex describer. -/
def describerC : CMachine := describer.toC

theorem describe_toC (b : ℕ) (g : AGate) (k : ℕ) :
    (g.toC).describe b k = ((g.describe b k : ℝ) : ℂ) := by
  have hcode : (g.toC).code = ((g.code : ℝ) : ℂ) := by
    rcases g with t | c | ⟨op, j, k⟩ | j
    · simp [AGate.toC, CGate.code, AGate.code]
    · simp [AGate.toC, CGate.code, AGate.code]
    · cases op <;> simp [AGate.toC, CGate.code, AGate.code]
    · simp [AGate.toC, CGate.code, AGate.code]
  have h1 : (g.toC).op₁ = g.op₁ := by cases g <;> rfl
  have h2 : (g.toC).op₂ = g.op₂ := by cases g <;> rfl
  have h3 : (g.toC).cst = ((g.cst : ℝ) : ℂ) := by
    cases g <;> simp [AGate.toC, CGate.cst, AGate.cst]
  unfold CGate.describe AGate.describe
  rw [hcode, h1, h2, h3]
  split_ifs <;> simp

theorem descProg_noGe : descProg.noGe = true := by decide

theorem describerC_describes : describerC.Describes familyC bLen pBound := by
  intro n i hi
  have hi' : i < (family 4 n).length := by simpa [familyC] using hi
  obtain ⟨cfg, hrun, hdesc⟩ := describer_describes (last := 4) (by norm_num) n i hi'
  refine ⟨cfg.toC, ?_, ?_⟩
  · have hinit : initConfigC [n, bLen n] (vecRegC (bitsOfC (bLen n) i)) =
        (initConfig [n, bLen n] (vecReg (bitsOf (bLen n) i))).toC := by
      rw [initConfig_toC]
      congr 1
      funext k
      simp only [vecRegC, vecReg, bitsOfC, bitsOf]
      split_ifs <;> simp
    have hno : describer.NoGe := Stmt.toMachine_noGe descProg_noGe
    rw [hinit, describerC, Machine.toC_runFinal hno, hrun]
    rfl
  · intro k hk
    have hget : (familyC n)[i]'hi = ((family 4 n)[i]'hi').toC := by simp [familyC]
    rw [hget, describe_toC, ← hdesc k hk]
    rfl

theorem familyC_length (n : ℕ) : (familyC n).length ≤ 2 ^ bLen n := by
  simpa [familyC] using family_length (last := 4) (by norm_num) n

theorem familyC_ops (n : ℕ) :
    ∀ g ∈ familyC n, g.op₁ < 2 ^ bLen n ∧ g.op₂ < 2 ^ bLen n := by
  intro g hg
  simp only [familyC, List.mem_map] at hg
  obtain ⟨g', hg', rfl⟩ := hg
  have := family_ops (last := 4) (by norm_num) n g' hg'
  cases g' <;> simpa [AGate.toC, CGate.op₁, CGate.op₂, AGate.op₁, AGate.op₂] using this

theorem familyC_depth (n : ℕ) : (familyC n).depth ≤ 3 * n + 4 := by
  unfold familyC family
  split_ifs with hv
  · have hm := mOf_le n
    rw [circ, List.map_map]
    refine (CCircuit.depth_range_le _ _ (3 * mOf n + 4) fun i hi =>
      dp_le hv.1 (lt_of_lt_of_le hi (fin_lt (by norm_num)))).trans (by omega)
  · simp [CCircuit.depth, CCircuit.gateDepths, AGate.toC]

/-- **The value of the last gate over `ℂ`**: the indicator of `Y = per_m(X)`. -/
theorem familyC_last {n : ℕ} (hv : Valid n) (x : ℕ → ℂ) :
    ∃ vals, (familyC n).values x = some vals ∧
      vals.getLast? = some (if x (mOf n * mOf n) =
        eval (fun p : Fin (mOf n) × Fin (mOf n) => x (p.1 * mOf n + p.2))
          (map (algebraMap ℝ ℂ) (per (mOf n))) then 1 else 0) := by
  have hm := hv.1
  have hvals := CCircuit.values_range (gate (mOf n)) (fin (mOf n) 4 + 1) x fun i hi =>
    gate_valid hm (lt_of_lt_of_le hi (fin_lt (by norm_num)))
  refine ⟨GateEval.vlist (fun c : ℝ => (c : ℂ)) zeroTest x (gate (mOf n)) (fin (mOf n) 4 + 1),
    ?_, (GateEval.vlist_getLast _ _ _ _ _).trans ?_⟩
  · rw [familyC, family, if_pos hv, circ, List.map_map]
    exact hvals
  · congr 1
    generalize mOf n = m at hm ⊢
    have hP := V_root_eq (K := ℂ) (e := fun c : ℝ => (c : ℂ)) (τ := zeroTest) (x := x)
      (fun c => by simp) hm
    have hY : GateEval.val (fun c : ℝ => (c : ℂ)) zeroTest x (gate m) (yIdx m) = x (m * m) :=
      V_yIdx
    rw [V_fin4, V_fin2, V_fin3, V_fin0 hm, V_fin1 hm, hP, hY]
    generalize (eval fun p : Fin m × Fin m => x (p.1 * m + p.2)) ((map (algebraMap ℝ ℂ)) (per m))
      = P
    generalize x (m * m) = Y
    simp only [zeroTest, sub_eq_zero]
    by_cases h : Y = P
    · simp [h]
    · simp [h, Ne.symm h]

theorem familyC_invalid {n : ℕ} (hv : ¬ Valid n) (x : ℕ → ℂ) :
    (familyC n).values x = some [0] := by
  rw [familyC, family, if_neg hv]; rfl

/-! ## Polynomial bounds -/

theorem bLen_poly : PolyBounded bLen :=
  ⟨8, 1, fun n => by
    unfold bLen; split_ifs <;> have := mOf_le n <;> nlinarith⟩

theorem depth_poly : PolyBounded fun n => 3 * n + 4 :=
  ⟨4, 1, fun n => by nlinarith⟩

theorem pBound_poly : PolyBounded pBound :=
  ⟨5000, 3, fun n => by
    unfold pBound descTime leafTime
    have : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
    have : n + 1 ≤ (n + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    nlinarith⟩

end Ryser

end ClassSep
