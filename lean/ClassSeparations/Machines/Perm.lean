import ClassSeparations.Machines.Complex
import ClassSeparations.Cert.Permanent
import ClassSeparations.Machines.RyserPAR

/-!
# The permanent languages, and their membership in `PAR` (Lemma 4.6)

`PERM = {(X, Y) ∈ ℝ^{m²} × ℝ : Y = per_m(X), m ≥ 1}` as a language over `ℝ^∞`: an input of
length `n` belongs to it iff `n = m² + 1` and the last coordinate equals the permanent of the
`m × m` matrix formed by the first `m²` coordinates (row-major).  Likewise for the thresholds
and over `ℂ`.

**Lemma 4.6.**  The languages `{Y = per_m(X)}`, `{Y ≤ per_m(X)}` and `{Y ≥ per_m(X)}` are in
`PAR_ℝ`, and `{Y = per_m(X)}` is in `PAR_ℂ` (Ryser's formula evaluated by circuits of depth
`O(m)` and size `2^m poly(m)`, whose gates are described in polynomial time).
-/

noncomputable section

open MvPolynomial Classical

namespace ClassSep

/-- The matrix `X` formed by the first `m²` coordinates of `w ∈ ℝⁿ` (row-major). -/
def permX {n : ℕ} (m : ℕ) (w : Fin n → ℝ) : Fin m × Fin m → ℝ :=
  fun p => if h : p.1.val * m + p.2.val < n then w ⟨_, h⟩ else 0

/-- The coordinate `Y` (number `m²`) of `w ∈ ℝⁿ`. -/
def permY {n : ℕ} (m : ℕ) (w : Fin n → ℝ) : ℝ :=
  if h : m * m < n then w ⟨m * m, h⟩ else 0

/-- The language `{(X, Y) : Y r per_m(X), m ≥ 1}` over `ℝ^∞`. -/
def permLang (r : PerRel) : Lang :=
  fun n => {w | ∃ m, 1 ≤ m ∧ n = m * m + 1 ∧ r.holds (permY m w) (eval (permX m w) (per m))}

/-- The complex matrix `X`. -/
def permXC {n : ℕ} (m : ℕ) (w : Fin n → ℂ) : Fin m × Fin m → ℂ :=
  fun p => if h : p.1.val * m + p.2.val < n then w ⟨_, h⟩ else 0

/-- The complex coordinate `Y`. -/
def permYC {n : ℕ} (m : ℕ) (w : Fin n → ℂ) : ℂ :=
  if h : m * m < n then w ⟨m * m, h⟩ else 0

/-- The graph of the complex permanent as a language over `ℂ^∞`. -/
def cpermLang : LangC :=
  fun n => {w | ∃ m, 1 ≤ m ∧ n = m * m + 1 ∧
    permYC m w = eval (permXC m w) (map (algebraMap ℝ ℂ) (per m))}

/-- Membership in `permLang` for input lengths `m² + 1`, in terms of the input registers. -/
private theorem permLang_iff {r : PerRel} {n : ℕ} (hv : Ryser.Valid n) (w : Fin n → ℝ) :
    w ∈ permLang r n ↔ r.holds (vecReg w (Ryser.mOf n * Ryser.mOf n))
      (eval (fun p : Fin (Ryser.mOf n) × Fin (Ryser.mOf n) =>
        vecReg w (p.1 * Ryser.mOf n + p.2)) (per (Ryser.mOf n))) := by
  constructor
  · rintro ⟨m, -, hn, h⟩
    have : m = Ryser.mOf n := Nat.mul_self_inj.mp (by have := hv.2; omega)
    subst this
    exact h
  · intro h
    exact ⟨_, hv.1, hv.2, h⟩

/-- Membership in `cpermLang` for input lengths `m² + 1`, in terms of the input registers. -/
private theorem cpermLang_iff {n : ℕ} (hv : Ryser.Valid n) (w : Fin n → ℂ) :
    w ∈ cpermLang n ↔ vecRegC w (Ryser.mOf n * Ryser.mOf n) =
      eval (fun p : Fin (Ryser.mOf n) × Fin (Ryser.mOf n) =>
        vecRegC w (p.1 * Ryser.mOf n + p.2)) (map (algebraMap ℝ ℂ) (per (Ryser.mOf n))) := by
  constructor
  · rintro ⟨m, -, hn, h⟩
    have : m = Ryser.mOf n := Nat.mul_self_inj.mp (by have := hv.2; omega)
    subst this
    exact h
  · intro h
    exact ⟨_, hv.1, hv.2, h⟩

/-- **Lemma 4.6** over `ℝ`. -/
theorem permLang_mem_PAR (r : PerRel) (hr : r = .eq ∨ r = .le ∨ r = .ge) :
    permLang r ∈ PAR_R := by
  have hl := Ryser.lastOf_lt r
  refine ⟨Ryser.family (Ryser.lastOf r), Ryser.describer, Ryser.bLen, fun n => 3 * n + 4,
    Ryser.pBound, Ryser.bLen_poly, Ryser.depth_poly, Ryser.pBound_poly,
    Ryser.describer_describes hl, fun n => ⟨Ryser.family_length hl n, Ryser.family_ops hl n,
      Ryser.family_depth hl n, fun w => ?_⟩⟩
  by_cases hv : Ryser.Valid n
  · obtain ⟨vals, hvals, hlast⟩ := Ryser.family_last_real r hr hv (vecReg w)
    refine ⟨vals, hvals, ?_⟩
    rw [hlast, permLang_iff hv]
  · refine ⟨[0], Ryser.family_invalid hv _, ?_⟩
    have : w ∉ permLang r n := fun ⟨m, hm, hn, _⟩ => hv ((Ryser.valid_iff n).mpr ⟨m, hm, hn⟩)
    simp [this]

/-- **Lemma 4.6** over `ℂ`. -/
theorem cpermLang_mem_PAR : cpermLang ∈ PAR_C := by
  refine ⟨Ryser.familyC, Ryser.describerC, Ryser.bLen, fun n => 3 * n + 4,
    Ryser.pBound, Ryser.bLen_poly, Ryser.depth_poly, Ryser.pBound_poly,
    Ryser.describerC_describes, fun n => ⟨Ryser.familyC_length n, Ryser.familyC_ops n,
      Ryser.familyC_depth n, fun w => ?_⟩⟩
  by_cases hv : Ryser.Valid n
  · obtain ⟨vals, hvals, hlast⟩ := Ryser.familyC_last hv (vecRegC w)
    refine ⟨vals, hvals, ?_⟩
    rw [hlast, cpermLang_iff hv]
  · refine ⟨[0], Ryser.familyC_invalid hv _, ?_⟩
    have : w ∉ cpermLang n := fun ⟨m, hm, hn, _⟩ => hv ((Ryser.valid_iff n).mpr ⟨m, hm, hn⟩)
    simp [this]

end ClassSep
