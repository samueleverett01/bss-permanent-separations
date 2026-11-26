import Mathlib

/-!
# Taylor polynomials as multivariate polynomials

For `g : ℝ^ι → ℝ`, a point `ξ₁` and an order `D`, the Taylor polynomial of order `D` of `g` at
`ξ₁` is the polynomial
`∑_{j ≤ D} (1/j!) Dʲg(ξ₁)(X - ξ₁, …, X - ξ₁) ∈ ℝ[X_i : i ∈ ι]`.
We prove the facts used in the paper: Taylor's theorem in little-`o` form for functions of
class `C^D`, uniqueness of polynomial approximations of order `o(|ξ - ξ₁|^D)`, the fact that a
polynomial of degree `≤ D` is its own Taylor polynomial of order `D`, and continuity of the
coefficients in the derivatives.
-/

noncomputable section

open MvPolynomial Filter Topology Asymptotics

namespace ClassSep

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The polynomial `Dʲg(ξ₁)(X - ξ₁, …, X - ξ₁)` written in the monomial basis. -/
def jetTerm (j : ℕ) (L : ContinuousMultilinearMap ℝ (fun _ : Fin j => ι → ℝ) ℝ)
    (ξ₁ : ι → ℝ) : MvPolynomial ι ℝ :=
  ∑ i : Fin j → ι, MvPolynomial.C (L fun k => Pi.single (i k) 1) *
    ∏ k : Fin j, (X (i k) - MvPolynomial.C (ξ₁ (i k)))

/-- The Taylor polynomial of order `D` of `g` at `ξ₁`. -/
def taylorPoly (D : ℕ) (g : (ι → ℝ) → ℝ) (ξ₁ : ι → ℝ) : MvPolynomial ι ℝ :=
  ∑ j ∈ Finset.range (D + 1),
    MvPolynomial.C ((j.factorial : ℝ)⁻¹) * jetTerm j (iteratedFDeriv ℝ j g ξ₁) ξ₁

theorem eval_jetTerm (j : ℕ) (L : ContinuousMultilinearMap ℝ (fun _ : Fin j => ι → ℝ) ℝ)
    (ξ₁ ξ : ι → ℝ) : eval ξ (jetTerm j L ξ₁) = L fun _ => ξ - ξ₁ := by
  sorry

theorem totalDegree_taylorPoly_le (D : ℕ) (g : (ι → ℝ) → ℝ) (ξ₁ : ι → ℝ) :
    (taylorPoly D g ξ₁).totalDegree ≤ D := by
  sorry

/-- **Taylor's theorem** in little-`o` form. -/
theorem taylorPoly_isLittleO {D : ℕ} {g : (ι → ℝ) → ℝ} {ξ₁ : ι → ℝ}
    (hg : ContDiffAt ℝ D g ξ₁) :
    (fun ξ => g ξ - eval ξ (taylorPoly D g ξ₁)) =o[𝓝 ξ₁] fun ξ => ‖ξ - ξ₁‖ ^ D := by
  sorry

/-- **Uniqueness**: two polynomials of degree `≤ D` that agree up to `o(|ξ - ξ₁|^D)` are
equal. -/
theorem eq_of_isLittleO {D : ℕ} {P P' : MvPolynomial ι ℝ} {ξ₁ : ι → ℝ}
    (hP : P.totalDegree ≤ D) (hP' : P'.totalDegree ≤ D)
    (h : (fun ξ => eval ξ P - eval ξ P') =o[𝓝 ξ₁] fun ξ => ‖ξ - ξ₁‖ ^ D) : P = P' := by
  sorry

/-- The Taylor polynomial of a `C^D` function is the unique polynomial of degree `≤ D` that
approximates it to order `o(|ξ - ξ₁|^D)`. -/
theorem taylorPoly_eq_of_isLittleO {D : ℕ} {g : (ι → ℝ) → ℝ} {ξ₁ : ι → ℝ}
    (hg : ContDiffAt ℝ D g ξ₁) {P : MvPolynomial ι ℝ} (hP : P.totalDegree ≤ D)
    (h : (fun ξ => g ξ - eval ξ P) =o[𝓝 ξ₁] fun ξ => ‖ξ - ξ₁‖ ^ D) :
    taylorPoly D g ξ₁ = P := by
  refine eq_of_isLittleO (ξ₁ := ξ₁) (totalDegree_taylorPoly_le D g ξ₁) hP ?_
  have := h.sub (taylorPoly_isLittleO hg)
  refine this.congr_left fun ξ => ?_
  ring

/-- A polynomial of degree `≤ D` is its own Taylor polynomial of order `D`. -/
theorem taylorPoly_eval_poly {D : ℕ} {f : MvPolynomial ι ℝ} (hf : f.totalDegree ≤ D)
    (ξ₁ : ι → ℝ) : taylorPoly D (fun ξ => eval ξ f) ξ₁ = f := by
  refine taylorPoly_eq_of_isLittleO ?_ hf ?_
  · sorry
  · simp only [sub_self]
    exact Asymptotics.isLittleO_zero _ _

/-- The Taylor polynomial depends only on the germ of `g` at `ξ₁`. -/
theorem taylorPoly_congr {D : ℕ} {g h : (ι → ℝ) → ℝ} {ξ₁ : ι → ℝ} (hgh : g =ᶠ[𝓝 ξ₁] h) :
    taylorPoly D g ξ₁ = taylorPoly D h ξ₁ := by
  sorry

/-- The coefficients of Taylor polynomials depend continuously on the base point and on the
derivatives: if the derivatives of order `≤ D` of `g_ε` converge to those of `g` at `ξ₁`,
uniformly near... (pointwise version) then the Taylor coefficients converge. -/
theorem tendsto_coeff_taylorPoly {D : ℕ} {β : Type*} {l : Filter β} {G : β → (ι → ℝ) → ℝ}
    {g : (ι → ℝ) → ℝ} {ξ₁ : ι → ℝ}
    (h : ∀ j ≤ D, Tendsto (fun b => iteratedFDeriv ℝ j (G b) ξ₁) l
      (𝓝 (iteratedFDeriv ℝ j g ξ₁))) (m : ι →₀ ℕ) :
    Tendsto (fun b => (taylorPoly D (G b) ξ₁).coeff m) l (𝓝 ((taylorPoly D g ξ₁).coeff m)) := by
  sorry

end ClassSep
