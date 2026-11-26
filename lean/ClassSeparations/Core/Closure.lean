import ClassSeparations.SA.Lemmas
import ClassSeparations.Basic.Circuits

/-!
# From real approximations to approximating circuits (§3.2, Lemma 3.3)

**Lemma 3.3.**  Fix finitely many circuit graphs.  Let `f ∈ ℝ[X]`, and suppose that for every
`η > 0` one of the graphs computes, for suitable real values of its constants, a polynomial all
of whose coefficients are within `η` of the corresponding coefficients of `f`.  Then one of the
graphs, with suitable constants in `ℝ((ε))`, approximates `f` in the sense of Definition 2.2.
-/

noncomputable section

open MvPolynomial

namespace ClassSep

variable {σ : Type} [Fintype σ]

/-- **Lemma 3.3.** -/
theorem closure_lemma (hS : SAFacts) (graphs : List (Shape σ)) (f : MvPolynomial σ ℝ)
    (h : ∀ η > 0, ∃ Γ ∈ graphs, ∃ (a : ℕ → ℝ) (P : MvPolynomial σ ℝ), Γ.Computes a P ∧
      ∀ m, |P.coeff m - f.coeff m| < η) :
    ∃ Γ ∈ graphs, ∃ (c : ℕ → LaurentSeries ℝ) (P : MvPolynomial σ (LaurentSeries ℝ)),
      Γ.Computes c P ∧ IsApprox P f := by
  sorry

/-- Lemma 3.3 in terms of border complexity. -/
theorem borderLE_of_approx (hS : SAFacts) (graphs : List (Shape σ)) (s : ℕ)
    (hs : ∀ Γ ∈ graphs, Γ.length ≤ s) (f : MvPolynomial σ ℝ)
    (h : ∀ η > 0, ∃ Γ ∈ graphs, ∃ (a : ℕ → ℝ) (P : MvPolynomial σ ℝ), Γ.Computes a P ∧
      ∀ m, |P.coeff m - f.coeff m| < η) :
    BorderLE f s := by
  obtain ⟨Γ, hΓ, c, P, hP, happ⟩ := closure_lemma hS graphs f h
  exact ⟨Γ, c, hs Γ hΓ, P, hP, happ⟩

end ClassSep
