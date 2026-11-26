import ClassSeparations.SA.Lemmas

/-!
# Derivatives of semialgebraic families (§3.1)

**Lemma 3.1.**  Let `V ⊆ ℝᴺ` be open and nonempty, `g : V × (0, ε₀) → ℝ` semialgebraic, and
`g₀ : V → ℝ` continuous with `g(ξ, ε) → g₀(ξ)` as `ε → 0⁺` for every `ξ ∈ V`.  Then there are
an open ball `V' ⊆ V` and `ε' > 0` such that `g` is `C¹` on `V' × (0, ε')`, `g₀` is `C¹` on
`V'`, and `∂g/∂ξᵢ(·, ε) → ∂g₀/∂ξᵢ` uniformly on `V'`.

**Corollary 3.2.**  The same for maps to `ℝ^κ`, with uniform convergence of all
`ξ`-derivatives up to order `D`.  We state the convergence of derivatives with the iterated
Fréchet derivatives `iteratedFDeriv ℝ j`, whose components are the partial derivatives
`∂^α` with `|α| = j`.
-/

noncomputable section

open Set Filter Topology

namespace ClassSep

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The domain `V × (0, ε₀)` as a subset of `ℝ^(Option ι)` (the coordinate `none` is `ε`). -/
def boxDomain (V : Set (ι → ℝ)) (ε₀ : ℝ) : Set (Option ι → ℝ) :=
  {v | v ∘ some ∈ V ∧ v none ∈ Ioo 0 ε₀}

/-- Uncurrying `g : ℝ^ι → ℝ → X` to a function on `ℝ^(Option ι)`. -/
def uncurryOpt {X : Type*} (g : (ι → ℝ) → ℝ → X) : (Option ι → ℝ) → X :=
  fun v => g (v ∘ some) (v none)

/-- **Lemma 3.1.** -/
theorem derivatives (hS : SAFacts) (V : Set (ι → ℝ)) (hV : IsOpen V) (hVne : V.Nonempty)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) (g : (ι → ℝ) → ℝ → ℝ)
    (hg : IsSAFunOn₁ (boxDomain V ε₀) (uncurryOpt g))
    (g₀ : (ι → ℝ) → ℝ) (hg₀ : ContinuousOn g₀ V)
    (hlim : ∀ ξ ∈ V, Tendsto (g ξ) (𝓝[>] 0) (𝓝 (g₀ ξ))) :
    ∃ (ξ' : ι → ℝ) (r' ε' : ℝ), 0 < r' ∧ Metric.ball ξ' r' ⊆ V ∧ 0 < ε' ∧ ε' ≤ ε₀ ∧
      ContDiffOn ℝ 1 (fun p : (ι → ℝ) × ℝ => g p.1 p.2) (Metric.ball ξ' r' ×ˢ Ioo 0 ε') ∧
      ContDiffOn ℝ 1 g₀ (Metric.ball ξ' r') ∧
      ∀ i : ι, TendstoUniformlyOn (fun ε ξ => fderiv ℝ (fun ξ => g ξ ε) ξ (Pi.single i 1))
        (fun ξ => fderiv ℝ g₀ ξ (Pi.single i 1)) (𝓝[>] 0) (Metric.ball ξ' r') := by
  sorry

/-- **Corollary 3.2.** -/
theorem derivatives_cor (hS : SAFacts) (V : Set (ι → ℝ)) (hV : IsOpen V) (hVne : V.Nonempty)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) (W : (ι → ℝ) → ℝ → (κ → ℝ))
    (hW : IsSAFunOn (boxDomain V ε₀) (uncurryOpt W))
    (φ : (ι → ℝ) → (κ → ℝ)) (hφ : ContinuousOn φ V)
    (hlim : ∀ ξ ∈ V, Tendsto (W ξ) (𝓝[>] 0) (𝓝 (φ ξ))) (D : ℕ) (hD : 1 ≤ D) :
    ∃ (ξ' : ι → ℝ) (r' ε' : ℝ), 0 < r' ∧ Metric.ball ξ' r' ⊆ V ∧ 0 < ε' ∧ ε' ≤ ε₀ ∧
      ContDiffOn ℝ 1 (fun p : (ι → ℝ) × ℝ => W p.1 p.2) (Metric.ball ξ' r' ×ˢ Ioo 0 ε') ∧
      (∀ ε ∈ Ioo 0 ε', ContDiffOn ℝ D (fun ξ => W ξ ε) (Metric.ball ξ' r')) ∧
      (∀ j ≤ D, ContinuousOn (fun p : (ι → ℝ) × ℝ => iteratedFDeriv ℝ j (fun ξ => W ξ p.2) p.1)
        (Metric.ball ξ' r' ×ˢ Ioo 0 ε')) ∧
      ContDiffOn ℝ D φ (Metric.ball ξ' r') ∧
      ∀ j ≤ D, TendstoUniformlyOn (fun ε ξ => iteratedFDeriv ℝ j (fun ξ => W ξ ε) ξ)
        (fun ξ => iteratedFDeriv ℝ j φ ξ) (𝓝[>] 0) (Metric.ball ξ' r') := by
  sorry

end ClassSep
