import ClassSeparations.SA.Facts

/-!
# Consequences of (S1)–(S8) used throughout the paper

Instances of (S1) (sets and functions defined by first-order formulas are semialgebraic) and
standard consequences of the facts in `SAFacts` that are used repeatedly.
-/

noncomputable section

open Set Filter Topology

namespace ClassSep

variable {α β : Type}

/-! ## Semialgebraic functions -/

/-- Polynomial maps are semialgebraic. -/
theorem isSAFunOn_poly (D : Set (α → ℝ)) (hD : IsSA D) (σ : β → MvPolynomial α ℝ) :
    IsSAFunOn D (fun x b => MvPolynomial.eval x (σ b)) := by
  sorry

/-- The preimage of a semialgebraic set under a semialgebraic map is semialgebraic. -/
theorem IsSAFunOn.preimage {D : Set (α → ℝ)} {g : (α → ℝ) → (β → ℝ)} [Finite β]
    (hg : IsSAFunOn D g) {s : Set (β → ℝ)} (hs : IsSA s) : IsSA (D ∩ g ⁻¹' s) := by
  sorry

/-- The image of a semialgebraic set under a semialgebraic map is semialgebraic. -/
theorem IsSAFunOn.image {D : Set (α → ℝ)} {g : (α → ℝ) → (β → ℝ)} [Finite α]
    (hg : IsSAFunOn D g) {s : Set (α → ℝ)} (hs : IsSA s) (hsD : s ⊆ D) : IsSA (g '' s) := by
  sorry

/-! ## Dimension in families -/

/-- **(S1), second sentence.**  Dimension is definable in semialgebraic families. -/
theorem isSA_dimGE_fiber [Fintype α] [Fintype β] {A : Set (α ⊕ β → ℝ)} (hA : IsSA A) (e : ℕ) :
    IsSA {c : β → ℝ | DimGE (fiberOver A c) e} := by
  sorry

/-! ## Consequences of the facts -/

/-- A semialgebraic set of dimension `< n` in `ℝⁿ` has empty interior, and so has its closure;
its complement is dense. -/
theorem dense_compl_of_dimLT (hS : SAFacts) [Fintype α] {A : Set (α → ℝ)} (hA : IsSA A)
    (h : DimLT A (Fintype.card α)) : Dense (closure A)ᶜ := by
  sorry

/-- **(S5)**: a semialgebraic function on an open set is continuous on an open dense subset. -/
theorem exists_open_dense_continuous (hS : SAFacts) [Fintype α] {O : Set (α → ℝ)}
    (hO : IsOpen O) {g : (α → ℝ) → ℝ} (hg : IsSAFunOn₁ O g) :
    ∃ O' ⊆ O, IsOpen O' ∧ O ⊆ closure O' ∧ IsSA O' ∧ ContinuousOn g O' := by
  sorry

/-- A semialgebraic function that is positive on an open set `O` is bounded below by a positive
constant on some open ball in `O`. -/
theorem exists_ball_lower_bound (hS : SAFacts) [Fintype α] {O : Set (α → ℝ)} (hO : IsOpen O)
    (hOne : O.Nonempty) {g : (α → ℝ) → ℝ} (hg : IsSAFunOn₁ O g) (hpos : ∀ x ∈ O, 0 < g x) :
    ∃ x₀ r c, 0 < r ∧ Metric.ball x₀ r ⊆ O ∧ 0 < c ∧ ∀ x ∈ Metric.ball x₀ r, c ≤ g x := by
  sorry

/-- If finitely many semialgebraic sets cover a nonempty open set, one of them has nonempty
interior (from (S4)(a)). -/
theorem exists_interior_of_finite_cover (hS : SAFacts) [Fintype α] {ι' : Type*} (s : Finset ι')
    (A : ι' → Set (α → ℝ)) (hA : ∀ i ∈ s, IsSA (A i)) {O : Set (α → ℝ)} (hO : IsOpen O)
    (hOne : O.Nonempty) (hcov : O ⊆ ⋃ i ∈ s, A i) :
    ∃ i ∈ s, (interior (A i ∩ O)).Nonempty := by
  sorry

/-- A semialgebraic set has dimension `0` (i.e. `< 1`) exactly when it is finite. -/
theorem dimLT_one_iff_finite (hS : SAFacts) [Fintype α] {A : Set (α → ℝ)} (hA : IsSA A) :
    DimLT A 1 ↔ A.Finite := by
  sorry

/-- **(S3)**: a semialgebraic subset of `ℝ` either contains an interval `(a, a + e)` or misses
such an interval. -/
theorem germ_right (hS : SAFacts) {A : Set ℝ} (hA : IsSA₁ A) (a : ℝ) :
    (∃ e > 0, Ioo a (a + e) ⊆ A) ∨ (∃ e > 0, Disjoint (Ioo a (a + e)) A) := by
  sorry

/-- **(S3)**: a semialgebraic function on `(0, δ)` that is bounded has a limit at `0⁺`. -/
theorem exists_tendsto_of_bdd (hS : SAFacts) {g : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hg : IsSAFun₁₁ (Ioo 0 δ) g) {M : ℝ} (hM : ∀ x ∈ Ioo 0 δ, |g x| ≤ M) :
    ∃ L, Tendsto g (𝓝[>] 0) (𝓝 L) := by
  sorry

end ClassSep
