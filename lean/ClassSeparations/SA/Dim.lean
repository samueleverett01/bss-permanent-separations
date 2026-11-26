import ClassSeparations.SA.Formula

/-!
# Semialgebraic dimension

We use the standard description of the dimension of a semialgebraic set (BCR98, §2.8;
vdD98, Ch. 4): `dim A ≥ d` exactly when the projection of `A` to some `d` coordinates has
nonempty interior.  We work with the two predicates `DimGE A d` and `DimLT A d := ¬ DimGE A d`.
In particular `DimGE A 0 ↔ A.Nonempty`, so the empty set has dimension `-∞`.
-/

noncomputable section

namespace ClassSep

variable {α β : Type}

/-- The projection of `A ⊆ ℝ^α` to the coordinates selected by `σ : Fin d → α`. -/
def coordProj (σ : Fin d → α) (A : Set (α → ℝ)) : Set (Fin d → ℝ) :=
  (fun v => v ∘ σ) '' A

/-- `dim A ≥ d`: the projection of `A` to some `d` distinct coordinates has nonempty
interior. -/
def DimGE (A : Set (α → ℝ)) (d : ℕ) : Prop :=
  ∃ σ : Fin d → α, Function.Injective σ ∧ (interior (coordProj σ A)).Nonempty

/-- `dim A < d`. -/
def DimLT (A : Set (α → ℝ)) (d : ℕ) : Prop := ¬ DimGE A d

/-- The fiber of `A ⊆ ℝ^(α ⊕ β)` over `c ∈ ℝ^β`, a subset of `ℝ^α`. -/
def fiberOver (A : Set (α ⊕ β → ℝ)) (c : β → ℝ) : Set (α → ℝ) :=
  {x | Sum.elim x c ∈ A}

theorem dimGE_zero_iff (A : Set (α → ℝ)) : DimGE A 0 ↔ A.Nonempty := by
  sorry

theorem DimGE.mono {A B : Set (α → ℝ)} {d : ℕ} (h : DimGE A d) (hAB : A ⊆ B) : DimGE B d := by
  sorry

theorem DimGE.of_le {A : Set (α → ℝ)} {d e : ℕ} (h : DimGE A d) (hed : e ≤ d) : DimGE A e := by
  sorry

/-- **(S4)(a), first part.**  A subset of `ℝⁿ` has dimension `n` exactly when it has nonempty
interior. -/
theorem dimGE_card_iff [Fintype α] (A : Set (α → ℝ)) :
    DimGE A (Fintype.card α) ↔ (interior A).Nonempty := by
  sorry

theorem dimLT_card_iff [Fintype α] (A : Set (α → ℝ)) :
    DimLT A (Fintype.card α) ↔ interior A = ∅ := by
  unfold DimLT
  rw [dimGE_card_iff, Set.not_nonempty_iff_eq_empty]

/-- Dimension never exceeds the number of coordinates. -/
theorem dimLT_succ_card [Fintype α] (A : Set (α → ℝ)) : DimLT A (Fintype.card α + 1) := by
  sorry

end ClassSep
