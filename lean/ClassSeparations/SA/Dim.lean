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
def coordProj {d : ℕ} (σ : Fin d → α) (A : Set (α → ℝ)) : Set (Fin d → ℝ) :=
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

/-- Restriction of coordinates along an injective map is an open map. -/
theorem isOpenMap_comp_of_injective {β γ : Type} [Finite β] [Finite γ] {f : β → γ}
    (hf : Function.Injective f) : IsOpenMap (fun u : γ → ℝ => u ∘ f) := by
  classical
  have := Fintype.ofFinite β
  have := Fintype.ofFinite γ
  have hsurj : Function.Surjective (LinearMap.funLeft ℝ ℝ f) :=
    LinearMap.funLeft_surjective_of_injective _ _ f hf
  exact (LinearMap.funLeft ℝ ℝ f).isOpenMap_of_finiteDimensional hsurj

theorem dimGE_zero_iff (A : Set (α → ℝ)) : DimGE A 0 ↔ A.Nonempty := by
  constructor
  · rintro ⟨σ, -, u, hu⟩
    obtain ⟨v, hv, -⟩ := interior_subset hu
    exact ⟨v, hv⟩
  · rintro ⟨v, hv⟩
    refine ⟨Fin.elim0, fun i => i.elim0, ?_⟩
    have : coordProj (Fin.elim0 : Fin 0 → α) A = Set.univ := by
      ext u
      simp only [Set.mem_univ, iff_true]
      exact ⟨v, hv, funext fun i => i.elim0⟩
    rw [this, interior_univ]
    exact Set.univ_nonempty

theorem DimGE.mono {A B : Set (α → ℝ)} {d : ℕ} (h : DimGE A d) (hAB : A ⊆ B) : DimGE B d := by
  obtain ⟨σ, hσ, hne⟩ := h
  exact ⟨σ, hσ, hne.mono (interior_mono (Set.image_mono hAB))⟩

theorem DimLT.mono {A B : Set (α → ℝ)} {d : ℕ} (h : DimLT B d) (hAB : A ⊆ B) : DimLT A d :=
  fun h' => h (h'.mono hAB)

theorem DimGE.of_le {A : Set (α → ℝ)} {d e : ℕ} (h : DimGE A d) (hed : e ≤ d) : DimGE A e := by
  obtain ⟨σ, hσ, hne⟩ := h
  refine ⟨σ ∘ Fin.castLE hed, hσ.comp (Fin.castLE_injective hed), ?_⟩
  have hopen := isOpenMap_comp_of_injective (β := Fin e) (γ := Fin d)
    (Fin.castLE_injective hed)
  have hsub : (fun u : Fin d → ℝ => u ∘ Fin.castLE hed) '' coordProj σ A =
      coordProj (σ ∘ Fin.castLE hed) A := by
    ext u
    simp only [coordProj, Set.mem_image]
    constructor
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨_, ⟨v, hv, rfl⟩, rfl⟩
  rw [← hsub]
  exact (hne.image _).mono (hopen.image_interior_subset _)

theorem DimLT.of_le {A : Set (α → ℝ)} {d e : ℕ} (h : DimLT A e) (hed : e ≤ d) : DimLT A d :=
  fun h' => h (h'.of_le hed)

/-- **(S4)(a), first part.**  A subset of `ℝⁿ` has dimension `n` exactly when it has nonempty
interior. -/
theorem dimGE_card_iff [Fintype α] (A : Set (α → ℝ)) :
    DimGE A (Fintype.card α) ↔ (interior A).Nonempty := by
  constructor
  · rintro ⟨σ, hσ, hne⟩
    have hbij : Function.Bijective σ :=
      (Fintype.bijective_iff_injective_and_card σ).2 ⟨hσ, by simp⟩
    let e : Fin (Fintype.card α) ≃ α := Equiv.ofBijective σ hbij
    have hopen := isOpenMap_comp_of_injective (β := α) (γ := Fin (Fintype.card α))
      e.symm.injective
    have himg : (fun u : Fin (Fintype.card α) → ℝ => u ∘ e.symm) '' coordProj σ A = A := by
      ext v
      simp only [coordProj, Set.mem_image]
      constructor
      · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
        convert hw using 1
        funext a
        simp only [Function.comp_apply]
        congr 1
        exact e.apply_symm_apply a
      · intro hv
        refine ⟨v ∘ σ, ⟨v, hv, rfl⟩, ?_⟩
        funext a
        simp only [Function.comp_apply]
        congr 1
        exact e.apply_symm_apply a
    rw [← himg]
    exact (hne.image _).mono (hopen.image_interior_subset _)
  · intro hne
    let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
    refine ⟨e.symm, e.symm.injective, ?_⟩
    have hopen := isOpenMap_comp_of_injective (β := Fin (Fintype.card α)) (γ := α)
      e.symm.injective
    exact (hne.image _).mono (hopen.image_interior_subset _)

theorem dimLT_card_iff [Fintype α] (A : Set (α → ℝ)) :
    DimLT A (Fintype.card α) ↔ interior A = ∅ := by
  unfold DimLT
  rw [dimGE_card_iff, Set.not_nonempty_iff_eq_empty]

/-- Dimension never exceeds the number of coordinates. -/
theorem dimLT_succ_card [Fintype α] (A : Set (α → ℝ)) : DimLT A (Fintype.card α + 1) := by
  rintro ⟨σ, hσ, -⟩
  have := Fintype.card_le_of_injective σ hσ
  simp at this

end ClassSep
