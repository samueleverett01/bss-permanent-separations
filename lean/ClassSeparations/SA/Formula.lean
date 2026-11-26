import Mathlib

/-!
# Semialgebraic sets as first-order definable sets

Paper, §2.3.  We define a set `s ⊆ ℝ^α` to be *semialgebraic* if it is defined by a
first-order formula over the ordered field `(ℝ, +, ×, <)` with real parameters.  Atomic
formulas are polynomial sign conditions `p > 0` and `p = 0` with `p ∈ ℝ[α]`.

With this definition, fact **(S1)** of the paper ("sets and maps defined by first-order
formulas are semialgebraic") holds by construction; the Tarski–Seidenberg theorem is the
statement that this notion agrees with the quantifier-free one, which the paper does not need
except in effective form (see `ClassSeparations.Cited`).

This file develops the closure properties used to verify, in each application of (S1), that
a concrete set or function is semialgebraic.
-/

noncomputable section

open MvPolynomial

namespace ClassSep

/-- First-order formulas of the ordered field `ℝ` with real parameters and free variables
indexed by `α`.  Atoms are polynomial sign conditions; `ex` binds the variable `none`. -/
inductive Fml : Type → Type 1 where
  | pos {α : Type} (p : MvPolynomial α ℝ) : Fml α
  | zero {α : Type} (p : MvPolynomial α ℝ) : Fml α
  | not {α : Type} (φ : Fml α) : Fml α
  | and {α : Type} (φ ψ : Fml α) : Fml α
  | ex {α : Type} (φ : Fml (Option α)) : Fml α

/-- Extend a valuation by a value for the new variable `none`. -/
def extendVal {α : Type} (a : ℝ) (v : α → ℝ) : Option α → ℝ := fun o => o.elim a v

/-- Truth of a formula under a valuation of its free variables. -/
def Fml.Holds : {α : Type} → Fml α → (α → ℝ) → Prop
  | _, .pos p, v => 0 < eval v p
  | _, .zero p, v => eval v p = 0
  | _, .not φ, v => ¬ φ.Holds v
  | _, .and φ ψ, v => φ.Holds v ∧ ψ.Holds v
  | _, .ex φ, v => ∃ a : ℝ, φ.Holds (extendVal a v)

/-- A set `s ⊆ ℝ^α` is semialgebraic if it is defined by a first-order formula. -/
def IsSA {α : Type} (s : Set (α → ℝ)) : Prop :=
  ∃ φ : Fml α, ∀ v, v ∈ s ↔ φ.Holds v

/-- A map `g : ℝ^α → ℝ^β` is semialgebraic on `D` if `D` and the graph of `g` over `D` are
semialgebraic.  The graph is a subset of `ℝ^(α ⊕ β)`. -/
def IsSAFunOn {α β : Type} (D : Set (α → ℝ)) (g : (α → ℝ) → (β → ℝ)) : Prop :=
  IsSA D ∧ IsSA {v : α ⊕ β → ℝ | v ∘ Sum.inl ∈ D ∧ g (v ∘ Sum.inl) = v ∘ Sum.inr}

/-- A real-valued function `g : ℝ^α → ℝ` is semialgebraic on `D`. -/
def IsSAFunOn₁ {α : Type} (D : Set (α → ℝ)) (g : (α → ℝ) → ℝ) : Prop :=
  IsSAFunOn D (fun x (_ : Unit) => g x)

/-- A subset of `ℝ` is semialgebraic. -/
def IsSA₁ (s : Set ℝ) : Prop := IsSA {v : Unit → ℝ | v () ∈ s}

/-- A function `ℝ → ℝ` is semialgebraic on `D ⊆ ℝ`. -/
def IsSAFun₁₁ (D : Set ℝ) (g : ℝ → ℝ) : Prop :=
  IsSAFunOn₁ {v : Unit → ℝ | v () ∈ D} (fun v => g (v ()))

/-! ## Basic closure properties -/

section Closure

variable {α β : Type}

theorem isSA_univ : IsSA (Set.univ : Set (α → ℝ)) := by
  refine ⟨.zero 0, fun v => ?_⟩
  simp [Fml.Holds]

theorem isSA_empty : IsSA (∅ : Set (α → ℝ)) := by
  refine ⟨.pos 0, fun v => ?_⟩
  simp [Fml.Holds]

theorem IsSA.compl {s : Set (α → ℝ)} (h : IsSA s) : IsSA sᶜ := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨.not φ, fun v => by simp [Fml.Holds, hφ]⟩

theorem IsSA.inter {s t : Set (α → ℝ)} (hs : IsSA s) (ht : IsSA t) : IsSA (s ∩ t) := by
  obtain ⟨φ, hφ⟩ := hs
  obtain ⟨ψ, hψ⟩ := ht
  exact ⟨.and φ ψ, fun v => by simp [Fml.Holds, hφ, hψ]⟩

theorem IsSA.union {s t : Set (α → ℝ)} (hs : IsSA s) (ht : IsSA t) : IsSA (s ∪ t) := by
  have := (hs.compl.inter ht.compl).compl
  simpa [Set.compl_inter, compl_compl] using this

theorem IsSA.diff {s t : Set (α → ℝ)} (hs : IsSA s) (ht : IsSA t) : IsSA (s \ t) :=
  hs.inter ht.compl

theorem isSA_pos (p : MvPolynomial α ℝ) : IsSA {v : α → ℝ | 0 < eval v p} :=
  ⟨.pos p, fun _ => Iff.rfl⟩

theorem isSA_zero (p : MvPolynomial α ℝ) : IsSA {v : α → ℝ | eval v p = 0} :=
  ⟨.zero p, fun _ => Iff.rfl⟩

theorem isSA_nonneg (p : MvPolynomial α ℝ) : IsSA {v : α → ℝ | 0 ≤ eval v p} := by
  have := (isSA_pos p).union (isSA_zero p)
  convert this using 1
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · intro h; rcases h.lt_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr h.symm
  · rintro (h | h)
    · exact h.le
    · exact h.symm ▸ le_refl _

/-- Existential quantification over the variable `none`. -/
theorem IsSA.exists_option {s : Set (Option α → ℝ)} (h : IsSA s) :
    IsSA {v : α → ℝ | ∃ a : ℝ, extendVal a v ∈ s} := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨.ex φ, fun v => by simp [Fml.Holds, hφ]⟩

/-- Substitution of polynomials for the variables of a formula. -/
def Fml.subst : {α β : Type} → Fml β → (β → MvPolynomial α ℝ) → Fml α
  | _, _, .pos p, σ => .pos (bind₁ σ p)
  | _, _, .zero p, σ => .zero (bind₁ σ p)
  | _, _, .not φ, σ => .not (φ.subst σ)
  | _, _, .and φ ψ, σ => .and (φ.subst σ) (ψ.subst σ)
  | _, _, .ex φ, σ =>
      .ex (φ.subst (fun o => o.elim (X none) (fun b => rename some (σ b))))

theorem eval_bind₁' {α β : Type} (v : α → ℝ) (σ : β → MvPolynomial α ℝ)
    (p : MvPolynomial β ℝ) : eval v (bind₁ σ p) = eval (fun b => eval v (σ b)) p :=
  eval₂Hom_bind₁ _ _ _ _

theorem Fml.holds_subst {α β : Type} (φ : Fml β) (σ : β → MvPolynomial α ℝ) (v : α → ℝ) :
    (φ.subst σ).Holds v ↔ φ.Holds (fun b => eval v (σ b)) := by
  induction φ generalizing α with
  | pos p => simp only [Fml.subst, Fml.Holds, eval_bind₁']
  | zero p => simp only [Fml.subst, Fml.Holds, eval_bind₁']
  | not φ ih => simp only [Fml.subst, Fml.Holds, ih]
  | and φ ψ ih₁ ih₂ => simp only [Fml.subst, Fml.Holds, ih₁, ih₂]
  | ex φ ih =>
    simp only [Fml.subst, Fml.Holds, ih]
    refine exists_congr fun a => ?_
    have : (fun o : Option _ => eval (extendVal a v)
        (Option.elim o (X none) fun b => rename some (σ b))) =
        extendVal a (fun b => eval v (σ b)) := by
      funext o
      cases o with
      | none => simp [extendVal]
      | some b => simp [extendVal, eval_rename]; rfl
    rw [this]

/-- Preimage of a semialgebraic set under a polynomial map. -/
theorem IsSA.preimage_poly {s : Set (β → ℝ)} (h : IsSA s) (σ : β → MvPolynomial α ℝ) :
    IsSA {v : α → ℝ | (fun b => eval v (σ b)) ∈ s} := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨φ.subst σ, fun v => by rw [Fml.holds_subst, ← hφ]; rfl⟩

/-- Preimage of a semialgebraic set under a renaming of the variables. -/
theorem IsSA.preimage_comp {s : Set (β → ℝ)} (h : IsSA s) (f : β → α) :
    IsSA {v : α → ℝ | v ∘ f ∈ s} := by
  have := h.preimage_poly (fun b => X (f b))
  simp only [MvPolynomial.eval_X] at this
  exact this

/-- Existential quantification over finitely many variables. -/
theorem IsSA.exists_fin : ∀ (n : ℕ) {α : Type} {s : Set (α ⊕ Fin n → ℝ)}, IsSA s →
    IsSA {v : α → ℝ | ∃ z : Fin n → ℝ, Sum.elim v z ∈ s}
  | 0, α, s, h => by
    have := h.preimage_comp (Sum.elim id (Fin.elim0 : Fin 0 → α))
    convert this using 1
    ext v
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨z, hz⟩
      convert hz using 1
      ext (i | i)
      · rfl
      · exact i.elim0
    · intro hv
      refine ⟨Fin.elim0, ?_⟩
      convert hv using 1
      ext (i | i)
      · rfl
      · exact i.elim0
  | n + 1, α, s, h => by
    -- variables of `α ⊕ Fin (n+1)` expressed through `Option (α ⊕ Fin n)`
    let g : α ⊕ Fin (n + 1) → Option (α ⊕ Fin n) :=
      Sum.elim (fun a => some (Sum.inl a)) (Fin.cases none fun i => some (Sum.inr i))
    have ht := h.preimage_comp g
    have h1 := ht.exists_option
    have h2 := IsSA.exists_fin n h1
    convert h2 using 1
    ext v
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨Fin.tail z, z 0, ?_⟩
      convert hz using 1
      ext (i | i)
      · rfl
      · refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    · rintro ⟨z, a, hz⟩
      refine ⟨Fin.cons a z, ?_⟩
      convert hz using 1
      ext (i | i)
      · rfl
      · refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem IsSA.exists_sum {γ : Type} [Finite γ] {s : Set (α ⊕ γ → ℝ)} (h : IsSA s) :
    IsSA {v : α → ℝ | ∃ z : γ → ℝ, Sum.elim v z ∈ s} := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin γ
  have h' := h.preimage_comp (Sum.map id e)
  have := IsSA.exists_fin n h'
  convert this using 1
  ext v
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z ∘ e.symm, ?_⟩
    convert hz using 1
    ext (i | i)
    · rfl
    · simp
  · rintro ⟨z, hz⟩
    refine ⟨z ∘ e, ?_⟩
    convert hz using 1
    ext (i | i) <;> rfl

/-- Universal quantification over finitely many variables. -/
theorem IsSA.forall_sum {γ : Type} [Finite γ] {s : Set (α ⊕ γ → ℝ)} (h : IsSA s) :
    IsSA {v : α → ℝ | ∀ z : γ → ℝ, Sum.elim v z ∈ s} := by
  have := (h.compl.exists_sum (γ := γ)).compl
  convert this using 1
  ext v
  simp

/-- Image of a semialgebraic set under a coordinate projection. -/
theorem IsSA.image_inl {γ : Type} [Finite γ] {s : Set (α ⊕ γ → ℝ)} (h : IsSA s) :
    IsSA ((fun v => v ∘ Sum.inl) '' s) := by
  have := h.exists_sum (γ := γ)
  convert this using 1
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u ∘ Sum.inr, ?_⟩
    convert hu using 1
    ext (i | i) <;> rfl
  · rintro ⟨z, hz⟩
    exact ⟨_, hz, rfl⟩

end Closure

end ClassSep
