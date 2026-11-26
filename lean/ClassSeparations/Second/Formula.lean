import ClassSeparations.SA.Complexity

/-!
# Formula builders with complexity bookkeeping (for Lemma 6.3 (d))

Derived connectives and quantifier blocks for first-order formulas `Fml`, with their semantics
and the effect on the complexity measures of `ClassSeparations.SA.Complexity`:

* `fren f φ`: renaming of the free variables;
* `ftt`, `fff`, `for_`, `fimp`, `fnonneg`: truth, falsity, disjunction, implication, `p ≥ 0`;
* `fandL`, `forL`: conjunction and disjunction of a list; `fandF`, `forF`: of a finite family;
* `fexN`, `fexT`, `fallT`: a block of existential (universal) quantifiers over `Fin n` or a
  finite type.

For the number of quantifier blocks we use the predicate `BB φ e a`: the pair
`φ.blockPair` is bounded componentwise by `(e, a)`.
-/

noncomputable section

open MvPolynomial

namespace ClassSep

namespace SetupAux

/-! ### Renaming -/

/-- Rename the free variables of a formula. -/
def fren : {α β : Type} → (α → β) → Fml α → Fml β
  | _, _, f, .pos p => .pos (rename f p)
  | _, _, f, .zero p => .zero (rename f p)
  | _, _, f, .not φ => .not (fren f φ)
  | _, _, f, .and φ ψ => .and (fren f φ) (fren f ψ)
  | _, _, f, .ex φ => .ex (fren (Option.map f) φ)

theorem extendVal_comp_map {α β : Type} (f : α → β) (a : ℝ) (v : β → ℝ) :
    extendVal a v ∘ Option.map f = extendVal a (v ∘ f) := by
  funext o; cases o <;> rfl

theorem holds_fren {α β : Type} (f : α → β) (φ : Fml α) (v : β → ℝ) :
    (fren f φ).Holds v ↔ φ.Holds (v ∘ f) := by
  induction φ generalizing β with
  | pos p => simp only [fren, Fml.Holds, eval_rename]
  | zero p => simp only [fren, Fml.Holds, eval_rename]
  | not φ ih => simp only [fren, Fml.Holds, ih]
  | and φ ψ ih₁ ih₂ => simp only [fren, Fml.Holds, ih₁, ih₂]
  | ex φ ih =>
    simp only [fren, Fml.Holds, ih, extendVal_comp_map]

theorem size_fren {α β : Type} (f : α → β) (φ : Fml α) : (fren f φ).size = φ.size := by
  induction φ generalizing β with
  | pos p => rfl
  | zero p => rfl
  | not φ ih => simp only [fren, Fml.size, ih]
  | and φ ψ ih₁ ih₂ => simp only [fren, Fml.size, ih₁, ih₂]
  | ex φ ih => simp only [fren, Fml.size, ih]

theorem numBound_fren {α β : Type} (f : α → β) (φ : Fml α) :
    (fren f φ).numBound = φ.numBound := by
  induction φ generalizing β with
  | pos p => rfl
  | zero p => rfl
  | not φ ih => simp only [fren, Fml.numBound, ih]
  | and φ ψ ih₁ ih₂ => simp only [fren, Fml.numBound, ih₁, ih₂]
  | ex φ ih => simp only [fren, Fml.numBound, ih]

theorem blockPair_fren {α β : Type} (f : α → β) (φ : Fml α) :
    (fren f φ).blockPair = φ.blockPair := by
  induction φ generalizing β with
  | pos p => rfl
  | zero p => rfl
  | not φ ih => simp only [fren, Fml.blockPair, ih]
  | and φ ψ ih₁ ih₂ => simp only [fren, Fml.blockPair, ih₁, ih₂]
  | ex φ ih => simp only [fren, Fml.blockPair, ih]

theorem maxDeg_fren_le {α β : Type} (f : α → β) (φ : Fml α) :
    (fren f φ).maxDeg ≤ φ.maxDeg := by
  induction φ generalizing β with
  | pos p => exact totalDegree_rename_le f p
  | zero p => exact totalDegree_rename_le f p
  | not φ ih => simpa only [fren, Fml.maxDeg] using ih f
  | and φ ψ ih₁ ih₂ =>
    simp only [fren, Fml.maxDeg]
    exact max_le_max (ih₁ f) (ih₂ f)
  | ex φ ih => simpa only [fren, Fml.maxDeg] using ih (Option.map f)

/-! ### Derived connectives -/

/-- Truth. -/
def ftt {α : Type} : Fml α := .zero 0

/-- Falsity. -/
def fff {α : Type} : Fml α := .pos 0

/-- Disjunction. -/
def for_ {α : Type} (φ ψ : Fml α) : Fml α := .not (.and (.not φ) (.not ψ))

/-- Implication. -/
def fimp {α : Type} (φ ψ : Fml α) : Fml α := .not (.and φ (.not ψ))

/-- `p ≥ 0`. -/
def fnonneg {α : Type} (p : MvPolynomial α ℝ) : Fml α := for_ (.pos p) (.zero p)

/-- Conjunction of a list. -/
def fandL {α : Type} : List (Fml α) → Fml α
  | [] => ftt
  | φ :: l => .and φ (fandL l)

/-- Disjunction of a list. -/
def forL {α : Type} : List (Fml α) → Fml α
  | [] => fff
  | φ :: l => for_ φ (forL l)

section Sem

variable {α : Type} (v : α → ℝ)

@[simp] theorem holds_ftt : (ftt : Fml α).Holds v := by simp [ftt, Fml.Holds]

@[simp] theorem holds_fff : ¬ (fff : Fml α).Holds v := by simp [fff, Fml.Holds]

@[simp] theorem holds_for (φ ψ : Fml α) : (for_ φ ψ).Holds v ↔ φ.Holds v ∨ ψ.Holds v := by
  simp only [for_, Fml.Holds]; tauto

@[simp] theorem holds_fimp (φ ψ : Fml α) : (fimp φ ψ).Holds v ↔ (φ.Holds v → ψ.Holds v) := by
  simp only [fimp, Fml.Holds]; tauto

@[simp] theorem holds_fnonneg (p : MvPolynomial α ℝ) :
    (fnonneg p).Holds v ↔ 0 ≤ eval v p := by
  simp only [fnonneg, holds_for, Fml.Holds]
  constructor
  · rintro (h | h)
    · exact h.le
    · exact h.ge
  · intro h
    rcases h.lt_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr h.symm

@[simp] theorem holds_fandL (l : List (Fml α)) :
    (fandL l).Holds v ↔ ∀ φ ∈ l, φ.Holds v := by
  induction l with
  | nil => simp [fandL]
  | cons φ l ih => simp [fandL, Fml.Holds, ih]

@[simp] theorem holds_forL (l : List (Fml α)) :
    (forL l).Holds v ↔ ∃ φ ∈ l, φ.Holds v := by
  induction l with
  | nil => simp [forL]
  | cons φ l ih => simp [forL, ih]

end Sem

/-! ### Measures of the derived connectives -/

section Measures

variable {α : Type}

@[simp] theorem size_ftt : (ftt : Fml α).size = 1 := rfl
@[simp] theorem size_fff : (fff : Fml α).size = 1 := rfl
@[simp] theorem size_for (φ ψ : Fml α) : (for_ φ ψ).size = φ.size + ψ.size := rfl
@[simp] theorem size_fimp (φ ψ : Fml α) : (fimp φ ψ).size = φ.size + ψ.size := rfl
@[simp] theorem size_fnonneg (p : MvPolynomial α ℝ) : (fnonneg p).size = 2 := rfl

@[simp] theorem numBound_ftt : (ftt : Fml α).numBound = 0 := rfl
@[simp] theorem numBound_fff : (fff : Fml α).numBound = 0 := rfl
@[simp] theorem numBound_for (φ ψ : Fml α) : (for_ φ ψ).numBound = φ.numBound + ψ.numBound := rfl
@[simp] theorem numBound_fimp (φ ψ : Fml α) :
    (fimp φ ψ).numBound = φ.numBound + ψ.numBound := rfl
@[simp] theorem numBound_fnonneg (p : MvPolynomial α ℝ) : (fnonneg p).numBound = 0 := rfl

@[simp] theorem maxDeg_ftt : (ftt : Fml α).maxDeg = 0 := by simp [ftt, Fml.maxDeg]
@[simp] theorem maxDeg_fff : (fff : Fml α).maxDeg = 0 := by simp [fff, Fml.maxDeg]
@[simp] theorem maxDeg_for (φ ψ : Fml α) : (for_ φ ψ).maxDeg = max φ.maxDeg ψ.maxDeg := rfl
@[simp] theorem maxDeg_fimp (φ ψ : Fml α) : (fimp φ ψ).maxDeg = max φ.maxDeg ψ.maxDeg := rfl
@[simp] theorem maxDeg_fnonneg (p : MvPolynomial α ℝ) : (fnonneg p).maxDeg = p.totalDegree := by
  simp [fnonneg, Fml.maxDeg]

theorem size_fandL (l : List (Fml α)) : (fandL l).size = (l.map Fml.size).sum + 1 := by
  induction l with
  | nil => rfl
  | cons φ l ih => simp only [fandL, Fml.size, ih, List.map_cons, List.sum_cons]; ring

theorem size_forL (l : List (Fml α)) : (forL l).size = (l.map Fml.size).sum + 1 := by
  induction l with
  | nil => rfl
  | cons φ l ih => simp only [forL, size_for, ih, List.map_cons, List.sum_cons]; ring

theorem numBound_fandL (l : List (Fml α)) :
    (fandL l).numBound = (l.map Fml.numBound).sum := by
  induction l with
  | nil => rfl
  | cons φ l ih => simp only [fandL, Fml.numBound, ih, List.map_cons, List.sum_cons]

theorem numBound_forL (l : List (Fml α)) :
    (forL l).numBound = (l.map Fml.numBound).sum := by
  induction l with
  | nil => rfl
  | cons φ l ih => simp only [forL, numBound_for, ih, List.map_cons, List.sum_cons]

theorem maxDeg_fandL_le (l : List (Fml α)) {d : ℕ} (h : ∀ φ ∈ l, φ.maxDeg ≤ d) :
    (fandL l).maxDeg ≤ d := by
  induction l with
  | nil => simp [fandL]
  | cons φ l ih =>
    simp only [fandL, Fml.maxDeg]
    exact max_le (h φ (by simp)) (ih fun ψ hψ => h ψ (by simp [hψ]))

theorem maxDeg_forL_le (l : List (Fml α)) {d : ℕ} (h : ∀ φ ∈ l, φ.maxDeg ≤ d) :
    (forL l).maxDeg ≤ d := by
  induction l with
  | nil => simp [forL]
  | cons φ l ih =>
    simp only [forL, maxDeg_for]
    exact max_le (h φ (by simp)) (ih fun ψ hψ => h ψ (by simp [hψ]))

theorem sum_map_le_of_forall (l : List (Fml α)) (g : Fml α → ℕ) {s : ℕ}
    (h : ∀ φ ∈ l, g φ ≤ s) : (l.map g).sum ≤ l.length * s := by
  induction l with
  | nil => simp
  | cons φ l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h φ (by simp)
    have h2 := ih fun ψ hψ => h ψ (by simp [hψ])
    nlinarith

end Measures

/-! ### Finite families -/

/-- Conjunction of a finite family. -/
def fandF {α : Type} (ι : Type) [Fintype ι] (F : ι → Fml α) : Fml α :=
  fandL (List.ofFn fun i : Fin (Fintype.card ι) => F ((Fintype.equivFin ι).symm i))

/-- Disjunction of a finite family. -/
def forF {α : Type} (ι : Type) [Fintype ι] (F : ι → Fml α) : Fml α :=
  forL (List.ofFn fun i : Fin (Fintype.card ι) => F ((Fintype.equivFin ι).symm i))

section Family

variable {α ι : Type} [Fintype ι] (F : ι → Fml α)

@[simp] theorem holds_fandF (v : α → ℝ) : (fandF ι F).Holds v ↔ ∀ i, (F i).Holds v := by
  simp only [fandF, holds_fandL, List.mem_ofFn, forall_exists_index]
  constructor
  · intro h i
    exact h _ ((Fintype.equivFin ι) i) (by simp)
  · rintro h φ i rfl
    exact h _

@[simp] theorem holds_forF (v : α → ℝ) : (forF ι F).Holds v ↔ ∃ i, (F i).Holds v := by
  simp only [forF, holds_forL, List.mem_ofFn]
  constructor
  · rintro ⟨φ, ⟨i, rfl⟩, h⟩
    exact ⟨_, h⟩
  · rintro ⟨i, h⟩
    exact ⟨_, ⟨(Fintype.equivFin ι) i, by simp⟩, h⟩

theorem size_fandF_le {s : ℕ} (h : ∀ i, (F i).size ≤ s) :
    (fandF ι F).size ≤ Fintype.card ι * s + 1 := by
  rw [fandF, size_fandL]
  have := sum_map_le_of_forall (List.ofFn fun i : Fin (Fintype.card ι) =>
    F ((Fintype.equivFin ι).symm i)) Fml.size (s := s) (by
      intro φ hφ
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hφ
      exact h _)
  rw [List.length_ofFn] at this
  omega

theorem size_forF_le {s : ℕ} (h : ∀ i, (F i).size ≤ s) :
    (forF ι F).size ≤ Fintype.card ι * s + 1 := by
  rw [forF, size_forL]
  have := sum_map_le_of_forall (List.ofFn fun i : Fin (Fintype.card ι) =>
    F ((Fintype.equivFin ι).symm i)) Fml.size (s := s) (by
      intro φ hφ
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hφ
      exact h _)
  rw [List.length_ofFn] at this
  omega

theorem numBound_fandF_le {s : ℕ} (h : ∀ i, (F i).numBound ≤ s) :
    (fandF ι F).numBound ≤ Fintype.card ι * s := by
  rw [fandF, numBound_fandL]
  have := sum_map_le_of_forall (List.ofFn fun i : Fin (Fintype.card ι) =>
    F ((Fintype.equivFin ι).symm i)) Fml.numBound (s := s) (by
      intro φ hφ
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hφ
      exact h _)
  rwa [List.length_ofFn] at this

theorem numBound_forF_le {s : ℕ} (h : ∀ i, (F i).numBound ≤ s) :
    (forF ι F).numBound ≤ Fintype.card ι * s := by
  rw [forF, numBound_forL]
  have := sum_map_le_of_forall (List.ofFn fun i : Fin (Fintype.card ι) =>
    F ((Fintype.equivFin ι).symm i)) Fml.numBound (s := s) (by
      intro φ hφ
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hφ
      exact h _)
  rwa [List.length_ofFn] at this

theorem maxDeg_fandF_le {d : ℕ} (h : ∀ i, (F i).maxDeg ≤ d) : (fandF ι F).maxDeg ≤ d :=
  maxDeg_fandL_le _ fun φ hφ => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hφ
    exact h _

theorem maxDeg_forF_le {d : ℕ} (h : ∀ i, (F i).maxDeg ≤ d) : (forF ι F).maxDeg ≤ d :=
  maxDeg_forL_le _ fun φ hφ => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hφ
    exact h _

end Family

/-! ### Quantifier blocks -/

/-- The renaming used to peel off the first variable of a block. -/
def peel (α : Type) (n : ℕ) : α ⊕ Fin (n + 1) → Option (α ⊕ Fin n) :=
  Sum.elim (fun a => some (Sum.inl a)) (Fin.cases none fun i => some (Sum.inr i))

/-- A block of `n` existential quantifiers. -/
def fexN : (n : ℕ) → {α : Type} → Fml (α ⊕ Fin n) → Fml α
  | 0, _, φ => fren (Sum.elim id Fin.elim0) φ
  | n + 1, α, φ => fexN n (.ex (fren (peel α n) φ))

theorem holds_fexN : ∀ (n : ℕ) {α : Type} (φ : Fml (α ⊕ Fin n)) (v : α → ℝ),
    (fexN n φ).Holds v ↔ ∃ z : Fin n → ℝ, φ.Holds (Sum.elim v z)
  | 0, α, φ, v => by
    rw [fexN, holds_fren]
    have : ∀ z : Fin 0 → ℝ, v ∘ Sum.elim id Fin.elim0 = Sum.elim v z := by
      intro z; funext i; rcases i with i | i
      · rfl
      · exact i.elim0
    constructor
    · intro h; exact ⟨Fin.elim0, by rw [← this]; exact h⟩
    · rintro ⟨z, h⟩; rw [this z]; exact h
  | n + 1, α, φ, v => by
    rw [fexN, holds_fexN n]
    simp only [Fml.Holds, holds_fren]
    have key : ∀ (z : Fin n → ℝ) (a : ℝ),
        extendVal a (Sum.elim v z) ∘ peel α n = Sum.elim v (Fin.cons a z) := by
      intro z a; funext i
      rcases i with i | i
      · rfl
      · refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    constructor
    · rintro ⟨z, a, h⟩
      exact ⟨Fin.cons a z, by rw [← key]; exact h⟩
    · rintro ⟨z, h⟩
      refine ⟨Fin.tail z, z 0, ?_⟩
      rw [key, Fin.cons_self_tail]
      exact h

theorem size_fexN : ∀ (n : ℕ) {α : Type} (φ : Fml (α ⊕ Fin n)), (fexN n φ).size = φ.size
  | 0, _, φ => size_fren _ φ
  | n + 1, α, φ => by rw [fexN, size_fexN n, Fml.size, size_fren]

theorem numBound_fexN : ∀ (n : ℕ) {α : Type} (φ : Fml (α ⊕ Fin n)),
    (fexN n φ).numBound = φ.numBound + n
  | 0, _, φ => by rw [fexN, numBound_fren]; rfl
  | n + 1, α, φ => by rw [fexN, numBound_fexN n, Fml.numBound, numBound_fren]; ring

theorem maxDeg_fexN_le : ∀ (n : ℕ) {α : Type} (φ : Fml (α ⊕ Fin n)),
    (fexN n φ).maxDeg ≤ φ.maxDeg
  | 0, _, φ => maxDeg_fren_le _ φ
  | n + 1, α, φ => by
    rw [fexN]
    exact (maxDeg_fexN_le n _).trans (maxDeg_fren_le _ φ)

/-- A block of existential quantifiers over a finite type. -/
def fexT {α : Type} (γ : Type) [Fintype γ] (φ : Fml (α ⊕ γ)) : Fml α :=
  fexN (Fintype.card γ) (fren (Sum.map id (Fintype.equivFin γ)) φ)

/-- A block of universal quantifiers over a finite type. -/
def fallT {α : Type} (γ : Type) [Fintype γ] (φ : Fml (α ⊕ γ)) : Fml α :=
  .not (fexT γ (.not φ))

section Blocks

variable {α γ : Type} [Fintype γ]

@[simp] theorem holds_fexT (φ : Fml (α ⊕ γ)) (v : α → ℝ) :
    (fexT γ φ).Holds v ↔ ∃ z : γ → ℝ, φ.Holds (Sum.elim v z) := by
  rw [fexT, holds_fexN]
  simp only [holds_fren]
  have key : ∀ z : Fin (Fintype.card γ) → ℝ,
      Sum.elim v z ∘ Sum.map id (Fintype.equivFin γ) =
        Sum.elim v (z ∘ (Fintype.equivFin γ)) := by
    intro z; funext i; rcases i with i | i <;> rfl
  constructor
  · rintro ⟨z, h⟩
    exact ⟨_, by rw [← key]; exact h⟩
  · rintro ⟨z, h⟩
    refine ⟨z ∘ (Fintype.equivFin γ).symm, ?_⟩
    rw [key]
    convert h using 2
    funext i; simp

@[simp] theorem holds_fallT (φ : Fml (α ⊕ γ)) (v : α → ℝ) :
    (fallT γ φ).Holds v ↔ ∀ z : γ → ℝ, φ.Holds (Sum.elim v z) := by
  simp [fallT, Fml.Holds]

theorem size_fexT (φ : Fml (α ⊕ γ)) : (fexT γ φ).size = φ.size := by
  rw [fexT, size_fexN, size_fren]

theorem size_fallT (φ : Fml (α ⊕ γ)) : (fallT γ φ).size = φ.size := by
  rw [fallT, Fml.size, size_fexT]; rfl

theorem numBound_fexT (φ : Fml (α ⊕ γ)) :
    (fexT γ φ).numBound = φ.numBound + Fintype.card γ := by
  rw [fexT, numBound_fexN, numBound_fren]

theorem numBound_fallT (φ : Fml (α ⊕ γ)) :
    (fallT γ φ).numBound = φ.numBound + Fintype.card γ := by
  rw [fallT, Fml.numBound, numBound_fexT]; rfl

theorem maxDeg_fexT_le (φ : Fml (α ⊕ γ)) : (fexT γ φ).maxDeg ≤ φ.maxDeg :=
  (maxDeg_fexN_le _ _).trans (maxDeg_fren_le _ _)

theorem maxDeg_fallT_le (φ : Fml (α ⊕ γ)) : (fallT γ φ).maxDeg ≤ φ.maxDeg :=
  maxDeg_fexT_le (Fml.not φ)

end Blocks

/-! ### Bounds for the number of quantifier blocks -/

/-- The block pair of `φ` is at most `(e, a)` componentwise. -/
def BB {α : Type} (φ : Fml α) (e a : ℕ) : Prop := φ.blockPair.1 ≤ e ∧ φ.blockPair.2 ≤ a

namespace BB

variable {α : Type}

theorem pos (p : MvPolynomial α ℝ) (e a : ℕ) : BB (.pos p) e a := by
  simp [BB, Fml.blockPair]

theorem zero (p : MvPolynomial α ℝ) (e a : ℕ) : BB (.zero p) e a := by
  simp [BB, Fml.blockPair]

theorem not {φ : Fml α} {e a : ℕ} (h : BB φ e a) : BB (.not φ) a e := ⟨h.2, h.1⟩

theorem and {φ ψ : Fml α} {e a : ℕ} (h₁ : BB φ e a) (h₂ : BB ψ e a) : BB (.and φ ψ) e a :=
  ⟨max_le h₁.1 h₂.1, max_le h₁.2 h₂.2⟩

theorem ex {φ : Fml (Option α)} {e a : ℕ} (h : BB φ e a) (he : 1 ≤ e) : BB (.ex φ) e (e + 1) :=
  ⟨max_le he h.1, Nat.add_le_add_right (max_le he h.1) 1⟩

theorem mono {φ : Fml α} {e a e' a' : ℕ} (h : BB φ e a) (he : e ≤ e') (ha : a ≤ a') :
    BB φ e' a' := ⟨h.1.trans he, h.2.trans ha⟩

theorem fren {β : Type} (f : α → β) {φ : Fml α} {e a : ℕ} (h : BB φ e a) :
    BB (SetupAux.fren f φ) e a := by
  unfold BB; rw [blockPair_fren]; exact h

theorem ftt (e a : ℕ) : BB (ftt : Fml α) e a := zero _ e a
theorem fff (e a : ℕ) : BB (fff : Fml α) e a := pos _ e a

theorem for_ {φ ψ : Fml α} {e a : ℕ} (h₁ : BB φ e a) (h₂ : BB ψ e a) : BB (for_ φ ψ) e a :=
  (h₁.not.and h₂.not).not

theorem fimp {φ ψ : Fml α} {e a : ℕ} (h₁ : BB φ a e) (h₂ : BB ψ e a) : BB (fimp φ ψ) e a :=
  (h₁.and h₂.not).not

theorem fnonneg (p : MvPolynomial α ℝ) (e a : ℕ) : BB (fnonneg p) e a :=
  for_ (pos p e a) (zero p e a)

theorem fandL {l : List (Fml α)} {e a : ℕ} (h : ∀ φ ∈ l, BB φ e a) : BB (fandL l) e a := by
  induction l with
  | nil => exact ftt e a
  | cons φ l ih => exact (h φ (by simp)).and (ih fun ψ hψ => h ψ (by simp [hψ]))

theorem forL {l : List (Fml α)} {e a : ℕ} (h : ∀ φ ∈ l, BB φ e a) : BB (forL l) e a := by
  induction l with
  | nil => exact fff e a
  | cons φ l ih => exact (h φ (by simp)).for_ (ih fun ψ hψ => h ψ (by simp [hψ]))

theorem fandF {ι : Type} [Fintype ι] {F : ι → Fml α} {e a : ℕ} (h : ∀ i, BB (F i) e a) :
    BB (fandF ι F) e a :=
  fandL fun φ hφ => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hφ
    exact h _

theorem forF {ι : Type} [Fintype ι] {F : ι → Fml α} {e a : ℕ} (h : ∀ i, BB (F i) e a) :
    BB (forF ι F) e a :=
  forL fun φ hφ => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hφ
    exact h _

theorem fexN : ∀ (n : ℕ) {α : Type} {φ : Fml (α ⊕ Fin n)} {e a : ℕ}, BB φ e a → 1 ≤ e →
    a ≤ e + 1 → BB (SetupAux.fexN n φ) e (e + 1)
  | 0, _, φ, e, a, h, _, ha => (h.fren _).mono le_rfl ha
  | n + 1, α, φ, e, a, h, he, ha => by
    rw [SetupAux.fexN]
    exact fexN n ((h.fren _).ex he) he le_rfl

theorem fexT {γ : Type} [Fintype γ] {φ : Fml (α ⊕ γ)} {e a : ℕ} (h : BB φ e a) (he : 1 ≤ e)
    (ha : a ≤ e + 1) : BB (SetupAux.fexT γ φ) e (e + 1) :=
  fexN _ (h.fren _) he ha

theorem fallT {γ : Type} [Fintype γ] {φ : Fml (α ⊕ γ)} {e a : ℕ} (h : BB φ e a) (ha : 1 ≤ a)
    (he : e ≤ a + 1) : BB (SetupAux.fallT γ φ) (a + 1) a :=
  (fexT h.not ha he).not

theorem blocks_le {φ : Fml α} {e a : ℕ} (h : BB φ e a) : φ.blocks ≤ e := h.1

end BB

end SetupAux

end ClassSep
