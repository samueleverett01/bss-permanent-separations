import ClassSeparations.SA.Facts

/-!
# Consequences of (S1)–(S8) used throughout the paper

Instances of (S1) (sets and functions defined by first-order formulas are semialgebraic) and
standard consequences of the facts in `SAFacts` that are used repeatedly.

The instances of (S1) are proved by exhibiting first-order definitions.  To keep the
bookkeeping manageable we first set up a small toolkit (namespace `ClassSep.FO`): polynomial
functions of the coordinates (`FO.IsPolyFn`, with the tactic `poly_fn`), atomic sign conditions,
the propositional connectives, and quantifiers over finitely many real variables, all stated
for sets written in set-builder notation.
-/

noncomputable section

open Set Filter Topology

namespace ClassSep

variable {α β : Type}

/-! ## A toolkit for first-order definitions -/

namespace FO

/-- `f` is a polynomial function of the coordinates. -/
def IsPolyFn {ι : Type} (f : (ι → ℝ) → ℝ) : Prop :=
  ∃ p : MvPolynomial ι ℝ, ∀ u, f u = MvPolynomial.eval u p

namespace IsPolyFn

variable {ι κ : Type} {f g : (ι → ℝ) → ℝ}

theorem const (c : ℝ) : IsPolyFn (fun _ : ι → ℝ => c) :=
  ⟨MvPolynomial.C c, fun u => by simp⟩

theorem coord (i : ι) : IsPolyFn (fun u : ι → ℝ => u i) :=
  ⟨MvPolynomial.X i, fun u => by simp⟩

theorem add (hf : IsPolyFn f) (hg : IsPolyFn g) : IsPolyFn (fun u => f u + g u) := by
  obtain ⟨p, hp⟩ := hf; obtain ⟨q, hq⟩ := hg
  exact ⟨p + q, fun u => by simp [hp, hq]⟩

theorem sub (hf : IsPolyFn f) (hg : IsPolyFn g) : IsPolyFn (fun u => f u - g u) := by
  obtain ⟨p, hp⟩ := hf; obtain ⟨q, hq⟩ := hg
  exact ⟨p - q, fun u => by simp [hp, hq]⟩

theorem mul (hf : IsPolyFn f) (hg : IsPolyFn g) : IsPolyFn (fun u => f u * g u) := by
  obtain ⟨p, hp⟩ := hf; obtain ⟨q, hq⟩ := hg
  exact ⟨p * q, fun u => by simp [hp, hq]⟩

theorem neg (hf : IsPolyFn f) : IsPolyFn (fun u => - f u) := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨-p, fun u => by simp [hp]⟩

theorem pow (hf : IsPolyFn f) (n : ℕ) : IsPolyFn (fun u => f u ^ n) := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨p ^ n, fun u => by simp [hp]⟩

/-- A polynomial evaluated at polynomial functions is a polynomial function. -/
theorem eval_comp {F : (κ → ℝ) → ι → ℝ} (hF : ∀ i, IsPolyFn (fun u => F u i))
    (p : MvPolynomial ι ℝ) : IsPolyFn (fun u => MvPolynomial.eval (F u) p) := by
  choose q hq using hF
  refine ⟨MvPolynomial.bind₁ q p, fun u => ?_⟩
  rw [eval_bind₁']
  have : (fun i => MvPolynomial.eval u (q i)) = F u := funext fun i => (hq i u).symm
  rw [this]

end IsPolyFn

/-- Tactic proving `FO.IsPolyFn` goals for explicit polynomial expressions in the coordinates. -/
macro "poly_fn" : tactic =>
  `(tactic| (
    try simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Function.comp_apply, Sum.elim_inl, Sum.elim_inr]
    repeat' first
      | exact IsPolyFn.const _
      | exact IsPolyFn.coord _
      | apply IsPolyFn.add
      | apply IsPolyFn.sub
      | apply IsPolyFn.mul
      | apply IsPolyFn.neg
      | apply IsPolyFn.pow))

variable {ι κ : Type}

theorem isSA_lt {f g : (ι → ℝ) → ℝ} (hf : IsPolyFn f) (hg : IsPolyFn g) :
    IsSA {u | f u < g u} := by
  obtain ⟨p, hp⟩ := hf; obtain ⟨q, hq⟩ := hg
  have := isSA_pos (q - p)
  convert this using 1
  ext u
  simp [hp, hq]

theorem isSA_le {f g : (ι → ℝ) → ℝ} (hf : IsPolyFn f) (hg : IsPolyFn g) :
    IsSA {u | f u ≤ g u} := by
  obtain ⟨p, hp⟩ := hf; obtain ⟨q, hq⟩ := hg
  have := isSA_nonneg (q - p)
  convert this using 1
  ext u
  simp [hp, hq]

theorem isSA_eq {f g : (ι → ℝ) → ℝ} (hf : IsPolyFn f) (hg : IsPolyFn g) :
    IsSA {u | f u = g u} := by
  obtain ⟨p, hp⟩ := hf; obtain ⟨q, hq⟩ := hg
  have := isSA_zero (p - q)
  convert this using 1
  ext u
  simp [hp, hq, sub_eq_zero]

theorem isSA_and {P Q : (ι → ℝ) → Prop} (hP : IsSA {u | P u}) (hQ : IsSA {u | Q u}) :
    IsSA {u | P u ∧ Q u} :=
  hP.inter hQ

theorem isSA_or {P Q : (ι → ℝ) → Prop} (hP : IsSA {u | P u}) (hQ : IsSA {u | Q u}) :
    IsSA {u | P u ∨ Q u} :=
  hP.union hQ

theorem isSA_not {P : (ι → ℝ) → Prop} (hP : IsSA {u | P u}) : IsSA {u | ¬ P u} :=
  hP.compl

theorem isSA_imp {P Q : (ι → ℝ) → Prop} (hP : IsSA {u | P u}) (hQ : IsSA {u | Q u}) :
    IsSA {u | P u → Q u} := by
  have := hP.compl.union hQ
  convert this using 1
  ext u
  simp [imp_iff_not_or]

theorem isSA_abs_lt {f g : (ι → ℝ) → ℝ} (hf : IsPolyFn f) (hg : IsPolyFn g) :
    IsSA {u | |f u| < g u} := by
  have := isSA_and (isSA_lt hf.neg hg) (isSA_lt hf hg)
  convert this using 1
  ext u
  simp only [mem_ofPred_eq, abs_lt]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, h2⟩

theorem isSA_abs_le {f g : (ι → ℝ) → ℝ} (hf : IsPolyFn f) (hg : IsPolyFn g) :
    IsSA {u | |f u| ≤ g u} := by
  have := isSA_and (isSA_le hf.neg hg) (isSA_le hf hg)
  convert this using 1
  ext u
  simp only [mem_ofPred_eq, abs_le]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, h2⟩

theorem isSA_const_and (p : Prop) {Q : (ι → ℝ) → Prop} (hQ : p → IsSA {u | Q u}) :
    IsSA {u | p ∧ Q u} := by
  by_cases hp : p
  · simpa [hp] using hQ hp
  · simpa [hp] using (isSA_empty : IsSA (∅ : Set (ι → ℝ)))

theorem isSA_biInter_finset {γ : Type*} (t : Finset γ) {s : γ → Set (ι → ℝ)}
    (h : ∀ i ∈ t, IsSA (s i)) : IsSA (⋂ i ∈ t, s i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (isSA_univ : IsSA (univ : Set (ι → ℝ)))
  | insert a t ha ih =>
    rw [Finset.set_biInter_insert]
    exact (h a (Finset.mem_insert_self _ _)).inter
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem isSA_iInter_finite {γ : Type*} [Finite γ] {s : γ → Set (ι → ℝ)}
    (h : ∀ i, IsSA (s i)) : IsSA (⋂ i, s i) := by
  have := Fintype.ofFinite γ
  simpa using isSA_biInter_finset Finset.univ (fun i _ => h i)

theorem isSA_iUnion_finite {γ : Type*} [Finite γ] {s : γ → Set (ι → ℝ)}
    (h : ∀ i, IsSA (s i)) : IsSA (⋃ i, s i) := by
  have := (isSA_iInter_finite (fun i => (h i).compl)).compl
  simpa [compl_iInter] using this

/-- Finite conjunctions. -/
theorem isSA_forall_fin {γ : Type*} [Finite γ] {P : γ → (ι → ℝ) → Prop}
    (h : ∀ c, IsSA {u | P c u}) : IsSA {u | ∀ c, P c u} := by
  rw [ofPred_forall]
  exact isSA_iInter_finite h

/-- Finite disjunctions. -/
theorem isSA_exists_fin {γ : Type*} [Finite γ] {P : γ → (ι → ℝ) → Prop}
    (h : ∀ c, IsSA {u | P c u}) : IsSA {u | ∃ c, P c u} := by
  rw [ofPred_exists]
  exact isSA_iUnion_finite h

/-- Existential quantification over `ℝ^γ`, `γ` finite. -/
theorem isSA_exists_fun {γ : Type} [Finite γ] {P : (ι → ℝ) → (γ → ℝ) → Prop}
    (h : IsSA {w : ι ⊕ γ → ℝ | P (w ∘ Sum.inl) (w ∘ Sum.inr)}) :
    IsSA {u | ∃ z, P u z} := by
  have := h.exists_sum (γ := γ)
  simpa using this

/-- Universal quantification over `ℝ^γ`, `γ` finite. -/
theorem isSA_forall_fun {γ : Type} [Finite γ] {P : (ι → ℝ) → (γ → ℝ) → Prop}
    (h : IsSA {w : ι ⊕ γ → ℝ | P (w ∘ Sum.inl) (w ∘ Sum.inr)}) :
    IsSA {u | ∀ z, P u z} := by
  have := h.forall_sum (γ := γ)
  simpa using this

/-- Existential quantification over `ℝ`. -/
theorem isSA_exists_real {P : (ι → ℝ) → ℝ → Prop}
    (h : IsSA {w : ι ⊕ Unit → ℝ | P (w ∘ Sum.inl) (w (Sum.inr ()))}) :
    IsSA {u | ∃ a, P u a} := by
  have := isSA_exists_fun (P := fun u (z : Unit → ℝ) => P u (z ())) h
  convert this using 1
  ext u
  simp only [mem_ofPred_eq]
  exact ⟨fun ⟨a, ha⟩ => ⟨fun _ => a, ha⟩, fun ⟨z, hz⟩ => ⟨z (), hz⟩⟩

/-- Universal quantification over `ℝ`. -/
theorem isSA_forall_real {P : (ι → ℝ) → ℝ → Prop}
    (h : IsSA {w : ι ⊕ Unit → ℝ | P (w ∘ Sum.inl) (w (Sum.inr ()))}) :
    IsSA {u | ∀ a, P u a} := by
  have := isSA_forall_fun (P := fun u (z : Unit → ℝ) => P u (z ())) h
  convert this using 1
  ext u
  simp only [mem_ofPred_eq]
  exact ⟨fun ha z => ha (z ()), fun hz a => hz (fun _ => a)⟩

end FO

open FO

/-- Preimage of a semialgebraic set under a map with polynomial coordinates. -/
theorem IsSA.preimage_polyFn {ι κ : Type} {s : Set (ι → ℝ)} (hs : IsSA s)
    {F : (κ → ℝ) → ι → ℝ} (hF : ∀ i, IsPolyFn (fun u => F u i)) : IsSA {u | F u ∈ s} := by
  choose q hq using hF
  have := hs.preimage_poly q
  convert this using 1
  ext u
  simp only [mem_ofPred_eq]
  have : F u = fun i => MvPolynomial.eval u (q i) := funext fun i => hq i u
  rw [this]

/-- The basic tool for first-order definitions involving a semialgebraic map `g`: conditions
on `(u, g (F u))`, where `F` is polynomial, define semialgebraic sets. -/
theorem IsSAFunOn.isSA_comp {κ : Type} {D : Set (α → ℝ)} {g : (α → ℝ) → (β → ℝ)} [Finite β]
    (hg : IsSAFunOn D g) {F : (κ → ℝ) → α → ℝ} (hF : ∀ a, IsPolyFn (fun u => F u a))
    {P : (κ → ℝ) → (β → ℝ) → Prop}
    (hP : IsSA {w : κ ⊕ β → ℝ | P (w ∘ Sum.inl) (w ∘ Sum.inr)}) :
    IsSA {u | F u ∈ D ∧ P u (g (F u))} := by
  have h1 : IsSA {w : κ ⊕ β → ℝ | Sum.elim (F (w ∘ Sum.inl)) (w ∘ Sum.inr) ∈
      {v : α ⊕ β → ℝ | v ∘ Sum.inl ∈ D ∧ g (v ∘ Sum.inl) = v ∘ Sum.inr}} := by
    refine hg.2.preimage_polyFn ?_
    rintro (a | b)
    · obtain ⟨p, hp⟩ := hF a
      refine ⟨MvPolynomial.rename Sum.inl p, fun w => ?_⟩
      simp [hp, MvPolynomial.eval_rename]
    · exact IsPolyFn.coord (Sum.inr b)
  have := isSA_exists_fun (P := fun u z => Sum.elim (F u) z ∈
      {v : α ⊕ β → ℝ | v ∘ Sum.inl ∈ D ∧ g (v ∘ Sum.inl) = v ∘ Sum.inr} ∧ P u z)
    (isSA_and h1 hP)
  convert this using 1
  ext u
  simp only [mem_ofPred_eq, Sum.elim_comp_inl, Sum.elim_comp_inr]
  constructor
  · rintro ⟨hD, hP⟩
    exact ⟨g (F u), ⟨hD, rfl⟩, hP⟩
  · rintro ⟨z, ⟨hD, rfl⟩, hP⟩
    exact ⟨hD, hP⟩

/-! ## Semialgebraic functions -/

/-- Polynomial maps are semialgebraic. -/
theorem isSAFunOn_poly [Finite β] (D : Set (α → ℝ)) (hD : IsSA D) (σ : β → MvPolynomial α ℝ) :
    IsSAFunOn D (fun x b => MvPolynomial.eval x (σ b)) := by
  refine ⟨hD, ?_⟩
  have h1 : IsSA {v : α ⊕ β → ℝ | v ∘ Sum.inl ∈ D} := hD.preimage_comp _
  have h2 : IsSA {v : α ⊕ β → ℝ | ∀ b, MvPolynomial.eval (v ∘ Sum.inl) (σ b) = v (Sum.inr b)} :=
    isSA_forall_fin fun b =>
      isSA_eq (IsPolyFn.eval_comp (fun a => IsPolyFn.coord _) _) (IsPolyFn.coord _)
  convert h1.inter h2 using 1
  ext v
  simp [funext_iff]

/-- The preimage of a semialgebraic set under a semialgebraic map is semialgebraic. -/
theorem IsSAFunOn.preimage {D : Set (α → ℝ)} {g : (α → ℝ) → (β → ℝ)} [Finite β]
    (hg : IsSAFunOn D g) {s : Set (β → ℝ)} (hs : IsSA s) : IsSA (D ∩ g ⁻¹' s) :=
  hg.isSA_comp (F := fun u => u) (fun a => IsPolyFn.coord a) (P := fun _ y => y ∈ s)
    (hs.preimage_comp Sum.inr)

/-- The image of a semialgebraic set under a semialgebraic map is semialgebraic. -/
theorem IsSAFunOn.image {D : Set (α → ℝ)} {g : (α → ℝ) → (β → ℝ)} [Finite α]
    (hg : IsSAFunOn D g) {s : Set (α → ℝ)} (hs : IsSA s) (hsD : s ⊆ D) : IsSA (g '' s) := by
  have h1 : IsSA {w : β ⊕ α → ℝ | Sum.elim (w ∘ Sum.inr) (w ∘ Sum.inl) ∈
      {v : α ⊕ β → ℝ | v ∘ Sum.inl ∈ D ∧ g (v ∘ Sum.inl) = v ∘ Sum.inr}} :=
    hg.2.preimage_polyFn (by rintro (a | b) <;> poly_fn)
  have h2 : IsSA {w : β ⊕ α → ℝ | w ∘ Sum.inr ∈ s} := hs.preimage_comp _
  have := isSA_exists_fun (P := fun y x => Sum.elim x y ∈
      {v : α ⊕ β → ℝ | v ∘ Sum.inl ∈ D ∧ g (v ∘ Sum.inl) = v ∘ Sum.inr} ∧ x ∈ s)
    (isSA_and h1 h2)
  convert this using 1
  ext y
  simp only [mem_image, mem_ofPred_eq, Sum.elim_comp_inl, Sum.elim_comp_inr]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, ⟨hsD hx, rfl⟩, hx⟩
  · rintro ⟨x, ⟨-, rfl⟩, hx⟩
    exact ⟨x, hx, rfl⟩

/-- Finite intersections of semialgebraic sets are semialgebraic. -/
theorem IsSA.iInter_finite {γ : Type*} [Finite γ] {s : γ → Set (α → ℝ)} (h : ∀ i, IsSA (s i)) :
    IsSA (⋂ i, s i) :=
  isSA_iInter_finite h

/-- Finite unions of semialgebraic sets are semialgebraic. -/
theorem IsSA.iUnion_finite {γ : Type*} [Finite γ] {s : γ → Set (α → ℝ)} (h : ∀ i, IsSA (s i)) :
    IsSA (⋃ i, s i) :=
  isSA_iUnion_finite h

/-- Open (sup-norm) balls are semialgebraic. -/
theorem isSA_ball [Fintype α] (x : α → ℝ) (r : ℝ) : IsSA (Metric.ball x r) := by
  rcases le_or_gt r 0 with hr | hr
  · rw [Metric.ball_eq_empty.2 hr]
    exact isSA_empty
  · have : Metric.ball x r = {y | ∀ i, |y i - x i| < r} := by
      ext y
      simp [Metric.mem_ball, dist_pi_lt_iff hr, Real.dist_eq]
    rw [this]
    exact isSA_forall_fin fun i => isSA_abs_lt (by poly_fn) (by poly_fn)

/-- Closed (sup-norm) balls are semialgebraic. -/
theorem isSA_closedBall [Fintype α] (x : α → ℝ) (r : ℝ) : IsSA (Metric.closedBall x r) := by
  rcases lt_or_ge r 0 with hr | hr
  · rw [Metric.closedBall_eq_empty.2 hr]
    exact isSA_empty
  · have : Metric.closedBall x r = {y | ∀ i, |y i - x i| ≤ r} := by
      ext y
      simp [Metric.mem_closedBall, dist_pi_le_iff hr, Real.dist_eq]
    rw [this]
    exact isSA_forall_fin fun i => isSA_abs_le (by poly_fn) (by poly_fn)

/-- The closure of a semialgebraic set is semialgebraic. -/
theorem IsSA.closure [Fintype α] {s : Set (α → ℝ)} (h : IsSA s) : IsSA (closure s) := by
  have : _root_.closure s =
      {y | ∀ r : ℝ, 0 < r → ∃ z : α → ℝ, z ∈ s ∧ ∀ i, |y i - z i| < r} := by
    ext y
    simp only [Metric.mem_closure_iff, mem_ofPred_eq]
    refine forall₂_congr fun r hr => ?_
    simp [dist_pi_lt_iff hr, Real.dist_eq]
  rw [this]
  apply isSA_forall_real
  apply isSA_imp
  · exact isSA_lt (by poly_fn) (by poly_fn)
  apply isSA_exists_fun
  apply isSA_and
  · exact h.preimage_comp _
  exact isSA_forall_fin fun i => isSA_abs_lt (by poly_fn) (by poly_fn)

/-- The interior of a semialgebraic set is semialgebraic. -/
theorem IsSA.interior [Fintype α] {s : Set (α → ℝ)} (h : IsSA s) : IsSA (interior s) := by
  have := h.compl.closure.compl
  rwa [closure_compl, compl_compl] at this

/-- Restriction of a semialgebraic map to a semialgebraic subset of its domain. -/
theorem IsSAFunOn.mono {D D' : Set (α → ℝ)} {g : (α → ℝ) → (β → ℝ)} (hg : IsSAFunOn D g)
    (hD' : IsSA D') (hsub : D' ⊆ D) : IsSAFunOn D' g := by
  refine ⟨hD', ?_⟩
  convert hg.2.inter (hD'.preimage_comp Sum.inl) using 1
  ext v
  simp only [mem_ofPred_eq, mem_inter_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨hsub h1, h2⟩, h1⟩
  · rintro ⟨⟨-, h2⟩, h1⟩
    exact ⟨h1, h2⟩

/-- Composition of semialgebraic maps. -/
theorem IsSAFunOn.comp {γ : Type} [Finite β] {D : Set (α → ℝ)} {E : Set (β → ℝ)}
    {g : (α → ℝ) → (β → ℝ)} {h : (β → ℝ) → (γ → ℝ)} (hg : IsSAFunOn D g) (hh : IsSAFunOn E h)
    (hmaps : ∀ x ∈ D, g x ∈ E) : IsSAFunOn D (h ∘ g) := by
  refine ⟨hg.1, ?_⟩
  have := hg.isSA_comp (κ := α ⊕ γ) (F := fun w => w ∘ Sum.inl) (fun a => IsPolyFn.coord _)
    (P := fun w y => Sum.elim y (w ∘ Sum.inr) ∈
      {v : β ⊕ γ → ℝ | v ∘ Sum.inl ∈ E ∧ h (v ∘ Sum.inl) = v ∘ Sum.inr})
    (hh.2.preimage_polyFn (by rintro (b | c) <;> poly_fn))
  convert this using 1
  ext w
  simp only [mem_ofPred_eq, Function.comp_apply, Sum.elim_comp_inl, Sum.elim_comp_inr]
  constructor
  · rintro ⟨hD, hw⟩
    exact ⟨hD, hmaps _ hD, hw⟩
  · rintro ⟨hD, -, hw⟩
    exact ⟨hD, hw⟩

/-- A map into `ℝ^β` (`β` finite) is semialgebraic iff its coordinates are. -/
theorem isSAFunOn_iff_coord [Finite β] {D : Set (α → ℝ)} {g : (α → ℝ) → (β → ℝ)} :
    IsSAFunOn D g ↔ IsSA D ∧ ∀ b, IsSAFunOn₁ D (fun x => g x b) := by
  constructor
  · intro hg
    refine ⟨hg.1, fun b => ⟨hg.1, ?_⟩⟩
    have := hg.isSA_comp (κ := α ⊕ Unit) (F := fun w => w ∘ Sum.inl)
      (fun a => IsPolyFn.coord _) (P := fun w y => y b = w (Sum.inr ()))
      (isSA_eq (by poly_fn) (by poly_fn))
    convert this using 1
    ext w
    simp [funext_iff, Unique.forall_iff]
  · rintro ⟨hD, hb⟩
    refine ⟨hD, ?_⟩
    have := isSA_and (hD.preimage_comp (Sum.inl : α → α ⊕ β)) (isSA_forall_fin fun b =>
      (hb b).2.preimage_polyFn
        (F := fun (v : α ⊕ β → ℝ) => Sum.elim (v ∘ Sum.inl) (fun _ : Unit => v (Sum.inr b)))
        (by rintro (a | u) <;> poly_fn))
    convert this using 1
    ext v
    simp only [mem_ofPred_eq, Sum.elim_comp_inl, funext_iff, Function.comp_apply]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun b => ⟨h1, fun _ => h2 b⟩⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun b => (h2 b).2 ()⟩

/-- Polynomial combinations of semialgebraic functions are semialgebraic. -/
theorem IsSAFunOn.poly_comp {γ : Type} [Finite β] {D : Set (α → ℝ)} {g : (α → ℝ) → (β → ℝ)}
    (hg : IsSAFunOn D g) (P : γ → MvPolynomial (α ⊕ β) ℝ) [Finite γ] :
    IsSAFunOn D (fun x c => MvPolynomial.eval (Sum.elim x (g x)) (P c)) := by
  refine ⟨hg.1, ?_⟩
  have := hg.isSA_comp (κ := α ⊕ γ) (F := fun w => w ∘ Sum.inl) (fun a => IsPolyFn.coord _)
    (P := fun w y => ∀ c, MvPolynomial.eval (Sum.elim (w ∘ Sum.inl) y) (P c) = w (Sum.inr c))
    (isSA_forall_fin fun c =>
      isSA_eq (IsPolyFn.eval_comp (by rintro (a | b) <;> poly_fn) _) (by poly_fn))
  convert this using 1
  ext w
  simp [funext_iff]

/-- The directional derivative of a function differentiable on an open set, characterized
through one-sided difference quotients (a first-order condition). -/
theorem fderiv_apply_eq_iff [Fintype α] {D : Set (α → ℝ)} (hD : IsOpen D) {g : (α → ℝ) → ℝ}
    (hdiff : DifferentiableOn ℝ g D) {x : α → ℝ} (hx : x ∈ D) (v : α → ℝ) (L : ℝ) :
    fderiv ℝ g x v = L ↔ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      x + h • v ∈ D → |g (x + h • v) - g x - h * L| ≤ ε * h := by
  have hgx : HasFDerivAt g (fderiv ℝ g x) x :=
    (hdiff.differentiableAt (hD.mem_nhds hx)).hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hφ : HasDerivAt (fun t : ℝ => g (x + t • v)) (fderiv ℝ g x v) 0 :=
    hgx.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  constructor
  · rintro rfl ε hε
    have := (hasDerivAt_iff_isLittleO.1 hφ).def hε
    obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 this
    refine ⟨δ, hδ, fun h h0 hδh _ => ?_⟩
    have := hδ' (y := h) (by simpa [Real.dist_eq, abs_of_pos h0] using hδh)
    simpa [Real.norm_eq_abs, abs_of_pos h0, mul_comm] using this
  · intro H
    have hw : HasDerivWithinAt (fun t : ℝ => g (x + t • v)) L (Ioi 0) 0 := by
      rw [hasDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
      intro ε hε
      obtain ⟨δ, hδ, hδ'⟩ := H ε hε
      have hcont : ∀ᶠ t in 𝓝 (0 : ℝ), x + t • v ∈ D :=
        hl.continuousAt.preimage_mem_nhds (by simpa using hD.mem_nhds hx)
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hδ),
        nhdsWithin_le_nhds hcont] with t ht0 htδ htD
      have ht0' : 0 < t := ht0
      have := hδ' t ht0' htδ htD
      simpa [Real.norm_eq_abs, abs_of_pos ht0', mul_comm] using this
    exact (uniqueDiffWithinAt_Ioi 0).eq_deriv _ hφ.hasDerivWithinAt hw

/-- **(S1)**: directional derivatives of a semialgebraic function that is differentiable on an
open set are semialgebraic there. -/
theorem IsSAFunOn₁.fderiv_apply [Fintype α] {D : Set (α → ℝ)} (hD : IsOpen D)
    {g : (α → ℝ) → ℝ} (hg : IsSAFunOn₁ D g) (hdiff : DifferentiableOn ℝ g D) (v : α → ℝ) :
    IsSAFunOn₁ D (fun x => fderiv ℝ g x v) := by
  refine ⟨hg.1, ?_⟩
  set G := {w : α ⊕ Unit → ℝ | w ∘ Sum.inl ∈ D ∧ (fun x (_ : Unit) => g x) (w ∘ Sum.inl) =
    w ∘ Sum.inr} with hGdef
  have hG : IsSA G := hg.2
  have hGmem : ∀ x a, Sum.elim x (fun _ => a) ∈ G ↔ x ∈ D ∧ g x = a := by
    intro x a
    simp [hGdef, funext_iff]
  -- the graph of the directional derivative, by a first-order formula
  have key : IsSA {w : α ⊕ Unit → ℝ | w ∘ Sum.inl ∈ D ∧ ∃ b : ℝ,
      Sum.elim (w ∘ Sum.inl) (fun _ => b) ∈ G ∧ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ h : ℝ, 0 < h → h < δ → w ∘ Sum.inl + h • v ∈ D →
          ∃ a : ℝ, Sum.elim (w ∘ Sum.inl + h • v) (fun _ => a) ∈ G ∧
            |a - b - h * w (Sum.inr ())| ≤ ε * h} := by
    apply isSA_and
    · exact hg.1.preimage_comp _
    apply isSA_exists_real
    apply isSA_and
    · exact hG.preimage_polyFn (by rintro (i | i) <;> poly_fn)
    apply isSA_forall_real
    apply isSA_imp
    · exact isSA_lt (by poly_fn) (by poly_fn)
    apply isSA_exists_real
    apply isSA_and
    · exact isSA_lt (by poly_fn) (by poly_fn)
    apply isSA_forall_real
    apply isSA_imp
    · exact isSA_lt (by poly_fn) (by poly_fn)
    apply isSA_imp
    · exact isSA_lt (by poly_fn) (by poly_fn)
    apply isSA_imp
    · exact hg.1.preimage_polyFn (by intro i; poly_fn)
    apply isSA_exists_real
    apply isSA_and
    · exact hG.preimage_polyFn (by rintro (i | i) <;> poly_fn)
    · exact isSA_abs_le (by poly_fn) (by poly_fn)
  convert key using 1
  ext w
  simp only [mem_ofPred_eq, hGmem]
  constructor
  · rintro ⟨hx, hfd⟩
    refine ⟨hx, g (w ∘ Sum.inl), ⟨hx, rfl⟩, ?_⟩
    have hfd' : fderiv ℝ g (w ∘ Sum.inl) v = w (Sum.inr ()) := congrFun hfd ()
    rw [fderiv_apply_eq_iff hD hdiff hx] at hfd'
    intro ε hε
    obtain ⟨δ, hδ, H⟩ := hfd' ε hε
    exact ⟨δ, hδ, fun h h0 h1 h2 => ⟨_, ⟨h2, rfl⟩, H h h0 h1 h2⟩⟩
  · rintro ⟨hx, b, ⟨-, rfl⟩, H⟩
    refine ⟨hx, funext fun _ => ?_⟩
    show fderiv ℝ g (w ∘ Sum.inl) v = w (Sum.inr ())
    rw [fderiv_apply_eq_iff hD hdiff hx]
    intro ε hε
    obtain ⟨δ, hδ, H'⟩ := H ε hε
    refine ⟨δ, hδ, fun h h0 h1 h2 => ?_⟩
    obtain ⟨a, ⟨-, rfl⟩, ha⟩ := H' h h0 h1 h2
    exact ha

/-! ## Dimension in families -/

/-- **(S1), second sentence.**  Dimension is definable in semialgebraic families. -/
theorem isSA_dimGE_fiber [Fintype α] [Fintype β] {A : Set (α ⊕ β → ℝ)} (hA : IsSA A) (e : ℕ) :
    IsSA {c : β → ℝ | DimGE (fiberOver A c) e} := by
  have key : {c : β → ℝ | DimGE (fiberOver A c) e} = {c | ∃ σ : Fin e → α,
      Function.Injective σ ∧ ∃ p : Fin e → ℝ, ∃ r : ℝ, 0 < r ∧ ∀ q : Fin e → ℝ,
        (∀ i, |q i - p i| < r) → ∃ x : α → ℝ, (∀ i, x (σ i) = q i) ∧ Sum.elim x c ∈ A} := by
    ext c
    simp only [mem_ofPred_eq]
    unfold DimGE
    refine exists_congr fun σ => and_congr_right fun _ => ?_
    constructor
    · rintro ⟨p, hp⟩
      rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hp
      obtain ⟨r, hr, hball⟩ := hp
      refine ⟨p, r, hr, fun q hq => ?_⟩
      have : q ∈ Metric.ball p r := by
        rw [Metric.mem_ball, dist_pi_lt_iff hr]
        intro i
        rw [Real.dist_eq]
        exact hq i
      obtain ⟨x, hx, rfl⟩ := hball this
      exact ⟨x, fun i => rfl, hx⟩
    · rintro ⟨p, r, hr, H⟩
      refine ⟨p, ?_⟩
      rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
      refine ⟨r, hr, fun q hq => ?_⟩
      rw [Metric.mem_ball, dist_pi_lt_iff hr] at hq
      obtain ⟨x, hxq, hx⟩ := H q (fun i => by rw [← Real.dist_eq]; exact hq i)
      exact ⟨x, hx, funext hxq⟩
  rw [key]
  apply isSA_exists_fin
  intro σ
  apply isSA_const_and
  intro _
  apply isSA_exists_fun
  apply isSA_exists_real
  apply isSA_and
  · exact isSA_lt (by poly_fn) (by poly_fn)
  apply isSA_forall_fun
  apply isSA_imp
  · exact isSA_forall_fin fun i => isSA_abs_lt (by poly_fn) (by poly_fn)
  apply isSA_exists_fun
  apply isSA_and
  · exact isSA_forall_fin fun i => isSA_eq (by poly_fn) (by poly_fn)
  exact hA.preimage_polyFn (by rintro (i | i) <;> poly_fn)

/-! ## Consequences of the facts -/

/-- A semialgebraic set of dimension `< n` in `ℝⁿ` has empty interior, and so has its closure;
its complement is dense. -/
theorem dense_compl_of_dimLT (hS : SAFacts) [Fintype α] {A : Set (α → ℝ)} (hA : IsSA A)
    (h : DimLT A (Fintype.card α)) : Dense (closure A)ᶜ := by
  have := hS.closure_dimLT A _ hA h
  rw [dimLT_card_iff] at this
  exact interior_eq_empty_iff_dense_compl.1 this

/-- **(S5)**: a semialgebraic function on an open set is continuous on an open dense subset. -/
theorem exists_open_dense_continuous (hS : SAFacts) [Fintype α] {O : Set (α → ℝ)}
    (hO : IsOpen O) {g : (α → ℝ) → ℝ} (hg : IsSAFunOn₁ O g) :
    ∃ O' ⊆ O, IsOpen O' ∧ O ⊆ closure O' ∧ IsSA O' ∧ ContinuousOn g O' := by
  obtain ⟨Z, hZ, -, hZdim, hZan⟩ := hS.nash O g hO hg
  have hdense := dense_compl_of_dimLT hS hZ hZdim
  refine ⟨O \ closure Z, sdiff_subset, hO.sdiff isClosed_closure, ?_, hg.1.diff hZ.closure, ?_⟩
  · simpa [sdiff_eq] using hdense.open_subset_closure_inter hO
  · intro x hx
    exact (hZan x ⟨hx.1, fun h => hx.2 (subset_closure h)⟩).continuousAt.continuousWithinAt

/-- A semialgebraic function that is positive on an open set `O` is bounded below by a positive
constant on some open ball in `O`. -/
theorem exists_ball_lower_bound (hS : SAFacts) [Fintype α] {O : Set (α → ℝ)} (hO : IsOpen O)
    (hOne : O.Nonempty) {g : (α → ℝ) → ℝ} (hg : IsSAFunOn₁ O g) (hpos : ∀ x ∈ O, 0 < g x) :
    ∃ x₀ r c, 0 < r ∧ Metric.ball x₀ r ⊆ O ∧ 0 < c ∧ ∀ x ∈ Metric.ball x₀ r, c ≤ g x := by
  obtain ⟨O', hO'O, hO'open, hOcl, -, hcont⟩ := exists_open_dense_continuous hS hO hg
  obtain ⟨x₀, hx₀⟩ : O'.Nonempty := by
    obtain ⟨x, hx⟩ := hOne
    exact closure_nonempty_iff.1 ⟨x, hOcl hx⟩
  have hca : ContinuousAt g x₀ := hcont.continuousAt (hO'open.mem_nhds hx₀)
  have hpos0 := hpos x₀ (hO'O hx₀)
  have hev : ∀ᶠ x in 𝓝 x₀, g x₀ / 2 < g x ∧ x ∈ O' :=
    (hca.eventually (lt_mem_nhds (half_lt_self hpos0))).and (hO'open.mem_nhds hx₀)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  exact ⟨x₀, r, g x₀ / 2, hr, fun x hx => hO'O (hball x hx).2, half_pos hpos0,
    fun x hx => (hball x hx).1.le⟩

/-- The empty set has dimension `-∞`. -/
theorem FO.dimLT_empty (d : ℕ) : DimLT (∅ : Set (α → ℝ)) d := by
  rintro ⟨σ, -, hne⟩
  simp [coordProj] at hne

/-- Finite unions of semialgebraic sets of dimension `< d` (from (S4)(a)). -/
theorem FO.isSA_dimLT_biUnion (hS : SAFacts) [Fintype α] {ι' : Type*} (t : Finset ι')
    (A : ι' → Set (α → ℝ)) (d : ℕ) (hA : ∀ i ∈ t, IsSA (A i)) (hd : ∀ i ∈ t, DimLT (A i) d) :
    IsSA (⋃ i ∈ t, A i) ∧ DimLT (⋃ i ∈ t, A i) d := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    have : (⋃ i ∈ (∅ : Finset ι'), A i) = ∅ := by simp
    rw [this]
    exact ⟨isSA_empty, dimLT_empty d⟩
  | insert a t ha ih =>
    rw [Finset.set_biUnion_insert]
    obtain ⟨h1, h2⟩ := ih (fun i hi => hA i (Finset.mem_insert_of_mem hi))
      (fun i hi => hd i (Finset.mem_insert_of_mem hi))
    have hAa := hA a (Finset.mem_insert_self a t)
    exact ⟨hAa.union h1, hS.union_dimLT _ _ _ hAa h1 (hd a (Finset.mem_insert_self a t)) h2⟩

/-- If finitely many semialgebraic sets cover a nonempty open set, one of them has nonempty
interior (from (S4)(a)). -/
theorem exists_interior_of_finite_cover (hS : SAFacts) [Fintype α] {ι' : Type*} (s : Finset ι')
    (A : ι' → Set (α → ℝ)) (hA : ∀ i ∈ s, IsSA (A i)) {O : Set (α → ℝ)} (hO : IsOpen O)
    (hOne : O.Nonempty) (hcov : O ⊆ ⋃ i ∈ s, A i) :
    ∃ i ∈ s, (interior (A i ∩ O)).Nonempty := by
  obtain ⟨x, hx⟩ := hOne
  obtain ⟨r, hr, hB⟩ := Metric.isOpen_iff.1 hO x hx
  by_contra hcon
  simp only [not_exists, not_and, not_nonempty_iff_eq_empty] at hcon
  have hd : ∀ i ∈ s, DimLT (A i ∩ Metric.ball x r) (Fintype.card α) := by
    intro i hi
    rw [dimLT_card_iff]
    exact eq_empty_of_subset_empty
      ((interior_mono (inter_subset_inter_right _ hB)).trans (hcon i hi).subset)
  obtain ⟨-, hU⟩ := isSA_dimLT_biUnion hS s (fun i => A i ∩ Metric.ball x r) _
    (fun i hi => (hA i hi).inter (isSA_ball x r)) hd
  rw [dimLT_card_iff] at hU
  have hsub : Metric.ball x r ⊆ ⋃ i ∈ s, A i ∩ Metric.ball x r := by
    intro y hy
    obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.1 (hcov (hB hy))
    exact mem_iUnion₂.2 ⟨i, hi, hyi, hy⟩
  have : x ∈ interior (⋃ i ∈ s, A i ∩ Metric.ball x r) :=
    interior_maximal hsub Metric.isOpen_ball (Metric.mem_ball_self hr)
  rw [hU] at this
  exact this

/-- `dim A ≥ 1` iff some coordinate projection of `A` has nonempty interior in `ℝ`. -/
theorem FO.dimGE_one_iff (A : Set (α → ℝ)) :
    DimGE A 1 ↔ ∃ a : α, (interior ((fun x : α → ℝ => x a) '' A)).Nonempty := by
  let e := Homeomorph.funUnique (Fin 1) ℝ
  have hproj : ∀ σ : Fin 1 → α,
      coordProj σ A = e ⁻¹' ((fun x : α → ℝ => x (σ 0)) '' A) := by
    intro σ
    ext q
    simp only [coordProj, mem_image, mem_preimage]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, hxq⟩
      refine ⟨x, hx, funext fun i => ?_⟩
      rw [Subsingleton.elim i 0]
      exact hxq
  constructor
  · rintro ⟨σ, -, hne⟩
    refine ⟨σ 0, ?_⟩
    rw [hproj, ← e.preimage_interior] at hne
    exact e.surjective.nonempty_preimage.1 hne
  · rintro ⟨a, hne⟩
    refine ⟨fun _ => a, fun i j _ => Subsingleton.elim i j, ?_⟩
    rw [hproj, ← e.preimage_interior]
    exact e.surjective.nonempty_preimage.2 hne

/-- A semialgebraic set has dimension `0` (i.e. `< 1`) exactly when it is finite. -/
theorem dimLT_one_iff_finite (hS : SAFacts) [Fintype α] {A : Set (α → ℝ)} (hA : IsSA A) :
    DimLT A 1 ↔ A.Finite := by
  unfold DimLT
  rw [dimGE_one_iff, not_exists]
  simp only [not_nonempty_iff_eq_empty]
  constructor
  · intro h
    have hfin : ∀ a, ((fun x : α → ℝ => x a) '' A).Finite := by
      intro a
      set P := (fun x : α → ℝ => x a) '' A with hP
      have hSA : IsSA₁ P := by
        show IsSA {v : Unit → ℝ | v () ∈ P}
        have : IsSA {v : Unit → ℝ | ∃ x : α → ℝ, x ∈ A ∧ x a = v ()} := by
          apply isSA_exists_fun
          apply isSA_and
          · exact hA.preimage_comp _
          · exact isSA_eq (by poly_fn) (by poly_fn)
        convert this using 1
        ext v
        simp [hP]
      obtain ⟨F, I, hPeq⟩ := hS.finite_union_intervals P hSA
      refine F.finite_toSet.subset fun t ht => ?_
      by_contra htF
      have ht' := ht
      rw [hPeq] at ht'
      rcases ht' with ht' | ht'
      · exact htF ht'
      · simp only [mem_iUnion] at ht'
        obtain ⟨p, hp, hpt⟩ := ht'
        have hopen : IsOpen {x : ℝ | p.1 < (x : EReal) ∧ (x : EReal) < p.2} :=
          isOpen_Ioo.preimage continuous_coe_real_ereal
        have hsub : {x : ℝ | p.1 < (x : EReal) ∧ (x : EReal) < p.2} ⊆ P := by
          rw [hPeq]
          intro y hy
          exact Or.inr (mem_iUnion₂.2 ⟨p, hp, hy⟩)
        have : t ∈ interior P := interior_maximal hsub hopen hpt
        rw [h a] at this
        exact this
    refine (Set.Finite.pi (t := fun a => (fun x : α → ℝ => x a) '' A) hfin).subset ?_
    intro x hx
    simp only [Set.mem_pi, mem_univ, true_implies]
    intro a
    exact ⟨x, hx, rfl⟩
  · intro hfin a
    by_contra hne
    obtain ⟨t, ht⟩ := nonempty_iff_ne_empty.2 hne
    exact infinite_of_mem_nhds t (mem_interior_iff_mem_nhds.1 ht) (hfin.image _)

/-- Finitely many points avoid some interval `(a, a + e)`. -/
theorem FO.exists_pos_forall_notMem_Ioo (F : Finset ℝ) (a : ℝ) :
    ∃ e > 0, ∀ f ∈ F, f ∉ Ioo a (a + e) := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert f F hf ih =>
    obtain ⟨e, he, H⟩ := ih
    rcases le_or_gt f a with hfa | hfa
    · refine ⟨e, he, fun y hy => ?_⟩
      rcases Finset.mem_insert.1 hy with rfl | hy
      · exact fun h => absurd h.1 (not_lt.2 hfa)
      · exact H y hy
    · refine ⟨min e (f - a), lt_min he (by linarith), fun y hy => ?_⟩
      rcases Finset.mem_insert.1 hy with rfl | hy
      · intro h
        have := h.2
        have := min_le_right e (y - a)
        linarith
      · intro h
        refine H y hy ⟨h.1, lt_of_lt_of_le h.2 ?_⟩
        have := min_le_left e (f - a)
        linarith

/-- **(S3)**: a semialgebraic subset of `ℝ` either contains an interval `(a, a + e)` or misses
such an interval. -/
theorem germ_right (hS : SAFacts) {A : Set ℝ} (hA : IsSA₁ A) (a : ℝ) :
    (∃ e > 0, Ioo a (a + e) ⊆ A) ∨ (∃ e > 0, Disjoint (Ioo a (a + e)) A) := by
  classical
  obtain ⟨P, I, hAeq⟩ := hS.finite_union_intervals A hA
  obtain ⟨e, he, hF⟩ := exists_pos_forall_notMem_Ioo
    (P ∪ I.image (fun p => p.1.toReal) ∪ I.image (fun p => p.2.toReal)) a
  -- no endpoint lies in `(a, a + e)`, so each interval contains all of it or none of it
  have hJ : ∀ p ∈ I, ∀ s ∈ Ioo a (a + e), ∀ t ∈ Ioo a (a + e),
      (p.1 < (t : EReal) ∧ (t : EReal) < p.2) → (p.1 < (s : EReal) ∧ (s : EReal) < p.2) := by
    intro p hp s hs t ht ⟨h1, h2⟩
    constructor
    · by_contra hle
      rw [not_lt] at hle
      have hne_bot : p.1 ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot s) hle
      have hne_top : p.1 ≠ ⊤ := ne_top_of_lt h1
      have hcoe : (p.1.toReal : EReal) = p.1 := EReal.coe_toReal hne_top hne_bot
      have hst1 : s ≤ p.1.toReal := by rw [← EReal.coe_le_coe_iff, hcoe]; exact hle
      have hst2 : p.1.toReal < t := by rw [← EReal.coe_lt_coe_iff, hcoe]; exact h1
      have hmem : p.1.toReal ∈
          P ∪ I.image (fun p => p.1.toReal) ∪ I.image (fun p => p.2.toReal) := by
        simp only [Finset.mem_union, Finset.mem_image]
        exact Or.inl (Or.inr ⟨p, hp, rfl⟩)
      exact hF _ hmem ⟨by linarith [hs.1], by linarith [ht.2]⟩
    · by_contra hle
      rw [not_lt] at hle
      have hne_top : p.2 ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top s) hle
      have hne_bot : p.2 ≠ ⊥ := ne_bot_of_gt h2
      have hcoe : (p.2.toReal : EReal) = p.2 := EReal.coe_toReal hne_top hne_bot
      have hst1 : p.2.toReal ≤ s := by rw [← EReal.coe_le_coe_iff, hcoe]; exact hle
      have hst2 : t < p.2.toReal := by rw [← EReal.coe_lt_coe_iff, hcoe]; exact h2
      have hmem : p.2.toReal ∈
          P ∪ I.image (fun p => p.1.toReal) ∪ I.image (fun p => p.2.toReal) := by
        simp only [Finset.mem_union, Finset.mem_image]
        exact Or.inr ⟨p, hp, rfl⟩
      exact hF _ hmem ⟨by linarith [ht.1], by linarith [hs.2]⟩
  by_cases hex : ∃ t ∈ Ioo a (a + e), t ∈ A
  · left
    obtain ⟨t, ht, htA⟩ := hex
    refine ⟨e, he, fun s hs => ?_⟩
    rw [hAeq] at htA ⊢
    rcases htA with htP | htJ
    · exact absurd ht
        (hF t (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_coe.1 htP))))
    · simp only [mem_iUnion] at htJ
      obtain ⟨p, hp, hpt⟩ := htJ
      exact Or.inr (mem_iUnion₂.2 ⟨p, hp, hJ p hp s hs t ht hpt⟩)
  · right
    exact ⟨e, he, Set.disjoint_left.2 fun t ht htA => hex ⟨t, ht, htA⟩⟩

/-- **(S3)**: a semialgebraic function on `(0, δ)` that is bounded has a limit at `0⁺`. -/
theorem exists_tendsto_of_bdd (hS : SAFacts) {g : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hg : IsSAFun₁₁ (Ioo 0 δ) g) {M : ℝ} (hM : ∀ x ∈ Ioo 0 δ, |g x| ≤ M) :
    ∃ L, Tendsto g (𝓝[>] 0) (𝓝 L) := by
  obtain ⟨δ', ⟨hδ'0, hδ'δ⟩, -, hcases⟩ := hS.monotonicity g δ hδ hg
  have hsub : Ioo 0 δ' ⊆ Ioo 0 δ := Ioo_subset_Ioo_right hδ'δ
  have hne : (Ioo (0 : ℝ) δ').Nonempty := nonempty_Ioo.2 hδ'0
  have hbddA : BddAbove (g '' Ioo 0 δ') := by
    refine ⟨M, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (le_abs_self _).trans (hM x (hsub hx))
  have hbddB : BddBelow (g '' Ioo 0 δ') := by
    refine ⟨-M, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (abs_le.1 (hM x (hsub hx))).1
  rcases hcases with ⟨c, hc⟩ | hmono | hanti
  · refine ⟨c, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [Ioo_mem_nhdsGT hδ'0] with x hx using (hc x hx).symm
  · exact ⟨_, hmono.monotoneOn.tendsto_nhdsWithin_Ioo_right hne hbddB⟩
  · exact ⟨_, hanti.antitoneOn.tendsto_nhdsWithin_Ioo_right hne hbddA⟩

end ClassSep
