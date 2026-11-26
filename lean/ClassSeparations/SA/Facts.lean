import ClassSeparations.SA.Dim

/-!
# The standard facts (S2)–(S8) about semialgebraic sets

Paper, §2.3.  These are textbook theorems of real algebraic geometry (BCR98, vdD98) that the
paper cites without proof.  We do not formalize them; instead every theorem that depends on
them takes a hypothesis `hS : SAFacts`.  Each field below is a precise, true statement
about semialgebraic sets in the sense of `ClassSep.IsSA` (first-order definable sets over
`(ℝ, +, ×, <)`), and we indicate the item of the paper and a reference.

Fact (S1) needs no hypothesis: with our definition of `IsSA` it holds by construction, and
its instances are proved in `ClassSeparations.SA.Formula` and `ClassSeparations.SA.Lemmas`.

Some items are stated in the specific form in which the paper uses them; each such form is an
immediate consequence of the cited statement (explained in the docstrings).
-/

noncomputable section

open Set Filter Topology

namespace ClassSep

/-- The standard facts (S2)–(S8) of §2.3, as hypotheses. -/
structure SAFacts : Prop where
  /-- **(S2) Definable choice** (vdD98, Ch. 6, (1.2)): a semialgebraic `E ⊆ ℝ^α × ℝ^β` has a
  semialgebraic section over its projection to `ℝ^α`.  (Outside the projection the section
  takes arbitrary values; its graph over all of `ℝ^α` is semialgebraic.) -/
  choice : ∀ {α β : Type} [Fintype α] [Fintype β] (E : Set (α ⊕ β → ℝ)), IsSA E →
    ∃ s : (α → ℝ) → (β → ℝ), IsSAFunOn univ s ∧
      ∀ x, (∃ y, Sum.elim x y ∈ E) → Sum.elim x (s x) ∈ E
  /-- **(S3), first part** (BCR98, Prop. 2.1.7; o-minimality): a semialgebraic subset of `ℝ`
  is a finite union of points and open intervals (with endpoints in `[-∞, ∞]`). -/
  finite_union_intervals : ∀ A : Set ℝ, IsSA₁ A →
    ∃ (P : Finset ℝ) (I : Finset (EReal × EReal)),
      A = (P : Set ℝ) ∪ ⋃ p ∈ I, {x : ℝ | p.1 < (x : EReal) ∧ (x : EReal) < p.2}
  /-- **(S3), monotonicity theorem** (vdD98, Ch. 3, (1.2)): a semialgebraic function on
  `(0, δ)` is, on some interval `(0, δ')`, continuous and either constant or strictly
  monotone. -/
  monotonicity : ∀ (g : ℝ → ℝ) (δ : ℝ), 0 < δ → IsSAFun₁₁ (Ioo 0 δ) g →
    ∃ δ' ∈ Ioc 0 δ, ContinuousOn g (Ioo 0 δ') ∧
      ((∃ c, ∀ x ∈ Ioo 0 δ', g x = c) ∨ StrictMonoOn g (Ioo 0 δ') ∨
        StrictAntiOn g (Ioo 0 δ'))
  /-- **(S4)(a)** (BCR98, Prop. 2.8.2): if a semialgebraic set has dimension `< d`, so does
  its closure. -/
  closure_dimLT : ∀ {α : Type} [Fintype α] (A : Set (α → ℝ)) (d : ℕ), IsSA A → DimLT A d →
    DimLT (closure A) d
  /-- **(S4)(a)** (BCR98, Prop. 2.8.5): a finite union has the largest of the dimensions. -/
  union_dimLT : ∀ {α : Type} [Fintype α] (A B : Set (α → ℝ)) (d : ℕ), IsSA A → IsSA B →
    DimLT A d → DimLT B d → DimLT (A ∪ B) d
  /-- **(S4)(b)** (BCR98, Prop. 2.8.13; vdD98, Ch. 4, (1.8)): `dim (Ā \ A) < dim A`. -/
  frontier_dim : ∀ {α : Type} [Fintype α] (A : Set (α → ℝ)) (d : ℕ), IsSA A →
    DimGE (closure A \ A) d → DimGE A (d + 1)
  /-- **(S4)(c)**, inequality `≥` (vdD98, Ch. 4, (1.5)): if the fibers of `A` over a set of
  dimension `≥ d` have dimension `≥ e`, then `dim A ≥ e + d`. -/
  fiber_dim_le : ∀ {α β : Type} [Fintype α] [Fintype β] (A : Set (α ⊕ β → ℝ)) (e d : ℕ),
    IsSA A → DimGE {c | DimGE (fiberOver A c) e} d → DimGE A (e + d)
  /-- **(S4)(c)**, inequality `≤` (vdD98, Ch. 4, (1.5)): if `dim A ≥ D`, then for some
  `e ≤ D` the fibers of dimension `≥ e` lie over a set of dimension `≥ D - e`. -/
  fiber_dim_ge : ∀ {α β : Type} [Fintype α] [Fintype β] (A : Set (α ⊕ β → ℝ)) (D : ℕ),
    IsSA A → DimGE A D → ∃ e ≤ D, DimGE {c | DimGE (fiberOver A c) e} (D - e)
  /-- **(S5), last part** (cell decomposition; BCR98, Thm. 2.3.1): a semialgebraic set in
  `ℝⁿ × ℝ` with finite nonempty fibers over an open set `V` is, over some open ball in `V`,
  the union of the graphs of continuous semialgebraic functions `λ₁ < ⋯ < λ_q`.  Here the
  last coordinate is `none : Option α`. -/
  finite_fibers : ∀ {α : Type} [Fintype α] (E : Set (Option α → ℝ)) (V : Set (α → ℝ)),
    IsSA E → IsOpen V → V.Nonempty →
    (∀ x ∈ V, {y : ℝ | extendVal y x ∈ E}.Finite ∧ {y : ℝ | extendVal y x ∈ E}.Nonempty) →
    ∃ (x₀ : α → ℝ) (r : ℝ), 0 < r ∧ Metric.ball x₀ r ⊆ V ∧
      ∃ (q : ℕ) (λ' : Fin q → (α → ℝ) → ℝ), 0 < q ∧
        (∀ i, IsSAFunOn₁ (Metric.ball x₀ r) (λ' i) ∧ ContinuousOn (λ' i) (Metric.ball x₀ r)) ∧
        (∀ x ∈ Metric.ball x₀ r, StrictMono fun i => λ' i x) ∧
        ∀ x ∈ Metric.ball x₀ r, {y : ℝ | extendVal y x ∈ E} = range fun i => λ' i x
  /-- **(S6) Sard** (BCR98, Thm. 9.6.2), for Nash maps between open subsets of `ℝᵐ`: the
  critical values of a semialgebraic map that is analytic on an open semialgebraic set form a
  semialgebraic set of dimension `< m`. -/
  sard : ∀ {α : Type} [Fintype α] (O : Set (α → ℝ)) (Φ : (α → ℝ) → (α → ℝ)),
    IsOpen O → IsSAFunOn O Φ → AnalyticOnNhd ℝ Φ O →
    IsSA {y | ∃ p ∈ O, Φ p = y ∧ ¬ Function.Surjective (fderiv ℝ Φ p)} ∧
      DimLT {y | ∃ p ∈ O, Φ p = y ∧ ¬ Function.Surjective (fderiv ℝ Φ p)} (Fintype.card α)
  /-- **(S7) Puiseux** (BCR98, §2.6 and Newton–Puiseux), in the asymptotic form used in the
  paper: a semialgebraic `a : (0, δ) → ℝ` agrees near `0⁺` with a convergent Puiseux series
  `∑_{i ≥ 0} cᵢ η^{(j₀ + i)/M}`; in particular, for every `J`, the error of the partial sum with
  `J` terms is `O(s^{j₀+J})` after the substitution `η = s^M`. -/
  puiseux : ∀ (a : ℝ → ℝ) (δ : ℝ), 0 < δ → IsSAFun₁₁ (Ioo 0 δ) a →
    ∃ (M : ℕ) (j₀ : ℤ) (c : ℕ → ℝ), 0 < M ∧ ∀ J : ℕ,
      (fun s : ℝ => a (s ^ M) - ∑ i ∈ Finset.range J, c i * s ^ (j₀ + i)) =O[𝓝[>] 0]
        (fun s : ℝ => s ^ (j₀ + J))
  /-- **(S8)** (BCR98, Prop. 2.8.8 and Thm. 2.8.8): a semialgebraic map does not increase
  dimension. -/
  dim_image : ∀ {α β : Type} [Fintype α] [Fintype β] (A : Set (α → ℝ))
    (g : (α → ℝ) → (β → ℝ)) (d : ℕ), IsSAFunOn A g → DimGE (g '' A) d → DimGE A d
  /-- **(S8)**: a semialgebraic bijection preserves dimension. -/
  dim_image_inj : ∀ {α β : Type} [Fintype α] [Fintype β] (A : Set (α → ℝ))
    (g : (α → ℝ) → (β → ℝ)) (d : ℕ), IsSAFunOn A g → InjOn g A → DimGE A d →
    DimGE (g '' A) d
  /-- **(S8)** (BCR98, Prop. 8.1.8): a semialgebraic function on an open set is Nash, i.e.
  analytic, on an open dense semialgebraic subset; equivalently, outside a semialgebraic set
  of dimension smaller than that of the ambient space. -/
  nash : ∀ {α : Type} [Fintype α] (O : Set (α → ℝ)) (g : (α → ℝ) → ℝ), IsOpen O →
    IsSAFunOn₁ O g →
    ∃ Z, IsSA Z ∧ Z ⊆ O ∧ DimLT Z (Fintype.card α) ∧ ∀ ξ ∈ O \ Z, AnalyticAt ℝ g ξ

end ClassSep
