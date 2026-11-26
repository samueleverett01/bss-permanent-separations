import ClassSeparations.Basic.Tree

/-!
# The polynomials on a path, and cells (§2.4, Lemma 2.5)

For a tree of depth `t` and a set of marked outcomes, the set of inputs with a marked outcome
is a finite union of *cells* `{p₁ = ⋯ = p_r = 0, q₁ > 0, …, q_m > 0}` with `r, m ≤ 2t`, where
all `pᵢ, qⱼ` are computed by one straight-line program with at most `8t` operations from the
input coordinates and the constants of the tree, and involve at most `2t` input coordinates.
-/

noncomputable section

open MvPolynomial

namespace ClassSep

universe u

variable {ι : Type u}

/-- A cell: the common zeros of the `eqs` at which all the `poss` are positive, together with
one straight-line program that computes all these polynomials. -/
structure Cell (ι : Type u) where
  prog : SLP ι ℝ
  eqs : List (MvPolynomial ι ℝ)
  poss : List (MvPolynomial ι ℝ)

/-- The set of points of a cell. -/
def Cell.carrier (B : Cell ι) : Set (ι → ℝ) :=
  {w | (∀ p ∈ B.eqs, eval w p = 0) ∧ ∀ q ∈ B.poss, 0 < eval w q}

/-- The constants used by an operand. -/
def Operand.constSet {σ K : Type*} : Operand σ K → Set K
  | .const a => {a}
  | _ => ∅

/-- The input coordinates used by an operand. -/
def Operand.inputSet {σ K : Type*} : Operand σ K → Set σ
  | .input i => {i}
  | _ => ∅

/-- The bounds of Lemma 2.5 for a cell, for a tree of depth `t` with constants in `K`. -/
structure Cell.Bounded (B : Cell ι) (t : ℕ) (K : Set ℝ) : Prop where
  eqs_len : B.eqs.length ≤ 2 * t
  poss_len : B.poss.length ≤ 2 * t
  prog_len : B.prog.length ≤ 8 * t
  computes_eqs : ∀ p ∈ B.eqs, B.prog.Computes p
  computes_poss : ∀ q ∈ B.poss, B.prog.Computes q
  consts : ∀ ins ∈ B.prog, ins.a.constSet ∪ ins.b.constSet ⊆ K ∪ {0, 1, -1}
  vars : ∃ I : Finset ι, I.card ≤ 2 * t ∧
    (∀ ins ∈ B.prog, ins.a.inputSet ∪ ins.b.inputSet ⊆ ↑I) ∧
    (∀ p ∈ B.eqs ++ B.poss, p.vars ⊆ I)

/-- **Lemma 2.5 (cells).**  For a tree of depth at most `t` and any set `S` of marked outcomes,
the set of inputs whose outcome is marked is a finite union of cells satisfying the bounds of
the lemma. -/
theorem cells (T : Tree ι) (t : ℕ) (hT : T.depth ≤ t) (S : Set (Option Bool)) :
    ∃ L : List (Cell ι), (∀ B ∈ L, B.Bounded t T.consts) ∧
      {w | T.run w ∈ S} = ⋃ B ∈ L, B.carrier := by
  sorry

end ClassSep
