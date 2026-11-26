import ClassSeparations.SA.Complexity

/-!
# Effective quantifier elimination (cited in Lemma 6.3 (d))

**[BPR06, Theorem 14.16]**: a prenex formula with `ω` quantifier blocks of `k₁, …, k_ω`
variables, `k` free variables, and `s` atom polynomials of degree at most `d`, is equivalent to a
quantifier-free formula with at most `s^{(k_ω+1)⋯(k₁+1)(k+1)} d^{O(k_ω)⋯O(k₁)O(k)}` atom
occurrences, whose polynomials have degree at most `d^{O(k_ω)⋯O(k₁)}`.

A formula in our sense is brought into prenex form without changing its atoms, its number of
quantified variables or its number of blocks (`Fml.blocks`).  Bounding all `kᵢ` and `k` by
`K = numBound + #free`, the products are at most `(C'(K + 1))^{ω + 1}`, which is at most
`(K + 2)^{C(ω + 1)}` for an absolute constant `C`.  The resulting weaker bound is the hypothesis
`EffectiveQE`.
-/

noncomputable section

namespace ClassSep

/-- Effective quantifier elimination [BPR06, Theorem 14.16], in the weakened form above. -/
def EffectiveQE : Prop :=
  ∃ C : ℕ, ∀ {α : Type} [Fintype α] (φ : Fml α),
    ∃ ψ : Fml α, ψ.IsQF ∧ (∀ v, ψ.Holds v ↔ φ.Holds v) ∧
      ψ.size ≤ (φ.size + φ.maxDeg + 2) ^ ((φ.numBound + Fintype.card α + 2) ^ (C * (φ.blocks + 1))) ∧
      ψ.maxDeg ≤ (φ.maxDeg + 2) ^ ((φ.numBound + Fintype.card α + 2) ^ (C * (φ.blocks + 1)))

end ClassSep
