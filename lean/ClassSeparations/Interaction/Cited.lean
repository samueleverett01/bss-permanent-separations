import Mathlib

/-!
# The counting bound (C) of Lemma 7.7

**(C)** For `S₀` polynomials of degree at most `Δ` in `M + K` variables, there is a partition of
`ℝᴹ` into at most `(S₀Δ)^{O(MK)}` sets such that on each set the truth value of every one-block
existential statement over these polynomials is constant.

The paper derives (C) from block elimination [BPR06, Algorithm 14.1] and the count of sign
conditions [BPR06, Proposition 7.31]: the set of sign conditions realized on the fiber
`{y} × ℝᴷ` is constant on each set of the partition, and it determines the truth value of every
one-block existential statement.  We state (C) in this form: the map sending `y` to the set of
sign vectors realized on its fiber takes at most `(S₀Δ + 2)^{C(M+1)(K+1)}` values.
-/

noncomputable section

open MvPolynomial

namespace ClassSep

/-- The set of sign vectors of `p` realized on the fiber over `y`. -/
def realizedSigns {M K S₀ : ℕ} (p : Fin S₀ → MvPolynomial (Fin M ⊕ Fin K) ℝ) (y : Fin M → ℝ) :
    Set (Fin S₀ → SignType) :=
  {s | ∃ u : Fin K → ℝ, ∀ i, SignType.sign (eval (Sum.elim y u) (p i)) = s i}

/-- **The counting bound (C)** [BPR06, Algorithm 14.1 and Proposition 7.31]. -/
def CountingBound : Prop :=
  ∃ C : ℕ, ∀ (M K S₀ Δ : ℕ) (p : Fin S₀ → MvPolynomial (Fin M ⊕ Fin K) ℝ),
    (∀ i, (p i).totalDegree ≤ Δ) →
    (Set.range (realizedSigns p)).encard ≤ ((S₀ * Δ + 2) ^ (C * (M + 1) * (K + 1)) : ℕ)

end ClassSep
