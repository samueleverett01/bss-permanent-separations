import ClassSeparations.Basic.Circuits

/-!
# Results cited by the paper

The deep results that the paper cites from the literature, stated as `Prop`s.  Theorems that
depend on them take them as explicit hypotheses; nothing here is assumed globally.

* `PermLowerBound` — Theorem 2.3 [Cla26, Theorems 1.4 and N.5].
* `BurgisserThm` — Theorem 2.5 [Bur04, Theorem 1.3 and Remark 1.4].

(The theorem of Baur and Strassen, Theorem 2.4, is proved in
`ClassSeparations.Core.BaurStrassen`.  The facts (S2)–(S8) on semialgebraic sets are the
hypothesis `ClassSep.SAFacts`.  Further cited results used for the class separations and for
interactive proofs are collected in `ClassSeparations.Machines.Cited` and
`ClassSeparations.Interaction.Cited`.)
-/

noncomputable section

open MvPolynomial

namespace ClassSep

/-- **Theorem 2.3** [Cla26, Theorems 1.4 and N.5]: there are `c > 0` and `m₀` such that for
every `m ≥ m₀` the border complexity of the permanent `per_m` is greater than
`m^{c (log m)^{1/3}} = 2^{c (log₂ m)^{4/3}}`. -/
def PermLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s : ℕ, BorderLE (per m) s →
    (2 : ℝ) ^ (c * Real.logb 2 m ^ (4 / 3 : ℝ)) < s

/-- **Theorem 2.5** (Bürgisser [Bur04, Theorem 1.3 and Remark 1.4]): there is an absolute
constant `C` such that if `f ∈ ℝ[X₁, …, Xₙ]` has degree at most `d ≥ 1` and some nonzero
multiple of `Y - f(X)` in `ℝ[X, Y]` has a straight-line program with `ℓ` operations, then the
border complexity of `f` is at most `C d³ (ℓ + n)`.  The variable `Y` is `none`. -/
def BurgisserThm : Prop :=
  ∃ C : ℕ, ∀ {σ : Type} [Fintype σ] (d ℓ : ℕ) (f : MvPolynomial σ ℝ), 1 ≤ d →
    f.totalDegree ≤ d →
    (∃ G : MvPolynomial (Option σ) ℝ, G ≠ 0 ∧ HasSLP ((X none - rename some f) * G) ℓ) →
    BorderLE f (C * d ^ 3 * (ℓ + Fintype.card σ))

end ClassSep
