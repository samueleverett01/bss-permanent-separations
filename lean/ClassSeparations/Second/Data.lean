import ClassSeparations.Second.Envelope
import ClassSeparations.Core.BaurStrassen
import ClassSeparations.SA.Lemmas

/-!
# The data of §6, and the split of the proof of Theorem 6.1

The proof of Theorem 6.1 has two parts.

**Part 1 (§6.1–6.2, Lemmas 6.2 and 6.3).**  From a tree that verifies `y = f(x)` with `∃ z ∀ u`,
isolate a certificate (Lemma 4.1), fix its coordinates, and form the margin systems (6) of the
cells of rejecting leaves, with parameters `(x, w)`.  This produces `SLData`: closed balls `K`
(sup norm) and `B̄` (Euclidean), a continuous `φ : K → B̄` whose `y`-coordinate is `f`, and
finitely many nonnegative polynomials `Q_b(x, w, ν, s)` (sums of squares of the margin systems,
with the unknowns `ν` of all cells embedded in one space `ℝ^M`) given by straight-line program
graphs, such that the set `𝒴` of their solutions with `s ≥ 0`, `x ∈ K`, `w ∈ B̄` has nonempty
bounded fibers, `v(x, w) = max {s : (x, w, ν, s) ∈ 𝒴}` vanishes exactly at `w = φ(x)`
(Lemma 6.3 (a)), and `v^N ≤ a |w - φ(x)|²` (Lemma 6.3 (c)) with `log N` polynomial in
`t, n, k, l` (Lemma 6.3 (d)).

**Part 2 (§6.3–6.6, Lemmas 6.4–6.7 and the final assembly).**  From such data, the envelope,
its continuity, its description as a value function, a generic linear term, Newton iteration and
Lemma 3.3 bound the border complexity of `f` by a polynomial in `d, κ, M, ℓ, log N, n`, where `ℓ`
bounds the lengths of the programs.
-/

noncomputable section

open MvPolynomial Set Filter Topology

namespace ClassSep

/-- The data of §6: balls, the map `φ`, and the margin systems `Q_b`. -/
structure SLData (σ κ : Type) [Fintype σ] [Fintype κ] (M : ℕ) where
  x₀ : σ → ℝ
  ρ : ℝ
  w₀ : κ → ℝ
  r₀ : ℝ
  φ : (σ → ℝ) → (κ → ℝ)
  /-- number of margin systems (cells of rejecting leaves) -/
  B : ℕ
  prog : Fin B → SLP (σ ⊕ κ ⊕ Option (Fin M)) ℕ
  out : Fin B → Operand (σ ⊕ κ ⊕ Option (Fin M)) ℕ
  cst : Fin B → ℕ → ℝ
  N : ℕ
  a : ℝ

namespace SLData

variable {σ κ : Type} [Fintype σ] [Fintype κ] {M : ℕ} (D : SLData σ κ M)

/-- The polynomial `Q_b(x, w, ν, s)`; the unknown `s` is `none`. -/
def Q (b : Fin D.B) : MvPolynomial (σ ⊕ κ ⊕ Option (Fin M)) ℝ :=
  progOutput (D.prog b) (D.cst b) (D.out b)

/-- The point `(x, w, ν, s)` as a valuation. -/
def pt (x : σ → ℝ) (w : κ → ℝ) (ν : Fin M → ℝ) (s : ℝ) : σ ⊕ κ ⊕ Option (Fin M) → ℝ :=
  Sum.elim x (Sum.elim w (extendVal s ν))

/-- `K`, a closed sup-norm ball. -/
def K : Set (σ → ℝ) := Metric.closedBall D.x₀ D.ρ

/-- `B̄`, a closed Euclidean ball. -/
def Bbar : Set (κ → ℝ) := {w | sqDist w D.w₀ ≤ D.r₀ ^ 2}

/-- `(x, w, ν, s) ∈ 𝒴`. -/
def InY (x : σ → ℝ) (w : κ → ℝ) (ν : Fin M → ℝ) (s : ℝ) : Prop :=
  x ∈ D.K ∧ w ∈ D.Bbar ∧ 0 ≤ s ∧ ∃ b, eval (pt x w ν s) (D.Q b) = 0

/-- The largest margin `v(x, w)`. -/
def v (x : σ → ℝ) (w : κ → ℝ) : ℝ := sSup {s | ∃ ν, D.InY x w ν s}

/-- The longest program. -/
def ℓmax : ℕ := Finset.univ.sup fun b : Fin D.B => (D.prog b).length

end SLData

/-- The properties of the data established in Part 1 (Lemmas 6.2, 6.3), for the polynomial `f`
whose graph is verified; `yc` is the coordinate `y` of `w = (y, z')`. -/
structure SLData.Good {σ κ : Type} [Fintype σ] [Fintype κ] {M : ℕ} (D : SLData σ κ M)
    (f : MvPolynomial σ ℝ) (yc : κ) : Prop where
  ρ_pos : 0 < D.ρ
  r₀_pos : 0 < D.r₀
  N_pos : 1 ≤ D.N
  a_pos : 0 < D.a
  φ_cont : ContinuousOn D.φ D.K
  φ_near : ∀ x ∈ D.K, sqDist (D.φ x) D.w₀ ≤ (D.r₀ / 2) ^ 2
  φ_f : ∀ x ∈ D.K, D.φ x yc = eval x f
  nonneg : ∀ b p, 0 ≤ eval p (D.Q b)
  fiber_ne : ∀ x ∈ D.K, ∀ w ∈ D.Bbar, ∃ ν s, D.InY x w ν s
  bounded : ∃ R, ∀ x w ν s, D.InY x w ν s → (∀ i, |ν i| ≤ R) ∧ s ≤ 1
  zero_iff : ∀ x ∈ D.K, ∀ w ∈ D.Bbar, D.v x w = 0 ↔ w = D.φ x
  flat : ∀ x ∈ D.K, ∀ w ∈ D.Bbar, D.v x w ^ D.N ≤ D.a * sqDist w (D.φ x)

/-! Part 2 of the proof (`sl_conclude_proof`, §6.3–6.6: Lemmas 6.4–6.7 and the assembly) is in
`ClassSeparations.Second.Conclude`; Part 1 (`sl_setup`, Lemmas 6.2–6.3) is in
`ClassSeparations.Second.Setup`. -/

end ClassSep
