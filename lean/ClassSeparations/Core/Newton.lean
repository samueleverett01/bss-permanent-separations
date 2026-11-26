import ClassSeparations.Analysis.Taylor
import ClassSeparations.Basic.Circuits

/-!
# Newton iteration as a circuit (§3.3, Lemma 3.4)

Let `ℛ = ℝ[χ][τ]/(τ^{D+1})`.  For polynomials `E = (E₁, …, E_κ)` in `(ξ, w) ∈ ℝᴺ × ℝ^κ`, a
point `(ξ₁, w₁)` and a matrix `A`, put `Ω⁽⁰⁾ = w₁` and
`Ω⁽ʲ⁺¹⁾ = Ω⁽ʲ⁾ - A E(ξ₁ + τχ, Ω⁽ʲ⁾)` in `ℛ^κ`, and let `gᵢ ∈ ℝ[ξ]` be the sum of the `D + 1`
coefficients of `Ωᵢ⁽ᴰ⁾` with `χ = ξ - ξ₁` substituted.

Every element formed in this iteration has its coefficient of `τʲ` homogeneous of degree `j`
in `χ`; summing the coefficients identifies such elements with polynomials in `χ` of degree
`≤ D`, multiplied with truncation of the total degree at `D`.  We define `newtonPoly` in this
second form, and the circuit of part (a) computes it in the first form.

**Lemma 3.4.**
(a) The `gᵢ` are computed by a circuit with at most `C((D+1)³ℓ + (D+1)²κ² + N)` gates plus the
constants of the program, whose graph depends only on the graph of the program and on `N`,
`κ`, `D`; each `gᵢ` has degree at most `D`; the coefficients of the `gᵢ` are polynomial
functions of the coefficients of `E` and of `ξ₁, w₁, A`.
(b) If `E(ξ₁, w₁) = 0` and `A` is the inverse of `∂_w E(ξ₁, w₁)`, and `ω` is a map with
`ω(ξ₁) = w₁` and `E(ξ, ω(ξ)) = 0` near `ξ₁` that is of class `C^D` at `ξ₁` (for instance the
analytic implicit function), then `gᵢ` is the Taylor polynomial of order `D` of `ωᵢ` at `ξ₁`.
-/

noncomputable section

open MvPolynomial Filter Topology

namespace ClassSep

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Truncation of a polynomial to its monomials of total degree at most `D`. -/
def truncDeg (D : ℕ) (p : MvPolynomial ι ℝ) : MvPolynomial ι ℝ :=
  ∑ m ∈ p.support.filter (fun m => m.degree ≤ D), monomial m (p.coeff m)

/-- One Newton step in `ℝ[χ]` with truncation at total degree `D`:
`Ω ↦ trunc_D (Ω - A · E(ξ₁ + χ, Ω))`. -/
def newtonStep (E : κ → MvPolynomial (ι ⊕ κ) ℝ) (ξ₁ : ι → ℝ) (A : Matrix κ κ ℝ) (D : ℕ)
    (Ω : κ → MvPolynomial ι ℝ) : κ → MvPolynomial ι ℝ :=
  fun k => truncDeg D (Ω k - ∑ l, MvPolynomial.C (A k l) *
    bind₁ (Sum.elim (fun i => MvPolynomial.C (ξ₁ i) + X i) Ω) (E l))

/-- The output `(g₁, …, g_κ)` of Lemma 3.4, as polynomials in `ξ`. -/
def newtonPoly (E : κ → MvPolynomial (ι ⊕ κ) ℝ) (ξ₁ : ι → ℝ) (w₁ : κ → ℝ) (A : Matrix κ κ ℝ)
    (D : ℕ) : κ → MvPolynomial ι ℝ :=
  fun k => bind₁ (fun i => X i - MvPolynomial.C (ξ₁ i))
    ((newtonStep E ξ₁ A D)^[D] (fun l => MvPolynomial.C (w₁ l)) k)

/-- The Jacobian matrix `∂_w E` at a point. -/
def jacW (E : κ → MvPolynomial (ι ⊕ κ) ℝ) (p : ι ⊕ κ → ℝ) : Matrix κ κ ℝ :=
  fun k l => eval p (pderiv (Sum.inr l) (E k))

/-- The polynomials computed by a program graph `Π` at output operands `o`, with constants
`c`. -/
def progOutputs {σ : Type} (Π : SLP σ ℕ) (c : ℕ → ℝ) {β : Type} (o : β → Operand σ ℕ) :
    β → MvPolynomial σ ℝ :=
  fun b => (o b).instantiate c |>.eval (Π.instantiate c).values

/-- **Lemma 3.4 (a)**: degree bound. -/
theorem totalDegree_newtonPoly_le (E : κ → MvPolynomial (ι ⊕ κ) ℝ) (ξ₁ : ι → ℝ) (w₁ : κ → ℝ)
    (A : Matrix κ κ ℝ) (D : ℕ) (k : κ) : (newtonPoly E ξ₁ w₁ A D k).totalDegree ≤ D := by
  sorry

/-- **Lemma 3.4 (a)**: the circuit.  The graph `Γ`, the output gates and the arrangement
`enc` of the constants depend only on the program graph `Π`, its outputs, and `ι`, `κ`, `D`. -/
theorem newton_circuit :
    ∃ C : ℕ, ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
      (Π : SLP (ι ⊕ κ) ℕ) (oE : κ → Operand (ι ⊕ κ) ℕ) (D : ℕ),
      ∃ (Γ : Shape ι) (out : κ → ℕ)
        (enc : (ℕ → ℝ) → (ι → ℝ) → (κ → ℝ) → Matrix κ κ ℝ → (ℕ → ℝ)),
        Γ.length ≤ C * ((D + 1) ^ 3 * (Π.length + 1) + (D + 1) ^ 2 * Fintype.card κ ^ 2 +
          Fintype.card ι) ∧
        ∀ (c : ℕ → ℝ) (ξ₁ : ι → ℝ) (w₁ : κ → ℝ) (A : Matrix κ κ ℝ) (k : κ),
          (Γ.values (enc c ξ₁ w₁ A)).getD (out k) 0 =
            newtonPoly (progOutputs Π c oE) ξ₁ w₁ A D k := by
  sorry

/-- **Lemma 3.4 (a)**: the coefficients of the `gᵢ` depend continuously (indeed polynomially)
on the coefficients of `E` (of bounded degree) and on `ξ₁, w₁, A`. -/
theorem tendsto_coeff_newtonPoly {β : Type*} {l : Filter β}
    {Eb : β → κ → MvPolynomial (ι ⊕ κ) ℝ} {E : κ → MvPolynomial (ι ⊕ κ) ℝ}
    {ξb : β → ι → ℝ} {ξ₁ : ι → ℝ} {wb : β → κ → ℝ} {w₁ : κ → ℝ}
    {Ab : β → Matrix κ κ ℝ} {A : Matrix κ κ ℝ} (B : ℕ)
    (hdeg : ∀ b k, (Eb b k).totalDegree ≤ B) (hdegE : ∀ k, (E k).totalDegree ≤ B)
    (hE : ∀ k m, Tendsto (fun b => (Eb b k).coeff m) l (𝓝 ((E k).coeff m)))
    (hξ : Tendsto ξb l (𝓝 ξ₁)) (hw : Tendsto wb l (𝓝 w₁)) (hA : Tendsto Ab l (𝓝 A))
    (D : ℕ) (k : κ) (m : ι →₀ ℕ) :
    Tendsto (fun b => (newtonPoly (Eb b) (ξb b) (wb b) (Ab b) D k).coeff m) l
      (𝓝 ((newtonPoly E ξ₁ w₁ A D k).coeff m)) := by
  sorry

/-- **Lemma 3.4 (b).** -/
theorem newtonPoly_eq_taylorPoly (E : κ → MvPolynomial (ι ⊕ κ) ℝ) (ξ₁ : ι → ℝ) (w₁ : κ → ℝ)
    (A : Matrix κ κ ℝ) (D : ℕ)
    (hE : ∀ k, eval (Sum.elim ξ₁ w₁) (E k) = 0) (hA : A * jacW E (Sum.elim ξ₁ w₁) = 1)
    (ω : (ι → ℝ) → (κ → ℝ)) (hω₁ : ω ξ₁ = w₁) (hωD : ContDiffAt ℝ D ω ξ₁)
    (hωE : ∀ᶠ ξ in 𝓝 ξ₁, ∀ k, eval (Sum.elim ξ (ω ξ)) (E k) = 0) (k : κ) :
    newtonPoly E ξ₁ w₁ A D k = taylorPoly D (fun ξ => ω ξ k) ξ₁ := by
  sorry

end ClassSep
