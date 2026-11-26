import ClassSeparations.Core.Derivatives
import ClassSeparations.Core.Newton
import ClassSeparations.Core.BaurStrassen

/-!
# The local theorem (§3.4, Theorem 3.5, Lemmas 3.6 and 3.7)

**Theorem 3.5.**  Let `K ⊆ ℝᴺ` be a closed ball, `B̄ ⊆ ℝ^κ` the closed ball of radius `r₀`
about `w₀`, and `λ ∈ ℝ^κ`.  Let `Q ∈ ℝ[ξ, w]` be nonnegative on `K × B̄` and computed by a
straight-line program with `ℓ` operations.  Let `φ : K → ℝ^κ` be continuous with
`|φ(ξ) - w₀| ≤ r₀/2`, and suppose that for every `ξ ∈ K`, `φ(ξ)` is the unique maximizer of
`⟨λ, w⟩` on `{w ∈ B̄ : Q(ξ, w) = 0}`.  Let `D ≥ 1`.  Then there are an open ball `V* ⊆ K`, a
semialgebraic `E* ⊆ V*` of dimension `< N`, and a circuit graph with `κ` outputs and at most
`C((D+1)³ℓ + (D+1)²κ² + N)` gates (depending only on the graph of the program and on `N`,
`κ`, `D`) such that `φ` is `C^D` on `V*` and, for every `ξ₁ ∈ V* \ E*`, the Taylor polynomial
of order `D` of `φᵢ` at `ξ₁` is a coefficientwise limit of polynomials of degree `≤ D`
computed at the `i`-th output with real constants.

Balls are taken in the sup norm of `ℝ^ι`; the Euclidean structure enters only through the
polynomial `|w - c|² = ∑ (wₖ - cₖ)²`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open MvPolynomial Set Filter Topology

namespace ClassSep

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Evaluation of a polynomial in `(ξ, w)`. -/
abbrev evalξw (ξ : ι → ℝ) (w : κ → ℝ) (Q : MvPolynomial (ι ⊕ κ) ℝ) : ℝ :=
  eval (Sum.elim ξ w) Q

/-- The regularized function `G_{c,ε}(ξ, w) = Q(ξ, w) - ε⟨λ, w⟩ + ε²|w - c|²`. -/
def regG (Q : MvPolynomial (ι ⊕ κ) ℝ) (lam c : κ → ℝ) (ε : ℝ) (ξ : ι → ℝ) (w : κ → ℝ) : ℝ :=
  evalξw ξ w Q - ε * (lam ⬝ᵥ w) + ε ^ 2 * ∑ k, (w k - c k) ^ 2

/-- The critical point equation (4): `∇_w Q(ξ, w) - ελ + 2ε²(w - c) = 0`. -/
def CriticalEq (Q : MvPolynomial (ι ⊕ κ) ℝ) (lam c : κ → ℝ) (ε : ℝ) (ξ : ι → ℝ)
    (w : κ → ℝ) : Prop :=
  ∀ k, evalξw ξ w (pderiv (Sum.inr k) Q) - ε * lam k + 2 * ε ^ 2 * (w k - c k) = 0

/-- The Hessian `∇²_w Q(ξ, w)`. -/
def hessW (Q : MvPolynomial (ι ⊕ κ) ℝ) (ξ : ι → ℝ) (w : κ → ℝ) : Matrix κ κ ℝ :=
  fun k l => evalξw ξ w (pderiv (Sum.inr l) (pderiv (Sum.inr k) Q))

/-- The set `Bad_c ⊆ ℝᴺ × (0, ∞)` of Lemma 3.7, as a subset of `ℝ^(Option ι)` (the coordinate
`none` is `ε`). -/
def badSet (Q : MvPolynomial (ι ⊕ κ) ℝ) (lam c : κ → ℝ) : Set (Option ι → ℝ) :=
  {v | 0 < v none ∧ ∃ w, CriticalEq Q lam c (v none) (v ∘ some) w ∧
    (hessW Q (v ∘ some) w + (2 * v none ^ 2) • (1 : Matrix κ κ ℝ)).det = 0}

/-- The hypotheses of Theorem 3.5 on `Q`, `φ`, `K = closedBall ξ₀ ρ` and
`B̄ = closedBall w₀ r₀`. -/
structure LocalHyp (Q : MvPolynomial (ι ⊕ κ) ℝ) (ξ₀ : ι → ℝ) (ρ : ℝ) (w₀ : κ → ℝ) (r₀ : ℝ)
    (lam : κ → ℝ) (φ : (ι → ℝ) → (κ → ℝ)) : Prop where
  ρ_pos : 0 < ρ
  r₀_pos : 0 < r₀
  nonneg : ∀ ξ ∈ Metric.closedBall ξ₀ ρ, ∀ w ∈ Metric.closedBall w₀ r₀, 0 ≤ evalξw ξ w Q
  cont : ContinuousOn φ (Metric.closedBall ξ₀ ρ)
  near : ∀ ξ ∈ Metric.closedBall ξ₀ ρ, dist (φ ξ) w₀ ≤ r₀ / 2
  zero : ∀ ξ ∈ Metric.closedBall ξ₀ ρ, evalξw ξ (φ ξ) Q = 0
  unique : ∀ ξ ∈ Metric.closedBall ξ₀ ρ, ∀ w ∈ Metric.closedBall w₀ r₀, evalξw ξ w Q = 0 →
    w ≠ φ ξ → lam ⬝ᵥ w < lam ⬝ᵥ φ ξ

/-! ## Polynomial functions and first-order definability

Tools to verify, in each application of (S1), that a concrete set is semialgebraic. -/

section Definable

variable {α β : Type}

/-- A function `ℝ^α → ℝ` given by a polynomial in the coordinates. -/
def PolyFn (f : (α → ℝ) → ℝ) : Prop := ∃ p : MvPolynomial α ℝ, ∀ v, f v = eval v p

namespace PolyFn

theorem congr {f g : (α → ℝ) → ℝ} (hf : PolyFn f) (h : ∀ v, f v = g v) : PolyFn g := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨p, fun v => (h v).symm.trans (hp v)⟩

theorem const (a : ℝ) : PolyFn (fun _ : α → ℝ => a) := ⟨C a, fun _ => by simp⟩

theorem coord (a : α) : PolyFn (fun v : α → ℝ => v a) := ⟨X a, fun _ => by simp⟩

theorem add {f g : (α → ℝ) → ℝ} (hf : PolyFn f) (hg : PolyFn g) :
    PolyFn (fun v => f v + g v) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p + q, fun v => by simp [hp, hq]⟩

theorem sub {f g : (α → ℝ) → ℝ} (hf : PolyFn f) (hg : PolyFn g) :
    PolyFn (fun v => f v - g v) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p - q, fun v => by simp [hp, hq]⟩

theorem mul {f g : (α → ℝ) → ℝ} (hf : PolyFn f) (hg : PolyFn g) :
    PolyFn (fun v => f v * g v) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p * q, fun v => by simp [hp, hq]⟩

theorem pow {f : (α → ℝ) → ℝ} (hf : PolyFn f) (n : ℕ) : PolyFn (fun v => f v ^ n) := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨p ^ n, fun v => by simp [hp]⟩

theorem sum {γ : Type*} (s : Finset γ) {f : γ → (α → ℝ) → ℝ} (h : ∀ i, PolyFn (f i)) :
    PolyFn (fun v => ∑ i ∈ s, f i v) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (α := α) 0
  | insert a s ha ih => simpa [Finset.sum_insert ha] using (h a).add ih

theorem prod {γ : Type*} (s : Finset γ) {f : γ → (α → ℝ) → ℝ} (h : ∀ i, PolyFn (f i)) :
    PolyFn (fun v => ∏ i ∈ s, f i v) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (α := α) 1
  | insert a s ha ih => simpa [Finset.prod_insert ha] using (h a).mul ih

theorem eval_poly (P : MvPolynomial β ℝ) {g : β → (α → ℝ) → ℝ} (h : ∀ b, PolyFn (g b)) :
    PolyFn (fun v => eval (fun b => g b v) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using const (α := α) a
  | add p q hp hq => simpa using hp.add hq
  | mul_X p b hp => simpa using hp.mul (h b)

theorem det {n : Type} [Fintype n] [DecidableEq n] {M : (α → ℝ) → Matrix n n ℝ}
    (h : ∀ i j, PolyFn (fun v => M v i j)) : PolyFn (fun v => (M v).det) := by
  simp only [Matrix.det_apply']
  exact sum _ fun σ => (const _).mul (prod _ fun i => h (σ i) i)

end PolyFn

/-- A first-order definable predicate on `ℝ^α`. -/
def Def (P : (α → ℝ) → Prop) : Prop := IsSA {v | P v}

namespace Def

theorem of_isSA {s : Set (α → ℝ)} (hs : IsSA s) : Def (· ∈ s) := hs

theorem isSA {s : Set (α → ℝ)} (h : Def (· ∈ s)) : IsSA s := h

theorem congr {P Q : (α → ℝ) → Prop} (h : Def P) (hPQ : ∀ v, P v ↔ Q v) : Def Q := by
  have : {v | P v} = {v | Q v} := Set.ext hPQ
  unfold Def
  rwa [← this]

theorem and {P Q : (α → ℝ) → Prop} (h1 : Def P) (h2 : Def Q) : Def (fun v => P v ∧ Q v) :=
  IsSA.inter h1 h2

theorem or {P Q : (α → ℝ) → Prop} (h1 : Def P) (h2 : Def Q) : Def (fun v => P v ∨ Q v) :=
  IsSA.union h1 h2

theorem not {P : (α → ℝ) → Prop} (h : Def P) : Def (fun v => ¬ P v) := IsSA.compl h

theorem imp {P Q : (α → ℝ) → Prop} (h1 : Def P) (h2 : Def Q) : Def (fun v => P v → Q v) :=
  (h1.not.or h2).congr fun _ => imp_iff_not_or.symm

theorem le {f g : (α → ℝ) → ℝ} (hf : PolyFn f) (hg : PolyFn g) : Def (fun v => f v ≤ g v) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  refine Def.congr (P := fun v => 0 ≤ eval v (q - p)) (isSA_nonneg (q - p)) fun v => ?_
  simp [hp, hq]

theorem lt {f g : (α → ℝ) → ℝ} (hf : PolyFn f) (hg : PolyFn g) : Def (fun v => f v < g v) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  refine Def.congr (P := fun v => 0 < eval v (q - p)) (isSA_pos (q - p)) fun v => ?_
  simp [hp, hq]

theorem eq {f g : (α → ℝ) → ℝ} (hf : PolyFn f) (hg : PolyFn g) : Def (fun v => f v = g v) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  refine Def.congr (P := fun v => eval v (p - q) = 0) (isSA_zero (p - q)) fun v => ?_
  simp [hp, hq, sub_eq_zero]

theorem comp {P : (α → ℝ) → Prop} (h : Def P) (f : α → β) : Def (fun v : β → ℝ => P (v ∘ f)) :=
  IsSA.preimage_comp h f

theorem mem_comp {s : Set (α → ℝ)} (hs : IsSA s) (f : α → β) :
    Def (fun v : β → ℝ => v ∘ f ∈ s) :=
  IsSA.preimage_comp hs f

theorem exists_fun {γ : Type} [Finite γ] {P : (α → ℝ) → (γ → ℝ) → Prop}
    (h : Def (fun u : α ⊕ γ → ℝ => P (u ∘ Sum.inl) (u ∘ Sum.inr))) :
    Def (fun v => ∃ z, P v z) :=
  IsSA.exists_sum h

theorem forall_fun {γ : Type} [Finite γ] {P : (α → ℝ) → (γ → ℝ) → Prop}
    (h : Def (fun u : α ⊕ γ → ℝ => P (u ∘ Sum.inl) (u ∘ Sum.inr))) :
    Def (fun v => ∀ z, P v z) :=
  IsSA.forall_sum h

theorem exists_real {P : (α → ℝ) → ℝ → Prop}
    (h : Def (fun u : Option α → ℝ => P (u ∘ some) (u none))) : Def (fun v => ∃ a, P v a) :=
  IsSA.exists_option h

theorem forall_real {P : (α → ℝ) → ℝ → Prop}
    (h : Def (fun u : Option α → ℝ => P (u ∘ some) (u none))) : Def (fun v => ∀ a, P v a) :=
  ((Def.exists_real (P := fun v a => ¬ P v a) h.not).not).congr fun _ => not_exists_not

theorem forall_fintype {γ : Type} [Finite γ] {P : γ → (α → ℝ) → Prop} (h : ∀ i, Def (P i)) :
    Def (fun v => ∀ i, P i v) := by
  have := IsSA.iInter_finite h
  unfold Def
  rwa [Set.iInter_ofPred] at this

end Def

end Definable

/-- `evalξw` is a polynomial function of its arguments. -/
theorem PolyFn.evalξw {α : Type} (Q : MvPolynomial (ι ⊕ κ) ℝ) {ξ : (α → ℝ) → ι → ℝ}
    {w : (α → ℝ) → κ → ℝ} (hξ : ∀ i, PolyFn (fun v => ξ v i))
    (hw : ∀ k, PolyFn (fun v => w v k)) : PolyFn (fun v => evalξw (ξ v) (w v) Q) :=
  PolyFn.eval_poly Q (g := fun b v => Sum.elim (ξ v) (w v) b) fun b => by
    cases b with
    | inl i => exact hξ i
    | inr k => exact hw k

theorem PolyFn.regG {α : Type} (Q : MvPolynomial (ι ⊕ κ) ℝ) (lam c : κ → ℝ) {e : (α → ℝ) → ℝ}
    {ξ : (α → ℝ) → ι → ℝ} {w : (α → ℝ) → κ → ℝ} (he : PolyFn e)
    (hξ : ∀ i, PolyFn (fun v => ξ v i)) (hw : ∀ k, PolyFn (fun v => w v k)) :
    PolyFn (fun v => regG Q lam c (e v) (ξ v) (w v)) := by
  unfold ClassSep.regG
  simp only [dotProduct]
  exact ((PolyFn.evalξw Q hξ hw).sub (he.mul (PolyFn.sum _ fun k => (PolyFn.const _).mul
    (hw k)))).add ((he.pow 2).mul (PolyFn.sum _ fun k => ((hw k).sub (PolyFn.const _)).pow 2))

/-- The set `Bad_c` is semialgebraic. -/
theorem isSA_badSet (Q : MvPolynomial (ι ⊕ κ) ℝ) (lam c : κ → ℝ) : IsSA (badSet Q lam c) := by
  have hcoord : ∀ i, PolyFn (fun u : Option ι ⊕ κ → ℝ => (u ∘ Sum.inl ∘ some) i) :=
    fun i => PolyFn.coord _
  have hcoordw : ∀ k, PolyFn (fun u : Option ι ⊕ κ → ℝ => (u ∘ Sum.inr) k) :=
    fun k => PolyFn.coord _
  have h1 : Def (fun u : Option ι ⊕ κ → ℝ =>
      CriticalEq Q lam c ((u ∘ Sum.inl) none) ((u ∘ Sum.inl) ∘ some) (u ∘ Sum.inr)) := by
    refine Def.forall_fintype fun k => Def.eq ?_ (PolyFn.const 0)
    exact ((PolyFn.evalξw _ hcoord hcoordw).sub ((PolyFn.coord _).mul (PolyFn.const _))).add
      (((PolyFn.const 2).mul ((PolyFn.coord _).pow 2)).mul
        ((PolyFn.coord _).sub (PolyFn.const _)))
  have h2 : Def (fun u : Option ι ⊕ κ → ℝ =>
      (hessW Q ((u ∘ Sum.inl) ∘ some) (u ∘ Sum.inr) +
        (2 * (u ∘ Sum.inl) none ^ 2) • (1 : Matrix κ κ ℝ)).det = 0) := by
    refine Def.eq (PolyFn.det fun k l => ?_) (PolyFn.const 0)
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hessW]
    exact (PolyFn.evalξw _ hcoord hcoordw).add
      (((PolyFn.const 2).mul ((PolyFn.coord _).pow 2)).mul (PolyFn.const _))
  have h := (Def.lt (PolyFn.const 0) (PolyFn.coord none)).and (Def.exists_fun
    (P := fun (v : Option ι → ℝ) (w : κ → ℝ) => CriticalEq Q lam c (v none) (v ∘ some) w ∧
      (hessW Q (v ∘ some) w + (2 * v none ^ 2) • (1 : Matrix κ κ ℝ)).det = 0) (h1.and h2))
  exact h

/-! ## Programs: unread inputs, and the program for `E` -/

namespace LocalProg

open BaurStrassen

section Indep

variable {σ : Type}

/-- The inputs read by an operand. -/
def opIn : Operand σ ℕ → List σ
  | .input i => [i]
  | _ => []

/-- The inputs read by a program graph and an output operand. -/
def progIn (prog : SLP σ ℕ) (o : Operand σ ℕ) : List σ :=
  prog.flatMap (fun ins => opIn ins.a ++ opIn ins.b) ++ opIn o

theorem length_opIn (o : Operand σ ℕ) : (opIn o).length ≤ 1 := by
  cases o <;> simp [opIn]

theorem length_progIn (prog : SLP σ ℕ) (o : Operand σ ℕ) :
    (progIn prog o).length ≤ 2 * prog.length + 1 := by
  have h : ∀ P : SLP σ ℕ,
      (P.flatMap (fun ins => opIn ins.a ++ opIn ins.b)).length ≤ 2 * P.length := by
    intro P
    induction P with
    | nil => simp
    | cons ins P ih =>
      have h1 := length_opIn ins.a
      have h2 := length_opIn ins.b
      simp only [List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
      omega
  have := h prog
  have h3 := length_opIn o
  simp only [progIn, List.length_append]
  omega

variable [DecidableEq σ]

/-- The polynomial `p` does not depend on the variable `j`. -/
def Indep (j : σ) (p : MvPolynomial σ ℝ) : Prop :=
  ∀ (x : σ → ℝ) (t : ℝ), eval (x + Pi.single j t) p = eval x p

theorem Indep.add {j : σ} {p q : MvPolynomial σ ℝ} (hp : Indep j p) (hq : Indep j q) :
    Indep j (p + q) := fun x t => by simp [hp x t, hq x t]

theorem Indep.sub {j : σ} {p q : MvPolynomial σ ℝ} (hp : Indep j p) (hq : Indep j q) :
    Indep j (p - q) := fun x t => by simp [hp x t, hq x t]

theorem Indep.mul {j : σ} {p q : MvPolynomial σ ℝ} (hp : Indep j p) (hq : Indep j q) :
    Indep j (p * q) := fun x t => by simp [hp x t, hq x t]

theorem indep_C (j : σ) (a : ℝ) : Indep j (C a) := fun x t => by simp

theorem indep_X {j i : σ} (h : i ≠ j) : Indep j (X i) := fun x t => by
  simp [h]

theorem indep_zero (j : σ) : Indep j (0 : MvPolynomial σ ℝ) := fun x t => by simp

theorem indep_apply {j : σ} (op : ArithOp) {p q : MvPolynomial σ ℝ} (hp : Indep j p)
    (hq : Indep j q) : Indep j (op.apply p q) := by
  cases op
  · exact hp.add hq
  · exact hp.sub hq
  · exact hp.mul hq

theorem indep_ev {j : σ} (c : ℕ → ℝ) (W : List (MvPolynomial σ ℝ))
    (hW : ∀ p ∈ W, Indep j p) (o : Operand σ ℕ) (ho : j ∉ opIn o) : Indep j (ev c W o) := by
  cases o with
  | input i =>
    simp only [opIn, List.mem_singleton] at ho
    exact indep_X (Ne.symm ho)
  | const m => exact indep_C j _
  | prev m =>
    simp only [ev_prev]
    by_cases hm : m < W.length
    · rw [List.getD_eq_getElem _ _ hm]
      exact hW _ (List.getElem_mem hm)
    · rw [List.getD_eq_default _ _ (not_lt.1 hm)]
      exact indep_zero j

theorem indep_vals {j : σ} (c : ℕ → ℝ) (P : SLP σ ℕ)
    (hP : ∀ ins ∈ P, j ∉ opIn ins.a ∧ j ∉ opIn ins.b) : ∀ p ∈ vals c P, Indep j p := by
  induction P using List.reverseRecOn with
  | nil => simp [vals, SLP.instantiate, SLP.values]
  | append_singleton P ins ih =>
    have ih' := ih fun ins' h => hP ins' (List.mem_append_left _ h)
    have hins := hP ins (List.mem_append_right _ (List.mem_singleton_self _))
    rw [vals_append_single]
    intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact ih' p hp
    · rw [List.mem_singleton] at hp
      subst hp
      exact indep_apply _ (indep_ev c _ ih' _ hins.1) (indep_ev c _ ih' _ hins.2)

theorem indep_progOutput {j : σ} (c : ℕ → ℝ) (prog : SLP σ ℕ) (o : Operand σ ℕ)
    (hj : j ∉ progIn prog o) : Indep j (progOutput prog c o) := by
  have hP : ∀ ins ∈ prog, j ∉ opIn ins.a ∧ j ∉ opIn ins.b := by
    intro ins hins
    constructor <;> intro h <;> refine hj (List.mem_append_left _ (List.mem_flatMap.2 ⟨ins, hins, ?_⟩))
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ h
  have ho : j ∉ opIn o := fun h => hj (List.mem_append_right _ h)
  exact indep_ev c _ (indep_vals c prog hP) o ho

end Indep

/-- If `Q` does not involve some `w_j`, the hypotheses of Theorem 3.5 cannot hold: moving
`φ(ξ₀)` along `e_j` gives another zero in `B̄` with at least the same value of `⟨λ, ·⟩`. -/
theorem not_localHyp_of_indep {Q : MvPolynomial (ι ⊕ κ) ℝ} {j : κ} (hj : Indep (Sum.inr j) Q)
    {ξ₀ : ι → ℝ} {ρ : ℝ} {w₀ : κ → ℝ} {r₀ : ℝ} {lam : κ → ℝ} {φ : (ι → ℝ) → (κ → ℝ)} :
    ¬ LocalHyp Q ξ₀ ρ w₀ r₀ lam φ := by
  intro h
  have hξ₀ : ξ₀ ∈ Metric.closedBall ξ₀ ρ := Metric.mem_closedBall_self h.ρ_pos.le
  set t : ℝ := if 0 ≤ lam j then r₀ / 2 else -(r₀ / 2) with ht
  have ht0 : t ≠ 0 := by
    have := h.r₀_pos
    rw [ht]; split_ifs <;> [exact ne_of_gt (by positivity); exact neg_ne_zero.2 (by positivity)]
  have htabs : |t| = r₀ / 2 := by
    have := h.r₀_pos
    rw [ht]; split_ifs
    · exact abs_of_pos (by positivity)
    · rw [abs_neg]; exact abs_of_pos (by positivity)
  have hlt : 0 ≤ lam j * t := by
    rw [ht]; split_ifs with hl
    · exact mul_nonneg hl (by linarith [h.r₀_pos])
    · push Not at hl
      nlinarith [h.r₀_pos]
  set w' : κ → ℝ := φ ξ₀ + Pi.single j t with hw'
  have hzero : evalξw ξ₀ w' Q = 0 := by
    have e : Sum.elim ξ₀ w' = Sum.elim ξ₀ (φ ξ₀) + Pi.single (Sum.inr j) t := by
      funext v
      cases v with
      | inl i => simp
      | inr k => simp [hw', Pi.single_apply]
    simp only [evalξw]
    rw [e, hj]
    exact h.zero ξ₀ hξ₀
  have hmem : w' ∈ Metric.closedBall w₀ r₀ := by
    rw [Metric.mem_closedBall, dist_pi_le_iff h.r₀_pos.le]
    intro k
    have hk : dist (φ ξ₀ k) (w₀ k) ≤ r₀ / 2 :=
      (dist_le_pi_dist (φ ξ₀) w₀ k).trans (h.near ξ₀ hξ₀)
    rw [Real.dist_eq] at hk ⊢
    by_cases hkj : k = j
    · subst hkj
      simp only [hw', Pi.add_apply, Pi.single_eq_same]
      calc |φ ξ₀ k + t - w₀ k| = |(φ ξ₀ k - w₀ k) + t| := by ring_nf
        _ ≤ |φ ξ₀ k - w₀ k| + |t| := abs_add_le _ _
        _ ≤ r₀ := by rw [htabs]; linarith
    · simp only [hw', Pi.add_apply, Pi.single_eq_of_ne hkj, add_zero]
      linarith [h.r₀_pos]
  have hne : w' ≠ φ ξ₀ := by
    intro he
    have := congrFun he j
    simp [hw'] at this
    exact ht0 this
  have := h.unique ξ₀ hξ₀ w' hmem hzero hne
  rw [hw', dotProduct_add, dotProduct_single] at this
  linarith

section QProg

/-- Shift the constant slots of an operand by `K`. -/
def shC {σ : Type} (K : ℕ) : Operand σ ℕ → Operand σ ℕ
  | .input i => .input i
  | .const m => .const (m + K)
  | .prev j => .prev j

/-- Shift the constant slots of a program graph by `K`. -/
def shProg {σ : Type} (K : ℕ) (prog : SLP σ ℕ) : SLP σ ℕ :=
  prog.map fun ins => ⟨ins.op, shC K ins.a, shC K ins.b⟩

/-- The output operand of a program of length `n`, with constants shifted by `K` and forward
references (which read `0`) replaced by the slot `0`. -/
def normO {σ : Type} (K n : ℕ) : Operand σ ℕ → Operand σ ℕ
  | .input i => .input i
  | .const m => .const (m + K)
  | .prev j => if j < n then .prev j else .const 0

/-- The slot holding the constant `αₖ`. -/
def kIdx (k : κ) : ℕ := (Fintype.equivFin κ k : ℕ) + 2

/-- Instructions adding `∑ₖ (e₂ wₖ + αₖ) wₖ` to the accumulator `acc` (slot `1` holds `e₂`,
slot `kIdx k` holds `αₖ`), starting at position `n`. -/
def tailP (n : ℕ) (acc : Operand (ι ⊕ κ) ℕ) : List κ → SLP (ι ⊕ κ) ℕ
  | [] => []
  | k :: ks => ⟨.mul, .const 1, .input (.inr k)⟩ :: ⟨.add, .prev n, .const (kIdx k)⟩ ::
      ⟨.mul, .prev (n + 1), .input (.inr k)⟩ :: ⟨.add, acc, .prev (n + 2)⟩ ::
      tailP (n + 4) (.prev (n + 3)) ks

/-- The output of `tailP`. -/
def tailO (n : ℕ) (acc : Operand (ι ⊕ κ) ℕ) : List κ → Operand (ι ⊕ κ) ℕ
  | [] => acc
  | _ :: ks => tailO (n + 4) (.prev (n + 3)) ks

theorem length_tailP (n : ℕ) (acc : Operand (ι ⊕ κ) ℕ) (ks : List κ) :
    (tailP n acc ks).length = 4 * ks.length := by
  induction ks generalizing n acc with
  | nil => rfl
  | cons k ks ih => simp only [tailP, List.length_cons, ih]; ring

/-- The program for `Q' = Q + ∑ₖ (e₂ wₖ + αₖ) wₖ`. -/
def qProg (prog : SLP (ι ⊕ κ) ℕ) (o : Operand (ι ⊕ κ) ℕ) : SLP (ι ⊕ κ) ℕ :=
  shProg (Fintype.card κ + 2) prog ++
    tailP prog.length (normO (Fintype.card κ + 2) prog.length o) (Finset.univ : Finset κ).toList

/-- The output operand of `qProg`. -/
def qOut (prog : SLP (ι ⊕ κ) ℕ) (o : Operand (ι ⊕ κ) ℕ) : Operand (ι ⊕ κ) ℕ :=
  tailO prog.length (normO (Fintype.card κ + 2) prog.length o) (Finset.univ : Finset κ).toList

/-- The new constants. -/
def extraC (e2 : ℝ) (al : κ → ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => e2
  | j + 2 => if h : j < Fintype.card κ then al ((Fintype.equivFin κ).symm ⟨j, h⟩) else 0

/-- The constants of `qProg`. -/
def qConst (cQ : ℕ → ℝ) (e2 : ℝ) (al : κ → ℝ) (m : ℕ) : ℝ :=
  if m < Fintype.card κ + 2 then extraC e2 al m else cQ (m - (Fintype.card κ + 2))

theorem length_qProg (prog : SLP (ι ⊕ κ) ℕ) (o : Operand (ι ⊕ κ) ℕ) :
    (qProg prog o).length = prog.length + 4 * Fintype.card κ := by
  simp [qProg, shProg, length_tailP]

theorem ev_last' (c : ℕ → ℝ) (P : SLP (ι ⊕ κ) ℕ) (ins : Instr (ι ⊕ κ) ℕ) {m : ℕ}
    (hm : m = P.length) :
    ev c (vals c (P ++ [ins])) (.prev m) =
      ins.op.apply (ev c (vals c P) ins.a) (ev c (vals c P) ins.b) := by
  subst hm; exact ev_last c P ins

theorem tail_spec (c : ℕ → ℝ) (e2 : ℝ) (al : κ → ℝ) (hc1 : c 1 = e2)
    (hck : ∀ k, c (kIdx k) = al k) :
    ∀ (ks : List κ) (P : SLP (ι ⊕ κ) ℕ) (acc : Operand (ι ⊕ κ) ℕ), Valid P.length acc →
      ev c (vals c (P ++ tailP P.length acc ks)) (tailO P.length acc ks) =
        ev c (vals c P) acc +
          (ks.map fun k => (C e2 * X (Sum.inr k) + C (al k)) * X (Sum.inr k)).sum := by
  intro ks
  induction ks with
  | nil => intro P acc _; simp [tailP, tailO]
  | cons k ks ih =>
    intro P acc hacc
    set n := P.length with hn
    set i1 : Instr (ι ⊕ κ) ℕ := ⟨.mul, .const 1, .input (.inr k)⟩
    set i2 : Instr (ι ⊕ κ) ℕ := ⟨.add, .prev n, .const (kIdx k)⟩
    set i3 : Instr (ι ⊕ κ) ℕ := ⟨.mul, .prev (n + 1), .input (.inr k)⟩
    set i4 : Instr (ι ⊕ κ) ℕ := ⟨.add, acc, .prev (n + 2)⟩
    set P1 := P ++ [i1]
    set P2 := P1 ++ [i2]
    set P3 := P2 ++ [i3]
    set P4 := P3 ++ [i4]
    have hP4 : P4.length = n + 4 := by simp [P4, P3, P2, P1, hn]
    have e : P ++ tailP n acc (k :: ks) = P4 ++ tailP P4.length (.prev (n + 3)) ks := by
      rw [hP4]; simp [tailP, P4, P3, P2, P1, i1, i2, i3, i4]
    have e' : tailO n acc (k :: ks) = tailO P4.length (.prev (n + 3)) ks := by
      rw [hP4]; rfl
    rw [e, e', ih P4 _ (by show n + 3 < P4.length; omega)]
    have v1 : ev c (vals c P1) (.prev n) = C e2 * X (Sum.inr k) := by
      rw [ev_last' c P i1 hn]; simp [i1, ArithOp.apply, hc1]
    have v2 : ev c (vals c P2) (.prev (n + 1)) = C e2 * X (Sum.inr k) + C (al k) := by
      rw [ev_last' c P1 i2 (by simp [P1, hn]), ← v1]; simp [i2, ArithOp.apply, hck]
    have v3 : ev c (vals c P3) (.prev (n + 2)) =
        (C e2 * X (Sum.inr k) + C (al k)) * X (Sum.inr k) := by
      rw [ev_last' c P2 i3 (by simp [P2, P1, hn]), ← v2]; simp [i3, ArithOp.apply]
    have hpre : P <+: P3 := by
      simp only [P3, P2, P1, List.append_assoc]; exact List.prefix_append _ _
    rw [ev_last' c P3 i4 (by simp [P3, P2, P1, hn])]
    simp only [i4, ArithOp.apply, List.map_cons, List.sum_cons]
    rw [v3, ev_mono c hpre hacc]
    ring

theorem progOutput_qProg (prog : SLP (ι ⊕ κ) ℕ) (o : Operand (ι ⊕ κ) ℕ) (cQ : ℕ → ℝ)
    (e2 : ℝ) (al : κ → ℝ) :
    progOutput (qProg prog o) (qConst cQ e2 al) (qOut prog o) =
      progOutput prog cQ o +
        ∑ k, (C e2 * X (Sum.inr k) + C (al k)) * X (Sum.inr k) := by
  set K := Fintype.card κ + 2 with hK
  set c' := qConst cQ e2 al with hc'
  have hshift : ∀ m, c' (m + K) = cQ m := by
    intro m; simp [hc', qConst, hK]
  have h0 : c' 0 = 0 := by simp [hc', qConst, extraC]
  have h1 : c' 1 = e2 := by simp [hc', qConst, extraC]
  have hk : ∀ k, c' (kIdx k) = al k := by
    intro k
    have hlt : (Fintype.equivFin κ k : ℕ) < Fintype.card κ := (Fintype.equivFin κ k).2
    simp [hc', qConst, kIdx, extraC, hlt]
  have hvals : vals c' (shProg K prog) = vals cQ prog := by
    have h : ∀ x : Operand (ι ⊕ κ) ℕ, (shC K x).instantiate c' = x.instantiate cQ := by
      intro x
      cases x with
      | const m => simp only [shC, Operand.instantiate, hshift]
      | _ => rfl
    simp only [vals, shProg, SLP.instantiate, List.map_map]
    congr 2
    funext ins
    simp [h]
  have hlen : (shProg K prog).length = prog.length := by simp [shProg]
  have hvalid : Valid (shProg K prog).length (normO K prog.length o) := by
    rw [hlen]
    cases o with
    | prev j =>
      simp only [normO]
      split_ifs with h
      · exact h
      · trivial
    | _ => trivial
  have hacc : ev c' (vals c' (shProg K prog)) (normO K prog.length o) = progOutput prog cQ o := by
    rw [hvals]
    change _ = ev cQ (vals cQ prog) o
    cases o with
    | input i => rfl
    | const m => simp [normO, hshift]
    | prev j =>
      simp only [normO]
      split_ifs with hj
      · rfl
      · simp only [ev_const, ev_prev, h0, map_zero]
        rw [List.getD_eq_default _ _ (by rw [length_vals]; omega)]
  have := tail_spec c' e2 al h1 hk (Finset.univ : Finset κ).toList (shProg K prog)
    (normO K prog.length o) hvalid
  rw [hlen, hacc, Finset.sum_map_toList] at this
  exact this

omit [DecidableEq ι] in
theorem pderiv_extra (k : κ) (e2 : ℝ) (al : κ → ℝ) :
    pderiv (Sum.inr k)
        (∑ l, (C e2 * X (Sum.inr l) + C (al l)) * X (Sum.inr l) : MvPolynomial (ι ⊕ κ) ℝ) =
      C (2 * e2) * X (Sum.inr k) + C (al k) := by
  classical
  rw [map_sum]
  rw [Finset.sum_eq_single k]
  · simp only [Derivation.leibniz, pderiv_X, Pi.single_eq_same, map_add, pderiv_C, smul_eq_mul,
      mul_one, add_zero, mul_zero]
    simp [two_mul]
    ring
  · intro l _ hl
    have : (Sum.inr l : ι ⊕ κ) ≠ Sum.inr k := fun h => hl (Sum.inr_injective h)
    simp [Derivation.leibniz, pderiv_X, this]
  · simp

end QProg

end LocalProg

/-! ## Derivatives of polynomial functions along lines -/

/-- The derivative of a polynomial along a line: `d/ds P(p + s v) = ∑ᵢ vᵢ ∂ᵢP(p + s v)`. -/
theorem hasDerivAt_eval_line {σ : Type} [Fintype σ] [DecidableEq σ] (P : MvPolynomial σ ℝ)
    (p v : σ → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => eval (p + s • v) P) (∑ i, v i * eval (p + t • v) (pderiv i P)) t := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const t a
  | add P Q hP hQ =>
    convert hP.add hQ using 1
    · funext s; simp
    · simp [mul_add, Finset.sum_add_distrib]
  | mul_X P i hP =>
    have hXi : HasDerivAt (fun s : ℝ => (p + s • v) i) (v i) t := by
      simpa using ((hasDerivAt_id t).mul_const (v i)).const_add (p i)
    convert hP.mul hXi using 1
    · funext s; simp
    · have hsing : ∀ j, eval (p + t • v) (pderiv j (X i : MvPolynomial σ ℝ)) =
          if j = i then 1 else 0 := by
        intro j
        by_cases hji : j = i
        · subst hji; simp
        · simp [pderiv_X, Ne.symm hji, hji]
      simp only [pderiv_mul, map_add, map_mul, eval_X, hsing, mul_add, Finset.sum_add_distrib,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_mul]
      congr 1
      · refine Finset.sum_congr rfl fun j _ => ?_
        ring
      · ring

/-! ## Lemma 3.7 -/

/-- The map `Φ(ξ, ε, w) = (ξ, ε, w + (∇_w Q(ξ, w) - ελ)/(2ε²))` on `ℝ^(Option ι ⊕ κ)` (the
coordinate `Sum.inl none` is `ε`). -/
def PhiMap (Q : MvPolynomial (ι ⊕ κ) ℝ) (lam : κ → ℝ) (x : Option ι ⊕ κ → ℝ) :
    Option ι ⊕ κ → ℝ :=
  Sum.elim (fun o => x (Sum.inl o)) (fun k => x (Sum.inr k) +
    (eval (x ∘ Sum.map some id) (pderiv (Sum.inr k) Q) - x (Sum.inl none) * lam k) /
      (2 * x (Sum.inl none) ^ 2))

/-- The open set `{ε > 0}`. -/
def posSet : Set (Option ι ⊕ κ → ℝ) := {x | 0 < x (Sum.inl none)}

theorem isOpen_posSet : IsOpen (posSet (ι := ι) (κ := κ)) :=
  isOpen_lt continuous_const (continuous_apply _)

theorem analyticOnNhd_PhiMap (Q : MvPolynomial (ι ⊕ κ) ℝ) (lam : κ → ℝ) :
    AnalyticOnNhd ℝ (PhiMap Q lam) posSet := by
  intro x hx
  have hproj : ∀ a : Option ι ⊕ κ, AnalyticAt ℝ (fun y : Option ι ⊕ κ → ℝ => y a) x :=
    fun a => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Option ι ⊕ κ => ℝ) a).analyticAt x
  refine AnalyticAt.pi (f := fun a y => PhiMap Q lam y a) fun a => ?_
  cases a with
  | inl o => exact hproj (Sum.inl o)
  | inr k =>
    have hev : AnalyticAt ℝ (fun y : Option ι ⊕ κ → ℝ =>
        eval (y ∘ Sum.map some id) (pderiv (Sum.inr k) Q)) x := by
      have := AnalyticOnNhd.eval_mvPolynomial (rename (Sum.map some id) (pderiv (Sum.inr k) Q))
        x (mem_univ _)
      simpa [eval_rename] using this
    have hden : (2 * x (Sum.inl none) ^ 2) ≠ 0 := by
      have : 0 < x (Sum.inl none) := hx
      positivity
    exact (hproj _).add ((hev.sub ((hproj _).mul analyticAt_const)).div
      (analyticAt_const.mul ((hproj _).pow 2)) hden)

theorem isSAFunOn_PhiMap (Q : MvPolynomial (ι ⊕ κ) ℝ) (lam : κ → ℝ) :
    IsSAFunOn posSet (PhiMap Q lam) := by
  have hO : Def (fun x : Option ι ⊕ κ → ℝ => 0 < x (Sum.inl none)) :=
    Def.lt (PolyFn.const 0) (PolyFn.coord _)
  refine ⟨hO, ?_⟩
  have hev : ∀ k, PolyFn (fun v : (Option ι ⊕ κ) ⊕ (Option ι ⊕ κ) → ℝ =>
      eval ((v ∘ Sum.inl) ∘ Sum.map some id) (pderiv (Sum.inr k) Q)) := fun k =>
    PolyFn.eval_poly _ (g := fun b v => ((v ∘ Sum.inl) ∘ Sum.map some id) b)
      fun b => PolyFn.coord _
  have h := (Def.comp hO (Sum.inl : Option ι ⊕ κ → (Option ι ⊕ κ) ⊕ (Option ι ⊕ κ))).and
    ((Def.forall_fintype fun o : Option ι =>
      Def.eq (PolyFn.coord (Sum.inl (Sum.inl o))) (PolyFn.coord (Sum.inr (Sum.inl o)))).and
    (Def.forall_fintype fun k : κ =>
      Def.eq ((((PolyFn.const 2).mul ((PolyFn.coord (Sum.inl (Sum.inl none))).pow 2)).mul
        ((PolyFn.coord (Sum.inr (Sum.inr k))).sub (PolyFn.coord (Sum.inl (Sum.inr k))))))
        ((hev k).sub ((PolyFn.coord (Sum.inl (Sum.inl none))).mul (PolyFn.const (lam k))))))
  refine (h.congr fun v => ?_).isSA
  simp only [mem_ofPred_eq, posSet, Function.comp_apply]
  constructor
  · rintro ⟨hpos, h1, h2⟩
    refine ⟨hpos, ?_⟩
    funext a
    cases a with
    | inl o => exact h1 o
    | inr k =>
      simp only [PhiMap, Function.comp_apply, Sum.elim_inr]
      have hd : (2 * v (Sum.inl (Sum.inl none)) ^ 2) ≠ 0 := by positivity
      rw [← h2 k]
      field_simp
      ring
  · rintro ⟨hpos, hΦ⟩
    refine ⟨hpos, fun o => congrFun hΦ (Sum.inl o), fun k => ?_⟩
    have := congrFun hΦ (Sum.inr k)
    simp only [PhiMap, Function.comp_apply, Sum.elim_inr] at this
    have hd : (2 * v (Sum.inl (Sum.inl none)) ^ 2) ≠ 0 := by positivity
    rw [← this]
    field_simp
    ring

/-- At a point of `Bad_c`, `(ξ, ε, c)` is a critical value of `Φ`. -/
theorem badSet_subset_critical (Q : MvPolynomial (ι ⊕ κ) ℝ) (lam c : κ → ℝ) :
    badSet Q lam c ⊆ fiberOver {y | ∃ p ∈ posSet, PhiMap Q lam p = y ∧
      ¬ Function.Surjective (fderiv ℝ (PhiMap Q lam) p)} c := by
  rintro v ⟨hpos, w, hcrit, hdet⟩
  set ε := v none with hε
  set p : Option ι ⊕ κ → ℝ := Sum.elim v w with hp
  have hpO : p ∈ posSet := hpos
  have hpf : p ∘ Sum.map some id = Sum.elim (v ∘ some) w := by
    funext a; cases a <;> rfl
  have hd : (2 * ε ^ 2) ≠ 0 := by positivity
  refine ⟨p, hpO, ?_, ?_⟩
  · funext a
    cases a with
    | inl o => rfl
    | inr k =>
      simp only [PhiMap, Sum.elim_inr, hpf]
      have hk := hcrit k
      simp only [evalξw] at hk
      change w k + (eval (Sum.elim (v ∘ some) w) (pderiv (Sum.inr k) Q) - ε * lam k) /
        (2 * ε ^ 2) = c k
      field_simp
      linear_combination hk
  · -- a kernel vector of `∇²_w Q + 2ε² I` gives a kernel vector of `dΦ`
    obtain ⟨u, hu0, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    set dv : Option ι ⊕ κ → ℝ := Sum.elim 0 u with hdv
    have hdv0 : dv ≠ 0 := by
      intro h0
      apply hu0
      funext l
      exact congrFun h0 (Sum.inr l)
    have hdiff : DifferentiableAt ℝ (PhiMap Q lam) p :=
      (analyticOnNhd_PhiMap Q lam p hpO).differentiableAt
    have h1 : HasDerivAt (fun t : ℝ => PhiMap Q lam (p + t • dv))
        (fderiv ℝ (PhiMap Q lam) p dv) 0 := by
      have hγ : HasDerivAt (fun t : ℝ => p + t • dv) dv 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const dv).const_add p
      exact hdiff.hasFDerivAt.comp_hasDerivAt_of_eq 0 hγ (by simp)
    have h2 : HasDerivAt (fun t : ℝ => PhiMap Q lam (p + t • dv)) 0 0 := by
      rw [hasDerivAt_pi]
      intro a
      cases a with
      | inl o =>
        have e : (fun t : ℝ => PhiMap Q lam (p + t • dv) (Sum.inl o)) = fun _ => p (Sum.inl o) := by
          funext t; simp [PhiMap, hdv]
        rw [e]
        exact hasDerivAt_const _ _
      | inr k =>
        have e : (fun t : ℝ => PhiMap Q lam (p + t • dv) (Sum.inr k)) = fun t =>
            (w k + t * u k) + (eval (Sum.elim (v ∘ some) w + t • Sum.elim (0 : ι → ℝ) u)
              (pderiv (Sum.inr k) Q) - ε * lam k) / (2 * ε ^ 2) := by
          funext t
          have e1 : (p + t • dv) ∘ Sum.map some id = Sum.elim (v ∘ some) w + t • Sum.elim (0 : ι → ℝ) u := by
            funext a; cases a <;> simp [hp, hdv]
          simp only [PhiMap, Sum.elim_inr, e1]
          simp [hp, hdv, hε]
        rw [e]
        have hl := hasDerivAt_eval_line (pderiv (Sum.inr k) Q) (Sum.elim (v ∘ some) w)
          (Sum.elim (0 : ι → ℝ) u) 0
        have h3 := (((hasDerivAt_id (0 : ℝ)).mul_const (u k)).const_add (w k)).add
          ((hl.sub_const (ε * lam k)).div_const (2 * ε ^ 2))
        convert h3 using 1
        · funext t
          simp only [Pi.add_apply, id]
        · have hk := congrFun hu k
          simp only [Matrix.mulVec, dotProduct, Matrix.add_apply, Matrix.smul_apply,
            Matrix.one_apply, smul_eq_mul, Pi.zero_apply, add_mul, Finset.sum_add_distrib,
            mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
            ite_true, hessW, evalξw] at hk
          simp only [Fintype.sum_sum_type, Sum.elim_inl, Pi.zero_apply, zero_mul,
            Finset.sum_const_zero, zero_add, Sum.elim_inr, zero_smul, add_zero, one_mul]
          simp_rw [mul_comm (u _) _]
          field_simp
          linear_combination (-1 : ℝ) * hk
    have hzero : fderiv ℝ (PhiMap Q lam) p dv = 0 := h1.unique h2
    intro hsurj
    have hinj : Function.Injective (fderiv ℝ (PhiMap Q lam) p : (Option ι ⊕ κ → ℝ) →ₗ[ℝ] _) :=
      LinearMap.injective_iff_surjective.2 hsurj
    exact hdv0 (hinj (by simpa using hzero))

/-! ## Lemma 3.6 -/

theorem continuous_evalξw (Q : MvPolynomial (ι ⊕ κ) ℝ) :
    Continuous (fun p : (ι → ℝ) × (κ → ℝ) => evalξw p.1 p.2 Q) := by
  refine (MvPolynomial.continuous_eval Q).comp (continuous_pi fun v => ?_)
  cases v with
  | inl i => exact (continuous_apply i).comp continuous_fst
  | inr k => exact (continuous_apply k).comp continuous_snd

/-- The derivative of `G_{c,ε}(ξ, ·)` along the coordinate direction `eₖ`. -/
theorem hasDerivAt_regG_line (Q : MvPolynomial (ι ⊕ κ) ℝ) (lam c : κ → ℝ) (ε : ℝ)
    (ξ : ι → ℝ) (w : κ → ℝ) (k : κ) :
    HasDerivAt (fun t : ℝ => regG Q lam c ε ξ (w + t • Pi.single k 1))
      (evalξw ξ w (pderiv (Sum.inr k) Q) - ε * lam k + 2 * ε ^ 2 * (w k - c k)) 0 := by
  set e : κ → ℝ := Pi.single k 1 with he
  have e1 : ∀ t : ℝ, Sum.elim ξ (w + t • e) =
      Sum.elim ξ w + t • Pi.single (Sum.inr k) (1 : ℝ) := by
    intro t
    funext a
    cases a with
    | inl i => simp
    | inr l => simp [he, Pi.single_apply]
  have hQ := hasDerivAt_eval_line Q (Sum.elim ξ w) (Pi.single (Sum.inr k) 1) 0
  have hQ' : HasDerivAt (fun t : ℝ => evalξw ξ (w + t • e) Q)
      (evalξw ξ w (pderiv (Sum.inr k) Q)) 0 := by
    convert hQ using 1
    · funext t
      simp only [evalξw, e1]
    · simp [Pi.single_apply]
  have hlin : HasDerivAt (fun t : ℝ => lam ⬝ᵥ (w + t • e)) (lam k) 0 := by
    have : (fun t : ℝ => lam ⬝ᵥ (w + t • e)) = fun t => lam ⬝ᵥ w + t * lam k := by
      funext t
      rw [dotProduct_add, dotProduct_smul, he, dotProduct_single, smul_eq_mul, mul_one,
        mul_comm]
    rw [this]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (lam k)).const_add (lam ⬝ᵥ w)
  have hsq : HasDerivAt (fun t : ℝ => ∑ l, ((w + t • e : κ → ℝ) l - c l) ^ 2)
      (2 * (w k - c k)) 0 := by
    have : (fun t : ℝ => ∑ l, ((w + t • e : κ → ℝ) l - c l) ^ 2) =
        fun t => ∑ l, (w l - c l) ^ 2 + (2 * (w k - c k) * t + t ^ 2) := by
      funext t
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k),
        ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
      have : ∀ l ∈ Finset.univ.erase k,
          ((w + t • e : κ → ℝ) l - c l) ^ 2 = (w l - c l) ^ 2 := by
        intro l hl
        rw [Finset.mem_erase] at hl
        simp [he, hl.1]
      rw [Finset.sum_congr rfl this]
      simp only [he, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
      ring
    rw [this]
    convert ((((hasDerivAt_id (0 : ℝ)).const_mul (2 * (w k - c k))).add
      ((hasDerivAt_id (0 : ℝ)).pow 2)).const_add (∑ l, (w l - c l) ^ 2)) using 1 <;> simp
  have := (hQ'.sub (hlin.const_mul ε)).add (hsq.const_mul (ε ^ 2))
  unfold regG
  convert this using 1
  ring

/-- At an interior minimizer, the critical point equation (4) holds. -/
theorem criticalEq_of_isLocalMin {Q : MvPolynomial (ι ⊕ κ) ℝ} {lam c : κ → ℝ} {ε : ℝ}
    {ξ : ι → ℝ} {w : κ → ℝ} (hmin : IsLocalMin (fun w => regG Q lam c ε ξ w) w) :
    CriticalEq Q lam c ε ξ w := by
  intro k
  have hc : Continuous (fun t : ℝ => w + t • Pi.single k (1 : ℝ)) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have ht : Tendsto (fun t : ℝ => w + t • Pi.single k (1 : ℝ)) (𝓝 0) (𝓝 w) := by
    have := hc.tendsto 0
    simpa only [zero_smul, add_zero] using this
  have hmin' : ∀ᶠ y in 𝓝 w, regG Q lam c ε ξ w ≤ regG Q lam c ε ξ y := hmin
  have hline : IsLocalMin (fun t : ℝ => regG Q lam c ε ξ (w + t • Pi.single k 1)) 0 := by
    have h1 := ht.eventually hmin'
    show ∀ᶠ t in 𝓝 (0 : ℝ), regG Q lam c ε ξ (w + (0 : ℝ) • Pi.single k 1) ≤
      regG Q lam c ε ξ (w + t • Pi.single k 1)
    rw [zero_smul, add_zero]
    exact h1
  exact hline.hasDerivAt_eq_zero (hasDerivAt_regG_line Q lam c ε ξ w k)

/-- The bounds (5) of the proof of Lemma 3.6. -/
theorem minimiser_bounds {Q : MvPolynomial (ι ⊕ κ) ℝ} {ξ₀ : ι → ℝ} {ρ : ℝ} {w₀ : κ → ℝ}
    {r₀ : ℝ} {lam : κ → ℝ} {φ : (ι → ℝ) → (κ → ℝ)} (h : LocalHyp Q ξ₀ ρ w₀ r₀ lam φ)
    (c : κ → ℝ) :
    ∃ M L : ℝ, ∀ ξ ∈ Metric.closedBall ξ₀ ρ, ∀ ε > 0, ∀ w ∈ Metric.closedBall w₀ r₀,
      (∀ w' ∈ Metric.closedBall w₀ r₀, regG Q lam c ε ξ w ≤ regG Q lam c ε ξ w') →
      evalξw ξ w Q ≤ ε * L + ε ^ 2 * M ∧ lam ⬝ᵥ φ ξ - ε * M ≤ lam ⬝ᵥ w := by
  set M : ℝ := Fintype.card κ * (r₀ + dist w₀ c) ^ 2 with hM
  set L : ℝ := ∑ k, |lam k| * (2 * r₀) with hL
  refine ⟨M, L, ?_⟩
  intro ξ hξ ε hε w hw hmin
  have hr₀ := h.r₀_pos
  have hφw₀ : dist (φ ξ) w₀ ≤ r₀ / 2 := h.near ξ hξ
  have hφB : φ ξ ∈ Metric.closedBall w₀ r₀ := by
    rw [Metric.mem_closedBall]; linarith
  have hG := hmin (φ ξ) hφB
  have hSφ : ∑ k, (φ ξ k - c k) ^ 2 ≤ M := by
    calc ∑ k, (φ ξ k - c k) ^ 2 ≤ ∑ _k : κ, (r₀ + dist w₀ c) ^ 2 :=
          Finset.sum_le_sum fun k _ => ?_
      _ = M := by simp [hM]
    have h1 : |φ ξ k - w₀ k| ≤ r₀ := by
      have := (dist_le_pi_dist (φ ξ) w₀ k).trans hφw₀
      rw [Real.dist_eq] at this
      linarith
    have h2 : |w₀ k - c k| ≤ dist w₀ c := by
      have := dist_le_pi_dist w₀ c k
      rwa [Real.dist_eq] at this
    have h3 : |φ ξ k - c k| ≤ r₀ + dist w₀ c := by
      calc |φ ξ k - c k| = |(φ ξ k - w₀ k) + (w₀ k - c k)| := by ring_nf
        _ ≤ |φ ξ k - w₀ k| + |w₀ k - c k| := abs_add_le _ _
        _ ≤ r₀ + dist w₀ c := add_le_add h1 h2
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h3 2
  have hLb : lam ⬝ᵥ w - lam ⬝ᵥ φ ξ ≤ L := by
    rw [← dotProduct_sub]
    unfold dotProduct
    refine Finset.sum_le_sum fun k _ => ?_
    have h1 : |w k - φ ξ k| ≤ 2 * r₀ := by
      have a1 := dist_le_pi_dist w w₀ k
      have a2 := dist_le_pi_dist (φ ξ) w₀ k
      rw [Real.dist_eq] at a1 a2
      have hw' : dist w w₀ ≤ r₀ := hw
      calc |w k - φ ξ k| = |(w k - w₀ k) - (φ ξ k - w₀ k)| := by ring_nf
        _ ≤ |w k - w₀ k| + |φ ξ k - w₀ k| := abs_sub _ _
        _ ≤ 2 * r₀ := by linarith
    calc lam k * (w - φ ξ) k ≤ |lam k * (w - φ ξ) k| := le_abs_self _
      _ = |lam k| * |w k - φ ξ k| := by rw [abs_mul]; rfl
      _ ≤ |lam k| * (2 * r₀) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have hQφ := h.zero ξ hξ
  have hQw := h.nonneg ξ hξ w hw
  have hSw : 0 ≤ ε ^ 2 * ∑ k, (w k - c k) ^ 2 :=
    mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun k _ => sq_nonneg _)
  have hSφ' : ε ^ 2 * ∑ k, (φ ξ k - c k) ^ 2 ≤ ε ^ 2 * M :=
    mul_le_mul_of_nonneg_left hSφ (sq_nonneg _)
  simp only [regG] at hG
  rw [hQφ] at hG
  have key : evalξw ξ w Q - ε * (lam ⬝ᵥ w) ≤ -(ε * (lam ⬝ᵥ φ ξ)) + ε ^ 2 * M := by linarith
  have hεL : ε * (lam ⬝ᵥ w - lam ⬝ᵥ φ ξ) ≤ ε * L := mul_le_mul_of_nonneg_left hLb hε.le
  refine ⟨by linarith [mul_sub ε (lam ⬝ᵥ w) (lam ⬝ᵥ φ ξ)], ?_⟩
  have : ε * (lam ⬝ᵥ φ ξ - ε * M) ≤ ε * (lam ⬝ᵥ w) := by nlinarith
  exact le_of_mul_le_mul_left this hε

/-- Uniform convergence in Lemma 3.6, from the bounds (5) and the uniqueness (3), by
compactness. -/
theorem minimiser_conv {Q : MvPolynomial (ι ⊕ κ) ℝ} {ξ₀ : ι → ℝ} {ρ : ℝ} {w₀ : κ → ℝ}
    {r₀ : ℝ} {lam : κ → ℝ} {φ : (ι → ℝ) → (κ → ℝ)} (h : LocalHyp Q ξ₀ ρ w₀ r₀ lam φ)
    (M L : ℝ) :
    ∀ η > 0, ∃ ε₁ > 0, ∀ ξ ∈ Metric.closedBall ξ₀ ρ, ∀ ε ∈ Ioo 0 ε₁,
      ∀ w ∈ Metric.closedBall w₀ r₀, evalξw ξ w Q ≤ ε * L + ε ^ 2 * M →
        lam ⬝ᵥ φ ξ - ε * M ≤ lam ⬝ᵥ w → dist w (φ ξ) < η := by
  intro η hη
  by_contra hcon
  push Not at hcon
  have hseq : ∀ n : ℕ, ∃ ξ ∈ Metric.closedBall ξ₀ ρ, ∃ ε ∈ Ioo (0 : ℝ) (1 / ((n : ℝ) + 1)),
      ∃ w ∈ Metric.closedBall w₀ r₀, evalξw ξ w Q ≤ ε * L + ε ^ 2 * M ∧
        lam ⬝ᵥ φ ξ - ε * M ≤ lam ⬝ᵥ w ∧ η ≤ dist w (φ ξ) :=
    fun n => hcon _ Nat.one_div_pos_of_nat
  choose ξs hξs εs hεs ws hws hQ hlam hd using hseq
  have hεlim : Tendsto εs atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat (fun n => (hεs n).1.le) (fun n => (hεs n).2.le)
  obtain ⟨⟨ξo, wo⟩, ⟨hξo, hwo⟩, ψ, hψ, hlim⟩ :=
    ((isCompact_closedBall ξ₀ ρ).prod (isCompact_closedBall w₀ r₀)).tendsto_subseq
      (x := fun n => (ξs n, ws n)) (fun n => ⟨hξs n, hws n⟩)
  have hε' : Tendsto (fun n => εs (ψ n)) atTop (𝓝 0) := hεlim.comp hψ.tendsto_atTop
  have hξ' : Tendsto (fun n => ξs (ψ n)) atTop (𝓝 ξo) :=
    (continuous_fst.tendsto (ξo, wo)).comp hlim
  have hw' : Tendsto (fun n => ws (ψ n)) atTop (𝓝 wo) :=
    (continuous_snd.tendsto (ξo, wo)).comp hlim
  -- `Q(ξ°, w°) = 0`
  have hQlim : Tendsto (fun n => evalξw (ξs (ψ n)) (ws (ψ n)) Q) atTop (𝓝 (evalξw ξo wo Q)) := by
    have h1 := ((continuous_evalξw Q).tendsto (ξo, wo)).comp hlim
    simp only [Function.comp_def] at h1
    exact h1
  have hbound : Tendsto (fun n => εs (ψ n) * L + εs (ψ n) ^ 2 * M) atTop (𝓝 0) := by
    simpa using (hε'.mul_const L).add ((hε'.pow 2).mul_const M)
  have hQ0 : evalξw ξo wo Q = 0 :=
    le_antisymm (le_of_tendsto_of_tendsto' hQlim hbound fun n => hQ _)
      (h.nonneg ξo hξo wo hwo)
  -- `⟨λ, w°⟩ ≥ ⟨λ, φ(ξ°)⟩`
  have hφlim : Tendsto (fun n => φ (ξs (ψ n))) atTop (𝓝 (φ ξo)) :=
    (h.cont ξo hξo).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hξ', Eventually.of_forall fun n => hξs _⟩)
  have hcd : Continuous (fun x : κ → ℝ => lam ⬝ᵥ x) := continuous_const.dotProduct continuous_id
  have hlow : Tendsto (fun n => lam ⬝ᵥ φ (ξs (ψ n)) - εs (ψ n) * M) atTop
      (𝓝 (lam ⬝ᵥ φ ξo)) := by
    simpa using ((hcd.tendsto _).comp hφlim).sub (hε'.mul_const M)
  have hlam0 : lam ⬝ᵥ φ ξo ≤ lam ⬝ᵥ wo :=
    le_of_tendsto_of_tendsto' hlow ((hcd.tendsto _).comp hw') fun n => hlam _
  -- `|w° - φ(ξ°)| ≥ η`
  have hdo : η ≤ dist wo (φ ξo) := ge_of_tendsto' (hw'.dist hφlim) fun n => hd _
  by_cases heq : wo = φ ξo
  · rw [heq, dist_self] at hdo
    linarith
  · have := h.unique ξo hξo wo hwo hQ0 heq
    linarith

/-- **Lemma 3.6.**  For fixed `c` there is `ε₀ > 0` such that for `ξ ∈ K` and `0 < ε < ε₀`,
every minimizer of `G_{c,ε}(ξ, ·)` on `B̄` lies in the interior of `B̄` and satisfies (4), and
the minimizers converge to `φ(ξ)` uniformly in `ξ ∈ K` and over all minimizers. -/
theorem minimisers {Q : MvPolynomial (ι ⊕ κ) ℝ} {ξ₀ : ι → ℝ} {ρ : ℝ} {w₀ : κ → ℝ} {r₀ : ℝ}
    {lam : κ → ℝ} {φ : (ι → ℝ) → (κ → ℝ)} (h : LocalHyp Q ξ₀ ρ w₀ r₀ lam φ) (c : κ → ℝ) :
    ∃ ε₀ > 0, (∀ ξ ∈ Metric.closedBall ξ₀ ρ, ∀ ε ∈ Ioo 0 ε₀, ∀ w ∈ Metric.closedBall w₀ r₀,
        (∀ w' ∈ Metric.closedBall w₀ r₀, regG Q lam c ε ξ w ≤ regG Q lam c ε ξ w') →
        w ∈ Metric.ball w₀ r₀ ∧ CriticalEq Q lam c ε ξ w) ∧
      ∀ η > 0, ∃ ε₁ > 0, ∀ ξ ∈ Metric.closedBall ξ₀ ρ, ∀ ε ∈ Ioo 0 ε₁,
        ∀ w ∈ Metric.closedBall w₀ r₀,
        (∀ w' ∈ Metric.closedBall w₀ r₀, regG Q lam c ε ξ w ≤ regG Q lam c ε ξ w') →
        dist w (φ ξ) < η := by
  obtain ⟨M, L, hbound⟩ := minimiser_bounds h c
  have hconv := minimiser_conv h M L
  have hr₀ := h.r₀_pos
  obtain ⟨ε₀, hε₀, h0⟩ := hconv (r₀ / 2) (by linarith)
  refine ⟨ε₀, hε₀, ?_, ?_⟩
  · intro ξ hξ ε hε w hw hmin
    obtain ⟨hb1, hb2⟩ := hbound ξ hξ ε hε.1 w hw hmin
    have hd := h0 ξ hξ ε hε w hw hb1 hb2
    have hint : w ∈ Metric.ball w₀ r₀ := by
      rw [Metric.mem_ball]
      calc dist w w₀ ≤ dist w (φ ξ) + dist (φ ξ) w₀ := dist_triangle _ _ _
        _ < r₀ / 2 + r₀ / 2 := add_lt_add_of_lt_of_le hd (h.near ξ hξ)
        _ = r₀ := by ring
    refine ⟨hint, criticalEq_of_isLocalMin ?_⟩
    filter_upwards [Metric.isOpen_ball.mem_nhds hint] with w' hw'
    exact hmin w' (Metric.ball_subset_closedBall hw')
  · intro η hη
    obtain ⟨ε₁, hε₁, h1⟩ := hconv η hη
    refine ⟨ε₁, hε₁, fun ξ hξ ε hε w hw hmin => ?_⟩
    obtain ⟨hb1, hb2⟩ := hbound ξ hξ ε hε.1 w hw hmin
    exact h1 ξ hξ ε hε w hw hb1 hb2

/-- **Lemma 3.7.**  There is `c` with `dim Bad_c ≤ N`. -/
theorem genericCentre (hS : SAFacts) (Q : MvPolynomial (ι ⊕ κ) ℝ) (lam : κ → ℝ) :
    ∃ c : κ → ℝ, IsSA (badSet Q lam c) ∧ DimLT (badSet Q lam c) (Fintype.card ι + 1) := by
  obtain ⟨hCV, hdim⟩ := hS.sard posSet (PhiMap Q lam) isOpen_posSet (isSAFunOn_PhiMap Q lam)
    (analyticOnNhd_PhiMap Q lam)
  set CV := {y | ∃ p ∈ posSet, PhiMap Q lam p = y ∧
    ¬ Function.Surjective (fderiv ℝ (PhiMap Q lam) p)} with hCVdef
  -- some fiber of the critical values has dimension `< N + 1`, by (S4)(c) and (S6)
  obtain ⟨c, hc⟩ : ∃ c : κ → ℝ, DimLT (fiberOver CV c) (Fintype.card (Option ι)) := by
    by_contra hcon
    have hall : {c : κ → ℝ | DimGE (fiberOver CV c) (Fintype.card (Option ι))} = univ := by
      ext c
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      by_contra h'
      exact hcon ⟨c, h'⟩
    have hge : DimGE {c : κ → ℝ | DimGE (fiberOver CV c) (Fintype.card (Option ι))}
        (Fintype.card κ) := by
      rw [hall, dimGE_card_iff, interior_univ]
      exact univ_nonempty
    apply hdim
    rw [Fintype.card_sum]
    exact hS.fiber_dim_le CV _ _ hCV hge
  refine ⟨c, isSA_badSet Q lam c, ?_⟩
  rw [← Fintype.card_option]
  exact hc.mono (badSet_subset_critical Q lam c)

/-! ## Auxiliary facts for the proof of Theorem 3.5 -/

theorem continuous_regG (Q : MvPolynomial (ι ⊕ κ) ℝ) (lam c : κ → ℝ) (ε : ℝ) (ξ : ι → ℝ) :
    Continuous (fun w => regG Q lam c ε ξ w) := by
  unfold regG
  simp only [dotProduct]
  have h0 : Continuous (fun w : κ → ℝ => (Sum.elim ξ w : ι ⊕ κ → ℝ)) := by
    refine continuous_pi fun v => ?_
    cases v with
    | inl i => exact continuous_const
    | inr k => exact continuous_apply k
  have h1 : Continuous (fun w : κ → ℝ => evalξw ξ w Q) :=
    (MvPolynomial.continuous_eval Q).comp h0
  fun_prop

/-- Minimizers of `G_{c,ε}(ξ, ·)` on `B̄` exist. -/
theorem exists_minimiser (Q : MvPolynomial (ι ⊕ κ) ℝ) (lam c : κ → ℝ) (ε : ℝ) (ξ : ι → ℝ)
    (w₀ : κ → ℝ) {r₀ : ℝ} (hr₀ : 0 ≤ r₀) :
    ∃ w ∈ Metric.closedBall w₀ r₀, ∀ w' ∈ Metric.closedBall w₀ r₀,
      regG Q lam c ε ξ w ≤ regG Q lam c ε ξ w' := by
  obtain ⟨w, hw, hmin⟩ := (isCompact_closedBall w₀ r₀).exists_isMinOn
    (Metric.nonempty_closedBall.2 hr₀) (continuous_regG Q lam c ε ξ).continuousOn
  exact ⟨w, hw, fun w' hw' => hmin hw'⟩

/-- The data `(ξ, ε, w)` with `ξ ∈ K`, `0 < ε < ε₀` and `w` a minimizer of `G_{c,ε}(ξ, ·)` on
`B̄`. -/
def MinData (Q : MvPolynomial (ι ⊕ κ) ℝ) (lam c : κ → ℝ) (ξ₀ : ι → ℝ) (ρ : ℝ) (w₀ : κ → ℝ)
    (r₀ ε₀ : ℝ) (ξ : ι → ℝ) (ε : ℝ) (w : κ → ℝ) : Prop :=
  ξ ∈ Metric.closedBall ξ₀ ρ ∧ ε ∈ Ioo 0 ε₀ ∧ w ∈ Metric.closedBall w₀ r₀ ∧
    ∀ w' ∈ Metric.closedBall w₀ r₀, regG Q lam c ε ξ w ≤ regG Q lam c ε ξ w'

/-- **(S1)**: the set of minimizers is semialgebraic. -/
theorem isSA_minData (Q : MvPolynomial (ι ⊕ κ) ℝ) (lam c : κ → ℝ) (ξ₀ : ι → ℝ) (ρ : ℝ)
    (w₀ : κ → ℝ) (r₀ ε₀ : ℝ) :
    IsSA {u : Option ι ⊕ κ → ℝ |
      MinData Q lam c ξ₀ ρ w₀ r₀ ε₀ (u ∘ Sum.inl ∘ some) (u (Sum.inl none)) (u ∘ Sum.inr)} := by
  have hmin : Def (fun u : Option ι ⊕ κ → ℝ => ∀ w' : κ → ℝ, w' ∈ Metric.closedBall w₀ r₀ →
      regG Q lam c (u (Sum.inl none)) (u ∘ Sum.inl ∘ some) (u ∘ Sum.inr) ≤
        regG Q lam c (u (Sum.inl none)) (u ∘ Sum.inl ∘ some) w') := by
    refine Def.forall_fun (P := fun (u : Option ι ⊕ κ → ℝ) (w' : κ → ℝ) =>
      w' ∈ Metric.closedBall w₀ r₀ →
        regG Q lam c (u (Sum.inl none)) (u ∘ Sum.inl ∘ some) (u ∘ Sum.inr) ≤
          regG Q lam c (u (Sum.inl none)) (u ∘ Sum.inl ∘ some) w') ?_
    refine Def.imp (Def.mem_comp (isSA_closedBall w₀ r₀) Sum.inr) (Def.le ?_ ?_)
    · exact PolyFn.regG Q lam c (PolyFn.coord _) (fun i => PolyFn.coord _)
        (fun k => PolyFn.coord _)
    · exact PolyFn.regG Q lam c (PolyFn.coord _) (fun i => PolyFn.coord _)
        (fun k => PolyFn.coord _)
  exact (Def.mem_comp (isSA_closedBall ξ₀ ρ) (Sum.inl ∘ some)).and
    (((Def.lt (PolyFn.const 0) (PolyFn.coord _)).and (Def.lt (PolyFn.coord _)
      (PolyFn.const ε₀))).and ((Def.mem_comp (isSA_closedBall w₀ r₀) Sum.inr).and hmin))

theorem isSA_boxDomain {V : Set (ι → ℝ)} (hV : IsSA V) (ε₀ : ℝ) : IsSA (boxDomain V ε₀) :=
  (Def.mem_comp hV some).and
    ((Def.lt (PolyFn.const 0) (PolyFn.coord none)).and (Def.lt (PolyFn.coord none)
      (PolyFn.const ε₀)))

/-- The set of `ξ ∈ U` whose fiber in `B` contains an interval `(0, e)` is semialgebraic. -/
theorem isSA_germSet {U : Set (ι → ℝ)} (hU : IsSA U) {B : Set (Option ι → ℝ)} (hB : IsSA B) :
    IsSA {ξ ∈ U | ∃ e > 0, ∀ ε ∈ Ioo 0 e, extendVal ε ξ ∈ B} := by
  let g : Option ι → Option (Option ι) := fun o => o.elim none (fun i => some (some i))
  have h1 : Def (fun u' : Option (Option ι) → ℝ =>
      (0 < u' none ∧ u' none < (u' ∘ some) none) →
        extendVal (u' none) ((u' ∘ some) ∘ some) ∈ B) := by
    refine Def.imp ((Def.lt (PolyFn.const 0) (PolyFn.coord _)).and
      (Def.lt (PolyFn.coord _) (PolyFn.coord _))) ((Def.mem_comp hB g).congr fun u' => ?_)
    have : u' ∘ g = extendVal (u' none) ((u' ∘ some) ∘ some) := by
      funext o; cases o <;> rfl
    rw [this]
  have h2 : Def (fun u : Option ι → ℝ =>
      0 < u none ∧ ∀ ε, (0 < ε ∧ ε < u none) → extendVal ε (u ∘ some) ∈ B) :=
    (Def.lt (PolyFn.const 0) (PolyFn.coord _)).and
      (Def.forall_real (P := fun (u : Option ι → ℝ) (ε : ℝ) =>
        (0 < ε ∧ ε < u none) → extendVal ε (u ∘ some) ∈ B) h1)
  have h3 := (Def.of_isSA hU).and (Def.exists_real
    (P := fun (ξ : ι → ℝ) (e : ℝ) => 0 < e ∧ ∀ ε, (0 < ε ∧ ε < e) → extendVal ε ξ ∈ B) h2)
  refine (h3.congr fun ξ => ?_).isSA
  simp only [mem_ofPred_eq, gt_iff_lt, mem_Ioo]

/-- If `dim B ≤ N`, the set of `ξ` whose fiber in `B` contains an interval `(0, e)` has
dimension `< N` (by (S4)(c)). -/
theorem dimLT_germSet (hS : SAFacts) {B : Set (Option ι → ℝ)} (hB : IsSA B)
    (hdim : DimLT B (Fintype.card ι + 1)) :
    DimLT {ξ : ι → ℝ | ∃ e > 0, ∀ ε ∈ Ioo 0 e, extendVal ε ξ ∈ B} (Fintype.card ι) := by
  intro hge
  let g : Option ι → Unit ⊕ ι := fun o => o.elim (Sum.inl ()) Sum.inr
  set A : Set (Unit ⊕ ι → ℝ) := {u | u ∘ g ∈ B} with hAdef
  have hA : IsSA A := hB.preimage_comp g
  have hfib : {ξ : ι → ℝ | ∃ e > 0, ∀ ε ∈ Ioo 0 e, extendVal ε ξ ∈ B} ⊆
      {ξ | DimGE (fiberOver A ξ) 1} := by
    rintro ξ ⟨e, he, hsub⟩
    have hsub' : {x : Unit → ℝ | x () ∈ Ioo 0 e} ⊆ fiberOver A ξ := by
      intro x hx
      show Sum.elim x ξ ∘ g ∈ B
      have : Sum.elim x ξ ∘ g = extendVal (x ()) ξ := by funext o; cases o <;> rfl
      rw [this]
      exact hsub _ hx
    refine DimGE.mono ?_ hsub'
    have h1 : Fintype.card Unit = 1 := rfl
    rw [← h1, dimGE_card_iff]
    have hopen : IsOpen {x : Unit → ℝ | x () ∈ Ioo 0 e} :=
      isOpen_Ioo.preimage (continuous_apply ())
    rw [hopen.interior_eq]
    exact ⟨fun _ => e / 2, by simp only [mem_ofPred_eq, mem_Ioo]; constructor <;> linarith⟩
  have h3 := hS.fiber_dim_le A 1 (Fintype.card ι) hA (hge.mono hfib)
  have hcard : 1 + Fintype.card ι = Fintype.card (Unit ⊕ ι) := by
    rw [Fintype.card_sum]; rfl
  rw [hcard, dimGE_card_iff] at h3
  apply hdim
  rw [← Fintype.card_option, dimGE_card_iff]
  have hg : Function.Injective g := by
    intro a b hab
    cases a <;> cases b <;> simp_all [g]
  have hT := isOpenMap_comp_of_injective (β := Option ι) (γ := Unit ⊕ ι) hg
  obtain ⟨u, hu⟩ := h3
  have hsub : (fun u : Unit ⊕ ι → ℝ => u ∘ g) '' interior A ⊆ interior B := by
    refine (hT.image_interior_subset A).trans (interior_mono ?_)
    rintro _ ⟨u, hu, rfl⟩
    exact hu
  exact ⟨u ∘ g, hsub ⟨u, hu, rfl⟩⟩

theorem eval_Ef {Q : MvPolynomial (ι ⊕ κ) ℝ} {E : κ → MvPolynomial (ι ⊕ κ) ℝ} {a : ℝ}
    {b : κ → ℝ} (hE : ∀ k, E k = pderiv (Sum.inr k) Q + (C a * X (Sum.inr k) + C (b k)))
    (ξ : ι → ℝ) (w : κ → ℝ) (k : κ) :
    eval (Sum.elim ξ w) (E k) = evalξw ξ w (pderiv (Sum.inr k) Q) + (a * w k + b k) := by
  simp [hE, evalξw]

theorem jacW_Ef {Q : MvPolynomial (ι ⊕ κ) ℝ} {E : κ → MvPolynomial (ι ⊕ κ) ℝ} {a : ℝ}
    {b : κ → ℝ} (hE : ∀ k, E k = pderiv (Sum.inr k) Q + (C a * X (Sum.inr k) + C (b k)))
    (ξ : ι → ℝ) (w : κ → ℝ) :
    jacW E (Sum.elim ξ w) = hessW Q ξ w + a • (1 : Matrix κ κ ℝ) := by
  ext k l
  simp only [jacW, hE, map_add, Derivation.leibniz, pderiv_X, pderiv_C, smul_eq_mul, mul_zero,
    add_zero, hessW, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, evalξw]
  by_cases hkl : k = l
  · subst hkl; simp
  · simp [hkl]

/-- The analytic part of Theorem 3.5: given a circuit graph `Γ` computing the Newton
polynomials of the system `E_{ε,c}(ξ, w) = ∇_w Q - ελ + 2ε²(w - c)` for all values of the
constants, the conclusion of Theorem 3.5 holds for `Γ`. -/
theorem local_data (hS : SAFacts) {Q : MvPolynomial (ι ⊕ κ) ℝ} {ξ₀ : ι → ℝ} {ρ : ℝ}
    {w₀ : κ → ℝ} {r₀ : ℝ} {lam : κ → ℝ} {φ : (ι → ℝ) → (κ → ℝ)}
    (h : LocalHyp Q ξ₀ ρ w₀ r₀ lam φ) (D : ℕ) (hD : 1 ≤ D) (Γ : Shape ι) (out : κ → ℕ)
    (Ef : ℝ → (κ → ℝ) → κ → MvPolynomial (ι ⊕ κ) ℝ)
    (hEf : ∀ ε c k, Ef ε c k = pderiv (Sum.inr k) Q +
      (C (2 * ε ^ 2) * X (Sum.inr k) + C (-(2 * ε ^ 2 * c k) - ε * lam k)))
    (enc : ℝ → (κ → ℝ) → (ι → ℝ) → (κ → ℝ) → Matrix κ κ ℝ → ℕ → ℝ)
    (hΓ : ∀ ε c ξ₁ w₁ A k,
      (Γ.values (enc ε c ξ₁ w₁ A)).getD (out k) 0 = newtonPoly (Ef ε c) ξ₁ w₁ A D k) :
    ∃ (ξs : ι → ℝ) (rs : ℝ) (Es : Set (ι → ℝ)),
      0 < rs ∧ Metric.ball ξs rs ⊆ Metric.closedBall ξ₀ ρ ∧ Es ⊆ Metric.ball ξs rs ∧
      IsSA Es ∧ DimLT Es (Fintype.card ι) ∧
      ContDiffOn ℝ D φ (Metric.ball ξs rs) ∧
      ∀ ξ₁ ∈ Metric.ball ξs rs \ Es, ∀ η > 0, ∃ a : ℕ → ℝ, ∀ k : κ,
        ((Γ.values a).getD (out k) 0).totalDegree ≤ D ∧
        ∀ m, |((Γ.values a).getD (out k) 0).coeff m -
          (taylorPoly D (fun ξ => φ ξ k) ξ₁).coeff m| < η := by
  classical
  -- the centre `c` (Lemma 3.7) and `ε₀` (Lemma 3.6)
  obtain ⟨c, hcSA, hcdim⟩ := genericCentre hS Q lam
  obtain ⟨ε₀, hε₀, hmin1, hmin2⟩ := minimisers h c
  set K := Metric.closedBall ξ₀ ρ with hK
  -- a semialgebraic choice `W` of minimizers ((S1), (S2))
  obtain ⟨s, hsSA, hs⟩ := hS.choice _ (isSA_minData Q lam c ξ₀ ρ w₀ r₀ ε₀)
  set W : (ι → ℝ) → ℝ → (κ → ℝ) := fun ξ ε => s (extendVal ε ξ) with hW
  have hWmin : ∀ ξ ∈ K, ∀ ε ∈ Ioo 0 ε₀, MinData Q lam c ξ₀ ρ w₀ r₀ ε₀ ξ ε (W ξ ε) := by
    intro ξ hξ ε hε
    obtain ⟨w, hw, hwmin⟩ := exists_minimiser Q lam c ε ξ w₀ h.r₀_pos.le
    exact hs (extendVal ε ξ) ⟨w, hξ, hε, hw, hwmin⟩
  have hWcrit : ∀ ξ ∈ K, ∀ ε ∈ Ioo 0 ε₀, CriticalEq Q lam c ε ξ (W ξ ε) := fun ξ hξ ε hε =>
    (hmin1 ξ hξ ε hε (W ξ ε) (hWmin ξ hξ ε hε).2.2.1 (hWmin ξ hξ ε hε).2.2.2).2
  -- Corollary 3.2 on the interior of `K`
  set V := Metric.ball ξ₀ ρ with hV
  have hVK : V ⊆ K := Metric.ball_subset_closedBall
  have hWSA : IsSAFunOn (boxDomain V ε₀) (uncurryOpt W) := by
    have e : uncurryOpt W = s := by
      funext v
      simp only [uncurryOpt, hW]
      congr 1
      funext o
      cases o <;> rfl
    rw [e]
    exact hsSA.mono (isSA_boxDomain (isSA_ball ξ₀ ρ) ε₀) (subset_univ _)
  have hlim : ∀ ξ ∈ V, Tendsto (W ξ) (𝓝[>] 0) (𝓝 (φ ξ)) := by
    intro ξ hξ
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro η hη
    obtain ⟨ε₁, hε₁, hconv⟩ := hmin2 η hη
    refine ⟨min ε₁ ε₀, lt_min hε₁ hε₀, fun ε hε hdist => ?_⟩
    have hεpos : 0 < ε := hε
    rw [Real.dist_eq, sub_zero, abs_of_pos hεpos] at hdist
    have hm := hWmin ξ (hVK hξ) ε ⟨hεpos, lt_of_lt_of_le hdist (min_le_right _ _)⟩
    exact hconv ξ (hVK hξ) ε ⟨hεpos, lt_of_lt_of_le hdist (min_le_left _ _)⟩ _ hm.2.2.1 hm.2.2.2
  obtain ⟨ξs, rs, ε', hrs, hball, hε', hε'le, -, hWD, -, hφD, hconv⟩ :=
    derivatives_cor hS V Metric.isOpen_ball ⟨ξ₀, Metric.mem_ball_self h.ρ_pos⟩ ε₀ hε₀ W hWSA φ
      (h.cont.mono hVK) hlim D hD
  -- the exceptional set `E*`
  set Es := {ξ ∈ Metric.ball ξs rs | ∃ e > 0, ∀ ε ∈ Ioo 0 e, extendVal ε ξ ∈ badSet Q lam c}
    with hEs
  refine ⟨ξs, rs, Es, hrs, hball.trans hVK, fun ξ hξ => hξ.1,
    isSA_germSet (isSA_ball ξs rs) hcSA, (dimLT_germSet hS hcSA hcdim).mono fun ξ hξ => hξ.2,
    hφD, ?_⟩
  rintro ξ₁ ⟨hξ₁, hξ₁E⟩ η hη
  have hξ₁K : ξ₁ ∈ K := hVK (hball hξ₁)
  have hnhds : Metric.ball ξs rs ∈ 𝓝 ξ₁ := Metric.isOpen_ball.mem_nhds hξ₁
  -- convergence of the Taylor coefficients of `W(·, ε)` to those of `φ`
  have hcomp : ∀ (f : (ι → ℝ) → (κ → ℝ)) (k : κ) (j : ℕ), j ≤ D → ContDiffAt ℝ D f ξ₁ →
      iteratedFDeriv ℝ j (fun ξ => f ξ k) ξ₁ =
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => ℝ) k).compContinuousMultilinearMap
          (iteratedFDeriv ℝ j f ξ₁) := fun f k j hj hf =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => ℝ) k).iteratedFDeriv_comp_left hf
      (by exact_mod_cast hj)
  have htend : ∀ k m, Tendsto (fun ε => (taylorPoly D (fun ξ => W ξ ε k) ξ₁).coeff m)
      (𝓝[>] 0) (𝓝 ((taylorPoly D (fun ξ => φ ξ k) ξ₁).coeff m)) := by
    intro k m
    refine tendsto_coeff_taylorPoly (fun j hj => ?_) m
    have h1 := (hconv j hj).tendsto_at hξ₁
    have h2 := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => ℝ)
      k).continuous_postcomp_continuousMultilinearMap.tendsto _).comp h1
    rw [hcomp φ k j hj (hφD.contDiffAt hnhds)]
    refine h2.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hε'] with ε hε
    exact (hcomp _ k j hj ((hWD ε hε).contDiffAt hnhds)).symm
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < ε' ∧ ∀ k, ∀ m ∈ degSet ι D,
      |(taylorPoly D (fun ξ => W ξ ε k) ξ₁).coeff m -
        (taylorPoly D (fun ξ => φ ξ k) ξ₁).coeff m| < η := by
    refine Filter.Eventually.and ?_ ?_
    · filter_upwards [Ioo_mem_nhdsGT hε'] with ε hε using hε.2
    · rw [Filter.eventually_all]
      intro k
      rw [Filter.eventually_all_finset]
      intro m _
      filter_upwards [(Metric.tendsto_nhds.1 (htend k m)) η hη] with ε hε
      rwa [Real.dist_eq] at hε
  obtain ⟨δ, hδ, hδsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  -- a small `ε` with `(ξ₁, ε) ∉ Bad_c`
  obtain ⟨ε, hεδ, hεbad⟩ : ∃ ε ∈ Ioo 0 δ, extendVal ε ξ₁ ∉ badSet Q lam c := by
    by_contra hcon
    push Not at hcon
    exact hξ₁E ⟨hξ₁, δ, hδ, hcon⟩
  obtain ⟨hεε', hcoef⟩ := hδsub hεδ
  have hεpos : 0 < ε := hεδ.1
  have hε₀' : ε ∈ Ioo 0 ε₀ := ⟨hεpos, lt_of_lt_of_le hεε' hε'le⟩
  set w₁ := W ξ₁ ε with hw₁
  have hcrit := hWcrit ξ₁ hξ₁K ε hε₀'
  have hdet : (hessW Q ξ₁ w₁ + (2 * ε ^ 2) • (1 : Matrix κ κ ℝ)).det ≠ 0 :=
    fun hd => hεbad ⟨hεpos, w₁, hcrit, hd⟩
  -- Newton iteration for `E = E_{ε,c}` at `(ξ₁, w₁)`
  set E := Ef ε c with hE
  have hjac := jacW_Ef (hEf ε c) ξ₁ w₁
  have hE0 : ∀ ξ w, CriticalEq Q lam c ε ξ w → ∀ k, eval (Sum.elim ξ w) (E k) = 0 := by
    intro ξ w hw k
    rw [eval_Ef (hEf ε c), ← hw k]
    ring
  set A := (jacW E (Sum.elim ξ₁ w₁))⁻¹ with hA
  have hAinv : A * jacW E (Sum.elim ξ₁ w₁) = 1 :=
    Matrix.nonsing_inv_mul _ (by rw [hjac]; exact isUnit_iff_ne_zero.2 hdet)
  have hωD : ContDiffAt ℝ D (fun ξ => W ξ ε) ξ₁ := (hWD ε ⟨hεpos, hεε'⟩).contDiffAt hnhds
  have hωE : ∀ᶠ ξ in 𝓝 ξ₁, ∀ k, eval (Sum.elim ξ (W ξ ε)) (E k) = 0 := by
    filter_upwards [hnhds] with ξ hξ
    exact hE0 ξ _ (hWcrit ξ (hVK (hball hξ)) ε hε₀')
  refine ⟨enc ε c ξ₁ w₁ A, fun k => ?_⟩
  rw [hΓ, newtonPoly_eq_taylorPoly E ξ₁ w₁ A D (hE0 ξ₁ w₁ hcrit) hAinv (fun ξ => W ξ ε) rfl
    hωD hωE k]
  refine ⟨totalDegree_taylorPoly_le _ _ _, fun m => ?_⟩
  by_cases hm : m ∈ degSet ι D
  · exact hcoef k m hm
  · have h1 : (taylorPoly D (fun ξ => W ξ ε k) ξ₁).coeff m = 0 := by
      by_contra hne
      exact hm (support_subset_degSet (totalDegree_taylorPoly_le _ _ _) (mem_support_iff.2 hne))
    have h2 : (taylorPoly D (fun ξ => φ ξ k) ξ₁).coeff m = 0 := by
      by_contra hne
      exact hm (support_subset_degSet (totalDegree_taylorPoly_le _ _ _) (mem_support_iff.2 hne))
    rw [h1, h2, sub_zero, abs_zero]
    exact hη

/-- **Theorem 3.5 (local theorem).** -/
theorem local_theorem (hS : SAFacts) :
    ∃ C : ℕ, ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
      (prog : SLP (ι ⊕ κ) ℕ) (oQ : Operand (ι ⊕ κ) ℕ) (D : ℕ), 1 ≤ D →
      ∃ (Γ : Shape ι) (out : κ → ℕ),
        Γ.length ≤ C * ((D + 1) ^ 3 * (prog.length + 1) + (D + 1) ^ 2 * Fintype.card κ ^ 2 +
          Fintype.card ι) ∧
        ∀ (cQ : ℕ → ℝ) (ξ₀ : ι → ℝ) (ρ : ℝ) (w₀ : κ → ℝ) (r₀ : ℝ) (lam : κ → ℝ)
          (φ : (ι → ℝ) → (κ → ℝ)),
          LocalHyp (progOutput prog cQ oQ) ξ₀ ρ w₀ r₀ lam φ →
          ∃ (ξs : ι → ℝ) (rs : ℝ) (Es : Set (ι → ℝ)),
            0 < rs ∧ Metric.ball ξs rs ⊆ Metric.closedBall ξ₀ ρ ∧ Es ⊆ Metric.ball ξs rs ∧
            IsSA Es ∧ DimLT Es (Fintype.card ι) ∧
            ContDiffOn ℝ D φ (Metric.ball ξs rs) ∧
            ∀ ξ₁ ∈ Metric.ball ξs rs \ Es, ∀ η > 0, ∃ a : ℕ → ℝ, ∀ k : κ,
              ((Γ.values a).getD (out k) 0).totalDegree ≤ D ∧
              ∀ m, |((Γ.values a).getD (out k) 0).coeff m -
                (taylorPoly D (fun ξ => φ ξ k) ξ₁).coeff m| < η := by
  obtain ⟨CB, hCB⟩ := baur_strassen
  obtain ⟨CN, hCN⟩ := newton_circuit
  refine ⟨CN * (9 * CB + 1), ?_⟩
  intro ι κ _ _ _ _ prog oQ D hD
  by_cases hκ : 2 * prog.length + 1 < Fintype.card κ
  · -- some `w_j` is not read by the program: the hypotheses cannot hold
    refine ⟨[], fun _ => 0, by simp, ?_⟩
    intro cQ ξ₀ ρ w₀ r₀ lam φ h
    exfalso
    set S : Finset κ :=
      ((LocalProg.progIn prog oQ).filterMap Sum.getRight?).toFinset with hS
    have hScard : S.card < (Finset.univ : Finset κ).card := by
      rw [Finset.card_univ]
      refine lt_of_le_of_lt ?_ hκ
      refine (List.toFinset_card_le _).trans ?_
      exact (List.length_filterMap_le _ _).trans (LocalProg.length_progIn prog oQ)
    obtain ⟨j, -, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card hScard
    have hj' : Sum.inr j ∉ LocalProg.progIn prog oQ := by
      intro hmem
      refine hj (List.mem_toFinset.2 (List.mem_filterMap.2 ⟨Sum.inr j, hmem, rfl⟩))
    exact LocalProg.not_localHyp_of_indep (LocalProg.indep_progOutput cQ prog oQ hj') h
  · push Not at hκ
    obtain ⟨prog'', o₀, od, cmap, hlen, hspec⟩ :=
      hCB (LocalProg.qProg prog oQ) (LocalProg.qOut prog oQ)
    obtain ⟨Γ, out, enc, hΓlen, hΓ⟩ := hCN prog'' (fun k => od (Sum.inr k)) D
    refine ⟨Γ, out, ?_, ?_⟩
    · rw [LocalProg.length_qProg] at hlen
      have h1 : prog''.length + 1 ≤ (9 * CB + 1) * (prog.length + 1) := by nlinarith
      refine hΓlen.trans ?_
      rw [mul_assoc]
      refine Nat.mul_le_mul_left _ ?_
      have h2 : (D + 1) ^ 3 * (prog''.length + 1) ≤
          (9 * CB + 1) * ((D + 1) ^ 3 * (prog.length + 1)) := by
        calc (D + 1) ^ 3 * (prog''.length + 1)
            ≤ (D + 1) ^ 3 * ((9 * CB + 1) * (prog.length + 1)) := Nat.mul_le_mul_left _ h1
          _ = (9 * CB + 1) * ((D + 1) ^ 3 * (prog.length + 1)) := by ring
      have h3 : (D + 1) ^ 2 * Fintype.card κ ^ 2 ≤
          (9 * CB + 1) * ((D + 1) ^ 2 * Fintype.card κ ^ 2) := Nat.le_mul_of_pos_left _ (by omega)
      have h4 : Fintype.card ι ≤ (9 * CB + 1) * Fintype.card ι :=
        Nat.le_mul_of_pos_left _ (by omega)
      rw [Nat.mul_add, Nat.mul_add]
      linarith
    · intro cQ ξ₀ ρ w₀ r₀ lam φ h
      set cs : ℝ → (κ → ℝ) → ℕ → ℝ := fun ε c =>
        cmap (LocalProg.qConst cQ (ε ^ 2) (fun l => -(2 * ε ^ 2 * c l) - ε * lam l)) with hcs
      refine local_data hS h D hD Γ out
        (fun ε c => progOutputs prog'' (cs ε c) (fun k => od (Sum.inr k))) ?_
        (fun ε c => enc (cs ε c)) (fun ε c ξ₁ w₁ A k => hΓ (cs ε c) ξ₁ w₁ A k)
      intro ε c k
      simp only [progOutputs]
      have := (hspec (LocalProg.qConst cQ (ε ^ 2) (fun l => -(2 * ε ^ 2 * c l) - ε * lam l))).2
        (Sum.inr k)
      change progOutput prog'' _ (od (Sum.inr k)) = _
      rw [this, LocalProg.progOutput_qProg, map_add, LocalProg.pderiv_extra]

end ClassSep
