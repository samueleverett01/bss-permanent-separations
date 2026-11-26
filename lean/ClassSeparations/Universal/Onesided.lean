import ClassSeparations.Cert.Value
import ClassSeparations.Cert.Permanent
import ClassSeparations.Core.Newton
import ClassSeparations.Core.Derivatives
import ClassSeparations.Core.Closure
import ClassSeparations.Basic.Cells
import ClassSeparations.Universal.Margin

/-!
# One-sided certificates (§5.1–5.5, Theorem 5.1, Lemma 5.2)

Let a tree on inputs `(x, y, z) ∈ ℝⁿ × ℝ × ℝᵏ` be given, together with a set `M` of *marked*
outcomes (§5.1).  A triple is marked if its outcome lies in `M`.  Marking the rejecting leaves
corresponds to `M = {some false, none}` (an input that divides by zero is rejected, hence
marked, as in the convention of §2.1).

**Theorem 5.1.**  Let `f` have degree at most `d ≥ 1`, `U ⊆ ℝⁿ` open and nonempty, and a tree of
depth `t` with marked outcomes be given.  Suppose that for every `x ∈ U`
(i) no triple `(x, f(x), z)` is marked, and
(ii) there is `ρ > 0` such that for every `y` with `f(x) < y < f(x) + ρ` some triple `(x, y, z)`
is marked.
Then the border complexity of `f` is at most `C(d+1)⁶((t+1)² + n)`.

## Structure of the proof

* `OnesidedAux.one_cell` (§5.2): one cell `B` covers a one-sided neighbourhood
  `{(x, y) : x ∈ U₁, f(x) < y < f(x) + e₀}` of the graph.
* `OnesidedAux.restrict_cell`: the certificate coordinates that do not occur in `B` are fixed
  to `0`; at most `2t` remain.
* §5.3: the margin system (`ClassSeparations.Universal.Margin`) and **Lemma 5.2**
  (`Margin.margin_cert_iff` for (a), `OnesidedAux.lemma_5_2_b`, `OnesidedAux.lemma_5_2_c`).
* §5.4–5.5 (`OnesidedAux.core`): level sets of the margin, Corollary 3.2, Proposition 4.5,
  nondegenerate points, the Taylor polynomials of level sets via Newton iteration.
* `OnesidedAux.composite`: the composite circuit of Lemma 3.4 applied to a circuit graph of
  Proposition 4.5.
-/

noncomputable section

set_option linter.unusedSectionVars false

open MvPolynomial Set Filter Topology

namespace ClassSep

namespace OnesidedAux

/-! ### First-order definable predicates

A small toolkit for verifying instances of (S1): predicates built from polynomial
(in)equalities by connectives and quantifiers over `ℝ` define semialgebraic sets. -/

section Dfn

variable {α β : Type}

/-- The predicate `P` on `ℝ^α` defines a semialgebraic set. -/
def Dfn (P : (α → ℝ) → Prop) : Prop := IsSA {v | P v}

/-- `t` is a polynomial function. -/
def PT (t : (α → ℝ) → ℝ) : Prop := ∃ p : MvPolynomial α ℝ, ∀ v, t v = eval v p

theorem PT.coord (i : α) : PT (fun v : α → ℝ => v i) := ⟨X i, fun v => by simp⟩

theorem PT.const (c : ℝ) : PT (fun _ : α → ℝ => c) := ⟨C c, fun v => by simp⟩

theorem PT.add {t s : (α → ℝ) → ℝ} (ht : PT t) (hs : PT s) : PT (fun v => t v + s v) := by
  obtain ⟨p, hp⟩ := ht; obtain ⟨q, hq⟩ := hs; exact ⟨p + q, fun v => by simp [hp, hq]⟩

theorem PT.sub {t s : (α → ℝ) → ℝ} (ht : PT t) (hs : PT s) : PT (fun v => t v - s v) := by
  obtain ⟨p, hp⟩ := ht; obtain ⟨q, hq⟩ := hs; exact ⟨p - q, fun v => by simp [hp, hq]⟩

theorem PT.mul {t s : (α → ℝ) → ℝ} (ht : PT t) (hs : PT s) : PT (fun v => t v * s v) := by
  obtain ⟨p, hp⟩ := ht; obtain ⟨q, hq⟩ := hs; exact ⟨p * q, fun v => by simp [hp, hq]⟩

theorem PT.evalp (p : MvPolynomial β ℝ) {T : β → (α → ℝ) → ℝ} (hT : ∀ b, PT (T b)) :
    PT (fun v => eval (fun b => T b v) p) := by
  choose q hq using hT
  refine ⟨bind₁ q p, fun v => ?_⟩
  rw [Margin.eval_bind₁_]
  have : (fun b => T b v) = fun b => eval v (q b) := funext fun b => hq b v
  show eval (fun b => T b v) p = _
  rw [this]

theorem PT.comp {t : (β → ℝ) → ℝ} (ht : PT t) {T : β → (α → ℝ) → ℝ} (hT : ∀ b, PT (T b)) :
    PT (fun v => t (fun b => T b v)) := by
  obtain ⟨p, hp⟩ := ht
  obtain ⟨q, hq⟩ := PT.evalp p hT
  refine ⟨q, fun v => ?_⟩
  show t (fun b => T b v) = _
  rw [hp]
  exact hq v

theorem PT.sumElim {γ δ : Type} {A : (α → ℝ) → γ → ℝ} {B : (α → ℝ) → δ → ℝ}
    (hA : ∀ c, PT (fun v => A v c)) (hB : ∀ c, PT (fun v => B v c)) :
    ∀ c, PT (fun v => Sum.elim (A v) (B v) c)
  | .inl c => hA c
  | .inr c => hB c

theorem PT.extendVal {γ : Type} {S : (α → ℝ) → ℝ} {N : (α → ℝ) → γ → ℝ} (hS : PT S)
    (hN : ∀ c, PT (fun v => N v c)) : ∀ o, PT (fun v => ClassSep.extendVal (S v) (N v) o)
  | none => hS
  | some c => hN c

theorem Dfn.of_iff {P Q : (α → ℝ) → Prop} (h : Dfn P) (e : ∀ v, P v ↔ Q v) : Dfn Q := by
  have : {v | P v} = {v | Q v} := Set.ext e
  unfold Dfn; rwa [← this]

theorem dfn_lt {t s : (α → ℝ) → ℝ} (ht : PT t) (hs : PT s) : Dfn (fun v => t v < s v) := by
  obtain ⟨p, hp⟩ := ht; obtain ⟨q, hq⟩ := hs
  exact Dfn.of_iff (isSA_pos (q - p)) fun v => by simp [hp, hq]

theorem dfn_eq {t s : (α → ℝ) → ℝ} (ht : PT t) (hs : PT s) : Dfn (fun v => t v = s v) := by
  obtain ⟨p, hp⟩ := ht; obtain ⟨q, hq⟩ := hs
  refine Dfn.of_iff (isSA_zero (q - p)) fun v => ?_
  rw [map_sub, sub_eq_zero, hp, hq, eq_comm]

theorem Dfn.and {P Q : (α → ℝ) → Prop} (hP : Dfn P) (hQ : Dfn Q) : Dfn (fun v => P v ∧ Q v) :=
  IsSA.inter hP hQ

theorem Dfn.or {P Q : (α → ℝ) → Prop} (hP : Dfn P) (hQ : Dfn Q) : Dfn (fun v => P v ∨ Q v) :=
  IsSA.union hP hQ

theorem Dfn.not {P : (α → ℝ) → Prop} (hP : Dfn P) : Dfn (fun v => ¬ P v) := IsSA.compl hP

theorem Dfn.imp {P Q : (α → ℝ) → Prop} (hP : Dfn P) (hQ : Dfn Q) : Dfn (fun v => P v → Q v) :=
  Dfn.of_iff (hP.not.or hQ) fun v => by tauto

theorem dfn_le {t s : (α → ℝ) → ℝ} (ht : PT t) (hs : PT s) : Dfn (fun v => t v ≤ s v) :=
  Dfn.of_iff (dfn_lt hs ht).not fun _ => not_lt

theorem Dfn.ex {P : (α → ℝ) → ℝ → Prop}
    (h : Dfn (fun w : Option α → ℝ => P (fun a => w (some a)) (w none))) :
    Dfn (fun v => ∃ a, P v a) :=
  IsSA.exists_option h

theorem Dfn.all {P : (α → ℝ) → ℝ → Prop}
    (h : Dfn (fun w : Option α → ℝ => P (fun a => w (some a)) (w none))) :
    Dfn (fun v => ∀ a, P v a) :=
  Dfn.of_iff (Dfn.ex (P := fun v a => ¬ P v a) h.not).not fun v => by simp

theorem Dfn.exFun {γ : Type} [Finite γ] {P : (α → ℝ) → (γ → ℝ) → Prop}
    (h : Dfn (fun w : α ⊕ γ → ℝ => P (fun a => w (.inl a)) (fun c => w (.inr c)))) :
    Dfn (fun v => ∃ z, P v z) :=
  IsSA.exists_sum h

theorem Dfn.comp {P : (β → ℝ) → Prop} (hP : Dfn P) {T : β → (α → ℝ) → ℝ}
    (hT : ∀ b, PT (T b)) : Dfn (fun v => P (fun b => T b v)) := by
  choose q hq using hT
  refine Dfn.of_iff (IsSA.preimage_poly hP q) fun v => ?_
  have : (fun b => eval v (q b)) = fun b => T b v := funext fun b => (hq b v).symm
  simp only [Set.mem_ofPred_eq, this]

theorem dfn_true : Dfn (fun _ : α → ℝ => True) := Dfn.of_iff isSA_univ fun _ => Iff.rfl

theorem Dfn.listAll {γ : Type} (l : List γ) {R : γ → (α → ℝ) → Prop}
    (h : ∀ p ∈ l, Dfn (R p)) : Dfn (fun v => ∀ p ∈ l, R p v) := by
  induction l with
  | nil => exact Dfn.of_iff dfn_true fun v => by simp
  | cons p l ih =>
    refine Dfn.of_iff ((h p (by simp)).and (ih fun q hq => h q (by simp [hq]))) fun v => ?_
    simp

theorem dfn_carrier (B : Cell α) : Dfn (fun v => v ∈ B.carrier) := by
  refine Dfn.of_iff ((Dfn.listAll B.eqs fun p _ => dfn_eq (PT.evalp p fun i => PT.coord i)
    (PT.const 0)).and (Dfn.listAll B.poss fun q _ => dfn_lt (PT.const 0)
      (PT.evalp q fun i => PT.coord i))) fun v => ?_
  exact Iff.rfl

theorem dfn_ball [Fintype β] (x₀ : β → ℝ) (r : ℝ) {T : β → (α → ℝ) → ℝ} (hT : ∀ b, PT (T b)) :
    Dfn (fun v => (fun b => T b v) ∈ Metric.ball x₀ r) :=
  Dfn.comp (P := fun u => u ∈ Metric.ball x₀ r) (isSA_ball x₀ r) hT

/-- The solutions of a polynomial system with a coordinate `s` and unknowns `ν`. -/
theorem dfn_sol {π κ : Type} [Fintype κ] (Q : MvPolynomial (π ⊕ Option κ) ℝ)
    {Ξ : (α → ℝ) → π → ℝ} (hΞ : ∀ p, PT (fun w => Ξ w p)) {S : (α → ℝ) → ℝ} (hS : PT S) :
    Dfn (fun w => ∃ ν : κ → ℝ, eval (Sum.elim (Ξ w) (extendVal (S w) ν)) Q = 0) := by
  refine Dfn.exFun (P := fun v ν => eval (Sum.elim (Ξ v) (extendVal (S v) ν)) Q = 0) ?_
  refine dfn_eq (PT.evalp Q (PT.sumElim (fun p => ?_) (PT.extendVal ?_ fun c => ?_)))
    (PT.const 0)
  · exact PT.comp (hΞ p) fun a => PT.coord (Sum.inl a)
  · exact PT.comp hS fun a => PT.coord (Sum.inl a)
  · exact PT.coord (Sum.inr c)

/-- The graph of the largest value of `s` on the solutions is definable. -/
theorem dfn_isGreatest {π κ : Type} [Fintype κ] (Q : MvPolynomial (π ⊕ Option κ) ℝ)
    {Ξ : (α → ℝ) → π → ℝ} (hΞ : ∀ p, PT (fun w => Ξ w p)) {S : (α → ℝ) → ℝ} (hS : PT S) :
    Dfn (fun w => IsGreatest {s | ∃ ν : κ → ℝ, eval (Sum.elim (Ξ w) (extendVal s ν)) Q = 0}
      (S w)) := by
  have h1 := dfn_sol Q hΞ hS
  have h2 : Dfn (fun w : Option α → ℝ => (∃ ν : κ → ℝ,
      eval (Sum.elim (Ξ (fun a => w (some a))) (extendVal (w none) ν)) Q = 0) →
        w none ≤ S (fun a => w (some a))) :=
    (dfn_sol Q (fun p => PT.comp (hΞ p) fun a => PT.coord (some a)) (PT.coord none)).imp
      (dfn_le (PT.coord none) (PT.comp hS fun a => PT.coord (some a)))
  refine Dfn.of_iff (h1.and (Dfn.all (P := fun v s => (∃ ν : κ → ℝ,
      eval (Sum.elim (Ξ v) (extendVal s ν)) Q = 0) → s ≤ S v) h2)) fun w => ?_
  simp only [IsGreatest, upperBounds, Set.mem_ofPred_eq]

end Dfn

/-! ### The setting -/

variable {σ : Type}

/-- The point `(x, y) ∈ ℝ^(σ ⊕ Unit)`. -/
def xy (x : σ → ℝ) (y : ℝ) : σ ⊕ Unit → ℝ := Sum.elim x (fun _ => y)

theorem xy_inl (x : σ → ℝ) (y : ℝ) (i : σ) : xy x y (.inl i) = x i := rfl
theorem xy_inr (x : σ → ℝ) (y : ℝ) (u : Unit) : xy x y (.inr u) = y := rfl

theorem continuous_xy : Continuous fun p : (σ → ℝ) × ℝ => xy p.1 p.2 := by
  refine continuous_pi fun v => ?_
  cases v with
  | inl i => exact (continuous_apply i).comp continuous_fst
  | inr u => exact continuous_snd

variable [Fintype σ] [DecidableEq σ] {κ : Type} [Fintype κ]

/-- The values of `s` on the solutions of a system `Q = 0` at the parameter `ξ`. -/
def solS (Q : MvPolynomial ((σ ⊕ Unit) ⊕ Option κ) ℝ) (ξ : σ ⊕ Unit → ℝ) : Set ℝ :=
  {s | ∃ ν : κ → ℝ, eval (Sum.elim ξ (extendVal s ν)) Q = 0}

/-- The largest value of `s` on the solutions (the margin, for the margin system). -/
def vM (Q : MvPolynomial ((σ ⊕ Unit) ⊕ Option κ) ℝ) (ξ : σ ⊕ Unit → ℝ) : ℝ := sSup (solS Q ξ)

/-- The conclusions of Lemma 5.2 (b), (c) on the ball `B(x₀, r₀)`, which is all that §5.4–5.5
use about the margin. -/
structure MarginHyp (Q : MvPolynomial ((σ ⊕ Unit) ⊕ Option κ) ℝ) (f : MvPolynomial σ ℝ)
    (x₀ : σ → ℝ) (r₀ e₀ : ℝ) : Prop where
  hr : 0 < r₀
  he : 0 < e₀
  nonneg : ∀ w, 0 ≤ eval w Q
  great : ∀ x ∈ Metric.ball x₀ r₀, ∀ y, eval x f < y → y < eval x f + e₀ →
    IsGreatest (solS Q (xy x y)) (vM Q (xy x y)) ∧ 0 < vM Q (xy x y) ∧ vM Q (xy x y) ≤ 1
  lim : ∀ x ∈ Metric.ball x₀ r₀,
    Tendsto (fun y => vM Q (xy x y)) (𝓝[>] (eval x f)) (𝓝 0)

/-! ### §5.2: one cell covers a one-sided neighbourhood -/

omit [Fintype σ] [DecidableEq σ] in
/-- A positive radius that works for each member of a finite list works uniformly. -/
theorem exists_pos_forall_list {γ : Type*} (L : List γ) (P : γ → ℝ → Prop)
    (hP : ∀ B e e', P B e → 0 < e' → e' ≤ e → P B e') (h : ∀ B ∈ L, ∃ e > 0, P B e) :
    ∃ e > 0, ∀ B ∈ L, P B e := by
  induction L with
  | nil => exact ⟨1, one_pos, by simp⟩
  | cons B L ih =>
    obtain ⟨e₁, he₁, h₁⟩ := h B (by simp)
    obtain ⟨e₂, he₂, h₂⟩ := ih fun B' hB' => h B' (by simp [hB'])
    refine ⟨min e₁ e₂, lt_min he₁ he₂, fun B' hB' => ?_⟩
    rcases List.mem_cons.1 hB' with rfl | hB'
    · exact hP _ _ _ h₁ (lt_min he₁ he₂) (min_le_left _ _)
    · exact hP _ _ _ (h₂ B' hB') (lt_min he₁ he₂) (min_le_right _ _)

omit [DecidableEq σ] in
theorem dfn_cert {k : ℕ} {α : Type} (B : Cell (σ ⊕ Unit ⊕ Fin k)) {Xf : (α → ℝ) → σ → ℝ}
    (hX : ∀ i, PT (fun w => Xf w i)) {Y : (α → ℝ) → ℝ} (hY : PT Y) :
    Dfn (fun w => ∃ z, inp3 (Xf w) (Y w) z ∈ B.carrier) := by
  refine Dfn.exFun (P := fun w z => inp3 (Xf w) (Y w) z ∈ B.carrier) ?_
  refine Dfn.comp (dfn_carrier B) (T := fun i (w : α ⊕ Fin k → ℝ) =>
    inp3 (Xf (fun a => w (.inl a))) (Y (fun a => w (.inl a))) (fun c => w (.inr c)) i)
    fun i => ?_
  rcases i with i | u | c
  · exact PT.comp (hX i) fun a => PT.coord (Sum.inl a : α ⊕ Fin k)
  · exact PT.comp hY fun a => PT.coord (Sum.inl a : α ⊕ Fin k)
  · exact PT.coord (Sum.inr c : α ⊕ Fin k)

/-- **§5.2.**  If finitely many cells cover a one-sided neighbourhood of the graph over `U`, one
of them covers `{(x, y) : x ∈ B(x₀, r₀), f(x) < y < f(x) + e₀}` for some ball `B(x₀, r₀) ⊆ U`
and `e₀ > 0`. -/
theorem one_cell (hS : SAFacts) {k : ℕ} (f : MvPolynomial σ ℝ) (U : Set (σ → ℝ))
    (hU : IsOpen U) (hUne : U.Nonempty) (L : List (Cell (σ ⊕ Unit ⊕ Fin k)))
    (hcov : ∀ x ∈ U, ∃ ρ > 0, ∀ y, eval x f < y → y < eval x f + ρ →
      ∃ B ∈ L, ∃ z, inp3 x y z ∈ B.carrier) :
    ∃ B ∈ L, ∃ (x₀ : σ → ℝ) (r₀ e₀ : ℝ), 0 < r₀ ∧ Metric.ball x₀ r₀ ⊆ U ∧ 0 < e₀ ∧
      ∀ x ∈ Metric.ball x₀ r₀, ∀ y, eval x f < y → y < eval x f + e₀ →
        ∃ z, inp3 x y z ∈ B.carrier := by
  -- every `x ∈ U` has a cell containing an initial interval above `f(x)` (S3)
  have hgerm : ∀ x ∈ U, ∃ B ∈ L, ∃ e > 0, ∀ y, eval x f < y → y < eval x f + e →
      ∃ z, inp3 x y z ∈ B.carrier := by
    intro x hx
    obtain ⟨ρ, hρ, hcx⟩ := hcov x hx
    by_contra hno
    push Not at hno
    have hdis : ∀ B ∈ L, ∃ e > 0, Disjoint (Ioo (eval x f) (eval x f + e))
        {y | ∃ z, inp3 x y z ∈ B.carrier} := by
      intro B hB
      have hSA : IsSA₁ {y | ∃ z, inp3 x y z ∈ B.carrier} :=
        dfn_cert (α := Unit) B (Xf := fun _ => x) (fun i => PT.const (x i)) (PT.coord ())
      rcases germ_right hS hSA (eval x f) with ⟨e, he, hsub⟩ | h
      · obtain ⟨y, hy1, hy2, hy⟩ := hno B hB e he
        obtain ⟨z, hz⟩ := hsub ⟨hy1, hy2⟩
        exact absurd hz (hy z)
      · exact h
    obtain ⟨e, he, hall⟩ := exists_pos_forall_list L
      (fun B e => Disjoint (Ioo (eval x f) (eval x f + e)) {y | ∃ z, inp3 x y z ∈ B.carrier})
      (fun B e e' h _ hle => h.mono_left (Ioo_subset_Ioo le_rfl (by linarith))) hdis
    obtain ⟨B, hB, z, hz⟩ := hcx (eval x f + min e ρ / 2)
      (by have := lt_min he hρ; linarith)
      (by have := min_le_right e ρ; have := lt_min he hρ; linarith)
    refine Set.disjoint_left.1 (hall B hB) ⟨?_, ?_⟩ ⟨z, hz⟩
    · have := lt_min he hρ; linarith
    · have := min_le_left e ρ; have := lt_min he hρ; linarith
  -- the sets of `x` for which a cell contains an initial interval, and (S2), (S4), (S5)
  let E : Cell (σ ⊕ Unit ⊕ Fin k) → Set (σ ⊕ Unit → ℝ) := fun B =>
    {w | 0 < w (.inr ()) ∧ ∀ y, eval (fun i => w (.inl i)) f < y →
      y < eval (fun i => w (.inl i)) f + w (.inr ()) →
        ∃ z, inp3 (fun i => w (.inl i)) y z ∈ B.carrier}
  have hE : ∀ B, IsSA (E B) := by
    intro B
    refine (dfn_lt (PT.const 0) (PT.coord (Sum.inr () : σ ⊕ Unit))).and (Dfn.all ?_)
    have c1 : ∀ i, PT (fun w : Option (σ ⊕ Unit) → ℝ => w (some (Sum.inl i))) :=
      fun i => PT.coord _
    have c2 : PT (fun w : Option (σ ⊕ Unit) → ℝ => w none) := PT.coord _
    have c3 : PT (fun w : Option (σ ⊕ Unit) → ℝ => w (some (Sum.inr ()))) := PT.coord _
    exact (((dfn_lt (PT.evalp f c1) c2).and
      (dfn_lt c2 ((PT.evalp f c1).add c3))).imp (dfn_cert B c1 c2)).of_iff fun w => by
      simp only [and_imp]
  let S : Fin L.length → Set (σ → ℝ) := fun i =>
    {x | ∃ e, Sum.elim x (fun _ => e) ∈ E (L.get i)}
  have hSsa : ∀ i ∈ (Finset.univ : Finset (Fin L.length)), IsSA (S i) := by
    intro i _
    refine Dfn.ex (P := fun x e => Sum.elim x (fun _ => e) ∈ E (L.get i)) ?_
    exact Dfn.comp (hE (L.get i)) (T := fun j (w : Option σ → ℝ) =>
      Sum.elim (fun a => w (some a)) (fun _ => w none) j) (PT.sumElim (fun a => PT.coord _)
        (fun _ => PT.coord _))
  have hScov : U ⊆ ⋃ i ∈ (Finset.univ : Finset (Fin L.length)), S i := by
    intro x hx
    obtain ⟨B, hB, e, he, h⟩ := hgerm x hx
    obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hB
    simp only [Set.mem_iUnion, Finset.mem_univ, exists_true_left]
    exact ⟨i, e, he, h⟩
  obtain ⟨i, -, x', hx'⟩ := exists_interior_of_finite_cover hS Finset.univ S hSsa hU hUne hScov
  obtain ⟨r', hr', hball'⟩ := Metric.isOpen_iff.1 isOpen_interior x' hx'
  have hball'' : Metric.ball x' r' ⊆ S i ∩ U := hball'.trans interior_subset
  obtain ⟨sec, hsec, hsecE⟩ := hS.choice (E (L.get i)) (hE _)
  have hg : IsSAFunOn₁ (Metric.ball x' r') (fun x => sec x ()) := by
    have := hsec.mono (isSA_ball x' r') (Set.subset_univ _)
    simpa [IsSAFunOn₁] using this
  have hpos : ∀ x ∈ Metric.ball x' r', 0 < sec x () ∧ ∀ y, eval x f < y →
      y < eval x f + sec x () → ∃ z, inp3 x y z ∈ (L.get i).carrier := by
    intro x hx
    obtain ⟨e, he⟩ := (hball'' hx).1
    have := hsecE x ⟨fun _ => e, he⟩
    exact this
  obtain ⟨x₀, r₀, c, hr₀, hsub, hc, hcle⟩ := exists_ball_lower_bound hS Metric.isOpen_ball
    ⟨x', Metric.mem_ball_self hr'⟩ hg (fun x hx => (hpos x hx).1)
  refine ⟨L.get i, List.get_mem _ _, x₀, r₀, c, hr₀, fun x hx => (hball'' (hsub hx)).2, hc,
    fun x hx y hy1 hy2 => (hpos x (hsub hx)).2 y hy1 (by linarith [hcle x hx])⟩

/-- The certificate coordinates that do not occur in a cell are fixed to `0`; at most `2t`
remain (Lemma 2.5). -/
theorem restrict_cell {k t : ℕ} {K : Set ℝ} (B : Cell (σ ⊕ Unit ⊕ Fin k)) (hB : B.Bounded t K) :
    ∃ (ζ : Type) (_ : Fintype ζ) (B' : Cell ((σ ⊕ Unit) ⊕ ζ)), Fintype.card ζ ≤ 2 * t ∧
      B'.prog.length ≤ 8 * t ∧ B'.eqs.length ≤ 2 * t ∧ B'.poss.length ≤ 2 * t ∧
      (∀ p ∈ B'.eqs ++ B'.poss, B'.prog.Computes p) ∧
      ∀ (x : σ → ℝ) (y : ℝ), (∃ z, inp3 x y z ∈ B.carrier) ↔
        ∃ z' : ζ → ℝ, Sum.elim (xy x y) z' ∈ B'.carrier := by
  obtain ⟨I, hIcard, -, hIvars⟩ := hB.vars
  let ζ := {j : Fin k // (Sum.inr (Sum.inr j) : σ ⊕ Unit ⊕ Fin k) ∈ I}
  let ρ : σ ⊕ Unit ⊕ Fin k → Operand ((σ ⊕ Unit) ⊕ ζ) ℝ := fun i =>
    match i with
    | .inl i => .input (.inl (.inl i))
    | .inr (.inl u) => .input (.inl (.inr u))
    | .inr (.inr j) => if h : (Sum.inr (Sum.inr j) : σ ⊕ Unit ⊕ Fin k) ∈ I then
        .input (.inr ⟨j, h⟩) else .const 0
  have hρ : Margin.NoPrev ρ := by
    intro i j
    rcases i with i | u | l
    · simp [ρ]
    · simp [ρ]
    · simp only [ρ]; split_ifs <;> simp
  refine ⟨ζ, inferInstance, Margin.Cell.substIn ρ B, ?_, ?_, ?_, ?_,
    Margin.Cell.computes_substIn hρ B ?_, fun x y => ?_⟩
  · have hinj : Function.Injective (fun j : ζ => (⟨Sum.inr (Sum.inr j.1), j.2⟩ : I)) := by
      intro a b h
      simp only [Subtype.mk.injEq, Sum.inr.injEq] at h
      exact Subtype.ext h
    have := Fintype.card_le_of_injective _ hinj
    simp only [Fintype.card_coe] at this
    omega
  · simp only [Margin.Cell.substIn, Margin.SLP.length_substIn]; exact hB.prog_len
  · simp only [Margin.Cell.substIn, List.length_map]; exact hB.eqs_len
  · simp only [Margin.Cell.substIn, List.length_map]; exact hB.poss_len
  · intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact hB.computes_eqs p hp
    · exact hB.computes_poss p hp
  · -- the substituted point
    have hpt : ∀ z' : ζ → ℝ, (fun i => eval (Sum.elim (xy x y) z') (Margin.ρpoly ρ i)) =
        inp3 x y (fun j => if h : (Sum.inr (Sum.inr j) : σ ⊕ Unit ⊕ Fin k) ∈ I then
          z' ⟨j, h⟩ else 0) := by
      intro z'
      funext i
      rcases i with i | u | l
      · simp [ρ, Margin.ρpoly, Operand.eval, xy, inp3]
      · simp [ρ, Margin.ρpoly, Operand.eval, xy, inp3]
      · simp only [ρ, Margin.ρpoly, inp3, Sum.elim_inr]
        split_ifs <;> simp [Operand.eval]
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨fun j => z j.1, ?_⟩
      rw [Margin.Cell.mem_carrier_substIn, hpt]
      have hagree : ∀ p ∈ B.eqs ++ B.poss, eval (inp3 x y (fun j =>
          if h : (Sum.inr (Sum.inr j) : σ ⊕ Unit ⊕ Fin k) ∈ I then z j else 0)) p =
            eval (inp3 x y z) p := by
        intro p hp
        refine eval₂Hom_congr' rfl (fun i hi _ => ?_) rfl
        have hiI : i ∈ I := hIvars p hp hi
        rcases i with i | u | l
        · rfl
        · rfl
        · simp [inp3, hiI]
      refine ⟨fun p hp => ?_, fun q hq => ?_⟩
      · rw [hagree p (List.mem_append_left _ hp)]; exact hz.1 p hp
      · rw [hagree q (List.mem_append_right _ hq)]; exact hz.2 q hq
    · rintro ⟨z', hz'⟩
      rw [Margin.Cell.mem_carrier_substIn, hpt] at hz'
      exact ⟨_, hz'⟩

/-! ### Lemma 5.2 (b), (c) -/

section Lemma52

variable {ζ : Type} [Fintype ζ] {B : Cell ((σ ⊕ Unit) ⊕ ζ)}
  {pS : Fin B.eqs.length → MvPolynomial ((σ ⊕ Unit) ⊕ Option ζ) ℝ}
  {qS : Fin B.poss.length → MvPolynomial ((σ ⊕ Unit) ⊕ Option ζ) ℝ}

/-- **Lemma 5.2 (b).**  On `A`, the coordinate `s` attains a maximum `v(x, y) ∈ (0, 1]` on the
solutions of the margin system. -/
theorem lemma_5_2_b (hH : Margin.IsHomog B pS qS) {f : MvPolynomial σ ℝ} {U₁ : Set (σ → ℝ)}
    {e₀ : ℝ} (hA : ∀ x ∈ U₁, ∀ y, eval x f < y → y < eval x f + e₀ →
      ∃ z, Sum.elim (xy x y) z ∈ B.carrier) :
    ∀ x ∈ U₁, ∀ y, eval x f < y → y < eval x f + e₀ →
      IsGreatest (solS (Margin.marginPoly pS qS) (xy x y))
        (vM (Margin.marginPoly pS qS) (xy x y)) ∧
      0 < vM (Margin.marginPoly pS qS) (xy x y) ∧ vM (Margin.marginPoly pS qS) (xy x y) ≤ 1 := by
  intro x hx y h1 h2
  obtain ⟨v, hv, hv0, hv1⟩ := Margin.margin_attains hH (hA x hx y h1 h2)
  have e : vM (Margin.marginPoly pS qS) (xy x y) = v := hv.csSup_eq
  rw [e]
  exact ⟨hv, hv0, hv1⟩

omit [DecidableEq σ] in
theorem continuous_xy_right (x : σ → ℝ) : Continuous fun y : ℝ => xy x y :=
  continuous_xy.comp (continuous_const.prodMk continuous_id)

/-- **Lemma 5.2 (c).**  For every `x`, `v(x, y) → 0` as `y` decreases to `f(x)`. -/
theorem lemma_5_2_c (hH : Margin.IsHomog B pS qS) {f : MvPolynomial σ ℝ} {x₀ : σ → ℝ}
    {r₀ e₀ : ℝ} (he₀ : 0 < e₀)
    (hA : ∀ x ∈ Metric.ball x₀ r₀, ∀ y, eval x f < y → y < eval x f + e₀ →
      ∃ z, Sum.elim (xy x y) z ∈ B.carrier)
    (hnot : ∀ x ∈ Metric.ball x₀ r₀, ¬ ∃ z, Sum.elim (xy x (eval x f)) z ∈ B.carrier) :
    ∀ x ∈ Metric.ball x₀ r₀,
      Tendsto (fun y => vM (Margin.marginPoly pS qS) (xy x y)) (𝓝[>] (eval x f)) (𝓝 0) := by
  intro x hx
  set a := eval x f with ha
  rw [Metric.tendsto_nhds]
  intro ε hε
  set K := (fun y => xy x y) '' Icc a (a + e₀ / 2) with hKdef
  have hK : IsCompact K := isCompact_Icc.image (continuous_xy_right x)
  have hC := Margin.margin_isClosed_proj pS qS hK hε.le
  set Cε := {ξ | ξ ∈ K ∧ ∃ s, ε ≤ s ∧ ∃ ν : Margin.MVar ζ B.poss.length → ℝ,
    eval (Sum.elim ξ (extendVal s ν)) (Margin.marginPoly pS qS) = 0} with hCε
  have hnotC : xy x a ∉ Cε := by
    rintro ⟨-, s, hs, ν, hν⟩
    exact hnot x hx ((Margin.margin_cert_iff hH (xy x a)).2 ⟨s, lt_of_lt_of_le hε hs, ν, hν⟩)
  have hopen : IsOpen {y : ℝ | xy x y ∉ Cε} := hC.isOpen_compl.preimage (continuous_xy_right x)
  have hev1 : ∀ᶠ y in 𝓝[>] a, xy x y ∉ Cε :=
    nhdsWithin_le_nhds (hopen.mem_nhds hnotC)
  have hev2 : ∀ᶠ y in 𝓝[>] a, y ∈ Ioo a (a + e₀ / 2) :=
    Ioo_mem_nhdsGT (by linarith)
  filter_upwards [hev1, hev2] with y hy1 hy2
  obtain ⟨hgr, hpos, -⟩ := lemma_5_2_b hH hA x hx y hy2.1 (by linarith [hy2.2])
  rw [Real.dist_eq, sub_zero, abs_of_pos hpos]
  by_contra hge
  push Not at hge
  obtain ⟨ν, hν⟩ := hgr.1
  exact hy1 ⟨⟨y, ⟨hy2.1.le, hy2.2.le⟩, rfl⟩, _, hge, ν, hν⟩

end Lemma52

/-! ### Analytic lemmas -/

section Analytic

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The derivative of a polynomial along a coordinate line. -/
theorem hasDerivAt_eval_line (p : MvPolynomial ι ℝ) (ξ : ι → ℝ) (i : ι) :
    HasDerivAt (fun t : ℝ => eval (ξ + t • Pi.single i 1) p) (eval ξ (pderiv i p)) 0 := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const (0 : ℝ) a
  | add p q hp hq =>
    have := hp.add hq
    simp only [map_add]
    exact this
  | mul_X p j hp =>
    have hj : HasDerivAt (fun t : ℝ => ξ j + t * (Pi.single i 1 : ι → ℝ) j)
        ((Pi.single i 1 : ι → ℝ) j) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const ((Pi.single i 1 : ι → ℝ) j)).const_add (ξ j)
    have := hp.mul hj
    simp only [map_mul, eval_X, Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_smul, add_zero,
      zero_mul] at this ⊢
    convert this using 1
    rw [Derivation.leibniz, pderiv_X]
    simp only [smul_eq_mul, map_add, map_mul, eval_X, Pi.single_apply]
    split_ifs with h
    · subst h; simp; ring
    · simp [mul_comm]

/-- At its base point, the derivatives of the Taylor polynomial of order `D ≥ 1` are those of
the function. -/
theorem eval_pderiv_taylorPoly {D : ℕ} (hD : 1 ≤ D) {g : (ι → ℝ) → ℝ} {ξ₁ : ι → ℝ}
    (hg : ContDiffAt ℝ D g ξ₁) (i : ι) :
    eval ξ₁ (pderiv i (taylorPoly D g ξ₁)) = fderiv ℝ g ξ₁ (Pi.single i 1) := by
  set P := taylorPoly D g ξ₁
  set e : ι → ℝ := Pi.single i 1
  have hline : Tendsto (fun t : ℝ => ξ₁ + t • e) (𝓝 0) (𝓝 ξ₁) := by
    have : Continuous (fun t : ℝ => ξ₁ + t • e) := by fun_prop
    simpa using this.tendsto 0
  have h1 := hasDerivAt_eval_line P ξ₁ i
  have hgd : HasFDerivAt g (fderiv ℝ g ξ₁) ξ₁ :=
    (hg.differentiableAt (by exact_mod_cast (show D ≠ 0 by omega))).hasFDerivAt
  have hlin : HasDerivAt (fun t : ℝ => ξ₁ + t • e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add ξ₁
  have h2 : HasDerivAt (fun t : ℝ => g (ξ₁ + t • e)) (fderiv ℝ g ξ₁ e) 0 :=
    hgd.comp_hasDerivAt_of_eq (0 : ℝ) hlin (by simp)
  -- the difference is `o(t)`
  have ho := (taylorPoly_isLittleO hg).comp_tendsto hline
  have hnorm : ∀ t : ℝ, ‖(ξ₁ + t • e) - ξ₁‖ = |t| := by
    intro t
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    have : ‖e‖ = 1 := by
      simp only [e]
      rw [Pi.norm_single]
      simp
    rw [this, mul_one]
  have ho' : (fun t : ℝ => g (ξ₁ + t • e) - eval (ξ₁ + t • e) P) =o[𝓝 0] fun t => t := by
    refine (ho.trans_isBigO ?_).congr_left fun t => rfl
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with t ht
    simp only [Function.comp_apply, hnorm, norm_pow, Real.norm_eq_abs, abs_abs, one_mul]
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at ht
    calc |t| ^ D ≤ |t| ^ 1 := pow_le_pow_of_le_one (abs_nonneg t) ht.le hD
      _ = |t| := pow_one _
  have h3 : HasDerivAt (fun t : ℝ => g (ξ₁ + t • e) - eval (ξ₁ + t • e) P) 0 0 := by
    rw [hasDerivAt_iff_isLittleO_nhds_zero]
    simp only [zero_add, zero_smul, add_zero, smul_zero, sub_zero]
    have h0 : g ξ₁ - eval ξ₁ P = 0 := by rw [eval_taylorPoly_self, sub_self]
    rw [h0]
    simpa using ho'
  have := (h2.sub h1).unique h3
  linarith

/-- Coefficients of Taylor polynomials depend continuously on the derivatives and on the base
point. -/
theorem tendsto_coeff_taylorPoly_var {D : ℕ} {β : Type*} {l : Filter β}
    {G : β → (ι → ℝ) → ℝ} {ξb : β → ι → ℝ} {g : (ι → ℝ) → ℝ} {ξ₁ : ι → ℝ}
    (hξ : Tendsto ξb l (𝓝 ξ₁))
    (h : ∀ j ≤ D, Tendsto (fun b => iteratedFDeriv ℝ j (G b) (ξb b)) l
      (𝓝 (iteratedFDeriv ℝ j g ξ₁))) (m : ι →₀ ℕ) :
    Tendsto (fun b => (taylorPoly D (G b) (ξb b)).coeff m) l (𝓝 ((taylorPoly D g ξ₁).coeff m)) := by
  have key : ∀ (g' : (ι → ℝ) → ℝ) (ξ' : ι → ℝ), (taylorPoly D g' ξ').coeff m =
      ∑ j ∈ Finset.range (D + 1), (j.factorial : ℝ)⁻¹ *
        ∑ i : Fin j → ι, iteratedFDeriv ℝ j g' ξ' (fun k => Pi.single (i k) 1) *
          (∏ k : Fin j, (X (i k) - C (ξ' (i k))) : MvPolynomial ι ℝ).coeff m := by
    intro g' ξ'
    simp only [taylorPoly, jetTerm, coeff_sum, coeff_C_mul, Finset.mul_sum]
  simp_rw [key]
  refine tendsto_finsetSum _ fun j hj => ?_
  refine Tendsto.const_mul _ (tendsto_finsetSum _ fun i _ => ?_)
  refine Tendsto.mul ?_ ?_
  · exact (h j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).eval_const _
  · have hc : CTo l (fun b => ∏ k : Fin j, (X (i k) - C (ξb b (i k)) : MvPolynomial ι ℝ))
        (∏ k : Fin j, (X (i k) - C (ξ₁ (i k)))) :=
      CTo.prod _ fun k _ => (CTo.const _).sub
        (CTo.const_C (((continuous_apply (i k)).tendsto ξ₁).comp hξ))
    exact hc m

end Analytic
section NewtonVariant

variable {ι κ' : Type} [Fintype ι] [DecidableEq ι] [Fintype κ'] [DecidableEq κ']

/-- **Lemma 3.4 (b)**, with an approximate solution: if `E(ξ, ω(ξ)) = o(|ξ - ξ₁|ᴰ)` (instead of
`= 0`), the Newton iteration still produces the Taylor polynomial of `ω`. -/
theorem newtonPoly_eq_taylorPoly' (E : κ' → MvPolynomial (ι ⊕ κ') ℝ) (ξ₁ : ι → ℝ) (w₁ : κ' → ℝ)
    (A : Matrix κ' κ' ℝ) (D : ℕ) (hA : A * jacW E (Sum.elim ξ₁ w₁) = 1)
    (ω : (ι → ℝ) → (κ' → ℝ)) (hω₁ : ω ξ₁ = w₁) (hωD : ContDiffAt ℝ D ω ξ₁)
    (hωE : ∀ l, (fun ξ => eval (Sum.elim ξ (ω ξ)) (E l)) =o[𝓝 ξ₁] fun ξ => ‖ξ - ξ₁‖ ^ D)
    (k : κ') : newtonPoly E ξ₁ w₁ A D k = taylorPoly D (fun ξ => ω ξ k) ξ₁ := by
  set τk : κ' → MvPolynomial ι ℝ := fun k => taylorPoly D (fun ξ => ω ξ k) ξ₁ with hτk
  set T : κ' → MvPolynomial ι ℝ :=
    fun k => bind₁ (fun i => X i + MvPolynomial.C (ξ₁ i)) (τk k) with hTdef
  have hωk : ∀ k, ContDiffAt ℝ D (fun ξ => ω ξ k) ξ₁ := contDiffAt_pi.1 hωD
  have hτ0 : ∀ k, eval ξ₁ (τk k) = w₁ k := fun k => by
    simp only [τk]; rw [eval_taylorPoly_self, hω₁]
  have hT : ∀ k, (T k).totalDegree ≤ D := fun k =>
    (totalDegree_bind₁_le _ (fun i => totalDegree_X_add_C_le i _) _).trans
      (totalDegree_taylorPoly_le _ _ _)
  have hevalT : ∀ k χ, eval χ (T k) = eval (fun i => χ i + ξ₁ i) (τk k) := by
    intro k χ
    simp only [T]
    rw [Margin.eval_bind₁_]
    simp
  have hT0 : ∀ k, (T k).coeff 0 = w₁ k := fun k => by
    rw [coeff_zero_eq_eval_zero', hevalT]
    simpa using hτ0 k
  have hF : ∀ l, (fun ξ => eval (Sum.elim ξ (fun k => eval ξ (τk k))) (E l)) =o[𝓝 ξ₁]
      (fun ξ => ‖ξ - ξ₁‖ ^ D) := by
    intro l
    obtain ⟨K, t, ht, hK⟩ :=
      (contDiff_eval_poly (E l)).contDiffAt.exists_lipschitzOnWith (x := Sum.elim ξ₁ w₁)
    have hτv : Tendsto (fun ξ => Sum.elim ξ (fun k => eval ξ (τk k))) (𝓝 ξ₁)
        (𝓝 (Sum.elim ξ₁ w₁)) := by
      have hc : Continuous (fun ξ : ι → ℝ => Sum.elim ξ (fun k => eval ξ (τk k))) :=
        continuous_pi fun v => by
          cases v with
          | inl i => exact continuous_apply i
          | inr k => exact MvPolynomial.continuous_eval _
      have := hc.tendsto ξ₁
      have e : Sum.elim ξ₁ (fun k => eval ξ₁ (τk k)) = Sum.elim ξ₁ w₁ := by
        congr 1; funext k; exact hτ0 k
      rwa [e] at this
    have hωv : Tendsto (fun ξ => Sum.elim ξ (ω ξ)) (𝓝 ξ₁) (𝓝 (Sum.elim ξ₁ w₁)) := by
      rw [tendsto_pi_nhds]
      intro v
      cases v with
      | inl i => simpa using (continuous_apply i).tendsto ξ₁
      | inr k =>
        have := (hωk k).continuousAt.tendsto
        simp only [hω₁] at this
        simpa using this
    have hdiff : (fun ξ => (fun k => eval ξ (τk k)) - ω ξ) =o[𝓝 ξ₁]
        fun ξ => ‖ξ - ξ₁‖ ^ D := by
      rw [Asymptotics.isLittleO_pi]
      intro k
      refine (taylorPoly_isLittleO (hωk k)).neg_left.congr_left fun ξ => ?_
      simp [τk]
    have hB : (fun ξ => eval (Sum.elim ξ (fun k => eval ξ (τk k))) (E l) -
        eval (Sum.elim ξ (ω ξ)) (E l)) =o[𝓝 ξ₁] (fun ξ => ‖ξ - ξ₁‖ ^ D) := by
      refine Asymptotics.IsBigO.trans_isLittleO ?_ hdiff
      refine Asymptotics.IsBigO.of_bound K ?_
      filter_upwards [hτv.eventually_mem ht, hωv.eventually_mem ht] with ξ h1 h2
      have hL := hK.dist_le_mul _ h1 _ h2
      rw [dist_eq_norm, dist_eq_norm] at hL
      refine hL.trans ?_
      gcongr
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun v => ?_
      cases v with
      | inl i => simp
      | inr k =>
        simpa using norm_le_pi_norm ((fun k => eval ξ (τk k)) - ω ξ) k
    exact (hB.add (hωE l)).congr_left fun ξ => by ring
  have hET : ∀ l, HighOrd (D + 1)
      (bind₁ (Sum.elim (fun i => MvPolynomial.C (ξ₁ i) + X i) T) (E l)) := by
    intro l
    apply highOrd_of_isLittleO
    have hT' : Tendsto (fun χ : ι → ℝ => ξ₁ + χ) (𝓝 0) (𝓝 ξ₁) := by
      simpa using (tendsto_const_nhds (x := ξ₁)).add (tendsto_id (x := 𝓝 (0 : ι → ℝ)))
    refine ((hF l).comp_tendsto hT').congr (fun χ => ?_) (fun χ => by simp)
    simp only [Function.comp_apply, Margin.eval_bind₁_]
    have hpt : (fun v => eval χ (Sum.elim (fun i => MvPolynomial.C (ξ₁ i) + X i) T v)) =
        Sum.elim (ξ₁ + χ) (fun k => eval (ξ₁ + χ) (τk k)) := by
      funext v
      cases v with
      | inl i => simp
      | inr k =>
        simp only [Sum.elim_inr, hevalT]
        rw [show (fun i => χ i + ξ₁ i) = ξ₁ + χ from funext fun i => by simp [add_comm]]
    rw [hpt]
  have hiter : ∀ n ≤ D, ∀ k, HighOrd (n + 1)
      ((newtonStep E ξ₁ A D)^[n] (fun l => MvPolynomial.C (w₁ l)) k - T k) := by
    intro n
    induction n with
    | zero =>
      intro _ k
      refine HighOrd.one_of_coeff_zero ?_
      simp [hT0]
    | succ n ih =>
      intro hn k
      rw [Function.iterate_succ_apply']
      exact newtonStep_highOrd E ξ₁ w₁ A D hA T hT hT0 hET (by omega) _ (ih (by omega)) k
  have hfin : (newtonStep E ξ₁ A D)^[D] (fun l => MvPolynomial.C (w₁ l)) k = T k := by
    have := (hiter D le_rfl k).eq_zero ((totalDegree_sub _ _).trans
      (max_le (totalDegree_iterate_newtonStep_le E ξ₁ w₁ A D D k) (hT k)))
    exact sub_eq_zero.1 this
  unfold newtonPoly
  rw [hfin]
  simp only [T, bind₁_bind₁]
  have : (fun i => bind₁ (fun i => X i - MvPolynomial.C (ξ₁ i))
      (X i + MvPolynomial.C (ξ₁ i) : MvPolynomial ι ℝ)) = X := funext fun i => by simp
  rw [this, bind₁_X_left]
  rfl

end NewtonVariant

/-! ### §5.4: level sets of the margin -/

omit [Fintype σ] [DecidableEq σ] in
theorem PT.xy {α : Type} {X : (α → ℝ) → σ → ℝ} (hX : ∀ i, PT (fun w => X w i))
    {Y : (α → ℝ) → ℝ} (hY : PT Y) : ∀ p, PT (fun w => xy (X w) (Y w) p)
  | .inl i => hX i
  | .inr _ => hY

theorem dfn_isGr {α : Type} (Q : MvPolynomial ((σ ⊕ Unit) ⊕ Option κ) ℝ)
    {X : (α → ℝ) → σ → ℝ} (hX : ∀ i, PT (fun w => X w i)) {Y : (α → ℝ) → ℝ} (hY : PT Y)
    {S : (α → ℝ) → ℝ} (hS : PT S) :
    Dfn (fun w => IsGreatest (solS Q (xy (X w) (Y w))) (S w)) :=
  dfn_isGreatest Q (Ξ := fun w => xy (X w) (Y w)) (PT.xy hX hY) hS

/-- Discharges goals `PT t` for polynomial expressions `t`. -/
macro "pt_tac" : tactic => `(tactic| repeat' first
  | exact PT.coord _
  | exact PT.const _
  | refine PT.sub ?_ ?_
  | refine PT.add ?_ ?_
  | refine PT.mul ?_ ?_
  | refine PT.evalp _ ?_
  | intro _)

/-- Discharges goals `Dfn P` for first-order predicates `P` built from polynomial
(in)equalities and the graph of the margin. -/
macro "dfn_tac" : tactic => `(tactic| repeat' first
  | refine dfn_isGr _ ?_ ?_ ?_
  | refine Dfn.and ?_ ?_
  | refine Dfn.all ?_
  | refine Dfn.ex ?_
  | refine Dfn.imp ?_ ?_
  | refine dfn_lt ?_ ?_
  | refine dfn_le ?_ ?_
  | exact PT.coord _
  | exact PT.const _
  | refine PT.sub ?_ ?_
  | refine PT.add ?_ ?_
  | refine PT.mul ?_ ?_
  | refine PT.evalp _ ?_
  | intro _)

section Levels

variable {Q : MvPolynomial ((σ ⊕ Unit) ⊕ Option κ) ℝ} {f : MvPolynomial σ ℝ} {x₀ : σ → ℝ}
  {r₀ e₀ : ℝ}

theorem isGr_iff (hM : MarginHyp Q f x₀ r₀ e₀) {x : σ → ℝ} (hx : x ∈ Metric.ball x₀ r₀) {y : ℝ}
    (h1 : eval x f < y) (h2 : y < eval x f + e₀) (s : ℝ) :
    IsGreatest (solS Q (xy x y)) s ↔ vM Q (xy x y) = s := by
  have hg := (hM.great x hx y h1 h2).1
  constructor
  · intro h; exact hg.unique h
  · rintro rfl; exact hg

omit [Fintype σ] [DecidableEq σ] in
theorem tendsto_add_nhdsGT (a : ℝ) : Tendsto (fun h : ℝ => a + h) (𝓝[>] 0) (𝓝[>] a) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have : Tendsto (fun h : ℝ => a + h) (𝓝 0) (𝓝 (a + 0)) :=
      (continuous_const.add continuous_id).tendsto 0
    rw [add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
    show a < a + h
    linarith

/-- **§5.4, first step.**  For every `x`, the margin `v(x, ·)` is continuous and strictly
increasing on an interval `(f(x), f(x) + e)` (monotonicity theorem (S3) and Lemma 5.2). -/
theorem mono_germ (hS : SAFacts) (hM : MarginHyp Q f x₀ r₀ e₀) :
    ∀ x ∈ Metric.ball x₀ r₀, ∃ e, 0 < e ∧ e ≤ e₀ ∧
      ContinuousOn (fun y => vM Q (xy x y)) (Ioo (eval x f) (eval x f + e)) ∧
      StrictMonoOn (fun y => vM Q (xy x y)) (Ioo (eval x f) (eval x f + e)) := by
  intro x hx
  set a := eval x f with ha
  set g : ℝ → ℝ := fun h => vM Q (xy x (a + h)) with hg
  have hgSA : IsSAFun₁₁ (Ioo 0 e₀) g := by
    refine ⟨(dfn_lt (PT.const 0) (PT.coord ())).and (dfn_lt (PT.coord ()) (PT.const e₀)), ?_⟩
    have hX : ∀ i, PT (fun _ : Unit ⊕ Unit → ℝ => x i) := fun i => PT.const _
    have hY : PT (fun w : Unit ⊕ Unit → ℝ => a + w (.inl ())) := (PT.const a).add (PT.coord _)
    refine Dfn.of_iff (((dfn_lt (PT.const 0) (PT.coord (Sum.inl ()))).and
      (dfn_lt (PT.coord (Sum.inl ())) (PT.const e₀))).and
        (dfn_isGr Q hX hY (PT.coord (Sum.inr ())))) fun w => ?_
    simp only [Set.mem_ofPred_eq, Function.comp_apply, Set.mem_Ioo]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨⟨h1, h2⟩, funext fun u => ?_⟩
      exact (isGr_iff hM hx (by linarith) (by linarith) _).1 h3
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨⟨h1, h2⟩, (isGr_iff hM hx (by linarith) (by linarith) _).2 ?_⟩
      exact congrFun h3 ()
  obtain ⟨δ', hδ', hcont, hcase⟩ := hS.monotonicity g e₀ hM.he hgSA
  have hlim : Tendsto g (𝓝[>] 0) (𝓝 0) := (hM.lim x hx).comp (tendsto_add_nhdsGT a)
  have hpos : ∀ h ∈ Ioo 0 e₀, 0 < g h := fun h hh =>
    (hM.great x hx (a + h) (by linarith [hh.1]) (by linarith [hh.2])).2.1
  have hmono : StrictMonoOn g (Ioo 0 δ') := by
    rcases hcase with ⟨c, hc⟩ | hm | hanti
    · exfalso
      have h1 : Tendsto g (𝓝[>] 0) (𝓝 c) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Ioo_mem_nhdsGT hδ'.1] with h hh
        exact (hc h hh).symm
      have hc0 := tendsto_nhds_unique h1 hlim
      have := hpos (δ' / 2) ⟨by linarith [hδ'.1], by linarith [hδ'.1, hδ'.2]⟩
      rw [hc (δ' / 2) ⟨by linarith [hδ'.1], by linarith [hδ'.1]⟩] at this
      linarith
    · exact hm
    · exfalso
      have hb : ∀ᶠ h in 𝓝[>] (0 : ℝ), g (δ' / 2) ≤ g h := by
        filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < δ' / 2 by linarith [hδ'.1])] with h hh
        exact (hanti ⟨hh.1, by linarith [hh.2, hδ'.1]⟩ ⟨by linarith [hδ'.1], by linarith [hδ'.1]⟩
          hh.2).le
      have h1 := ge_of_tendsto hlim hb
      have h2 := hpos (δ' / 2) ⟨by linarith [hδ'.1], by linarith [hδ'.1, hδ'.2]⟩
      linarith
  refine ⟨δ', hδ'.1, hδ'.2, ?_, ?_⟩
  · have e1 : (fun y => vM Q (xy x y)) = fun y => g (y - a) := by
      funext y; simp only [g, add_sub_cancel]
    rw [e1]
    exact hcont.comp (continuousOn_id.sub continuousOn_const)
      (fun y hy => ⟨by show 0 < y - a; linarith [hy.1], by show y - a < δ'; linarith [hy.2]⟩)
  · intro y₁ hy₁ y₂ hy₂ hlt
    have := hmono ⟨sub_pos.2 hy₁.1, by linarith [hy₁.2]⟩ ⟨sub_pos.2 hy₂.1, by linarith [hy₂.2]⟩
      (by linarith)
    simpa [g] using this

/-- First-order form of "`v(x, ·)` is continuous and strictly increasing on
`(f(x), f(x) + e)`" (with `0 < e ≤ e₀`). -/
def GoodP (Q : MvPolynomial ((σ ⊕ Unit) ⊕ Option κ) ℝ) (f : MvPolynomial σ ℝ) (e₀ : ℝ)
    (x : σ → ℝ) (e : ℝ) : Prop :=
  0 < e ∧ e ≤ e₀ ∧
  (∀ y₁, ∀ y₂, ∀ s₁, ∀ s₂, eval x f < y₁ → y₁ < y₂ → y₂ < eval x f + e →
    IsGreatest (solS Q (xy x y₁)) s₁ → IsGreatest (solS Q (xy x y₂)) s₂ → s₁ < s₂) ∧
  (∀ y, ∀ s, eval x f < y → y < eval x f + e → IsGreatest (solS Q (xy x y)) s →
    ∀ ε, 0 < ε → ∃ η, 0 < η ∧ ∀ y', ∀ s', eval x f < y' → y' < eval x f + e →
      y - η < y' → y' < y + η → IsGreatest (solS Q (xy x y')) s' → s - ε < s' ∧ s' < s + ε)

theorem goodP_iff (hM : MarginHyp Q f x₀ r₀ e₀) {x : σ → ℝ} (hx : x ∈ Metric.ball x₀ r₀)
    {e : ℝ} (he : 0 < e) (hee : e ≤ e₀) :
    GoodP Q f e₀ x e ↔
      ContinuousOn (fun y => vM Q (xy x y)) (Ioo (eval x f) (eval x f + e)) ∧
      StrictMonoOn (fun y => vM Q (xy x y)) (Ioo (eval x f) (eval x f + e)) := by
  have hgr : ∀ y ∈ Ioo (eval x f) (eval x f + e), ∀ s,
      IsGreatest (solS Q (xy x y)) s ↔ vM Q (xy x y) = s :=
    fun y hy s => isGr_iff hM hx hy.1 (by linarith [hy.2]) s
  simp only [GoodP, he, hee, true_and]
  constructor
  · rintro ⟨hmono, hcont⟩
    refine ⟨?_, fun y₁ hy₁ y₂ hy₂ hlt => hmono y₁ y₂ _ _ hy₁.1 hlt hy₂.2
      ((hgr y₁ hy₁ _).2 rfl) ((hgr y₂ hy₂ _).2 rfl)⟩
    rw [Metric.continuousOn_iff]
    intro b hb ε hε
    obtain ⟨η, hη, h⟩ := hcont b _ hb.1 hb.2 ((hgr b hb _).2 rfl) ε hε
    refine ⟨η, hη, fun a ha hab => ?_⟩
    rw [Real.dist_eq, abs_lt] at hab ⊢
    have := h a _ ha.1 ha.2 (by linarith) (by linarith) ((hgr a ha _).2 rfl)
    constructor <;> linarith [this.1, this.2]
  · rintro ⟨hcont, hmono⟩
    refine ⟨fun y₁ y₂ s₁ s₂ h1 h12 h2 hg1 hg2 => ?_, fun y s h1 h2 hg ε hε => ?_⟩
    · have hy₁ : y₁ ∈ Ioo (eval x f) (eval x f + e) := ⟨h1, by linarith⟩
      have hy₂ : y₂ ∈ Ioo (eval x f) (eval x f + e) := ⟨by linarith, h2⟩
      rw [← (hgr y₁ hy₁ s₁).1 hg1, ← (hgr y₂ hy₂ s₂).1 hg2]
      exact hmono hy₁ hy₂ h12
    · have hy : y ∈ Ioo (eval x f) (eval x f + e) := ⟨h1, h2⟩
      rw [Metric.continuousOn_iff] at hcont
      obtain ⟨η, hη, h⟩ := hcont y hy ε hε
      refine ⟨η, hη, fun y' s' h1' h2' h3 h4 hg' => ?_⟩
      have hy' : y' ∈ Ioo (eval x f) (eval x f + e) := ⟨h1', h2'⟩
      have := h y' hy' (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
      rw [Real.dist_eq, abs_lt, (hgr y' hy' s').1 hg', (hgr y hy s).1 hg] at this
      constructor <;> linarith [this.1, this.2]

/-- **§5.4.**  There are a ball `U₂` and `e₂ > 0` such that `v(x, ·)` is continuous and strictly
increasing on `(f(x), f(x) + e₂)` for every `x ∈ U₂` ((S1), (S2), (S5)). -/
theorem uniform_mono (hS : SAFacts) (hM : MarginHyp Q f x₀ r₀ e₀) :
    ∃ (x₂ : σ → ℝ) (r₂ e₂ : ℝ), 0 < r₂ ∧ Metric.ball x₂ r₂ ⊆ Metric.ball x₀ r₀ ∧ 0 < e₂ ∧
      e₂ ≤ e₀ ∧ ∀ x ∈ Metric.ball x₂ r₂,
        ContinuousOn (fun y => vM Q (xy x y)) (Ioo (eval x f) (eval x f + e₂)) ∧
        StrictMonoOn (fun y => vM Q (xy x y)) (Ioo (eval x f) (eval x f + e₂)) := by
  set E := {w : σ ⊕ Unit → ℝ | GoodP Q f e₀ (fun i => w (.inl i)) (w (.inr ()))} with hEdef
  have hE : IsSA E := by
    show Dfn (fun w : σ ⊕ Unit → ℝ => GoodP Q f e₀ (fun i => w (.inl i)) (w (.inr ())))
    unfold GoodP
    dfn_tac
  obtain ⟨sec, hsec, hsecE⟩ := hS.choice E hE
  have hex : ∀ x ∈ Metric.ball x₀ r₀, GoodP Q f e₀ x (sec x ()) := by
    intro x hx
    obtain ⟨e, he, hee, hc, hm⟩ := mono_germ hS hM x hx
    exact hsecE x ⟨fun _ => e, (goodP_iff hM hx he hee).2 ⟨hc, hm⟩⟩
  have hg : IsSAFunOn₁ (Metric.ball x₀ r₀) (fun x => sec x ()) := by
    have := hsec.mono (isSA_ball x₀ r₀) (Set.subset_univ _)
    simpa [IsSAFunOn₁] using this
  obtain ⟨x₂, r₂, c, hr₂, hsub, hc, hcle⟩ := exists_ball_lower_bound hS Metric.isOpen_ball
    ⟨x₀, Metric.mem_ball_self hM.hr⟩ hg (fun x hx => (hex x hx).1)
  refine ⟨x₂, r₂, c, hr₂, hsub, hc,
    (hcle x₂ (Metric.mem_ball_self hr₂)).trans (hex x₂ (hsub (Metric.mem_ball_self hr₂))).2.1,
    fun x hx => ?_⟩
  have hgood := hex x (hsub hx)
  obtain ⟨hcont, hmono⟩ := (goodP_iff hM (hsub hx) hgood.1 hgood.2.1).1 hgood
  have hI : Ioo (eval x f) (eval x f + c) ⊆ Ioo (eval x f) (eval x f + sec x ()) :=
    Ioo_subset_Ioo le_rfl (by linarith [hcle x hx])
  exact ⟨hcont.mono hI, hmono.mono hI⟩

/-- **§5.4.**  On a smaller ball, `v(x, ·)` exceeds a fixed level `δ₀ > 0` on
`(f(x), f(x) + e₂)`. -/
theorem uniform_level (hS : SAFacts) (hM : MarginHyp Q f x₀ r₀ e₀) {x₂ : σ → ℝ} {r₂ e₂ : ℝ}
    (hr₂ : 0 < r₂) (hsub : Metric.ball x₂ r₂ ⊆ Metric.ball x₀ r₀) (he₂ : 0 < e₂)
    (he₂₀ : e₂ ≤ e₀) :
    ∃ (x₃ : σ → ℝ) (r₃ δ₀ : ℝ), 0 < r₃ ∧ Metric.ball x₃ r₃ ⊆ Metric.ball x₂ r₂ ∧ 0 < δ₀ ∧
      ∀ x ∈ Metric.ball x₃ r₃, ∃ y, eval x f < y ∧ y < eval x f + e₂ ∧ δ₀ < vM Q (xy x y) := by
  set E := {w : σ ⊕ Unit → ℝ | 0 < w (.inr ()) ∧ ∃ y, ∃ s,
    eval (fun i => w (.inl i)) f < y ∧ y < eval (fun i => w (.inl i)) f + e₂ ∧
    IsGreatest (solS Q (xy (fun i => w (.inl i)) y)) s ∧ w (.inr ()) < s} with hEdef
  have hE : IsSA E := by
    show Dfn (fun w : σ ⊕ Unit → ℝ => 0 < w (.inr ()) ∧ ∃ y, ∃ s,
      eval (fun i => w (.inl i)) f < y ∧ y < eval (fun i => w (.inl i)) f + e₂ ∧
      IsGreatest (solS Q (xy (fun i => w (.inl i)) y)) s ∧ w (.inr ()) < s)
    dfn_tac
  obtain ⟨sec, hsec, hsecE⟩ := hS.choice E hE
  have hex : ∀ x ∈ Metric.ball x₂ r₂, Sum.elim x (sec x) ∈ E := by
    intro x hx
    have hy1 : eval x f < eval x f + e₂ / 2 := by linarith
    have hy2 : eval x f + e₂ / 2 < eval x f + e₀ := by linarith
    obtain ⟨hgr, hpos, -⟩ := hM.great x (hsub hx) _ hy1 hy2
    refine hsecE x ⟨fun _ => vM Q (xy x (eval x f + e₂ / 2)) / 2, ?_⟩
    exact ⟨half_pos hpos, _, _, hy1, show eval x f + e₂ / 2 < eval x f + e₂ by linarith, hgr,
      half_lt_self hpos⟩
  have hg : IsSAFunOn₁ (Metric.ball x₂ r₂) (fun x => sec x ()) := by
    have := hsec.mono (isSA_ball x₂ r₂) (Set.subset_univ _)
    simpa [IsSAFunOn₁] using this
  obtain ⟨x₃, r₃, c, hr₃, hsub₃, hc, hcle⟩ := exists_ball_lower_bound hS Metric.isOpen_ball
    ⟨x₂, Metric.mem_ball_self hr₂⟩ hg (fun x hx => (hex x hx).1)
  refine ⟨x₃, r₃, c, hr₃, hsub₃, hc, fun x hx => ?_⟩
  obtain ⟨-, y, s, h1, h2, hgr, hlt⟩ := hex x (hsub₃ hx)
  have h1 : eval x f < y := h1
  have h2 : y < eval x f + e₂ := h2
  have hgr : IsGreatest (solS Q (xy x y)) s := hgr
  have hlt : sec x () < s := hlt
  refine ⟨y, h1, h2, ?_⟩
  rw [(isGr_iff hM (hsub (hsub₃ hx)) h1 (by linarith) s).1 hgr]
  exact lt_of_le_of_lt (hcle x hx) hlt

/-- **§5.4, the level functions `f_δ`.**  For `x ∈ U₃` and `0 < δ < δ₀` let `F x δ` be the unique
`y ∈ (f(x), f(x) + e₂)` with `v(x, y) = δ`.  Then `F x δ → f(x)` as `δ → 0⁺`, and `F` is
semialgebraic on `U₃ × (0, δ₀)` ((S1)). -/
theorem level_fun (hM : MarginHyp Q f x₀ r₀ e₀) {x₃ : σ → ℝ} {r₃ e₂ δ₀ : ℝ}
    (hsub : Metric.ball x₃ r₃ ⊆ Metric.ball x₀ r₀) (he₂ : 0 < e₂) (he₂₀ : e₂ ≤ e₀)
    (hδ₀ : 0 < δ₀) (hcm : ∀ x ∈ Metric.ball x₃ r₃,
      ContinuousOn (fun y => vM Q (xy x y)) (Ioo (eval x f) (eval x f + e₂)) ∧
      StrictMonoOn (fun y => vM Q (xy x y)) (Ioo (eval x f) (eval x f + e₂)))
    (hlev : ∀ x ∈ Metric.ball x₃ r₃, ∃ y, eval x f < y ∧ y < eval x f + e₂ ∧
      δ₀ < vM Q (xy x y)) :
    ∃ F : (σ → ℝ) → ℝ → ℝ,
      (∀ x ∈ Metric.ball x₃ r₃, ∀ δ ∈ Ioo 0 δ₀, eval x f < F x δ ∧ F x δ < eval x f + e₂ ∧
        vM Q (xy x (F x δ)) = δ) ∧
      (∀ x ∈ Metric.ball x₃ r₃, Tendsto (F x) (𝓝[>] 0) (𝓝 (eval x f))) ∧
      IsSAFunOn (boxDomain (Metric.ball x₃ r₃) δ₀) (uncurryOpt (fun x δ (_ : Unit) => F x δ)) := by
  -- existence by the intermediate value theorem
  have hexist : ∀ x ∈ Metric.ball x₃ r₃, ∀ δ ∈ Ioo 0 δ₀,
      ∃ y, eval x f < y ∧ y < eval x f + e₂ ∧ vM Q (xy x y) = δ := by
    intro x hx δ hδ
    obtain ⟨yp, h1, h2, h3⟩ := hlev x hx
    have hev : ∀ᶠ y in 𝓝[>] (eval x f), vM Q (xy x y) < δ ∧ y ∈ Ioo (eval x f) yp :=
      ((hM.lim x (hsub hx)).eventually (gt_mem_nhds hδ.1)).and (Ioo_mem_nhdsGT h1)
    obtain ⟨ym, hym, hymI⟩ := hev.exists
    have hsubI : Icc ym yp ⊆ Ioo (eval x f) (eval x f + e₂) :=
      fun y hy => ⟨by linarith [hymI.1, hy.1], by linarith [hy.2]⟩
    obtain ⟨y, hy, hyv⟩ := intermediate_value_Icc hymI.2.le ((hcm x hx).1.mono hsubI)
      ⟨hym.le, by linarith [hδ.2]⟩
    exact ⟨y, (hsubI hy).1, (hsubI hy).2, hyv⟩
  classical
  let F : (σ → ℝ) → ℝ → ℝ := fun x δ =>
    if h : ∃ y, eval x f < y ∧ y < eval x f + e₂ ∧ vM Q (xy x y) = δ then h.choose else 0
  have hF : ∀ x ∈ Metric.ball x₃ r₃, ∀ δ ∈ Ioo 0 δ₀, eval x f < F x δ ∧
      F x δ < eval x f + e₂ ∧ vM Q (xy x (F x δ)) = δ := by
    intro x hx δ hδ
    have h := hexist x hx δ hδ
    have hFe : F x δ = h.choose := by
      show (if h' : ∃ y, eval x f < y ∧ y < eval x f + e₂ ∧ vM Q (xy x y) = δ then h'.choose
        else 0) = _
      rw [dite_eq_left_of_eq_true (eq_true h)]
    rw [hFe]
    exact h.choose_spec
  have huniq : ∀ x ∈ Metric.ball x₃ r₃, ∀ δ ∈ Ioo 0 δ₀, ∀ y, eval x f < y →
      y < eval x f + e₂ → vM Q (xy x y) = δ → y = F x δ := by
    intro x hx δ hδ y h1 h2 h3
    obtain ⟨h1', h2', h3'⟩ := hF x hx δ hδ
    exact (hcm x hx).2.injOn ⟨h1, h2⟩ ⟨h1', h2'⟩ (h3.trans h3'.symm)
  refine ⟨F, hF, fun x hx => ?_, ?_⟩
  · -- `F x δ → f(x)`
    rw [Metric.tendsto_nhds]
    intro ε hε
    set ε' := min ε (e₂ / 2) with hε'
    have hε'pos : 0 < ε' := lt_min hε (by linarith)
    have hy'1 : eval x f < eval x f + ε' := by linarith
    have hy'2 : eval x f + ε' < eval x f + e₂ := by linarith [min_le_right ε (e₂ / 2)]
    have hc := (hM.great x (hsub hx) _ hy'1 (by linarith)).2.1
    filter_upwards [Ioo_mem_nhdsGT (lt_min hc hδ₀)] with δ hδ
    have hδ' : δ ∈ Ioo 0 δ₀ := ⟨hδ.1, lt_of_lt_of_le hδ.2 (min_le_right _ _)⟩
    obtain ⟨h1, h2, h3⟩ := hF x hx δ hδ'
    have hlt : F x δ < eval x f + ε' := by
      by_contra hge
      push Not at hge
      have hle : vM Q (xy x (eval x f + ε')) ≤ vM Q (xy x (F x δ)) :=
        ((hcm x hx).2.le_iff_le ⟨hy'1, hy'2⟩ ⟨h1, h2⟩).2 hge
      rw [h3] at hle
      linarith [hδ.2, min_le_left (vM Q (xy x (eval x f + ε'))) δ₀]
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [min_le_left ε (e₂ / 2)]
  · have hX : ∀ i, PT (fun w : Option σ ⊕ Unit → ℝ => w (Sum.inl (some i))) :=
      fun i => PT.coord _
    refine ⟨Dfn.of_iff ((dfn_ball x₃ r₃ (T := fun i (u : Option σ → ℝ) => u (some i))
      (fun i => PT.coord _)).and ((dfn_lt (PT.const 0) (PT.coord none)).and
        (dfn_lt (PT.coord none) (PT.const δ₀)))) fun u => Iff.rfl, ?_⟩
    refine Dfn.of_iff (((dfn_ball x₃ r₃ hX).and ((dfn_lt (PT.const 0)
      (PT.coord (Sum.inl none))).and (dfn_lt (PT.coord (Sum.inl none)) (PT.const δ₀)))).and
        ((dfn_lt (PT.evalp f hX) (PT.coord (Sum.inr ()))).and ((dfn_lt (PT.coord (Sum.inr ()))
          ((PT.evalp f hX).add (PT.const e₂))).and
            (dfn_isGr Q hX (PT.coord (Sum.inr ())) (PT.coord (Sum.inl none)))))) fun w => ?_
    change ((fun i => w (Sum.inl (some i))) ∈ Metric.ball x₃ r₃ ∧ 0 < w (Sum.inl none) ∧
        w (Sum.inl none) < δ₀) ∧ (eval (fun i => w (Sum.inl (some i))) f < w (Sum.inr ()) ∧
        w (Sum.inr ()) < eval (fun i => w (Sum.inl (some i))) f + e₂ ∧
        IsGreatest (solS Q (xy (fun i => w (Sum.inl (some i))) (w (Sum.inr ()))))
          (w (Sum.inl none))) ↔
      ((fun i => w (Sum.inl (some i))) ∈ Metric.ball x₃ r₃ ∧ 0 < w (Sum.inl none) ∧
        w (Sum.inl none) < δ₀) ∧
      (fun _ => F (fun i => w (Sum.inl (some i))) (w (Sum.inl none))) = w ∘ Sum.inr
    constructor
    · rintro ⟨⟨hxb, hδ1, hδ2⟩, h1, h2, hgr⟩
      refine ⟨⟨hxb, hδ1, hδ2⟩, funext fun u => ?_⟩
      have hv := (isGr_iff hM (hsub hxb) h1 (by linarith) _).1 hgr
      exact (huniq _ hxb _ ⟨hδ1, hδ2⟩ _ h1 h2 hv).symm
    · rintro ⟨⟨hxb, hδ1, hδ2⟩, heq⟩
      have hy : F (fun i => w (Sum.inl (some i))) (w (Sum.inl none)) = w (Sum.inr ()) :=
        congrFun heq ()
      obtain ⟨h1, h2, h3⟩ := hF _ hxb _ ⟨hδ1, hδ2⟩
      rw [hy] at h1 h2 h3
      exact ⟨⟨hxb, hδ1, hδ2⟩, h1, h2, (isGr_iff hM (hsub hxb) h1 (by linarith) _).2 h3⟩

/-- The level functions after Corollary 3.2: `F x δ = f_δ(x)` on `V* × (0, δ₁)`,
`V* = B(xs, rs)`. -/
structure LevelData (Q : MvPolynomial ((σ ⊕ Unit) ⊕ Option κ) ℝ) (f : MvPolynomial σ ℝ)
    (d : ℕ) (x₀ : σ → ℝ) (r₀ : ℝ) (F : (σ → ℝ) → ℝ → ℝ) (xs : σ → ℝ) (rs e₂ δ₁ : ℝ) : Prop where
  hrs : 0 < rs
  sub : Metric.ball xs rs ⊆ Metric.ball x₀ r₀
  he₂ : 0 < e₂
  hδ₁ : 0 < δ₁
  mono : ∀ x ∈ Metric.ball xs rs,
    StrictMonoOn (fun y => vM Q (xy x y)) (Ioo (eval x f) (eval x f + e₂))
  level : ∀ x ∈ Metric.ball xs rs, ∀ δ ∈ Ioo 0 δ₁,
    eval x f < F x δ ∧ F x δ < eval x f + e₂ ∧ vM Q (xy x (F x δ)) = δ
  smooth : ∀ δ ∈ Ioo 0 δ₁, ContDiffOn ℝ d (fun x => F x δ) (Metric.ball xs rs)
  conv : ∀ j ≤ d, TendstoUniformlyOn (fun δ x => iteratedFDeriv ℝ j (fun x => F x δ) x)
    (fun x => iteratedFDeriv ℝ j (fun x => eval x f) x) (𝓝[>] 0) (Metric.ball xs rs)

/-- **§5.4.**  The level functions `f_δ` exist, and by Corollary 3.2 their derivatives of order
`≤ d` converge uniformly to those of `f` on a ball `V*`. -/
theorem level_data (hS : SAFacts) (hM : MarginHyp Q f x₀ r₀ e₀) (d : ℕ) (hd : 1 ≤ d) :
    ∃ (F : (σ → ℝ) → ℝ → ℝ) (xs : σ → ℝ) (rs e₂ δ₁ : ℝ), e₂ ≤ e₀ ∧
      LevelData Q f d x₀ r₀ F xs rs e₂ δ₁ := by
  obtain ⟨x₂, r₂, e₂, hr₂, hsub₂, he₂, he₂₀, hcm₂⟩ := uniform_mono hS hM
  obtain ⟨x₃, r₃, δ₀, hr₃, hsub₃, hδ₀, hlev⟩ := uniform_level hS hM hr₂ hsub₂ he₂ he₂₀
  obtain ⟨F, hF, hFlim, hFsa⟩ := level_fun hM (hsub₃.trans hsub₂) he₂ he₂₀ hδ₀
    (fun x hx => hcm₂ x (hsub₃ hx)) hlev
  have hφ : ContinuousOn (fun x : σ → ℝ => fun _ : Unit => eval x f) (Metric.ball x₃ r₃) :=
    (continuous_pi fun _ => MvPolynomial.continuous_eval f).continuousOn
  obtain ⟨xs, rs, δ₁, hrs, hsubs, hδ₁, hδ₁₀, -, hCd, -, -, hconv⟩ :=
    derivatives_cor hS (κ := Unit) (Metric.ball x₃ r₃) Metric.isOpen_ball
      ⟨x₃, Metric.mem_ball_self hr₃⟩ δ₀ hδ₀ (fun x δ (_ : Unit) => F x δ) hFsa
      (fun x _ => eval x f) hφ (fun x hx => tendsto_pi_nhds.2 fun _ => hFlim x hx) d hd
  set e := ContinuousLinearEquiv.funUnique Unit ℝ ℝ with he
  have key : ∀ (j : ℕ) (G : (σ → ℝ) → (Unit → ℝ)) (x : σ → ℝ),
      iteratedFDeriv ℝ j (fun x => G x ()) x =
        (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin j => σ → ℝ) (Unit → ℝ) ℝ
          (e : (Unit → ℝ) →L[ℝ] ℝ)) (iteratedFDeriv ℝ j G x) := by
    intro j G x
    exact ContinuousLinearEquiv.iteratedFDeriv_comp_left (f := G) (x := x) (i := j) e
  refine ⟨F, xs, rs, e₂, δ₁, he₂₀, ⟨hrs, hsubs.trans (hsub₃.trans hsub₂), he₂, hδ₁,
    fun x hx => (hcm₂ x (hsub₃ (hsubs hx))).2,
    fun x hx δ hδ => hF x (hsubs hx) δ ⟨hδ.1, lt_of_lt_of_le hδ.2 hδ₁₀⟩, fun δ hδ => ?_,
    fun j hj => ?_⟩⟩
  · have : (fun x => F x δ) = (e : (Unit → ℝ) →L[ℝ] ℝ) ∘ (fun x (_ : Unit) => F x δ) := rfl
    rw [this]
    exact (e : (Unit → ℝ) →L[ℝ] ℝ).contDiff.comp_contDiffOn (hCd δ hδ)
  · have := ((ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin j => σ → ℝ)
      (Unit → ℝ) ℝ (e : (Unit → ℝ) →L[ℝ] ℝ)).uniformContinuous).comp_tendstoUniformlyOn
        (hconv j hj)
    have e1 : (fun δ x => iteratedFDeriv ℝ j (fun x => F x δ) x) = fun δ =>
        (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin j => σ → ℝ) (Unit → ℝ)
          ℝ (e : (Unit → ℝ) →L[ℝ] ℝ)) ∘
            (fun x => iteratedFDeriv ℝ j (fun x (_ : Unit) => F x δ) x) := by
      funext δ x
      exact key j (fun x _ => F x δ) x
    have e2 : (fun x => iteratedFDeriv ℝ j (fun x => eval x f) x) =
        (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin j => σ → ℝ) (Unit → ℝ)
          ℝ (e : (Unit → ℝ) →L[ℝ] ℝ)) ∘
            (fun x => iteratedFDeriv ℝ j (fun x (_ : Unit) => eval x f) x) := by
      funext x
      exact key j (fun x _ => eval x f) x
    rw [e1, e2]
    exact this

/-- The set `A = {(x, y) : x ∈ U₁, f(x) < y < f(x) + e₀}` of §5.2. -/
def Aset (f : MvPolynomial σ ℝ) (x₀ : σ → ℝ) (r₀ e₀ : ℝ) : Set (σ ⊕ Unit → ℝ) :=
  {ξ | (fun i => ξ (.inl i)) ∈ Metric.ball x₀ r₀ ∧ eval (fun i => ξ (.inl i)) f < ξ (.inr ()) ∧
    ξ (.inr ()) < eval (fun i => ξ (.inl i)) f + e₀}

omit [DecidableEq σ] in
theorem xy_eta (ξ : σ ⊕ Unit → ℝ) : xy (fun i => ξ (.inl i)) (ξ (.inr ())) = ξ := by
  funext v; cases v <;> rfl

omit [DecidableEq σ] in
theorem continuous_inl_part : Continuous fun ξ : σ ⊕ Unit → ℝ => fun i => ξ (.inl i) :=
  continuous_pi fun _ => continuous_apply _

theorem isOpen_Aset (f : MvPolynomial σ ℝ) (x₀ : σ → ℝ) (r₀ e₀ : ℝ) :
    IsOpen (Aset f x₀ r₀ e₀) := by
  have h1 : Continuous fun ξ : σ ⊕ Unit → ℝ => eval (fun i => ξ (.inl i)) f :=
    (MvPolynomial.continuous_eval f).comp continuous_inl_part
  have h2 : Continuous fun ξ : σ ⊕ Unit → ℝ => ξ (.inr ()) := continuous_apply _
  exact (Metric.isOpen_ball.preimage continuous_inl_part).inter
    ((isOpen_lt h1 h2).inter (isOpen_lt h2 (h1.add continuous_const)))

theorem isSA_Aset (f : MvPolynomial σ ℝ) (x₀ : σ → ℝ) (r₀ e₀ : ℝ) :
    IsSA (Aset f x₀ r₀ e₀) := by
  have hX : ∀ i, PT (fun ξ : σ ⊕ Unit → ℝ => ξ (.inl i)) := fun i => PT.coord _
  exact (dfn_ball x₀ r₀ hX).and ((dfn_lt (PT.evalp f hX) (PT.coord (Sum.inr ()))).and
    (dfn_lt (PT.coord (Sum.inr ())) ((PT.evalp f hX).add (PT.const e₀))))

omit [Fintype σ] in
theorem hasDerivAt_xy (x : σ → ℝ) (t : ℝ) :
    HasDerivAt (fun t => xy x t) (Pi.single (Sum.inr ()) 1) t := by
  rw [hasDerivAt_pi]
  intro i
  cases i with
  | inl j => simpa [xy, Pi.single_apply] using hasDerivAt_const t (x j)
  | inr u => simpa [xy] using hasDerivAt_id' t

omit [DecidableEq σ] in
theorem dist_xy_le (x : σ → ℝ) (t y : ℝ) : dist (xy x t) (xy x y) ≤ |t - y| := by
  refine (dist_pi_le_iff (abs_nonneg _)).2 fun i => ?_
  cases i with
  | inl j => simp [xy]
  | inr u => simp [xy, Real.dist_eq]

/-- **§5.5, nondegenerate points.**  In every nonempty open subset of
`A' = {(x, y) : x ∈ V*, f(x) < y < f(x) + e₂}` there is a point of `A°` at which
`∂v/∂y ≠ 0`. -/
theorem dense_good {d : ℕ} (hd : 1 ≤ d) {F : (σ → ℝ) → ℝ → ℝ} {xs : σ → ℝ} {rs e₂ δ₁ : ℝ}
    (he₂₀ : e₂ ≤ e₀) (hL : LevelData Q f d x₀ r₀ F xs rs e₂ δ₁)
    {A₀ : Set (σ ⊕ Unit → ℝ)} (hdense : Aset f x₀ r₀ e₀ ⊆ closure A₀)
    (hA₀ : ∀ ξ ∈ A₀, ContDiffAt ℝ d (vM Q) ξ) {N : Set (σ ⊕ Unit → ℝ)} (hN : IsOpen N)
    (hNne : N.Nonempty) (hNA : ∀ ξ ∈ N, (fun i => ξ (.inl i)) ∈ Metric.ball xs rs ∧
      eval (fun i => ξ (.inl i)) f < ξ (.inr ()) ∧ ξ (.inr ()) < eval (fun i => ξ (.inl i)) f + e₂) :
    ∃ ξ ∈ N, ξ ∈ A₀ ∧ fderiv ℝ (vM Q) ξ (Pi.single (.inr ()) 1) ≠ 0 := by
  have hNsub : N ⊆ Aset f x₀ r₀ e₀ := fun ξ hξ =>
    ⟨hL.sub (hNA ξ hξ).1, (hNA ξ hξ).2.1, by linarith [(hNA ξ hξ).2.2]⟩
  have hmeet : ∀ N' : Set (σ ⊕ Unit → ℝ), IsOpen N' → N'.Nonempty → N' ⊆ N → (N' ∩ A₀).Nonempty :=
    fun N' hN' ⟨ξ', hξ'⟩ hsub => mem_closure_iff.1 (hdense (hNsub (hsub hξ'))) N' hN' hξ'
  obtain ⟨ξ, hξN, hξA₀⟩ := hmeet N hN hNne subset_rfl
  have hd' : ((d : ℕ) : WithTop ℕ∞) ≠ ((⊤ : ℕ∞) : WithTop ℕ∞) := by simp
  have hd0 : ((d : ℕ) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hevN : ∀ᶠ z in 𝓝 ξ, z ∈ N := hN.mem_nhds hξN
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.1
    (hevN.and ((hA₀ ξ hξA₀).eventually hd'))
  by_cases hex : ∃ ξ' ∈ Metric.ball ξ ρ, fderiv ℝ (vM Q) ξ' (Pi.single (.inr ()) 1) ≠ 0
  · obtain ⟨ξ', hξ', hne⟩ := hex
    have hcont : ContinuousAt (fun ξ => fderiv ℝ (vM Q) ξ (Pi.single (.inr ()) 1)) ξ' :=
      ((hball ξ' hξ').2.continuousAt_fderiv hd0).clm_apply continuousAt_const
    obtain ⟨ρ', hρ', hball'⟩ := Metric.eventually_nhds_iff_ball.1
      ((hcont.eventually_ne hne).and (Metric.isOpen_ball.mem_nhds hξ'))
    obtain ⟨ξ'', hξ''1, hξ''2⟩ := hmeet (Metric.ball ξ' ρ') Metric.isOpen_ball
      ⟨ξ', Metric.mem_ball_self hρ'⟩ fun z hz => (hball z (hball' z hz).2).1
    exact ⟨ξ'', (hball ξ'' (hball' ξ'' hξ''1).2).1, hξ''2, (hball' ξ'' hξ''1).1⟩
  · exfalso
    push Not at hex
    set x := fun i => ξ (.inl i) with hx
    set y := ξ (.inr ()) with hy
    have hξeq : xy x y = ξ := xy_eta ξ
    have hmem : ∀ t, |t - y| < ρ → xy x t ∈ Metric.ball ξ ρ := fun t ht => by
      rw [Metric.mem_ball, ← hξeq]; exact lt_of_le_of_lt (dist_xy_le x t y) ht
    have hderiv : ∀ t, |t - y| < ρ → HasDerivAt (fun t => vM Q (xy x t)) 0 t := by
      intro t ht
      have hdiff := ((hball _ (hmem t ht)).2.differentiableAt hd0).hasFDerivAt
      have := hdiff.comp_hasDerivAt t (hasDerivAt_xy x t)
      rwa [hex _ (hmem t ht)] at this
    obtain ⟨c, hc, hcv⟩ := exists_hasDerivAt_eq_slope (fun t => vM Q (xy x t)) (fun _ => 0)
      (show y < y + ρ / 2 by linarith)
      (fun t ht => (hderiv t (by rw [abs_lt]; constructor <;> linarith [ht.1, ht.2])).continuousAt
        |>.continuousWithinAt)
      (fun t ht => hderiv t (by rw [abs_lt]; constructor <;> linarith [ht.1, ht.2]))
    have heq : vM Q (xy x (y + ρ / 2)) = vM Q (xy x y) := by
      have h3 : (vM Q (xy x (y + ρ / 2)) - vM Q (xy x y)) / (y + ρ / 2 - y) = 0 := hcv.symm
      rw [div_eq_zero_iff] at h3
      rcases h3 with h3 | h3
      · linarith
      · exfalso; linarith
    have hA1 := hNA _ ((hball _ (hmem y (by simp [hρ]))).1)
    have hA2 := hNA _ ((hball _ (hmem (y + ρ / 2) (by
      rw [add_sub_cancel_left, abs_of_pos (by linarith)]; linarith))).1)
    simp only [xy_inl, xy_inr] at hA1 hA2
    have := (hL.mono x hA1.1) ⟨hA1.2.1, hA1.2.2⟩ ⟨hA2.2.1, hA2.2.2⟩ (show y < y + ρ / 2 by linarith)
    linarith

/-- **§5.5, a level set near the graph.**  For every `ε > 0` there are a level `δ ∈ (0, ε)` and a
point `x₁` within `ε` of the centre of `V*` such that `ξ₁ = (x₁, f_δ(x₁)) ∈ A°` and
`∂v/∂y(ξ₁) ≠ 0`. -/
theorem good_points {d : ℕ} (hd : 1 ≤ d) {F : (σ → ℝ) → ℝ → ℝ} {xs : σ → ℝ} {rs e₂ δ₁ : ℝ}
    (he₂₀ : e₂ ≤ e₀) (hL : LevelData Q f d x₀ r₀ F xs rs e₂ δ₁)
    {A₀ : Set (σ ⊕ Unit → ℝ)} (hdense : Aset f x₀ r₀ e₀ ⊆ closure A₀)
    (hA₀ : ∀ ξ ∈ A₀, ContDiffAt ℝ d (vM Q) ξ) :
    ∀ ε > 0, ∃ (δ : ℝ) (x₁ : σ → ℝ), 0 < δ ∧ δ < ε ∧ δ < δ₁ ∧ dist x₁ xs < ε ∧
      x₁ ∈ Metric.ball xs rs ∧ xy x₁ (F x₁ δ) ∈ A₀ ∧
      fderiv ℝ (vM Q) (xy x₁ (F x₁ δ)) (Pi.single (.inr ()) 1) ≠ 0 := by
  intro ε hε
  set ε₁ := min ε rs with hε₁def
  have hε₁ : 0 < ε₁ := lt_min hε hL.hrs
  set b := min ε δ₁ / 2 with hbdef
  have hb : 0 < b := half_pos (lt_min hε hL.hδ₁)
  have hbε : b < min ε δ₁ := half_lt_self (lt_min hε hL.hδ₁)
  set a := b / 2 with hadef
  have ha : 0 < a := half_pos hb
  have hab : a < b := half_lt_self hb
  have haI : a ∈ Ioo 0 δ₁ := ⟨ha, by linarith [min_le_right ε δ₁]⟩
  have hbI : b ∈ Ioo 0 δ₁ := ⟨hb, by linarith [min_le_right ε δ₁]⟩
  have hsubb : Metric.ball xs ε₁ ⊆ Metric.ball xs rs := Metric.ball_subset_ball (min_le_right _ _)
  set S := {ξ : σ ⊕ Unit → ℝ | (fun i => ξ (.inl i)) ∈ Metric.ball xs ε₁} with hSdef
  have hSo : IsOpen S := Metric.isOpen_ball.preimage continuous_inl_part
  have hFc : ∀ δ ∈ Ioo 0 δ₁,
      ContinuousOn (fun ξ : σ ⊕ Unit → ℝ => F (fun i => ξ (.inl i)) δ) S :=
    fun δ hδ => (hL.smooth δ hδ).continuousOn.comp continuous_inl_part.continuousOn
      (fun ξ hξ => hsubb hξ)
  set N := (S ∩ (fun ξ : σ ⊕ Unit → ℝ => ξ (.inr ()) - F (fun i => ξ (.inl i)) a) ⁻¹' Ioi 0) ∩
    (fun ξ : σ ⊕ Unit → ℝ => F (fun i => ξ (.inl i)) b - ξ (.inr ())) ⁻¹' Ioi 0 with hNdef
  have hN : IsOpen N := by
    have hc1 : ContinuousOn (fun ξ : σ ⊕ Unit → ℝ => ξ (.inr ()) - F (fun i => ξ (.inl i)) a) S :=
      (continuous_apply (Sum.inr ())).continuousOn.sub (hFc a haI)
    have h1 := hc1.isOpen_inter_preimage hSo (isOpen_Ioi (a := (0 : ℝ)))
    have h2 : ContinuousOn (fun ξ : σ ⊕ Unit → ℝ => F (fun i => ξ (.inl i)) b - ξ (.inr ()))
        (S ∩ (fun ξ : σ ⊕ Unit → ℝ => ξ (.inr ()) - F (fun i => ξ (.inl i)) a) ⁻¹' Ioi 0) :=
      ((hFc b hbI).sub (continuous_apply _).continuousOn).mono inter_subset_left
    exact h2.isOpen_inter_preimage h1 (isOpen_Ioi (a := (0 : ℝ)))
  have hxs : xs ∈ Metric.ball xs rs := Metric.mem_ball_self hL.hrs
  obtain ⟨ha1, ha2, ha3⟩ := hL.level xs hxs a haI
  obtain ⟨hb1, hb2, hb3⟩ := hL.level xs hxs b hbI
  have hFab : F xs a < F xs b := by
    rw [← (hL.mono xs hxs).lt_iff_lt ⟨ha1, ha2⟩ ⟨hb1, hb2⟩, ha3, hb3]; exact hab
  have hNne : N.Nonempty := by
    refine ⟨xy xs ((F xs a + F xs b) / 2), ⟨⟨show xs ∈ Metric.ball xs ε₁ from
      Metric.mem_ball_self hε₁, ?_⟩, ?_⟩⟩
    · show 0 < (F xs a + F xs b) / 2 - F xs a
      linarith
    · show 0 < F xs b - (F xs a + F xs b) / 2
      linarith
  have hNA : ∀ ξ ∈ N, (fun i => ξ (.inl i)) ∈ Metric.ball xs rs ∧
      eval (fun i => ξ (.inl i)) f < ξ (.inr ()) ∧
      ξ (.inr ()) < eval (fun i => ξ (.inl i)) f + e₂ := by
    rintro ξ ⟨⟨hξS, hξa⟩, hξb⟩
    have hxr := hsubb hξS
    obtain ⟨h1, -, -⟩ := hL.level _ hxr a haI
    obtain ⟨-, h2, -⟩ := hL.level _ hxr b hbI
    simp only [Set.mem_preimage, Set.mem_Ioi, sub_pos] at hξa hξb
    exact ⟨hxr, by linarith, by linarith⟩
  obtain ⟨ξ₁, hξN, hξA₀, hD⟩ := dense_good hd he₂₀ hL hdense hA₀ hN hNne hNA
  obtain ⟨hx₁, hy1, hy2⟩ := hNA ξ₁ hξN
  obtain ⟨⟨hξS, hξa⟩, hξb⟩ := hξN
  set x₁ := fun i => ξ₁ (.inl i) with hx₁def
  set y₁ := ξ₁ (.inr ()) with hy₁def
  simp only [Set.mem_preimage, Set.mem_Ioi, sub_pos] at hξa hξb
  obtain ⟨h1a, h2a, h3a⟩ := hL.level x₁ hx₁ a haI
  obtain ⟨h1b, h2b, h3b⟩ := hL.level x₁ hx₁ b hbI
  set δ := vM Q (xy x₁ y₁) with hδdef
  have hδa : a < δ := by
    rw [← h3a]; exact (hL.mono x₁ hx₁) ⟨h1a, h2a⟩ ⟨hy1, hy2⟩ hξa
  have hδb : δ < b := by
    rw [← h3b]; exact (hL.mono x₁ hx₁) ⟨hy1, hy2⟩ ⟨h1b, h2b⟩ hξb
  have hδI : δ ∈ Ioo 0 δ₁ := ⟨by linarith, by linarith [min_le_right ε δ₁]⟩
  obtain ⟨h1δ, h2δ, h3δ⟩ := hL.level x₁ hx₁ δ hδI
  have hyF : F x₁ δ = y₁ := (hL.mono x₁ hx₁).injOn ⟨h1δ, h2δ⟩ ⟨hy1, hy2⟩ h3δ
  have hξ₁eq : xy x₁ (F x₁ δ) = ξ₁ := by rw [hyF]; exact xy_eta ξ₁
  refine ⟨δ, x₁, by linarith, by linarith [min_le_left ε δ₁], by linarith [min_le_right ε δ₁],
    ?_, hx₁, by rw [hξ₁eq]; exact hξA₀, by rw [hξ₁eq]; exact hD⟩
  have := hξS
  rw [Set.mem_ofPred_eq, Metric.mem_ball] at this
  linarith [min_le_left ε rs]

omit [Fintype σ] [DecidableEq σ] [Fintype κ] in
theorem unit_matrix_mul_eq_one {A M : Matrix Unit Unit ℝ} (h : A () () * M () () = 1) :
    A * M = 1 := by
  ext i j
  cases i; cases j
  simp [Matrix.mul_apply, h]

/-- **§5.5, the Taylor polynomial of a level set.**  At a nondegenerate point
`ξ₁ = (x₁, f_δ(x₁)) ∈ A°`, the Taylor polynomial of order `d` of `f_δ` at `x₁` is obtained from
the Taylor polynomial `P` of `v` at `ξ₁` by the Newton iteration of Lemma 3.4 for
`E = P - δ`. -/
theorem taylor_level {d : ℕ} (hd : 1 ≤ d) {F : (σ → ℝ) → ℝ → ℝ} {xs : σ → ℝ} {rs e₂ δ₁ : ℝ}
    (hL : LevelData Q f d x₀ r₀ F xs rs e₂ δ₁) {δ : ℝ} (hδ : δ ∈ Ioo 0 δ₁) {x₁ : σ → ℝ}
    (hx₁ : x₁ ∈ Metric.ball xs rs) (hcd : ContDiffAt ℝ d (vM Q) (xy x₁ (F x₁ δ)))
    (hD : fderiv ℝ (vM Q) (xy x₁ (F x₁ δ)) (Pi.single (.inr ()) 1) ≠ 0) :
    taylorPoly d (fun x => F x δ) x₁ =
      newtonPoly (fun _ : Unit => taylorPoly d (vM Q) (xy x₁ (F x₁ δ)) - C δ) x₁
        (fun _ => F x₁ δ) (fun _ _ => (eval (xy x₁ (F x₁ δ))
          (pderiv (.inr ()) (taylorPoly d (vM Q) (xy x₁ (F x₁ δ)))))⁻¹) d () := by
  set ξ₁ := xy x₁ (F x₁ δ) with hξ₁
  set P := taylorPoly d (vM Q) ξ₁ with hP
  have hpd : eval ξ₁ (pderiv (.inr ()) P) = fderiv ℝ (vM Q) ξ₁ (Pi.single (.inr ()) 1) :=
    eval_pderiv_taylorPoly hd hcd _
  have hFd : ContDiffAt ℝ d (fun x => F x δ) x₁ :=
    (hL.smooth δ hδ).contDiffAt (Metric.isOpen_ball.mem_nhds hx₁)
  have hωD : ContDiffAt ℝ d (fun x (_ : Unit) => F x δ) x₁ := contDiffAt_pi.2 fun _ => hFd
  refine (newtonPoly_eq_taylorPoly' (fun _ : Unit => P - C δ) x₁ (fun _ => F x₁ δ) _ d ?_
    (fun x _ => F x δ) rfl hωD ?_ ()).symm
  · have hJ : jacW (fun _ : Unit => P - C δ) (Sum.elim x₁ fun _ => F x₁ δ) () () =
        eval ξ₁ (pderiv (.inr ()) P) := by
      simp only [jacW, map_sub, pderiv_C, sub_zero]
      rfl
    refine unit_matrix_mul_eq_one ?_
    show (eval ξ₁ (pderiv (.inr ()) P))⁻¹ *
      jacW (fun _ : Unit => P - C δ) (Sum.elim x₁ fun _ => F x₁ δ) () () = 1
    rw [hJ, hpd]
    exact inv_mul_cancel₀ hD
  · intro l
    have hlev : ∀ᶠ x in 𝓝 x₁, vM Q (xy x (F x δ)) = δ := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hx₁] with x hx using (hL.level x hx δ hδ).2.2
    have hξt : Tendsto (fun x => xy x (F x δ)) (𝓝 x₁) (𝓝 ξ₁) :=
      (continuous_xy.continuousAt.comp (continuousAt_id.prodMk hFd.continuousAt)).tendsto
    have ho := (taylorPoly_isLittleO hcd).comp_tendsto hξt
    obtain ⟨K, t, ht, hK⟩ := (hFd.of_le (by exact_mod_cast hd)).exists_lipschitzOnWith
    have hbig : (fun x => ‖xy x (F x δ) - ξ₁‖ ^ d) =O[𝓝 x₁] (fun x => ‖x - x₁‖ ^ d) := by
      refine Asymptotics.IsBigO.of_bound ((max 1 (K : ℝ)) ^ d) ?_
      filter_upwards [ht] with x hx
      have h1 : ‖xy x (F x δ) - ξ₁‖ ≤ max 1 (K : ℝ) * ‖x - x₁‖ := by
        refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun v => ?_
        cases v with
        | inl i =>
          simp only [Pi.sub_apply, hξ₁, xy_inl]
          exact (norm_le_pi_norm (x - x₁) i).trans
            (le_mul_of_one_le_left (norm_nonneg _) (le_max_left _ _))
        | inr u =>
          simp only [Pi.sub_apply, hξ₁, xy_inr]
          have := hK.dist_le_mul x hx x₁ (mem_of_mem_nhds ht)
          rw [dist_eq_norm, dist_eq_norm] at this
          exact this.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
      rw [norm_pow, norm_pow, norm_norm, norm_norm, ← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) h1 d
    refine ((ho.trans_isBigO hbig).neg_left).congr' ?_ EventuallyEq.rfl
    filter_upwards [hlev] with x hx
    show -(vM Q (xy x (F x δ)) - eval (xy x (F x δ)) P) = eval (xy x (F x δ)) (P - C δ)
    rw [hx, map_sub, eval_C]
    ring

end Levels

/-! ### §5.4–5.5: from the margin to the polynomial -/

/-- **§5.4–5.5, the analytic core.**  Given the margin `v` (the largest `s` on the solutions of
`Q = 0`) with the properties of Lemma 5.2 and the conclusion of Proposition 4.5 for `Q`, the
polynomial `f` is approximated by the Newton iteration (Lemma 3.4) applied to `Ψ - δ`, where `Ψ`
is computed by one of the circuit graphs of Proposition 4.5. -/
theorem core (hS : SAFacts) (Q : MvPolynomial ((σ ⊕ Unit) ⊕ Option κ) ℝ)
    (f : MvPolynomial σ ℝ) (d : ℕ) (hd : 1 ≤ d) (hf : f.totalDegree ≤ d) (x₀ : σ → ℝ)
    (r₀ e₀ : ℝ) (hM : MarginHyp Q f x₀ r₀ e₀) (graphs : List (Shape (σ ⊕ Unit) × ℕ))
    (hvf : ∀ (A : Set (σ ⊕ Unit → ℝ)) (v : (σ ⊕ Unit → ℝ) → ℝ),
      IsOpen A → A.Nonempty → IsSA A → (∀ ξ ∈ A, IsGreatest (solS Q ξ) (v ξ)) →
      ∃ A₀ ⊆ A, IsSA A₀ ∧ A ⊆ closure A₀ ∧
        ∀ ξ₁ ∈ A₀, ContDiffAt ℝ d v ξ₁ ∧ ∃ Γo ∈ graphs, ∀ η > 0, ∃ a : ℕ → ℝ,
          ((Γo.1.values a).getD Γo.2 0).totalDegree ≤ d ∧
          ∀ m, |((Γo.1.values a).getD Γo.2 0).coeff m - (taylorPoly d v ξ₁).coeff m| < η) :
    ∀ η > 0, ∃ Γo ∈ graphs, ∃ (a : ℕ → ℝ) (x₁ : σ → ℝ) (y₁ δ b : ℝ), ∀ m,
      |(newtonPoly (fun _ : Unit => (Γo.1.values a).getD Γo.2 0 - C δ) x₁ (fun _ => y₁)
        (fun _ _ => b) d ()).coeff m - f.coeff m| < η := by
  intro η hη
  -- §5.4: the level functions and Corollary 3.2
  obtain ⟨F, xs, rs, e₂, δ₁, he₂₀, hL⟩ := level_data hS hM d hd
  -- Proposition 4.5 for the margin on `A`
  have hAgr : ∀ ξ ∈ Aset f x₀ r₀ e₀, IsGreatest (solS Q ξ) (vM Q ξ) := by
    rintro ξ ⟨h1, h2, h3⟩
    have := (hM.great _ h1 _ h2 h3).1
    rwa [xy_eta] at this
  have hAne : (Aset f x₀ r₀ e₀).Nonempty :=
    ⟨xy x₀ (eval x₀ f + e₀ / 2), show x₀ ∈ Metric.ball x₀ r₀ from Metric.mem_ball_self hM.hr,
      show eval x₀ f < eval x₀ f + e₀ / 2 by linarith [hM.he],
      show eval x₀ f + e₀ / 2 < eval x₀ f + e₀ by linarith [hM.he]⟩
  obtain ⟨A₀, -, -, hdense, hA₀⟩ :=
    hvf _ (vM Q) (isOpen_Aset f x₀ r₀ e₀) hAne (isSA_Aset f x₀ r₀ e₀) hAgr
  -- §5.5: nondegenerate points on level sets near the graph
  have hgood := good_points hd he₂₀ hL hdense (fun ξ hξ => (hA₀ ξ hξ).1)
  choose! δf x₁f hgf using hgood
  have hδt : Tendsto δf (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · rw [Metric.tendsto_nhds]
      intro ε hε
      filter_upwards [Ioo_mem_nhdsGT hε] with t ht
      obtain ⟨h1, h2, -⟩ := hgf t ht.1
      rw [Real.dist_eq, sub_zero, abs_of_pos h1]
      linarith [ht.2]
    · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      exact (hgf t ht).1
  have hxt : Tendsto x₁f (𝓝[>] 0) (𝓝 xs) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [Ioo_mem_nhdsGT hε] with t ht
    linarith [(hgf t ht.1).2.2.2.1, ht.2]
  have hxt' : Tendsto x₁f (𝓝[>] 0) (𝓝[Metric.ball xs rs] xs) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hxt, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    exact (hgf t ht).2.2.2.2.1
  -- convergence of the derivatives of `f_δ` at the moving points
  have hfd : ∀ n : WithTop ℕ∞, ContDiff ℝ n (fun x : σ → ℝ => eval x f) :=
    fun n => (AnalyticOnNhd.eval_mvPolynomial f).contDiff
  have hder : ∀ j ≤ d, Tendsto (fun t => iteratedFDeriv ℝ j (fun x => F x (δf t)) (x₁f t))
      (𝓝[>] 0) (𝓝 (iteratedFDeriv ℝ j (fun x => eval x f) xs)) := by
    intro j hj
    have hu : TendstoUniformlyOn (fun t x => iteratedFDeriv ℝ j (fun x => F x (δf t)) x)
        (fun x => iteratedFDeriv ℝ j (fun x => eval x f) x) (𝓝[>] 0) (Metric.ball xs rs) :=
      fun u hu => hδt.eventually (hL.conv j hj u hu)
    have hc : ContinuousWithinAt (fun x => iteratedFDeriv ℝ j (fun x => eval x f) x)
        (Metric.ball xs rs) xs :=
      ((hfd j).continuous_iteratedFDeriv le_rfl).continuousWithinAt
    exact hu.tendsto_comp hc hxt'
  have hcoef : ∀ m, Tendsto (fun t => (taylorPoly d (fun x => F x (δf t)) (x₁f t)).coeff m)
      (𝓝[>] 0) (𝓝 (f.coeff m)) := by
    intro m
    have := tendsto_coeff_taylorPoly_var hxt hder m
    rwa [taylorPoly_eval_poly hf] at this
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ m ∈ degSet σ d,
      |(taylorPoly d (fun x => F x (δf t)) (x₁f t)).coeff m - f.coeff m| < η / 2 := by
    rw [Filter.eventually_all_finset]
    intro m _
    filter_upwards [Metric.tendsto_nhds.1 (hcoef m) (η / 2) (half_pos hη)] with t ht
    rwa [Real.dist_eq] at ht
  obtain ⟨t, ht, htpos⟩ := (hev.and self_mem_nhdsWithin).exists
  obtain ⟨hδpos, -, hδδ₁, -, hx₁, hA₀mem, hD⟩ := hgf t htpos
  set δ := δf t with hδdef
  set x₁ := x₁f t with hx₁def
  set ξ₁ := xy x₁ (F x₁ δ) with hξ₁def
  obtain ⟨hcd, Γo, hΓo, happ⟩ := hA₀ ξ₁ hA₀mem
  have hT := taylor_level hd hL ⟨hδpos, hδδ₁⟩ hx₁ hcd hD
  set P := taylorPoly d (vM Q) ξ₁ with hPdef
  set b := (eval ξ₁ (pderiv (.inr ()) P))⁻¹ with hbdef
  -- the approximants of `P` given by Proposition 4.5, along `ηₙ = 1/(n+1)`
  choose! a ha using happ
  set an : ℕ → ℕ → ℝ := fun n => a (1 / ((n : ℝ) + 1)) with handef
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hPsi : ∀ m, Tendsto (fun n => ((Γo.1.values (an n)).getD Γo.2 0).coeff m) atTop
      (𝓝 (P.coeff m)) := by
    intro m
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq]
    refine lt_of_lt_of_le ((ha _ (hpos n)).2 m) (le_trans ?_ hN.le)
    gcongr
  have hNt : ∀ m, Tendsto (fun n => (newtonPoly (fun _ : Unit =>
      (Γo.1.values (an n)).getD Γo.2 0 - C δ) x₁ (fun _ => F x₁ δ) (fun _ _ => b) d ()).coeff m)
      atTop (𝓝 ((newtonPoly (fun _ : Unit => P - C δ) x₁ (fun _ => F x₁ δ)
        (fun _ _ => b) d ()).coeff m)) := by
    intro m
    refine tendsto_coeff_newtonPoly d (fun n _ => ?_) (fun _ => ?_) (fun _ m' => ?_)
      tendsto_const_nhds tendsto_const_nhds tendsto_const_nhds d () m
    · exact (totalDegree_sub _ _).trans (max_le (ha _ (hpos n)).1 (by simp))
    · exact (totalDegree_sub _ _).trans (max_le (totalDegree_taylorPoly_le _ _ _) (by simp))
    · simp only [coeff_sub]
      exact (hPsi m').sub tendsto_const_nhds
  have hev2 : ∀ᶠ n in atTop, ∀ m ∈ degSet σ d,
      |(newtonPoly (fun _ : Unit => (Γo.1.values (an n)).getD Γo.2 0 - C δ) x₁
        (fun _ => F x₁ δ) (fun _ _ => b) d ()).coeff m -
        (newtonPoly (fun _ : Unit => P - C δ) x₁ (fun _ => F x₁ δ)
          (fun _ _ => b) d ()).coeff m| < η / 2 := by
    rw [Filter.eventually_all_finset]
    intro m _
    filter_upwards [Metric.tendsto_nhds.1 (hNt m) (η / 2) (half_pos hη)] with n hn
    rwa [Real.dist_eq] at hn
  obtain ⟨n, hn⟩ := hev2.exists
  refine ⟨Γo, hΓo, an n, x₁, F x₁ δ, δ, b, fun m => ?_⟩
  by_cases hm : m ∈ degSet σ d
  · have h1 := hn m hm
    have h2 := ht m hm
    rw [hT] at h2
    calc _ ≤ |(newtonPoly (fun _ : Unit => (Γo.1.values (an n)).getD Γo.2 0 - C δ) x₁
          (fun _ => F x₁ δ) (fun _ _ => b) d ()).coeff m -
          (newtonPoly (fun _ : Unit => P - C δ) x₁ (fun _ => F x₁ δ)
            (fun _ _ => b) d ()).coeff m| +
          |(newtonPoly (fun _ : Unit => P - C δ) x₁ (fun _ => F x₁ δ)
            (fun _ _ => b) d ()).coeff m - f.coeff m| := abs_sub_le _ _ _
      _ < η / 2 + η / 2 := add_lt_add h1 h2
      _ = η := add_halves η
  · have h1 : (newtonPoly (fun _ : Unit => (Γo.1.values (an n)).getD Γo.2 0 - C δ) x₁
        (fun _ => F x₁ δ) (fun _ _ => b) d ()).coeff m = 0 :=
      notMem_support_iff.1 fun h => hm (support_subset_degSet
        (totalDegree_newtonPoly_le _ _ _ _ _ _) h)
    have h2 : f.coeff m = 0 := notMem_support_iff.1 fun h => hm (support_subset_degSet hf h)
    rw [h1, h2, sub_zero, abs_zero]
    exact hη

end OnesidedAux

/-! ### The composite circuit -/

namespace OnesidedAux

section Circuit

variable {ι : Type}

/-- One instruction per gate; the position `j` of the gate itself reads `0`. -/
def gateInstr (j : ℕ) : Gate ι → Instr ι ℕ
  | .var i => ⟨.add, .input i, .prev j⟩
  | .const k => ⟨.add, .const (k + 1), .prev j⟩
  | .add a b => ⟨.add, .prev a, .prev b⟩
  | .mul a b => ⟨.mul, .prev a, .prev b⟩

/-- The program graph of a circuit graph (constant slots shifted by one). -/
def shapeProg (Γ : Shape ι) : SLP ι ℕ := Γ.mapIdx fun j g => gateInstr j g

/-- Constants: slot `0` holds `δ`, slot `k + 1` holds `a k`. -/
def shiftC (δ : ℝ) (a : ℕ → ℝ) : ℕ → ℝ
  | 0 => δ
  | k + 1 => a k

theorem Shape.values_append_single (Γ : Shape ι) (g : Gate ι) (a : ℕ → ℝ) :
    Shape.values (Γ ++ [g]) a = Γ.values a ++ [g.eval a (Γ.values a)] := by
  simp [Shape.values, List.foldl_append]

theorem Shape.length_values (Γ : Shape ι) (a : ℕ → ℝ) : (Γ.values a).length = Γ.length := by
  induction Γ using List.reverseRecOn with
  | nil => rfl
  | append_singleton Γ g ih => simp [Shape.values_append_single, ih]

theorem values_shapeProg (Γ : Shape ι) (δ : ℝ) (a : ℕ → ℝ) :
    ((shapeProg Γ).instantiate (shiftC δ a)).values = Γ.values a := by
  induction Γ using List.reverseRecOn with
  | nil => rfl
  | append_singleton Γ g ih =>
    have hp : (shapeProg (Γ ++ [g])).instantiate (shiftC δ a) =
        (shapeProg Γ).instantiate (shiftC δ a) ++
          [⟨(gateInstr Γ.length g).op, (gateInstr Γ.length g).a.instantiate (shiftC δ a),
            (gateInstr Γ.length g).b.instantiate (shiftC δ a)⟩] := by
      simp [shapeProg, List.mapIdx_append, SLP.instantiate]
    rw [hp, BaurStrassen.values_append_single, ih, Shape.values_append_single]
    congr 2
    have hl : (Shape.values Γ a).length = Γ.length := Shape.length_values Γ a
    have h0 : (Shape.values Γ a)[Γ.length]? = none := List.getElem?_eq_none (by rw [hl])
    cases g with
    | var i =>
      simp [gateInstr, Instr.eval, Operand.instantiate, Operand.eval, ArithOp.apply, Gate.eval, h0]
    | const k =>
      simp [gateInstr, Instr.eval, Operand.instantiate, Operand.eval, ArithOp.apply, Gate.eval,
        h0, shiftC]
    | add j l => simp [gateInstr, Instr.eval, Operand.instantiate, Operand.eval, ArithOp.apply,
        Gate.eval]
    | mul j l => simp [gateInstr, Instr.eval, Operand.instantiate, Operand.eval, ArithOp.apply,
        Gate.eval]

end Circuit

/-- **The circuit** (§5.5): for a circuit graph `Γ` with output gate `o` on the variables
`(x, y)`, a circuit graph on `x` computing (with suitable constants) the Newton iteration of
Lemma 3.4 with one unknown `y` for `E = Ψ - δ`, where `Ψ` is computed by `Γ` at `o`. -/
theorem composite :
    ∃ K : ℕ, ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (Γo : Shape (σ ⊕ Unit) × ℕ) (d : ℕ),
      ∃ Γc : Shape σ, Γc.length ≤ K * ((d + 1) ^ 3 * (Γo.1.length + 2) + (d + 1) ^ 2 +
          Fintype.card σ) + 1 ∧
        ∀ (a : ℕ → ℝ) (x₁ : σ → ℝ) (y₁ δ b : ℝ), ∃ c : ℕ → ℝ,
          Γc.Computes c (newtonPoly (fun _ : Unit => (Γo.1.values a).getD Γo.2 0 - C δ) x₁
            (fun _ => y₁) (fun _ _ => b) d ()) := by
  obtain ⟨CN, hCN⟩ := newton_circuit
  refine ⟨CN, fun {σ} _ _ Γo d => ?_⟩
  -- the program graph of `E = Ψ - δ`
  set progE : SLP (σ ⊕ Unit) ℕ := shapeProg Γo.1 ++ [⟨.sub, .prev Γo.2, .const 0⟩] with hprogE
  set oE : Unit → Operand (σ ⊕ Unit) ℕ := fun _ => .prev Γo.1.length with hoE
  have hE : ∀ (a : ℕ → ℝ) (δ : ℝ), progOutputs progE (shiftC δ a) oE =
      fun _ => (Γo.1.values a).getD Γo.2 0 - C δ := by
    intro a δ
    funext u
    have hinst : progE.instantiate (shiftC δ a) = (shapeProg Γo.1).instantiate (shiftC δ a) ++
        [⟨.sub, .prev Γo.2, .const δ⟩] := by
      simp [hprogE, SLP.instantiate, Operand.instantiate, shiftC]
    simp only [progOutputs, hoE, Operand.instantiate]
    rw [hinst, BaurStrassen.values_append_single, values_shapeProg]
    simp only [Operand.eval]
    rw [List.getD_append_right _ _ _ _ (by rw [Shape.length_values]), Shape.length_values]
    simp [Instr.eval, Operand.eval, ArithOp.apply]
  obtain ⟨Γ', out, enc, hlen, hval⟩ := hCN progE oE d
  refine ⟨Γ' ++ [Gate.add (out ()) (Γ'.length + 1)], ?_, fun a x₁ y₁ δ b => ?_⟩
  · have hpl : progE.length = Γo.1.length + 1 := by simp [hprogE, shapeProg]
    rw [List.length_append, List.length_singleton]
    refine Nat.add_le_add_right (hlen.trans (le_of_eq ?_)) 1
    rw [hpl]
    simp
  · refine ⟨enc (shiftC δ a) x₁ (fun _ => y₁) (fun _ _ => b), ?_⟩
    rw [Shape.Computes, Shape.values_append_single]
    refine List.mem_append_right _ (List.mem_singleton.2 ?_)
    have h1 := hval (shiftC δ a) x₁ (fun _ => y₁) (fun _ _ => b) ()
    rw [hE] at h1
    simp only [Gate.eval]
    rw [List.getD_eq_default (Γ'.values _) (0 : MvPolynomial σ ℝ) (n := Γ'.length + 1)
      (by rw [Shape.length_values]; omega), add_zero]
    exact h1.symm

/-- The size bound of Theorem 5.1. -/
theorem size_bound (Cc Cv d t n g : ℕ)
    (hg : g ≤ Cv * ((d + 1) ^ 3 * (50 * t + 11 + 1) + (d + 1) ^ 2 * (4 * t + 3) ^ 2 + (n + 1))) :
    Cc * ((d + 1) ^ 3 * (g + 2) + (d + 1) ^ 2 + n) + 1 ≤
      (Cc * (68 * Cv + 4) + 1) * (d + 1) ^ 6 * ((t + 1) ^ 2 + n) := by
  set X := d + 1 with hXdef
  set W := X ^ 6 * ((t + 1) ^ 2 + n) with hWdef
  have hX : 1 ≤ X := by omega
  have hX3 : X ^ 3 ≤ X ^ 6 := Nat.pow_le_pow_right hX (by norm_num)
  have hX5 : X ^ 5 ≤ X ^ 6 := Nat.pow_le_pow_right hX (by norm_num)
  have hX2 : X ^ 2 ≤ X ^ 6 := Nat.pow_le_pow_right hX (by norm_num)
  have hX6 : 1 ≤ X ^ 6 := Nat.one_le_pow _ _ hX
  have hT : 1 ≤ (t + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hW : 1 ≤ W := by
    have := Nat.mul_le_mul hX6 (show 1 ≤ (t + 1) ^ 2 + n by omega)
    simpa using this
  have hW3 : X ^ 3 ≤ W := (Nat.le_mul_of_pos_right _ (by omega)).trans
    (Nat.mul_le_mul_right _ hX3)
  have hW2 : X ^ 2 ≤ W := (Nat.le_mul_of_pos_right _ (by omega)).trans
    (Nat.mul_le_mul_right _ hX2)
  have hWn : n ≤ W := (Nat.le_mul_of_pos_left _ (by omega)).trans
    (Nat.mul_le_mul_left _ (by omega))
  have a1 : X ^ 3 * (X ^ 3 * (50 * t + 11 + 1)) ≤ 50 * W := by
    have e : X ^ 3 * (X ^ 3 * (50 * t + 11 + 1)) = X ^ 6 * (50 * t + 12) := by ring
    rw [e, hWdef, mul_left_comm]
    exact Nat.mul_le_mul_left _ (by nlinarith)
  have a2 : X ^ 3 * (X ^ 2 * (4 * t + 3) ^ 2) ≤ 16 * W := by
    have e : X ^ 3 * (X ^ 2 * (4 * t + 3) ^ 2) = X ^ 5 * (4 * t + 3) ^ 2 := by ring
    rw [e, hWdef, mul_left_comm]
    exact Nat.mul_le_mul hX5 (by nlinarith)
  have a3 : X ^ 3 * (n + 1) ≤ 2 * W := by
    rw [hWdef, mul_left_comm]
    exact Nat.mul_le_mul hX3 (by nlinarith)
  have hg' : X ^ 3 * g ≤ Cv * (68 * W) := by
    calc X ^ 3 * g ≤ X ^ 3 * (Cv * (X ^ 3 * (50 * t + 11 + 1) + X ^ 2 * (4 * t + 3) ^ 2 +
          (n + 1))) := Nat.mul_le_mul_left _ hg
      _ = Cv * (X ^ 3 * (X ^ 3 * (50 * t + 11 + 1)) + X ^ 3 * (X ^ 2 * (4 * t + 3) ^ 2) +
          X ^ 3 * (n + 1)) := by ring
      _ ≤ Cv * (50 * W + 16 * W + 2 * W) := Nat.mul_le_mul_left _ (by omega)
      _ = Cv * (68 * W) := by ring
  calc Cc * (X ^ 3 * (g + 2) + X ^ 2 + n) + 1
      = Cc * (X ^ 3 * g + 2 * X ^ 3 + X ^ 2 + n) + 1 := by ring
    _ ≤ Cc * (Cv * (68 * W) + 2 * W + W + W) + W := by
        gcongr
    _ = (Cc * (68 * Cv + 4) + 1) * W := by ring
    _ = (Cc * (68 * Cv + 4) + 1) * X ^ 6 * ((t + 1) ^ 2 + n) := by rw [hWdef]; ring

end OnesidedAux

/-- **Theorem 5.1 (one-sided certificates).** -/
theorem onesided (hS : SAFacts) :
    ∃ C : ℕ, ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (d t k : ℕ) (f : MvPolynomial σ ℝ),
      1 ≤ d → f.totalDegree ≤ d →
      ∀ U : Set (σ → ℝ), IsOpen U → U.Nonempty →
      ∀ (T : Tree (σ ⊕ Unit ⊕ Fin k)) (M : Set (Option Bool)), T.depth ≤ t →
      (∀ x ∈ U, ∀ z, T.run (inp3 x (eval x f) z) ∉ M) →
      (∀ x ∈ U, ∃ ρ > 0, ∀ y, eval x f < y → y < eval x f + ρ →
        ∃ z, T.run (inp3 x y z) ∈ M) →
      BorderLE f (C * (d + 1) ^ 6 * ((t + 1) ^ 2 + Fintype.card σ)) := by
  obtain ⟨Cv, hCv⟩ := value_functions hS
  obtain ⟨Cc, hCc⟩ := OnesidedAux.composite
  refine ⟨Cc * (68 * Cv + 4) + 1, fun {σ} _ _ d t k f hd hf U hU hUne T M hT hi hii => ?_⟩
  classical
  obtain ⟨L', hLb, hLeq'⟩ := cells T t hT M
  -- (ii): the marked triples lie in the cells
  have hcov : ∀ x ∈ U, ∃ ρ > 0, ∀ y, eval x f < y → y < eval x f + ρ →
      ∃ B ∈ L', ∃ z, inp3 x y z ∈ B.carrier := by
    intro x hx
    obtain ⟨ρ, hρ, h⟩ := hii x hx
    refine ⟨ρ, hρ, fun y hy1 hy2 => ?_⟩
    obtain ⟨z, hz⟩ := h y hy1 hy2
    have : inp3 x y z ∈ {w | T.run w ∈ M} := hz
    rw [hLeq', Set.mem_iUnion₂] at this
    obtain ⟨B, hB, hzB⟩ := this
    exact ⟨B, hB, z, hzB⟩
  obtain ⟨B, hBL, x₀, r₀, e₀, hr₀, hball, he₀, hcert⟩ :=
    OnesidedAux.one_cell hS f U hU hUne L' hcov
  -- (i): no point of the graph has a certificate in `B`
  have hnot : ∀ x ∈ U, ¬ ∃ z, inp3 x (eval x f) z ∈ B.carrier := by
    rintro x hx ⟨z, hz⟩
    have : inp3 x (eval x f) z ∈ {w | T.run w ∈ M} := by
      rw [hLeq', Set.mem_iUnion₂]; exact ⟨B, hBL, hz⟩
    exact hi x hx z this
  obtain ⟨ζ, _, B', hζ, hlen, heqs, hposs, hcompB', hiff⟩ :=
    OnesidedAux.restrict_cell B (hLb B hBL)
  obtain ⟨pS, qS, hH, prog, cQ, oQ, hprog_len, hprog⟩ := Margin.exists_margin_graph B' hcompB'
  have hA : ∀ x ∈ Metric.ball x₀ r₀, ∀ y, eval x f < y → y < eval x f + e₀ →
      ∃ z, Sum.elim (OnesidedAux.xy x y) z ∈ B'.carrier :=
    fun x hx y h1 h2 => (hiff x y).1 (hcert x hx y h1 h2)
  have hnot' : ∀ x ∈ Metric.ball x₀ r₀,
      ¬ ∃ z, Sum.elim (OnesidedAux.xy x (eval x f)) z ∈ B'.carrier :=
    fun x hx h => hnot x (hball hx) ((hiff x (eval x f)).2 h)
  have hM : OnesidedAux.MarginHyp (Margin.marginPoly pS qS) f x₀ r₀ e₀ :=
    ⟨hr₀, he₀, Margin.marginPoly_nonneg pS qS, OnesidedAux.lemma_5_2_b hH hA,
      OnesidedAux.lemma_5_2_c hH he₀ hA hnot'⟩
  obtain ⟨graphs, hgraph_len, hgraphs⟩ := hCv prog oQ d hd
  have happrox := OnesidedAux.core hS (Margin.marginPoly pS qS) f d hd hf x₀ r₀ e₀ hM graphs
    (fun A v hAo hAne hASA hgr => hgraphs cQ A v hAo hAne hASA
      (by rw [hprog]; exact Margin.marginPoly_nonneg pS qS) (by rw [hprog]; exact hgr))
  choose Γc hΓclen hΓc using fun Γo : Shape (σ ⊕ Unit) × ℕ => hCc Γo d
  refine borderLE_of_approx hS (graphs.map Γc) _ ?_ f ?_
  · intro Γ hΓ
    obtain ⟨Γo, hΓo, rfl⟩ := List.mem_map.1 hΓ
    refine (hΓclen Γo).trans ?_
    refine OnesidedAux.size_bound Cc Cv d t (Fintype.card σ) Γo.1.length ?_
    refine (hgraph_len Γo hΓo).trans (Nat.mul_le_mul_left _ ?_)
    have hcardκ : Fintype.card (Margin.MVar ζ B'.poss.length) + 1 ≤ 4 * t + 3 := by
      simp only [Margin.MVar, Fintype.card_sum, Fintype.card_option, Fintype.card_fin]
      omega
    have hcardι : Fintype.card (σ ⊕ Unit) = Fintype.card σ + 1 := by simp
    rw [hcardι]
    gcongr
    omega
  · intro η hη
    obtain ⟨Γo, hΓo, a, x₁, y₁, δ, b, happ⟩ := happrox η hη
    obtain ⟨c, hc⟩ := hΓc Γo a x₁ y₁ δ b
    exact ⟨Γc Γo, List.mem_map_of_mem hΓo, c, _, hc, happ⟩

/-- The rejecting outcomes: a rejecting leaf, or a division by zero. -/
def rejecting : Set (Option Bool) := {some false, none}

/-- Theorem 5.1 applied with the rejecting leaves marked, to a tree that accepts `(x, y, z)` for
every `z` exactly when `y = f(x)` (on `U`). -/
theorem onesided_universal_eq (hS : SAFacts) :
    ∃ C : ℕ, ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (d t k : ℕ) (f : MvPolynomial σ ℝ),
      1 ≤ d → f.totalDegree ≤ d →
      ∀ U : Set (σ → ℝ), IsOpen U → U.Nonempty →
      ∀ T : Tree (σ ⊕ Unit ⊕ Fin k), T.depth ≤ t →
      (∀ x ∈ U, ∀ y : ℝ, (∀ z, T.Accepts (inp3 x y z)) ↔ y = eval x f) →
      BorderLE f (C * (d + 1) ^ 6 * ((t + 1) ^ 2 + Fintype.card σ)) := by
  obtain ⟨C, hC⟩ := onesided hS
  refine ⟨C, fun {σ} _ _ d t k f hd hf U hU hUne T hT hacc => ?_⟩
  have hrej : ∀ w, T.run w ∈ rejecting ↔ ¬ T.Accepts w := by
    intro w
    simp only [rejecting, Tree.Accepts, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases T.run w with _ | _ | _ <;> simp
  refine hC d t k f hd hf U hU hUne T rejecting hT (fun x hx z => ?_) (fun x hx => ?_)
  · rw [hrej, not_not]
    exact (hacc x hx (eval x f)).2 rfl z
  · refine ⟨1, one_pos, fun y hy _ => ?_⟩
    have hne : ¬ (∀ z, T.Accepts (inp3 x y z)) := fun h =>
      (ne_of_gt hy) ((hacc x hx y).1 h)
    obtain ⟨z, hz⟩ := not_forall.1 hne
    exact ⟨z, (hrej _).2 hz⟩

end ClassSep
