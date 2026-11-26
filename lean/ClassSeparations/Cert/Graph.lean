import ClassSeparations.Core.Local
import ClassSeparations.Core.Closure
import ClassSeparations.Cert.Isolate
import ClassSeparations.Basic.Cells

/-!
# The graph theorem and thresholds (§4.2–4.3)

**Theorem 4.2 (graph theorem).**  Let `f ∈ ℝ[X₁, …, Xₙ]` have degree at most `d ≥ 1` and let
`U ⊆ ℝⁿ` be open and nonempty.  Suppose that a tree of depth `t` on inputs
`(x, y, z) ∈ ℝⁿ × ℝ × ℝᵏ` satisfies, for all `x ∈ U` and `y ∈ ℝ`,
`(∃ z, the tree accepts (x, y, z)) ↔ y = f(x)`.  Then the border complexity of `f` is at most
`C((d+1)³t + (d+1)²(k̄+2)² + n)` with `k̄ = min(k, 2t)`, for an absolute constant `C`.

**Remark 4.3 (several outputs).**  The same holds for a polynomial map `f = (f₁, …, f_μ)` and
the language `y = f(x)` with `y ∈ ℝ^μ`, with the bound `C((d+1)³t + (d+1)²(k̄+μ+1)² + n)` for
each `fᵢ`.

**Theorem 4.4 (threshold theorem).**  The same bound as in Theorem 4.2 holds if the tree
verifies `y ≤ f(x)` (or `y ≥ f(x)`) in the existential sense.

## Proof outline

All four statements are derived from `graph_general`, in which `y ∈ ℝ^υ` and the tree decides
`R(y, f(x))` for a reflexive relation `R` such that `R(y, v)`, `y ≠ v` imply
`⟨λ_y, y⟩ < ⟨λ_y, v⟩` (`R` is `=` with `λ_y = 0`, or `≤`/`≥` with `λ_y = ±1`).

* Lemma 2.5 (`cells`) and `exists_interior_of_finite_cover` fix a cell `B` and a ball `U₁`.
* The certificate coordinates not occurring in `B` are set to `0` (`Jset`, `extZ`).
* Lemma 4.1 (`isolate`) gives `x₀, z₀, N, I, ζ`; the variables of `Q` are
  `w = (y, u) ∈ ℝ^(υ ⊕ (Jset \ I))` (`Kap`).
* `Q = ∑ pᵢ(x, y, (a, u))²` (`Qpoly`) has a program with `≤ 12t` operations
  (`qpoly_computes`), obtained by substitution in the cell's program and appending squares and
  sums.
* `localHyp_of_iso` verifies the hypotheses of Theorem 3.5 with `λ = (λ_y, 0)`.
* Theorem 3.5 and Lemma 3.3 conclude, since `f` is its own Taylor polynomial of order `d`.
-/

noncomputable section

open MvPolynomial Set

namespace ClassSep

namespace GraphAux

variable {α β : Type}

/-! ### Straight-line programs -/

theorem computes_mono {P P' : SLP β ℝ} (h : P <+: P') {p : MvPolynomial β ℝ}
    (hp : P.Computes p) : P'.Computes p := by
  obtain ⟨o, rfl⟩ := hp
  cases o with
  | input i => exact ⟨.input i, rfl⟩
  | const c => exact ⟨.const c, rfl⟩
  | prev j =>
    by_cases hj : j < P.length
    · refine ⟨.prev j, ?_⟩
      show P.values.getD j 0 = P'.values.getD j 0
      rw [BaurStrassen.getD_of_prefix (BaurStrassen.values_prefix h)
        (by rwa [BaurStrassen.length_values])]
    · refine ⟨.const 0, ?_⟩
      show P.values.getD j 0 = C 0
      rw [List.getD_eq_default _ _ (by rw [BaurStrassen.length_values]; omega), C_0]

theorem computes_snoc {P : SLP β ℝ} {p q : MvPolynomial β ℝ} (hp : P.Computes p)
    (hq : P.Computes q) (op : ArithOp) :
    ∃ ins : Instr β ℝ, (P ++ [ins]).Computes (op.apply p q) := by
  obtain ⟨o₁, rfl⟩ := hp
  obtain ⟨o₂, rfl⟩ := hq
  refine ⟨⟨op, o₁, o₂⟩, .prev P.length, ?_⟩
  show _ = (P ++ [_]).values.getD P.length 0
  rw [BaurStrassen.values_append_single,
    List.getD_append_right _ _ _ _ (by rw [BaurStrassen.length_values]),
    BaurStrassen.length_values, Nat.sub_self]
  rfl

/-- A program computing all the `ps` extends to one computing `∑ p²` with `2 |ps|` more
operations. -/
theorem computes_sumSq (P : SLP β ℝ) : ∀ ps : List (MvPolynomial β ℝ),
    (∀ p ∈ ps, P.Computes p) →
    ∃ P' : SLP β ℝ, P <+: P' ∧ P'.length ≤ P.length + 2 * ps.length ∧
      P'.Computes (ps.map (· ^ 2)).sum
  | [], _ => ⟨P, List.prefix_refl _, by simp, .const 0, by simp [Operand.eval]⟩
  | p :: ps, h => by
    obtain ⟨P₁, h₁, hl₁, hc₁⟩ :=
      computes_sumSq P ps (fun q hq => h q (List.mem_cons_of_mem _ hq))
    have hp₁ : P₁.Computes p := computes_mono h₁ (h p List.mem_cons_self)
    obtain ⟨i₁, hc₂⟩ := computes_snoc hp₁ hp₁ .mul
    have hS₂ := computes_mono (List.prefix_append P₁ [i₁]) hc₁
    obtain ⟨i₂, hc₃⟩ := computes_snoc hc₂ hS₂ .add
    refine ⟨P₁ ++ [i₁] ++ [i₂],
      h₁.trans ((List.prefix_append _ _).trans (List.prefix_append _ _)), ?_, ?_⟩
    · simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    · simpa [ArithOp.apply, sq] using hc₃

/-- Substitution of input coordinates by input coordinates or constants. -/
def opSubst (sub : α → β ⊕ ℝ) : Operand α ℝ → Operand β ℝ
  | .input a => (sub a).elim .input .const
  | .const c => .const c
  | .prev j => .prev j

/-- Substitution in a program. -/
def progSubst (sub : α → β ⊕ ℝ) (P : SLP α ℝ) : SLP β ℝ :=
  P.map fun ins => ⟨ins.op, opSubst sub ins.a, opSubst sub ins.b⟩

/-- The polynomial substituted for an input coordinate. -/
def subPoly (sub : α → β ⊕ ℝ) (a : α) : MvPolynomial β ℝ := (sub a).elim X C

theorem opSubst_eval (sub : α → β ⊕ ℝ) (vals : List (MvPolynomial α ℝ)) (o : Operand α ℝ) :
    (opSubst sub o).eval (vals.map (bind₁ (subPoly sub))) =
      bind₁ (subPoly sub) (o.eval vals) := by
  cases o with
  | input a =>
    rcases h : sub a with b | c <;> simp [opSubst, subPoly, h, Operand.eval]
  | const c => simp [opSubst, Operand.eval]
  | prev j =>
    simp only [opSubst, Operand.eval]
    simpa using List.getD_map vals 0 (n := j) (bind₁ (subPoly sub))

theorem foldl_progSubst (sub : α → β ⊕ ℝ) (P : SLP α ℝ) :
    ∀ init : List (MvPolynomial α ℝ),
    (progSubst sub P).foldl (fun vals ins => vals ++ [ins.eval vals])
        (init.map (bind₁ (subPoly sub))) =
      (P.foldl (fun vals ins => vals ++ [ins.eval vals]) init).map (bind₁ (subPoly sub)) := by
  induction P with
  | nil => intro init; rfl
  | cons ins P ih =>
    intro init
    simp only [progSubst, List.map_cons, List.foldl_cons] at ih ⊢
    rw [← ih]
    congr 1
    simp only [List.map_append, List.map_cons, List.map_nil]
    congr 2
    simp only [Instr.eval, opSubst_eval]
    cases ins.op <;> simp [ArithOp.apply]

theorem values_progSubst (sub : α → β ⊕ ℝ) (P : SLP α ℝ) :
    (progSubst sub P).values = P.values.map (bind₁ (subPoly sub)) := by
  have := foldl_progSubst sub P []
  simpa [SLP.values] using this

theorem computes_progSubst (sub : α → β ⊕ ℝ) {P : SLP α ℝ} {p : MvPolynomial α ℝ}
    (h : P.Computes p) : (progSubst sub P).Computes (bind₁ (subPoly sub) p) := by
  obtain ⟨o, rfl⟩ := h
  exact ⟨opSubst sub o, by rw [values_progSubst, opSubst_eval]⟩

theorem length_progSubst (sub : α → β ⊕ ℝ) (P : SLP α ℝ) :
    (progSubst sub P).length = P.length :=
  List.length_map _

/-- A program over `ℝ` gives a program graph with the same number of operations. -/
theorem exists_progOutput {P : SLP β ℝ} {q : MvPolynomial β ℝ} (h : P.Computes q) :
    ∃ (prog : SLP β ℕ) (oQ : Operand β ℕ) (cQ : ℕ → ℝ),
      prog.length = P.length ∧ progOutput prog cQ oQ = q := by
  obtain ⟨o, rfl⟩ := h
  refine ⟨BaurStrassen.graphOf (BaurStrassen.allConsts P o) P,
    BaurStrassen.toSlot (BaurStrassen.allConsts P o) o,
    fun m => (BaurStrassen.allConsts P o).getD m 0, BaurStrassen.length_graphOf _ _, ?_⟩
  rw [progOutput, BaurStrassen.graphOf_instantiate, BaurStrassen.toSlot_out_instantiate]

/-! ### Cells -/

theorem isSA_allZero (l : List (MvPolynomial α ℝ)) :
    IsSA {w : α → ℝ | ∀ p ∈ l, eval w p = 0} := by
  induction l with
  | nil => simpa using (isSA_univ : IsSA (Set.univ : Set (α → ℝ)))
  | cons p l ih =>
    have := (isSA_zero p).inter ih
    convert this using 1
    ext w
    simp

theorem isSA_allPos (l : List (MvPolynomial α ℝ)) :
    IsSA {w : α → ℝ | ∀ p ∈ l, 0 < eval w p} := by
  induction l with
  | nil => simpa using (isSA_univ : IsSA (Set.univ : Set (α → ℝ)))
  | cons p l ih =>
    have := (isSA_pos p).inter ih
    convert this using 1
    ext w
    simp

theorem isSA_carrier (B : Cell α) : IsSA B.carrier :=
  (isSA_allZero B.eqs).inter (isSA_allPos B.poss)

theorem eval_congr_vars {p : MvPolynomial α ℝ} {v v' : α → ℝ}
    (h : ∀ i ∈ p.vars, v i = v' i) : eval v p = eval v' p :=
  eval₂Hom_congr' rfl (fun i hi _ => h i hi) rfl

theorem mem_carrier_congr (B : Cell α) {Iv : Finset α}
    (hv : ∀ p ∈ B.eqs ++ B.poss, p.vars ⊆ Iv) {v v' : α → ℝ} (h : ∀ a ∈ Iv, v a = v' a) :
    v ∈ B.carrier ↔ v' ∈ B.carrier := by
  have he : ∀ p ∈ B.eqs ++ B.poss, eval v p = eval v' p :=
    fun p hp => eval_congr_vars (fun i hi => h i (hv p hp hi))
  show ((∀ p ∈ B.eqs, eval v p = 0) ∧ ∀ q ∈ B.poss, 0 < eval v q) ↔
    ((∀ p ∈ B.eqs, eval v' p = 0) ∧ ∀ q ∈ B.poss, 0 < eval v' q)
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun p hp => (he p (List.mem_append_left _ hp)) ▸ h1 p hp,
      fun q hq => (he q (List.mem_append_right _ hq)) ▸ h2 q hq⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun p hp => (he p (List.mem_append_left _ hp)).symm ▸ h1 p hp,
      fun q hq => (he q (List.mem_append_right _ hq)).symm ▸ h2 q hq⟩

theorem accepts_iff_cells {ι : Type} (T : Tree ι) (L : List (Cell ι))
    (hL : {w | T.run w ∈ ({some true} : Set (Option Bool))} = ⋃ B ∈ L, B.carrier)
    (w : ι → ℝ) : T.Accepts w ↔ ∃ B ∈ L, w ∈ B.carrier := by
  have := Set.ext_iff.1 hL w
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.mem_iUnion, exists_prop] at this
  exact this

theorem one_le_depth {ι : Type} (T : Tree ι) : 1 ≤ T.depth := by
  cases T <;> simp [Tree.depth]

/-! ### Semialgebraic sets -/

/-- The preimage of a semialgebraic set under `(x, z) ↦ (x, f(x), zp(z))`. -/
theorem isSA_pre {σ υ γ : Type} {k : ℕ} {S : Set (σ ⊕ υ ⊕ Fin k → ℝ)} (hS : IsSA S)
    (f : υ → MvPolynomial σ ℝ) (zp : Fin k → MvPolynomial γ ℝ) :
    IsSA {v : σ ⊕ γ → ℝ | Sum.elim (v ∘ Sum.inl) (Sum.elim
      (fun i => eval (v ∘ Sum.inl) (f i)) (fun j => eval (v ∘ Sum.inr) (zp j))) ∈ S} := by
  have := hS.preimage_poly (Sum.elim (fun a => X (Sum.inl a))
    (Sum.elim (fun u => rename Sum.inl (f u)) (fun j => rename Sum.inr (zp j))) :
      σ ⊕ υ ⊕ Fin k → MvPolynomial (σ ⊕ γ) ℝ)
  convert this using 1
  ext v
  simp only [Set.mem_ofPred_eq]
  apply iff_of_eq
  congr 1
  funext a
  rcases a with a | u | j <;> simp [eval_rename]

/-- Extension of `zJ : ℝ^J` by zero to `ℝᵏ`. -/
def extZ {k : ℕ} (Jset : Finset (Fin k)) (zJ : ↥Jset → ℝ) : Fin k → ℝ :=
  fun j => if h : j ∈ Jset then zJ ⟨j, h⟩ else 0

/-! ### The data of the proof after isolating a certificate

`Jset` is the set of certificate coordinates that occur in the cell, `I ⊆ Jset` the set of
fixed coordinates with values `z₀`.  The variables `w` of `Q` are `Kap = υ ⊕ (Jset \ I)`:
`w = (y, u)`. -/

section Data

variable {σ υ : Type} {k : ℕ} (Jset : Finset (Fin k)) (I : Finset ↥Jset) (z₀ : ↥Jset → ℝ)

/-- The variables `w = (y, u)`. -/
abbrev Kap (υ : Type) {k : ℕ} (Jset : Finset (Fin k)) (I : Finset ↥Jset) : Type :=
  υ ⊕ {j : ↥Jset // j ∉ I}

/-- The certificate coordinates in `Jset` determined by `w`: `(a, u)`. -/
def zJof (w : Kap υ Jset I → ℝ) : ↥Jset → ℝ :=
  fun j => if h : j ∈ I then z₀ j else w (Sum.inr ⟨j, h⟩)

/-- The input `(x, y, (a, u))` of the tree (with the coordinates outside `Jset` set to `0`). -/
def ptOf (x : σ → ℝ) (w : Kap υ Jset I → ℝ) : σ ⊕ υ ⊕ Fin k → ℝ :=
  Sum.elim x (Sum.elim (w ∘ Sum.inl) (extZ Jset (zJof Jset I z₀ w)))

/-- The substitution of the inputs of the cell's program. -/
def subst (σ υ : Type) : σ ⊕ υ ⊕ Fin k → (σ ⊕ Kap υ Jset I) ⊕ ℝ
  | .inl a => .inl (.inl a)
  | .inr (.inl u) => .inl (.inr (.inl u))
  | .inr (.inr j) =>
    if h : j ∈ Jset then
      (if h' : (⟨j, h⟩ : ↥Jset) ∈ I then .inr (z₀ ⟨j, h⟩) else .inl (.inr (.inr ⟨⟨j, h⟩, h'⟩)))
    else .inr 0

theorem eval_subPoly (x : σ → ℝ) (w : Kap υ Jset I → ℝ) (a : σ ⊕ υ ⊕ Fin k) :
    eval (Sum.elim x w) (subPoly (subst Jset I z₀ σ υ) a) = ptOf Jset I z₀ x w a := by
  rcases a with a | u | j
  · simp [subPoly, subst, ptOf]
  · simp [subPoly, subst, ptOf]
  · by_cases h : j ∈ Jset
    · by_cases h' : (⟨j, h⟩ : ↥Jset) ∈ I
      · simp [subPoly, subst, ptOf, extZ, zJof, h, h']
      · simp [subPoly, subst, ptOf, extZ, zJof, h, h']
    · simp [subPoly, subst, ptOf, extZ, h]

/-- The polynomial `Q(x, w) = ∑ pᵢ(x, y, (a, u))²`. -/
def Qpoly (B : Cell (σ ⊕ υ ⊕ Fin k)) : MvPolynomial (σ ⊕ Kap υ Jset I) ℝ :=
  ((B.eqs.map (bind₁ (subPoly (subst Jset I z₀ σ υ)))).map (· ^ 2)).sum

theorem eval_Qpoly (B : Cell (σ ⊕ υ ⊕ Fin k)) (x : σ → ℝ) (w : Kap υ Jset I → ℝ) :
    eval (Sum.elim x w) (Qpoly Jset I z₀ B) =
      (B.eqs.map fun p => (eval (ptOf Jset I z₀ x w) p) ^ 2).sum := by
  simp only [Qpoly, map_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro p _
  simp only [Function.comp_apply, map_pow, ClassSep.eval_bind₁', eval_subPoly]

theorem qpoly_computes {t : ℕ} {K : Set ℝ} (B : Cell (σ ⊕ υ ⊕ Fin k)) (hB : B.Bounded t K) :
    ∃ P : SLP (σ ⊕ Kap υ Jset I) ℝ, P.length ≤ 12 * t ∧ P.Computes (Qpoly Jset I z₀ B) := by
  obtain ⟨P', -, hlen, hc⟩ := computes_sumSq (progSubst (subst Jset I z₀ σ υ) B.prog)
    (B.eqs.map (bind₁ (subPoly (subst Jset I z₀ σ υ)))) (by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact computes_progSubst _ (hB.computes_eqs q hq))
  refine ⟨P', ?_, hc⟩
  rw [length_progSubst, List.length_map] at hlen
  have h1 := hB.prog_len
  have h2 := hB.eqs_len
  omega

theorem card_Kap [Fintype υ] : Fintype.card (Kap υ Jset I) ≤ Fintype.card υ + Jset.card := by
  rw [Fintype.card_sum]
  have := Fintype.card_subtype_le (fun j : ↥Jset => j ∉ I)
  rw [Fintype.card_coe] at this
  omega

/-- The map `φ(x) = (f(x), υ(x))`. -/
def phiOf (f : υ → MvPolynomial σ ℝ) (ζ : (σ → ℝ) → (↥Jset → ℝ)) (x : σ → ℝ) :
    Kap υ Jset I → ℝ :=
  Sum.elim (fun i => eval x (f i)) (fun j => ζ x j.1)

end Data

/-! ### The zero is isolated: the hypotheses of the local theorem -/

section Iso

open Filter Topology

variable {σ υ : Type} [Fintype σ] [Fintype υ] {k : ℕ}

/-- The core of the proofs of Theorems 4.2 and 4.4: after fixing a cell and isolating a
certificate, the polynomial `Q` and the map `φ` satisfy the hypotheses of the local theorem,
with `λ = (lamY, 0)`. -/
theorem localHyp_of_iso (f : υ → MvPolynomial σ ℝ) (R : (υ → ℝ) → (υ → ℝ) → Prop)
    (lamY : υ → ℝ) (hlam : ∀ y v, R y v → y ≠ v → lamY ⬝ᵥ y < lamY ⬝ᵥ v)
    (Acc : Set (σ ⊕ υ ⊕ Fin k → ℝ)) (U : Set (σ → ℝ))
    (hacc : ∀ x ∈ U, ∀ y : υ → ℝ,
      (∃ z, Sum.elim x (Sum.elim y z) ∈ Acc) ↔ R y (fun i => eval x (f i)))
    (B : Cell (σ ⊕ υ ⊕ Fin k)) (hBacc : B.carrier ⊆ Acc)
    (Jset : Finset (Fin k)) (U₁ : Set (σ → ℝ)) (hU₁ : U₁ ⊆ U)
    (F : Set (σ ⊕ ↥Jset → ℝ))
    (hF : ∀ x zJ, Sum.elim x zJ ∈ F ↔
      x ∈ U₁ ∧ Sum.elim x (Sum.elim (fun i => eval x (f i)) (extZ Jset zJ)) ∈ B.carrier)
    (x₀ : σ → ℝ) (z₀ : ↥Jset → ℝ) (N : Set (σ ⊕ ↥Jset → ℝ)) (I : Finset ↥Jset) (r₃ : ℝ)
    (ζ : (σ → ℝ) → (↥Jset → ℝ))
    (hN : IsOpen N) (hr₃ : 0 < r₃) (hsub : Metric.ball x₀ r₃ ⊆ U₁)
    (hζ : AnalyticOnNhd ℝ ζ (Metric.ball x₀ r₃))
    (hiso : ∀ x ∈ Metric.ball x₀ r₃, ∀ z : ↥Jset → ℝ,
      (Sum.elim x z ∈ F ∩ N ∧ ∀ i ∈ I, z i = z₀ i) ↔ z = ζ x) :
    ∃ ρ r₀ : ℝ, LocalHyp (Qpoly Jset I z₀ B) x₀ ρ (phiOf Jset I f ζ x₀) r₀
      (Sum.elim lamY 0) (phiOf Jset I f ζ) := by
  set φ := phiOf Jset I f ζ with hφdef
  have hζc : ContinuousOn ζ (Metric.ball x₀ r₃) := hζ.continuousOn
  have hφc : ContinuousOn φ (Metric.ball x₀ r₃) := by
    refine continuousOn_pi.2 fun a => ?_
    rcases a with u | j
    · exact (continuous_eval (f u)).continuousOn
    · exact continuousOn_pi.1 hζc j.1
  have hisoζ : ∀ x ∈ Metric.ball x₀ r₃, Sum.elim x (ζ x) ∈ F ∧ Sum.elim x (ζ x) ∈ N ∧
      ∀ i ∈ I, ζ x i = z₀ i := by
    intro x hx
    obtain ⟨⟨h1, h2⟩, h3⟩ := (hiso x hx (ζ x)).2 rfl
    exact ⟨h1, h2, h3⟩
  have hzJ : ∀ x ∈ Metric.ball x₀ r₃, zJof Jset I z₀ (φ x) = ζ x := by
    intro x hx
    funext j
    by_cases hj : j ∈ I
    · simp [zJof, hj, (hisoζ x hx).2.2 j hj]
    · simp [zJof, hj, φ, phiOf]
  have hpt : ∀ x ∈ Metric.ball x₀ r₃, ptOf Jset I z₀ x (φ x) ∈ B.carrier := by
    intro x hx
    have := ((hF x (ζ x)).1 (hisoζ x hx).1).2
    rw [ptOf, hzJ x hx]
    exact this
  -- continuity
  have hcSE : Continuous fun p : (σ → ℝ) × (Kap υ Jset I → ℝ) =>
      (Sum.elim p.1 p.2 : σ ⊕ Kap υ Jset I → ℝ) := by
    refine continuous_pi fun a => ?_
    rcases a with a | a
    · exact (continuous_apply a).comp continuous_fst
    · exact (continuous_apply a).comp continuous_snd
  have hptq : ∀ q : MvPolynomial (σ ⊕ υ ⊕ Fin k) ℝ,
      Continuous fun p : (σ → ℝ) × (Kap υ Jset I → ℝ) => eval (ptOf Jset I z₀ p.1 p.2) q := by
    intro q
    have : (fun p : (σ → ℝ) × (Kap υ Jset I → ℝ) => eval (ptOf Jset I z₀ p.1 p.2) q) =
        fun p => eval (Sum.elim p.1 p.2) (bind₁ (subPoly (subst Jset I z₀ σ υ)) q) := by
      funext p
      rw [ClassSep.eval_bind₁']
      simp only [eval_subPoly]
    rw [this]
    exact (continuous_eval _).comp hcSE
  have hGx : Continuous fun p : (σ → ℝ) × (Kap υ Jset I → ℝ) =>
      (Sum.elim p.1 (zJof Jset I z₀ p.2) : σ ⊕ ↥Jset → ℝ) := by
    refine continuous_pi fun a => ?_
    rcases a with a | j
    · exact (continuous_apply a).comp continuous_fst
    · by_cases hj : j ∈ I
      · simp only [Sum.elim_inr, zJof, hj, ↓reduceDIte]
        exact continuous_const
      · simp only [Sum.elim_inr, zJof, hj, ↓reduceDIte]
        exact (continuous_apply _).comp continuous_snd
  -- a neighbourhood of `(x₀, w₀)` on which the positivity conditions hold and `N` is met
  have hx₀ : x₀ ∈ Metric.ball x₀ r₃ := Metric.mem_ball_self hr₃
  have hev : ∀ᶠ p in 𝓝 (x₀, φ x₀), (∀ q ∈ B.poss, 0 < eval (ptOf Jset I z₀ p.1 p.2) q) ∧
      Sum.elim p.1 (zJof Jset I z₀ p.2) ∈ N := by
    refine Filter.Eventually.and ?_ ?_
    · have := (Filter.eventually_all_finite (List.finite_toSet B.poss)).2 (fun q hq =>
        ((hptq q).tendsto (x₀, φ x₀)).eventually (lt_mem_nhds ((hpt x₀ hx₀).2 q hq)))
      exact this.mono fun p hp q hq => hp q hq
    · refine (hGx.tendsto (x₀, φ x₀)).eventually_mem (hN.mem_nhds ?_)
      show Sum.elim x₀ (zJof Jset I z₀ (φ x₀)) ∈ N
      rw [hzJ x₀ hx₀]
      exact (hisoζ x₀ hx₀).2.1
  obtain ⟨ε, hε, hεp⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨δ, hδ, hδp⟩ := Metric.continuousAt_iff.1
    (hφc.continuousAt (Metric.isOpen_ball.mem_nhds hx₀)) (ε / 4) (by positivity)
  have h5 : 0 < min (min δ ε) r₃ := lt_min (lt_min hδ hε) hr₃
  have hK : ∀ ξ ∈ Metric.closedBall x₀ (min (min δ ε) r₃ / 2),
      ξ ∈ Metric.ball x₀ r₃ ∧ dist ξ x₀ < δ ∧ dist ξ x₀ < ε := by
    intro ξ hξ
    rw [Metric.mem_closedBall] at hξ
    have h1 : min (min δ ε) r₃ ≤ min δ ε := min_le_left _ _
    have h2 : min (min δ ε) r₃ ≤ r₃ := min_le_right _ _
    have h3 : min δ ε ≤ δ := min_le_left _ _
    have h4 : min δ ε ≤ ε := min_le_right _ _
    exact ⟨Metric.mem_ball.2 (by linarith), by linarith, by linarith⟩
  have hW : ∀ ξ ∈ Metric.closedBall x₀ (min (min δ ε) r₃ / 2),
      ∀ w ∈ Metric.closedBall (φ x₀) (ε / 2),
      (∀ q ∈ B.poss, 0 < eval (ptOf Jset I z₀ ξ w) q) ∧ Sum.elim ξ (zJof Jset I z₀ w) ∈ N := by
    intro ξ hξ w hw
    refine hεp (y := (ξ, w)) ?_
    rw [Prod.dist_eq]
    exact max_lt (hK ξ hξ).2.2 (lt_of_le_of_lt (Metric.mem_closedBall.1 hw) (by linarith))
  refine ⟨min (min δ ε) r₃ / 2, ε / 2, ⟨by positivity, by positivity, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- nonnegativity
    intro ξ _ w _
    show 0 ≤ eval (Sum.elim ξ w) (Qpoly Jset I z₀ B)
    rw [eval_Qpoly]
    refine List.sum_nonneg (fun a ha => ?_)
    obtain ⟨p, _, rfl⟩ := List.mem_map.1 ha
    positivity
  · -- continuity
    exact hφc.mono (fun ξ hξ => (hK ξ hξ).1)
  · -- `φ` stays near `w₀`
    intro ξ hξ
    have := hδp (hK ξ hξ).2.1
    linarith
  · -- `Q(ξ, φ(ξ)) = 0`
    intro ξ hξ
    show eval (Sum.elim ξ (φ ξ)) (Qpoly Jset I z₀ B) = 0
    rw [eval_Qpoly]
    apply List.sum_eq_zero
    intro a ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
    have h0 : eval (ptOf Jset I z₀ ξ (φ ξ)) p = 0 := (hpt ξ (hK ξ hξ).1).1 p hp
    simp only [h0]
    ring
  · -- uniqueness of the maximizer
    intro ξ hξ w hw hQ0 hne
    have hQ0' : (B.eqs.map fun p => (eval (ptOf Jset I z₀ ξ w) p) ^ 2).sum = 0 := by
      rw [← eval_Qpoly]; exact hQ0
    have hnn : ∀ a ∈ B.eqs.map fun p => (eval (ptOf Jset I z₀ ξ w) p) ^ 2, 0 ≤ a := by
      intro a ha
      obtain ⟨p, _, rfl⟩ := List.mem_map.1 ha
      positivity
    have hzero : ∀ p ∈ B.eqs, eval (ptOf Jset I z₀ ξ w) p = 0 := by
      intro p hp
      have := List.single_le_sum hnn _
        (List.mem_map_of_mem (f := fun p => (eval (ptOf Jset I z₀ ξ w) p) ^ 2) hp)
      rw [hQ0'] at this
      exact (pow_eq_zero_iff (n := 2) (by norm_num)).1 (le_antisymm this (sq_nonneg _))
    obtain ⟨hξ₃, -, -⟩ := hK ξ hξ
    have hcar : ptOf Jset I z₀ ξ w ∈ B.carrier := ⟨hzero, (hW ξ hξ w hw).1⟩
    have hξU : ξ ∈ U := hU₁ (hsub hξ₃)
    have hRw : R (w ∘ Sum.inl) (fun i => eval ξ (f i)) :=
      (hacc ξ hξU _).1 ⟨extZ Jset (zJof Jset I z₀ w), hBacc hcar⟩
    by_cases hy : w ∘ Sum.inl = fun i => eval ξ (f i)
    · exfalso
      apply hne
      have hFm : Sum.elim ξ (zJof Jset I z₀ w) ∈ F := by
        refine (hF ξ _).2 ⟨hsub hξ₃, ?_⟩
        have := hcar
        rw [ptOf, hy] at this
        exact this
      have hzeq : zJof Jset I z₀ w = ζ ξ :=
        (hiso ξ hξ₃ _).1 ⟨⟨hFm, (hW ξ hξ w hw).2⟩, fun i hi => by simp [zJof, hi]⟩
      funext a
      rcases a with u | ⟨j, hj⟩
      · exact congrFun hy u
      · have := congrFun hzeq j
        simp only [zJof, hj, ↓reduceDIte] at this
        rw [this]
        rfl
    · have := hlam _ _ hRw hy
      simpa [dotProduct, Fintype.sum_sum_type, φ, phiOf] using this

end Iso

end GraphAux

open GraphAux in
/-- The common form of Theorems 4.2 and 4.4 and Remark 4.3: the tree decides
`R(y, f(x))` in the existential sense, where `R` is reflexive and `y ↦ ⟨lamY, y⟩` is maximized
at `f(x)` among the `y` with `R(y, f(x))`. -/
theorem graph_general (hS : SAFacts) :
    ∃ C : ℕ, ∀ {σ υ : Type} [Fintype σ] [DecidableEq σ] [Fintype υ] [DecidableEq υ]
      (d t k : ℕ) (f : υ → MvPolynomial σ ℝ) (R : (υ → ℝ) → (υ → ℝ) → Prop) (lamY : υ → ℝ),
      (∀ v, R v v) → (∀ y v, R y v → y ≠ v → lamY ⬝ᵥ y < lamY ⬝ᵥ v) →
      1 ≤ d → (∀ i, (f i).totalDegree ≤ d) →
      ∀ U : Set (σ → ℝ), IsOpen U → U.Nonempty →
      ∀ T : Tree (σ ⊕ υ ⊕ Fin k), T.depth ≤ t →
      (∀ x ∈ U, ∀ y : υ → ℝ,
        (∃ z, T.Accepts (Sum.elim x (Sum.elim y z))) ↔ R y (fun i => eval x (f i))) →
      ∀ i, BorderLE (f i) (C * ((d + 1) ^ 3 * t +
        (d + 1) ^ 2 * (min k (2 * t) + Fintype.card υ + 1) ^ 2 + Fintype.card σ)) := by
  obtain ⟨CL, hCL⟩ := local_theorem hS
  refine ⟨13 * (CL + 1), ?_⟩
  intro σ υ _ _ _ _ d t k f R lamY hR hlam hd hf U hU hUne T hT hacc i
  have ht : 1 ≤ t := (one_le_depth T).trans hT
  -- Lemma 2.5: the accepted inputs form a finite union of cells
  obtain ⟨L, hLb, hLeq⟩ := cells T t hT {some true}
  have hAcc := accepts_iff_cells T L hLeq
  -- fixing a cell
  have hAsa : ∀ B : Cell (σ ⊕ υ ⊕ Fin k),
      IsSA {x : σ → ℝ | ∃ z, Sum.elim x (Sum.elim (fun i => eval x (f i)) z) ∈ B.carrier} := by
    intro B
    have h1 := (isSA_pre (isSA_carrier B) f
      (fun j : Fin k => (X j : MvPolynomial (Fin k) ℝ))).exists_sum (γ := Fin k)
    convert h1 using 1
    ext x
    simp [Function.comp_def]
  obtain ⟨B, hBL, hint⟩ : ∃ B ∈ L, (interior ({x : σ → ℝ |
      ∃ z, Sum.elim x (Sum.elim (fun i => eval x (f i)) z) ∈ B.carrier} ∩ U)).Nonempty := by
    classical
    obtain ⟨B, hB, hne⟩ := exists_interior_of_finite_cover hS L.toFinset
      (fun B => {x : σ → ℝ | ∃ z, Sum.elim x (Sum.elim (fun i => eval x (f i)) z) ∈ B.carrier})
      (fun B _ => hAsa B) hU hUne (by
        intro x hx
        obtain ⟨z, hz⟩ := (hacc x hx _).2 (hR _)
        obtain ⟨B, hB, hzB⟩ := (hAcc _).1 hz
        exact Set.mem_iUnion₂.2 ⟨B, List.mem_toFinset.2 hB, z, hzB⟩)
    exact ⟨B, List.mem_toFinset.1 hB, hne⟩
  obtain ⟨xc, hxc⟩ := hint
  obtain ⟨rc, hrc, hball⟩ := Metric.isOpen_iff.1 isOpen_interior xc hxc
  have hball' := hball.trans interior_subset
  -- the certificate coordinates occurring in the cell
  have hBb := hLb B hBL
  obtain ⟨Iv, hIvcard, -, hIv⟩ := hBb.vars
  obtain ⟨Jset, hJcard, hJ⟩ : ∃ Jset : Finset (Fin k), Jset.card ≤ min k (2 * t) ∧
      ∀ j, (Sum.inr (Sum.inr j) : σ ⊕ υ ⊕ Fin k) ∈ Iv → j ∈ Jset := by
    classical
    refine ⟨Finset.univ.filter (fun j => (Sum.inr (Sum.inr j) : σ ⊕ υ ⊕ Fin k) ∈ Iv),
      le_min ?_ ?_, fun j hj => by simp [hj]⟩
    · exact (Finset.card_le_univ _).trans (by simp)
    · refine (Finset.card_le_card_of_injOn (fun j => (Sum.inr (Sum.inr j) : σ ⊕ υ ⊕ Fin k))
        (fun j hj => by simpa using hj) (fun a _ b _ h => by simpa using h)).trans hIvcard
  -- the set `F`
  obtain ⟨F, hFdef⟩ : ∃ F : Set (σ ⊕ ↥Jset → ℝ), F = {v | v ∘ Sum.inl ∈ Metric.ball xc rc ∧
      Sum.elim (v ∘ Sum.inl) (Sum.elim (fun i => eval (v ∘ Sum.inl) (f i))
        (extZ Jset (v ∘ Sum.inr))) ∈ B.carrier} := ⟨_, rfl⟩
  have hF : ∀ x zJ, Sum.elim x zJ ∈ F ↔ x ∈ Metric.ball xc rc ∧
      Sum.elim x (Sum.elim (fun i => eval x (f i)) (extZ Jset zJ)) ∈ B.carrier := by
    intro x zJ
    rw [hFdef]
    exact Iff.rfl
  have hFsa : IsSA F := by
    rw [hFdef]
    have h1 := (isSA_ball xc rc).preimage_comp (Sum.inl : σ → σ ⊕ ↥Jset)
    have h2 := isSA_pre (isSA_carrier B) f
      (fun j : Fin k => if h : j ∈ Jset then (X ⟨j, h⟩ : MvPolynomial ↥Jset ℝ) else 0)
    convert h1.inter h2 using 1
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    apply and_congr Iff.rfl
    apply iff_of_eq
    congr 3
    funext j
    by_cases h : j ∈ Jset <;> simp [extZ, h]
  have hFsub : ∀ v ∈ F, v ∘ Sum.inl ∈ Metric.ball xc rc := by
    rw [hFdef]
    exact fun v hv => hv.1
  have hproj : ∀ x ∈ Metric.ball xc rc, ∃ zJ, Sum.elim x zJ ∈ F := by
    intro x hx
    obtain ⟨z, hz⟩ := (hball' hx).1
    refine ⟨fun j => z j.1, (hF x _).2 ⟨hx, ?_⟩⟩
    refine (mem_carrier_congr B hIv ?_).1 hz
    intro a ha
    rcases a with a | u | j
    · rfl
    · rfl
    · simp [extZ, hJ j ha]
  -- Lemma 4.1
  obtain ⟨x₀, z₀, N, I, r₃, ζ, -, hN, -, hr₃, hsub, -, hζ, hiso⟩ :=
    isolate hS xc rc hrc F hFsa hFsub hproj
  -- the hypotheses of the local theorem
  obtain ⟨ρ, r₀, hLH⟩ := localHyp_of_iso f R lamY hlam {w | T.Accepts w} U hacc B
    (fun w hw => (hAcc w).2 ⟨B, hBL, hw⟩) Jset (Metric.ball xc rc) (fun x hx => (hball' hx).2)
    F hF x₀ z₀ N I r₃ ζ hN hr₃ hsub hζ hiso
  obtain ⟨P, hPlen, hPc⟩ := qpoly_computes Jset I z₀ B hBb
  obtain ⟨prog, oQ, cQ, hplen, hout⟩ := exists_progOutput hPc
  obtain ⟨Γ, out, hΓ, hmain⟩ := hCL prog oQ d hd
  rw [← hout] at hLH
  obtain ⟨ξs, rs, Es, hrs, -, -, -, hEdim, -, happ⟩ := hmain cQ x₀ ρ _ r₀ _ _ hLH
  obtain ⟨ξ₁, hξ₁⟩ : (Metric.ball ξs rs \ Es).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at hcon
    have h2 : Metric.ball ξs rs ⊆ interior Es := interior_maximal hcon Metric.isOpen_ball
    rw [(dimLT_card_iff Es).1 hEdim] at h2
    exact h2 (Metric.mem_ball_self hrs)
  -- size bookkeeping
  have hcard : Fintype.card (Kap υ Jset I) ≤ Fintype.card υ + min k (2 * t) :=
    (card_Kap Jset I).trans (by omega)
  set S := (d + 1) ^ 3 * t + (d + 1) ^ 2 * (min k (2 * t) + Fintype.card υ + 1) ^ 2 +
    Fintype.card σ with hS_def
  have hS1 : 1 ≤ S := by
    have : 1 ≤ (d + 1) ^ 3 * t := Nat.one_le_iff_ne_zero.2 (by positivity)
    omega
  have hbound : Γ.length ≤ 13 * (CL + 1) * S := by
    have hpl : prog.length + 1 ≤ 13 * t := by omega
    have hk2 : Fintype.card (Kap υ Jset I) ^ 2 ≤ (min k (2 * t) + Fintype.card υ + 1) ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    calc Γ.length ≤ CL * ((d + 1) ^ 3 * (prog.length + 1) +
          (d + 1) ^ 2 * Fintype.card (Kap υ Jset I) ^ 2 + Fintype.card σ) := hΓ
      _ ≤ CL * ((d + 1) ^ 3 * (13 * t) +
          (d + 1) ^ 2 * (min k (2 * t) + Fintype.card υ + 1) ^ 2 + Fintype.card σ) := by
        gcongr
      _ ≤ CL * (13 * S) := by
        apply Nat.mul_le_mul_left
        rw [hS_def]
        ring_nf
        omega
      _ ≤ 13 * (CL + 1) * S := by
        rw [show CL * (13 * S) = 13 * CL * S by ring]
        exact Nat.mul_le_mul_right _ (by omega)
  -- Lemma 3.3
  refine borderLE_of_approx hS [Γ, [Gate.const 0]] _ ?_ (f i) ?_
  · intro Γ' hΓ'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hΓ'
    rcases hΓ' with rfl | rfl
    · exact hbound
    · simp only [List.length_cons, List.length_nil, zero_add]
      nlinarith
  · intro η hη
    obtain ⟨a, ha⟩ := happ ξ₁ hξ₁ η hη
    have hc := (ha (Sum.inl i)).2
    have htay : taylorPoly d (fun ξ => phiOf Jset I f ζ ξ (Sum.inl i)) ξ₁ = f i :=
      taylorPoly_eval_poly (hf i) ξ₁
    rw [htay] at hc
    by_cases hlt : out (Sum.inl i) < (Γ.values a).length
    · refine ⟨Γ, by simp, a, _, ?_, hc⟩
      rw [List.getD_eq_getElem _ _ hlt]
      exact List.getElem_mem hlt
    · rw [List.getD_eq_default _ _ (not_lt.1 hlt)] at hc
      refine ⟨[Gate.const 0], by simp, fun _ => 0, 0, ?_, hc⟩
      simp [Shape.Computes, Shape.values, Gate.eval]

/-- **Remark 4.3 (several outputs).** -/
theorem graph_theorem_vec (hS : SAFacts) :
    ∃ C : ℕ, ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (μ d t k : ℕ)
      (f : Fin μ → MvPolynomial σ ℝ), 1 ≤ d → (∀ i, (f i).totalDegree ≤ d) →
      ∀ U : Set (σ → ℝ), IsOpen U → U.Nonempty →
      ∀ T : Tree (σ ⊕ Fin μ ⊕ Fin k), T.depth ≤ t →
      (∀ x ∈ U, ∀ y : Fin μ → ℝ,
        (∃ z, T.Accepts (Sum.elim x (Sum.elim y z))) ↔ y = fun i => eval x (f i)) →
      ∀ i, BorderLE (f i)
        (C * ((d + 1) ^ 3 * t + (d + 1) ^ 2 * (min k (2 * t) + μ + 1) ^ 2 + Fintype.card σ)) := by
  obtain ⟨C, hC⟩ := graph_general hS
  refine ⟨C, ?_⟩
  intro σ _ _ μ d t k f hd hf U hU hUne T hT hacc i
  have h := hC d t k f (fun y v => y = v) 0 (fun _ => rfl) (fun _ _ h hne => absurd h hne) hd hf
    U hU hUne T hT hacc i
  simpa only [Fintype.card_fin] using h

/-- **Theorem 4.2 (graph theorem).** -/
theorem graph_theorem (hS : SAFacts) :
    ∃ C : ℕ, ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (d t k : ℕ) (f : MvPolynomial σ ℝ),
      1 ≤ d → f.totalDegree ≤ d →
      ∀ U : Set (σ → ℝ), IsOpen U → U.Nonempty →
      ∀ T : Tree (σ ⊕ Unit ⊕ Fin k), T.depth ≤ t →
      (∀ x ∈ U, ∀ y : ℝ, (∃ z, T.Accepts (inp3 x y z)) ↔ y = eval x f) →
      BorderLE f
        (C * ((d + 1) ^ 3 * t + (d + 1) ^ 2 * (min k (2 * t) + 2) ^ 2 + Fintype.card σ)) := by
  obtain ⟨C, hC⟩ := graph_general hS
  refine ⟨C, ?_⟩
  intro σ _ _ d t k f hd hf U hU hUne T hT hacc
  have h := hC (υ := Unit) d t k (fun _ => f) (fun y v => y = v) 0 (fun _ => rfl)
    (fun _ _ h hne => absurd h hne) hd (fun _ => hf) U hU hUne T hT (fun x hx y => by
      rw [show (y = fun _ => eval x f) ↔ y () = eval x f from
        ⟨fun h => congrFun h (), fun h => funext fun _ => h⟩]
      exact hacc x hx (y ())) ()
  rwa [Fintype.card_unit] at h

/-- **Theorem 4.4 (threshold theorem)**, case `y ≤ f(x)`. -/
theorem threshold_theorem_le (hS : SAFacts) :
    ∃ C : ℕ, ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (d t k : ℕ) (f : MvPolynomial σ ℝ),
      1 ≤ d → f.totalDegree ≤ d →
      ∀ U : Set (σ → ℝ), IsOpen U → U.Nonempty →
      ∀ T : Tree (σ ⊕ Unit ⊕ Fin k), T.depth ≤ t →
      (∀ x ∈ U, ∀ y : ℝ, (∃ z, T.Accepts (inp3 x y z)) ↔ y ≤ eval x f) →
      BorderLE f
        (C * ((d + 1) ^ 3 * t + (d + 1) ^ 2 * (min k (2 * t) + 2) ^ 2 + Fintype.card σ)) := by
  obtain ⟨C, hC⟩ := graph_general hS
  refine ⟨C, ?_⟩
  intro σ _ _ d t k f hd hf U hU hUne T hT hacc
  have h := hC (υ := Unit) d t k (fun _ => f) (fun y v => y () ≤ v ()) (fun _ => 1)
    (fun _ => le_rfl) (fun y v h hne => by
      have h' : y () ≠ v () := fun h' => hne (funext fun _ => h')
      simpa [dotProduct] using lt_of_le_of_ne h h')
    hd (fun _ => hf) U hU hUne T hT (fun x hx y => hacc x hx (y ())) ()
  rwa [Fintype.card_unit] at h

/-- **Theorem 4.4 (threshold theorem)**, case `y ≥ f(x)`. -/
theorem threshold_theorem_ge (hS : SAFacts) :
    ∃ C : ℕ, ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (d t k : ℕ) (f : MvPolynomial σ ℝ),
      1 ≤ d → f.totalDegree ≤ d →
      ∀ U : Set (σ → ℝ), IsOpen U → U.Nonempty →
      ∀ T : Tree (σ ⊕ Unit ⊕ Fin k), T.depth ≤ t →
      (∀ x ∈ U, ∀ y : ℝ, (∃ z, T.Accepts (inp3 x y z)) ↔ eval x f ≤ y) →
      BorderLE f
        (C * ((d + 1) ^ 3 * t + (d + 1) ^ 2 * (min k (2 * t) + 2) ^ 2 + Fintype.card σ)) := by
  obtain ⟨C, hC⟩ := graph_general hS
  refine ⟨C, ?_⟩
  intro σ _ _ d t k f hd hf U hU hUne T hT hacc
  have h := hC (υ := Unit) d t k (fun _ => f) (fun y v => v () ≤ y ()) (fun _ => -1)
    (fun _ => le_rfl) (fun y v h hne => by
      have h' : v () ≠ y () := fun h' => hne (funext fun _ => h'.symm)
      simpa [dotProduct] using lt_of_le_of_ne h h')
    hd (fun _ => hf) U hU hUne T hT (fun x hx y => hacc x hx (y ())) ()
  rwa [Fintype.card_unit] at h

end ClassSep
