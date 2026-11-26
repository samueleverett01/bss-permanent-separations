import ClassSeparations.SA.Lemmas

/-!
# Derivatives of semialgebraic families (§3.1)

**Lemma 3.1.**  Let `V ⊆ ℝᴺ` be open and nonempty, `g : V × (0, ε₀) → ℝ` semialgebraic, and
`g₀ : V → ℝ` continuous with `g(ξ, ε) → g₀(ξ)` as `ε → 0⁺` for every `ξ ∈ V`.  Then there are
an open ball `V' ⊆ V` and `ε' > 0` such that `g` is `C¹` on `V' × (0, ε')`, `g₀` is `C¹` on
`V'`, and `∂g/∂ξᵢ(·, ε) → ∂g₀/∂ξᵢ` uniformly on `V'`.

**Corollary 3.2.**  The same for maps to `ℝ^κ`, with uniform convergence of all
`ξ`-derivatives up to order `D`.  We state the convergence of derivatives with the iterated
Fréchet derivatives `iteratedFDeriv ℝ j`, whose components are the partial derivatives
`∂^α` with `|α| = j`.
-/

noncomputable section

open Set Filter Topology

namespace ClassSep

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The domain `V × (0, ε₀)` as a subset of `ℝ^(Option ι)` (the coordinate `none` is `ε`). -/
def boxDomain (V : Set (ι → ℝ)) (ε₀ : ℝ) : Set (Option ι → ℝ) :=
  {v | v ∘ some ∈ V ∧ v none ∈ Ioo 0 ε₀}

/-- Uncurrying `g : ℝ^ι → ℝ → X` to a function on `ℝ^(Option ι)`. -/
def uncurryOpt {X : Type*} (g : (ι → ℝ) → ℝ → X) : (Option ι → ℝ) → X :=
  fun v => g (v ∘ some) (v none)

/-!
## Proof

The proof follows the paper, with these adaptations.

* *A box on which `g` is analytic* (`Deriv.exists_box_analytic`): by `SAFacts.nash`, `g` is
  analytic off a semialgebraic set `Z` with empty interior.  Off a closed nowhere dense set of
  `ξ` the fibres `Z_ξ` are finite (`Deriv.exists_closed_finite_fibers`, from (S4)); applying
  `SAFacts.finite_fibers` to `Z ∪ {ε = ε₀}` gives a continuous positive lower bound for the
  fibres on a ball, hence a box avoiding `Z`.
* *Uniform convergence of a bounded family* (`Deriv.exists_ball_tendstoUniformlyOn`): the set
  `Λ` of limit values (closure of the graph over `ε = 0`) has empty interior by (S4)(b), hence
  finite fibres off a nowhere dense set; over a ball it is a union of graphs `λ₁ < ⋯ < λ_q`.
  The argument that `q = 1` uses the Baire category theorem
  (`Deriv.exists_ball_eventually_le_or_ge`) to find a ball and an `ε₁` on which the family stays
  on one side of `(λ₁ + λ₂)/2`; uniform convergence then follows by compactness.
* *One partial derivative* (`Deriv.exists_ball_partial`): this is applied to
  `θ ∘ ∂g/∂ξᵢ` with `θ(v) = v/(1+|v|)`; the limit is finite somewhere by the mean value
  theorem along a coordinate segment, and then on a ball where `θ⁻¹` is uniformly continuous.
* *All partial derivatives and identification of the limit* (`Deriv.exists_ball_C1_limit`):
  after treating the coordinates one after another, the derivatives `D_ξ g(·, ε)` converge
  uniformly in operator norm, and `hasFDerivAt_of_tendstoUniformlyOn` identifies the limit with
  the derivative of `g₀`.  (The continuity of `g₀` is not needed.)
* *Corollary 3.2* (`Deriv.cor_step`): induction on the order `j`, applying the strong form of
  the lemma to the coordinates `∂^α W_k` of the `j`-th derivative (which are semialgebraic by
  `IsSAFunOn₁.fderiv_apply`); the iterated derivatives are recovered from their values on tuples
  of basis vectors through a continuous left inverse of the evaluation map `Deriv.evalCLM`.
-/

namespace Deriv

set_option linter.unusedSectionVars false

section SAHelpers

variable {α β : Type}

theorem isSA_preimage_map {s : Set (β → ℝ)} (h : IsSA s) (σ : β → MvPolynomial α ℝ)
    (F : (α → ℝ) → (β → ℝ)) (hF : ∀ v b, F v b = MvPolynomial.eval v (σ b)) :
    IsSA {v | F v ∈ s} := by
  have hF' : F = fun v b => MvPolynomial.eval v (σ b) := by funext v b; exact hF v b
  subst hF'
  exact h.preimage_poly σ

theorem extendVal_none (a : ℝ) (v : α → ℝ) : extendVal a v none = a := rfl
theorem extendVal_some (a : ℝ) (v : α → ℝ) (i : α) : extendVal a v (some i) = v i := rfl

theorem extendVal_eta (v : Option α → ℝ) : extendVal (v none) (v ∘ some) = v := by
  funext o; cases o <;> rfl

theorem mem_boxDomain {U : Set (ι → ℝ)} {e ε : ℝ} {ξ : ι → ℝ} :
    extendVal ε ξ ∈ boxDomain U e ↔ ξ ∈ U ∧ ε ∈ Ioo 0 e := Iff.rfl

theorem uncurryOpt_extendVal {X : Type*} (g : (ι → ℝ) → ℝ → X) (ε : ℝ) (ξ : ι → ℝ) :
    uncurryOpt g (extendVal ε ξ) = g ξ ε := rfl

theorem isSA_boxDomain {U : Set (ι → ℝ)} (hU : IsSA U) (e : ℝ) : IsSA (boxDomain U e) := by
  have h1 := hU.preimage_comp (some : ι → Option ι)
  have h2 := isSA_pos (MvPolynomial.X (R := ℝ) (none : Option ι))
  have h3 := isSA_pos (MvPolynomial.C e - MvPolynomial.X (R := ℝ) (none : Option ι))
  convert h1.inter (h2.inter h3) using 1
  ext v
  simp [boxDomain, sub_pos]

theorem isOpen_boxDomain {U : Set (ι → ℝ)} (hU : IsOpen U) (e : ℝ) :
    IsOpen (boxDomain U e) := by
  have h1 : Continuous fun v : Option ι → ℝ => v ∘ some :=
    continuous_pi fun i => continuous_apply (some i)
  exact (hU.preimage h1).inter (isOpen_Ioo.preimage (continuous_apply none))

theorem boxDomain_mono {U U' : Set (ι → ℝ)} {e e' : ℝ} (hU : U' ⊆ U) (he : e' ≤ e) :
    boxDomain U' e' ⊆ boxDomain U e := fun _ hv =>
  ⟨hU hv.1, hv.2.1, lt_of_lt_of_le hv.2.2 he⟩

theorem isSA₁_fiber {A : Set (Option ι → ℝ)} (hA : IsSA A) (ξ : ι → ℝ) :
    IsSA₁ {y | extendVal y ξ ∈ A} :=
  isSA_preimage_map hA (fun o => o.elim (MvPolynomial.X ()) (fun i => MvPolynomial.C (ξ i)))
    (fun v => extendVal (v ()) ξ) (by intro v o; cases o <;> simp [extendVal])

theorem isSAFunOn₁_congr {D : Set (α → ℝ)} {f f' : (α → ℝ) → ℝ} (h : IsSAFunOn₁ D f)
    (heq : EqOn f f' D) : IsSAFunOn₁ D f' := by
  refine ⟨h.1, ?_⟩
  convert h.2 using 1
  ext v
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hv, hv'⟩; exact ⟨hv, by rw [heq hv]; exact hv'⟩
  · rintro ⟨hv, hv'⟩; exact ⟨hv, by rw [← heq hv]; exact hv'⟩

theorem isSAFunOn₁_mono {D D' : Set (α → ℝ)} {f : (α → ℝ) → ℝ} (h : IsSAFunOn₁ D f)
    (hD' : IsSA D') (hsub : D' ⊆ D) : IsSAFunOn₁ D' f :=
  IsSAFunOn.mono h hD' hsub

/-- A slice `ε ↦ h ξ ε` of a semialgebraic family. -/
theorem isSAFunOn₁_slice {U : Set (ι → ℝ)} {e : ℝ} {h : (ι → ℝ) → ℝ → ℝ}
    (hh : IsSAFunOn₁ (boxDomain U e) (uncurryOpt h)) {ξ : ι → ℝ} (hξ : ξ ∈ U) :
    IsSAFun₁₁ (Ioo 0 e) (h ξ) := by
  refine ⟨?_, ?_⟩
  · have hset : {y | extendVal y ξ ∈ boxDomain U e} = Ioo 0 e := by
      ext y; simp only [Set.mem_ofPred_eq, mem_boxDomain]
      exact ⟨fun h => h.2, fun h => ⟨hξ, h⟩⟩
    have := isSA₁_fiber hh.1 ξ
    rw [hset] at this
    exact this
  · have := isSA_preimage_map hh.2
      (Sum.elim (fun o => o.elim (MvPolynomial.X (Sum.inl ())) (fun i => MvPolynomial.C (ξ i)))
        (fun _ => MvPolynomial.X (Sum.inr ())))
      (fun w => Sum.elim (extendVal (w (Sum.inl ())) ξ) (fun _ => w (Sum.inr ())))
      (by intro v b; rcases b with (o | u) <;> [cases o; skip] <;> simp [extendVal])
    convert this using 1
    ext w
    simp only [Set.mem_ofPred_eq]
    have e1 : (Sum.elim (extendVal (w (Sum.inl ())) ξ) (fun _ => w (Sum.inr ())) :
        Option ι ⊕ Unit → ℝ) ∘ Sum.inl = extendVal (w (Sum.inl ())) ξ := rfl
    have e2 : (Sum.elim (extendVal (w (Sum.inl ())) ξ) (fun _ => w (Sum.inr ())) :
        Option ι ⊕ Unit → ℝ) ∘ Sum.inr = fun _ => w (Sum.inr ()) := rfl
    rw [e1, e2, mem_boxDomain, uncurryOpt_extendVal]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨hξ, h1⟩, ?_⟩
      funext u
      exact congrFun h2 ()
    · rintro ⟨h1, h2⟩
      refine ⟨h1.2, ?_⟩
      funext u
      cases u
      exact congrFun h2 ()

/-- `θ(v) = v/(1+|v|)`, a semialgebraic homeomorphism `ℝ → (-1,1)`. -/
def theta (v : ℝ) : ℝ := v / (1 + |v|)

/-- The inverse of `θ` on `(-1, 1)`. -/
def thetaInv (w : ℝ) : ℝ := w / (1 - |w|)

theorem theta_pos_denom (v : ℝ) : 0 < 1 + |v| := by positivity

theorem abs_theta (v : ℝ) : |theta v| = |v| / (1 + |v|) := by
  rw [theta, abs_div, abs_of_pos (theta_pos_denom v)]

theorem abs_theta_lt_one (v : ℝ) : |theta v| < 1 := by
  rw [abs_theta, div_lt_one (theta_pos_denom v)]; linarith

theorem thetaInv_theta (v : ℝ) : thetaInv (theta v) = v := by
  have h1 := theta_pos_denom v
  have h2 : 1 - |theta v| = 1 / (1 + |v|) := by
    rw [abs_theta]; field_simp; ring
  rw [thetaInv, h2, theta]; field_simp

theorem theta_strictMono : StrictMono theta := by
  intro a b hab
  unfold theta
  rw [div_lt_div_iff₀ (theta_pos_denom a) (theta_pos_denom b)]
  rcases le_or_gt 0 a with ha | ha <;> rcases le_or_gt 0 b with hb | hb
  · rw [abs_of_nonneg ha, abs_of_nonneg hb]; nlinarith
  · linarith
  · rw [abs_of_neg ha, abs_of_nonneg hb]; nlinarith
  · rw [abs_of_neg ha, abs_of_neg hb]; nlinarith

theorem continuous_theta : Continuous theta :=
  continuous_id.div (continuous_const.add continuous_abs) fun v => (theta_pos_denom v).ne'

theorem continuousOn_thetaInv : ContinuousOn thetaInv (Ioo (-1) 1) := by
  refine continuousOn_id.div (continuousOn_const.sub continuous_abs.continuousOn) ?_
  intro w hw
  exact (sub_pos.2 (abs_lt.2 hw)).ne'

theorem isSAFunOn_theta :
    IsSAFunOn (univ : Set (Unit → ℝ)) (fun u (_ : Unit) => theta (u ())) := by
  refine ⟨isSA_univ, ?_⟩
  open MvPolynomial in
  have h1 := (isSA_nonneg (X (R := ℝ) (Sum.inl () : Unit ⊕ Unit))).inter
    (isSA_zero (X (Sum.inr ()) * (1 + X (Sum.inl ())) - X (R := ℝ) (Sum.inl () : Unit ⊕ Unit)))
  open MvPolynomial in
  have h2 := (isSA_pos (- X (R := ℝ) (Sum.inl () : Unit ⊕ Unit))).inter
    (isSA_zero (X (Sum.inr ()) * (1 - X (Sum.inl ())) - X (R := ℝ) (Sum.inl () : Unit ⊕ Unit)))
  convert h1.union h2 using 1
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_univ, true_and, Set.mem_union, Set.mem_inter_iff,
    MvPolynomial.eval_X, map_sub, map_mul, map_add, map_one, map_neg]
  have hfun : ((fun _ : Unit => theta ((w ∘ Sum.inl) ())) = w ∘ Sum.inr) ↔
      theta (w (Sum.inl ())) = w (Sum.inr ()) := by
    constructor
    · intro h; exact congrFun h ()
    · intro h; funext u; exact h
  rw [hfun]
  set a := w (Sum.inl ())
  set b := w (Sum.inr ())
  unfold theta
  rw [div_eq_iff (theta_pos_denom a).ne']
  rcases le_or_gt 0 a with ha | ha
  · rw [abs_of_nonneg ha]
    constructor
    · intro h; left; exact ⟨ha, by linarith⟩
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · linarith
      · linarith
  · rw [abs_of_neg ha]
    constructor
    · intro h; right; exact ⟨by linarith, by linarith⟩
    · rintro (⟨h, -⟩ | ⟨-, h⟩)
      · linarith
      · linarith

theorem isSAFunOn₁_theta {D : Set (α → ℝ)} {f : (α → ℝ) → ℝ} (h : IsSAFunOn₁ D f) :
    IsSAFunOn₁ D (fun x => Deriv.theta (f x)) :=
  IsSAFunOn.comp h isSAFunOn_theta (fun _ _ => mem_univ _)

end SAHelpers

section DimHelpers

variable {α β : Type}

theorem DimGE.of_comp {A : Set (α → ℝ)} {B : Set (β → ℝ)} {d : ℕ} (emb : α → β)
    (hemb : Function.Injective emb) (hAB : ∀ u ∈ A, ∃ w ∈ B, w ∘ emb = u) (h : DimGE A d) :
    DimGE B d := by
  obtain ⟨σ, hσ, hne⟩ := h
  refine ⟨emb ∘ σ, hemb.comp hσ, hne.mono (interior_mono ?_)⟩
  rintro _ ⟨u, hu, rfl⟩
  obtain ⟨w, hw, rfl⟩ := hAB u hu
  exact ⟨w, hw, rfl⟩

/-- Off a closed nowhere dense set, the fibers of a semialgebraic set with empty interior in
`ℝ^(Option ι)` are finite ((S4)(a),(c)). -/
theorem exists_closed_finite_fibers (hS : SAFacts) {A : Set (Option ι → ℝ)} (hA : IsSA A)
    (hint : interior A = ∅) :
    ∃ T : Set (ι → ℝ), IsClosed T ∧ interior T = ∅ ∧
      ∀ ξ ∉ T, {y : ℝ | extendVal y ξ ∈ A}.Finite := by
  let f : Option ι → Unit ⊕ ι := fun o => o.elim (Sum.inl ()) Sum.inr
  let A' : Set (Unit ⊕ ι → ℝ) := {w | w ∘ f ∈ A}
  have hA' : IsSA A' := hA.preimage_comp f
  have hfib : ∀ ξ, fiberOver A' ξ = {v : Unit → ℝ | v () ∈ {y | extendVal y ξ ∈ A}} := by
    intro ξ; ext v
    simp only [fiberOver, A', Set.mem_ofPred_eq]
    have : Sum.elim v ξ ∘ f = extendVal (v ()) ξ := by funext o; cases o <;> rfl
    rw [this]
  let T₀ := {c : ι → ℝ | DimGE (fiberOver A' c) 1}
  have hT₀ : IsSA T₀ := isSA_dimGE_fiber hA' 1
  have hT₀dim : DimLT T₀ (Fintype.card ι) := by
    intro hge
    have h1 := hS.fiber_dim_le A' 1 (Fintype.card ι) hA' hge
    have h2 : DimGE A (Fintype.card (Option ι)) := by
      rw [Fintype.card_option, add_comm]
      refine DimGE.of_comp (Sum.elim (fun _ => none) some) ?_ ?_ h1
      · intro a b hab
        rcases a with (a | a) <;> rcases b with (b | b) <;> simp_all
      · intro u hu
        refine ⟨u ∘ f, hu, ?_⟩
        funext x; rcases x with (a | a) <;> rfl
    rw [dimGE_card_iff, hint] at h2
    exact Set.not_nonempty_empty h2
  refine ⟨closure T₀, isClosed_closure, ?_, ?_⟩
  · exact (dimLT_card_iff _).1 (hS.closure_dimLT T₀ _ hT₀ hT₀dim)
  · intro ξ hξ
    have hξ' : ξ ∉ T₀ := fun h => hξ (subset_closure h)
    have hsa : IsSA (fiberOver A' ξ) := by rw [hfib]; exact isSA₁_fiber hA ξ
    have hfin := (dimLT_one_iff_finite hS hsa).1 hξ'
    rw [hfib] at hfin
    have : {y | extendVal y ξ ∈ A} =
        (fun v : Unit → ℝ => v ()) '' {v | v () ∈ {y | extendVal y ξ ∈ A}} := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_image]
      exact ⟨fun h => ⟨fun _ => y, h, rfl⟩, by rintro ⟨v, hv, rfl⟩; exact hv⟩
    rw [this]; exact hfin.image _

/-- Iterating a shrinking step over a finite type. -/
theorem iterate_boxes {γ : Type*} [Fintype γ] (P : γ → Set (ι → ℝ) → ℝ → Prop)
    (x₀ : ι → ℝ) (r₀ e₀ : ℝ)
    (hmono : ∀ c s t e e', P c s e → t ⊆ s → 0 < e' → e' ≤ e → P c t e')
    (hstep : ∀ c x r e, 0 < r → Metric.ball x r ⊆ Metric.ball x₀ r₀ → 0 < e → e ≤ e₀ →
      ∃ x' r' e', 0 < r' ∧ Metric.ball x' r' ⊆ Metric.ball x r ∧ 0 < e' ∧ e' ≤ e ∧
        P c (Metric.ball x' r') e')
    (hr₀ : 0 < r₀) (he₀ : 0 < e₀) :
    ∃ x r e, 0 < r ∧ Metric.ball x r ⊆ Metric.ball x₀ r₀ ∧ 0 < e ∧ e ≤ e₀ ∧
      ∀ c, P c (Metric.ball x r) e := by
  classical
  suffices ∀ s : Finset γ, ∃ x r e, 0 < r ∧ Metric.ball x r ⊆ Metric.ball x₀ r₀ ∧ 0 < e ∧
      e ≤ e₀ ∧ ∀ c ∈ s, P c (Metric.ball x r) e by
    obtain ⟨x, r, e, hr, hb, he, hle, hP⟩ := this Finset.univ
    exact ⟨x, r, e, hr, hb, he, hle, fun c => hP c (Finset.mem_univ c)⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨x₀, r₀, e₀, hr₀, subset_rfl, he₀, le_rfl, by simp⟩
  | insert a s ha ih =>
    obtain ⟨x, r, e, hr, hb, he, hle, hP⟩ := ih
    obtain ⟨x', r', e', hr', hb', he', hle', hP'⟩ := hstep a x r e hr hb he hle
    refine ⟨x', r', e', hr', hb'.trans hb, he', hle'.trans hle, ?_⟩
    intro c hc
    rcases Finset.mem_insert.1 hc with rfl | hc
    · exact hP'
    · exact hmono c _ _ _ _ (hP c hc) hb' he' hle'

end DimHelpers

/-! ### Step 1: a box on which the family is analytic -/

theorem nonempty_diff_of_interior_eq_empty {U T : Set (ι → ℝ)} (hU : IsOpen U)
    (hUne : U.Nonempty) (hTint : interior T = ∅) : (U \ T).Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at hne
  have : U ⊆ interior T := interior_maximal hne hU
  rw [hTint] at this
  obtain ⟨x, hx⟩ := hUne
  exact this hx

/-- **Step 1 of Lemma 3.1.** A semialgebraic family is analytic on a box. -/
theorem exists_box_analytic (hS : SAFacts) {U : Set (ι → ℝ)} (hU : IsOpen U)
    (hUne : U.Nonempty) {e : ℝ} (he : 0 < e) {h : (ι → ℝ) → ℝ → ℝ}
    (hh : IsSAFunOn₁ (boxDomain U e) (uncurryOpt h)) :
    ∃ (x : ι → ℝ) (r e' : ℝ), 0 < r ∧ Metric.ball x r ⊆ U ∧ 0 < e' ∧ e' ≤ e ∧
      ∀ v ∈ boxDomain (Metric.ball x r) e', AnalyticAt ℝ (uncurryOpt h) v := by
  obtain ⟨Z, hZ, hZO, hZdim, hZan⟩ :=
    hS.nash (boxDomain U e) (uncurryOpt h) (isOpen_boxDomain hU e) hh
  have hZint : interior Z = ∅ := (dimLT_card_iff Z).1 hZdim
  obtain ⟨T, hTcl, hTint, hTfin⟩ := exists_closed_finite_fibers hS hZ hZint
  have hUT : (U \ T).Nonempty := nonempty_diff_of_interior_eq_empty hU hUne hTint
  have hUTo : IsOpen (U \ T) := hU.sdiff hTcl
  let E : Set (Option ι → ℝ) := Z ∪ {v | v none = e}
  have hE : IsSA E := by
    refine hZ.union ?_
    have := isSA_zero (MvPolynomial.X (R := ℝ) (none : Option ι) - MvPolynomial.C e)
    convert this using 1
    ext v; simp [sub_eq_zero]
  have hEfib : ∀ ξ, {y : ℝ | extendVal y ξ ∈ E} = {y | extendVal y ξ ∈ Z} ∪ {e} := by
    intro ξ; ext y; simp [E, extendVal_none, or_comm]
  obtain ⟨x₀, r, hr, hball, q, lam, hq, hlam, hmono, hrange⟩ :=
    hS.finite_fibers E (U \ T) hE hUTo hUT (by
      intro ξ hξ
      rw [hEfib]
      exact ⟨(hTfin ξ hξ.2).union (Set.finite_singleton e), ⟨e, Or.inr rfl⟩⟩)
  let l₀ := lam ⟨0, hq⟩
  have hl₀mem : ∀ ξ ∈ Metric.ball x₀ r, extendVal (l₀ ξ) ξ ∈ E := by
    intro ξ hξ
    have : l₀ ξ ∈ range fun i => lam i ξ := ⟨_, rfl⟩
    rw [← hrange ξ hξ] at this
    exact this
  have hl₀pos : ∀ ξ ∈ Metric.ball x₀ r, 0 < l₀ ξ := by
    intro ξ hξ
    rcases hl₀mem ξ hξ with hZ' | he'
    · exact (hZO hZ').2.1
    · simp only [Set.mem_ofPred_eq, extendVal_none] at he'; rw [he']; exact he
  have hl₀min : ∀ ξ ∈ Metric.ball x₀ r, ∀ y, extendVal y ξ ∈ E → l₀ ξ ≤ y := by
    intro ξ hξ y hy
    have : y ∈ {y : ℝ | extendVal y ξ ∈ E} := hy
    rw [hrange ξ hξ] at this
    obtain ⟨i, rfl⟩ := this
    exact (hmono ξ hξ).monotone (show (⟨0, hq⟩ : Fin q) ≤ i from
      Fin.le_iff_val_le_val.2 (Nat.zero_le _))
  have hcont : ContinuousAt l₀ x₀ :=
    ((hlam ⟨0, hq⟩).2).continuousAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))
  set c := l₀ x₀ / 2 with hc
  have hc0 : 0 < c := by have := hl₀pos x₀ (Metric.mem_ball_self hr); positivity
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuousAt_iff.1 hcont c hc0
  refine ⟨x₀, min δ r, min c e, lt_min hδ hr, ?_, lt_min hc0 he, min_le_right _ _, ?_⟩
  · exact (Metric.ball_subset_ball (min_le_right _ _)).trans (hball.trans sdiff_subset)
  · intro v hv
    have hξ : v ∘ some ∈ Metric.ball x₀ r := Metric.ball_subset_ball (min_le_right _ _) hv.1
    have hξδ : dist (v ∘ some) x₀ < δ := lt_of_lt_of_le hv.1 (min_le_left _ _)
    have hlt : c < l₀ (v ∘ some) := by
      have := hδc hξδ
      rw [Real.dist_eq, abs_lt] at this
      linarith
    have hvO : v ∈ boxDomain U e :=
      ⟨(hball hξ).1, hv.2.1, lt_of_lt_of_le hv.2.2 (min_le_right _ _)⟩
    refine hZan v ⟨hvO, fun hvZ => ?_⟩
    have hmem : extendVal (v none) (v ∘ some) ∈ E := by rw [extendVal_eta]; exact Or.inl hvZ
    have h1 := hl₀min _ hξ _ hmem
    have h2 : v none < c := lt_of_lt_of_le hv.2.2 (min_le_left _ _)
    linarith

/-! ### Uniform convergence of bounded semialgebraic families -/

/-- The graph of `F` over the box `U × (0, e)`, as a subset of `ℝ^(Option ι ⊕ Unit)`. -/
def graphSet (U : Set (ι → ℝ)) (e : ℝ) (F : (ι → ℝ) → ℝ → ℝ) : Set (Option ι ⊕ Unit → ℝ) :=
  {v | v ∘ Sum.inl ∈ boxDomain U e ∧
    (fun x (_ : Unit) => uncurryOpt F x) (v ∘ Sum.inl) = v ∘ Sum.inr}

/-- The point `(ξ, ε, y)` of `ℝ^(Option ι ⊕ Unit)`. -/
def gpt (ε : ℝ) (ξ : ι → ℝ) (y : ℝ) : Option ι ⊕ Unit → ℝ :=
  Sum.elim (extendVal ε ξ) (fun _ => y)

theorem mem_graphSet_iff {U : Set (ι → ℝ)} {e : ℝ} {F : (ι → ℝ) → ℝ → ℝ}
    {w : Option ι ⊕ Unit → ℝ} :
    w ∈ graphSet U e F ↔ (fun i => w (Sum.inl (some i))) ∈ U ∧ w (Sum.inl none) ∈ Ioo 0 e ∧
      w (Sum.inr ()) = F (fun i => w (Sum.inl (some i))) (w (Sum.inl none)) := by
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, (congrFun h3 ()).symm⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, h2⟩, ?_⟩
    funext u; cases u; exact h3.symm

theorem gpt_mem_graphSet {U : Set (ι → ℝ)} {e : ℝ} {F : (ι → ℝ) → ℝ → ℝ} {ξ : ι → ℝ} {ε : ℝ}
    (hξ : ξ ∈ U) (hε : ε ∈ Ioo 0 e) : gpt ε ξ (F ξ ε) ∈ graphSet U e F :=
  mem_graphSet_iff.2 ⟨hξ, hε, rfl⟩

theorem continuous_gpt : Continuous (fun p : ℝ × (ι → ℝ) × ℝ => gpt p.1 p.2.1 p.2.2) := by
  refine continuous_pi fun b => ?_
  rcases b with (o | u)
  · cases o with
    | none => exact continuous_fst
    | some i => exact (continuous_apply i).comp (continuous_fst.comp continuous_snd)
  · exact continuous_snd.comp continuous_snd

theorem tendsto_gpt {X : Type*} {l : Filter X} {a : X → ℝ} {b : X → ι → ℝ} {c : X → ℝ}
    {a₀ : ℝ} {b₀ : ι → ℝ} {c₀ : ℝ} (ha : Tendsto a l (𝓝 a₀)) (hb : Tendsto b l (𝓝 b₀))
    (hc : Tendsto c l (𝓝 c₀)) :
    Tendsto (fun t => gpt (a t) (b t) (c t)) l (𝓝 (gpt a₀ b₀ c₀)) :=
  (continuous_gpt.tendsto (a₀, b₀, c₀)).comp (ha.prodMk_nhds (hb.prodMk_nhds hc))

/-- Points of the closure of the graph over `ε = 0` satisfy every closed condition that holds
on the graph near them. -/
theorem closure_graphSet_le {U : Set (ι → ℝ)} {e : ℝ} {F : (ι → ℝ) → ℝ → ℝ} {y : ι → ℝ}
    {v : ℝ} (hcl : gpt 0 y v ∈ closure (graphSet U e F)) {S : Set (ι → ℝ)} (hS : S ∈ 𝓝 y)
    {δ : ℝ} (hδ : 0 < δ) {ψ : (ι → ℝ) → ℝ → ℝ}
    (hψ : ContinuousAt (fun p : (ι → ℝ) × ℝ => ψ p.1 p.2) (y, v))
    (hle : ∀ ξ ∈ S, ∀ ε ∈ Ioo 0 δ, ξ ∈ U → ε ∈ Ioo 0 e → ψ ξ (F ξ ε) ≤ 0) : ψ y v ≤ 0 := by
  let P : (Option ι ⊕ Unit → ℝ) → (ι → ℝ) × ℝ :=
    fun w => (fun i => w (Sum.inl (some i)), w (Sum.inr ()))
  have hP1 : Continuous fun w : Option ι ⊕ Unit → ℝ => fun i => w (Sum.inl (some i)) :=
    continuous_pi fun i => continuous_apply _
  have hP : Continuous P := hP1.prodMk (continuous_apply _)
  have hne : (𝓝[graphSet U e F] (gpt 0 y v)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
  have htend : Tendsto (fun w => ψ (P w).1 (P w).2) (𝓝[graphSet U e F] (gpt 0 y v))
      (𝓝 (ψ y v)) := by
    have := hψ.tendsto.comp (hP.tendsto (gpt 0 y v))
    exact this.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto htend ?_
  have h1 : {w : Option ι ⊕ Unit → ℝ | (fun i => w (Sum.inl (some i))) ∈ S} ∈
      𝓝 (gpt 0 y v) := hP1.continuousAt.preimage_mem_nhds hS
  have h2 : {w : Option ι ⊕ Unit → ℝ | w (Sum.inl none) < δ} ∈ 𝓝 (gpt 0 y v) :=
    ((continuous_apply (Sum.inl none : Option ι ⊕ Unit)).continuousAt
      (x := gpt 0 y v)).preimage_mem_nhds (Iio_mem_nhds hδ)
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds h1,
    mem_nhdsWithin_of_mem_nhds h2] with w hw hw1 hw2
  obtain ⟨hU, hε, heq⟩ := mem_graphSet_iff.1 hw
  simp only [P]
  rw [heq]
  exact hle _ hw1 _ ⟨hε.1, hw2⟩ hU hε

/-- Baire category: if `F(ξ, ε)` stays eventually on one side of `β(ξ)` for every `ξ`, then on
some ball it does so uniformly. -/
theorem exists_ball_eventually_le_or_ge {x : ι → ℝ} {r : ℝ} (hr : 0 < r) {e : ℝ} (he : 0 < e)
    {F : (ι → ℝ) → ℝ → ℝ} {β : (ι → ℝ) → ℝ} (hβ : ContinuousOn β (Metric.ball x r))
    (hFc : ∀ ε ∈ Ioo 0 e, ContinuousOn (fun ξ => F ξ ε) (Metric.ball x r))
    (hconv : ∀ ξ ∈ Metric.ball x r,
      (∀ᶠ ε in 𝓝[>] 0, F ξ ε < β ξ) ∨ (∀ᶠ ε in 𝓝[>] 0, β ξ < F ξ ε)) :
    ∃ y δ ε₁, 0 < δ ∧ Metric.ball y δ ⊆ Metric.ball x r ∧ 0 < ε₁ ∧
      ((∀ ξ ∈ Metric.ball y δ, ∀ ε ∈ Ioo 0 ε₁, F ξ ε ≤ β ξ) ∨
       (∀ ξ ∈ Metric.ball y δ, ∀ ε ∈ Ioo 0 ε₁, β ξ ≤ F ξ ε)) := by
  set K := Metric.closedBall x (r / 2) with hK
  have hKsub : K ⊆ Metric.ball x r := Metric.closedBall_subset_ball (by linarith)
  let t : ℕ → ℝ := fun n => min e (1 / ((n : ℝ) + 1))
  have ht : ∀ n, 0 < t n := fun n => lt_min he (by positivity)
  have hte : ∀ n, ∀ ε ∈ Ioo 0 (t n), ε ∈ Ioo 0 e :=
    fun n ε hε => ⟨hε.1, lt_of_lt_of_le hε.2 (min_le_left _ _)⟩
  let C : ℕ → Set (ι → ℝ) := fun n =>
    K ∩ ⋂ ε ∈ Ioo 0 (t n), K ∩ (fun ξ => F ξ ε - β ξ) ⁻¹' Iic 0
  let C' : ℕ → Set (ι → ℝ) := fun n =>
    K ∩ ⋂ ε ∈ Ioo 0 (t n), K ∩ (fun ξ => β ξ - F ξ ε) ⁻¹' Iic 0
  have hC : ∀ n, IsClosed (C n) := fun n =>
    Metric.isClosed_closedBall.inter (isClosed_biInter fun ε hε =>
      (((hFc ε (hte n ε hε)).sub hβ).mono hKsub).preimage_isClosed_of_isClosed
        Metric.isClosed_closedBall isClosed_Iic)
  have hC' : ∀ n, IsClosed (C' n) := fun n =>
    Metric.isClosed_closedBall.inter (isClosed_biInter fun ε hε =>
      ((hβ.sub (hFc ε (hte n ε hε))).mono hKsub).preimage_isClosed_of_isClosed
        Metric.isClosed_closedBall isClosed_Iic)
  let f : Option (ℕ ⊕ ℕ) → Set (ι → ℝ) := fun i =>
    match i with
    | none => (Metric.ball x (r / 2))ᶜ
    | some (Sum.inl n) => C n
    | some (Sum.inr n) => C' n
  have hf : ∀ i, IsClosed (f i) := by
    intro i
    rcases i with _ | (n | n)
    · exact Metric.isOpen_ball.isClosed_compl
    · exact hC n
    · exact hC' n
  have hcov : ⋃ i, f i = univ := by
    refine Set.eq_univ_of_forall fun ξ => ?_
    rw [Set.mem_iUnion]
    by_cases hξ : ξ ∈ Metric.ball x (r / 2)
    · have hξK : ξ ∈ K := Metric.ball_subset_closedBall hξ
      rcases hconv ξ (hKsub hξK) with hev | hev
      · obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0:ℝ) < u from hu)
        refine ⟨some (Sum.inl n), hξK, Set.mem_iInter₂.2 fun ε hε => ⟨hξK, ?_⟩⟩
        have : F ξ ε < β ξ :=
          hsub ⟨hε.1, lt_trans (lt_of_lt_of_le hε.2 (min_le_right _ _)) hn⟩
        show F ξ ε - β ξ ≤ 0
        linarith
      · obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0:ℝ) < u from hu)
        refine ⟨some (Sum.inr n), hξK, Set.mem_iInter₂.2 fun ε hε => ⟨hξK, ?_⟩⟩
        have : β ξ < F ξ ε :=
          hsub ⟨hε.1, lt_trans (lt_of_lt_of_le hε.2 (min_le_right _ _)) hn⟩
        show β ξ - F ξ ε ≤ 0
        linarith
    · exact ⟨none, hξ⟩
  have hd := dense_iUnion_interior_of_closed hf hcov
  obtain ⟨z, hz, hxz⟩ := Metric.mem_closure_iff.1 (hd x) (r / 2) (by linarith)
  have hzb : z ∈ Metric.ball x (r / 2) := by rw [Metric.mem_ball, dist_comm]; exact hxz
  rw [Set.mem_iUnion] at hz
  obtain ⟨i, hi⟩ := hz
  obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.1 isOpen_interior z hi
  rcases i with _ | (n | n)
  · exact absurd hzb (interior_subset hi)
  · refine ⟨z, δ, t n, hδ, fun ξ hξ => hKsub (interior_subset (hδsub hξ)).1, ht n,
      Or.inl fun ξ hξ ε hε => ?_⟩
    have h1 := (Set.mem_iInter₂.1 (interior_subset (hδsub hξ)).2 ε hε).2
    have h2 : F ξ ε - β ξ ≤ 0 := h1
    linarith
  · refine ⟨z, δ, t n, hδ, fun ξ hξ => hKsub (interior_subset (hδsub hξ)).1, ht n,
      Or.inr fun ξ hξ ε hε => ?_⟩
    have h1 := (Set.mem_iInter₂.1 (interior_subset (hδsub hξ)).2 ε hε).2
    have h2 : β ξ - F ξ ε ≤ 0 := h1
    linarith

/-- If the closure of the graph over `ε = 0` is the graph of a continuous function `ℓ` over a
compact set `K`, then `F(·, ε) → ℓ` uniformly on `K`. -/
theorem tendstoUniformlyOn_of_closure_graph {U : Set (ι → ℝ)} {e : ℝ} (he : 0 < e)
    {F : (ι → ℝ) → ℝ → ℝ} {K : Set (ι → ℝ)} (hK : IsCompact K) (hKU : K ⊆ U)
    {ℓ : (ι → ℝ) → ℝ} (hℓ : ContinuousOn ℓ K)
    (hb : ∀ ξ ∈ U, ∀ ε ∈ Ioo 0 e, F ξ ε ∈ Icc (-1:ℝ) 1)
    (huniq : ∀ ξ ∈ K, ∀ v, gpt 0 ξ v ∈ closure (graphSet U e F) → v = ℓ ξ) :
    TendstoUniformlyOn (fun ε ξ => F ξ ε) ℓ (𝓝[>] 0) K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  by_contra hcon
  have hfreq : ∀ n : ℕ, ∃ ε ∈ Ioo 0 (min e (1 / ((n : ℝ) + 1))), ∃ ξ ∈ K,
      η ≤ dist (ℓ ξ) (F ξ ε) := by
    intro n
    rw [Filter.not_eventually] at hcon
    have hmem : Ioo 0 (min e (1 / ((n : ℝ) + 1))) ∈ 𝓝[>] (0:ℝ) :=
      Ioo_mem_nhdsGT (lt_min he (by positivity))
    obtain ⟨ε, hε1, hε2⟩ := (hcon.and_eventually hmem).exists
    push Not at hε1
    obtain ⟨ξ, hξ, hd⟩ := hε1
    exact ⟨ε, hε2, ξ, hξ, hd⟩
  choose εs hεs ξs hξs hd using hfreq
  have hεe : ∀ n, εs n ∈ Ioo 0 e := fun n =>
    ⟨(hεs n).1, lt_of_lt_of_le (hεs n).2 (min_le_left _ _)⟩
  have hmemc : ∀ n, (ξs n, F (ξs n) (εs n)) ∈ K ×ˢ Icc (-1:ℝ) 1 :=
    fun n => ⟨hξs n, hb _ (hKU (hξs n)) _ (hεe n)⟩
  obtain ⟨⟨ξ', v'⟩, ⟨hξ'K, -⟩, φ, hφ, hlim⟩ := (hK.prod isCompact_Icc).tendsto_subseq hmemc
  have hε0 : Tendsto (fun n => εs (φ n)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat (fun n => (hεs (φ n)).1.le) (fun n => ?_)
    have h1 := (hεs (φ n)).2
    have h2 : (n : ℝ) ≤ φ n := by exact_mod_cast hφ.id_le n
    have h3 : 1 / ((φ n : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    exact (lt_of_lt_of_le h1 ((min_le_right _ _).trans h3)).le
  have hξlim : Tendsto (fun n => ξs (φ n)) atTop (𝓝 ξ') :=
    ((continuous_fst.tendsto _).comp hlim : _)
  have hvlim : Tendsto (fun n => F (ξs (φ n)) (εs (φ n))) atTop (𝓝 v') :=
    ((continuous_snd.tendsto _).comp hlim : _)
  have hcl : gpt 0 ξ' v' ∈ closure (graphSet U e F) :=
    mem_closure_of_tendsto (tendsto_gpt hε0 hξlim hvlim)
      (Eventually.of_forall fun n => gpt_mem_graphSet (hKU (hξs (φ n))) (hεe (φ n)))
  have hv' := huniq ξ' hξ'K v' hcl
  have hℓlim : Tendsto (fun n => ℓ (ξs (φ n))) atTop (𝓝 (ℓ ξ')) :=
    (hℓ ξ' hξ'K).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hξlim, Eventually.of_forall fun n => hξs _⟩)
  have hge : η ≤ dist (ℓ ξ') v' :=
    ge_of_tendsto (hℓlim.dist hvlim) (Eventually.of_forall fun n => hd (φ n))
  rw [hv', dist_self] at hge
  linarith

/-- **Uniform convergence of bounded semialgebraic families** (the core of Lemma 3.1): a bounded
semialgebraic family `F(ξ, ε)`, continuous on the box, converges uniformly as `ε → 0⁺` to a
continuous function on some ball. -/
theorem exists_ball_tendstoUniformlyOn (hS : SAFacts) {U : Set (ι → ℝ)} (hU : IsOpen U)
    (hUne : U.Nonempty) {e : ℝ} (he : 0 < e) {F : (ι → ℝ) → ℝ → ℝ}
    (hF : IsSAFunOn₁ (boxDomain U e) (uncurryOpt F))
    (hFc : ContinuousOn (uncurryOpt F) (boxDomain U e))
    (hFb : ∀ ξ ∈ U, ∀ ε ∈ Ioo 0 e, F ξ ε ∈ Icc (-1:ℝ) 1) :
    ∃ (x : ι → ℝ) (r : ℝ), 0 < r ∧ Metric.ball x r ⊆ U ∧ ∃ ℓ : (ι → ℝ) → ℝ,
      ContinuousOn ℓ (Metric.ball x r) ∧
      TendstoUniformlyOn (fun ε ξ => F ξ ε) ℓ (𝓝[>] 0) (Metric.ball x r) := by
  set Γ := graphSet U e F with hΓdef
  have hΓ : IsSA Γ := hF.2
  set Λ : Set (Option ι → ℝ) := {u | gpt 0 (u ∘ some) (u none) ∈ closure Γ} with hΛdef
  have hΛ : IsSA Λ :=
    isSA_preimage_map (IsSA.closure hΓ)
      (Sum.elim (fun o => o.elim 0 (fun i => MvPolynomial.X (some i)))
        (fun _ => MvPolynomial.X none))
      (fun u => gpt 0 (u ∘ some) (u none))
      (by intro v b; rcases b with ((_ | i) | u) <;> simp [gpt, extendVal])
  -- the graph has empty interior
  have hΓint : interior Γ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro w hw
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 isOpen_interior w hw
    let w' := Function.update w (Sum.inr ()) (w (Sum.inr ()) + δ / 2)
    have hw' : w' ∈ Γ := interior_subset (hball (by
      rw [Metric.mem_ball, dist_pi_lt_iff hδ]
      intro b
      by_cases hb : b = Sum.inr ()
      · subst hb
        simp only [w', Function.update_self, Real.dist_eq, add_sub_cancel_left,
          abs_of_pos (half_pos hδ)]
        linarith
      · simp only [w', Function.update_of_ne hb, dist_self]
        exact hδ))
    have hw0 : w ∈ Γ := interior_subset hw
    obtain ⟨-, -, h1⟩ := mem_graphSet_iff.1 hw0
    obtain ⟨-, -, h2⟩ := mem_graphSet_iff.1 hw'
    simp only [w', Function.update_self, ne_eq, reduceCtorEq, not_false_eq_true,
      Function.update_of_ne] at h2
    linarith
  -- the set of limit values has empty interior ((S4)(b))
  have hΛint : interior Λ = ∅ := by
    by_contra hne
    have h1 : DimGE Λ (Fintype.card (Option ι)) :=
      (dimGE_card_iff Λ).2 (Set.nonempty_iff_ne_empty.2 hne)
    have h2 : DimGE (closure Γ \ Γ) (Fintype.card (Option ι)) := by
      refine DimGE.of_comp (fun o => o.elim (Sum.inr ()) (fun i => Sum.inl (some i))) ?_ ?_ h1
      · intro a b hab
        cases a <;> cases b <;> simp_all
      · intro u hu
        refine ⟨gpt 0 (u ∘ some) (u none), ⟨hu, fun hmem => ?_⟩, ?_⟩
        · obtain ⟨-, hε, -⟩ := mem_graphSet_iff.1 hmem
          exact lt_irrefl _ hε.1
        · funext o; cases o <;> rfl
    have h3 := hS.frontier_dim Γ _ hΓ h2
    have h4 : DimGE Γ (Fintype.card (Option ι ⊕ Unit)) := by
      rwa [Fintype.card_sum, Fintype.card_unit]
    rw [dimGE_card_iff, hΓint] at h4
    exact Set.not_nonempty_empty h4
  obtain ⟨T, hTcl, hTint, hTfin⟩ := exists_closed_finite_fibers hS hΛ hΛint
  -- pointwise limits ((S3))
  let ℓ : (ι → ℝ) → ℝ := fun ξ => limUnder (𝓝[>] (0:ℝ)) (F ξ)
  have hℓ : ∀ ξ ∈ U, Tendsto (F ξ) (𝓝[>] 0) (𝓝 (ℓ ξ)) := fun ξ hξ =>
    tendsto_nhds_limUnder (exists_tendsto_of_bdd hS he (isSAFunOn₁_slice hF hξ) (M := 1)
      (fun ε hε => abs_le.2 (hFb ξ hξ ε hε)))
  have hℓΛ : ∀ ξ ∈ U, extendVal (ℓ ξ) ξ ∈ Λ := by
    intro ξ hξ
    refine mem_closure_of_tendsto (tendsto_gpt ((continuous_id.tendsto (0:ℝ)).mono_left
      nhdsWithin_le_nhds) tendsto_const_nhds (hℓ ξ hξ)) ?_
    filter_upwards [Ioo_mem_nhdsGT he] with ε hε using gpt_mem_graphSet hξ hε
  have hUT : (U \ T).Nonempty := nonempty_diff_of_interior_eq_empty hU hUne hTint
  -- the limit set is a union of graphs over a ball ((S5))
  obtain ⟨x₄, r₄, hr₄, hball₄, q, lam, hq, hlam, hmono, hrange⟩ :=
    hS.finite_fibers Λ (U \ T) hΛ (hU.sdiff hTcl) hUT
      (fun ξ hξ => ⟨hTfin ξ hξ.2, ⟨ℓ ξ, hℓΛ ξ hξ.1⟩⟩)
  have hB₄U : Metric.ball x₄ r₄ ⊆ U := hball₄.trans sdiff_subset
  have hΛy : ∀ y ∈ Metric.ball x₄ r₄, ∀ j, gpt 0 y (lam j y) ∈ closure Γ := by
    intro y hy j
    have : lam j y ∈ {v : ℝ | extendVal v y ∈ Λ} := by rw [hrange y hy]; exact ⟨j, rfl⟩
    exact this
  -- there is only one graph
  have hq1 : q = 1 := by
    by_contra hq1
    have hq2 : 1 < q := by omega
    obtain ⟨β, hβdef⟩ : ∃ β : (ι → ℝ) → ℝ,
        ∀ ξ, β ξ = (lam ⟨0, hq⟩ ξ + lam ⟨1, hq2⟩ ξ) / 2 := ⟨_, fun _ => rfl⟩
    have hab : ∀ ξ ∈ Metric.ball x₄ r₄, lam ⟨0, hq⟩ ξ < lam ⟨1, hq2⟩ ξ := fun ξ hξ =>
      hmono ξ hξ (show (⟨0, hq⟩ : Fin q) < ⟨1, hq2⟩ from Fin.mk_lt_mk.2 zero_lt_one)
    have hβc : ContinuousOn β (Metric.ball x₄ r₄) :=
      (((hlam _).2.add (hlam _).2).div_const 2).congr (fun ξ _ => hβdef ξ)
    have hFc' : ∀ ε ∈ Ioo 0 e, ContinuousOn (fun ξ => F ξ ε) (Metric.ball x₄ r₄) := by
      intro ε hε
      have hcont : Continuous fun ξ : ι → ℝ => extendVal ε ξ :=
        continuous_pi fun o => by cases o with
          | none => exact continuous_const
          | some i => exact continuous_apply i
      exact hFc.comp hcont.continuousOn (fun ξ hξ => ⟨hB₄U hξ, hε⟩)
    have hconv : ∀ ξ ∈ Metric.ball x₄ r₄,
        (∀ᶠ ε in 𝓝[>] 0, F ξ ε < β ξ) ∨ (∀ᶠ ε in 𝓝[>] 0, β ξ < F ξ ε) := by
      intro ξ hξ
      have hmem : ℓ ξ ∈ {y : ℝ | extendVal y ξ ∈ Λ} := hℓΛ ξ (hB₄U hξ)
      rw [hrange ξ hξ] at hmem
      obtain ⟨j, hj⟩ := hmem
      have hlt := hab ξ hξ
      have hβξ := hβdef ξ
      by_cases hj0 : j = ⟨0, hq⟩
      · left
        have : ℓ ξ < β ξ := by
          rw [← hj, hj0]; linarith
        exact (hℓ ξ (hB₄U hξ)).eventually (gt_mem_nhds this)
      · right
        have hj1 : (⟨1, hq2⟩ : Fin q) ≤ j := by
          rw [Fin.le_iff_val_le_val]
          have : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
          simp only; omega
        have : β ξ < ℓ ξ := by
          rw [← hj]
          have := (hmono ξ hξ).monotone hj1
          linarith
        exact (hℓ ξ (hB₄U hξ)).eventually (lt_mem_nhds this)
    obtain ⟨y, δ, ε₁, hδ, hyball, hε₁, hcase⟩ :=
      exists_ball_eventually_le_or_ge hr₄ he hβc hFc' hconv
    have hy : y ∈ Metric.ball x₄ r₄ := hyball (Metric.mem_ball_self hδ)
    have hβy : ContinuousAt β y := hβc.continuousAt (Metric.isOpen_ball.mem_nhds hy)
    have hβy' : ContinuousAt (fun p : (ι → ℝ) × ℝ => β p.1) (y, lam ⟨1, hq2⟩ y) :=
      ContinuousAt.comp (g := β) hβy continuousAt_fst
    have hβy'' : ContinuousAt (fun p : (ι → ℝ) × ℝ => β p.1) (y, lam ⟨0, hq⟩ y) :=
      ContinuousAt.comp (g := β) hβy continuousAt_fst
    have hlt := hab y hy
    have hβyv := hβdef y
    rcases hcase with hle | hge
    · have hc : ContinuousAt (fun p : (ι → ℝ) × ℝ => p.2 - β p.1) (y, lam ⟨1, hq2⟩ y) :=
        continuousAt_snd.sub hβy'
      have := closure_graphSet_le (hΛy y hy ⟨1, hq2⟩) (Metric.ball_mem_nhds y hδ) hε₁
        (ψ := fun ξ t => t - β ξ) hc
        (fun ξ hξ ε hε _ _ => by have := hle ξ hξ ε hε; linarith)
      linarith
    · have hc : ContinuousAt (fun p : (ι → ℝ) × ℝ => β p.1 - p.2) (y, lam ⟨0, hq⟩ y) :=
        hβy''.sub continuousAt_snd
      have := closure_graphSet_le (hΛy y hy ⟨0, hq⟩) (Metric.ball_mem_nhds y hδ) hε₁
        (ψ := fun ξ t => β ξ - t) hc
        (fun ξ hξ ε hε _ _ => by have := hge ξ hξ ε hε; linarith)
      linarith
  subst hq1
  have hΛuniq : ∀ ξ ∈ Metric.ball x₄ r₄, ∀ v, gpt 0 ξ v ∈ closure Γ → v = lam 0 ξ := by
    intro ξ hξ v hv
    have : v ∈ {y : ℝ | extendVal y ξ ∈ Λ} := hv
    rw [hrange ξ hξ] at this
    obtain ⟨j, rfl⟩ := this
    rw [Subsingleton.elim j 0]
  have hK : Metric.closedBall x₄ (r₄ / 2) ⊆ Metric.ball x₄ r₄ :=
    Metric.closedBall_subset_ball (by linarith)
  refine ⟨x₄, r₄ / 2, half_pos hr₄, (Metric.ball_subset_ball (by linarith)).trans hB₄U, lam 0,
    (hlam 0).2.mono (Metric.ball_subset_ball (by linarith)), ?_⟩
  exact (tendstoUniformlyOn_of_closure_graph he (isCompact_closedBall x₄ (r₄ / 2))
    (hK.trans hB₄U) ((hlam 0).2.mono hK) hFb
    (fun ξ hξ v hv => hΛuniq ξ (hK hξ) v hv)).mono Metric.ball_subset_closedBall

/-! ### Partial derivatives in the `ξ`-directions -/

/-- The embedding `ξ ↦ (ξ, 0)` of `ℝ^ι` into `ℝ^(Option ι)`. -/
def embedCLM : (ι → ℝ) →L[ℝ] (Option ι → ℝ) :=
  ContinuousLinearMap.pi fun o => Option.elim o 0 ContinuousLinearMap.proj

theorem embedCLM_apply (v : ι → ℝ) : embedCLM v = extendVal 0 v := by
  funext o; cases o <;> rfl

theorem continuous_extendVal (ε : ℝ) : Continuous fun ξ : ι → ℝ => extendVal ε ξ :=
  continuous_pi fun o => by
    cases o with
    | none => exact continuous_const
    | some i => exact continuous_apply i

theorem continuous_extendVal₂ : Continuous fun p : (ι → ℝ) × ℝ => extendVal p.2 p.1 :=
  continuous_pi fun o => by
    cases o with
    | none => exact continuous_snd
    | some i => exact (continuous_apply i).comp continuous_fst

theorem hasFDerivAt_extendVal (ε : ℝ) (ξ : ι → ℝ) :
    HasFDerivAt (fun y : ι → ℝ => extendVal ε y)
      (embedCLM : (ι → ℝ) →L[ℝ] (Option ι → ℝ)) ξ := by
  have : (fun y : ι → ℝ => extendVal ε y) = fun y => embedCLM y + extendVal ε 0 := by
    funext y o; cases o <;> simp [embedCLM_apply, extendVal]
  rw [this]
  exact embedCLM.hasFDerivAt.add_const _

theorem hasFDerivAt_slice {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {H : (Option ι → ℝ) → X} {ξ : ι → ℝ} {ε : ℝ} {L : (Option ι → ℝ) →L[ℝ] X}
    (hH : HasFDerivAt H L (extendVal ε ξ)) :
    HasFDerivAt (fun y => H (extendVal ε y)) (L.comp embedCLM) ξ :=
  hH.comp ξ (hasFDerivAt_extendVal ε ξ)

theorem fderiv_slice_apply {H : (Option ι → ℝ) → ℝ} {ξ : ι → ℝ} {ε : ℝ}
    (hH : DifferentiableAt ℝ H (extendVal ε ξ)) (v : ι → ℝ) :
    fderiv ℝ (fun y => H (extendVal ε y)) ξ v = fderiv ℝ H (extendVal ε ξ) (extendVal 0 v) := by
  rw [(hasFDerivAt_slice hH.hasFDerivAt).fderiv]
  simp [embedCLM_apply]

theorem extendVal_zero_single (i : ι) :
    extendVal 0 (Pi.single i (1:ℝ)) = Pi.single (some i) 1 := by
  funext o; cases o <;> simp [extendVal, Pi.single_apply]

theorem partial_eq {h : (ι → ℝ) → ℝ → ℝ} {ξ : ι → ℝ} {ε : ℝ}
    (hd : DifferentiableAt ℝ (uncurryOpt h) (extendVal ε ξ)) (i : ι) :
    fderiv ℝ (fun y => h y ε) ξ (Pi.single i 1) =
      fderiv ℝ (uncurryOpt h) (extendVal ε ξ) (Pi.single (some i) 1) := by
  rw [← extendVal_zero_single]
  exact fderiv_slice_apply hd _

theorem differentiableAt_slice {h : (ι → ℝ) → ℝ → ℝ} {ξ : ι → ℝ} {ε : ℝ}
    (hd : DifferentiableAt ℝ (uncurryOpt h) (extendVal ε ξ)) :
    DifferentiableAt ℝ (fun y => h y ε) ξ :=
  (hasFDerivAt_slice hd.hasFDerivAt).differentiableAt

/-- The operator norm on `ℝ^ι` is bounded by the sum of the values on basis vectors. -/
theorem norm_le_sum_single (T : (ι → ℝ) →L[ℝ] ℝ) : ‖T‖ ≤ ∑ i, |T (Pi.single i 1)| := by
  refine T.opNorm_le_bound (Finset.sum_nonneg fun i _ => abs_nonneg _) fun v => ?_
  have hv : v = ∑ i, v i • Pi.single i (1:ℝ) := by
    ext j; simp [Pi.single_apply]
  conv_lhs => rw [hv]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  calc ‖∑ i, v i * T (Pi.single i 1)‖ ≤ ∑ i, ‖v i * T (Pi.single i 1)‖ := norm_sum_le _ _
    _ ≤ ∑ i, |T (Pi.single i 1)| * ‖v‖ := Finset.sum_le_sum fun i _ => by
        rw [norm_mul, Real.norm_eq_abs (T _), mul_comm]
        exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v i) (abs_nonneg _)
    _ = (∑ i, |T (Pi.single i 1)|) * ‖v‖ := by rw [Finset.sum_mul]

/-- The mean value argument of the paper ("the limit is finite"). -/
theorem false_of_deriv_ge {φ φ' : ℝ → ℝ → ℝ} {ρ a b : ℝ} (hρ : 0 < ρ)
    (hd : ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ t ∈ Ioo (-ρ) ρ, HasDerivAt (φ ε) (φ' ε t) t)
    (hM : ∀ M : ℝ, ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ t ∈ Ioo (-ρ) ρ, M ≤ φ' ε t)
    (h0 : Tendsto (fun ε => φ ε 0) (𝓝[>] 0) (𝓝 a))
    (h1 : Tendsto (fun ε => φ ε (ρ / 2)) (𝓝[>] 0) (𝓝 b)) : False := by
  set M := 2 * (b - a) / ρ + 1 with hMdef
  have hev : ∀ᶠ ε in 𝓝[>] (0:ℝ), M * (ρ / 2 - 0) ≤ φ ε (ρ / 2) - φ ε 0 := by
    filter_upwards [hd, hM M] with ε hdε hMε
    have hconv : Convex ℝ (Ioo (-ρ) ρ) := convex_Ioo _ _
    have hcont : ContinuousOn (φ ε) (Ioo (-ρ) ρ) :=
      fun t ht => (hdε t ht).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ (φ ε) (interior (Ioo (-ρ) ρ)) := by
      rw [interior_Ioo]; exact fun t ht => (hdε t ht).differentiableAt.differentiableWithinAt
    have hderiv : ∀ t ∈ interior (Ioo (-ρ) ρ), M ≤ deriv (φ ε) t := by
      rw [interior_Ioo]; intro t ht; rw [(hdε t ht).deriv]; exact hMε t ht
    exact hconv.mul_sub_le_image_sub_of_le_deriv hcont hdiff hderiv 0 ⟨by linarith, hρ⟩ (ρ / 2)
      ⟨by linarith, by linarith⟩ (by linarith)
  have hlim : M * (ρ / 2 - 0) ≤ b - a := ge_of_tendsto (h1.sub h0) hev
  have : M * (ρ / 2 - 0) = (b - a) + ρ / 2 := by rw [hMdef]; field_simp; ring
  linarith

theorem false_of_deriv_le {φ φ' : ℝ → ℝ → ℝ} {ρ a b : ℝ} (hρ : 0 < ρ)
    (hd : ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ t ∈ Ioo (-ρ) ρ, HasDerivAt (φ ε) (φ' ε t) t)
    (hM : ∀ M : ℝ, ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ t ∈ Ioo (-ρ) ρ, φ' ε t ≤ M)
    (h0 : Tendsto (fun ε => φ ε 0) (𝓝[>] 0) (𝓝 a))
    (h1 : Tendsto (fun ε => φ ε (ρ / 2)) (𝓝[>] 0) (𝓝 b)) : False :=
  false_of_deriv_ge (φ := fun ε t => -φ ε t) (φ' := fun ε t => -φ' ε t) hρ
    (hd.mono fun _ h t ht => (h t ht).neg)
    (fun M => (hM (-M)).mono fun _ h t ht => by have := h t ht; linarith)
    h0.neg h1.neg

theorem tendstoUniformlyOn_comp_of_uniformContinuousOn {X ι' : Type*} {Φ : ℝ → ℝ}
    {J : Set ℝ} (hΦ : UniformContinuousOn Φ J) {G : ι' → X → ℝ} {f : X → ℝ} {l : Filter ι'}
    {s : Set X} (h : TendstoUniformlyOn G f l s) (hG : ∀ᶠ n in l, ∀ x ∈ s, G n x ∈ J)
    (hf : ∀ x ∈ s, f x ∈ J) :
    TendstoUniformlyOn (fun n x => Φ (G n x)) (fun x => Φ (f x)) l s := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro η hη
  obtain ⟨δ, hδ, hΦδ⟩ := Metric.uniformContinuousOn_iff.1 hΦ η hη
  filter_upwards [h δ hδ, hG] with n hn hGn x hx
  exact hΦδ _ (hf x hx) _ (hGn x hx) (hn x hx)

/-- **Lemma 3.1 for one coordinate direction**: the partial derivatives `∂g/∂ξᵢ(·, ε)` converge
uniformly on some ball to a continuous function. -/
theorem exists_ball_partial (hS : SAFacts) {U : Set (ι → ℝ)} (hU : IsOpen U)
    (hUne : U.Nonempty) {e : ℝ} (he : 0 < e) {h : (ι → ℝ) → ℝ → ℝ}
    (hh : IsSAFunOn₁ (boxDomain U e) (uncurryOpt h))
    (hsm : ContDiffOn ℝ 1 (uncurryOpt h) (boxDomain U e))
    (h₀ : (ι → ℝ) → ℝ) (hlim : ∀ ξ ∈ U, Tendsto (h ξ) (𝓝[>] 0) (𝓝 (h₀ ξ))) (i : ι) :
    ∃ (x : ι → ℝ) (r : ℝ), 0 < r ∧ Metric.ball x r ⊆ U ∧ ∃ ℓ : (ι → ℝ) → ℝ,
      ContinuousOn ℓ (Metric.ball x r) ∧
      TendstoUniformlyOn (fun ε ξ => fderiv ℝ (fun ξ => h ξ ε) ξ (Pi.single i 1)) ℓ
        (𝓝[>] 0) (Metric.ball x r) := by
  have hO := isOpen_boxDomain hU e
  have hdiff : ∀ v ∈ boxDomain U e, DifferentiableAt ℝ (uncurryOpt h) v :=
    fun v hv => (hsm.differentiableOn one_ne_zero v hv).differentiableAt (hO.mem_nhds hv)
  obtain ⟨D, hDdef⟩ : ∃ D : (ι → ℝ) → ℝ → ℝ,
      ∀ ξ ε, D ξ ε = fderiv ℝ (fun ξ => h ξ ε) ξ (Pi.single i 1) := ⟨_, fun _ _ => rfl⟩
  have hDeq' : EqOn (fun v => fderiv ℝ (uncurryOpt h) v (Pi.single (some i) 1)) (uncurryOpt D)
      (boxDomain U e) := by
    intro v hv
    have := partial_eq (hdiff _ (by rw [extendVal_eta]; exact hv)) i (h := h)
      (ξ := v ∘ some) (ε := v none)
    rw [extendVal_eta] at this
    show _ = D (v ∘ some) (v none)
    rw [hDdef]; exact this.symm
  obtain ⟨F, hFdef⟩ : ∃ F : (ι → ℝ) → ℝ → ℝ, ∀ ξ ε, F ξ ε = theta (D ξ ε) :=
    ⟨_, fun _ _ => rfl⟩
  have hFeq : uncurryOpt F = fun v => theta (uncurryOpt D v) := by
    funext v; exact hFdef _ _
  have hFsa : IsSAFunOn₁ (boxDomain U e) (uncurryOpt F) := by
    have h1 := IsSAFunOn₁.fderiv_apply hO hh (hsm.differentiableOn one_ne_zero)
      (Pi.single (some i) 1)
    have h2 := isSAFunOn₁_congr h1 hDeq'
    rw [hFeq]
    exact isSAFunOn₁_theta h2
  have hFc : ContinuousOn (uncurryOpt F) (boxDomain U e) := by
    have h1 : ContinuousOn (fun v => fderiv ℝ (uncurryOpt h) v (Pi.single (some i) 1))
        (boxDomain U e) :=
      (hsm.continuousOn_fderiv_of_isOpen hO le_rfl).clm_apply continuousOn_const
    rw [hFeq]
    exact continuous_theta.comp_continuousOn (h1.congr (fun v hv => (hDeq' hv).symm))
  have hFb : ∀ ξ ∈ U, ∀ ε ∈ Ioo 0 e, F ξ ε ∈ Icc (-1:ℝ) 1 := fun ξ _ ε _ => by
    rw [hFdef]; exact abs_le.1 (abs_theta_lt_one _).le
  obtain ⟨x₁, r₁, hr₁, hb₁, ℓt, hℓtc, hℓtu⟩ :=
    exists_ball_tendstoUniformlyOn hS hU hUne he hFsa hFc hFb
  have hℓtb : ∀ ξ ∈ Metric.ball x₁ r₁, |ℓt ξ| ≤ 1 := by
    intro ξ hξ
    have ht := hℓtu.tendsto_at hξ
    refine abs_le.2 ⟨ge_of_tendsto ht ?_, le_of_tendsto ht ?_⟩
    · filter_upwards [Ioo_mem_nhdsGT he] with ε hε using (hFb ξ (hb₁ hξ) ε hε).1
    · filter_upwards [Ioo_mem_nhdsGT he] with ε hε using (hFb ξ (hb₁ hξ) ε hε).2
  -- the derivative of `g` along the coordinate line
  have hline : ∀ ξ ∈ U, ∀ ε ∈ Ioo 0 e, ∀ t : ℝ, ξ + t • Pi.single i 1 ∈ U →
      HasDerivAt (fun s : ℝ => h (ξ + s • Pi.single i 1) ε)
        (D (ξ + t • Pi.single i 1) ε) t := by
    intro ξ _ ε hε t ht
    have hd := differentiableAt_slice (hdiff _ ⟨ht, hε⟩) (h := h)
    have hγ : HasDerivAt (fun s : ℝ => ξ + s • (Pi.single i 1 : ι → ℝ)) (Pi.single i 1) t := by
      simpa using ((hasDerivAt_id t).smul_const (Pi.single i (1:ℝ) : ι → ℝ)).const_add ξ
    have := hd.hasFDerivAt.comp_hasDerivAt t hγ
    rw [hDdef]
    exact this
  have hchord : ∀ t ∈ Ioo (-r₁) r₁, x₁ + t • Pi.single i (1:ℝ) ∈ Metric.ball x₁ r₁ := by
    intro t ht
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Pi.norm_single, norm_one,
      mul_one, Real.norm_eq_abs]
    exact abs_lt.2 ht
  -- the limit is finite somewhere
  have hfin : ∃ ξ₀ ∈ Metric.ball x₁ r₁, |ℓt ξ₀| < 1 := by
    by_contra hcon
    push Not at hcon
    have hone : ∀ ξ ∈ Metric.ball x₁ r₁, |ℓt ξ| = 1 :=
      fun ξ hξ => le_antisymm (hℓtb ξ hξ) (hcon ξ hξ)
    have hcont : ContinuousOn (fun t : ℝ => ℓt (x₁ + t • Pi.single i (1:ℝ))) (Ioo (-r₁) r₁) :=
      hℓtc.comp (by fun_prop : Continuous fun t : ℝ => x₁ + t • Pi.single i (1:ℝ)).continuousOn
        (fun t ht => hchord t ht)
    have hsq : EqOn ((fun t : ℝ => ℓt (x₁ + t • Pi.single i (1:ℝ))) ^ 2) 1
        (Ioo (-r₁) r₁) := by
      intro t ht
      simp only [Pi.pow_apply, Pi.one_apply]
      rw [← sq_abs, hone _ (hchord t ht), one_pow]
    have hderiv : ∀ ε ∈ Ioo 0 e, ∀ t ∈ Ioo (-r₁) r₁,
        HasDerivAt (fun s : ℝ => h (x₁ + s • Pi.single i 1) ε)
          (D (x₁ + t • Pi.single i 1) ε) t :=
      fun ε hε t ht => hline x₁ (hb₁ (Metric.mem_ball_self hr₁)) ε hε t (hb₁ (hchord t ht))
    have hl0 : Tendsto (fun ε => h (x₁ + (0:ℝ) • Pi.single i 1) ε) (𝓝[>] 0)
        (𝓝 (h₀ (x₁ + (0:ℝ) • Pi.single i 1))) :=
      hlim _ (hb₁ (hchord 0 ⟨by linarith, hr₁⟩))
    have hl1 : Tendsto (fun ε => h (x₁ + (r₁ / 2) • Pi.single i 1) ε) (𝓝[>] 0)
        (𝓝 (h₀ (x₁ + (r₁ / 2) • Pi.single i 1))) :=
      hlim _ (hb₁ (hchord _ ⟨by linarith, by linarith⟩))
    rcases isPreconnected_Ioo.eq_one_or_eq_neg_one_of_sq_eq hcont hsq with hp | hm
    · refine false_of_deriv_ge hr₁ (φ := fun ε s => h (x₁ + s • Pi.single i 1) ε)
        (φ' := fun ε t => D (x₁ + t • Pi.single i 1) ε) ?_ ?_ hl0 hl1
      · filter_upwards [Ioo_mem_nhdsGT he] with ε hε using hderiv ε hε
      · intro M
        have hθ : 0 < 1 - theta M := by have := abs_lt.1 (abs_theta_lt_one M); linarith
        filter_upwards [Metric.tendstoUniformlyOn_iff.1 hℓtu _ hθ] with ε hε t ht
        have h1 := hε _ (hchord t ht)
        have h2 : ℓt (x₁ + t • Pi.single i 1) = 1 := hp ht
        rw [h2, hFdef, Real.dist_eq, abs_lt] at h1
        have h3 : theta M < theta (D (x₁ + t • Pi.single i 1) ε) := by linarith
        exact (theta_strictMono.lt_iff_lt.1 h3).le
    · refine false_of_deriv_le hr₁ (φ := fun ε s => h (x₁ + s • Pi.single i 1) ε)
        (φ' := fun ε t => D (x₁ + t • Pi.single i 1) ε) ?_ ?_ hl0 hl1
      · filter_upwards [Ioo_mem_nhdsGT he] with ε hε using hderiv ε hε
      · intro M
        have hθ : 0 < theta M + 1 := by have := abs_lt.1 (abs_theta_lt_one M); linarith
        filter_upwards [Metric.tendstoUniformlyOn_iff.1 hℓtu _ hθ] with ε hε t ht
        have h1 := hε _ (hchord t ht)
        have h2 : ℓt (x₁ + t • Pi.single i 1) = -1 := hm ht
        rw [h2, hFdef, Real.dist_eq, abs_lt] at h1
        have h3 : theta (D (x₁ + t • Pi.single i 1) ε) < theta M := by linarith
        exact (theta_strictMono.lt_iff_lt.1 h3).le
  obtain ⟨ξ₀, hξ₀, hξ₀1⟩ := hfin
  -- a ball on which `|ℓt| ≤ c < 1`
  set c := (1 + |ℓt ξ₀|) / 2 with hc
  have hc1 : c < 1 := by rw [hc]; linarith
  have hcont₀ : ContinuousAt ℓt ξ₀ := hℓtc.continuousAt (Metric.isOpen_ball.mem_nhds hξ₀)
  obtain ⟨ρ, hρ, hρc⟩ := Metric.continuousAt_iff.1 hcont₀ ((1 - |ℓt ξ₀|) / 2) (by linarith)
  set ρ' := min ρ (r₁ - dist ξ₀ x₁) with hρ'
  have hρ'pos : 0 < ρ' := lt_min hρ (by have := Metric.mem_ball.1 hξ₀; linarith)
  have hB₂ : Metric.ball ξ₀ ρ' ⊆ Metric.ball x₁ r₁ :=
    Metric.ball_subset_ball' (by rw [hρ']; linarith [min_le_right ρ (r₁ - dist ξ₀ x₁)])
  have hℓc : ∀ ξ ∈ Metric.ball ξ₀ ρ', |ℓt ξ| ≤ c := by
    intro ξ hξ
    have h1 := hρc (lt_of_lt_of_le (Metric.mem_ball.1 hξ) (min_le_left _ _))
    rw [Real.dist_eq] at h1
    have h2 := abs_sub_abs_le_abs_sub (ℓt ξ) (ℓt ξ₀)
    rw [hc]; linarith
  set c' := (1 + c) / 2 with hc'
  have hc'1 : c' < 1 := by rw [hc']; linarith
  have hcc' : c < c' := by rw [hc']; linarith
  have hJ : Icc (-c') c' ⊆ Ioo (-1) 1 := Icc_subset_Ioo (by linarith) hc'1
  have hΦ : UniformContinuousOn thetaInv (Icc (-c') c') :=
    isCompact_Icc.uniformContinuousOn_of_continuous (continuousOn_thetaInv.mono hJ)
  have hG : ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ ξ ∈ Metric.ball ξ₀ ρ', F ξ ε ∈ Icc (-c') c' := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 hℓtu _ (sub_pos.2 hcc')] with ε hε ξ hξ
    have h1 := hε ξ (hB₂ hξ)
    have h2 := hℓc ξ hξ
    rw [Real.dist_eq] at h1
    have h3 := abs_sub_abs_le_abs_sub (F ξ ε) (ℓt ξ)
    rw [abs_sub_comm] at h1
    exact abs_le.1 (by linarith)
  have hf : ∀ ξ ∈ Metric.ball ξ₀ ρ', ℓt ξ ∈ Icc (-c') c' :=
    fun ξ hξ => abs_le.1 ((hℓc ξ hξ).trans hcc'.le)
  have hU' := tendstoUniformlyOn_comp_of_uniformContinuousOn hΦ (hℓtu.mono hB₂) hG hf
  refine ⟨ξ₀, ρ', hρ'pos, hB₂.trans hb₁, fun ξ => thetaInv (ℓt ξ), ?_, ?_⟩
  · exact continuousOn_thetaInv.comp (hℓtc.mono hB₂) (fun ξ hξ => hJ (hf ξ hξ))
  · refine hU'.congr (Eventually.of_forall fun ε ξ _ => ?_)
    simp only [hFdef, thetaInv_theta, hDdef]

/-- **Lemma 3.1, strong form.**  For a semialgebraic family that is `C¹` on the box and converges
pointwise, on some ball the limit is `C¹`, the family converges uniformly, and so do all the
first partial derivatives in `ξ`. -/
theorem exists_ball_C1_limit (hS : SAFacts) {U : Set (ι → ℝ)} (hU : IsOpen U)
    (hUne : U.Nonempty) {e : ℝ} (he : 0 < e) {h : (ι → ℝ) → ℝ → ℝ}
    (hh : IsSAFunOn₁ (boxDomain U e) (uncurryOpt h))
    (hsm : ContDiffOn ℝ 1 (uncurryOpt h) (boxDomain U e))
    (h₀ : (ι → ℝ) → ℝ) (hlim : ∀ ξ ∈ U, Tendsto (h ξ) (𝓝[>] 0) (𝓝 (h₀ ξ))) :
    ∃ (x : ι → ℝ) (r : ℝ), 0 < r ∧ Metric.ball x r ⊆ U ∧
      ContDiffOn ℝ 1 h₀ (Metric.ball x r) ∧
      TendstoUniformlyOn (fun ε ξ => h ξ ε) h₀ (𝓝[>] 0) (Metric.ball x r) ∧
      ∀ i : ι, TendstoUniformlyOn (fun ε ξ => fderiv ℝ (fun ξ => h ξ ε) ξ (Pi.single i 1))
        (fun ξ => fderiv ℝ h₀ ξ (Pi.single i 1)) (𝓝[>] 0) (Metric.ball x r) := by
  have hO := isOpen_boxDomain hU e
  have hdiff : ∀ v ∈ boxDomain U e, DifferentiableAt ℝ (uncurryOpt h) v :=
    fun v hv => (hsm.differentiableOn one_ne_zero v hv).differentiableAt (hO.mem_nhds hv)
  obtain ⟨r₀, hr₀, hb₀⟩ := Metric.isOpen_iff.1 hU _ hUne.some_mem
  -- treat the coordinates one after another
  obtain ⟨x, r, -, hr, hb, -, -, hP⟩ := iterate_boxes (γ := ι)
    (fun i s _ => ∃ ℓ : (ι → ℝ) → ℝ, ContinuousOn ℓ s ∧
      TendstoUniformlyOn (fun ε ξ => fderiv ℝ (fun ξ => h ξ ε) ξ (Pi.single i 1)) ℓ
        (𝓝[>] 0) s)
    hUne.some r₀ e
    (fun i s t _ _ ⟨ℓ, h1, h2⟩ hts _ _ => ⟨ℓ, h1.mono hts, h2.mono hts⟩)
    (fun i x' r' e' hr' hb' he' _ => by
      have hsub : Metric.ball x' r' ⊆ U := hb'.trans hb₀
      obtain ⟨x'', r'', hr'', hb'', hP⟩ := exists_ball_partial hS Metric.isOpen_ball
        ⟨x', Metric.mem_ball_self hr'⟩ he
        (isSAFunOn₁_mono hh (isSA_boxDomain (isSA_ball _ _) e) (boxDomain_mono hsub le_rfl))
        (hsm.mono (boxDomain_mono hsub le_rfl)) h₀ (fun ξ hξ => hlim ξ (hsub hξ)) i
      exact ⟨x'', r'', e', hr'', hb'', he', le_rfl, hP⟩)
    hr₀ he
  choose ℓ hℓc hℓu using hP
  have hbU : Metric.ball x r ⊆ U := hb.trans hb₀
  set B := Metric.ball x r with hB
  -- the candidate derivative of the limit
  let L : (ι → ℝ) → ((ι → ℝ) →L[ℝ] ℝ) := fun ξ => ∑ i, ℓ i ξ • ContinuousLinearMap.proj i
  have hLapp : ∀ ξ j, L ξ (Pi.single j 1) = ℓ j ξ := by
    intro ξ j
    simp [L, Pi.single_apply]
  have hLc : ContinuousOn L B := by
    exact continuousOn_finsetSum _ fun i _ => (hℓc i).smul continuousOn_const
  -- a modified family, defined for every `ε`
  let c : ℝ → ℝ := fun ε => if ε ∈ Ioo 0 e then ε else e / 2
  have hc : ∀ ε, c ε ∈ Ioo 0 e := by
    intro ε; simp only [c]; split_ifs with h1
    · exact h1
    · exact ⟨half_pos he, half_lt_self he⟩
  have hceq : ∀ᶠ ε in 𝓝[>] (0:ℝ), c ε = ε := by
    filter_upwards [Ioo_mem_nhdsGT he] with ε hε
    simp only [c, hε, ite_true]
  let f : ℝ → (ι → ℝ) → ℝ := fun ε ξ => h ξ (c ε)
  let f' : ℝ → (ι → ℝ) → ((ι → ℝ) →L[ℝ] ℝ) := fun ε ξ => fderiv ℝ (f ε) ξ
  have hfd : ∀ ε, ∀ ξ ∈ B, HasFDerivAt (f ε) (f' ε ξ) ξ := fun ε ξ hξ =>
    (differentiableAt_slice (hdiff _ ⟨hbU hξ, hc ε⟩) (h := h)).hasFDerivAt
  have hfeq : ∀ᶠ ε in 𝓝[>] (0:ℝ), f ε = fun ξ => h ξ ε := by
    filter_upwards [hceq] with ε hε
    funext ξ; simp only [f, hε]
  have hfg : ∀ ξ ∈ B, Tendsto (fun ε => f ε ξ) (𝓝[>] 0) (𝓝 (h₀ ξ)) := by
    intro ξ hξ
    refine (hlim ξ (hbU hξ)).congr' ?_
    filter_upwards [hfeq] with ε hε
    rw [hε]
  -- uniform convergence of the derivatives
  have hf'u : TendstoUniformlyOn f' L (𝓝[>] 0) B := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro η hη
    set η' := η / ((Fintype.card ι : ℝ) + 1) with hη'
    have hη'pos : 0 < η' := by positivity
    have hall : ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ i, ∀ ξ ∈ B,
        dist (ℓ i ξ) (fderiv ℝ (fun ξ => h ξ ε) ξ (Pi.single i 1)) < η' :=
      eventually_all.2 fun i => Metric.tendstoUniformlyOn_iff.1 (hℓu i) η' hη'pos
    filter_upwards [hall, hfeq] with ε hε hfε ξ hξ
    have hf'ε : f' ε ξ = fderiv ℝ (fun ξ => h ξ ε) ξ := by simp only [f', hfε]
    rw [hf'ε, dist_eq_norm]
    refine lt_of_le_of_lt (norm_le_sum_single _) ?_
    calc ∑ i, |(L ξ - fderiv ℝ (fun ξ => h ξ ε) ξ) (Pi.single i 1)|
        ≤ ∑ _i : ι, η' := Finset.sum_le_sum fun i _ => by
          rw [sub_apply, hLapp, ← Real.dist_eq]
          exact (hε i ξ hξ).le
      _ = (Fintype.card ι : ℝ) * η' := by simp
      _ < η := by
          rw [hη', mul_div_assoc']
          rw [div_lt_iff₀ (by positivity)]
          nlinarith
  have hderiv : ∀ ξ ∈ B, HasFDerivAt h₀ (L ξ) ξ := fun ξ hξ =>
    hasFDerivAt_of_tendstoUniformlyOn Metric.isOpen_ball hf'u hfd hfg hξ
  have hfderiv : ∀ ξ ∈ B, fderiv ℝ h₀ ξ = L ξ := fun ξ hξ => (hderiv ξ hξ).fderiv
  -- uniform convergence of the functions
  have hfu : TendstoUniformlyOn f h₀ (𝓝[>] 0) B := by
    have hcs := uniformCauchySeqOn_ball_of_fderiv hf'u.uniformCauchySeqOn hfd
      (hfg x (Metric.mem_ball_self hr)).cauchy_map
    exact hcs.tendstoUniformlyOn_of_tendsto hfg
  refine ⟨x, r, hr, hbU, ?_, ?_, ?_⟩
  · have hdo : DifferentiableOn ℝ h₀ B := fun ξ hξ =>
      (hderiv ξ hξ).differentiableAt.differentiableWithinAt
    have h1 : ContDiffOn ℝ ((0 : WithTop ℕ∞) + 1) h₀ B :=
      (contDiffOn_succ_iff_fderiv_of_isOpen Metric.isOpen_ball).2
        ⟨hdo, by intro h; exact absurd h (by simp),
          contDiffOn_zero.2 (hLc.congr fun ξ hξ => hfderiv ξ hξ)⟩
    simpa using h1
  · refine hfu.congr ?_
    filter_upwards [hfeq] with ε hε ξ _
    rw [hε]
  · intro i
    refine (hℓu i).congr_right fun ξ hξ => ?_
    rw [hfderiv ξ hξ, hLapp]

theorem contDiff_extendVal (ε : ℝ) : ContDiff ℝ ⊤ fun ξ : ι → ℝ => extendVal ε ξ :=
  contDiff_pi.2 fun o => by
    cases o with
    | none => exact contDiff_const
    | some i => exact contDiff_apply ℝ (fun _ : ι => ℝ) i

theorem contDiff_extendVal₂ : ContDiff ℝ ⊤ fun p : (ι → ℝ) × ℝ => extendVal p.2 p.1 :=
  contDiff_pi.2 fun o => by
    cases o with
    | none => exact contDiff_snd
    | some i => exact (contDiff_apply ℝ (fun _ : ι => ℝ) i).comp contDiff_fst

/-! ### Higher derivatives (Corollary 3.2) -/

/-- Iterated partial derivatives in the `ξ`-directions of a function on `ℝ^(Option ι)`; the
outermost derivative is in the direction `m 0`. -/
def iterPartial (H : (Option ι → ℝ) → ℝ) : (j : ℕ) → (Fin j → ι) → (Option ι → ℝ) → ℝ
  | 0, _ => H
  | j + 1, m => fun v => fderiv ℝ (iterPartial H j (Fin.tail m)) v (Pi.single (some (m 0)) 1)

theorem contDiffOn_iterPartial {H : (Option ι → ℝ) → ℝ} {O : Set (Option ι → ℝ)}
    (hO : IsOpen O) (hH : ContDiffOn ℝ ⊤ H O) :
    ∀ (j : ℕ) (m : Fin j → ι), ContDiffOn ℝ ⊤ (iterPartial H j m) O
  | 0, _ => hH
  | j + 1, m => by
    have := contDiffOn_iterPartial hO hH j (Fin.tail m)
    exact (this.fderiv_of_isOpen hO le_top).clm_apply contDiffOn_const

theorem isSAFunOn₁_iterPartial {H : (Option ι → ℝ) → ℝ} {O : Set (Option ι → ℝ)}
    (hO : IsOpen O) (hH : ContDiffOn ℝ ⊤ H O) (hsa : IsSAFunOn₁ O H) :
    ∀ (j : ℕ) (m : Fin j → ι), IsSAFunOn₁ O (iterPartial H j m)
  | 0, _ => hsa
  | j + 1, m => IsSAFunOn₁.fderiv_apply hO (isSAFunOn₁_iterPartial hO hH hsa j (Fin.tail m))
      ((contDiffOn_iterPartial hO hH j (Fin.tail m)).differentiableOn (by simp)) _

theorem fderiv_eval_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {j : ℕ}
    {T : E → ContinuousMultilinearMap ℝ (fun _ : Fin j => ι → ℝ) (κ → ℝ)} {ξ : E}
    (hT : DifferentiableAt ℝ T ξ) (u : Fin j → ι → ℝ) (k : κ) (v : E) :
    fderiv ℝ (fun y => T y u k) ξ v = fderiv ℝ T ξ v u k := by
  let Λ : ContinuousMultilinearMap ℝ (fun _ : Fin j => ι → ℝ) (κ → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj k : (κ → ℝ) →L[ℝ] ℝ).comp
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => ι → ℝ) (κ → ℝ) u)
  have : HasFDerivAt (fun y => Λ (T y)) (Λ.comp (fderiv ℝ T ξ)) ξ :=
    Λ.hasFDerivAt.comp ξ hT.hasFDerivAt
  have h2 : fderiv ℝ (fun y => T y u k) ξ = Λ.comp (fderiv ℝ T ξ) := this.fderiv
  rw [h2]; rfl

/-- The components of the iterated `ξ`-derivatives are the iterated partial derivatives. -/
theorem iteratedFDeriv_eq_iterPartial {W : (ι → ℝ) → ℝ → (κ → ℝ)} {U : Set (ι → ℝ)}
    (hU : IsOpen U) {e : ℝ} (hW : ContDiffOn ℝ ⊤ (uncurryOpt W) (boxDomain U e)) {ε : ℝ}
    (hε : ε ∈ Ioo 0 e) (k : κ) :
    ∀ (j : ℕ) (m : Fin j → ι) (ξ : ι → ℝ), ξ ∈ U →
      iteratedFDeriv ℝ j (fun y => W y ε) ξ (fun l => Pi.single (m l) 1) k =
        iterPartial (fun v => uncurryOpt W v k) j m (extendVal ε ξ)
  | 0, m, ξ, hξ => by
    rw [iteratedFDeriv_zero_apply]
    rfl
  | j + 1, m, ξ, hξ => by
    have hO := isOpen_boxDomain hU e
    have hWε : ContDiffOn ℝ ⊤ (fun y => W y ε) U :=
      hW.comp (contDiff_extendVal ε).contDiffOn (fun y hy => ⟨hy, hε⟩)
    have hdiffT : DifferentiableAt ℝ (iteratedFDeriv ℝ j (fun y => W y ε)) ξ :=
      (hWε.contDiffAt (hU.mem_nhds hξ)).differentiableAt_iteratedFDeriv (by simp)
    rw [iteratedFDeriv_succ_apply_left, ← fderiv_eval_apply hdiffT]
    have hev : (fun y => iteratedFDeriv ℝ j (fun y => W y ε) y
        (Fin.tail (α := fun _ => ι → ℝ) (fun l => Pi.single (m l) (1:ℝ))) k) =ᶠ[𝓝 ξ]
        (fun y => iterPartial (fun v => uncurryOpt W v k) j (Fin.tail m) (extendVal ε y)) := by
      filter_upwards [hU.mem_nhds hξ] with y hy
      exact iteratedFDeriv_eq_iterPartial hU hW hε k j (Fin.tail m) y hy
    rw [hev.fderiv_eq]
    have hdJ : DifferentiableAt ℝ (iterPartial (fun v => uncurryOpt W v k) j (Fin.tail m))
        (extendVal ε ξ) :=
      ((contDiffOn_iterPartial hO (contDiffOn_pi.1 hW k) j (Fin.tail m)).differentiableOn
        (by simp) (extendVal ε ξ) ⟨hξ, hε⟩).differentiableAt (hO.mem_nhds ⟨hξ, hε⟩)
    rw [fderiv_slice_apply hdJ, extendVal_zero_single]
    rfl

/-- Evaluation of a multilinear map on all tuples of standard basis vectors, followed by all
coordinates. -/
def evalCLM (j : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin j => ι → ℝ) (κ → ℝ) →L[ℝ] (κ × (Fin j → ι) → ℝ) :=
  ContinuousLinearMap.pi fun p => (ContinuousLinearMap.proj p.1).comp
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => ι → ℝ) (κ → ℝ)
      (fun l => Pi.single (p.2 l) 1))

theorem evalCLM_apply (j : ℕ)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin j => ι → ℝ) (κ → ℝ))
    (p : κ × (Fin j → ι)) : evalCLM j T p = T (fun l => Pi.single (p.2 l) 1) p.1 := rfl

theorem evalCLM_injective (j : ℕ) : Function.Injective (evalCLM (ι := ι) (κ := κ) j) := by
  intro T T' h
  have h' : T.toMultilinearMap = T'.toMultilinearMap := by
    refine Module.Basis.ext_multilinear (fun _ => Pi.basisFun ℝ ι) fun v => ?_
    funext k
    have := congrFun h (k, v)
    simpa [evalCLM_apply, Pi.basisFun_apply] using this
  exact ContinuousMultilinearMap.toMultilinearMap_injective h'

theorem evalCLM_hasLeftInverse (j : ℕ) : (evalCLM (ι := ι) (κ := κ) j).HasLeftInverse :=
  ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional (evalCLM_injective j)

theorem tendstoUniformlyOn_of_evalCLM {X : Type*} {j : ℕ}
    {T : ℝ → X → ContinuousMultilinearMap ℝ (fun _ : Fin j => ι → ℝ) (κ → ℝ)}
    {T₀ : X → ContinuousMultilinearMap ℝ (fun _ : Fin j => ι → ℝ) (κ → ℝ)} {l : Filter ℝ}
    {s : Set X}
    (h : ∀ p, TendstoUniformlyOn (fun n x => evalCLM j (T n x) p)
      (fun x => evalCLM j (T₀ x) p) l s) :
    TendstoUniformlyOn T T₀ l s := by
  have hpi : TendstoUniformlyOn (fun n x => evalCLM j (T n x)) (fun x => evalCLM j (T₀ x))
      l s := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro η hη
    have := eventually_all.2 fun p => Metric.tendstoUniformlyOn_iff.1 (h p) η hη
    filter_upwards [this] with n hn x hx
    exact (dist_pi_lt_iff hη).2 fun p => hn p x hx
  obtain ⟨g, hg⟩ := evalCLM_hasLeftInverse (ι := ι) (κ := κ) j
  have := g.uniformContinuous.comp_tendstoUniformlyOn hpi
  have e1 : ∀ n, (g ∘ fun x => evalCLM j (T n x)) = T n := fun n => funext fun x => hg _
  have e2 : (g ∘ fun x => evalCLM j (T₀ x)) = T₀ := funext fun x => hg _
  simpa only [e1, e2] using this

theorem contDiffOn_of_evalCLM {j : ℕ} {n : WithTop ℕ∞}
    {T : (ι → ℝ) → ContinuousMultilinearMap ℝ (fun _ : Fin j => ι → ℝ) (κ → ℝ)}
    {s : Set (ι → ℝ)} (h : ∀ p, ContDiffOn ℝ n (fun x => evalCLM j (T x) p) s) :
    ContDiffOn ℝ n T s := by
  obtain ⟨g, hg⟩ := evalCLM_hasLeftInverse (ι := ι) (κ := κ) j
  have h1 : ContDiffOn ℝ n (fun x => evalCLM j (T x)) s := contDiffOn_pi.2 h
  have h2 := g.contDiff.comp_contDiffOn h1
  exact h2.congr fun x _ => (hg (T x)).symm

theorem continuousOn_of_evalCLM {X : Type*} [TopologicalSpace X] {j : ℕ}
    {T : X → ContinuousMultilinearMap ℝ (fun _ : Fin j => ι → ℝ) (κ → ℝ)}
    {s : Set X} (h : ∀ p, ContinuousOn (fun x => evalCLM j (T x) p) s) :
    ContinuousOn T s := by
  obtain ⟨g, hg⟩ := evalCLM_hasLeftInverse (ι := ι) (κ := κ) j
  have h1 : ContinuousOn (fun x => evalCLM j (T x)) s := continuousOn_pi.2 h
  have h2 := g.continuous.comp_continuousOn h1
  exact h2.congr fun x _ => (hg (T x)).symm

/-- One step of the induction in Corollary 3.2: from pointwise convergence of the `j`-th
derivatives to uniform convergence of the `j`-th and `(j+1)`-st derivatives on a smaller ball. -/
theorem cor_step (hS : SAFacts) {U : Set (ι → ℝ)} (hU : IsOpen U) {e : ℝ} (he : 0 < e)
    {W : (ι → ℝ) → ℝ → (κ → ℝ)}
    (hWsa : ∀ k, IsSAFunOn₁ (boxDomain U e) (fun v => uncurryOpt W v k))
    (hWsm : ContDiffOn ℝ ⊤ (uncurryOpt W) (boxDomain U e)) (φ : (ι → ℝ) → (κ → ℝ)) (j : ℕ)
    {x : ι → ℝ} {r : ℝ} (hr : 0 < r) (hball : Metric.ball x r ⊆ U)
    (hφ : ContDiffOn ℝ j φ (Metric.ball x r))
    (hpt : ∀ ξ ∈ Metric.ball x r, Tendsto (fun ε => iteratedFDeriv ℝ j (fun y => W y ε) ξ)
      (𝓝[>] 0) (𝓝 (iteratedFDeriv ℝ j φ ξ))) :
    ∃ (x' : ι → ℝ) (r' : ℝ), 0 < r' ∧ Metric.ball x' r' ⊆ Metric.ball x r ∧
      ContDiffOn ℝ ((j + 1 : ℕ) : WithTop ℕ∞) φ (Metric.ball x' r') ∧
      TendstoUniformlyOn (fun ε ξ => iteratedFDeriv ℝ j (fun y => W y ε) ξ)
        (iteratedFDeriv ℝ j φ) (𝓝[>] 0) (Metric.ball x' r') ∧
      TendstoUniformlyOn (fun ε ξ => iteratedFDeriv ℝ (j + 1) (fun y => W y ε) ξ)
        (iteratedFDeriv ℝ (j + 1) φ) (𝓝[>] 0) (Metric.ball x' r') := by
  have hO := isOpen_boxDomain hU e
  have hHsm : ∀ k, ContDiffOn ℝ ⊤ (fun v => uncurryOpt W v k) (boxDomain U e) :=
    fun k => contDiffOn_pi.1 hWsm k
  -- the coordinates of the `j`-th derivative, as functions on the box
  obtain ⟨J, hJdef⟩ : ∃ J : κ × (Fin j → ι) → (Option ι → ℝ) → ℝ,
      ∀ p, J p = iterPartial (fun v => uncurryOpt W v p.1) j p.2 := ⟨_, fun _ => rfl⟩
  obtain ⟨hfam, hfamdef⟩ : ∃ hfam : κ × (Fin j → ι) → (ι → ℝ) → ℝ → ℝ,
      ∀ p ξ ε, hfam p ξ ε = J p (extendVal ε ξ) := ⟨_, fun _ _ _ => rfl⟩
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : κ × (Fin j → ι) → (ι → ℝ) → ℝ,
      ∀ p ξ, ψ p ξ = evalCLM j (iteratedFDeriv ℝ j φ ξ) p := ⟨_, fun _ _ => rfl⟩
  have hJsm : ∀ p, ContDiffOn ℝ ⊤ (J p) (boxDomain U e) := fun p => by
    rw [hJdef]; exact contDiffOn_iterPartial hO (hHsm p.1) j p.2
  have hJsa : ∀ p, IsSAFunOn₁ (boxDomain U e) (J p) := fun p => by
    rw [hJdef]; exact isSAFunOn₁_iterPartial hO (hHsm p.1) (hWsa p.1) j p.2
  have hunc : ∀ p, uncurryOpt (hfam p) = J p := fun p => funext fun v => by
    simp only [uncurryOpt, hfamdef, extendVal_eta]
  have hiter : ∀ p, ∀ ξ ∈ U, ∀ ε ∈ Ioo 0 e,
      evalCLM j (iteratedFDeriv ℝ j (fun y => W y ε) ξ) p = hfam p ξ ε := by
    intro p ξ hξ ε hε
    rw [hfamdef, hJdef, evalCLM_apply]
    exact iteratedFDeriv_eq_iterPartial hU hWsm hε p.1 j p.2 ξ hξ
  have hlimp : ∀ p, ∀ ξ ∈ Metric.ball x r, Tendsto (hfam p ξ) (𝓝[>] 0) (𝓝 (ψ p ξ)) := by
    intro p ξ hξ
    have h1 := ((evalCLM j).continuous.tendsto _).comp (hpt ξ hξ)
    have h2 := ((continuous_apply p).tendsto _).comp h1
    rw [hψdef]
    refine h2.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT he] with ε hε
    exact hiter p ξ (hball hξ) ε hε
  -- apply the strong form of Lemma 3.1 to every coordinate
  obtain ⟨x', r', -, hr', hb', -, -, hP⟩ := iterate_boxes (γ := κ × (Fin j → ι))
    (fun p s _ => ContDiffOn ℝ 1 (ψ p) s ∧
      TendstoUniformlyOn (fun ε ξ => hfam p ξ ε) (ψ p) (𝓝[>] 0) s ∧
      ∀ i, TendstoUniformlyOn (fun ε ξ => fderiv ℝ (fun ξ => hfam p ξ ε) ξ (Pi.single i 1))
        (fun ξ => fderiv ℝ (ψ p) ξ (Pi.single i 1)) (𝓝[>] 0) s)
    x r e
    (fun p s t _ _ ⟨h1, h2, h3⟩ hts _ _ => ⟨h1.mono hts, h2.mono hts, fun i => (h3 i).mono hts⟩)
    (fun p x₁ r₁ e₁ hr₁ hb₁ he₁ _ => by
      have hsub : Metric.ball x₁ r₁ ⊆ U := hb₁.trans hball
      have hsa' : IsSAFunOn₁ (boxDomain (Metric.ball x₁ r₁) e) (uncurryOpt (hfam p)) := by
        rw [hunc]
        exact isSAFunOn₁_mono (hJsa p) (isSA_boxDomain (isSA_ball _ _) e)
          (boxDomain_mono hsub le_rfl)
      have hsm' : ContDiffOn ℝ 1 (uncurryOpt (hfam p)) (boxDomain (Metric.ball x₁ r₁) e) := by
        rw [hunc]
        exact ((hJsm p).mono (boxDomain_mono hsub le_rfl)).of_le le_top
      obtain ⟨x₂, r₂, hr₂, hb₂, h1, h2, h3⟩ := exists_ball_C1_limit hS Metric.isOpen_ball
        ⟨x₁, Metric.mem_ball_self hr₁⟩ he hsa' hsm' (ψ p) (fun ξ hξ => hlimp p ξ (hb₁ hξ))
      exact ⟨x₂, r₂, e₁, hr₂, hb₂, he₁, le_rfl, h1, h2, h3⟩)
    hr he
  have hB'U : Metric.ball x' r' ⊆ U := hb'.trans hball
  -- uniform convergence of the `j`-th derivatives
  have hunifj : TendstoUniformlyOn (fun ε ξ => iteratedFDeriv ℝ j (fun y => W y ε) ξ)
      (iteratedFDeriv ℝ j φ) (𝓝[>] 0) (Metric.ball x' r') := by
    refine tendstoUniformlyOn_of_evalCLM fun p => ?_
    refine ((hP p).2.1.congr ?_).congr_right (fun ξ _ => hψdef p ξ)
    filter_upwards [Ioo_mem_nhdsGT he] with ε hε ξ hξ
    exact (hiter p ξ (hB'U hξ) ε hε).symm
  -- the `j`-th derivative of `φ` is `C¹`
  have hC1 : ContDiffOn ℝ 1 (iteratedFDeriv ℝ j φ) (Metric.ball x' r') :=
    contDiffOn_of_evalCLM fun p => ((hP p).1).congr fun ξ _ => (hψdef p ξ).symm
  have hφ' : ContDiffOn ℝ ((j + 1 : ℕ) : WithTop ℕ∞) φ (Metric.ball x' r') := by
    have hUD : UniqueDiffOn ℝ (Metric.ball x' r') := Metric.isOpen_ball.uniqueDiffOn
    have hφB := hφ.mono hb'
    rw [contDiffOn_nat_iff_continuousOn_differentiableOn hUD] at hφB ⊢
    have hEq : ∀ m : ℕ, EqOn (iteratedFDerivWithin ℝ m φ (Metric.ball x' r'))
        (iteratedFDeriv ℝ m φ) (Metric.ball x' r') :=
      fun m => iteratedFDerivWithin_of_isOpen m Metric.isOpen_ball
    refine ⟨fun m hm => ?_, fun m hm => ?_⟩
    · rcases Nat.lt_or_ge m (j + 1) with hlt | hge
      · exact hφB.1 m (by omega)
      · have hmj : m = j + 1 := by omega
        subst hmj
        have hc : ContinuousOn (iteratedFDeriv ℝ (j + 1) φ) (Metric.ball x' r') := by
          rw [iteratedFDeriv_succ_eq_comp_left]
          exact (LinearIsometryEquiv.continuous _).comp_continuousOn
            (hC1.continuousOn_fderiv_of_isOpen Metric.isOpen_ball le_rfl)
        exact hc.congr (hEq (j + 1))
    · rcases Nat.lt_or_ge m j with hlt | hge
      · exact hφB.2 m hlt
      · have hmj : m = j := by omega
        subst hmj
        exact (hC1.differentiableOn one_ne_zero).congr (hEq m)
  -- uniform convergence of the `(j+1)`-st derivatives
  have hunifj1 : TendstoUniformlyOn (fun ε ξ => iteratedFDeriv ℝ (j + 1) (fun y => W y ε) ξ)
      (iteratedFDeriv ℝ (j + 1) φ) (𝓝[>] 0) (Metric.ball x' r') := by
    refine tendstoUniformlyOn_of_evalCLM fun p' => ?_
    obtain ⟨k, m'⟩ := p'
    have h := (hP (k, Fin.tail m')).2.2 (m' 0)
    refine (h.congr ?_).congr_right ?_
    · filter_upwards [Ioo_mem_nhdsGT he] with ε hε ξ hξ
      have hξU := hB'U hξ
      have hdJ : DifferentiableAt ℝ (J (k, Fin.tail m')) (extendVal ε ξ) :=
        ((hJsm (k, Fin.tail m')).differentiableOn (by simp) (extendVal ε ξ)
          ⟨hξU, hε⟩).differentiableAt (hO.mem_nhds ⟨hξU, hε⟩)
      show fderiv ℝ (fun ξ => hfam (k, Fin.tail m') ξ ε) ξ (Pi.single (m' 0) 1) =
        evalCLM (j + 1) (iteratedFDeriv ℝ (j + 1) (fun y => W y ε) ξ) (k, m')
      rw [evalCLM_apply, iteratedFDeriv_eq_iterPartial hU hWsm hε k (j + 1) m' ξ hξU]
      simp only [hfamdef]
      rw [fderiv_slice_apply hdJ, extendVal_zero_single, hJdef]
      rfl
    · intro ξ hξ
      have hdT : DifferentiableAt ℝ (iteratedFDeriv ℝ j φ) ξ :=
        (hC1.differentiableOn one_ne_zero ξ hξ).differentiableAt
          (Metric.isOpen_ball.mem_nhds hξ)
      show fderiv ℝ (ψ (k, Fin.tail m')) ξ (Pi.single (m' 0) 1) =
        evalCLM (j + 1) (iteratedFDeriv ℝ (j + 1) φ ξ) (k, m')
      rw [evalCLM_apply, iteratedFDeriv_succ_apply_left, ← fderiv_eval_apply hdT]
      congr 1
      congr 1
      funext y
      rw [hψdef, evalCLM_apply]
      rfl
  exact ⟨x', r', hr', hb', hφ', hunifj, hunifj1⟩

end Deriv

/-- **Lemma 3.1.** -/
theorem derivatives (hS : SAFacts) (V : Set (ι → ℝ)) (hV : IsOpen V) (hVne : V.Nonempty)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) (g : (ι → ℝ) → ℝ → ℝ)
    (hg : IsSAFunOn₁ (boxDomain V ε₀) (uncurryOpt g))
    (g₀ : (ι → ℝ) → ℝ) (hg₀ : ContinuousOn g₀ V)
    (hlim : ∀ ξ ∈ V, Tendsto (g ξ) (𝓝[>] 0) (𝓝 (g₀ ξ))) :
    ∃ (ξ' : ι → ℝ) (r' ε' : ℝ), 0 < r' ∧ Metric.ball ξ' r' ⊆ V ∧ 0 < ε' ∧ ε' ≤ ε₀ ∧
      ContDiffOn ℝ 1 (fun p : (ι → ℝ) × ℝ => g p.1 p.2) (Metric.ball ξ' r' ×ˢ Ioo 0 ε') ∧
      ContDiffOn ℝ 1 g₀ (Metric.ball ξ' r') ∧
      ∀ i : ι, TendstoUniformlyOn (fun ε ξ => fderiv ℝ (fun ξ => g ξ ε) ξ (Pi.single i 1))
        (fun ξ => fderiv ℝ g₀ ξ (Pi.single i 1)) (𝓝[>] 0) (Metric.ball ξ' r') := by
  -- the continuity of `g₀` is not needed (`hg₀` is unused)
  obtain ⟨x₁, r₁, e₁, hr₁, hb₁, he₁, he₁le, han⟩ :=
    Deriv.exists_box_analytic hS hV hVne hε₀ hg
  have hsm : ContDiffOn ℝ ⊤ (uncurryOpt g) (boxDomain (Metric.ball x₁ r₁) e₁) :=
    fun v hv => (han v hv).contDiffAt.contDiffWithinAt
  have hsa : IsSAFunOn₁ (boxDomain (Metric.ball x₁ r₁) e₁) (uncurryOpt g) :=
    Deriv.isSAFunOn₁_mono hg (Deriv.isSA_boxDomain (isSA_ball _ _) e₁)
      (Deriv.boxDomain_mono hb₁ he₁le)
  obtain ⟨x, r, hr, hb, hC1, -, hu⟩ := Deriv.exists_ball_C1_limit hS Metric.isOpen_ball
    ⟨x₁, Metric.mem_ball_self hr₁⟩ he₁ hsa (hsm.of_le le_top) g₀ (fun ξ hξ => hlim ξ (hb₁ hξ))
  refine ⟨x, r, e₁, hr, hb.trans hb₁, he₁, he₁le, ?_, hC1, hu⟩
  have hmaps : MapsTo (fun p : (ι → ℝ) × ℝ => extendVal p.2 p.1) (Metric.ball x r ×ˢ Ioo 0 e₁)
      (boxDomain (Metric.ball x₁ r₁) e₁) := fun p hp => ⟨hb hp.1, hp.2⟩
  have h1 : ContDiffOn ℝ ⊤ (fun p : (ι → ℝ) × ℝ => g p.1 p.2) (Metric.ball x r ×ˢ Ioo 0 e₁) :=
    hsm.comp Deriv.contDiff_extendVal₂.contDiffOn hmaps
  exact h1.of_le le_top

/-- **Corollary 3.2.** -/
theorem derivatives_cor (hS : SAFacts) (V : Set (ι → ℝ)) (hV : IsOpen V) (hVne : V.Nonempty)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) (W : (ι → ℝ) → ℝ → (κ → ℝ))
    (hW : IsSAFunOn (boxDomain V ε₀) (uncurryOpt W))
    (φ : (ι → ℝ) → (κ → ℝ)) (hφ : ContinuousOn φ V)
    (hlim : ∀ ξ ∈ V, Tendsto (W ξ) (𝓝[>] 0) (𝓝 (φ ξ))) (D : ℕ) (hD : 1 ≤ D) :
    ∃ (ξ' : ι → ℝ) (r' ε' : ℝ), 0 < r' ∧ Metric.ball ξ' r' ⊆ V ∧ 0 < ε' ∧ ε' ≤ ε₀ ∧
      ContDiffOn ℝ 1 (fun p : (ι → ℝ) × ℝ => W p.1 p.2) (Metric.ball ξ' r' ×ˢ Ioo 0 ε') ∧
      (∀ ε ∈ Ioo 0 ε', ContDiffOn ℝ D (fun ξ => W ξ ε) (Metric.ball ξ' r')) ∧
      (∀ j ≤ D, ContinuousOn (fun p : (ι → ℝ) × ℝ => iteratedFDeriv ℝ j (fun ξ => W ξ p.2) p.1)
        (Metric.ball ξ' r' ×ˢ Ioo 0 ε')) ∧
      ContDiffOn ℝ D φ (Metric.ball ξ' r') ∧
      ∀ j ≤ D, TendstoUniformlyOn (fun ε ξ => iteratedFDeriv ℝ j (fun ξ => W ξ ε) ξ)
        (fun ξ => iteratedFDeriv ℝ j φ ξ) (𝓝[>] 0) (Metric.ball ξ' r') := by
  -- the hypothesis `1 ≤ D` is not needed
  obtain ⟨r₀, hr₀, hb₀⟩ := Metric.isOpen_iff.1 hV _ hVne.some_mem
  have hWk : ∀ k, IsSAFunOn₁ (boxDomain V ε₀) (fun v => uncurryOpt W v k) :=
    (isSAFunOn_iff_coord.1 hW).2
  -- a box on which all coordinates of `W` are analytic
  obtain ⟨x₁, r₁, e₁, hr₁, hb₁, he₁, he₁le, han⟩ := Deriv.iterate_boxes (γ := κ)
    (fun k s e => ∀ v ∈ boxDomain s e, AnalyticAt ℝ (fun v => uncurryOpt W v k) v)
    hVne.some r₀ ε₀
    (fun k s t e e' h hts _ hle v hv => h v (Deriv.boxDomain_mono hts hle hv))
    (fun k x r e hr hb he hle => by
      have hsub : Metric.ball x r ⊆ V := hb.trans hb₀
      obtain ⟨x', r', e', hr', hb', he', hle', han⟩ := Deriv.exists_box_analytic hS
        Metric.isOpen_ball ⟨x, Metric.mem_ball_self hr⟩ he (h := fun ξ ε => W ξ ε k)
        (Deriv.isSAFunOn₁_mono (hWk k) (Deriv.isSA_boxDomain (isSA_ball _ _) e)
          (Deriv.boxDomain_mono hsub hle))
      exact ⟨x', r', e', hr', hb', he', hle', han⟩)
    hr₀ hε₀
  have hb₁V : Metric.ball x₁ r₁ ⊆ V := hb₁.trans hb₀
  have hWsm : ContDiffOn ℝ ⊤ (uncurryOpt W) (boxDomain (Metric.ball x₁ r₁) e₁) :=
    fun v hv => (analyticAt_pi_iff.2 fun k => han k v hv).contDiffAt.contDiffWithinAt
  have hWsa : ∀ k, IsSAFunOn₁ (boxDomain (Metric.ball x₁ r₁) e₁) (fun v => uncurryOpt W v k) :=
    fun k => Deriv.isSAFunOn₁_mono (hWk k) (Deriv.isSA_boxDomain (isSA_ball _ _) e₁)
      (Deriv.boxDomain_mono hb₁V he₁le)
  -- induction on the order of the derivatives
  have hR : ∀ j : ℕ, ∃ (x : ι → ℝ) (r : ℝ), 0 < r ∧ Metric.ball x r ⊆ Metric.ball x₁ r₁ ∧
      ContDiffOn ℝ j φ (Metric.ball x r) ∧
      (∀ j' < j, TendstoUniformlyOn (fun ε ξ => iteratedFDeriv ℝ j' (fun y => W y ε) ξ)
        (iteratedFDeriv ℝ j' φ) (𝓝[>] 0) (Metric.ball x r)) ∧
      ∀ ξ ∈ Metric.ball x r, Tendsto (fun ε => iteratedFDeriv ℝ j (fun y => W y ε) ξ)
        (𝓝[>] 0) (𝓝 (iteratedFDeriv ℝ j φ ξ)) := by
    intro j
    induction j with
    | zero =>
      refine ⟨x₁, r₁, hr₁, subset_rfl, ?_, fun j' hj' => absurd hj' (Nat.not_lt_zero _), ?_⟩
      · exact contDiffOn_zero.2 (hφ.mono hb₁V)
      · intro ξ hξ
        simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
        exact ((LinearIsometryEquiv.continuous _).tendsto _).comp (hlim ξ (hb₁V hξ))
    | succ j ih =>
      obtain ⟨x, r, hr, hb, hφj, hunif, hpt⟩ := ih
      obtain ⟨x', r', hr', hb', hφj1, huj, huj1⟩ :=
        Deriv.cor_step hS Metric.isOpen_ball he₁ hWsa hWsm φ j hr hb hφj hpt
      refine ⟨x', r', hr', hb'.trans hb, hφj1, fun j' hj' => ?_,
        fun ξ hξ => huj1.tendsto_at hξ⟩
      rcases Nat.lt_or_ge j' j with h | h
      · exact (hunif j' h).mono hb'
      · have : j' = j := by omega
        subst this; exact huj
  obtain ⟨x, r, hr, hb, hφD, hunif, hpt⟩ := hR D
  obtain ⟨x', r', hr', hb', hφD1, hujD, -⟩ :=
    Deriv.cor_step hS Metric.isOpen_ball he₁ hWsa hWsm φ D hr hb hφD hpt
  have hbB : Metric.ball x' r' ⊆ Metric.ball x₁ r₁ := hb'.trans hb
  have hmaps : MapsTo (fun p : (ι → ℝ) × ℝ => extendVal p.2 p.1)
      (Metric.ball x' r' ×ˢ Ioo 0 e₁) (boxDomain (Metric.ball x₁ r₁) e₁) :=
    fun p hp => ⟨hbB hp.1, hp.2⟩
  refine ⟨x', r', e₁, hr', hbB.trans hb₁V, he₁, he₁le, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : ContDiffOn ℝ ⊤ (fun p : (ι → ℝ) × ℝ => W p.1 p.2)
        (Metric.ball x' r' ×ˢ Ioo 0 e₁) :=
      hWsm.comp Deriv.contDiff_extendVal₂.contDiffOn hmaps
    exact h1.of_le le_top
  · intro ε hε
    have h1 : ContDiffOn ℝ ⊤ (fun ξ => W ξ ε) (Metric.ball x' r') :=
      hWsm.comp (Deriv.contDiff_extendVal ε).contDiffOn (fun y hy => ⟨hbB hy, hε⟩)
    exact h1.of_le le_top
  · intro j _
    refine Deriv.continuousOn_of_evalCLM fun p => ?_
    have hJc : ContinuousOn (Deriv.iterPartial (fun v => uncurryOpt W v p.1) j p.2)
        (boxDomain (Metric.ball x₁ r₁) e₁) :=
      (Deriv.contDiffOn_iterPartial (Deriv.isOpen_boxDomain Metric.isOpen_ball e₁)
        (contDiffOn_pi.1 hWsm p.1) j p.2).continuousOn
    refine (hJc.comp Deriv.continuous_extendVal₂.continuousOn hmaps).congr ?_
    intro q hq
    exact Deriv.iteratedFDeriv_eq_iterPartial Metric.isOpen_ball hWsm hq.2 p.1 j p.2 q.1
      (hbB hq.1)
  · exact hφD1.of_le (by exact_mod_cast Nat.le_succ D)
  · intro j hj
    rcases Nat.lt_or_ge j D with h | h
    · exact (hunif j h).mono hb'
    · have : j = D := by omega
      subst this; exact hujD

end ClassSep
