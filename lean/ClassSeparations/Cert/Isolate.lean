import ClassSeparations.SA.Lemmas

/-!
# Isolating a certificate (§4.1, Lemma 4.1)

**Lemma 4.1.**  Let `U₁ ⊆ ℝⁿ` be an open ball and `F ⊆ U₁ × ℝᵏ` a semialgebraic set that
projects onto `U₁`.  Then there are a point `q₀ = (x₀, z₀) ∈ F`, an open neighborhood `N` of
`q₀`, a set `I` of coordinates of `ℝᵏ`, a ball `U₃ ⊆ U₁` about `x₀` and an analytic map
`ζ : U₃ → ℝᵏ` such that for every `x ∈ U₃` the point `(x, ζ(x))` is the only point `(x, z)` of
`F ∩ N` whose coordinates `z_I` equal those of `z₀`.

Here `x` ranges over `ℝ^α` and `z` over `ℝ^β` for finite types `α`, `β`.

## Proof

We do not follow the paper's proof (which uses Nash manifolds and tangent spaces).  Instead we
argue by induction on the number of coordinates of `z`, splitting off one coordinate `y` at a
time (`β = Option β'`, `y = z none`).  Let `G ⊆ ℝ^α × ℝ` be the projection of `F` to the
coordinates `(x, y)`.

* If `G` has nonempty interior, it contains a box `ball x₁ ε × {c}`.  We fix `y = c` (so the
  coordinate `none` belongs to `I`) and apply the induction hypothesis to the slice `y = c`.
* Otherwise, by (S4)(c), the fibers `G_x` are finite for `x` in a nonempty open set, so by
  (S5) the set `G` is, over a ball, the union of the graphs of continuous semialgebraic
  functions `λ₁ < ⋯ < λ_q`.  Shrinking the ball (S8) we may assume `λ₁` analytic.  We apply
  the induction hypothesis to the slice `y = λ₁(x)`; the neighborhood condition `y < λᵢ(x)`
  (`i ≠ 1`) forces `y = λ₁(x)` for points of `F`.
-/

noncomputable section

open Set Filter Topology

namespace ClassSep

section IsolateAux

variable {α : Type} [Fintype α]

/-! ### Small facts about `extendVal` -/

theorem extendVal_none_some {β : Type} (z : Option β → ℝ) :
    extendVal (z none) (z ∘ some) = z := by
  funext o; cases o <;> rfl

theorem eq_extendVal_iff {β : Type} (a : ℝ) (v : β → ℝ) (z : Option β → ℝ) :
    z = extendVal a v ↔ z none = a ∧ z ∘ some = v := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩; rw [← h1, ← h2, extendVal_none_some]

/-! ### Semialgebraicity of the auxiliary sets -/

/-- Fibers of semialgebraic sets are semialgebraic. -/
theorem isSA_fiberOver {γ δ : Type} {A : Set (γ ⊕ δ → ℝ)} (hA : IsSA A) (c : δ → ℝ) :
    IsSA (fiberOver A c) := by
  have := hA.preimage_poly
    (Sum.elim (fun g => MvPolynomial.X g) (fun d => MvPolynomial.C (c d)) :
      γ ⊕ δ → MvPolynomial γ ℝ)
  convert this using 1
  ext x
  simp only [fiberOver, Set.mem_ofPred_eq]
  have : (fun i => MvPolynomial.eval x
      ((Sum.elim (fun g => MvPolynomial.X g) (fun d => MvPolynomial.C (c d)) :
        γ ⊕ δ → MvPolynomial γ ℝ) i)) = Sum.elim x c := by
    funext i; rcases i with g | d <;> simp
  rw [this]

omit [Fintype α] in
/-- Substituting a constant for the coordinate `none`. -/
theorem isSA_subst_const {β : Type} {F : Set (α ⊕ Option β → ℝ)} (hF : IsSA F) (c : ℝ) :
    IsSA {v : α ⊕ β → ℝ | Sum.elim (v ∘ Sum.inl) (extendVal c (v ∘ Sum.inr)) ∈ F} := by
  let σ : α ⊕ Option β → MvPolynomial (α ⊕ β) ℝ :=
    Sum.elim (fun a => MvPolynomial.X (Sum.inl a))
      (fun o => o.elim (MvPolynomial.C c) (fun b => MvPolynomial.X (Sum.inr b)))
  have := hF.preimage_poly σ
  convert this using 1
  ext v
  simp only [Set.mem_ofPred_eq]
  have : (fun i => MvPolynomial.eval v (σ i)) =
      Sum.elim (v ∘ Sum.inl) (extendVal c (v ∘ Sum.inr)) := by
    funext i; rcases i with a | _ | b <;> simp [σ, extendVal]
  rw [this]

omit [Fintype α] in
/-- Substituting a semialgebraic function of `x` for the coordinate `none`. -/
theorem isSA_subst_fun {β : Type} {F : Set (α ⊕ Option β → ℝ)} (hF : IsSA F)
    {D : Set (α → ℝ)} {g : (α → ℝ) → ℝ} (hg : IsSAFunOn₁ D g) :
    IsSA {v : α ⊕ β → ℝ | v ∘ Sum.inl ∈ D ∧
      Sum.elim (v ∘ Sum.inl) (extendVal (g (v ∘ Sum.inl)) (v ∘ Sum.inr)) ∈ F} := by
  obtain ⟨-, hΓ⟩ := hg
  let f₁ : α ⊕ Unit → Option (α ⊕ β) := Sum.elim (fun a => some (Sum.inl a)) (fun _ => none)
  let f₂ : α ⊕ Option β → Option (α ⊕ β) :=
    Sum.elim (fun a => some (Sum.inl a)) (fun o => o.elim none (fun b => some (Sum.inr b)))
  have h := ((hΓ.preimage_comp f₁).inter (hF.preimage_comp f₂)).exists_option
  convert h using 1
  ext v
  have e1 : ∀ a : ℝ, extendVal a v ∘ f₁ = Sum.elim (v ∘ Sum.inl) (fun _ => a) := by
    intro a; funext i; rcases i with x | u <;> rfl
  have e2 : ∀ a : ℝ, extendVal a v ∘ f₂ = Sum.elim (v ∘ Sum.inl) (extendVal a (v ∘ Sum.inr)) := by
    intro a; funext i; rcases i with x | _ | b <;> rfl
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, e1, e2, Sum.elim_comp_inl, Sum.elim_comp_inr]
  constructor
  · rintro ⟨hD, hv⟩
    exact ⟨g (v ∘ Sum.inl), ⟨hD, rfl⟩, hv⟩
  · rintro ⟨a, ⟨hD, ha⟩, hv⟩
    have ha' : g (v ∘ Sum.inl) = a := congrFun ha ()
    rw [ha']
    exact ⟨hD, hv⟩

/-! ### The dichotomy: a box, or finite fibers -/

/-- A semialgebraic `E ⊆ ℝ^α × ℝ` either contains a box `ball x₁ ε × {c}`, or its fibers over
the points of some nonempty open subset of a given nonempty open `V` are finite. -/
theorem box_or_finite_fibers (hS : SAFacts) {E : Set (Option α → ℝ)} (hE : IsSA E)
    {V : Set (α → ℝ)} (hV : IsOpen V) (hVne : V.Nonempty) :
    (∃ (x₁ : α → ℝ) (c ε : ℝ), 0 < ε ∧ ∀ x ∈ Metric.ball x₁ ε, extendVal c x ∈ E) ∨
    (∃ V' ⊆ V, IsOpen V' ∧ V'.Nonempty ∧ ∀ x ∈ V', {y : ℝ | extendVal y x ∈ E}.Finite) := by
  let g : Option α → Unit ⊕ α := fun o => o.elim (Sum.inl ()) Sum.inr
  have hg : ∀ (y : ℝ) (x : α → ℝ), Sum.elim (fun _ : Unit => y) x ∘ g = extendVal y x := by
    intro y x; funext o; cases o <;> rfl
  set E' : Set (Unit ⊕ α → ℝ) := {v | v ∘ g ∈ E} with hE'_def
  have hE' : IsSA E' := hE.preimage_comp g
  have hmemE' : ∀ (y : ℝ) (x : α → ℝ),
      Sum.elim (fun _ : Unit => y) x ∈ E' ↔ extendVal y x ∈ E := by
    intro y x; simp only [E', Set.mem_ofPred_eq, hg]
  by_cases hint : (interior E').Nonempty
  · left
    obtain ⟨w, hw⟩ := hint
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior w hw
    refine ⟨w ∘ Sum.inr, w (Sum.inl ()), ε, hε, fun x hx => ?_⟩
    rw [← hmemE']
    apply interior_subset
    apply hball
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    rintro (u | a)
    · simp [hε]
    · exact lt_of_le_of_lt (dist_le_pi_dist x (w ∘ Sum.inr) a) hx
  · right
    have hdimE' : DimLT E' (Fintype.card (Unit ⊕ α)) := by
      rw [dimLT_card_iff]; exact Set.not_nonempty_iff_eq_empty.1 hint
    set S : Set (α → ℝ) := {x | DimGE (fiberOver E' x) 1} with hS_def
    have hSsa : IsSA S := isSA_dimGE_fiber hE' 1
    have hSdim : DimLT S (Fintype.card α) := by
      intro h
      apply hdimE'
      have := hS.fiber_dim_le E' 1 (Fintype.card α) hE' h
      rwa [Fintype.card_sum, Fintype.card_unit]
    have hdense := dense_compl_of_dimLT hS hSsa hSdim
    refine ⟨V ∩ (closure S)ᶜ, Set.inter_subset_left, hV.inter isClosed_closure.isOpen_compl,
      hdense.inter_open_nonempty V hV hVne, ?_⟩
    rintro x ⟨-, hx⟩
    have hxS : x ∉ S := fun h => hx (subset_closure h)
    have hfin : (fiberOver E' x).Finite :=
      (dimLT_one_iff_finite hS (isSA_fiberOver hE' x)).1 hxS
    have : {y : ℝ | extendVal y x ∈ E} = (fun y : ℝ => fun _ : Unit => y) ⁻¹' fiberOver E' x := by
      ext y; simp only [Set.mem_ofPred_eq, Set.mem_preimage, fiberOver, hmemE']
    rw [this]
    exact hfin.preimage (fun y₁ _ y₂ _ h => congrFun h ())

/-! ### The induction -/

/-- Conclusion of the isolation lemma in the form used in the induction on `β`: the set `I` of
fixed coordinates is a predicate `p`, the point `z₀` is `ζ x₀`, and analyticity is stated
coordinatewise. -/
def IsoConcl (α : Type) [Fintype α] (β : Type) (xc : α → ℝ) (rc : ℝ)
    (F : Set (α ⊕ β → ℝ)) : Prop :=
  ∃ (x₀ : α → ℝ) (N : Set (α ⊕ β → ℝ)) (p : β → Prop) (r₃ : ℝ) (ζ : (α → ℝ) → (β → ℝ)),
    IsOpen N ∧ 0 < r₃ ∧ Metric.ball x₀ r₃ ⊆ Metric.ball xc rc ∧
    (∀ b, AnalyticOnNhd ℝ (fun x => ζ x b) (Metric.ball x₀ r₃)) ∧
    ∀ x ∈ Metric.ball x₀ r₃, ∀ z : β → ℝ,
      (Sum.elim x z ∈ F ∩ N ∧ ∀ i, p i → z i = ζ x₀ i) ↔ z = ζ x

/-- The isolation lemma for a fixed type `β` of certificate coordinates. -/
def IsoP (α : Type) [Fintype α] (β : Type) : Prop :=
  ∀ (xc : α → ℝ) (rc : ℝ), 0 < rc → ∀ F : Set (α ⊕ β → ℝ), IsSA F →
    (∀ x ∈ Metric.ball xc rc, ∃ z, Sum.elim x z ∈ F) → IsoConcl α β xc rc F

theorem isoP_empty : IsoP α PEmpty := by
  intro xc rc hrc F _ hproj
  refine ⟨xc, Set.univ, fun _ => False, rc, fun _ => PEmpty.elim, isOpen_univ, hrc, subset_rfl,
    fun b => b.elim, ?_⟩
  intro x hx z
  have hz : ∀ z' : PEmpty → ℝ, z' = z := fun z' => funext fun b => b.elim
  obtain ⟨z', hz'⟩ := hproj x hx
  constructor
  · intro _; exact funext fun b => b.elim
  · intro _
    refine ⟨⟨hz z' ▸ hz', Set.mem_univ _⟩, fun i => i.elim⟩

theorem isoP_of_equiv {β β' : Type} (e : β ≃ β') (ih : IsoP α β) : IsoP α β' := by
  intro xc rc hrc F hF hproj
  set F₁ : Set (α ⊕ β → ℝ) := {v | v ∘ Sum.map id e.symm ∈ F} with hF₁_def
  have hF₁ : IsSA F₁ := hF.preimage_comp _
  have hmem : ∀ x (z : β → ℝ), Sum.elim x z ∈ F₁ ↔ Sum.elim x (z ∘ e.symm) ∈ F := by
    intro x z; simp only [F₁, Set.mem_ofPred_eq, Sum.elim_comp_map, Function.comp_id]
  obtain ⟨x₀, N, p, r₃, ζ, hN, hr₃, hsub, han, hiff⟩ := ih xc rc hrc F₁ hF₁ (by
    intro x hx
    obtain ⟨z, hz⟩ := hproj x hx
    refine ⟨z ∘ e, (hmem x _).2 ?_⟩
    have : z ∘ e ∘ e.symm = z := by funext b; simp
    rwa [Function.comp_assoc, this])
  refine ⟨x₀, {v | v ∘ Sum.map id e ∈ N}, fun i => p (e.symm i), r₃, fun x => ζ x ∘ e.symm,
    hN.preimage (continuous_pi fun _ => continuous_apply _), hr₃, hsub,
    fun b => han (e.symm b), ?_⟩
  intro x hx z
  have h := hiff x hx (z ∘ e)
  have h1 : Sum.elim x (z ∘ e) ∈ F₁ ↔ Sum.elim x z ∈ F := by
    rw [hmem]
    have : z ∘ e ∘ e.symm = z := by funext b; simp
    rw [Function.comp_assoc, this]
  have h2 : (∀ i, p (e.symm i) → z i = (ζ x₀ ∘ e.symm) i) ↔
      (∀ i, p i → (z ∘ e) i = ζ x₀ i) := by
    rw [← e.forall_congr_right]
    simp
  rw [Equiv.eq_comp_symm, ← h, Set.mem_inter_iff, Set.mem_inter_iff, h1, h2]
  simp only [Set.mem_ofPred_eq, Sum.elim_comp_map, Function.comp_id]

omit [Fintype α] in
/-- Open sets of the form `{(x, w) : x ∈ B, w_j < g(x)}` with `g` continuous on `B`. -/
theorem isOpen_lt_fun {γ : Type} {B : Set (α → ℝ)} (hB : IsOpen B) {g : (α → ℝ) → ℝ}
    (hg : ContinuousOn g B) (j : γ) :
    IsOpen {v : α ⊕ γ → ℝ | v ∘ Sum.inl ∈ B ∧ v (Sum.inr j) < g (v ∘ Sum.inl)} := by
  have hπ : Continuous fun v : α ⊕ γ → ℝ => v ∘ Sum.inl :=
    continuous_pi fun _ => continuous_apply _
  have hU : IsOpen ((fun v : α ⊕ γ → ℝ => v ∘ Sum.inl) ⁻¹' B) := hB.preimage hπ
  have hcont : ContinuousOn (fun v : α ⊕ γ → ℝ => g (v ∘ Sum.inl) - v (Sum.inr j))
      ((fun v : α ⊕ γ → ℝ => v ∘ Sum.inl) ⁻¹' B) :=
    (hg.comp hπ.continuousOn fun v hv => hv).sub (continuous_apply _).continuousOn
  convert hcont.isOpen_inter_preimage hU (isOpen_Ioi (a := (0 : ℝ))) using 1
  ext v
  simp [sub_pos]

/-- The induction step, first case: the projection `G` contains a box. -/
theorem isoConcl_option_box {β : Type} (ih : IsoP α β) {xc : α → ℝ} {rc : ℝ}
    {F : Set (α ⊕ Option β → ℝ)} (hF : IsSA F) {x₁ : α → ℝ} {c ε : ℝ} (hε : 0 < ε)
    (hbox : ∀ x ∈ Metric.ball x₁ ε, x ∈ Metric.ball xc rc ∧
      ∃ z' : β → ℝ, Sum.elim x (extendVal c z') ∈ F) :
    IsoConcl α (Option β) xc rc F := by
  set Fc : Set (α ⊕ β → ℝ) := {v | Sum.elim (v ∘ Sum.inl) (extendVal c (v ∘ Sum.inr)) ∈ F}
    with hFc_def
  have hFc : IsSA Fc := isSA_subst_const hF c
  have hmem : ∀ x (z' : β → ℝ), Sum.elim x z' ∈ Fc ↔ Sum.elim x (extendVal c z') ∈ F := by
    intro x z'; simp only [Fc, Set.mem_ofPred_eq, Sum.elim_comp_inl, Sum.elim_comp_inr]
  obtain ⟨x₀, N', p', r₃, ζ', hN', hr₃, hsub, han, hiff⟩ := ih x₁ ε hε Fc hFc
    (fun x hx => (hbox x hx).2.imp fun z' hz' => (hmem x z').2 hz')
  refine ⟨x₀, {v | v ∘ Sum.map id some ∈ N'}, fun o => o.elim True p', r₃,
    fun x => extendVal c (ζ' x), hN'.preimage (continuous_pi fun _ => continuous_apply _),
    hr₃, fun x hx => (hbox x (hsub hx)).1, ?_, ?_⟩
  · intro o
    cases o with
    | none => exact analyticOnNhd_const
    | some b => exact han b
  · intro x hx z
    have hN'mem : Sum.elim x z ∘ Sum.map id some = Sum.elim x (z ∘ some) := by
      rw [Sum.elim_comp_map, Function.comp_id]
    rw [eq_extendVal_iff, ← hiff x hx (z ∘ some)]
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, hN'mem, hmem]
    constructor
    · rintro ⟨⟨hzF, hzN⟩, hp⟩
      have hc : z none = c := hp none trivial
      refine ⟨hc, ⟨?_, hzN⟩, fun i hi => hp (some i) hi⟩
      rw [← hc, extendVal_none_some]; exact hzF
    · rintro ⟨hc, ⟨hzF, hzN⟩, hp⟩
      refine ⟨⟨?_, hzN⟩, ?_⟩
      · rw [← hc, extendVal_none_some] at hzF; exact hzF
      · intro o ho
        cases o with
        | none => exact hc
        | some i => exact hp i ho

/-- The induction step, second case: over a ball, the projection `G` is the union of the
graphs of continuous semialgebraic functions `lam 0 < ⋯ < lam (q-1)`. -/
theorem isoConcl_option_graph (hS : SAFacts) {β : Type} (ih : IsoP α β) {xc : α → ℝ} {rc : ℝ}
    {F : Set (α ⊕ Option β → ℝ)} (hF : IsSA F) {x₂ : α → ℝ} {r₂ : ℝ} (hr₂ : 0 < r₂)
    (hsub₂: Metric.ball x₂ r₂ ⊆ Metric.ball xc rc) {q : ℕ} (lam : Fin q → (α → ℝ) → ℝ)
    (hq : 0 < q)
    (hlam : ∀ i, IsSAFunOn₁ (Metric.ball x₂ r₂) (lam i) ∧
      ContinuousOn (lam i) (Metric.ball x₂ r₂))
    (hmono : ∀ x ∈ Metric.ball x₂ r₂, StrictMono fun i => lam i x)
    (hfib : ∀ x ∈ Metric.ball x₂ r₂, ∀ y : ℝ,
      (∃ z' : β → ℝ, Sum.elim x (extendVal y z') ∈ F) ↔ ∃ i, lam i x = y) :
    IsoConcl α (Option β) xc rc F := by
  set i₀ : Fin q := ⟨0, hq⟩ with hi₀
  have hi₀lt : ∀ i : Fin q, i ≠ i₀ → i₀ < i := by
    intro i hi
    rw [Fin.lt_def]
    have : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
    simp only [hi₀]
    omega
  -- shrink the ball so that `lam i₀` is analytic on it
  obtain ⟨Z, hZ, -, hZdim, hZan⟩ :=
    hS.nash (Metric.ball x₂ r₂) (lam i₀) Metric.isOpen_ball (hlam i₀).1
  have hdense := dense_compl_of_dimLT hS hZ hZdim
  have hO : IsOpen (Metric.ball x₂ r₂ ∩ (closure Z)ᶜ) :=
    Metric.isOpen_ball.inter isClosed_closure.isOpen_compl
  obtain ⟨x₃, hx₃⟩ := hdense.inter_open_nonempty (Metric.ball x₂ r₂) Metric.isOpen_ball
    ⟨x₂, Metric.mem_ball_self hr₂⟩
  obtain ⟨r₃', hr₃', hball₃⟩ := Metric.isOpen_iff.1 hO x₃ hx₃
  have hsub₃ : Metric.ball x₃ r₃' ⊆ Metric.ball x₂ r₂ := fun x hx => (hball₃ hx).1
  have hanL : AnalyticOnNhd ℝ (lam i₀) (Metric.ball x₃ r₃') := fun x hx =>
    hZan x ⟨(hball₃ hx).1, fun hxZ => (hball₃ hx).2 (subset_closure hxZ)⟩
  -- the slice `y = lam i₀ x`
  set F'' : Set (α ⊕ β → ℝ) := {v | v ∘ Sum.inl ∈ Metric.ball x₃ r₃' ∧
    Sum.elim (v ∘ Sum.inl) (extendVal (lam i₀ (v ∘ Sum.inl)) (v ∘ Sum.inr)) ∈ F} with hF''_def
  have hF'' : IsSA F'' :=
    isSA_subst_fun hF (IsSAFunOn.mono (hlam i₀).1 (isSA_ball x₃ r₃') hsub₃)
  have hmem'' : ∀ x (z' : β → ℝ), Sum.elim x z' ∈ F'' ↔
      x ∈ Metric.ball x₃ r₃' ∧ Sum.elim x (extendVal (lam i₀ x) z') ∈ F := by
    intro x z'; simp only [F'', Set.mem_ofPred_eq, Sum.elim_comp_inl, Sum.elim_comp_inr]
  have hproj'' : ∀ x ∈ Metric.ball x₃ r₃', ∃ z', Sum.elim x z' ∈ F'' := by
    intro x hx
    obtain ⟨z', hz'⟩ := (hfib x (hsub₃ hx) (lam i₀ x)).2 ⟨i₀, rfl⟩
    exact ⟨z', (hmem'' x z').2 ⟨hx, hz'⟩⟩
  obtain ⟨x₀, N', p', r₃, ζ', hN', hr₃, hsub, han, hiff⟩ := ih x₃ r₃' hr₃' F'' hF'' hproj''
  -- the neighborhood
  let C : Fin q → Set (α ⊕ Option β → ℝ) := fun i =>
    {v | v ∘ Sum.inl ∈ Metric.ball x₂ r₂ ∧ (i = i₀ ∨ v (Sum.inr none) < lam i (v ∘ Sum.inl))}
  have hC : ∀ i, IsOpen (C i) := by
    intro i
    by_cases h : i = i₀
    · have : C i = (fun v : α ⊕ Option β → ℝ => v ∘ Sum.inl) ⁻¹' Metric.ball x₂ r₂ := by
        ext v; simp [C, h]
      rw [this]
      exact Metric.isOpen_ball.preimage (continuous_pi fun _ => continuous_apply _)
    · have : C i = {v : α ⊕ Option β → ℝ | v ∘ Sum.inl ∈ Metric.ball x₂ r₂ ∧
          v (Sum.inr none) < lam i (v ∘ Sum.inl)} := by
        ext v; simp [C, h]
      rw [this]
      exact isOpen_lt_fun Metric.isOpen_ball (hlam i).2 none
  set N : Set (α ⊕ Option β → ℝ) := {v | v ∘ Sum.map id some ∈ N'} ∩ ⋂ i, C i with hN_def
  have hNopen : IsOpen N :=
    (hN'.preimage (continuous_pi fun _ => continuous_apply _)).inter (isOpen_iInter_of_finite hC)
  refine ⟨x₀, N, fun o => o.elim False p', r₃, fun x => extendVal (lam i₀ x) (ζ' x), hNopen,
    hr₃, hsub.trans (hsub₃.trans hsub₂), ?_, ?_⟩
  · intro o
    cases o with
    | none => exact hanL.mono hsub
    | some b => exact han b
  · intro x hx z
    have hx₃ : x ∈ Metric.ball x₃ r₃' := hsub hx
    have hx₂ : x ∈ Metric.ball x₂ r₂ := hsub₃ hx₃
    have hN'mem : Sum.elim x z ∘ Sum.map id some = Sum.elim x (z ∘ some) := by
      rw [Sum.elim_comp_map, Function.comp_id]
    have hCmem : ∀ i, Sum.elim x z ∈ C i ↔ (i = i₀ ∨ z none < lam i x) := by
      intro i
      simp only [C, Set.mem_ofPred_eq, Sum.elim_comp_inl, Sum.elim_inr]
      exact and_iff_right hx₂
    rw [eq_extendVal_iff, ← hiff x hx (z ∘ some)]
    simp only [N, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq, hN'mem, hCmem, hmem'']
    constructor
    · rintro ⟨⟨hzF, hzN, hzC⟩, hp⟩
      have hz0 : z none = lam i₀ x := by
        obtain ⟨i, hi⟩ := (hfib x hx₂ (z none)).1 ⟨z ∘ some, by rw [extendVal_none_some]; exact hzF⟩
        by_cases h : i = i₀
        · rw [← hi, h]
        · rcases hzC i with h' | h'
          · exact absurd h' h
          · rw [hi] at h'; exact absurd h' (lt_irrefl _)
      refine ⟨hz0, ⟨⟨hx₃, ?_⟩, hzN⟩, fun i hi => hp (some i) hi⟩
      rw [← hz0, extendVal_none_some]; exact hzF
    · rintro ⟨hz0, ⟨⟨-, hzF⟩, hzN⟩, hp⟩
      rw [← hz0, extendVal_none_some] at hzF
      refine ⟨⟨hzF, hzN, fun i => ?_⟩, ?_⟩
      · by_cases h : i = i₀
        · exact Or.inl h
        · right; rw [hz0]; exact hmono x hx₂ (hi₀lt i h)
      · intro o ho
        cases o with
        | none => exact ho.elim
        | some i => exact hp i ho

theorem isoP_option (hS : SAFacts) {β : Type} [Fintype β] (ih : IsoP α β) :
    IsoP α (Option β) := by
  intro xc rc hrc F hF hproj
  set G : Set (Option α → ℝ) := {w | w ∘ some ∈ Metric.ball xc rc ∧
    ∃ z' : β → ℝ, Sum.elim (w ∘ some) (extendVal (w none) z') ∈ F} with hG_def
  have hG : IsSA G := by
    let h : α ⊕ Option β → Option α ⊕ β :=
      Sum.elim (fun a => Sum.inl (some a)) (fun o => o.elim (Sum.inl none) Sum.inr)
    have h1 := (isSA_ball xc rc).preimage_comp (some : α → Option α)
    have h2 := (hF.preimage_comp h).exists_sum (γ := β)
    convert h1.inter h2 using 1
    ext w
    simp only [G, Set.mem_ofPred_eq, Set.mem_inter_iff]
    apply and_congr Iff.rfl
    apply exists_congr; intro z'
    have : Sum.elim w z' ∘ h = Sum.elim (w ∘ some) (extendVal (w none) z') := by
      funext i; rcases i with a | _ | b <;> rfl
    rw [this]
  have hGmem : ∀ (y : ℝ) (x : α → ℝ), extendVal y x ∈ G ↔
      x ∈ Metric.ball xc rc ∧ ∃ z' : β → ℝ, Sum.elim x (extendVal y z') ∈ F :=
    fun y x => Iff.rfl
  rcases box_or_finite_fibers hS hG Metric.isOpen_ball ⟨xc, Metric.mem_ball_self hrc⟩ with
    ⟨x₁, c, ε, hε, hbox⟩ | ⟨V', hV'sub, hV', hV'ne, hfin⟩
  · exact isoConcl_option_box ih hF hε fun x hx => (hGmem c x).1 (hbox x hx)
  · have hne : ∀ x ∈ V', {y : ℝ | extendVal y x ∈ G}.Nonempty := by
      intro x hx
      obtain ⟨z, hz⟩ := hproj x (hV'sub hx)
      refine ⟨z none, (hGmem _ x).2 ⟨hV'sub hx, z ∘ some, ?_⟩⟩
      rw [extendVal_none_some]; exact hz
    obtain ⟨x₂, r₂, hr₂, hsub₂, q, lam, hq, hlam, hmono, hfib⟩ :=
      hS.finite_fibers G V' hG hV' hV'ne (fun x hx => ⟨hfin x hx, hne x hx⟩)
    refine isoConcl_option_graph hS ih hF hr₂ (hsub₂.trans hV'sub) lam hq hlam hmono ?_
    intro x hx y
    have h := Set.ext_iff.1 (hfib x hx) y
    simp only [Set.mem_ofPred_eq, Set.mem_range] at h
    rw [← h, hGmem]
    exact ⟨fun h' => ⟨hV'sub (hsub₂ hx), h'⟩, fun h' => h'.2⟩

theorem isoP_all (hS : SAFacts) (β : Type) [Fintype β] : IsoP α β := by
  refine Fintype.induction_empty_option (P := fun β _ => IsoP α β) ?_ ?_ ?_ β
  · intro β β' _ e h; exact isoP_of_equiv e h
  · exact isoP_empty
  · intro β _ h; exact isoP_option hS h

end IsolateAux

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- **Lemma 4.1 (isolating a certificate).** -/
theorem isolate (hS : SAFacts) (xc : α → ℝ) (rc : ℝ) (hrc : 0 < rc)
    (F : Set (α ⊕ β → ℝ)) (hF : IsSA F)
    (hFsub : ∀ v ∈ F, v ∘ Sum.inl ∈ Metric.ball xc rc)
    (hproj : ∀ x ∈ Metric.ball xc rc, ∃ z, Sum.elim x z ∈ F) :
    ∃ (x₀ : α → ℝ) (z₀ : β → ℝ) (N : Set (α ⊕ β → ℝ)) (I : Finset β) (r₃ : ℝ)
      (ζ : (α → ℝ) → (β → ℝ)),
      Sum.elim x₀ z₀ ∈ F ∧ IsOpen N ∧ Sum.elim x₀ z₀ ∈ N ∧ 0 < r₃ ∧
      Metric.ball x₀ r₃ ⊆ Metric.ball xc rc ∧ ζ x₀ = z₀ ∧
      AnalyticOnNhd ℝ ζ (Metric.ball x₀ r₃) ∧
      ∀ x ∈ Metric.ball x₀ r₃, ∀ z : β → ℝ,
        (Sum.elim x z ∈ F ∩ N ∧ ∀ i ∈ I, z i = z₀ i) ↔ z = ζ x := by
  classical
  -- the hypothesis `hFsub` is not needed
  obtain ⟨x₀, N, p, r₃, ζ, hN, hr₃, hsub, han, hiff⟩ := isoP_all hS β xc rc hrc F hF hproj
  have hx₀ : x₀ ∈ Metric.ball x₀ r₃ := Metric.mem_ball_self hr₃
  have h0 := (hiff x₀ hx₀ (ζ x₀)).2 rfl
  refine ⟨x₀, ζ x₀, N, Finset.univ.filter p, r₃, ζ, h0.1.1, hN, h0.1.2, hr₃, hsub, rfl,
    analyticOnNhd_pi_iff.2 han, ?_⟩
  intro x hx z
  rw [← hiff x hx z]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

end ClassSep
