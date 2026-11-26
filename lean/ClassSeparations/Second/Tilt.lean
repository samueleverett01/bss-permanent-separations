import ClassSeparations.Second.EnvBasic

/-!
# A generic linear term (§6.5, Lemma 6.7)

By (S8) there is an open dense semialgebraic `Reg ⊆ 𝒪` on which `e` is Nash; `Sing = 𝒪 \ Reg`
has dimension `≤ n + κ - 1`.  The map `G(x, c) = (x, ∇_c e(x; c))` is semialgebraic on `𝒪`
(Lemma 6.4 (a)), and `Bad`, the union of `G(Sing)` and of the critical values of `G` on `Reg`,
has dimension `≤ n + κ - 1` by (S8) and (S6).

**Lemma 6.7.**  There are `â ∈ ℝ^κ`, a ball `V ⊆ int K'` and `ϑ₁ > 0` such that for `x ∈ V` and
`0 < ϑ < ϑ₁` every `c ∈ int B̄` with `∇_c e(x; c) = ϑ â` has `(x, c) ∈ Reg` and
`∇²_c e(x; c)` invertible.

Here `𝒪 = int K' × int B̄`, `K'` is any ball in `K`; `(x, c) ∈ Reg` is expressed by analyticity
of `e` at `(x, c)`, and the Hessian in `c` by iterated partial derivatives `pd`.

*Proof.*  The set `A = {(x, ϑ, â) : ϑ > 0, (x, ϑ â) ∈ Bad}` has empty interior (a slice
`ϑ = ϑ₀` of an open subset of `A` maps onto an open subset of `Bad`).  By (S4)(c) some `â` has
a fiber `F = A_â` with empty interior in `(x, ϑ)`-space.  By (S3) every `x` has `F_x` either
containing or missing an interval `(0, e)`; the first alternative cannot hold on an open set
(it would give a box inside `F`), so the second holds on an open set, and then (S5) gives a box
`V × (0, ϑ₁)` disjoint from `F`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open MvPolynomial Set Filter Topology

namespace ClassSep

open SecondAux

namespace SecondAux

variable {σ : Type} [Fintype σ]

theorem isSA_extendVal_mem {ι : Type} {F : Set (Option σ → ℝ)} (hF : IsSA F) (gt : ι)
    (gx : σ → ι) : IsSA {w : ι → ℝ | extendVal (w gt) (w ∘ gx) ∈ F} := by
  refine hF.preimage_polyFn (F := fun w => extendVal (w gt) (w ∘ gx)) fun o => ?_
  cases o with
  | none => exact FO.IsPolyFn.coord gt
  | some i => exact FO.IsPolyFn.coord (gx i)

/-- A box `V × (0, e₀)` on which a first-order property holds, from its validity for small
`t > 0` at every point of an open set (S5). -/
theorem exists_box (hS : SAFacts) {U : Set (σ → ℝ)} (hU : IsOpen U) (hUne : U.Nonempty)
    (hUsa : IsSA U) {F : Set (Option σ → ℝ)} (hF : IsSA F)
    (hP : ∀ x ∈ U, ∃ e > 0, ∀ t ∈ Ioo 0 e, extendVal t x ∈ F) :
    ∃ (x₀ : σ → ℝ) (r e₀ : ℝ), 0 < r ∧ Metric.ball x₀ r ⊆ U ∧ 0 < e₀ ∧
      ∀ x ∈ Metric.ball x₀ r, ∀ t ∈ Ioo 0 e₀, extendVal t x ∈ F := by
  set S : (σ → ℝ) → Set ℝ :=
    fun x => {e | 0 < e ∧ e ≤ 1 ∧ ∀ t, 0 < t → t < e → extendVal t x ∈ F} with hSdef
  set g : (σ → ℝ) → ℝ := fun x => sSup (S x) with hg
  have hbdd : ∀ x, BddAbove (S x) := fun x => ⟨1, fun e he => he.2.1⟩
  have hne : ∀ x ∈ U, (S x).Nonempty := by
    intro x hx
    obtain ⟨e, he, hPe⟩ := hP x hx
    refine ⟨min e 1, lt_min he one_pos, min_le_right _ _, fun t ht0 ht => ?_⟩
    exact hPe t ⟨ht0, ht.trans_le (min_le_left _ _)⟩
  have hpos : ∀ x ∈ U, 0 < g x := by
    intro x hx
    obtain ⟨e, he⟩ := hne x hx
    exact he.1.trans_le (le_csSup (hbdd x) he)
  have hgsa : IsSAFunOn₁ U g := by
    refine ⟨hUsa, ?_⟩
    have key : IsSA {v : σ ⊕ Unit → ℝ | v ∘ Sum.inl ∈ U ∧
        ((∀ e : ℝ, (0 < e ∧ e ≤ 1 ∧ ∀ t : ℝ, 0 < t → t < e →
            extendVal t (v ∘ Sum.inl) ∈ F) → e ≤ v (Sum.inr ())) ∧
         ∀ s' : ℝ, (∀ e : ℝ, (0 < e ∧ e ≤ 1 ∧ ∀ t : ℝ, 0 < t → t < e →
            extendVal t (v ∘ Sum.inl) ∈ F) → e ≤ s') → v (Sum.inr ()) ≤ s')} := by
      refine FO.isSA_and (hUsa.preimage_comp _) (FO.isSA_and ?_ ?_)
      · refine FO.isSA_forall_real (FO.isSA_imp (FO.isSA_and
          (FO.isSA_lt (FO.IsPolyFn.const 0) (FO.IsPolyFn.coord _))
          (FO.isSA_and (FO.isSA_le (FO.IsPolyFn.coord _) (FO.IsPolyFn.const 1))
            (FO.isSA_forall_real (FO.isSA_imp
              (FO.isSA_lt (FO.IsPolyFn.const 0) (FO.IsPolyFn.coord _))
              (FO.isSA_imp (FO.isSA_lt (FO.IsPolyFn.coord _) (FO.IsPolyFn.coord _))
                (isSA_extendVal_mem hF _ _)))))) ?_)
        exact FO.isSA_le (FO.IsPolyFn.coord _) (FO.IsPolyFn.coord _)
      · refine FO.isSA_forall_real (FO.isSA_imp ?_
          (FO.isSA_le (FO.IsPolyFn.coord _) (FO.IsPolyFn.coord _)))
        refine FO.isSA_forall_real (FO.isSA_imp (FO.isSA_and
          (FO.isSA_lt (FO.IsPolyFn.const 0) (FO.IsPolyFn.coord _))
          (FO.isSA_and (FO.isSA_le (FO.IsPolyFn.coord _) (FO.IsPolyFn.const 1))
            (FO.isSA_forall_real (FO.isSA_imp
              (FO.isSA_lt (FO.IsPolyFn.const 0) (FO.IsPolyFn.coord _))
              (FO.isSA_imp (FO.isSA_lt (FO.IsPolyFn.coord _) (FO.IsPolyFn.coord _))
                (isSA_extendVal_mem hF _ _)))))) ?_)
        exact FO.isSA_le (FO.IsPolyFn.coord _) (FO.IsPolyFn.coord _)
    convert key using 1
    ext v
    simp only [mem_ofPred_eq]
    constructor
    · rintro ⟨hx, hv⟩
      have hv' : g (v ∘ Sum.inl) = v (Sum.inr ()) := congrFun hv ()
      refine ⟨hx, fun e he => ?_, fun s' hs' => ?_⟩
      · rw [← hv']; exact le_csSup (hbdd _) he
      · rw [← hv']; exact csSup_le (hne _ hx) hs'
    · rintro ⟨hx, hub, hlub⟩
      refine ⟨hx, funext fun _ => ?_⟩
      exact le_antisymm (csSup_le (hne _ hx) hub) (hlub _ fun e he => le_csSup (hbdd _) he)
  obtain ⟨x₀, r, c, hr, hball, hc, hcg⟩ := exists_ball_lower_bound hS hU hUne hgsa hpos
  refine ⟨x₀, r, c, hr, hball, hc, fun x hx t ht => ?_⟩
  have hlt : t < sSup (S x) := ht.2.trans_le (hcg x hx)
  obtain ⟨e, he, hte⟩ := exists_lt_of_lt_csSup (hne x (hball hx)) hlt
  exact he.2.2 t ht.1 hte

end SecondAux

namespace SLData

variable {σ κ : Type} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ] {M : ℕ}
  {D : SLData σ κ M} {f : MvPolynomial σ ℝ} {yc : κ}

/-- **Lemma 6.7.** -/
theorem Good.tilt (hS : SAFacts) (hG : D.Good f yc) {x' : σ → ℝ} {ρ' : ℝ} (hρ' : 0 < ρ')
    (hball : Metric.ball x' ρ' ⊆ D.K) :
    ∃ (â : κ → ℝ) (xV : σ → ℝ) (rV ϑ₁ : ℝ), 0 < rV ∧ Metric.ball xV rV ⊆ Metric.ball x' ρ' ∧
      0 < ϑ₁ ∧ ∀ x ∈ Metric.ball xV rV, ∀ ϑ ∈ Ioo 0 ϑ₁, ∀ c ∈ D.Bo,
        (∀ k, D.grad x c k = ϑ * â k) →
        AnalyticAt ℝ D.envξ (Sum.elim x c) ∧
        IsUnit (Matrix.of fun k l : κ =>
          pd (pd D.envξ (Sum.inr k)) (Sum.inr l) (Sum.elim x c)).det := by
  classical
  -- the open set `𝒪 = int K' × int B̄`
  set O : Set (σ ⊕ κ → ℝ) :=
    {ξ | ξ ∘ Sum.inl ∈ Metric.ball x' ρ' ∧ ξ ∘ Sum.inr ∈ D.Bo} with hOdef
  have hcl : Continuous fun ξ : σ ⊕ κ → ℝ => ξ ∘ Sum.inl :=
    continuous_pi fun _ => continuous_apply _
  have hcr : Continuous fun ξ : σ ⊕ κ → ℝ => ξ ∘ Sum.inr :=
    continuous_pi fun _ => continuous_apply _
  have hOopen : IsOpen O := (Metric.isOpen_ball.preimage hcl).inter (isOpen_Bo.preimage hcr)
  have hOsa : IsSA O :=
    FO.isSA_and ((isSA_ball x' ρ').preimage_comp _)
      (FO.isSA_lt (isPolyFn_sqDist (fun k => FO.IsPolyFn.coord _)
        (fun k => FO.IsPolyFn.const _)) (FO.IsPolyFn.const _))
  have hOK : O ⊆ D.Kξ := fun ξ hξ => hball hξ.1
  -- (S8): `Reg` and `Sing`
  have hsa : IsSAFunOn₁ O D.envξ := IsSAFunOn.mono hG.isSAFunOn_envξ hOsa hOK
  obtain ⟨Z, hZ, -, hZdim, hZan⟩ := hS.nash O D.envξ hOopen hsa
  set Reg := O \ closure Z with hReg
  set Sing := O ∩ closure Z with hSing
  have hRegopen : IsOpen Reg := hOopen.sdiff isClosed_closure
  have hRegsa : IsSA Reg := hOsa.diff hZ.closure
  have hSingsa : IsSA Sing := hOsa.inter hZ.closure
  have hSingdim : DimLT Sing (Fintype.card (σ ⊕ κ)) :=
    (hS.closure_dimLT Z _ hZ hZdim).mono inter_subset_right
  have hRegan : ∀ ξ ∈ Reg, AnalyticAt ℝ D.envξ ξ := fun ξ hξ =>
    hZan ξ ⟨hξ.1, fun h => hξ.2 (subset_closure h)⟩
  -- the map `G(x, c) = (x, ∇_c e(x; c))`
  set G : (σ ⊕ κ → ℝ) → (σ ⊕ κ → ℝ) := fun ξ =>
    Sum.elim (ξ ∘ Sum.inl) (fun k => D.grad (ξ ∘ Sum.inl) (ξ ∘ Sum.inr) k) with hGdef
  have hGsa : IsSAFunOn O G := by
    refine isSAFunOn_iff_coord.2 ⟨hOsa, fun b => ?_⟩
    rcases b with i | k
    · have h := isSAFunOn_poly O hOsa
        (fun _ : Unit => (X (Sum.inl i) : MvPolynomial (σ ⊕ κ) ℝ))
      have e : (fun x (_ : Unit) => eval x (X (Sum.inl i) : MvPolynomial (σ ⊕ κ) ℝ)) =
          (fun x (_ : Unit) => G x (Sum.inl i)) := by
        funext x _; simp [hGdef]
      rw [e] at h
      exact h
    · exact IsSAFunOn.mono ((isSAFunOn_iff_coord.1 hG.isSAFunOn_grad).2 k) hOsa hOK
  have hGpt : ∀ ξ ∈ Reg, ∀ k, G ξ (Sum.inr k) = pd D.envξ (Sum.inr k) ξ := by
    intro ξ hξ k
    have hd : DifferentiableAt ℝ D.envξ (Sum.elim (ξ ∘ Sum.inl) (ξ ∘ Sum.inr)) := by
      rw [Sum.elim_comp_inl_inr]; exact (hRegan ξ hξ).differentiableAt
    have h1 := hG.grad_eq_pd (hball hξ.1.1) hd k
    rw [Sum.elim_comp_inl_inr] at h1
    exact h1
  have hGan : AnalyticOnNhd ℝ G Reg := by
    intro ξ hξ
    have e : G = fun x b => (fun b x => G x b) b x := rfl
    rw [e, analyticAt_pi_iff]
    intro b
    rcases b with i | k
    · exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : σ ⊕ κ => ℝ) (Sum.inl i)).analyticAt ξ
    · refine (analyticAt_pd (hRegan ξ hξ) (Sum.inr k)).congr ?_
      filter_upwards [hRegopen.mem_nhds hξ] with ξ' hξ'
      exact (hGpt ξ' hξ' k).symm
  -- (S6) and (S8): `Bad` is small
  obtain ⟨hCritsa, hCritdim⟩ := hS.sard Reg G hRegopen (IsSAFunOn.mono hGsa hRegsa sdiff_subset)
    hGan
  set Crit := {y | ∃ p ∈ Reg, G p = y ∧ ¬ Function.Surjective (fderiv ℝ G p)} with hCrit
  set Bad := G '' Sing ∪ Crit with hBad
  have hGSsa : IsSA (G '' Sing) := hGsa.image hSingsa inter_subset_left
  have hBadsa : IsSA Bad := hGSsa.union hCritsa
  have hBaddim : DimLT Bad (Fintype.card (σ ⊕ κ)) := by
    refine hS.union_dimLT _ _ _ hGSsa hCritsa (fun hge => ?_) hCritdim
    exact hSingdim (hS.dim_image Sing G _ (IsSAFunOn.mono hGsa hSingsa inter_subset_left) hge)
  -- the set `A = {(x, ϑ, â) : ϑ > 0, (x, ϑ â) ∈ Bad}` has empty interior
  set A : Set (Option σ ⊕ κ → ℝ) := {u | 0 < u (Sum.inl none) ∧
    Sum.elim (u ∘ Sum.inl ∘ some) (fun k => u (Sum.inl none) * u (Sum.inr k)) ∈ Bad} with hAdef
  have hAsa : IsSA A := by
    refine FO.isSA_and (FO.isSA_lt (FO.IsPolyFn.const 0) (FO.IsPolyFn.coord _)) ?_
    refine hBadsa.preimage_polyFn (F := fun u : Option σ ⊕ κ → ℝ =>
      Sum.elim (u ∘ Sum.inl ∘ some) (fun k => u (Sum.inl none) * u (Sum.inr k))) fun b => ?_
    rcases b with i | k
    · exact FO.IsPolyFn.coord _
    · exact (FO.IsPolyFn.coord _).mul (FO.IsPolyFn.coord _)
  have hAint : interior A = ∅ := by
    by_contra hne
    obtain ⟨u₀, hu₀⟩ := nonempty_iff_ne_empty.2 hne
    have hϑ₀ : 0 < u₀ (Sum.inl none) := (interior_subset hu₀).1
    set ϑ₀ := u₀ (Sum.inl none) with hϑ₀def
    set s : (σ ⊕ κ → ℝ) → (Option σ ⊕ κ → ℝ) := fun y =>
      Sum.elim (extendVal ϑ₀ (y ∘ Sum.inl)) (fun k => y (Sum.inr k) / ϑ₀) with hs
    have hscont : Continuous s := by
      refine continuous_pi fun b => ?_
      rcases b with o | k
      · cases o with
        | none => exact continuous_const
        | some i => exact continuous_apply _
      · exact (continuous_apply _).div_const _
    set y₀ : σ ⊕ κ → ℝ := Sum.elim (u₀ ∘ Sum.inl ∘ some) (fun k => ϑ₀ * u₀ (Sum.inr k))
      with hy₀
    have hsy₀ : s y₀ = u₀ := by
      funext b
      rcases b with o | k
      · cases o <;> rfl
      · simp only [hs, hy₀, Sum.elim_inr]
        field_simp
    have hsub : s ⁻¹' interior A ⊆ Bad := by
      intro y hy
      have hA := (interior_subset hy : s y ∈ A).2
      convert hA using 1
      funext b
      rcases b with i | k
      · rfl
      · simp only [hs, Sum.elim_inr, Sum.elim_inl, extendVal, Option.elim]
        field_simp
    apply hBaddim
    rw [dimGE_card_iff]
    refine ⟨y₀, interior_maximal hsub (isOpen_interior.preimage hscont) ?_⟩
    rw [mem_preimage, hsy₀]
    exact hu₀
  have hAdim : DimLT A (Fintype.card σ + 1 + Fintype.card κ) := by
    rw [show Fintype.card σ + 1 + Fintype.card κ = Fintype.card (Option σ ⊕ κ) by simp,
      dimLT_card_iff]
    exact hAint
  -- (S4)(c): a direction `â` whose fiber has empty interior
  obtain ⟨â, hâ⟩ : ∃ â : κ → ℝ, ¬ DimGE (fiberOver A â) (Fintype.card σ + 1) := by
    by_contra hall
    push Not at hall
    apply hAdim
    apply hS.fiber_dim_le A (Fintype.card σ + 1) (Fintype.card κ) hAsa
    rw [show {c | DimGE (fiberOver A c) (Fintype.card σ + 1)} = univ from
      eq_univ_of_forall hall, dimGE_card_iff, interior_univ]
    exact univ_nonempty
  set F := fiberOver A â with hFdef
  have hFsa : IsSA F := by
    refine hAsa.preimage_polyFn (F := fun v : Option σ → ℝ => Sum.elim v â) fun b => ?_
    rcases b with o | k
    · exact FO.IsPolyFn.coord _
    · exact FO.IsPolyFn.const _
  have hFint : interior F = ∅ := by
    have : DimLT F (Fintype.card (Option σ)) := by rw [Fintype.card_option]; exact hâ
    exact (dimLT_card_iff _).1 this
  -- (S3): each `F_x` contains or misses an interval `(0, e)`
  set G₁ : Set (σ → ℝ) := {x | ∃ e > 0, ∀ t ∈ Ioo 0 e, extendVal t x ∈ F} with hG₁
  set G₂ : Set (σ → ℝ) := {x | ∃ e > 0, ∀ t ∈ Ioo 0 e, extendVal t x ∈ Fᶜ} with hG₂
  have hGisa : ∀ F' : Set (Option σ → ℝ), IsSA F' →
      IsSA {x : σ → ℝ | ∃ e > 0, ∀ t ∈ Ioo 0 e, extendVal t x ∈ F'} := by
    intro F' hF'
    have key : IsSA {x : σ → ℝ | ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t → t < e →
        extendVal t x ∈ F'} :=
      FO.isSA_exists_real (FO.isSA_and (FO.isSA_lt (FO.IsPolyFn.const 0) (FO.IsPolyFn.coord _))
        (FO.isSA_forall_real (FO.isSA_imp (FO.isSA_lt (FO.IsPolyFn.const 0)
          (FO.IsPolyFn.coord _)) (FO.isSA_imp (FO.isSA_lt (FO.IsPolyFn.coord _)
            (FO.IsPolyFn.coord _)) (isSA_extendVal_mem hF' _ _)))))
    convert key using 1
    ext x
    simp only [mem_ofPred_eq, gt_iff_lt, mem_Ioo]
    exact exists_congr fun e => and_congr_right fun _ =>
      ⟨fun h t h0 h1 => h t ⟨h0, h1⟩, fun h t ht => h t ht.1 ht.2⟩
  have hcov : Metric.ball x' ρ' ⊆
      ⋃ b ∈ (Finset.univ : Finset Bool), (if b then G₁ else G₂) := by
    intro x _
    have hA1 : IsSA₁ {t | extendVal t x ∈ F} := by
      show IsSA {v : Unit → ℝ | extendVal (v ()) x ∈ F}
      refine hFsa.preimage_polyFn (F := fun v : Unit → ℝ => extendVal (v ()) x) fun o => ?_
      cases o with
      | none => exact FO.IsPolyFn.coord _
      | some i => exact FO.IsPolyFn.const _
    rcases germ_right hS hA1 0 with ⟨e, he, hsub⟩ | ⟨e, he, hdisj⟩
    · refine mem_iUnion₂.2 ⟨true, Finset.mem_univ _, e, he, fun t ht => ?_⟩
      exact hsub (by simpa using ht)
    · refine mem_iUnion₂.2 ⟨false, Finset.mem_univ _, e, he, fun t ht hF => ?_⟩
      exact Set.disjoint_left.1 hdisj (by simpa using ht) hF
  obtain ⟨b, -, hb⟩ := exists_interior_of_finite_cover hS (Finset.univ : Finset Bool)
    (fun b : Bool => if b then G₁ else G₂)
    (fun b _ => by
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte]; exact hGisa Fᶜ hFsa.compl
      · simp only [↓reduceIte]; exact hGisa F hFsa)
    Metric.isOpen_ball ⟨x', Metric.mem_ball_self hρ'⟩ hcov
  cases b with
  | true =>
    -- a box inside `F` would contradict `interior F = ∅`
    exfalso
    simp only [if_true] at hb
    obtain ⟨x₀, r, e₀, hr, hVU, he₀, hbox⟩ := exists_box hS isOpen_interior hb
      ((hGisa F hFsa).inter (isSA_ball _ _)).interior hFsa
      (fun x hx => (interior_subset hx).1)
    have hcs : Continuous fun v : Option σ → ℝ => v ∘ some :=
      continuous_pi fun _ => continuous_apply _
    have hboxopen : IsOpen {v : Option σ → ℝ | v ∘ some ∈ Metric.ball x₀ r ∧ v none ∈ Ioo 0 e₀} :=
      (Metric.isOpen_ball.preimage hcs).inter (isOpen_Ioo.preimage (continuous_apply none))
    have hboxsub : {v : Option σ → ℝ | v ∘ some ∈ Metric.ball x₀ r ∧ v none ∈ Ioo 0 e₀} ⊆ F := by
      intro v hv
      have := hbox (v ∘ some) hv.1 (v none) hv.2
      convert this using 1
      funext o
      cases o <;> rfl
    have hmem : extendVal (e₀ / 2) x₀ ∈ interior F :=
      interior_maximal hboxsub hboxopen ⟨Metric.mem_ball_self hr, half_pos he₀, half_lt_self he₀⟩
    rw [hFint] at hmem
    exact hmem
  | false =>
    simp only [Bool.false_eq_true, if_false] at hb
    obtain ⟨xV, rV, ϑ₁, hrV, hVU, hϑ₁, hbox⟩ := exists_box hS isOpen_interior hb
      ((hGisa Fᶜ hFsa.compl).inter (isSA_ball _ _)).interior hFsa.compl
      (fun x hx => (interior_subset hx).1)
    refine ⟨â, xV, rV, ϑ₁, hrV, fun x hx => (interior_subset (hVU hx)).2, hϑ₁, ?_⟩
    intro x hx ϑ hϑ c hc hgrad
    have hxB : x ∈ Metric.ball x' ρ' := (interior_subset (hVU hx)).2
    have hξO : Sum.elim x c ∈ O := ⟨hxB, hc⟩
    have hGξ : G (Sum.elim x c) = Sum.elim x (fun k => ϑ * â k) := by
      simp only [hGdef, Sum.elim_comp_inl, Sum.elim_comp_inr]
      congr 1
      funext k
      exact hgrad k
    have hnotBad : G (Sum.elim x c) ∉ Bad := by
      intro hBad'
      apply hbox x hx ϑ hϑ
      show Sum.elim (extendVal ϑ x) â ∈ A
      refine ⟨hϑ.1, ?_⟩
      rw [hGξ] at hBad'
      exact hBad'
    have hξReg : Sum.elim x c ∈ Reg :=
      ⟨hξO, fun hcl => hnotBad (Or.inl ⟨_, ⟨hξO, hcl⟩, rfl⟩)⟩
    have han := hRegan _ hξReg
    refine ⟨han, ?_⟩
    have hsurj : Function.Surjective (fderiv ℝ G (Sum.elim x c)) := by
      by_contra hns
      exact hnotBad (Or.inr ⟨_, hξReg, rfl, hns⟩)
    -- the derivative of `G` at `ξ`
    set ξ := Sum.elim x c with hξ
    set G' : (σ ⊕ κ → ℝ) → (σ ⊕ κ → ℝ) := fun ξ' b =>
      Sum.elim (fun i => ξ' (Sum.inl i)) (fun k => pd D.envξ (Sum.inr k) ξ') b with hG'
    have hGG' : G =ᶠ[𝓝 ξ] G' := by
      filter_upwards [hRegopen.mem_nhds hξReg] with ξ' hξ'
      funext b
      rcases b with i | k
      · rfl
      · exact hGpt ξ' hξ' k
    have hcomp : ∀ b, DifferentiableAt ℝ (fun ξ' => G' ξ' b) ξ := by
      intro b
      rcases b with i | k
      · exact differentiableAt_apply _ _
      · exact (analyticAt_pd han _).differentiableAt
    have hfd : fderiv ℝ G ξ = ContinuousLinearMap.pi fun b => fderiv ℝ (fun ξ' => G' ξ' b) ξ := by
      rw [hGG'.fderiv_eq]
      exact fderiv_pi hcomp
    set H : Matrix κ κ ℝ := Matrix.of fun k l => pd (pd D.envξ (Sum.inr k)) (Sum.inr l) ξ
      with hH
    have hmv : Function.Surjective H.mulVec := by
      intro v
      obtain ⟨h, hh⟩ := hsurj (Sum.elim 0 v)
      rw [hfd] at hh
      have h0 : ∀ i, h (Sum.inl i) = 0 := by
        intro i
        have := congrFun hh (Sum.inl i)
        simp only [ContinuousLinearMap.pi_apply, Sum.elim_inl, Pi.zero_apply, hG'] at this
        rw [(hasFDerivAt_apply (Sum.inl i) ξ).fderiv] at this
        simpa using this
      have hv : ∀ k, fderiv ℝ (pd D.envξ (Sum.inr k)) ξ h = v k := by
        intro k
        have := congrFun hh (Sum.inr k)
        simpa [hG'] using this
      refine ⟨h ∘ Sum.inr, funext fun k => ?_⟩
      rw [← hv k]
      have hdecomp : h = ∑ j, h j • (Pi.single j 1 : σ ⊕ κ → ℝ) := by
        funext j
        simp [Finset.sum_apply, Pi.single_apply]
      conv_rhs => rw [hdecomp]
      rw [map_sum]
      simp only [map_smul, smul_eq_mul, Fintype.sum_sum_type, h0, zero_mul,
        Finset.sum_const_zero, zero_add]
      simp only [Matrix.mulVec, dotProduct, hH, Matrix.of_apply, pd, Function.comp_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [← Matrix.isUnit_iff_isUnit_det]
    exact Matrix.mulVec_surjective_iff_isUnit.1 hmv

end SLData

end ClassSep
