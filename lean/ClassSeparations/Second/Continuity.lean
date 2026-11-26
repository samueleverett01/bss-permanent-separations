import ClassSeparations.Second.EnvBasic

/-!
# Continuity of the envelope (§6.3, Lemma 6.5)

**Lemma 6.5.**  There is a closed ball `K' ⊆ K` such that `e` is continuous on `K' × B̄`.
Consequently, for every `η > 0`,
`μ(η) = min {e(x; c) : x ∈ K', c ∈ B̄, |c - φ(x)| ≥ η} > 0`.

We take `K'` inside the interior of `K`, and measure `|c - φ(x)|` by its square `sqDist`.

*Proof.*  `e` is semialgebraic (S1), so by (S8) it is analytic, hence continuous, outside a
semialgebraic set `Z` of dimension `< n + κ` of `int K × ℝ^κ`.  If `e` is discontinuous (within
`K × B̄`) at `(x°, c°)`, the Lipschitz bound of Lemma 6.4 (a), uniform in `x`, shows that `e` is
discontinuous at `(x°, c)` for all `c ∈ B̄` near `c°`; these points lie in `Z`, so the fiber of
`Z` over `x°` has nonempty interior.  By (S4)(c) the set `X'` of such `x°` has dimension `< n`,
and `K'` can be chosen disjoint from its closure.  The minimum is then positive by compactness
and Lemma 6.4.
-/

noncomputable section

set_option linter.unusedSectionVars false

open MvPolynomial Set Filter Topology

namespace ClassSep

open SecondAux

namespace SLData

variable {σ κ : Type} [Fintype σ] [Fintype κ] {M : ℕ} {D : SLData σ κ M}
  {f : MvPolynomial σ ℝ} {yc : κ}

/-- Points of `int B̄` arbitrarily close to any point of `B̄`. -/
theorem exists_Bo_near (hr : 0 < D.r₀) {c : κ → ℝ} (hc : c ∈ D.Bbar) {δ : ℝ} (hδ : 0 < δ) :
    ∃ c' ∈ D.Bo, sqDist c' c < δ ^ 2 := by
  set t : ℝ := min (1 / 2) (δ / (2 * D.r₀)) with ht
  have ht0 : 0 < t := lt_min (by norm_num) (div_pos hδ (by positivity))
  have ht1 : t ≤ 1 / 2 := min_le_left _ _
  have ht2 : t * D.r₀ ≤ δ / 2 := by
    have := min_le_right (1 / 2 : ℝ) (δ / (2 * D.r₀))
    rw [← ht] at this
    calc t * D.r₀ ≤ δ / (2 * D.r₀) * D.r₀ := mul_le_mul_of_nonneg_right this hr.le
      _ = δ / 2 := by field_simp
  set c' : κ → ℝ := fun k => c k + t * (D.w₀ k - c k) with hc'
  have hc0 : sqDist c D.w₀ ≤ D.r₀ ^ 2 := hc
  have e1 : sqDist c' D.w₀ = (1 - t) ^ 2 * sqDist c D.w₀ := by
    simp only [sqDist, hc', Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have e2 : sqDist c' c = t ^ 2 * sqDist c D.w₀ := by
    simp only [sqDist, hc', Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hnn := sd_nonneg c D.w₀
  refine ⟨c', ?_, ?_⟩
  · show sqDist c' D.w₀ < D.r₀ ^ 2
    rw [e1]
    have h1 : (1 - t) ^ 2 < 1 := by nlinarith
    have h2 : (1 - t) ^ 2 * sqDist c D.w₀ ≤ (1 - t) ^ 2 * D.r₀ ^ 2 :=
      mul_le_mul_of_nonneg_left hc0 (sq_nonneg _)
    nlinarith [sq_pos_of_pos hr]
  · rw [e2]
    have h2 : t ^ 2 * sqDist c D.w₀ ≤ t ^ 2 * D.r₀ ^ 2 :=
      mul_le_mul_of_nonneg_left hc0 (sq_nonneg _)
    have h3 : (t * D.r₀) ^ 2 ≤ (δ / 2) ^ 2 := pow_le_pow_left₀ (by positivity) ht2 2
    nlinarith

/-- **Lemma 6.5.** -/
theorem Good.env_continuity (hS : SAFacts) (hG : D.Good f yc) :
    ∃ (x' : σ → ℝ) (ρ' : ℝ), 0 < ρ' ∧ Metric.closedBall x' ρ' ⊆ Metric.ball D.x₀ D.ρ ∧
      ContinuousOn D.envξ {ξ | ξ ∘ Sum.inl ∈ Metric.closedBall x' ρ' ∧ ξ ∘ Sum.inr ∈ D.Bbar} ∧
      ∀ η > 0, ∃ μ > 0, ∀ x ∈ Metric.closedBall x' ρ', ∀ c ∈ D.Bbar,
        η ≤ sqDist c (D.φ x) → μ ≤ D.env x c := by
  classical
  have hr₀ := hG.r₀_pos
  set L : ℝ := 8 * D.a * D.r₀ with hL
  have hL0 : 0 ≤ L := by have := hG.a_pos; positivity
  -- (S8): `e` is analytic off a semialgebraic set `Z` of small dimension
  have hsa : IsSAFunOn₁ D.OK D.envξ := hG.isSAFunOn_envξ.mono D.isSA_OK OK_subset_Kξ
  obtain ⟨Z, hZ, -, hZdim, hZan⟩ := hS.nash D.OK D.envξ isOpen_OK hsa
  -- the base points over which `Z` has a fiber with interior
  set Z' : Set (κ ⊕ σ → ℝ) := {v | v ∘ Sum.swap ∈ Z} with hZ'
  have hZ'sa : IsSA Z' := hZ.preimage_comp Sum.swap
  have hfib : ∀ (x : σ → ℝ) (c : κ → ℝ), c ∈ fiberOver Z' x ↔ Sum.elim x c ∈ Z := by
    intro x c
    show (Sum.elim c x) ∘ Sum.swap ∈ Z ↔ _
    have : (Sum.elim c x) ∘ Sum.swap = Sum.elim x c := by
      funext i; rcases i with i | i <;> rfl
    rw [this]
  set X' : Set (σ → ℝ) := {x | DimGE (fiberOver Z' x) (Fintype.card κ)} with hX'
  have hX'sa : IsSA X' := isSA_dimGE_fiber hZ'sa _
  have hX'dim : DimLT X' (Fintype.card σ) := by
    intro hge
    have h1 := hS.fiber_dim_le Z' (Fintype.card κ) (Fintype.card σ) hZ'sa hge
    rw [show Fintype.card κ + Fintype.card σ = Fintype.card (κ ⊕ σ) by simp, dimGE_card_iff]
      at h1
    apply hZdim
    rw [dimGE_card_iff]
    obtain ⟨v, hv⟩ := h1
    have hinj : Function.Injective (Sum.swap : σ ⊕ κ → κ ⊕ σ) :=
      fun a b h => by simpa using congrArg Sum.swap h
    have hopen := isOpenMap_comp_of_injective hinj
    have hsub : (fun u : κ ⊕ σ → ℝ => u ∘ Sum.swap) '' interior Z' ⊆ Z := by
      rintro _ ⟨u, hu, rfl⟩
      exact (interior_subset hu : u ∈ Z')
    exact ⟨v ∘ Sum.swap, interior_maximal hsub (hopen _ isOpen_interior) ⟨v, hv, rfl⟩⟩
  have hcl : interior (closure X') = ∅ :=
    (dimLT_card_iff _).1 (hS.closure_dimLT X' _ hX'sa hX'dim)
  have hdense : Dense (closure X')ᶜ := interior_eq_empty_iff_dense_compl.1 hcl
  obtain ⟨x', hx'1, hx'2⟩ := hdense.inter_open_nonempty (Metric.ball D.x₀ D.ρ) Metric.isOpen_ball
    ⟨D.x₀, Metric.mem_ball_self hG.ρ_pos⟩
  have hopen : IsOpen (Metric.ball D.x₀ D.ρ ∩ (closure X')ᶜ) :=
    Metric.isOpen_ball.inter isClosed_closure.isOpen_compl
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.1 hopen x' ⟨hx'1, hx'2⟩
  have hK'good : ∀ x ∈ Metric.closedBall x' (ε / 2),
      x ∈ Metric.ball D.x₀ D.ρ ∧ x ∉ closure X' := fun x hx =>
    hεsub (Metric.closedBall_subset_ball (half_lt_self hε) hx)
  have hK'K : ∀ x ∈ Metric.closedBall x' (ε / 2), x ∈ D.K := fun x hx =>
    Metric.ball_subset_closedBall (hK'good x hx).1
  set S : Set (σ ⊕ κ → ℝ) :=
    {ξ | ξ ∘ Sum.inl ∈ Metric.closedBall x' (ε / 2) ∧ ξ ∘ Sum.inr ∈ D.Bbar} with hSdef
  -- continuity on `K' × B̄`
  have hcont : ContinuousOn D.envξ S := by
    intro ξ₀ hξ₀
    by_contra hnc
    rw [Metric.continuousWithinAt_iff] at hnc
    push Not at hnc
    obtain ⟨η, hη, hbad⟩ := hnc
    have hx₀K : ξ₀ ∘ Sum.inl ∈ D.K := hK'K _ hξ₀.1
    set δ₀ : ℝ := η / (4 * (L + 1)) with hδ₀
    have hδ₀pos : 0 < δ₀ := by positivity
    have hLδ₀ : L * δ₀ < η / 4 := by
      rw [hδ₀, mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    -- every `c ∈ B̄` near `c₀` gives a point of `Z` over `x₀`
    have hsubZ : ∀ c ∈ D.Bbar, sqDist c (ξ₀ ∘ Sum.inr) < δ₀ ^ 2 →
        Sum.elim (ξ₀ ∘ Sum.inl) c ∈ Z := by
      intro c hc hcc
      by_contra hcZ
      have hOK : Sum.elim (ξ₀ ∘ Sum.inl) c ∈ D.OK := (hK'good _ hξ₀.1).1
      have hca : ContinuousAt D.envξ (Sum.elim (ξ₀ ∘ Sum.inl) c) :=
        (hZan _ ⟨hOK, hcZ⟩).continuousAt
      rw [Metric.continuousAt_iff] at hca
      obtain ⟨δ₁, hδ₁, hδ₁p⟩ := hca (η / 4) (by positivity)
      set q : ℝ := Real.sqrt (Fintype.card κ) + 1 with hq
      have hq0 : 0 < q := by positivity
      set δ : ℝ := min δ₁ (δ₀ / q) with hδ
      have hδpos : 0 < δ := lt_min hδ₁ (div_pos hδ₀pos hq0)
      obtain ⟨ξ, hξS, hξd, hξe⟩ := hbad δ hδpos
      have hxK : ξ ∘ Sum.inl ∈ D.K := hK'K _ hξS.1
      -- the `x`-distance
      have hxd : dist (Sum.elim (ξ ∘ Sum.inl) c) (Sum.elim (ξ₀ ∘ Sum.inl) c) < δ₁ := by
        refine lt_of_le_of_lt ?_ (hξd.trans_le (min_le_left _ _))
        refine (dist_pi_le_iff dist_nonneg).2 fun i => ?_
        rcases i with i | k
        · exact dist_le_pi_dist ξ ξ₀ (Sum.inl i)
        · simp
      have h1 := hδ₁p hxd
      -- the `c`-distance
      have hcξ : Real.sqrt (sqDist (ξ ∘ Sum.inr) (ξ₀ ∘ Sum.inr)) < δ₀ := by
        have hk : ∀ k, |ξ (Sum.inr k) - ξ₀ (Sum.inr k)| < δ₀ / q := by
          intro k
          have := (dist_le_pi_dist ξ ξ₀ (Sum.inr k)).trans_lt (hξd.trans_le (min_le_right _ _))
          rwa [Real.dist_eq] at this
        have hsq : sqDist (ξ ∘ Sum.inr) (ξ₀ ∘ Sum.inr) ≤ Fintype.card κ * (δ₀ / q) ^ 2 := by
          unfold sqDist
          calc ∑ k, ((ξ ∘ Sum.inr) k - (ξ₀ ∘ Sum.inr) k) ^ 2 ≤ ∑ _k : κ, (δ₀ / q) ^ 2 :=
                Finset.sum_le_sum fun k _ => by
                  have := hk k
                  have h0 := abs_nonneg (ξ (Sum.inr k) - ξ₀ (Sum.inr k))
                  rw [← sq_abs]
                  exact pow_le_pow_left₀ h0 this.le 2
            _ = Fintype.card κ * (δ₀ / q) ^ 2 := by simp
        have hs1 : Real.sqrt (Fintype.card κ * (δ₀ / q) ^ 2) = Real.sqrt (Fintype.card κ) * (δ₀ / q) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
        have hs2 : Real.sqrt (Fintype.card κ) * (δ₀ / q) < δ₀ := by
          rw [mul_div_assoc', div_lt_iff₀ hq0, hq]
          nlinarith [Real.sqrt_nonneg (Fintype.card κ : ℝ)]
        calc Real.sqrt (sqDist (ξ ∘ Sum.inr) (ξ₀ ∘ Sum.inr))
            ≤ Real.sqrt (Fintype.card κ * (δ₀ / q) ^ 2) := Real.sqrt_le_sqrt hsq
          _ < δ₀ := by rw [hs1]; exact hs2
      have hcc' : Real.sqrt (sqDist c (ξ₀ ∘ Sum.inr)) < δ₀ := by
        rw [Real.sqrt_lt' hδ₀pos]; exact hcc
      -- Lipschitz bounds, uniform in `x`
      have l1 := hG.env_lip hxK hξS.2 hc
      have l2 := hG.env_lip hx₀K hc hξ₀.2
      have tri := sd_triangle (ξ ∘ Sum.inr) (ξ₀ ∘ Sum.inr) c
      rw [sd_comm (ξ₀ ∘ Sum.inr) c] at tri
      have he1 : D.envξ ξ = D.env (ξ ∘ Sum.inl) (ξ ∘ Sum.inr) := rfl
      have he0 : D.envξ ξ₀ = D.env (ξ₀ ∘ Sum.inl) (ξ₀ ∘ Sum.inr) := rfl
      rw [Real.dist_eq, he1, he0] at hξe
      rw [Real.dist_eq, envξ_elim, envξ_elim] at h1
      have hA : |D.env (ξ ∘ Sum.inl) (ξ ∘ Sum.inr) - D.env (ξ ∘ Sum.inl) c| ≤ L * (2 * δ₀) := by
        refine l1.trans (mul_le_mul_of_nonneg_left (tri.trans (by linarith)) hL0)
      have hB : |D.env (ξ₀ ∘ Sum.inl) c - D.env (ξ₀ ∘ Sum.inl) (ξ₀ ∘ Sum.inr)| ≤ L * δ₀ :=
        l2.trans (mul_le_mul_of_nonneg_left hcc'.le hL0)
      have hsum : |D.env (ξ ∘ Sum.inl) (ξ ∘ Sum.inr) - D.env (ξ₀ ∘ Sum.inl) (ξ₀ ∘ Sum.inr)| ≤
          L * (2 * δ₀) + η / 4 + L * δ₀ := by
        calc _ = |(D.env (ξ ∘ Sum.inl) (ξ ∘ Sum.inr) - D.env (ξ ∘ Sum.inl) c) +
              (D.env (ξ ∘ Sum.inl) c - D.env (ξ₀ ∘ Sum.inl) c) +
              (D.env (ξ₀ ∘ Sum.inl) c - D.env (ξ₀ ∘ Sum.inl) (ξ₀ ∘ Sum.inr))| := by ring_nf
          _ ≤ |D.env (ξ ∘ Sum.inl) (ξ ∘ Sum.inr) - D.env (ξ ∘ Sum.inl) c| +
              |D.env (ξ ∘ Sum.inl) c - D.env (ξ₀ ∘ Sum.inl) c| +
              |D.env (ξ₀ ∘ Sum.inl) c - D.env (ξ₀ ∘ Sum.inl) (ξ₀ ∘ Sum.inr)| :=
                abs_add_three _ _ _
          _ ≤ L * (2 * δ₀) + η / 4 + L * δ₀ := by linarith
      linarith
    -- so the fiber of `Z` over `x₀` has nonempty interior
    obtain ⟨c', hc'Bo, hc'near⟩ := exists_Bo_near (D := D) hr₀ hξ₀.2 hδ₀pos
    have hU : IsOpen (D.Bo ∩ {c | sqDist c (ξ₀ ∘ Sum.inr) < δ₀ ^ 2}) :=
      isOpen_Bo.inter (isOpen_lt (continuous_sd _) continuous_const)
    have hUsub : D.Bo ∩ {c | sqDist c (ξ₀ ∘ Sum.inr) < δ₀ ^ 2} ⊆ fiberOver Z' (ξ₀ ∘ Sum.inl) :=
      fun c hc => (hfib _ c).2 (hsubZ c (Bo_subset_Bbar hc.1) hc.2)
    have hmem : ξ₀ ∘ Sum.inl ∈ X' := by
      show DimGE (fiberOver Z' (ξ₀ ∘ Sum.inl)) (Fintype.card κ)
      rw [dimGE_card_iff]
      exact ⟨c', interior_maximal hUsub hU ⟨hc'Bo, hc'near⟩⟩
    exact (hK'good _ hξ₀.1).2 (subset_closure hmem)
  refine ⟨x', ε / 2, half_pos hε, fun x hx => (hK'good x hx).1, hcont, fun η hη => ?_⟩
  -- positivity of `μ(η)` by compactness
  have hSeq : S = (fun p : (σ → ℝ) × (κ → ℝ) => (Sum.elim p.1 p.2 : σ ⊕ κ → ℝ)) ''
      (Metric.closedBall x' (ε / 2) ×ˢ D.Bbar) := by
    ext ξ
    constructor
    · intro h
      exact ⟨(ξ ∘ Sum.inl, ξ ∘ Sum.inr), ⟨h.1, h.2⟩, Sum.elim_comp_inl_inr ξ⟩
    · rintro ⟨p, hp, rfl⟩
      exact hp
  have hSc : IsCompact S := by
    rw [hSeq]
    exact ((isCompact_closedBall _ _).prod isCompact_Bbar).image continuous_elim_pair
  have hgc : ContinuousOn (fun ξ : σ ⊕ κ → ℝ => sqDist (ξ ∘ Sum.inr) (D.φ (ξ ∘ Sum.inl))) S := by
    have h1 : ContinuousOn (fun ξ : σ ⊕ κ → ℝ => D.φ (ξ ∘ Sum.inl)) S :=
      hG.φ_cont.comp (continuous_pi fun i => continuous_apply _).continuousOn
        (fun ξ hξ => hK'K _ hξ.1)
    unfold sqDist
    exact continuousOn_finsetSum _ fun k _ =>
      (((continuous_apply (Sum.inr k)).continuousOn).sub
        ((continuous_apply k).comp_continuousOn h1)).pow 2
  set T : Set (σ ⊕ κ → ℝ) :=
    S ∩ (fun ξ : σ ⊕ κ → ℝ => sqDist (ξ ∘ Sum.inr) (D.φ (ξ ∘ Sum.inl))) ⁻¹' Ici η with hTdef
  have hTc : IsCompact T :=
    hSc.of_isClosed_subset (hgc.preimage_isClosed_of_isClosed hSc.isClosed isClosed_Ici)
      inter_subset_left
  rcases T.eq_empty_or_nonempty with hT | hT
  · refine ⟨1, one_pos, fun x hx c hc hη' => ?_⟩
    have : Sum.elim x c ∈ T := ⟨⟨hx, hc⟩, hη'⟩
    rw [hT] at this
    exact absurd this (notMem_empty _)
  · obtain ⟨ξm, hξm, hmin⟩ := hTc.exists_isMinOn hT (hcont.mono inter_subset_left)
    have hpos : 0 < D.envξ ξm := by
      refine hG.env_pos (hK'K _ hξm.1.1) hξm.1.2 fun heq => ?_
      have h2 : η ≤ sqDist (ξm ∘ Sum.inr) (D.φ (ξm ∘ Sum.inl)) := hξm.2
      rw [heq, sd_self] at h2
      linarith
    refine ⟨D.envξ ξm, hpos, fun x hx c hc hη' => ?_⟩
    have hmem : Sum.elim x c ∈ T := ⟨⟨hx, hc⟩, hη'⟩
    have h := isMinOn_iff.1 hmin _ hmem
    rw [envξ_elim] at h
    exact h

end SLData

end ClassSep
