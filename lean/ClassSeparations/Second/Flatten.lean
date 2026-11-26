import ClassSeparations.Second.Data
import ClassSeparations.Second.Exponent
import ClassSeparations.Second.Formula

/-!
# The margin and a power of it (§6.2, Lemma 6.3)

We work with data `D : SLData σ κ M` (with `N`, `a` not yet chosen) satisfying the properties
established in §6.1–6.2 before Lemma 6.3 (`SetupAux.Pre`): `K` and `B̄` are balls, `φ` is
continuous on `K` with `|φ - w₀| ≤ r₀/2`, the `Q_b` are nonnegative, the solutions are bounded,
and, by Lemma 6.2 and Lemma 5.2 (a), for `x ∈ K` and `w ∈ B̄` some margin system has a solution
with `s > 0` exactly when `w ≠ φ(x)`.

* **Lemma 6.3 (a)** (`lemma_6_3_a`): the fibers of `𝒴` over `K × B̄` are nonempty,
  `0 ≤ v ≤ 1`, and `v(x, w) = 0 ↔ w = φ(x)`.
* **Lemma 6.3 (b)** (`lemma_6_3_b`): `v` is upper semicontinuous on `K × B̄`.
* **Lemma 6.3 (c)** (`lemma_6_3_c`): `g(τ) = sup {v(x, w) : |w - φ(x)| ≤ τ}` tends to `0`, and
  a bound `g(τ) ≤ L τ^{1/m}` gives `v^{2m} ≤ a |w - φ(x)|²`.
* **Lemma 6.3 (d)** (`lemma_6_3_d`): the graph of `g` is defined by an explicit first-order
  formula (`fGraph`) whose complexity is bounded in terms of `n, |κ|, M`, the number `B` of
  margin systems and the length `ℓ` of their programs; effective quantifier elimination
  (`exponent_bound`) gives `N` with `log N` polynomial in these quantities.
-/

noncomputable section

open MvPolynomial Set Filter Topology

namespace ClassSep

namespace SetupAux

variable {σ κ : Type} [Fintype σ] [Fintype κ] {M : ℕ}

/-- The properties of the data established before Lemma 6.3. -/
structure Pre (D : SLData σ κ M) : Prop where
  ρ_pos : 0 < D.ρ
  r₀_pos : 0 < D.r₀
  φ_cont : ContinuousOn D.φ D.K
  φ_near : ∀ x ∈ D.K, sqDist (D.φ x) D.w₀ ≤ (D.r₀ / 2) ^ 2
  nonneg : ∀ b p, 0 ≤ eval p (D.Q b)
  bounded : ∃ R, ∀ x w ν s, D.InY x w ν s → (∀ i, |ν i| ≤ R) ∧ s ≤ 1
  rej_iff : ∀ x ∈ D.K, ∀ w ∈ D.Bbar,
    (∃ b ν, ∃ s > 0, eval (SLData.pt x w ν s) (D.Q b) = 0) ↔ w ≠ D.φ x

/-! ### Squared distances -/

theorem sqd_le_of_coord {u w : κ → ℝ} (c : κ) : (u c - w c) ^ 2 ≤ sqDist u w :=
  Finset.single_le_sum (f := fun j => (u j - w j) ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ c)

theorem sqd_abs_le {u w : κ → ℝ} {r : ℝ} (hr : 0 ≤ r) (h : sqDist u w ≤ r ^ 2) (c : κ) :
    |u c - w c| ≤ r := by
  have h2 : (u c - w c) ^ 2 ≤ r ^ 2 := (sqd_le_of_coord c).trans h
  exact abs_le.2 ⟨by nlinarith, by nlinarith⟩

theorem sqd_self (u : κ → ℝ) : sqDist u u = 0 := by simp [sqDist]

theorem sqd_nonneg (u w : κ → ℝ) : 0 ≤ sqDist u w :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem sqd_eq_zero_iff {u w : κ → ℝ} : sqDist u w = 0 ↔ u = w := by
  constructor
  · intro h
    funext c
    have h1 := sqd_le_of_coord (u := u) (w := w) c
    rw [h] at h1
    nlinarith [sq_nonneg (u c - w c)]
  · rintro rfl; exact sqd_self u

theorem continuous_sqd : Continuous fun p : (κ → ℝ) × (κ → ℝ) => sqDist p.1 p.2 := by
  unfold sqDist; fun_prop

/-! ### Closedness and compactness of `𝒴` -/

/-- The points `(x, w, ν, s)`. -/
abbrev Pt (σ κ : Type) (M : ℕ) : Type := (σ → ℝ) × (κ → ℝ) × (Fin M → ℝ) × ℝ

/-- The points of `𝒴` with `s ≥ ε`. -/
def Ysol (D : SLData σ κ M) (ε : ℝ) : Set (Pt σ κ M) :=
  {p | D.InY p.1 p.2.1 p.2.2.1 p.2.2.2 ∧ ε ≤ p.2.2.2}

omit [Fintype σ] [Fintype κ] in
theorem continuous_pt :
    Continuous fun p : Pt σ κ M => SLData.pt p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  refine continuous_pi fun v => ?_
  rcases v with i | c | o
  · exact (continuous_apply i).comp continuous_fst
  · exact (continuous_apply c).comp (continuous_fst.comp continuous_snd)
  · cases o with
    | none => exact continuous_snd.comp (continuous_snd.comp continuous_snd)
    | some j =>
      exact (continuous_apply j).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))

variable {D : SLData σ κ M}

theorem isClosed_K : IsClosed D.K := Metric.isClosed_closedBall

theorem isClosed_Bbar : IsClosed D.Bbar :=
  isClosed_le ((continuous_sqd).comp (continuous_id.prodMk continuous_const)) continuous_const

theorem Bbar_sub (hr : 0 ≤ D.r₀) : D.Bbar ⊆ Metric.closedBall D.w₀ D.r₀ := by
  intro w hw
  rw [Metric.mem_closedBall, dist_pi_le_iff hr]
  intro c
  rw [Real.dist_eq]
  exact sqd_abs_le hr hw c

theorem isClosed_Ysol (ε : ℝ) : IsClosed (Ysol D ε) := by
  have h1 : IsClosed {p : Pt σ κ M | p.1 ∈ D.K} := isClosed_K.preimage continuous_fst
  have h2 : IsClosed {p : Pt σ κ M | p.2.1 ∈ D.Bbar} :=
    isClosed_Bbar.preimage (continuous_fst.comp continuous_snd)
  have hs : Continuous fun p : Pt σ κ M => p.2.2.2 :=
    continuous_snd.comp (continuous_snd.comp continuous_snd)
  have h3 : IsClosed {p : Pt σ κ M | 0 ≤ p.2.2.2} := isClosed_le continuous_const hs
  have h4 : IsClosed {p : Pt σ κ M | ∃ b, eval (SLData.pt p.1 p.2.1 p.2.2.1 p.2.2.2) (D.Q b) = 0} := by
    have : {p : Pt σ κ M | ∃ b, eval (SLData.pt p.1 p.2.1 p.2.2.1 p.2.2.2) (D.Q b) = 0} =
        ⋃ b, {p : Pt σ κ M | eval (SLData.pt p.1 p.2.1 p.2.2.1 p.2.2.2) (D.Q b) = 0} := by
      ext p; simp
    rw [this]
    exact isClosed_iUnion_of_finite fun b =>
      isClosed_eq ((MvPolynomial.continuous_eval _).comp continuous_pt) continuous_const
  have h5 : IsClosed {p : Pt σ κ M | ε ≤ p.2.2.2} := isClosed_le continuous_const hs
  exact (h1.inter (h2.inter (h3.inter h4))).inter h5

theorem Pre.isCompact_Ysol (hD : Pre D) (ε : ℝ) : IsCompact (Ysol D ε) := by
  obtain ⟨R, hR⟩ := hD.bounded
  refine (((isCompact_closedBall D.x₀ D.ρ).prod ((isCompact_closedBall D.w₀ D.r₀).prod
    ((isCompact_closedBall (0 : Fin M → ℝ) (max R 0)).prod (isCompact_Icc (a := (0 : ℝ))
      (b := 1)))))).of_isClosed_subset (isClosed_Ysol ε) ?_
  rintro ⟨x, w, ν, s⟩ ⟨hY, -⟩
  obtain ⟨hν, hs1⟩ := hR x w ν s hY
  refine ⟨hY.1, Bbar_sub hD.r₀_pos.le hY.2.1, ?_, hY.2.2.1, hs1⟩
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (le_max_right _ _)]
  intro i
  rw [Real.norm_eq_abs]
  exact (hν i).trans (le_max_left _ _)

/-- The parameters `(x, w)` at which `𝒴` has a point with `s ≥ ε` form a closed set. -/
theorem Pre.isClosed_proj (hD : Pre D) (ε : ℝ) :
    IsClosed {q : (σ → ℝ) × (κ → ℝ) | ∃ ν s, D.InY q.1 q.2 ν s ∧ ε ≤ s} := by
  have hc : Continuous fun p : Pt σ κ M => (p.1, p.2.1) :=
    continuous_fst.prodMk (continuous_fst.comp continuous_snd)
  have := ((hD.isCompact_Ysol ε).image hc).isClosed
  convert this using 1
  ext ⟨x, w⟩
  simp only [Set.mem_ofPred_eq, Set.mem_image, Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨ν, s, hY, hs⟩
    exact ⟨x, w, ν, s, ⟨hY, hs⟩, rfl, rfl⟩
  · rintro ⟨x', w', ν, s, ⟨hY, hs⟩, rfl, rfl⟩
    exact ⟨ν, s, hY, hs⟩

/-! ### Lemma 6.3 (a) -/

/-- The fiber of `𝒴` over `(x, w)`. -/
def fib (D : SLData σ κ M) (x : σ → ℝ) (w : κ → ℝ) : Set ℝ := {s | ∃ ν, D.InY x w ν s}

theorem v_eq (x : σ → ℝ) (w : κ → ℝ) : D.v x w = sSup (fib D x w) := rfl

theorem Pre.bddAbove_fib (hD : Pre D) (x : σ → ℝ) (w : κ → ℝ) : BddAbove (fib D x w) := by
  obtain ⟨R, hR⟩ := hD.bounded
  exact ⟨1, fun s ⟨ν, hν⟩ => (hR x w ν s hν).2⟩

theorem Pre.φ_mem (hD : Pre D) {x : σ → ℝ} (hx : x ∈ D.K) : D.φ x ∈ D.Bbar := by
  have h := hD.φ_near x hx
  have hr := hD.r₀_pos
  show sqDist (D.φ x) D.w₀ ≤ D.r₀ ^ 2
  nlinarith

theorem Pre.pos_of_ne (hD : Pre D) {x : σ → ℝ} (hx : x ∈ D.K) {w : κ → ℝ} (hw : w ∈ D.Bbar)
    (hne : w ≠ D.φ x) : ∃ ν, ∃ s > 0, D.InY x w ν s := by
  obtain ⟨b, ν, s, hs, h⟩ := (hD.rej_iff x hx w hw).2 hne
  exact ⟨ν, s, hs, hx, hw, hs.le, b, h⟩

theorem Pre.eq_of_pos (hD : Pre D) {x : σ → ℝ} {w : κ → ℝ} {ν : Fin M → ℝ} {s : ℝ}
    (h : D.InY x w ν s) (hs : 0 < s) : w ≠ D.φ x := by
  obtain ⟨hx, hw, -, b, hb⟩ := h
  exact (hD.rej_iff x hx w hw).1 ⟨b, ν, s, hs, hb⟩

theorem Pre.fiber_ne [Nonempty κ] (hD : Pre D) :
    ∀ x ∈ D.K, ∀ w ∈ D.Bbar, ∃ ν s, D.InY x w ν s := by
  intro x hx w hw
  by_cases hne : w = D.φ x
  · subst hne
    -- a limit of points `(x, φ(x) + t)` with `t > 0`
    set wt : ℝ → κ → ℝ := fun t c => D.φ x c + t with hwt
    have hcont : Continuous wt := by
      rw [hwt]; fun_prop
    have hlim : Tendsto (fun t : ℝ => (x, wt t)) (𝓝[>] 0) (𝓝 (x, D.φ x)) := by
      have : (x, wt 0) = (x, D.φ x) := by simp [wt]
      rw [← this]
      exact ((continuous_const.prodMk hcont).tendsto 0).mono_left nhdsWithin_le_nhds
    have hball : ∀ᶠ t in 𝓝[>] (0 : ℝ), wt t ∈ D.Bbar := by
      have h1 : Tendsto (fun t => sqDist (wt t) D.w₀) (𝓝 0) (𝓝 (sqDist (D.φ x) D.w₀)) := by
        have : sqDist (wt 0) D.w₀ = sqDist (D.φ x) D.w₀ := by simp [wt]
        rw [← this]
        exact ((continuous_sqd.comp (hcont.prodMk continuous_const)).tendsto 0)
      have hlt : sqDist (D.φ x) D.w₀ < D.r₀ ^ 2 := by
        have := hD.φ_near x hx
        have := hD.r₀_pos
        nlinarith
      exact (h1.eventually (gt_mem_nhds hlt)).filter_mono nhdsWithin_le_nhds |>.mono
        fun t ht => ht.le
    have hmem : ∀ᶠ t in 𝓝[>] (0 : ℝ),
        (x, wt t) ∈ {q : (σ → ℝ) × (κ → ℝ) | ∃ ν s, D.InY q.1 q.2 ν s ∧ 0 ≤ s} := by
      filter_upwards [hball, self_mem_nhdsWithin] with t ht htpos
      have hne : wt t ≠ D.φ x := by
        intro h
        obtain ⟨c⟩ := ‹Nonempty κ›
        have := congrFun h c
        simp only [wt] at this
        have : (0 : ℝ) < t := htpos
        linarith
      obtain ⟨ν, s, hs, hY⟩ := hD.pos_of_ne hx ht hne
      exact ⟨ν, s, hY, hs.le⟩
    obtain ⟨ν, s, hY, -⟩ := (hD.isClosed_proj 0).mem_of_tendsto hlim hmem
    exact ⟨ν, s, hY⟩
  · obtain ⟨ν, s, -, hY⟩ := hD.pos_of_ne hx hw hne
    exact ⟨ν, s, hY⟩

theorem Pre.v_nonneg [Nonempty κ] (hD : Pre D) {x : σ → ℝ} (hx : x ∈ D.K) {w : κ → ℝ}
    (hw : w ∈ D.Bbar) : 0 ≤ D.v x w := by
  obtain ⟨ν, s, hY⟩ := hD.fiber_ne x hx w hw
  exact hY.2.2.1.trans (le_csSup (hD.bddAbove_fib x w) ⟨ν, hY⟩)

theorem Pre.v_le_one [Nonempty κ] (hD : Pre D) {x : σ → ℝ} (hx : x ∈ D.K) {w : κ → ℝ}
    (hw : w ∈ D.Bbar) : D.v x w ≤ 1 := by
  obtain ⟨R, hR⟩ := hD.bounded
  obtain ⟨ν, s, hY⟩ := hD.fiber_ne x hx w hw
  exact csSup_le ⟨s, ν, hY⟩ fun s ⟨ν, hν⟩ => (hR x w ν s hν).2

theorem Pre.le_v (hD : Pre D) {x : σ → ℝ} {w : κ → ℝ} {ν : Fin M → ℝ} {s : ℝ}
    (h : D.InY x w ν s) : s ≤ D.v x w :=
  le_csSup (hD.bddAbove_fib x w) ⟨ν, h⟩

theorem Pre.zero_iff [Nonempty κ] (hD : Pre D) :
    ∀ x ∈ D.K, ∀ w ∈ D.Bbar, D.v x w = 0 ↔ w = D.φ x := by
  intro x hx w hw
  constructor
  · intro h0
    by_contra hne
    obtain ⟨ν, s, hs, hY⟩ := hD.pos_of_ne hx hw hne
    have := hD.le_v hY
    linarith
  · intro heq
    refine le_antisymm ?_ (hD.v_nonneg hx hw)
    obtain ⟨ν, s, hY⟩ := hD.fiber_ne x hx w hw
    refine csSup_le ⟨s, ν, hY⟩ fun s ⟨ν, hν⟩ => ?_
    by_contra hs
    exact hD.eq_of_pos hν (lt_of_not_ge hs) heq

/-- **Lemma 6.3 (a).** -/
theorem lemma_6_3_a [Nonempty κ] (hD : Pre D) :
    (∀ x ∈ D.K, ∀ w ∈ D.Bbar, ∃ ν s, D.InY x w ν s) ∧
    (∀ x ∈ D.K, ∀ w ∈ D.Bbar, 0 ≤ D.v x w ∧ D.v x w ≤ 1) ∧
    (∀ x ∈ D.K, ∀ w ∈ D.Bbar, D.v x w = 0 ↔ w = D.φ x) :=
  ⟨hD.fiber_ne, fun _ hx _ hw => ⟨hD.v_nonneg hx hw, hD.v_le_one hx hw⟩, hD.zero_iff⟩

/-! ### Lemma 6.3 (b) -/

/-- **Lemma 6.3 (b)**: `v` is upper semicontinuous on `K × B̄`. -/
theorem lemma_6_3_b [Nonempty κ] (hD : Pre D) :
    UpperSemicontinuousOn (fun q : (σ → ℝ) × (κ → ℝ) => D.v q.1 q.2) (D.K ×ˢ D.Bbar) := by
  rintro ⟨x, w⟩ ⟨hx, hw⟩ c hc
  simp only at hc
  have h0 := hD.v_nonneg hx hw
  set c' := (D.v x w + c) / 2 with hc'
  have hc'pos : 0 < c' := by rw [hc']; linarith
  have hnot : (x, w) ∉ {q : (σ → ℝ) × (κ → ℝ) | ∃ ν s, D.InY q.1 q.2 ν s ∧ c' ≤ s} := by
    rintro ⟨ν, s, hY, hs⟩
    have := hD.le_v hY
    simp only at this
    rw [hc'] at hs
    linarith
  have hopen := (hD.isClosed_proj c').isOpen_compl
  filter_upwards [nhdsWithin_le_nhds (hopen.mem_nhds hnot), self_mem_nhdsWithin] with q hq hqK
  obtain ⟨hqx, hqw⟩ := hqK
  obtain ⟨ν₀, s₀, hY₀⟩ := hD.fiber_ne q.1 hqx q.2 hqw
  have : D.v q.1 q.2 ≤ c' := by
    refine csSup_le ⟨s₀, ν₀, hY₀⟩ fun s ⟨ν, hν⟩ => ?_
    by_contra hs
    exact hq ⟨ν, s, hν, (lt_of_not_ge hs).le⟩
  rw [hc'] at this
  linarith

/-! ### Lemma 6.3 (c) -/

/-- The values `s` of `𝒴` over the points `(x, w)` with `|w - φ(x)| ≤ τ`. -/
def gset (D : SLData σ κ M) (τ : ℝ) : Set ℝ :=
  {s | ∃ x w ν, D.InY x w ν s ∧ sqDist w (D.φ x) ≤ τ ^ 2}

/-- `g(τ) = sup {v(x, w) : x ∈ K, w ∈ B̄, |w - φ(x)| ≤ τ}`. -/
def gfun (D : SLData σ κ M) (τ : ℝ) : ℝ := sSup (gset D τ)

theorem Pre.bddAbove_gset (hD : Pre D) (τ : ℝ) : BddAbove (gset D τ) := by
  obtain ⟨R, hR⟩ := hD.bounded
  exact ⟨1, fun s ⟨x, w, ν, hY, _⟩ => (hR x w ν s hY).2⟩

theorem Pre.gset_nonempty [Nonempty κ] (hD : Pre D) (τ : ℝ) : (gset D τ).Nonempty := by
  have hx₀ : D.x₀ ∈ D.K := Metric.mem_closedBall_self hD.ρ_pos.le
  obtain ⟨ν, s, hY⟩ := hD.fiber_ne D.x₀ hx₀ _ (hD.φ_mem hx₀)
  exact ⟨s, D.x₀, _, ν, hY, by rw [sqd_self]; positivity⟩

theorem Pre.gfun_nonneg [Nonempty κ] (hD : Pre D) (τ : ℝ) : 0 ≤ gfun D τ := by
  obtain ⟨s, x, w, ν, hY, hd⟩ := hD.gset_nonempty τ
  exact hY.2.2.1.trans (le_csSup (hD.bddAbove_gset τ) ⟨x, w, ν, hY, hd⟩)

theorem Pre.v_le_gfun [Nonempty κ] (hD : Pre D) {x : σ → ℝ} (hx : x ∈ D.K) {w : κ → ℝ}
    (hw : w ∈ D.Bbar) {τ : ℝ} (hτ : sqDist w (D.φ x) ≤ τ ^ 2) : D.v x w ≤ gfun D τ := by
  obtain ⟨ν, s, hY⟩ := hD.fiber_ne x hx w hw
  exact csSup_le_csSup (hD.bddAbove_gset τ) ⟨s, ν, hY⟩ fun s ⟨ν, hν⟩ => ⟨x, w, ν, hν, hτ⟩

/-- `g(τ) → 0` as `τ → 0⁺`. -/
theorem Pre.gfun_tendsto [Nonempty κ] (hD : Pre D) : Tendsto (gfun D) (𝓝[>] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- a positive lower bound `δ` for `|w - φ(x)|²` on the points of `𝒴` with `s ≥ ε / 2`
  obtain ⟨δ, hδ, hδY⟩ : ∃ δ > 0, ∀ p ∈ Ysol D (ε / 2), δ ≤ sqDist p.2.1 (D.φ p.1) := by
    rcases (Ysol D (ε / 2)).eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun p hp => by rw [he] at hp; exact hp.elim⟩
    · have hcont : ContinuousOn (fun p : Pt σ κ M => sqDist p.2.1 (D.φ p.1)) (Ysol D (ε / 2)) := by
        have h1 : ContinuousOn (fun p : Pt σ κ M => (p.2.1, D.φ p.1)) (Ysol D (ε / 2)) := by
          refine ContinuousOn.prodMk (continuous_fst.comp continuous_snd).continuousOn ?_
          refine hD.φ_cont.comp continuous_fst.continuousOn ?_
          intro p hp
          exact hp.1.1
        have := (continuous_sqd (κ := κ)).comp_continuousOn h1
        exact this
      obtain ⟨p, hp, hmin⟩ := (hD.isCompact_Ysol (ε / 2)).exists_isMinOn hne hcont
      refine ⟨sqDist p.2.1 (D.φ p.1), ?_, fun q hq => hmin hq⟩
      have hne' := hD.eq_of_pos hp.1 (by linarith [hp.2])
      rcases (sqd_nonneg p.2.1 (D.φ p.1)).lt_or_eq with h | h
      · exact h
      · exact absurd (sqd_eq_zero_iff.1 h.symm) hne'
  have hev : ∀ᶠ τ in 𝓝[>] (0 : ℝ), τ ^ 2 < δ := by
    have : Tendsto (fun τ : ℝ => τ ^ 2) (𝓝 0) (𝓝 0) := by
      have := (continuous_pow 2).tendsto (0 : ℝ)
      simpa using this
    exact (this.eventually (gt_mem_nhds hδ)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hev] with τ hτ
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hD.gfun_nonneg τ)]
  refine lt_of_le_of_lt (csSup_le (hD.gset_nonempty τ) fun s ⟨x, w, ν, hY, hd⟩ => ?_)
    (half_lt_self hε)
  by_contra hs
  have := hδY (x, w, ν, s) ⟨hY, (lt_of_not_ge hs).le⟩
  simp only at this
  linarith

/-- From a rate `g(τ) ≤ L τ^{1/m}` to the bound `v^{2m} ≤ a |w - φ(x)|²`. -/
theorem Pre.flat_of_rate [Nonempty κ] (hD : Pre D) (m : ℕ) (hm : 1 ≤ m) (L σ₁ : ℝ)
    (hσ₁ : 0 < σ₁) (hL : ∀ τ ∈ Ioo 0 σ₁, gfun D τ ≤ L * τ ^ ((1 : ℝ) / m)) :
    ∃ a > 0, ∀ x ∈ D.K, ∀ w ∈ D.Bbar, D.v x w ^ (2 * m) ≤ a * sqDist w (D.φ x) := by
  set L' := max L 0 with hL'
  refine ⟨L' ^ (2 * m) + 1 / σ₁ ^ 2, by positivity, fun x hx w hw => ?_⟩
  have hv0 := hD.v_nonneg hx hw
  have hv1 := hD.v_le_one hx hw
  have hd0 := sqd_nonneg w (D.φ x)
  set τ := Real.sqrt (sqDist w (D.φ x)) with hτ
  have hτ0 : 0 ≤ τ := Real.sqrt_nonneg _
  have hτ2 : τ ^ 2 = sqDist w (D.φ x) := Real.sq_sqrt hd0
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  rcases hτ0.lt_or_eq with hτpos | hτz
  · rcases lt_or_ge τ σ₁ with hlt | hge
    · -- near the graph: `v ≤ g(τ) ≤ L τ^{1/m}`
      have hg := hD.v_le_gfun hx hw (τ := τ) hτ2.ge
      have hgL := hL τ ⟨hτpos, hlt⟩
      have hpow : 0 < τ ^ ((1 : ℝ) / m) := Real.rpow_pos_of_pos hτpos _
      have hvL : D.v x w ≤ L' * τ ^ ((1 : ℝ) / m) :=
        hg.trans (hgL.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow.le))
      have h2 : (τ ^ ((1 : ℝ) / m)) ^ (2 * m) = τ ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hτ0]
        have : (1 : ℝ) / m * ((2 * m : ℕ) : ℝ) = (2 : ℕ) := by
          push_cast; field_simp
        rw [this, Real.rpow_natCast]
      have h3 : D.v x w ^ (2 * m) ≤ (L' * τ ^ ((1 : ℝ) / m)) ^ (2 * m) :=
        pow_le_pow_left₀ hv0 hvL _
      rw [mul_pow, h2, hτ2] at h3
      have h4 : 0 ≤ 1 / σ₁ ^ 2 * sqDist w (D.φ x) := by positivity
      nlinarith
    · -- far from the graph: `v ≤ 1 ≤ τ / σ₁`
      have h1 : D.v x w ^ (2 * m) ≤ 1 := pow_le_one₀ hv0 hv1
      have h2 : 1 ≤ 1 / σ₁ ^ 2 * sqDist w (D.φ x) := by
        rw [← hτ2, one_div, inv_mul_eq_div, le_div_iff₀ (by positivity), one_mul]
        exact pow_le_pow_left₀ hσ₁.le hge 2
      have h3 : 0 ≤ L' ^ (2 * m) * sqDist w (D.φ x) := by positivity
      nlinarith
  · -- on the graph
    have hd : sqDist w (D.φ x) = 0 := by rw [← hτ2, ← hτz]; ring
    have hw' : w = D.φ x := sqd_eq_zero_iff.1 hd
    rw [(hD.zero_iff x hx w hw).2 hw', hd, mul_zero, zero_pow (by omega)]

/-- **Lemma 6.3 (c)**: `g(τ) → 0`, and a rate `g(τ) ≤ L τ^{1/m}` near `0` gives
`v^{2m} ≤ a |w - φ(x)|²` on `K × B̄`. -/
theorem lemma_6_3_c [Nonempty κ] (hD : Pre D) :
    (∀ τ, 0 ≤ gfun D τ) ∧ Tendsto (gfun D) (𝓝[>] 0) (𝓝 0) ∧
    ∀ (m : ℕ), 1 ≤ m → ∀ L σ₁ : ℝ, 0 < σ₁ → (∀ τ ∈ Ioo 0 σ₁, gfun D τ ≤ L * τ ^ ((1 : ℝ) / m)) →
      ∃ a > 0, ∀ x ∈ D.K, ∀ w ∈ D.Bbar, D.v x w ^ (2 * m) ≤ a * sqDist w (D.φ x) :=
  ⟨hD.gfun_nonneg, hD.gfun_tendsto, hD.flat_of_rate⟩

end SetupAux

end ClassSep
