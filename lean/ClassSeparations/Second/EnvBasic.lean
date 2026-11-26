import ClassSeparations.Second.Data

/-!
# The envelope of §6.3 for the data `SLData`

For `x ∈ K` the *atoms* over `x` are the pairs `(ω, s)` with `(x, ω, ν, s) ∈ 𝒴` for some `ν`;
they form a compact set `At x ⊆ ℝ^κ × [0, 1]` with `ω ∈ B̄`.  The envelope is
`e(x; c) = envelope (At x) a N c` (Lemma 6.4, `envelope_props`).

This file collects the consequences of Lemma 6.4 for the data of §6 (`e(x; ·)` is `C¹`,
Lipschitz on `B̄`, nonnegative on `B̄`, and vanishes on `B̄` exactly at `φ(x)`), and the facts
(S1) that `e` and its gradient in `c` are semialgebraic.

Generic helpers live in the namespace `ClassSep.SecondAux`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open MvPolynomial Set Filter Topology

namespace ClassSep

namespace SecondAux

/-- The partial derivative of `g` in the coordinate direction `i`. -/
def pd {α : Type} [DecidableEq α] (g : (α → ℝ) → ℝ) (i : α) : (α → ℝ) → ℝ :=
  fun ξ => fderiv ℝ g ξ (Pi.single i 1)

/-- Partial derivatives of analytic functions are analytic. -/
theorem analyticAt_pd {α : Type} [Fintype α] [DecidableEq α] {g : (α → ℝ) → ℝ} {ξ₁ : α → ℝ}
    (hg : AnalyticAt ℝ g ξ₁) (i : α) : AnalyticAt ℝ (pd g i) ξ₁ := by
  have h1 : AnalyticAt ℝ (fderiv ℝ g) ξ₁ := hg.fderiv
  have h2 : AnalyticAt ℝ (fun L : (α → ℝ) →L[ℝ] ℝ => L (Pi.single i 1)) (fderiv ℝ g ξ₁) :=
    (ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1 : α → ℝ)).analyticAt _
  exact h2.comp h1

variable {κ : Type} [Fintype κ]

/-- A coordinate bound from `sqDist`. -/
theorem sd_abs_sub_le {u w : κ → ℝ} {r : ℝ} (hr : 0 ≤ r) (h : sqDist u w ≤ r ^ 2)
    (k : κ) : |u k - w k| ≤ r := by
  have h1 : (u k - w k) ^ 2 ≤ sqDist u w :=
    Finset.single_le_sum (f := fun j => (u j - w j) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ k)
  have h2 : (u k - w k) ^ 2 ≤ r ^ 2 := h1.trans h
  exact abs_le.2 ⟨by nlinarith, by nlinarith⟩

theorem sd_nonneg (u w : κ → ℝ) : 0 ≤ sqDist u w :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem sd_comm (u w : κ → ℝ) : sqDist u w = sqDist w u := by
  unfold sqDist
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem sd_self (u : κ → ℝ) : sqDist u u = 0 := by simp [sqDist]

theorem sd_eq_zero_iff {u w : κ → ℝ} : sqDist u w = 0 ↔ u = w := by
  constructor
  · intro h
    funext k
    have h1 : (u k - w k) ^ 2 ≤ sqDist u w :=
      Finset.single_le_sum (f := fun j => (u j - w j) ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ k)
    rw [h] at h1
    nlinarith [sq_nonneg (u k - w k)]
  · rintro rfl; exact sd_self u

theorem continuous_sd (w : κ → ℝ) : Continuous fun u : κ → ℝ => sqDist u w := by
  unfold sqDist; fun_prop

/-- The Euclidean distance as a distance in `EuclideanSpace`. -/
theorem sd_sqrt_eq (u w : κ → ℝ) :
    Real.sqrt (sqDist u w) = dist (WithLp.toLp 2 u : EuclideanSpace ℝ κ) (WithLp.toLp 2 w) := by
  rw [EuclideanSpace.dist_eq]
  congr 1
  unfold sqDist
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Real.dist_eq, sq_abs]

/-- The triangle inequality for the Euclidean distance. -/
theorem sd_triangle (u v w : κ → ℝ) :
    Real.sqrt (sqDist u w) ≤ Real.sqrt (sqDist u v) + Real.sqrt (sqDist v w) := by
  rw [sd_sqrt_eq, sd_sqrt_eq, sd_sqrt_eq]
  exact dist_triangle _ _ _

/-! ### Configurations of atoms, as points of `ℝ^(Cfg κ M r)` -/

/-- Coordinates of a configuration of `r` atoms: the weights, the atoms `ω`, the values `s` and
the unknowns `ν`. -/
abbrev Cfg (κ : Type) (M r : ℕ) := Fin r ⊕ (Fin r × κ) ⊕ Fin r ⊕ (Fin r × Fin M)

namespace Cfg

variable {κ : Type} {M r : ℕ}

def lam (z : Cfg κ M r → ℝ) : Fin r → ℝ := fun i => z (Sum.inl i)
def om (z : Cfg κ M r → ℝ) : Fin r → κ → ℝ := fun i k => z (Sum.inr (Sum.inl (i, k)))
def s (z : Cfg κ M r → ℝ) : Fin r → ℝ := fun i => z (Sum.inr (Sum.inr (Sum.inl i)))
def nu (z : Cfg κ M r → ℝ) : Fin r → Fin M → ℝ :=
  fun i m => z (Sum.inr (Sum.inr (Sum.inr (i, m))))

/-- Assemble a configuration. -/
def mk (lam : Fin r → ℝ) (om : Fin r → κ → ℝ) (s : Fin r → ℝ) (nu : Fin r → Fin M → ℝ) :
    Cfg κ M r → ℝ :=
  Sum.elim lam (Sum.elim (fun p => om p.1 p.2) (Sum.elim s (fun p => nu p.1 p.2)))

@[simp] theorem lam_mk (lam : Fin r → ℝ) (om : Fin r → κ → ℝ) (s : Fin r → ℝ)
    (nu : Fin r → Fin M → ℝ) : Cfg.lam (mk lam om s nu) = lam := rfl
@[simp] theorem om_mk (lam : Fin r → ℝ) (om : Fin r → κ → ℝ) (s : Fin r → ℝ)
    (nu : Fin r → Fin M → ℝ) : Cfg.om (mk lam om s nu) = om := rfl
@[simp] theorem s_mk (lam : Fin r → ℝ) (om : Fin r → κ → ℝ) (s : Fin r → ℝ)
    (nu : Fin r → Fin M → ℝ) : Cfg.s (mk lam om s nu) = s := rfl
@[simp] theorem nu_mk (lam : Fin r → ℝ) (om : Fin r → κ → ℝ) (s : Fin r → ℝ)
    (nu : Fin r → Fin M → ℝ) : Cfg.nu (mk lam om s nu) = nu := rfl

end Cfg

/-- Finite sums of polynomial functions. -/
theorem isPolyFn_sum {ι γ : Type} (t : Finset γ) {f : γ → (ι → ℝ) → ℝ}
    (h : ∀ i, FO.IsPolyFn (f i)) : FO.IsPolyFn (fun u => ∑ i ∈ t, f i u) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using FO.IsPolyFn.const (ι := ι) 0
  | insert a t ha ih => simpa [Finset.sum_insert ha] using (h a).add ih

theorem isPolyFn_sqDist {ι : Type} {A B : (ι → ℝ) → κ → ℝ}
    (hA : ∀ k, FO.IsPolyFn (fun u => A u k)) (hB : ∀ k, FO.IsPolyFn (fun u => B u k)) :
    FO.IsPolyFn (fun u => sqDist (A u) (B u)) := by
  unfold sqDist
  exact isPolyFn_sum _ fun k => ((hA k).sub (hB k)).pow 2

theorem isPolyFn_envJ {ι : Type} {r : ℕ} (a : ℝ) (N : ℕ)
    {lam : (ι → ℝ) → Fin r → ℝ} {om : (ι → ℝ) → Fin r → κ → ℝ} {s : (ι → ℝ) → Fin r → ℝ}
    {c : (ι → ℝ) → κ → ℝ} (hl : ∀ i, FO.IsPolyFn (fun u => lam u i))
    (ho : ∀ i k, FO.IsPolyFn (fun u => om u i k)) (hs : ∀ i, FO.IsPolyFn (fun u => s u i))
    (hc : ∀ k, FO.IsPolyFn (fun u => c u k)) :
    FO.IsPolyFn (fun u => envJ a N (lam u) (om u) (s u) (c u)) := by
  unfold envJ
  have hbar : ∀ k, FO.IsPolyFn (fun u => ∑ i, lam u i * om u i k) :=
    fun k => isPolyFn_sum _ fun i => (hl i).mul (ho i k)
  refine ((isPolyFn_sum _ fun i => (hl i).mul ((hs i).pow N)).sub
    ((FO.IsPolyFn.const a).mul (isPolyFn_sum _ fun i => (hl i).mul
      (isPolyFn_sqDist (ho i) hbar)))).sub
    (((FO.IsPolyFn.const 2).mul (FO.IsPolyFn.const a)).mul (isPolyFn_sqDist hc hbar))

end SecondAux

open SecondAux

namespace SLData

variable {σ κ : Type} [Fintype σ] [Fintype κ] {M : ℕ} (D : SLData σ κ M)

/-- The atoms over `x`: pairs `(ω, s)` with `(x, ω, ν, s) ∈ 𝒴` for some `ν`. -/
def At (x : σ → ℝ) : Set ((κ → ℝ) × ℝ) := {p | ∃ ν, D.InY x p.1 ν p.2}

/-- The envelope `e(x; c)`. -/
def env (x : σ → ℝ) (c : κ → ℝ) : ℝ := envelope (D.At x) D.a D.N c

/-- The envelope as a function of `ξ = (x, c) ∈ ℝ^(σ ⊕ κ)`. -/
def envξ (ξ : σ ⊕ κ → ℝ) : ℝ := D.env (ξ ∘ Sum.inl) (ξ ∘ Sum.inr)

/-- The open ball `int B̄`. -/
def Bo : Set (κ → ℝ) := {w | sqDist w D.w₀ < D.r₀ ^ 2}

/-- The open set `int K × ℝ^κ`. -/
def OK : Set (σ ⊕ κ → ℝ) := {ξ | ξ ∘ Sum.inl ∈ Metric.ball D.x₀ D.ρ}

/-- The domain `K × ℝ^κ`. -/
def Kξ : Set (σ ⊕ κ → ℝ) := {ξ | ξ ∘ Sum.inl ∈ D.K}

/-- The gradient of `e(x; ·)`. -/
def grad [DecidableEq κ] (x : σ → ℝ) (c : κ → ℝ) (k : κ) : ℝ :=
  fderiv ℝ (D.env x) c (Pi.single k 1)

theorem envξ_elim (x : σ → ℝ) (c : κ → ℝ) : D.envξ (Sum.elim x c) = D.env x c := rfl

variable {D}

theorem At_eq_empty {x : σ → ℝ} (hx : x ∉ D.K) : D.At x = ∅ := by
  ext p
  simp only [At, InY, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_exists]
  exact fun ν h => hx h.1

theorem At_ball (x : σ → ℝ) : ∀ p ∈ D.At x, sqDist p.1 D.w₀ ≤ D.r₀ ^ 2 := by
  rintro p ⟨ν, h⟩
  exact h.2.1

theorem Bo_subset_Bbar : D.Bo ⊆ D.Bbar :=
  fun w (h : sqDist w D.w₀ < D.r₀ ^ 2) => le_of_lt h

theorem isOpen_Bo : IsOpen D.Bo := isOpen_lt (continuous_sd _) continuous_const

theorem isClosed_Bbar : IsClosed D.Bbar := isClosed_le (continuous_sd _) continuous_const

theorem isOpen_OK : IsOpen D.OK :=
  Metric.isOpen_ball.preimage (continuous_pi fun _ => continuous_apply _)

theorem OK_subset_Kξ : D.OK ⊆ D.Kξ := fun _ h => Metric.ball_subset_closedBall h

theorem isCompact_Bbar : IsCompact D.Bbar := by
  refine Metric.isCompact_of_isClosed_isBounded isClosed_Bbar
    ((Metric.isBounded_closedBall (x := D.w₀) (r := |D.r₀|)).subset fun c hc => ?_)
  rw [Metric.mem_closedBall, dist_pi_le_iff (abs_nonneg _)]
  intro k
  rw [Real.dist_eq]
  exact sd_abs_sub_le (abs_nonneg _) (by rw [sq_abs]; exact hc) k

theorem continuous_elim_pair :
    Continuous fun p : (σ → ℝ) × (κ → ℝ) => (Sum.elim p.1 p.2 : σ ⊕ κ → ℝ) := by
  refine continuous_pi fun i => ?_
  rcases i with i | k
  · exact (continuous_apply i).comp continuous_fst
  · exact (continuous_apply k).comp continuous_snd

/-- Points within `r₀/2` of a point of the ball of radius `r₀/2` lie in the open ball. -/
theorem mem_Bo_of_near (hr : 0 < D.r₀) {c φ : κ → ℝ} (hφ : sqDist φ D.w₀ ≤ (D.r₀ / 2) ^ 2)
    (hc : sqDist c φ < (D.r₀ / 2) ^ 2) : c ∈ D.Bo := by
  have h1 : Real.sqrt (sqDist c φ) < D.r₀ / 2 := by
    rw [Real.sqrt_lt' (by positivity)]; exact hc
  have h2 : Real.sqrt (sqDist φ D.w₀) ≤ D.r₀ / 2 := by
    rw [Real.sqrt_le_left (by positivity)]; exact hφ
  have h3 := sd_triangle c φ D.w₀
  have h4 : Real.sqrt (sqDist c D.w₀) < D.r₀ := by linarith
  show sqDist c D.w₀ < D.r₀ ^ 2
  have h5 := Real.sq_sqrt (sd_nonneg c D.w₀)
  have h6 := Real.sqrt_nonneg (sqDist c D.w₀)
  nlinarith

variable {f : MvPolynomial σ ℝ} {yc : κ}

theorem Good.phi_mem (hG : D.Good f yc) {x : σ → ℝ} (hx : x ∈ D.K) : D.φ x ∈ D.Bbar := by
  have h := hG.φ_near x hx
  have hr := hG.r₀_pos
  show sqDist (D.φ x) D.w₀ ≤ D.r₀ ^ 2
  nlinarith [sd_nonneg (D.φ x) D.w₀]

theorem continuous_pt (x : σ → ℝ) :
    Continuous fun q : (κ → ℝ) × (Fin M → ℝ) × ℝ => pt x q.1 q.2.1 q.2.2 := by
  refine continuous_pi fun i => ?_
  rcases i with i | k | _ | m
  · exact continuous_const
  · exact (continuous_apply k).comp continuous_fst
  · exact continuous_snd.comp continuous_snd
  · exact (continuous_apply m).comp (continuous_fst.comp continuous_snd)

theorem Good.isCompact_At (hG : D.Good f yc) (x : σ → ℝ) : IsCompact (D.At x) := by
  by_cases hx : x ∈ D.K
  swap
  · rw [At_eq_empty hx]; exact isCompact_empty
  obtain ⟨R, hR⟩ := hG.bounded
  set Y : Set ((κ → ℝ) × (Fin M → ℝ) × ℝ) := {q | D.InY x q.1 q.2.1 q.2.2} with hYdef
  have hYeq : Y = {q | q.1 ∈ D.Bbar} ∩ {q | 0 ≤ q.2.2} ∩
      ⋃ b, {q | eval (pt x q.1 q.2.1 q.2.2) (D.Q b) = 0} := by
    ext q
    simp only [hYdef, InY, mem_ofPred_eq, mem_inter_iff, mem_iUnion]
    exact ⟨fun h => ⟨⟨h.2.1, h.2.2.1⟩, h.2.2.2⟩, fun h => ⟨hx, h.1.1, h.1.2, h.2⟩⟩
  have hYc : IsClosed Y := by
    rw [hYeq]
    refine (IsClosed.inter ?_ ?_).inter (isClosed_iUnion_of_finite fun b => ?_)
    · exact isClosed_Bbar.preimage continuous_fst
    · exact isClosed_le continuous_const (continuous_snd.comp continuous_snd)
    · exact isClosed_eq ((MvPolynomial.continuous_eval _).comp (continuous_pt (M := M) x))
        continuous_const
  have hYb : Bornology.IsBounded Y := by
    refine isBounded_iff_forall_norm_le.2 ⟨‖D.w₀‖ + D.r₀ + |R| + 1, fun q hq => ?_⟩
    have hr := hG.r₀_pos
    obtain ⟨hν, hs⟩ := hR x q.1 q.2.1 q.2.2 hq
    have hB : (0 : ℝ) ≤ ‖D.w₀‖ + D.r₀ + |R| + 1 := by positivity
    rw [norm_prod_le_iff, norm_prod_le_iff]
    refine ⟨?_, ?_, ?_⟩
    · refine (pi_norm_le_iff_of_nonneg hB).2 fun k => ?_
      have h1 := sd_abs_sub_le hr.le hq.2.1 k
      have h2 : |D.w₀ k| ≤ ‖D.w₀‖ := by
        simpa [Real.norm_eq_abs] using norm_le_pi_norm D.w₀ k
      rw [Real.norm_eq_abs]
      have h3 := abs_sub_abs_le_abs_sub (q.1 k) (D.w₀ k)
      have := abs_nonneg R
      linarith
    · refine (pi_norm_le_iff_of_nonneg hB).2 fun m => ?_
      rw [Real.norm_eq_abs]
      have := hν m
      have := le_abs_self R
      have := norm_nonneg D.w₀
      linarith
    · rw [Real.norm_eq_abs, abs_of_nonneg hq.2.2.1]
      have := abs_nonneg R
      have := norm_nonneg D.w₀
      linarith
  have hY : IsCompact Y := Metric.isCompact_of_isClosed_isBounded hYc hYb
  have hAt : D.At x = (fun q : (κ → ℝ) × (Fin M → ℝ) × ℝ => (q.1, q.2.2)) '' Y := by
    ext p
    simp only [At, mem_ofPred_eq, mem_image, hYdef]
    constructor
    · rintro ⟨ν, h⟩
      exact ⟨(p.1, ν, p.2), h, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.2.1, hq⟩
  rw [hAt]
  exact hY.image (by fun_prop)

theorem Good.At_nonempty (hG : D.Good f yc) {x : σ → ℝ} (hx : x ∈ D.K) :
    (D.At x).Nonempty := by
  have hw : D.w₀ ∈ D.Bbar := by
    show sqDist D.w₀ D.w₀ ≤ D.r₀ ^ 2
    rw [sd_self]; positivity
  obtain ⟨ν, s, h⟩ := hG.fiber_ne x hx D.w₀ hw
  exact ⟨(D.w₀, s), ν, h⟩

theorem Good.At_s (hG : D.Good f yc) (x : σ → ℝ) : ∀ p ∈ D.At x, 0 ≤ p.2 ∧ p.2 ≤ 1 := by
  rintro p ⟨ν, h⟩
  obtain ⟨R, hR⟩ := hG.bounded
  exact ⟨h.2.2.1, (hR _ _ _ _ h).2⟩

/-- The largest margin is attained. -/
theorem Good.v_mem (hG : D.Good f yc) {x : σ → ℝ} (hx : x ∈ D.K) {w : κ → ℝ}
    (hw : w ∈ D.Bbar) : (w, D.v x w) ∈ D.At x := by
  set S := {s | ∃ ν, D.InY x w ν s} with hS
  have hSc : IsClosed S := by
    have : S = (fun s : ℝ => (w, s)) ⁻¹' D.At x := by
      ext s; simp [hS, At]
    rw [this]
    exact (hG.isCompact_At x).isClosed.preimage (by fun_prop)
  have hne : S.Nonempty := by
    obtain ⟨ν, s, h⟩ := hG.fiber_ne x hx w hw
    exact ⟨s, ν, h⟩
  have hbdd : BddAbove S := by
    obtain ⟨R, hR⟩ := hG.bounded
    exact ⟨1, fun s ⟨ν, h⟩ => (hR _ _ _ _ h).2⟩
  exact hSc.csSup_mem hne hbdd

theorem Good.le_v (hG : D.Good f yc) {x : σ → ℝ} {w : κ → ℝ} {s : ℝ}
    (hs : (w, s) ∈ D.At x) : s ≤ D.v x w := by
  obtain ⟨R, hR⟩ := hG.bounded
  refine le_csSup ⟨1, fun s ⟨ν, h⟩ => (hR _ _ _ _ h).2⟩ hs

theorem Good.v_nonneg (hG : D.Good f yc) {x : σ → ℝ} (hx : x ∈ D.K) {w : κ → ℝ}
    (hw : w ∈ D.Bbar) : 0 ≤ D.v x w :=
  (hG.At_s x _ (hG.v_mem hx hw)).1

/-- Lemma 6.4, applied to the atoms over `x ∈ K`. -/
theorem Good.envProps (hG : D.Good f yc) {x : σ → ℝ} (hx : x ∈ D.K) :
    (∀ c, ∃ p ∈ envAdm (D.At x) (Fintype.card κ + 3),
      envJ D.a D.N p.1 p.2.1 p.2.2 c = D.env x c) ∧
    ContDiff ℝ 1 (D.env x) ∧
    (∀ c, ∀ p ∈ envAdm (D.At x) (Fintype.card κ + 3),
      envJ D.a D.N p.1 p.2.1 p.2.2 c = D.env x c →
      ∀ v, fderiv ℝ (D.env x) c v =
        4 * D.a * ∑ k, (∑ i, p.1 i * p.2.1 i k - c k) * v k) ∧
    (∀ c c', sqDist c D.w₀ ≤ D.r₀ ^ 2 → sqDist c' D.w₀ ≤ D.r₀ ^ 2 →
      |D.env x c - D.env x c'| ≤ 8 * D.a * D.r₀ * Real.sqrt (sqDist c c')) ∧
    (∀ c s, (c, s) ∈ D.At x → s ^ D.N ≤ D.env x c) ∧
    (∀ φ : κ → ℝ, (∀ p ∈ D.At x, p.2 ^ D.N ≤ D.a * sqDist p.1 φ) → D.env x φ ≤ 0) :=
  envelope_props (D.At x) (hG.isCompact_At x) (hG.At_nonempty hx) D.w₀ D.r₀ hG.r₀_pos.le
    (At_ball x)
    (hG.At_s x) D.a hG.a_pos D.N hG.N_pos

theorem Good.contDiff_env (hG : D.Good f yc) {x : σ → ℝ} (hx : x ∈ D.K) :
    ContDiff ℝ 1 (D.env x) :=
  (hG.envProps hx).2.1

theorem Good.differentiable_env (hG : D.Good f yc) {x : σ → ℝ} (hx : x ∈ D.K) :
    Differentiable ℝ (D.env x) :=
  (hG.contDiff_env hx).differentiable one_ne_zero

theorem Good.env_lip (hG : D.Good f yc) {x : σ → ℝ} (hx : x ∈ D.K) {c c' : κ → ℝ}
    (hc : c ∈ D.Bbar) (hc' : c' ∈ D.Bbar) :
    |D.env x c - D.env x c'| ≤ 8 * D.a * D.r₀ * Real.sqrt (sqDist c c') :=
  (hG.envProps hx).2.2.2.1 c c' hc hc'

theorem Good.env_ge (hG : D.Good f yc) {x : σ → ℝ} (hx : x ∈ D.K) {c : κ → ℝ}
    (hc : c ∈ D.Bbar) : D.v x c ^ D.N ≤ D.env x c :=
  (hG.envProps hx).2.2.2.2.1 c _ (hG.v_mem hx hc)

theorem Good.env_nonneg (hG : D.Good f yc) {x : σ → ℝ} (hx : x ∈ D.K) {c : κ → ℝ}
    (hc : c ∈ D.Bbar) : 0 ≤ D.env x c :=
  (pow_nonneg (hG.v_nonneg hx hc) _).trans (hG.env_ge hx hc)

theorem Good.env_phi (hG : D.Good f yc) {x : σ → ℝ} (hx : x ∈ D.K) : D.env x (D.φ x) = 0 := by
  refine le_antisymm ((hG.envProps hx).2.2.2.2.2 (D.φ x) fun p hp => ?_)
    (hG.env_nonneg hx (hG.phi_mem hx))
  have hp1 : p.1 ∈ D.Bbar := At_ball x p hp
  have hs := hG.At_s x p hp
  have hle : p.2 ≤ D.v x p.1 := hG.le_v (x := x) (w := p.1) (s := p.2) hp
  calc p.2 ^ D.N ≤ D.v x p.1 ^ D.N := pow_le_pow_left₀ hs.1 hle _
    _ ≤ D.a * sqDist p.1 (D.φ x) := hG.flat x hx p.1 hp1

theorem Good.env_pos (hG : D.Good f yc) {x : σ → ℝ} (hx : x ∈ D.K) {c : κ → ℝ}
    (hc : c ∈ D.Bbar) (hne : c ≠ D.φ x) : 0 < D.env x c := by
  have hv : 0 < D.v x c := by
    rcases (hG.v_nonneg hx hc).lt_or_eq with h | h
    · exact h
    · exact absurd ((hG.zero_iff x hx c hc).1 h.symm) hne
  exact (pow_pos hv _).trans_le (hG.env_ge hx hc)

/-- `J ≤ 1` on admissible choices. -/
theorem Good.envJ_le_one (hG : D.Good f yc) (x : σ → ℝ) {r : ℕ}
    {p : (Fin r → ℝ) × (Fin r → κ → ℝ) × (Fin r → ℝ)} (hp : p ∈ envAdm (D.At x) r)
    (c : κ → ℝ) : envJ D.a D.N p.1 p.2.1 p.2.2 c ≤ 1 := by
  obtain ⟨hl, hsum, hat⟩ := hp
  have ha := hG.a_pos
  unfold envJ
  simp only
  have h1 : ∑ i, p.1 i * p.2.2 i ^ D.N ≤ ∑ i, p.1 i := by
    refine Finset.sum_le_sum fun i _ => ?_
    have hs := hG.At_s x _ (hat i)
    have : p.2.2 i ^ D.N ≤ 1 := pow_le_one₀ hs.1 hs.2
    nlinarith [hl i]
  have h2 : 0 ≤ ∑ i, p.1 i * sqDist (p.2.1 i) (fun k => ∑ i, p.1 i * p.2.1 i k) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hl i) (sd_nonneg _ _)
  have h3 := sd_nonneg c (fun k => ∑ i, p.1 i * p.2.1 i k)
  nlinarith

/-- For `x ∈ K`, `e(x; c)` is the largest value of `J`. -/
theorem Good.isGreatest_env (hG : D.Good f yc) {x : σ → ℝ} (hx : x ∈ D.K) (c : κ → ℝ) :
    IsGreatest ((fun p => envJ D.a D.N p.1 p.2.1 p.2.2 c) ''
      envAdm (D.At x) (Fintype.card κ + 3)) (D.env x c) := by
  obtain ⟨p, hp, hpe⟩ := (hG.envProps hx).1 c
  refine ⟨⟨p, hp, hpe⟩, ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  exact le_csSup ⟨1, by rintro _ ⟨q', hq', rfl⟩; exact hG.envJ_le_one x hq' c⟩ ⟨q, hq, rfl⟩

variable (D)

/-- An admissible configuration of `r` atoms over `x`. -/
def CfgOK {r : ℕ} (x : σ → ℝ) (z : Cfg κ M r → ℝ) : Prop :=
  (∀ i, 0 ≤ Cfg.lam z i) ∧ ∑ i, Cfg.lam z i = 1 ∧
    ∀ i, D.InY x (Cfg.om z i) (Cfg.nu z i) (Cfg.s z i)

/-- The value of `J` at a configuration. -/
def cfgJ {r : ℕ} (z : Cfg κ M r → ℝ) (c : κ → ℝ) : ℝ :=
  envJ D.a D.N (Cfg.lam z) (Cfg.om z) (Cfg.s z) c

variable {D}

theorem mem_envAdm_iff {r : ℕ} (x : σ → ℝ)
    (p : (Fin r → ℝ) × (Fin r → κ → ℝ) × (Fin r → ℝ)) :
    p ∈ envAdm (D.At x) r ↔ ∃ z, D.CfgOK x z ∧ (Cfg.lam z, Cfg.om z, Cfg.s z) = p := by
  constructor
  · rintro ⟨hl, hsum, hat⟩
    choose ν hν using hat
    exact ⟨Cfg.mk p.1 p.2.1 p.2.2 ν, ⟨hl, hsum, hν⟩, rfl⟩
  · rintro ⟨z, ⟨hl, hsum, hat⟩, rfl⟩
    exact ⟨hl, hsum, fun i => ⟨_, hat i⟩⟩

/-- The first-order description of `e(x; c)`. -/
theorem Good.env_eq_iff (hG : D.Good f yc) {x : σ → ℝ} (hx : x ∈ D.K) (c : κ → ℝ) (t : ℝ) :
    D.env x c = t ↔ (∃ z : Cfg κ M (Fintype.card κ + 3) → ℝ, D.CfgOK x z ∧ D.cfgJ z c = t) ∧
      ∀ z : Cfg κ M (Fintype.card κ + 3) → ℝ, D.CfgOK x z → D.cfgJ z c ≤ t := by
  have hgr := hG.isGreatest_env hx c
  constructor
  · rintro rfl
    obtain ⟨⟨p, hp, hpe⟩, hub⟩ := hgr
    obtain ⟨z, hz, rfl⟩ := (mem_envAdm_iff x p).1 hp
    refine ⟨⟨z, hz, hpe⟩, fun z' hz' => hub ⟨_, (mem_envAdm_iff x _).2 ⟨z', hz', rfl⟩, rfl⟩⟩
  · rintro ⟨⟨z, hz, rfl⟩, hub⟩
    refine le_antisymm ?_ (hgr.2 ⟨_, (mem_envAdm_iff x _).2 ⟨z, hz, rfl⟩, rfl⟩)
    obtain ⟨p, hp, hpe⟩ := hgr.1
    obtain ⟨z', hz', rfl⟩ := (mem_envAdm_iff x p).1 hp
    rw [← hpe]
    exact hub z' hz'

/-- The value `J` at an admissible configuration is at most `e`. -/
theorem Good.cfgJ_le_env (hG : D.Good f yc) {x : σ → ℝ} (hx : x ∈ D.K) (c : κ → ℝ)
    {z : Cfg κ M (Fintype.card κ + 3) → ℝ} (hz : D.CfgOK x z) : D.cfgJ z c ≤ D.env x c :=
  ((hG.env_eq_iff hx c _).1 rfl).2 z hz

/-- `e` is attained at an admissible configuration. -/
theorem Good.exists_cfg (hG : D.Good f yc) {x : σ → ℝ} (hx : x ∈ D.K) (c : κ → ℝ) :
    ∃ z : Cfg κ M (Fintype.card κ + 3) → ℝ, D.CfgOK x z ∧ D.cfgJ z c = D.env x c :=
  ((hG.env_eq_iff hx c _).1 rfl).1

variable [DecidableEq κ]

/-- The gradient of `e(x; ·)` at a maximizing configuration. -/
theorem Good.grad_eq (hG : D.Good f yc) {x : σ → ℝ} (hx : x ∈ D.K) (c : κ → ℝ)
    {z : Cfg κ M (Fintype.card κ + 3) → ℝ} (hz : D.CfgOK x z) (hzJ : D.cfgJ z c = D.env x c)
    (k : κ) : D.grad x c k = 4 * D.a * (∑ i, Cfg.lam z i * Cfg.om z i k - c k) := by
  have := (hG.envProps hx).2.2.1 c _ ((mem_envAdm_iff x _).2 ⟨z, hz, rfl⟩) hzJ
    (Pi.single k 1)
  rw [grad, this]
  congr 1
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hj; simp [hj]
  · simp

/-! ### (S1): the envelope and its gradient are semialgebraic -/

variable (D)

theorem isSA_InY {ι : Type} (fx : σ → ι) (fw : κ → ι) (fν : Fin M → ι) (fs : ι) :
    IsSA {u : ι → ℝ | D.InY (u ∘ fx) (u ∘ fw) (u ∘ fν) (u fs)} := by
  unfold InY
  refine FO.isSA_and ((isSA_closedBall D.x₀ D.ρ).preimage_comp fx)
    (FO.isSA_and ?_ (FO.isSA_and ?_ ?_))
  · exact FO.isSA_le (isPolyFn_sqDist (fun k => FO.IsPolyFn.coord _)
      (fun k => FO.IsPolyFn.const _)) (FO.IsPolyFn.const _)
  · exact FO.isSA_le (FO.IsPolyFn.const 0) (FO.IsPolyFn.coord fs)
  · refine FO.isSA_exists_fin fun b => FO.isSA_eq ?_ (FO.IsPolyFn.const 0)
    refine FO.IsPolyFn.eval_comp (fun i => ?_) _
    rcases i with i | k | _ | m
    · exact FO.IsPolyFn.coord (fx i)
    · exact FO.IsPolyFn.coord (fw k)
    · exact FO.IsPolyFn.coord fs
    · exact FO.IsPolyFn.coord (fν m)

theorem isSA_cfgOK {ι : Type} {r : ℕ} (gx : σ → ι) (gz : Cfg κ M r → ι) :
    IsSA {u : ι → ℝ | D.CfgOK (u ∘ gx) (u ∘ gz)} := by
  unfold CfgOK
  refine FO.isSA_and (FO.isSA_forall_fin fun i => ?_) (FO.isSA_and ?_
    (FO.isSA_forall_fin fun i => ?_))
  · exact FO.isSA_le (FO.IsPolyFn.const 0) (FO.IsPolyFn.coord _)
  · exact FO.isSA_eq (isPolyFn_sum _ fun i => FO.IsPolyFn.coord _) (FO.IsPolyFn.const 1)
  · exact D.isSA_InY gx (fun k => gz (Sum.inr (Sum.inl (i, k))))
      (fun m => gz (Sum.inr (Sum.inr (Sum.inr (i, m))))) (gz (Sum.inr (Sum.inr (Sum.inl i))))

theorem isPolyFn_cfgJ {ι : Type} {r : ℕ} (gz : Cfg κ M r → ι) (gc : κ → ι) :
    FO.IsPolyFn (fun u : ι → ℝ => D.cfgJ (u ∘ gz) (u ∘ gc)) :=
  isPolyFn_envJ _ _ (fun _ => FO.IsPolyFn.coord _) (fun _ _ => FO.IsPolyFn.coord _)
    (fun _ => FO.IsPolyFn.coord _) (fun _ => FO.IsPolyFn.coord _)

theorem isSA_Kξ : IsSA D.Kξ := (isSA_closedBall D.x₀ D.ρ).preimage_comp Sum.inl

theorem isSA_OK : IsSA D.OK := (isSA_ball D.x₀ D.ρ).preimage_comp Sum.inl

variable {D}

/-- **(S1)**: the graph of `e` over `K`, with arbitrary positions of the variables. -/
theorem Good.isSA_env_eq (hG : D.Good f yc) {ι : Type} (gx : σ → ι) (gc : κ → ι) (gt : ι) :
    IsSA {u : ι → ℝ | u ∘ gx ∈ D.K ∧ D.env (u ∘ gx) (u ∘ gc) = u gt} := by
  have key : IsSA {u : ι → ℝ | u ∘ gx ∈ D.K ∧
      ((∃ z : Cfg κ M (Fintype.card κ + 3) → ℝ, D.CfgOK (u ∘ gx) z ∧
        D.cfgJ z (u ∘ gc) = u gt) ∧
      ∀ z : Cfg κ M (Fintype.card κ + 3) → ℝ, D.CfgOK (u ∘ gx) z →
        D.cfgJ z (u ∘ gc) ≤ u gt)} := by
    refine FO.isSA_and ((isSA_closedBall D.x₀ D.ρ).preimage_comp _) (FO.isSA_and ?_ ?_)
    · refine FO.isSA_exists_fun (FO.isSA_and ?_ ?_)
      · exact D.isSA_cfgOK (Sum.inl ∘ gx) Sum.inr
      · exact FO.isSA_eq (D.isPolyFn_cfgJ Sum.inr (Sum.inl ∘ gc)) (FO.IsPolyFn.coord _)
    · refine FO.isSA_forall_fun (FO.isSA_imp ?_ ?_)
      · exact D.isSA_cfgOK (Sum.inl ∘ gx) Sum.inr
      · exact FO.isSA_le (D.isPolyFn_cfgJ Sum.inr (Sum.inl ∘ gc)) (FO.IsPolyFn.coord _)
  convert key using 1
  ext u
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨hx, hv⟩
    exact ⟨hx, (hG.env_eq_iff hx _ _).1 hv⟩
  · rintro ⟨hx, hv⟩
    exact ⟨hx, (hG.env_eq_iff hx _ _).2 hv⟩

/-- **(S1)**: the envelope is semialgebraic on `K × ℝ^κ`. -/
theorem Good.isSAFunOn_envξ (hG : D.Good f yc) : IsSAFunOn₁ D.Kξ D.envξ := by
  refine ⟨D.isSA_Kξ, ?_⟩
  have key := hG.isSA_env_eq (Sum.inl ∘ Sum.inl) (Sum.inl ∘ Sum.inr) (Sum.inr ())
  convert key using 1
  ext v
  simp only [mem_ofPred_eq, Kξ]
  constructor
  · rintro ⟨hx, hv⟩
    exact ⟨hx, congrFun hv ()⟩
  · rintro ⟨hx, hv⟩
    exact ⟨hx, funext fun _ => hv⟩

/-- **(S1)**: the gradient of the envelope in `c` is semialgebraic on `K × ℝ^κ`. -/
theorem Good.isSAFunOn_grad (hG : D.Good f yc) :
    IsSAFunOn D.Kξ (fun ξ k => D.grad (ξ ∘ Sum.inl) (ξ ∘ Sum.inr) k) := by
  refine isSAFunOn_iff_coord.2 ⟨D.isSA_Kξ, fun k => ⟨D.isSA_Kξ, ?_⟩⟩
  have key : IsSA {v : (σ ⊕ κ) ⊕ Unit → ℝ | v ∘ Sum.inl ∘ Sum.inl ∈ D.K ∧
      ∃ z : Cfg κ M (Fintype.card κ + 3) → ℝ, D.CfgOK (v ∘ Sum.inl ∘ Sum.inl) z ∧
        (∀ z' : Cfg κ M (Fintype.card κ + 3) → ℝ, D.CfgOK (v ∘ Sum.inl ∘ Sum.inl) z' →
          D.cfgJ z' (v ∘ Sum.inl ∘ Sum.inr) ≤ D.cfgJ z (v ∘ Sum.inl ∘ Sum.inr)) ∧
        v (Sum.inr ()) = 4 * D.a * (∑ i, Cfg.lam z i * Cfg.om z i k - v (Sum.inl (Sum.inr k)))}
      := by
    refine FO.isSA_and ((isSA_closedBall D.x₀ D.ρ).preimage_comp _) ?_
    refine FO.isSA_exists_fun (FO.isSA_and ?_ (FO.isSA_and ?_ ?_))
    · exact D.isSA_cfgOK (Sum.inl ∘ Sum.inl ∘ Sum.inl) Sum.inr
    · refine FO.isSA_forall_fun (FO.isSA_imp ?_ ?_)
      · exact D.isSA_cfgOK (Sum.inl ∘ Sum.inl ∘ Sum.inl ∘ Sum.inl) Sum.inr
      · exact FO.isSA_le (D.isPolyFn_cfgJ Sum.inr (Sum.inl ∘ Sum.inl ∘ Sum.inl ∘ Sum.inr))
          (D.isPolyFn_cfgJ (Sum.inl ∘ Sum.inr) (Sum.inl ∘ Sum.inl ∘ Sum.inl ∘ Sum.inr))
    · exact FO.isSA_eq (FO.IsPolyFn.coord _) ((FO.IsPolyFn.const _).mul
        ((isPolyFn_sum _ fun i => (FO.IsPolyFn.coord _).mul (FO.IsPolyFn.coord _)).sub
          (FO.IsPolyFn.coord _)))
  convert key using 1
  ext v
  simp only [mem_ofPred_eq, Kξ]
  constructor
  · rintro ⟨hx, hv⟩
    refine ⟨hx, ?_⟩
    have hv' : D.grad (v ∘ Sum.inl ∘ Sum.inl) (v ∘ Sum.inl ∘ Sum.inr) k = v (Sum.inr ()) :=
      congrFun hv ()
    obtain ⟨⟨z, hz, hzJ⟩, hub⟩ := (hG.env_eq_iff hx (v ∘ Sum.inl ∘ Sum.inr) _).1 rfl
    refine ⟨z, hz, fun z' hz' => hzJ ▸ hub z' hz', ?_⟩
    rw [← hv']
    exact hG.grad_eq hx _ hz hzJ k
  · rintro ⟨hx, z, hz, hmax, hv⟩
    refine ⟨hx, funext fun _ => ?_⟩
    have hzJ : D.cfgJ z (v ∘ Sum.inl ∘ Sum.inr) = D.env (v ∘ Sum.inl ∘ Sum.inl)
        (v ∘ Sum.inl ∘ Sum.inr) :=
      ((hG.env_eq_iff hx _ _).2 ⟨⟨z, hz, rfl⟩, hmax⟩).symm
    show D.grad _ _ k = v (Sum.inr ())
    rw [hv]
    exact hG.grad_eq hx _ hz hzJ k

/-- Where `e` is differentiable jointly in `(x, c)`, the gradient in `c` is the partial
derivative of the joint function. -/
theorem Good.grad_eq_pd [DecidableEq σ] (hG : D.Good f yc) {x : σ → ℝ} (hx : x ∈ D.K)
    {c : κ → ℝ} (h : DifferentiableAt ℝ D.envξ (Sum.elim x c)) (k : κ) :
    D.grad x c k = pd D.envξ (Sum.inr k) (Sum.elim x c) := by
  have hl1 : HasDerivAt (fun t : ℝ => c + t • (Pi.single k 1 : κ → ℝ)) (Pi.single k 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single k 1 : κ → ℝ)).const_add c
  have hl2 : HasDerivAt (fun t : ℝ => Sum.elim x c + t • (Pi.single (Sum.inr k) 1 : σ ⊕ κ → ℝ))
      (Pi.single (Sum.inr k) 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
      (Pi.single (Sum.inr k) 1 : σ ⊕ κ → ℝ)).const_add (Sum.elim x c)
  have h1 := ((hG.differentiable_env hx) c).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl1
    (by simp)
  have h2 := h.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl2 (by simp)
  have heq : (D.env x ∘ fun t : ℝ => c + t • (Pi.single k 1 : κ → ℝ)) =
      (D.envξ ∘ fun t : ℝ => Sum.elim x c + t • (Pi.single (Sum.inr k) 1 : σ ⊕ κ → ℝ)) := by
    funext t
    simp only [Function.comp_apply]
    rw [← envξ_elim]
    congr 1
    funext i
    rcases i with i | j
    · simp
    · by_cases hj : j = k
      · subst hj; simp
      · simp [hj]
  rw [heq] at h1
  exact h1.unique h2

end SLData

end ClassSep
