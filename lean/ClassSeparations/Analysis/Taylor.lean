import Mathlib

/-!
# Taylor polynomials as multivariate polynomials

For `g : ℝ^ι → ℝ`, a point `ξ₁` and an order `D`, the Taylor polynomial of order `D` of `g` at
`ξ₁` is the polynomial
`∑_{j ≤ D} (1/j!) Dʲg(ξ₁)(X - ξ₁, …, X - ξ₁) ∈ ℝ[X_i : i ∈ ι]`.
We prove the facts used in the paper: Taylor's theorem in little-`o` form for functions of
class `C^D`, uniqueness of polynomial approximations of order `o(|ξ - ξ₁|^D)`, the fact that a
polynomial of degree `≤ D` is its own Taylor polynomial of order `D`, and continuity of the
coefficients in the derivatives.
-/

noncomputable section

open MvPolynomial Filter Topology Asymptotics

namespace ClassSep

universe u

/-! ### Taylor's theorem in little-`o` form for general normed spaces -/

section General

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The value at `x` of the Taylor expansion of order `D` of `f` at `x₀`. -/
def taylorSum {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] (D : ℕ) (f : E → F)
    (x₀ x : E) : F :=
  ∑ j ∈ Finset.range (D + 1), ((j.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ j f x₀ (fun _ => x - x₀)

/-- **Taylor's theorem** in little-`o` form, for functions between normed spaces. The proof is
by induction on `D`, applying the induction hypothesis to `fderiv ℝ f` and the mean value
inequality along the segment `[x₀, x]` (only radial derivatives are used, so no symmetry of the
iterated derivatives is needed). -/
theorem taylorSum_isLittleO :
    ∀ (D : ℕ) {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {x₀ : E},
      ContDiffAt ℝ D f x₀ → (fun x => f x - taylorSum D f x₀ x) =o[𝓝 x₀] fun x => ‖x - x₀‖ ^ D
  | 0, F, _, _, f, x₀, hf => by
    simp only [taylorSum, zero_add, Finset.sum_range_one, Nat.factorial_zero, Nat.cast_one,
      inv_one, one_smul, iteratedFDeriv_zero_apply, pow_zero]
    exact (isLittleO_one_iff ℝ).mpr (tendsto_sub_nhds_zero_iff.mpr hf.continuousAt.tendsto)
  | D + 1, F, _, _, f, x₀, hf => by
    have IH := taylorSum_isLittleO D (F := E →L[ℝ] F) (hf.fderiv_right (m := D) (by simp))
    have hdiff : ∀ᶠ y in 𝓝 x₀, DifferentiableAt ℝ f y :=
      (hf.eventually (by simp)).mono fun y hy => hy.differentiableAt (by simp)
    rw [isLittleO_iff] at IH ⊢
    intro c hc
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp ((IH hc).and hdiff)
    filter_upwards [Metric.ball_mem_nhds x₀ hε] with x hx
    set h := x - x₀ with hh
    -- the points of the segment `[x₀, x]`
    have hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, x₀ + t • h ∈ Metric.ball x₀ ε := by
      intro t ht
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg ht.1]
      rw [Metric.mem_ball, dist_eq_norm] at hx
      calc t * ‖h‖ ≤ 1 * ‖h‖ := by gcongr; exact ht.2
        _ = ‖h‖ := one_mul _
        _ < ε := hx
    set M : ℕ → F := fun j => iteratedFDeriv ℝ j f x₀ (fun _ => h) with hM
    let φ : ℝ → F := fun t =>
      f (x₀ + t • h) - ∑ j ∈ Finset.range (D + 2), (t ^ j * (j.factorial : ℝ)⁻¹) • M j
    let φ' : ℝ → F := fun t =>
      (fderiv ℝ f (x₀ + t • h) - taylorSum D (fderiv ℝ f) x₀ (x₀ + t • h)) h
    -- the radial derivative of the Taylor polynomial
    have hφ'eq : ∀ t : ℝ, φ' t = fderiv ℝ f (x₀ + t • h) h -
        ∑ j ∈ Finset.range (D + 2), ((j : ℝ) * t ^ (j - 1) * (j.factorial : ℝ)⁻¹) • M j := by
      intro t
      simp only [φ', sub_apply, taylorSum, add_sub_cancel_left]
      congr 1
      rw [Finset.sum_range_succ' _ (D + 1)]
      simp only [CharP.cast_eq_zero, zero_mul, zero_smul, add_zero,
        FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
        Pi.smul_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 : (iteratedFDeriv ℝ i (fderiv ℝ f) x₀ fun _ => t • h) =
          t ^ i • iteratedFDeriv ℝ i (fderiv ℝ f) x₀ fun _ => h := by
        rw [ContinuousMultilinearMap.map_smul_univ]
        simp
      have h2 : (iteratedFDeriv ℝ i (fderiv ℝ f) x₀ fun _ => h) h = M (i + 1) := by
        simp only [hM]
        rw [iteratedFDeriv_succ_apply_right]
        rfl
      rw [h1, smul_apply, h2, smul_smul, Nat.add_sub_cancel,
        Nat.factorial_succ, Nat.cast_mul]
      congr 1
      have : (i.factorial : ℝ) ≠ 0 := by positivity
      field_simp
    have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt φ (φ' t) (Set.Icc (0 : ℝ) 1) t := by
      intro t ht
      refine HasDerivAt.hasDerivWithinAt ?_
      rw [hφ'eq]
      have hline : HasDerivAt (fun s : ℝ => x₀ + s • h) h t := by
        simpa using ((hasDerivAt_id t).smul_const h).const_add x₀
      have hf' : HasDerivAt (fun s : ℝ => f (x₀ + s • h)) (fderiv ℝ f (x₀ + t • h) h) t :=
        ((hball _ (hseg t ht)).2.hasFDerivAt).comp_hasDerivAt t hline
      refine hf'.sub ?_
      have := HasDerivAt.sum (u := Finset.range (D + 2))
        (A := fun j s => (s ^ j * (j.factorial : ℝ)⁻¹) • M j)
        (A' := fun j => ((j : ℝ) * t ^ (j - 1) * (j.factorial : ℝ)⁻¹) • M j) (x := t)
        (fun j _ => ((hasDerivAt_pow j t).mul_const _).smul_const (M j))
      convert this using 1
      ext s
      simp
    have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1, ‖φ' t‖ ≤ c * ‖h‖ ^ (D + 1) := by
      intro t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self ht
      have hb := (hball _ (hseg t ht')).1
      rw [add_sub_cancel_left, norm_pow, norm_norm, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg ht.1] at hb
      calc ‖φ' t‖ ≤ ‖fderiv ℝ f (x₀ + t • h) - taylorSum D (fderiv ℝ f) x₀ (x₀ + t • h)‖ * ‖h‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ c * (t * ‖h‖) ^ D * ‖h‖ := by gcongr
        _ ≤ c * (1 * ‖h‖) ^ D * ‖h‖ := by
            gcongr
            · exact mul_nonneg ht.1 (norm_nonneg _)
            · exact ht.2.le
        _ = c * ‖h‖ ^ (D + 1) := by ring
    have hmain := norm_image_sub_le_of_norm_deriv_le_segment_01' hderiv hbound
    have hφ1 : φ 1 = f x - taylorSum (D + 1) f x₀ x := by
      simp only [φ, taylorSum, one_pow, one_mul, one_smul, hh, add_sub_cancel, hM]
    have hφ0 : φ 0 = 0 := by
      simp only [φ, zero_smul, add_zero]
      rw [Finset.sum_range_succ']
      simp [hM]
    rw [hφ1, hφ0, sub_zero] at hmain
    simpa only [norm_pow, norm_norm] using hmain

end General

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The polynomial `Dʲg(ξ₁)(X - ξ₁, …, X - ξ₁)` written in the monomial basis. -/
def jetTerm (j : ℕ) (L : ContinuousMultilinearMap ℝ (fun _ : Fin j => ι → ℝ) ℝ)
    (ξ₁ : ι → ℝ) : MvPolynomial ι ℝ :=
  ∑ i : Fin j → ι, MvPolynomial.C (L fun k => Pi.single (i k) 1) *
    ∏ k : Fin j, (X (i k) - MvPolynomial.C (ξ₁ (i k)))

/-- The Taylor polynomial of order `D` of `g` at `ξ₁`. -/
def taylorPoly (D : ℕ) (g : (ι → ℝ) → ℝ) (ξ₁ : ι → ℝ) : MvPolynomial ι ℝ :=
  ∑ j ∈ Finset.range (D + 1),
    MvPolynomial.C ((j.factorial : ℝ)⁻¹) * jetTerm j (iteratedFDeriv ℝ j g ξ₁) ξ₁

theorem eval_jetTerm (j : ℕ) (L : ContinuousMultilinearMap ℝ (fun _ : Fin j => ι → ℝ) ℝ)
    (ξ₁ ξ : ι → ℝ) : eval ξ (jetTerm j L ξ₁) = L fun _ => ξ - ξ₁ := by
  have hdec : ξ - ξ₁ = ∑ i, (ξ i - ξ₁ i) • (Pi.single i 1 : ι → ℝ) := by
    ext l
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hdec, ContinuousMultilinearMap.map_sum]
  simp only [ContinuousMultilinearMap.map_smul_univ, jetTerm, map_sum, map_mul, eval_C, map_prod,
    map_sub, eval_X, smul_eq_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

theorem totalDegree_jetTerm_le (j : ℕ)
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin j => ι → ℝ) ℝ) (ξ₁ : ι → ℝ) :
    (jetTerm j L ξ₁).totalDegree ≤ j := by
  unfold jetTerm
  refine totalDegree_finsetSum_le fun i _ => ?_
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ k : Fin j, (X (i k) - C (ξ₁ (i k)) : MvPolynomial ι ℝ).totalDegree
      ≤ ∑ _k : Fin j, 1 :=
        Finset.sum_le_sum fun k _ => (totalDegree_sub_C_le _ _).trans (totalDegree_X _).le
    _ = j := by simp

theorem totalDegree_taylorPoly_le (D : ℕ) (g : (ι → ℝ) → ℝ) (ξ₁ : ι → ℝ) :
    (taylorPoly D g ξ₁).totalDegree ≤ D := by
  unfold taylorPoly
  refine totalDegree_finsetSum_le fun j hj => ?_
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  exact (totalDegree_jetTerm_le _ _ _).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))

theorem eval_taylorPoly (D : ℕ) (g : (ι → ℝ) → ℝ) (ξ₁ ξ : ι → ℝ) :
    eval ξ (taylorPoly D g ξ₁) = taylorSum D g ξ₁ ξ := by
  simp only [taylorPoly, taylorSum, map_sum, map_mul, eval_C, eval_jetTerm, smul_eq_mul]

/-- **Taylor's theorem** in little-`o` form. -/
theorem taylorPoly_isLittleO {D : ℕ} {g : (ι → ℝ) → ℝ} {ξ₁ : ι → ℝ}
    (hg : ContDiffAt ℝ D g ξ₁) :
    (fun ξ => g ξ - eval ξ (taylorPoly D g ξ₁)) =o[𝓝 ξ₁] fun ξ => ‖ξ - ξ₁‖ ^ D := by
  simpa only [eval_taylorPoly] using taylorSum_isLittleO D hg

/-- A univariate real polynomial of degree `≤ D` which is `o(s^D)` as `s → 0` vanishes. -/
theorem poly_eq_zero_of_isLittleO :
    ∀ (D : ℕ) {p : Polynomial ℝ}, p.natDegree ≤ D →
      (fun s => p.eval s) =o[𝓝[≠] (0 : ℝ)] (fun s => s ^ D) → p = 0
  | 0, p, hp, h => by
    rw [Nat.le_zero, Polynomial.natDegree_eq_zero] at hp
    obtain ⟨c, rfl⟩ := hp
    simp only [Polynomial.eval_C, pow_zero] at h
    have := (isLittleO_one_iff ℝ).mp h
    rw [tendsto_const_nhds_iff] at this
    simp [this]
  | D + 1, p, hp, h => by
    have h0 : p.coeff 0 = 0 := by
      have h1 : Tendsto (fun s => p.eval s) (𝓝[≠] 0) (𝓝 0) := by
        refine h.trans_tendsto ?_
        have : Tendsto (fun s : ℝ => s ^ (D + 1)) (𝓝 0) (𝓝 0) := by
          simpa using ((continuous_pow (D + 1)).tendsto (0 : ℝ))
        exact this.mono_left nhdsWithin_le_nhds
      have h2 : Tendsto (fun s => p.eval s) (𝓝[≠] 0) (𝓝 (p.eval 0)) :=
        p.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      rw [Polynomial.coeff_zero_eq_eval_zero]
      exact tendsto_nhds_unique h2 h1
    have hpq : p = Polynomial.X * p.divX := by
      conv_lhs => rw [← Polynomial.X_mul_divX_add p]
      rw [h0, map_zero, add_zero]
    have hq : p.divX = 0 := by
      refine poly_eq_zero_of_isLittleO D ?_ ?_
      · rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one]
        omega
      · have := (isBigO_refl (fun s : ℝ => s⁻¹) (𝓝[≠] (0 : ℝ))).mul_isLittleO h
        refine this.congr' ?_ ?_
        · filter_upwards [self_mem_nhdsWithin] with s hs
          have hs' : s ≠ 0 := hs
          conv_lhs => rw [hpq]
          simp only [Polynomial.eval_mul, Polynomial.eval_X]
          field_simp
        · filter_upwards [self_mem_nhdsWithin] with s hs
          have hs' : s ≠ 0 := hs
          field_simp
          ring
    rw [hpq, hq, mul_zero]

omit [Fintype ι] [DecidableEq ι] in
/-- The natural degree of the restriction of a multivariate polynomial to an affine line is at
most its total degree. -/
theorem natDegree_aeval_le (Q : MvPolynomial ι ℝ) (g : ι → Polynomial ℝ)
    (hg : ∀ i, (g i).natDegree ≤ 1) : (aeval g Q).natDegree ≤ Q.totalDegree := by
  conv_lhs => rw [Q.as_sum]
  rw [map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
  rw [aeval_monomial, Polynomial.algebraMap_eq]
  refine Polynomial.natDegree_mul_le.trans ?_
  rw [Polynomial.natDegree_C, zero_add]
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  refine le_trans ?_ (le_totalDegree hm)
  refine Finset.sum_le_sum fun i _ => Polynomial.natDegree_pow_le.trans ?_
  calc m i * (g i).natDegree ≤ m i * 1 := Nat.mul_le_mul_left _ (hg i)
    _ = m i := mul_one _

set_option linter.unusedSectionVars false in
/-- **Uniqueness**: two polynomials of degree `≤ D` that agree up to `o(|ξ - ξ₁|^D)` are
equal. -/
theorem eq_of_isLittleO {D : ℕ} {P P' : MvPolynomial ι ℝ} {ξ₁ : ι → ℝ}
    (hP : P.totalDegree ≤ D) (hP' : P'.totalDegree ≤ D)
    (h : (fun ξ => eval ξ P - eval ξ P') =o[𝓝 ξ₁] fun ξ => ‖ξ - ξ₁‖ ^ D) : P = P' := by
  set Q := P - P' with hQ
  have hQdeg : Q.totalDegree ≤ D := (totalDegree_sub _ _).trans (max_le hP hP')
  have hQ' : (fun ξ => eval ξ Q) =o[𝓝 ξ₁] fun ξ => ‖ξ - ξ₁‖ ^ D := by
    simpa only [hQ, map_sub] using h
  suffices hz : ∀ ξ, eval ξ Q = 0 by
    refine MvPolynomial.funext fun ξ => ?_
    have := hz ξ
    rwa [hQ, map_sub, sub_eq_zero] at this
  intro ξ
  set u := ξ - ξ₁ with hu
  set p : Polynomial ℝ :=
    aeval (fun i => Polynomial.C (ξ₁ i) + Polynomial.C (u i) * Polynomial.X) Q with hp
  have hp_eval : ∀ s : ℝ, p.eval s = eval (ξ₁ + s • u) Q := by
    intro s
    rw [← Polynomial.coe_aeval_eq_eval, hp, ← AlgHom.comp_apply, comp_aeval]
    have e1 : (fun i => Polynomial.aeval s
        (Polynomial.C (ξ₁ i) + Polynomial.C (u i) * Polynomial.X)) = ξ₁ + s • u := by
      ext i
      simp only [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
        Algebra.algebraMap_self, RingHom.id_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e1]
    rfl
  have hp_deg : p.natDegree ≤ D := by
    refine (natDegree_aeval_le Q _ fun i => ?_).trans hQdeg
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · simp
    · exact (Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_X_le)
  have hp_o : (fun s => p.eval s) =o[𝓝[≠] (0 : ℝ)] (fun s => s ^ D) := by
    have ht : Tendsto (fun s : ℝ => ξ₁ + s • u) (𝓝[≠] 0) (𝓝 ξ₁) := by
      have hc : Continuous (fun s : ℝ => ξ₁ + s • u) := by fun_prop
      have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ))
      simpa using this
    have h2 := hQ'.comp_tendsto ht
    refine (h2.trans_isBigO ?_).congr_left fun s => (hp_eval s).symm
    refine IsBigO.of_bound (‖u‖ ^ D) (Eventually.of_forall fun s => ?_)
    simp only [Function.comp_apply, add_sub_cancel_left]
    rw [norm_pow, norm_norm, norm_pow, norm_smul, mul_pow]
    exact le_of_eq (mul_comm _ _)
  have hp0 := poly_eq_zero_of_isLittleO D hp_deg hp_o
  have h1 := hp_eval 1
  rw [hp0, Polynomial.eval_zero, one_smul, hu, add_sub_cancel] at h1
  exact h1.symm

/-- The Taylor polynomial of a `C^D` function is the unique polynomial of degree `≤ D` that
approximates it to order `o(|ξ - ξ₁|^D)`. -/
theorem taylorPoly_eq_of_isLittleO {D : ℕ} {g : (ι → ℝ) → ℝ} {ξ₁ : ι → ℝ}
    (hg : ContDiffAt ℝ D g ξ₁) {P : MvPolynomial ι ℝ} (hP : P.totalDegree ≤ D)
    (h : (fun ξ => g ξ - eval ξ P) =o[𝓝 ξ₁] fun ξ => ‖ξ - ξ₁‖ ^ D) :
    taylorPoly D g ξ₁ = P := by
  refine eq_of_isLittleO (ξ₁ := ξ₁) (totalDegree_taylorPoly_le D g ξ₁) hP ?_
  have := h.sub (taylorPoly_isLittleO hg)
  refine this.congr_left fun ξ => ?_
  ring

/-- A polynomial of degree `≤ D` is its own Taylor polynomial of order `D`. -/
theorem taylorPoly_eval_poly {D : ℕ} {f : MvPolynomial ι ℝ} (hf : f.totalDegree ≤ D)
    (ξ₁ : ι → ℝ) : taylorPoly D (fun ξ => eval ξ f) ξ₁ = f := by
  refine taylorPoly_eq_of_isLittleO ?_ hf ?_
  · exact (AnalyticOnNhd.eval_mvPolynomial f ξ₁ (Set.mem_univ _)).contDiffAt
  · simp only [sub_self]
    exact Asymptotics.isLittleO_zero _ _

/-- The Taylor polynomial depends only on the germ of `g` at `ξ₁`. -/
theorem taylorPoly_congr {D : ℕ} {g h : (ι → ℝ) → ℝ} {ξ₁ : ι → ℝ} (hgh : g =ᶠ[𝓝 ξ₁] h) :
    taylorPoly D g ξ₁ = taylorPoly D h ξ₁ := by
  unfold taylorPoly
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [(hgh.iteratedFDeriv ℝ j).eq_of_nhds]

/-- The coefficients of Taylor polynomials depend continuously on the base point and on the
derivatives: if the derivatives of order `≤ D` of `g_ε` converge to those of `g` at `ξ₁`,
uniformly near... (pointwise version) then the Taylor coefficients converge. -/
theorem tendsto_coeff_taylorPoly {D : ℕ} {β : Type*} {l : Filter β} {G : β → (ι → ℝ) → ℝ}
    {g : (ι → ℝ) → ℝ} {ξ₁ : ι → ℝ}
    (h : ∀ j ≤ D, Tendsto (fun b => iteratedFDeriv ℝ j (G b) ξ₁) l
      (𝓝 (iteratedFDeriv ℝ j g ξ₁))) (m : ι →₀ ℕ) :
    Tendsto (fun b => (taylorPoly D (G b) ξ₁).coeff m) l (𝓝 ((taylorPoly D g ξ₁).coeff m)) := by
  have key : ∀ g' : (ι → ℝ) → ℝ, (taylorPoly D g' ξ₁).coeff m =
      ∑ j ∈ Finset.range (D + 1), (j.factorial : ℝ)⁻¹ *
        ∑ i : Fin j → ι, iteratedFDeriv ℝ j g' ξ₁ (fun k => Pi.single (i k) 1) *
          (∏ k : Fin j, (X (i k) - C (ξ₁ (i k))) : MvPolynomial ι ℝ).coeff m := by
    intro g'
    simp only [taylorPoly, jetTerm, coeff_sum, coeff_C_mul, Finset.mul_sum]
  simp_rw [key]
  refine tendsto_finsetSum _ fun j hj => ?_
  refine Tendsto.const_mul _ (tendsto_finsetSum _ fun i _ => ?_)
  refine Tendsto.mul_const _ ?_
  exact (h j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).eval_const _

end ClassSep
