import ClassSeparations.SA.Lemmas
import ClassSeparations.SA.Complexity
import ClassSeparations.Second.Cited

/-!
# An effective bound for the leading Puiseux exponent (Lemma 6.3 (d), core)

Let `g : (0, σ₀) → ℝ` be nonnegative with `g(σ) → 0`, and suppose that its graph is defined by
a first-order formula `φ` in two free variables `(σ, y)`.  By effective quantifier elimination
(`EffectiveQE`) the graph is defined by a quantifier-free formula with at most `B` atoms of
degree at most `B`.  Each point of the graph is a zero of one of the atom polynomials (a graph
has empty interior), and all but finitely many are zeros of an atom of positive degree in `y`;
the product `P` of these has degree `≤ B²` and vanishes on the graph near `0`.  The leading
exponent `γ` of the Puiseux expansion of `g` (S7) is a slope of the Newton polygon of `P`,
a ratio of positive integers at most `deg P`, so `γ ≥ 1/B²` and `g(σ) ≤ L σ^{1/B²}` near `0`.
-/

noncomputable section

open Set Filter Topology

namespace ClassSep

/-- The bound `B` of effective quantifier elimination for a formula in two free variables. -/
def qeBound (C : ℕ) (φ : Fml (Fin 2)) : ℕ :=
  (φ.size + φ.maxDeg + 2) ^ ((φ.numBound + 2 + 2) ^ (C * (φ.blocks + 1)))

namespace ExpAux

open MvPolynomial

/-! ### Quantifier-free formulas are determined by the signs of their atoms -/

/-- The list of atom polynomials of a formula (atoms under quantifiers are omitted; they are
irrelevant for quantifier-free formulas). -/
def atoms : {α : Type} → Fml α → List (MvPolynomial α ℝ)
  | _, .pos p => [p]
  | _, .zero p => [p]
  | _, .not φ => atoms φ
  | _, .and φ ψ => atoms φ ++ atoms ψ
  | _, .ex _ => []

theorem length_atoms_le {α : Type} (φ : Fml α) : (atoms φ).length ≤ φ.size := by
  induction φ with
  | pos p => simp [atoms, Fml.size]
  | zero p => simp [atoms, Fml.size]
  | not φ ih => simpa [atoms, Fml.size] using ih
  | and φ ψ ih₁ ih₂ => simp only [atoms, Fml.size, List.length_append]; omega
  | ex φ _ => simp [atoms]

theorem totalDegree_le_of_mem_atoms {α : Type} (φ : Fml α) {p : MvPolynomial α ℝ}
    (hp : p ∈ atoms φ) : p.totalDegree ≤ φ.maxDeg := by
  induction φ with
  | pos q =>
    simp only [atoms, List.mem_singleton] at hp
    subst hp; simp [Fml.maxDeg]
  | zero q =>
    simp only [atoms, List.mem_singleton] at hp
    subst hp; simp [Fml.maxDeg]
  | not φ ih => exact ih hp
  | and φ ψ ih₁ ih₂ =>
    simp only [atoms, List.mem_append] at hp
    simp only [Fml.maxDeg]
    rcases hp with hp | hp
    · exact (ih₁ hp).trans (le_max_left _ _)
    · exact (ih₂ hp).trans (le_max_right _ _)
  | ex φ _ => simp [atoms] at hp

/-- The truth value of a quantifier-free formula depends only on the signs of its atoms. -/
theorem holds_congr {α : Type} (φ : Fml α) (hφ : φ.IsQF) (v w : α → ℝ)
    (h : ∀ p ∈ atoms φ, (0 < eval v p ↔ 0 < eval w p) ∧ (eval v p = 0 ↔ eval w p = 0)) :
    φ.Holds v ↔ φ.Holds w := by
  induction φ with
  | pos p => exact (h p (by simp [atoms])).1
  | zero p => exact (h p (by simp [atoms])).2
  | not φ ih =>
    simp only [Fml.Holds]
    exact not_congr (ih hφ v w h)
  | and φ ψ ih₁ ih₂ =>
    simp only [Fml.Holds]
    exact and_congr (ih₁ hφ.1 v w fun p hp => h p (by simp [atoms, hp]))
      (ih₂ hφ.2 v w fun p hp => h p (by simp [atoms, hp]))
  | ex φ _ => exact hφ.elim

/-- Near a point at which no nonzero atom vanishes, a quantifier-free formula has constant
truth value. -/
theorem eventually_holds_iff {α : Type} (φ : Fml α) (hφ : φ.IsQF) (v₀ : α → ℝ)
    (h : ∀ p ∈ atoms φ, p ≠ 0 → eval v₀ p ≠ 0) :
    ∀ᶠ v in 𝓝 v₀, (φ.Holds v ↔ φ.Holds v₀) := by
  classical
  have hev : ∀ p ∈ (atoms φ).toFinset, ∀ᶠ v in 𝓝 v₀,
      (0 < eval v p ↔ 0 < eval v₀ p) ∧ (eval v p = 0 ↔ eval v₀ p = 0) := by
    intro p hp
    rw [List.mem_toFinset] at hp
    by_cases hp0 : p = 0
    · subst hp0
      exact Eventually.of_forall fun v => by simp
    · have hne := h p hp hp0
      have hc : Tendsto (fun v => eval v p) (𝓝 v₀) (𝓝 (eval v₀ p)) :=
        (MvPolynomial.continuous_eval p).tendsto v₀
      rcases hne.lt_or_gt with hlt | hgt
      · filter_upwards [hc.eventually (gt_mem_nhds hlt)] with v hv
        exact ⟨iff_of_false (not_lt.2 hv.le) (not_lt.2 hlt.le), iff_of_false hv.ne hlt.ne⟩
      · filter_upwards [hc.eventually (lt_mem_nhds hgt)] with v hv
        exact ⟨iff_of_true hv hgt, iff_of_false hv.ne' hgt.ne'⟩
  filter_upwards [(Filter.eventually_all_finset _).2 hev] with v hv
  exact holds_congr φ hφ v v₀ fun p hp => hv p (List.mem_toFinset.2 hp)

/-! ### A polynomial vanishing on the graph -/

/-- Each point of the graph is a zero of a nonzero atom (the graph has empty interior). -/
theorem exists_atom_zero (ψ : Fml (Fin 2)) (hψ : ψ.IsQF) (g : ℝ → ℝ) (σ₀ : ℝ)
    (hgraph : ∀ σ ∈ Ioo 0 σ₀, ∀ y, ψ.Holds ![σ, y] ↔ y = g σ) {σ : ℝ} (hσ : σ ∈ Ioo 0 σ₀) :
    ∃ p ∈ atoms ψ, p ≠ 0 ∧ eval ![σ, g σ] p = 0 := by
  by_contra hcon
  push Not at hcon
  have hev := eventually_holds_iff ψ hψ ![σ, g σ] hcon
  have hcont : Continuous fun t : ℝ => ![σ, g σ + t] := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact continuous_const
    · exact continuous_const.add continuous_id
  have ht : Tendsto (fun t : ℝ => ![σ, g σ + t]) (𝓝[>] 0) (𝓝 ![σ, g σ]) := by
    have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using this
  obtain ⟨t, ht1, ht2⟩ := ((ht.eventually hev).and self_mem_nhdsWithin).exists
  have h1 : ψ.Holds ![σ, g σ] := (hgraph σ hσ (g σ)).2 rfl
  have h2 := (hgraph σ hσ (g σ + t)).1 (ht1.2 h1)
  have h3 : (0 : ℝ) < t := ht2
  linarith

/-- The product of the nonzero atoms vanishes on the graph. -/
theorem exists_poly (ψ : Fml (Fin 2)) (hψ : ψ.IsQF) (g : ℝ → ℝ) (σ₀ : ℝ)
    (hgraph : ∀ σ ∈ Ioo 0 σ₀, ∀ y, ψ.Holds ![σ, y] ↔ y = g σ) :
    ∃ P : MvPolynomial (Fin 2) ℝ, P ≠ 0 ∧ P.totalDegree ≤ ψ.size * ψ.maxDeg ∧
      ∀ σ ∈ Ioo 0 σ₀, eval ![σ, g σ] P = 0 := by
  classical
  let l := (atoms ψ).filter (fun p => p ≠ 0)
  refine ⟨l.prod, ?_, ?_, ?_⟩
  · refine List.prod_ne_zero fun h0 => ?_
    simp [l, List.mem_filter] at h0
  · refine (totalDegree_list_prod l).trans ?_
    have h1 : (l.map totalDegree).sum ≤ (l.map totalDegree).length • ψ.maxDeg :=
      List.sum_le_length_nsmul _ _ fun d hd => by
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hd
        exact totalDegree_le_of_mem_atoms ψ (List.mem_filter.1 hp).1
    have h2 : (l.map totalDegree).length ≤ ψ.size := by
      rw [List.length_map]
      exact (List.length_filter_le _ _).trans (length_atoms_le ψ)
    rw [smul_eq_mul] at h1
    exact h1.trans (Nat.mul_le_mul_right _ h2)
  · intro σ hσ
    obtain ⟨p, hp, hp0, hpz⟩ := exists_atom_zero ψ hψ g σ₀ hgraph hσ
    rw [map_list_prod]
    refine List.prod_eq_zero ?_
    rw [← hpz]
    exact List.mem_map_of_mem (List.mem_filter.2 ⟨hp, by simpa using hp0⟩)

/-! ### The Newton polygon argument -/

theorem eval_fin_two (P : MvPolynomial (Fin 2) ℝ) (x y : ℝ) :
    eval ![x, y] P = ∑ d ∈ P.support, P.coeff d * (x ^ d 0 * y ^ d 1) := by
  rw [eval_eq']
  simp [Fin.prod_univ_two]

theorem sum_fin_two_le_totalDegree {P : MvPolynomial (Fin 2) ℝ} {d : Fin 2 →₀ ℕ}
    (hd : d ∈ P.support) : d 0 + d 1 ≤ P.totalDegree := by
  have := le_totalDegree hd
  rwa [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two] at this

/-- If `P(s^M, s^j u(s)) = 0` for small `s > 0`, with `u(s) → c ≠ 0`, then the weight
`(a, b) ↦ M a + j b` takes equal values at two monomials of `P` with different `y`-degrees;
hence `M ≤ j · deg P`. -/
theorem newton (P : MvPolynomial (Fin 2) ℝ) (hP : P ≠ 0) (M j : ℕ) (hM : 0 < M) (hj : 0 < j)
    (u : ℝ → ℝ) (c : ℝ) (hc : c ≠ 0) (hu : Tendsto u (𝓝[>] 0) (𝓝 c))
    (hzero : ∀ᶠ s in 𝓝[>] (0 : ℝ), eval ![s ^ M, s ^ j * u s] P = 0) :
    M ≤ j * P.totalDegree := by
  classical
  set w : (Fin 2 →₀ ℕ) → ℕ := fun d => M * d 0 + j * d 1 with hw
  have hpair : ∃ d ∈ P.support, ∃ d' ∈ P.support, w d = w d' ∧ d 1 < d' 1 := by
    by_contra hcon
    push Not at hcon
    -- `w` is injective on the support
    have hinj : ∀ d ∈ P.support, ∀ d' ∈ P.support, w d = w d' → d = d' := by
      intro d hd d' hd' hdd
      have h1 : d 1 = d' 1 := le_antisymm (hcon d' hd' d hd hdd.symm) (hcon d hd d' hd' hdd)
      have h0 : d 0 = d' 0 := by
        have : M * d 0 = M * d' 0 := by simp only [hw] at hdd; rw [h1] at hdd; omega
        exact Nat.eq_of_mul_eq_mul_left hM this
      ext i
      fin_cases i
      · exact h0
      · exact h1
    obtain ⟨d₀, hd₀, hmin⟩ := P.support.exists_min_image w (Finset.nonempty_iff_ne_empty.2 fun h => hP (MvPolynomial.support_eq_empty.1 h))
    set e := w d₀
    let F : ℝ → ℝ := fun s => ∑ d ∈ P.support, P.coeff d * s ^ (w d - e) * u s ^ d 1
    have hF : ∀ s : ℝ, eval ![s ^ M, s ^ j * u s] P = s ^ e * F s := by
      intro s
      rw [eval_fin_two, Finset.mul_sum]
      refine Finset.sum_congr rfl fun d hd => ?_
      obtain ⟨k, hk⟩ : ∃ k, w d = e + k := ⟨w d - e, by have := hmin d hd; omega⟩
      have hk' : w d - e = k := by omega
      rw [hk']
      have hwd : M * d 0 + j * d 1 = e + k := hk
      calc P.coeff d * ((s ^ M) ^ d 0 * (s ^ j * u s) ^ d 1)
          = P.coeff d * (s ^ (M * d 0 + j * d 1) * u s ^ d 1) := by
            rw [pow_add, pow_mul, pow_mul, mul_pow]; ring
        _ = s ^ e * (P.coeff d * s ^ k * u s ^ d 1) := by rw [hwd, pow_add]; ring
    have hFzero : ∀ᶠ s in 𝓝[>] (0 : ℝ), F s = 0 := by
      filter_upwards [hzero, self_mem_nhdsWithin] with s hs hpos
      rw [hF] at hs
      exact (mul_eq_zero.1 hs).resolve_left (pow_ne_zero _ (ne_of_gt hpos))
    have hlim : Tendsto F (𝓝[>] 0)
        (𝓝 (∑ d ∈ P.support, P.coeff d * (0 : ℝ) ^ (w d - e) * c ^ d 1)) := by
      refine tendsto_finsetSum _ fun d _ => ?_
      have hpow : Tendsto (fun s : ℝ => s ^ (w d - e)) (𝓝[>] 0) (𝓝 ((0 : ℝ) ^ (w d - e))) :=
        ((continuous_pow _).tendsto 0).mono_left nhdsWithin_le_nhds
      exact (tendsto_const_nhds.mul hpow).mul (hu.pow _)
    have hR : ∑ d ∈ P.support, P.coeff d * (0 : ℝ) ^ (w d - e) * c ^ d 1 =
        P.coeff d₀ * c ^ d₀ 1 := by
      rw [Finset.sum_eq_single_of_mem d₀ hd₀]
      · simp only [e, Nat.sub_self, pow_zero, mul_one]
      · intro d hd hne
        have hlt : e < w d := lt_of_le_of_ne (hmin d hd) fun h => hne (hinj d hd d₀ hd₀ h.symm)
        rw [zero_pow (by omega)]
        ring
    have h0 : Tendsto F (𝓝[>] 0) (𝓝 0) := tendsto_const_nhds.congr' (hFzero.mono fun s hs => hs.symm)
    have := tendsto_nhds_unique hlim h0
    rw [hR] at this
    exact mul_ne_zero ((mem_support_iff.1 hd₀)) (pow_ne_zero _ hc) this
  obtain ⟨d, hd, d', hd', hdd, hlt⟩ := hpair
  have hdeg := sum_fin_two_le_totalDegree hd'
  simp only [hw] at hdd
  -- `j (d'₁ - d₁) = M (d₀ - d'₀)` with both sides positive
  have h1 : j * d 1 < j * d' 1 := Nat.mul_lt_mul_of_pos_left hlt hj
  have h2 : M * d' 0 < M * d 0 := by omega
  have h3 : d' 0 < d 0 := lt_of_mul_lt_mul_left h2 (Nat.zero_le M)
  have h4 : M * (d' 0 + 1) ≤ M * d 0 := Nat.mul_le_mul_left _ h3
  have h5 : j * d' 1 ≤ j * P.totalDegree := Nat.mul_le_mul_left _ (by omega)
  nlinarith

/-! ### From a bound along `s ↦ s^M` to the bound in `σ` -/

theorem final_step (g : ℝ → ℝ) (M n D : ℕ) (hM : 0 < M) (hD : 0 < D) (hn : M ≤ n * D)
    (K s₁ : ℝ) (hs₁ : 0 < s₁) (hK : ∀ s ∈ Ioo 0 s₁, g (s ^ M) ≤ K * s ^ n) :
    ∃ L σ₁ : ℝ, 0 < σ₁ ∧ ∀ σ ∈ Ioo 0 σ₁, g σ ≤ L * σ ^ ((1 : ℝ) / D) := by
  refine ⟨max K 0, min (s₁ ^ M) 1, lt_min (pow_pos hs₁ M) one_pos, fun σ hσ => ?_⟩
  have hσ0 : 0 < σ := hσ.1
  have hσ1 : σ < 1 := hσ.2.trans_le (min_le_right _ _)
  have hσs : σ < s₁ ^ M := hσ.2.trans_le (min_le_left _ _)
  have hM0 : M ≠ 0 := hM.ne'
  set s := σ ^ ((M : ℝ)⁻¹)
  have hs0 : 0 < s := Real.rpow_pos_of_pos hσ0 _
  have hsM : s ^ M = σ := Real.rpow_inv_natCast_pow hσ0.le hM0
  have hss : s < s₁ := by
    have := Real.rpow_lt_rpow hσ0.le hσs (by positivity : (0 : ℝ) < (M : ℝ)⁻¹)
    rwa [Real.pow_rpow_inv_natCast hs₁.le hM0] at this
  have h1 := hK s ⟨hs0, hss⟩
  rw [hsM] at h1
  have hsn : s ^ n = σ ^ ((M : ℝ)⁻¹ * n) := (Real.rpow_mul_natCast hσ0.le _ _).symm
  have hexp : (1 : ℝ) / D ≤ (M : ℝ)⁻¹ * n := by
    have hD' : (0 : ℝ) < D := by exact_mod_cast hD
    have hM' : (0 : ℝ) < M := by exact_mod_cast hM
    have hn' : (M : ℝ) ≤ n * D := by exact_mod_cast hn
    rw [div_le_iff₀ hD', inv_mul_eq_div, div_mul_eq_mul_div, le_div_iff₀ hM']
    linarith
  have h2 : σ ^ ((M : ℝ)⁻¹ * n) ≤ σ ^ ((1 : ℝ) / D) :=
    Real.rpow_le_rpow_of_exponent_ge hσ0 hσ1.le hexp
  have h3 : 0 ≤ σ ^ ((M : ℝ)⁻¹ * n) := Real.rpow_nonneg hσ0.le _
  calc g σ ≤ K * s ^ n := h1
    _ ≤ max K 0 * s ^ n := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ = max K 0 * σ ^ ((M : ℝ)⁻¹ * n) := by rw [hsn]
    _ ≤ max K 0 * σ ^ ((1 : ℝ) / D) := mul_le_mul_of_nonneg_left h2 (le_max_right _ _)

/-! ### `g` is semialgebraic -/

theorem isSAFun₁₁_of_graph (φ : Fml (Fin 2)) (g : ℝ → ℝ) (σ₀ : ℝ)
    (hgraph : ∀ σ ∈ Ioo 0 σ₀, ∀ y, φ.Holds ![σ, y] ↔ y = g σ) : IsSAFun₁₁ (Ioo 0 σ₀) g := by
  have hD : IsSA {v : Unit → ℝ | v () ∈ Ioo (0 : ℝ) σ₀} := by
    have := (isSA_pos (X () : MvPolynomial Unit ℝ)).inter
      (isSA_pos (C σ₀ - X () : MvPolynomial Unit ℝ))
    convert this using 1
    ext v
    simp [sub_pos]
  unfold IsSAFun₁₁ IsSAFunOn₁ IsSAFunOn
  refine ⟨hD, ?_⟩
  have h1 : IsSA {v : Unit ⊕ Unit → ℝ |
      v ∘ Sum.inl ∈ {v : Unit → ℝ | v () ∈ Ioo (0 : ℝ) σ₀}} := hD.preimage_comp _
  have h2 : IsSA {v : Unit ⊕ Unit → ℝ |
      v ∘ ![Sum.inl (), Sum.inr ()] ∈ {w : Fin 2 → ℝ | φ.Holds w}} :=
    IsSA.preimage_comp ⟨φ, fun _ => Iff.rfl⟩ _
  convert h1.inter h2 using 1
  ext v
  have hv : v ∘ ![Sum.inl (), Sum.inr ()] = ![v (Sum.inl ()), v (Sum.inr ())] := by
    funext i; fin_cases i <;> rfl
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, hv, Function.comp_apply]
  constructor
  · rintro ⟨hσ, hg⟩
    exact ⟨hσ, (hgraph _ hσ _).2 (congrFun hg ()).symm⟩
  · rintro ⟨hσ, hφ⟩
    refine ⟨hσ, ?_⟩
    funext x
    exact ((hgraph _ hσ _).1 hφ).symm

/-! ### The Puiseux expansion and the leading exponent -/

theorem exists_Ioo_of_eventually {p : ℝ → Prop} (hp : ∀ᶠ s in 𝓝[>] (0 : ℝ), p s) :
    ∃ s₁ > 0, ∀ s ∈ Ioo 0 s₁, p s := by
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hp
  exact ⟨u, hu, fun s hs => hsub hs⟩

theorem puiseux_bound (g : ℝ → ℝ) (σ₀ : ℝ) (hσ₀ : 0 < σ₀) (P : MvPolynomial (Fin 2) ℝ)
    (hP : P ≠ 0) (hPz : ∀ σ ∈ Ioo 0 σ₀, eval ![σ, g σ] P = 0)
    (hlim : Tendsto g (𝓝[>] 0) (𝓝 0)) (M : ℕ) (j₀ : ℤ) (cs : ℕ → ℝ) (hM : 0 < M)
    (hJ : ∀ J : ℕ, (fun s : ℝ => g (s ^ M) - ∑ i ∈ Finset.range J, cs i * s ^ (j₀ + i)) =O[𝓝[>] 0]
      (fun s : ℝ => s ^ (j₀ + J)))
    (D : ℕ) (hD : 0 < D) (hPD : P.totalDegree ≤ D) :
    ∃ n : ℕ, ∃ K s₁ : ℝ, 0 < s₁ ∧ M ≤ n * D ∧ ∀ s ∈ Ioo 0 s₁, g (s ^ M) ≤ K * s ^ n := by
  classical
  have hpowM : Tendsto (fun s : ℝ => s ^ M) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := ((continuous_pow M).tendsto (0 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa [zero_pow hM.ne'] using this
    · filter_upwards [self_mem_nhdsWithin] with s hs using pow_pos (show (0 : ℝ) < s from hs) M
  have hgM : Tendsto (fun s => g (s ^ M)) (𝓝[>] 0) (𝓝 0) := hlim.comp hpowM
  by_cases hflat : ∀ i, cs i = 0
  · -- the expansion vanishes identically: `g(s^M) = O(s^J)` for every `J`
    obtain ⟨K, hK, hKb⟩ := (hJ (Int.toNat (M - j₀))).exists_pos
    rw [Asymptotics.isBigOWith_iff] at hKb
    obtain ⟨s₁, hs₁, hb⟩ := exists_Ioo_of_eventually hKb
    refine ⟨M, K, min s₁ 1, lt_min hs₁ one_pos, Nat.le_mul_of_pos_right M hD, fun s hs => ?_⟩
    have hs0 : 0 < s := hs.1
    have hs1 : s < 1 := hs.2.trans_le (min_le_right _ _)
    have h0 := hb s ⟨hs0, hs.2.trans_le (min_le_left _ _)⟩
    simp only [hflat, zero_mul, Finset.sum_const_zero, sub_zero, Real.norm_eq_abs] at h0
    have hexp : (M : ℤ) ≤ j₀ + ((Int.toNat (M - j₀) : ℕ) : ℤ) := by omega
    have h1 : |s ^ (j₀ + ((Int.toNat (M - j₀) : ℕ) : ℤ))| ≤ s ^ M := by
      rw [abs_of_pos (zpow_pos hs0 _)]
      calc s ^ (j₀ + ((Int.toNat (M - j₀) : ℕ) : ℤ)) ≤ s ^ (M : ℤ) :=
            zpow_le_zpow_right_of_le_one₀ hs0 hs1.le hexp
        _ = s ^ M := zpow_natCast s M
    calc g (s ^ M) ≤ |g (s ^ M)| := le_abs_self _
      _ ≤ K * |s ^ (j₀ + ((Int.toNat (M - j₀) : ℕ) : ℤ))| := h0
      _ ≤ K * s ^ M := mul_le_mul_of_nonneg_left h1 hK.le
  · push Not at hflat
    set i₀ := Nat.find hflat
    have hci₀ : cs i₀ ≠ 0 := Nat.find_spec hflat
    have hlt : ∀ i < i₀, cs i = 0 := fun i hi => by
      by_contra h
      exact Nat.find_min hflat hi h
    set c := cs i₀
    set k : ℤ := j₀ + i₀
    have hsum : ∀ s : ℝ, ∑ i ∈ Finset.range (i₀ + 1), cs i * s ^ (j₀ + i) = c * s ^ k := by
      intro s
      rw [Finset.sum_range_succ, Finset.sum_eq_zero fun i hi => by
        rw [hlt i (Finset.mem_range.1 hi), zero_mul], zero_add]
    obtain ⟨K, hK, hKb⟩ := (hJ (i₀ + 1)).exists_pos
    rw [Asymptotics.isBigOWith_iff] at hKb
    simp only [hsum, Real.norm_eq_abs] at hKb
    have hk1 : j₀ + ((i₀ + 1 : ℕ) : ℤ) = k + 1 := by push_cast; ring
    rw [hk1] at hKb
    -- the normalized function `u(s) = g(s^M) / s^k` tends to the leading coefficient `c`
    set u : ℝ → ℝ := fun s => g (s ^ M) / s ^ k with hu_def
    have hu_bound : ∀ᶠ s in 𝓝[>] (0 : ℝ), |u s - c| ≤ K * s := by
      filter_upwards [hKb, self_mem_nhdsWithin] with s hs hpos
      have hpos' : (0 : ℝ) < s := hpos
      have hsk : 0 < s ^ k := zpow_pos hpos' k
      rw [abs_of_pos (zpow_pos hpos' _), zpow_add_one₀ hpos'.ne'] at hs
      have : u s - c = (g (s ^ M) - c * s ^ k) / s ^ k := by
        simp only [hu_def]
        field_simp
      rw [this, abs_div, abs_of_pos hsk, div_le_iff₀ hsk]
      linarith
    have hu : Tendsto u (𝓝[>] 0) (𝓝 c) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero' (g := fun s => K * s) (Eventually.of_forall fun s => norm_nonneg _)
        (hu_bound.mono fun s hs => by rwa [Real.norm_eq_abs]) ?_
      have : Tendsto (fun s : ℝ => K * s) (𝓝 0) (𝓝 (K * 0)) :=
        tendsto_const_nhds.mul tendsto_id
      simpa using this.mono_left nhdsWithin_le_nhds
    have hcabs : 0 < |c| := abs_pos.2 hci₀
    -- the leading exponent is positive since `g → 0`
    have hkpos : 0 < k := by
      by_contra hk
      push Not at hk
      have e1 : ∀ᶠ s in 𝓝[>] (0 : ℝ), |c| / 2 < |u s| :=
        ((continuous_abs.tendsto c).comp hu).eventually (lt_mem_nhds (by linarith))
      have e2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), |g (s ^ M)| < |c| / 2 := by
        have := (continuous_abs.tendsto 0).comp hgM
        rw [abs_zero] at this
        exact this.eventually (gt_mem_nhds (by linarith))
      have e3 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < 1 :=
        nhdsWithin_le_nhds (gt_mem_nhds one_pos)
      obtain ⟨s, h1, h2, h3, h4⟩ := (e1.and (e2.and (e3.and self_mem_nhdsWithin))).exists
      have hs0 : (0 : ℝ) < s := h4
      have hsk : 1 ≤ s ^ k := one_le_zpow_of_nonpos₀ hs0 h3.le hk
      have hgu : g (s ^ M) = u s * s ^ k := by
        simp only [hu_def]
        field_simp
      rw [hgu, abs_mul, abs_of_pos (zpow_pos hs0 k)] at h2
      nlinarith [abs_nonneg (u s)]
    set j := k.toNat
    have hjk : (j : ℤ) = k := Int.toNat_of_nonneg hkpos.le
    have hj : 0 < j := by omega
    have hgu : ∀ s : ℝ, 0 < s → g (s ^ M) = s ^ j * u s := by
      intro s hs
      simp only [hu_def]
      rw [← hjk, zpow_natCast]
      field_simp
    have hzero : ∀ᶠ s in 𝓝[>] (0 : ℝ), eval ![s ^ M, s ^ j * u s] P = 0 := by
      have hlt' : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ^ M < σ₀ :=
        (hpowM.mono_right nhdsWithin_le_nhds).eventually (gt_mem_nhds hσ₀)
      filter_upwards [hlt', self_mem_nhdsWithin] with s hs hpos
      rw [← hgu s hpos]
      exact hPz _ ⟨pow_pos hpos M, hs⟩
    have hMj := newton P hP M j hM hj u c hci₀ hu hzero
    have hub : ∀ᶠ s in 𝓝[>] (0 : ℝ), u s < |c| + 1 :=
      hu.eventually (gt_mem_nhds (by linarith [le_abs_self c]))
    obtain ⟨s₁, hs₁, hb⟩ := exists_Ioo_of_eventually hub
    refine ⟨j, |c| + 1, s₁, hs₁, hMj.trans (Nat.mul_le_mul_left _ hPD), fun s hs => ?_⟩
    rw [hgu s hs.1, mul_comm (|c| + 1)]
    exact mul_le_mul_of_nonneg_left (hb s hs).le (pow_nonneg hs.1.le _)

end ExpAux

/-- **Lemma 6.3 (d), core.** -/
theorem exponent_bound (hS : SAFacts) (hQE : EffectiveQE) :
    ∃ C : ℕ, ∀ (φ : Fml (Fin 2)) (g : ℝ → ℝ) (σ₀ : ℝ), 0 < σ₀ →
      (∀ σ ∈ Ioo 0 σ₀, ∀ y, φ.Holds ![σ, y] ↔ y = g σ) →
      (∀ σ ∈ Ioo 0 σ₀, 0 ≤ g σ) → Tendsto g (𝓝[>] 0) (𝓝 0) →
      ∃ L σ₁ : ℝ, 0 < σ₁ ∧ ∀ σ ∈ Ioo 0 σ₁,
        g σ ≤ L * σ ^ ((1 : ℝ) / ((qeBound C φ : ℝ) * qeBound C φ)) := by
  obtain ⟨C, hC⟩ := hQE
  refine ⟨C, fun φ g σ₀ hσ₀ hgraph _ hlim => ?_⟩
  -- a quantifier-free equivalent `ψ` with at most `B` atoms of degree at most `B`
  obtain ⟨ψ, hψQF, hψφ, hsize, hdeg⟩ := hC φ
  simp only [Fintype.card_fin] at hsize hdeg
  have hB1 : ψ.size ≤ qeBound C φ := hsize
  have hB2 : ψ.maxDeg ≤ qeBound C φ := hdeg.trans (Nat.pow_le_pow_left (by omega) _)
  have hBpos : 0 < qeBound C φ := by unfold qeBound; positivity
  have hBB : 0 < qeBound C φ * qeBound C φ := Nat.mul_pos hBpos hBpos
  have hgraphψ : ∀ σ ∈ Ioo 0 σ₀, ∀ y, ψ.Holds ![σ, y] ↔ y = g σ :=
    fun σ hσ y => (hψφ _).trans (hgraph σ hσ y)
  -- a nonzero polynomial of degree `≤ B²` vanishing on the graph
  obtain ⟨P, hP0, hPdeg, hPz⟩ := ExpAux.exists_poly ψ hψQF g σ₀ hgraphψ
  have hPD : P.totalDegree ≤ qeBound C φ * qeBound C φ :=
    hPdeg.trans (Nat.mul_le_mul hB1 hB2)
  -- the Puiseux expansion (S7) and its leading exponent
  obtain ⟨M, j₀, cs, hM, hJ⟩ := hS.puiseux g σ₀ hσ₀ (ExpAux.isSAFun₁₁_of_graph φ g σ₀ hgraph)
  obtain ⟨n, K, s₁, hs₁, hn, hK⟩ :=
    ExpAux.puiseux_bound g σ₀ hσ₀ P hP0 hPz hlim M j₀ cs hM hJ _ hBB hPD
  obtain ⟨L, σ₁, hσ₁, hL⟩ := ExpAux.final_step g M n _ hM hBB hn K s₁ hs₁ hK
  refine ⟨L, σ₁, hσ₁, fun σ hσ => ?_⟩
  have := hL σ hσ
  push_cast at this
  exact this

end ClassSep
