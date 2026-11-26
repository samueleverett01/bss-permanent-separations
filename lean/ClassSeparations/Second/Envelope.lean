import Mathlib

/-!
# The envelope (§6.3, Lemma 6.4), in abstract form

Fix `x`.  The atoms form a compact set `At ⊆ ℝ^κ × [0, 1]` of pairs `(ω, s)` with `ω` in a
closed ball `B̄`.  For `c ∈ ℝ^κ`, `e(c)` is the maximum over weights `λ₁, …, λ_r ≥ 0` with
`∑ λᵢ = 1` (`r = κ + 3`) and atoms `(ωᵢ, sᵢ)` of
`J = ∑ λᵢ sᵢ^N - a ∑ λᵢ |ωᵢ - ω̄|² - 2a |c - ω̄|²`, `ω̄ = ∑ λᵢ ωᵢ` (Euclidean norms written as
sums of squares).

**Lemma 6.4.**
(a) `e` is continuously differentiable on `ℝ^κ` with `∇e(c) = 4a(m₁* - c)`, where `m₁*` is the
mean `ω̄` common to all maximizers; on `B̄` it is Lipschitz with constant `8 a r₀` (`r₀` the radius).
(b) `e(c) ≥ s^N` for every atom `(c, s)`.
(c) If `s^N ≤ a|ω - φ|²` for all atoms, then `e(φ) = 0` when `(φ, 0)` is an atom, and in any
case `e(φ) ≤ 0`.

Here the Lipschitz constant is stated for the Euclidean distance of `ℝ^κ` computed as the
square root of the sum of squares.
-/

noncomputable section

open Set Filter Topology

namespace ClassSep

variable {κ : Type} [Fintype κ]

/-- Squared Euclidean distance on `ℝ^κ`. -/
def sqDist (u v : κ → ℝ) : ℝ := ∑ k, (u k - v k) ^ 2

/-- The objective `J` of (9) for weights `λ`, atoms `(ω i, s i)` and center `c`. -/
def envJ (a : ℝ) (N : ℕ) {r : ℕ} (lam : Fin r → ℝ) (ω : Fin r → κ → ℝ) (s : Fin r → ℝ)
    (c : κ → ℝ) : ℝ :=
  let ωbar : κ → ℝ := fun k => ∑ i, lam i * ω i k
  ∑ i, lam i * s i ^ N - a * ∑ i, lam i * sqDist (ω i) ωbar - 2 * a * sqDist c ωbar

/-- The admissible choices: weights in the standard simplex and atoms in `At`. -/
def envAdm (At : Set ((κ → ℝ) × ℝ)) (r : ℕ) : Set ((Fin r → ℝ) × (Fin r → κ → ℝ) × (Fin r → ℝ)) :=
  {p | (∀ i, 0 ≤ p.1 i) ∧ ∑ i, p.1 i = 1 ∧ ∀ i, (p.2.1 i, p.2.2 i) ∈ At}

/-- The envelope `e(c)`: the supremum (a maximum, by compactness) of `J`. -/
def envelope (At : Set ((κ → ℝ) × ℝ)) (a : ℝ) (N : ℕ) (c : κ → ℝ) : ℝ :=
  sSup ((fun p => envJ a N p.1 p.2.1 p.2.2 c) '' envAdm At (Fintype.card κ + 3))

namespace EnvAux

/-! ### Algebraic identities -/

/-- The mean `ω̄ = ∑ λᵢ ωᵢ`. -/
def mean {r : ℕ} (lam : Fin r → ℝ) (ω : Fin r → κ → ℝ) : κ → ℝ := fun k => ∑ i, lam i * ω i k

theorem envJ_eq (a : ℝ) (N : ℕ) {r : ℕ} (lam : Fin r → ℝ) (ω : Fin r → κ → ℝ) (s : Fin r → ℝ)
    (c : κ → ℝ) : envJ a N lam ω s c = ∑ i, lam i * s i ^ N -
      a * ∑ i, lam i * sqDist (ω i) (mean lam ω) - 2 * a * sqDist c (mean lam ω) := rfl

theorem sqDist_comm (u v : κ → ℝ) : sqDist u v = sqDist v u :=
  Finset.sum_congr rfl fun _ _ => by ring

theorem sqDist_nonneg (u v : κ → ℝ) : 0 ≤ sqDist u v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem sqDist_self (u : κ → ℝ) : sqDist u u = 0 := by simp [sqDist]

theorem sqDist_zero (u : κ → ℝ) : sqDist u 0 = ∑ k, u k ^ 2 := by simp [sqDist]

theorem wsum_sq {r : ℕ} (lam t : Fin r → ℝ) (x : ℝ) :
    ∑ i, lam i * (t i - x) ^ 2 =
      ∑ i, lam i * t i ^ 2 - 2 * x * ∑ i, lam i * t i + x ^ 2 * ∑ i, lam i := by
  have : ∀ i, lam i * (t i - x) ^ 2 = lam i * t i ^ 2 - 2 * x * (lam i * t i) + x ^ 2 * lam i :=
    fun i => by ring
  simp_rw [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- Variance decomposition: `∑ λᵢ |ωᵢ - φ|² = ∑ λᵢ |ωᵢ - ω̄|² + |ω̄ - φ|²`. -/
theorem variance_decomp {r : ℕ} (lam : Fin r → ℝ) (hl : ∑ i, lam i = 1) (ω : Fin r → κ → ℝ)
    (φ : κ → ℝ) : ∑ i, lam i * sqDist (ω i) φ =
      ∑ i, lam i * sqDist (ω i) (mean lam ω) + sqDist (mean lam ω) φ := by
  simp only [sqDist, Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun i k => lam i * (ω i k - mean lam ω k) ^ 2),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : ∀ x : ℝ, ∑ i, lam i * (ω i k - x) ^ 2 =
      ∑ i, lam i * ω i k ^ 2 - 2 * x * ∑ i, lam i * ω i k + x ^ 2 * ∑ i, lam i :=
    fun x => wsum_sq lam (fun i => ω i k) x
  rw [h1, h1, hl]
  simp only [mean]
  ring

/-- `J` after moving the center: `J(c + h) = J(c) + 4a⟨ω̄ - c, h⟩ - 2a|h|²`. -/
theorem envJ_add (a : ℝ) (N : ℕ) {r : ℕ} (lam : Fin r → ℝ) (ω : Fin r → κ → ℝ)
    (s : Fin r → ℝ) (c h : κ → ℝ) :
    envJ a N lam ω s (c + h) = envJ a N lam ω s c +
      4 * a * ∑ k, (mean lam ω k - c k) * h k - 2 * a * ∑ k, h k ^ 2 := by
  have : sqDist (c + h) (mean lam ω) = sqDist c (mean lam ω) -
      2 * ∑ k, (mean lam ω k - c k) * h k + ∑ k, h k ^ 2 := by
    simp only [sqDist, Pi.add_apply, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [envJ_eq, envJ_eq, this]
  ring

/-- The value of `j(c; m)` at a moment vector `m = (m₀, m₂, m₁)`. -/
def jfun (a : ℝ) (c : κ → ℝ) (m : ℝ × ℝ × (κ → ℝ)) : ℝ :=
  m.1 - a * m.2.1 + ∑ k, (-a * m.2.2 k ^ 2 + 4 * a * c k * m.2.2 k - 2 * a * c k ^ 2)

/-- The moment vector `(∑ λᵢ sᵢ^N, ∑ λᵢ |ωᵢ|², ω̄)`. -/
def mom (N : ℕ) {r : ℕ} (p : (Fin r → ℝ) × (Fin r → κ → ℝ) × (Fin r → ℝ)) :
    ℝ × ℝ × (κ → ℝ) :=
  (∑ i, p.1 i * p.2.2 i ^ N, ∑ i, p.1 i * ∑ k, p.2.1 i k ^ 2, mean p.1 p.2.1)

/-- The moment vector of a single atom. -/
def mu (N : ℕ) (x : (κ → ℝ) × ℝ) : ℝ × ℝ × (κ → ℝ) := (x.2 ^ N, ∑ k, x.1 k ^ 2, x.1)

theorem mom_eq_sum (N : ℕ) {r : ℕ} (p : (Fin r → ℝ) × (Fin r → κ → ℝ) × (Fin r → ℝ)) :
    mom N p = ∑ i, p.1 i • mu N (p.2.1 i, p.2.2 i) := by
  ext
  · simp [mom, mu, Prod.fst_sum]
  · simp [mom, mu, Prod.fst_sum, Prod.snd_sum]
  · simp [mom, mu, mean, Prod.snd_sum, Finset.sum_apply]

theorem envJ_moment (a : ℝ) (N : ℕ) {r : ℕ} (p : (Fin r → ℝ) × (Fin r → κ → ℝ) × (Fin r → ℝ))
    (hl : ∑ i, p.1 i = 1) (c : κ → ℝ) : envJ a N p.1 p.2.1 p.2.2 c = jfun a c (mom N p) := by
  have hv := variance_decomp p.1 hl p.2.1 0
  simp only [sqDist_zero] at hv
  have hs : ∑ k, (-a * mean p.1 p.2.1 k ^ 2 + 4 * a * c k * mean p.1 p.2.1 k - 2 * a * c k ^ 2) =
      a * ∑ k, mean p.1 p.2.1 k ^ 2 - 2 * a * sqDist c (mean p.1 p.2.1) := by
    simp only [sqDist, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [envJ_eq, jfun, mom]
  simp only
  rw [hs, hv]
  ring

theorem jfun_mid (a : ℝ) (c : κ → ℝ) (m m' : ℝ × ℝ × (κ → ℝ)) :
    jfun a c ((1 / 2 : ℝ) • m + (1 / 2 : ℝ) • m') =
      (jfun a c m + jfun a c m') / 2 + a / 4 * sqDist m.2.2 m'.2.2 := by
  have key : ∀ k, -a * ((1 / 2 : ℝ) * m.2.2 k + (1 / 2 : ℝ) * m'.2.2 k) ^ 2 +
      4 * a * c k * ((1 / 2 : ℝ) * m.2.2 k + (1 / 2 : ℝ) * m'.2.2 k) - 2 * a * c k ^ 2 =
      (-a * m.2.2 k ^ 2 + 4 * a * c k * m.2.2 k - 2 * a * c k ^ 2) / 2 +
      (-a * m'.2.2 k ^ 2 + 4 * a * c k * m'.2.2 k - 2 * a * c k ^ 2) / 2 +
      a / 4 * (m.2.2 k - m'.2.2 k) ^ 2 := fun k => by ring
  simp only [jfun, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, sqDist]
  rw [Finset.sum_congr rfl fun k _ => key k, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.sum_div, ← Finset.sum_div, ← Finset.mul_sum]
  ring

/-! ### Carathéodory: midpoints of achievable moment vectors are achievable -/

theorem sum_extend_emb {ι : Type*} [Fintype ι] {n : ℕ} (e : ι ↪ Fin n) {M : Type*}
    [AddCommMonoid M] (F : Fin n → M) (hF : ∀ j, (¬ ∃ i, e i = j) → F j = 0) :
    ∑ j, F j = ∑ i, F (e i) := by
  classical
  rw [← Finset.sum_map Finset.univ e F]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun j _ hj => hF j ?_
  rintro ⟨i, rfl⟩
  exact hj (Finset.mem_map_of_mem _ (Finset.mem_univ i))

theorem mom_mem_convexHull {At : Set ((κ → ℝ) × ℝ)} (N : ℕ) {r : ℕ}
    {p : (Fin r → ℝ) × (Fin r → κ → ℝ) × (Fin r → ℝ)} (hp : p ∈ envAdm At r) :
    mom N p ∈ convexHull ℝ (mu N '' At) := by
  rw [mom_eq_sum]
  exact (convex_convexHull ℝ _).sum_mem (fun i _ => hp.1 i) hp.2.1
    (fun i _ => subset_convexHull ℝ _ ⟨_, hp.2.2 i, rfl⟩)

theorem exists_adm_of_mem_convexHull {At : Set ((κ → ℝ) × ℝ)} (hne : At.Nonempty) (N : ℕ)
    {m : ℝ × ℝ × (κ → ℝ)} (hm : m ∈ convexHull ℝ (mu N '' At)) :
    ∃ p ∈ envAdm At (Fintype.card κ + 3), mom N p = m := by
  classical
  obtain ⟨ι, _, z, w, hz, hai, hw, hw1, hwz⟩ := eq_pos_convex_span_of_mem_convexHull hm
  have hcard : Fintype.card ι ≤ Fintype.card κ + 3 := by
    have h1 := hai.card_le_finrank_succ
    have h2 : Module.finrank ℝ (vectorSpan ℝ (Set.range z)) ≤
        Module.finrank ℝ (ℝ × ℝ × (κ → ℝ)) := Submodule.finrank_le _
    have h3 : Module.finrank ℝ (ℝ × ℝ × (κ → ℝ)) = Fintype.card κ + 2 := by
      rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_self,
        Module.finrank_fintype_fun_eq_card]
      ring
    omega
  let e : ι ↪ Fin (Fintype.card κ + 3) :=
    (Fintype.equivFin ι).toEmbedding.trans (Fin.castLEEmb hcard)
  have hx : ∀ i, ∃ x ∈ At, mu N x = z i := fun i => hz ⟨i, rfl⟩
  choose x hxAt hxz using hx
  obtain ⟨x₀, hx₀⟩ := hne
  let lam' : Fin (Fintype.card κ + 3) → ℝ := Function.extend e w 0
  let at' : Fin (Fintype.card κ + 3) → (κ → ℝ) × ℝ := Function.extend e x (fun _ => x₀)
  have hlam_e : ∀ i, lam' (e i) = w i := fun i => e.injective.extend_apply _ _ _
  have hat_e : ∀ i, at' (e i) = x i := fun i => e.injective.extend_apply _ _ _
  have hlam_n : ∀ j, (¬ ∃ i, e i = j) → lam' j = 0 := fun j hj => by
    simp only [lam', Function.extend_apply' _ _ _ hj, Pi.zero_apply]
  have hat_n : ∀ j, (¬ ∃ i, e i = j) → at' j = x₀ := fun j hj => by
    simp only [at', Function.extend_apply' _ _ _ hj]
  refine ⟨(lam', fun j => (at' j).1, fun j => (at' j).2), ⟨fun j => ?_, ?_, fun j => ?_⟩, ?_⟩
  · show 0 ≤ lam' j
    by_cases hj : ∃ i, e i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [hlam_e]
      exact (hw i).le
    · rw [hlam_n j hj]
  · simp only
    rw [sum_extend_emb e lam' (fun j hj => hlam_n j hj)]
    simp only [hlam_e, hw1]
  · by_cases hj : ∃ i, e i = j
    · obtain ⟨i, rfl⟩ := hj
      simp only [hat_e]
      exact hxAt i
    · simp only [hat_n j hj]
      exact hx₀
  · rw [mom_eq_sum]
    simp only [Prod.mk.eta]
    rw [sum_extend_emb e (fun j => lam' j • mu N (at' j)) (fun j hj => by simp [hlam_n j hj])]
    simp only [hlam_e, hat_e, hxz, hwz]

theorem exists_mid {At : Set ((κ → ℝ) × ℝ)} (hne : At.Nonempty) (N : ℕ)
    {p q : (Fin (Fintype.card κ + 3) → ℝ) × (Fin (Fintype.card κ + 3) → κ → ℝ) ×
      (Fin (Fintype.card κ + 3) → ℝ)}
    (hp : p ∈ envAdm At (Fintype.card κ + 3)) (hq : q ∈ envAdm At (Fintype.card κ + 3)) :
    ∃ p'' ∈ envAdm At (Fintype.card κ + 3),
      mom N p'' = (1 / 2 : ℝ) • mom N p + (1 / 2 : ℝ) • mom N q :=
  exists_adm_of_mem_convexHull hne N <| convex_convexHull ℝ _ (mom_mem_convexHull N hp)
    (mom_mem_convexHull N hq) (by norm_num) (by norm_num) (by norm_num)

/-- `J` at a configuration realizing the midpoint of the moments of `p` and `q`. -/
theorem envJ_mid (a : ℝ) (N : ℕ) {r : ℕ} {At : Set ((κ → ℝ) × ℝ)}
    {p q p'' : (Fin r → ℝ) × (Fin r → κ → ℝ) × (Fin r → ℝ)}
    (hp : p ∈ envAdm At r) (hq : q ∈ envAdm At r) (hp'' : p'' ∈ envAdm At r)
    (hmid : mom N p'' = (1 / 2 : ℝ) • mom N p + (1 / 2 : ℝ) • mom N q) (c : κ → ℝ) :
    envJ a N p''.1 p''.2.1 p''.2.2 c = (envJ a N p.1 p.2.1 p.2.2 c + envJ a N q.1 q.2.1 q.2.2 c) / 2
      + a / 4 * sqDist (mean p.1 p.2.1) (mean q.1 q.2.1) := by
  rw [envJ_moment a N p'' hp''.2.1, envJ_moment a N p hp.2.1, envJ_moment a N q hq.2.1, hmid,
    jfun_mid]
  rfl

/-! ### Compactness and existence of maximizers -/

omit [Fintype κ] in
theorem isCompact_envAdm {At : Set ((κ → ℝ) × ℝ)} (hAt : IsCompact At) (r : ℕ) :
    IsCompact (envAdm At r) := by
  have hK : IsCompact ((Set.pi univ fun _ : Fin r => Icc (0 : ℝ) 1) ×ˢ
      ((Set.pi univ fun _ : Fin r => Prod.fst '' At) ×ˢ
        (Set.pi univ fun _ : Fin r => Prod.snd '' At))) :=
    (isCompact_univ_pi fun _ => isCompact_Icc).prod
      ((isCompact_univ_pi fun _ => hAt.image continuous_fst).prod
        (isCompact_univ_pi fun _ => hAt.image continuous_snd))
  refine hK.of_isClosed_subset ?_ ?_
  · have h1 : IsClosed {p : (Fin r → ℝ) × (Fin r → κ → ℝ) × (Fin r → ℝ) | ∀ i, 0 ≤ p.1 i} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun i => isClosed_le continuous_const (by fun_prop)
    have h2 : IsClosed {p : (Fin r → ℝ) × (Fin r → κ → ℝ) × (Fin r → ℝ) | ∑ i, p.1 i = 1} :=
      isClosed_eq (by fun_prop) continuous_const
    have h3 : IsClosed {p : (Fin r → ℝ) × (Fin r → κ → ℝ) × (Fin r → ℝ) |
        ∀ i, (p.2.1 i, p.2.2 i) ∈ At} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun i => hAt.isClosed.preimage (by fun_prop)
    exact h1.inter (h2.inter h3)
  · rintro p ⟨h0, h1, h2⟩
    refine ⟨fun i _ => ⟨h0 i, ?_⟩, fun i _ => ⟨_, h2 i, rfl⟩, fun i _ => ⟨_, h2 i, rfl⟩⟩
    rw [← h1]
    exact Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)

theorem continuous_envJ (a : ℝ) (N : ℕ) (r : ℕ) (c : κ → ℝ) :
    Continuous fun p : (Fin r → ℝ) × (Fin r → κ → ℝ) × (Fin r → ℝ) =>
      envJ a N p.1 p.2.1 p.2.2 c := by
  simp only [envJ, sqDist]
  fun_prop

theorem sum_uniform {r : ℕ} (hr : 0 < r) (x : ℝ) : ∑ _i : Fin r, (1 / r : ℝ) * x = x := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

omit [Fintype κ] in
/-- A single atom, repeated with uniform weights. -/
theorem single_mem_envAdm {At : Set ((κ → ℝ) × ℝ)} {x : (κ → ℝ) × ℝ} (hx : x ∈ At) {r : ℕ}
    (hr : 0 < r) : ((fun _ => (1 / r : ℝ)), (fun _ => x.1), (fun _ => x.2)) ∈ envAdm At r := by
  refine ⟨fun _ => by positivity, ?_, fun _ => hx⟩
  simpa using sum_uniform hr 1

theorem envJ_single (a : ℝ) (N : ℕ) {r : ℕ} (hr : 0 < r) (ω : κ → ℝ) (s : ℝ) :
    envJ a N (fun _ : Fin r => (1 / r : ℝ)) (fun _ => ω) (fun _ => s) ω = s ^ N := by
  have hm : mean (fun _ : Fin r => (1 / r : ℝ)) (fun _ => ω) = ω := by
    funext k
    exact sum_uniform hr (ω k)
  rw [envJ_eq, hm, sqDist_self, sum_uniform hr]
  simp

omit [Fintype κ] in
theorem envAdm_nonempty {At : Set ((κ → ℝ) × ℝ)} (hne : At.Nonempty) {r : ℕ} (hr : 0 < r) :
    (envAdm At r).Nonempty :=
  ⟨_, single_mem_envAdm hne.some_mem hr⟩

theorem le_envelope {At : Set ((κ → ℝ) × ℝ)} (hAt : IsCompact At) (a : ℝ) (N : ℕ)
    (c : κ → ℝ) {p} (hp : p ∈ envAdm At (Fintype.card κ + 3)) :
    envJ a N p.1 p.2.1 p.2.2 c ≤ envelope At a N c :=
  le_csSup ((isCompact_envAdm hAt _).image (continuous_envJ a N _ c)).bddAbove
    (mem_image_of_mem _ hp)

theorem exists_max {At : Set ((κ → ℝ) × ℝ)} (hAt : IsCompact At) (hne : At.Nonempty) (a : ℝ)
    (N : ℕ) (c : κ → ℝ) : ∃ p ∈ envAdm At (Fintype.card κ + 3),
      envJ a N p.1 p.2.1 p.2.2 c = envelope At a N c := by
  obtain ⟨p, hp, hmax⟩ := (isCompact_envAdm hAt (Fintype.card κ + 3)).exists_isMaxOn
    (envAdm_nonempty hne (by omega)) (continuous_envJ a N _ c).continuousOn
  have hgr : IsGreatest ((fun p => envJ a N p.1 p.2.1 p.2.2 c) ''
      envAdm At (Fintype.card κ + 3)) (envJ a N p.1 p.2.1 p.2.2 c) := by
    refine ⟨mem_image_of_mem _ hp, ?_⟩
    rintro _ ⟨q, hq, rfl⟩
    exact hmax hq
  exact ⟨p, hp, hgr.csSup_eq.symm⟩

/-! ### The analytic estimates -/

/-- Strict concavity in `m₁`: the mean of any configuration is close to the mean of a
maximizer, quantitatively. -/
theorem mean_sq_le {At : Set ((κ → ℝ) × ℝ)} (hAt : IsCompact At) (hne : At.Nonempty) (a : ℝ)
    (N : ℕ) {c : κ → ℝ}
    {p q : (Fin (Fintype.card κ + 3) → ℝ) × (Fin (Fintype.card κ + 3) → κ → ℝ) ×
      (Fin (Fintype.card κ + 3) → ℝ)}
    (hp : p ∈ envAdm At (Fintype.card κ + 3))
    (hpm : envJ a N p.1 p.2.1 p.2.2 c = envelope At a N c)
    (hq : q ∈ envAdm At (Fintype.card κ + 3)) :
    a * sqDist (mean p.1 p.2.1) (mean q.1 q.2.1) ≤
      2 * (envelope At a N c - envJ a N q.1 q.2.1 q.2.2 c) := by
  obtain ⟨p'', hp'', hmid⟩ := exists_mid hne N hp hq
  have h1 := le_envelope hAt a N c hp''
  rw [envJ_mid a N hp hq hp'' hmid c] at h1
  linarith

theorem key_bound {At : Set ((κ → ℝ) × ℝ)} (hAt : IsCompact At) (hne : At.Nonempty) {a : ℝ}
    (ha : 0 < a) (N : ℕ) {c h : κ → ℝ}
    {p q : (Fin (Fintype.card κ + 3) → ℝ) × (Fin (Fintype.card κ + 3) → κ → ℝ) ×
      (Fin (Fintype.card κ + 3) → ℝ)}
    (hp : p ∈ envAdm At (Fintype.card κ + 3))
    (hpm : envJ a N p.1 p.2.1 p.2.2 c = envelope At a N c)
    (hq : q ∈ envAdm At (Fintype.card κ + 3))
    (hqm : envJ a N q.1 q.2.1 q.2.2 (c + h) = envelope At a N (c + h)) :
    ∑ k, (mean q.1 q.2.1 k - mean p.1 p.2.1 k) * h k ≤ 8 * ∑ k, h k ^ 2 ∧
      sqDist (mean q.1 q.2.1) (mean p.1 p.2.1) ≤ 64 * ∑ k, h k ^ 2 := by
  have h1 := mean_sq_le hAt hne a N hp hpm hq
  have h2 := envJ_add a N q.1 q.2.1 q.2.2 c h
  have h3 := envJ_add a N p.1 p.2.1 p.2.2 c h
  have h4 := le_envelope hAt a N (c + h) hp
  have hsplit : ∑ k, (mean q.1 q.2.1 k - c k) * h k - ∑ k, (mean p.1 p.2.1 k - c k) * h k =
      ∑ k, (mean q.1 q.2.1 k - mean p.1 p.2.1 k) * h k := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [sqDist_comm] at h1
  have hCS : (∑ k, (mean q.1 q.2.1 k - mean p.1 p.2.1 k) * h k) ^ 2 ≤
      sqDist (mean q.1 q.2.1) (mean p.1 p.2.1) * ∑ k, h k ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  set I := ∑ k, (mean q.1 q.2.1 k - mean p.1 p.2.1 k) * h k
  set S := ∑ k, h k ^ 2
  set D := sqDist (mean q.1 q.2.1) (mean p.1 p.2.1)
  set Aq := ∑ k, (mean q.1 q.2.1 k - c k) * h k
  set Ap := ∑ k, (mean p.1 p.2.1 k - c k) * h k
  have hDI : a * D ≤ a * (8 * I) := by
    have : a * Aq - a * Ap = a * I := by rw [← hsplit]; ring
    linarith
  have hDI' : D ≤ 8 * I := le_of_mul_le_mul_left hDI ha
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hD0 : 0 ≤ D := sqDist_nonneg _ _
  have hIS : I ≤ 8 * S := by
    by_contra hcon
    push Not at hcon
    have hIpos : 0 < I := by linarith
    nlinarith [mul_pos (sub_pos.2 hcon) hIpos, mul_nonneg (sub_nonneg.2 hDI') hS0]
  exact ⟨hIS, by linarith⟩

theorem deriv_bound {At : Set ((κ → ℝ) × ℝ)} (hAt : IsCompact At) (hne : At.Nonempty) {a : ℝ}
    (ha : 0 < a) (N : ℕ) {c : κ → ℝ}
    {p : (Fin (Fintype.card κ + 3) → ℝ) × (Fin (Fintype.card κ + 3) → κ → ℝ) ×
      (Fin (Fintype.card κ + 3) → ℝ)}
    (hp : p ∈ envAdm At (Fintype.card κ + 3))
    (hpm : envJ a N p.1 p.2.1 p.2.2 c = envelope At a N c) (h : κ → ℝ) :
    |envelope At a N (c + h) - envelope At a N c - 4 * a * ∑ k, (mean p.1 p.2.1 k - c k) * h k|
      ≤ 32 * a * ∑ k, h k ^ 2 := by
  obtain ⟨q, hq, hqm⟩ := exists_max hAt hne a N (c + h)
  have hb := (key_bound hAt hne ha N hp hpm hq hqm).1
  have h2 := envJ_add a N q.1 q.2.1 q.2.2 c h
  have h3 := envJ_add a N p.1 p.2.1 p.2.2 c h
  have h4 := le_envelope hAt a N (c + h) hp
  have h5 := le_envelope hAt a N c hq
  have hsplit : ∑ k, (mean q.1 q.2.1 k - c k) * h k - ∑ k, (mean p.1 p.2.1 k - c k) * h k =
      ∑ k, (mean q.1 q.2.1 k - mean p.1 p.2.1 k) * h k := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  set I := ∑ k, (mean q.1 q.2.1 k - mean p.1 p.2.1 k) * h k
  set S := ∑ k, h k ^ 2
  set Aq := ∑ k, (mean q.1 q.2.1 k - c k) * h k
  set Ap := ∑ k, (mean p.1 p.2.1 k - c k) * h k
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have e1 : a * Aq - a * Ap = a * I := by rw [← hsplit]; ring
  have e2 : a * I ≤ a * (8 * S) := mul_le_mul_of_nonneg_left hb ha.le
  have e3 : 0 ≤ a * S := mul_nonneg ha.le hS0
  rw [abs_le]
  constructor <;> linarith

/-- The candidate derivative `v ↦ 4a⟨m - c, v⟩`. -/
def gradCLM (a : ℝ) (m c : κ → ℝ) : (κ → ℝ) →L[ℝ] ℝ :=
  ∑ k, (4 * a * (m k - c k)) • ContinuousLinearMap.proj k

theorem gradCLM_apply (a : ℝ) (m c v : κ → ℝ) :
    gradCLM a m c v = 4 * a * ∑ k, (m k - c k) * v k := by
  simp [gradCLM, Finset.mul_sum, mul_assoc]

theorem hasFDerivAt_envelope {At : Set ((κ → ℝ) × ℝ)} (hAt : IsCompact At) (hne : At.Nonempty)
    {a : ℝ} (ha : 0 < a) (N : ℕ) {c : κ → ℝ}
    {p : (Fin (Fintype.card κ + 3) → ℝ) × (Fin (Fintype.card κ + 3) → κ → ℝ) ×
      (Fin (Fintype.card κ + 3) → ℝ)}
    (hp : p ∈ envAdm At (Fintype.card κ + 3))
    (hpm : envJ a N p.1 p.2.1 p.2.2 c = envelope At a N c) :
    HasFDerivAt (envelope At a N) (gradCLM a (mean p.1 p.2.1) c) c := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine Asymptotics.IsBigO.trans_isLittleO (g := fun h : κ → ℝ => ‖h‖ ^ 2) ?_
    (Asymptotics.isLittleO_norm_pow_id one_lt_two)
  refine Asymptotics.IsBigO.of_bound (32 * a * Fintype.card κ) (Eventually.of_forall fun h => ?_)
  rw [gradCLM_apply, Real.norm_eq_abs, norm_pow, norm_norm]
  refine (deriv_bound hAt hne ha N hp hpm h).trans ?_
  have hS : ∑ k, h k ^ 2 ≤ Fintype.card κ * ‖h‖ ^ 2 := by
    calc ∑ k, h k ^ 2 ≤ ∑ _k : κ, ‖h‖ ^ 2 := Finset.sum_le_sum fun k _ => by
          rw [← sq_abs, ← Real.norm_eq_abs]
          exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm h k) 2
      _ = Fintype.card κ * ‖h‖ ^ 2 := by simp
  have := mul_le_mul_of_nonneg_left hS (by positivity : (0 : ℝ) ≤ 32 * a)
  linarith

/-- The mean of a configuration lies in the ball containing the atoms. -/
theorem mean_mem_ball {At : Set ((κ → ℝ) × ℝ)} {w₀ : κ → ℝ} {r₀ : ℝ}
    (hball : ∀ p ∈ At, sqDist p.1 w₀ ≤ r₀ ^ 2) {r : ℕ}
    {p : (Fin r → ℝ) × (Fin r → κ → ℝ) × (Fin r → ℝ)} (hp : p ∈ envAdm At r) :
    sqDist (mean p.1 p.2.1) w₀ ≤ r₀ ^ 2 := by
  have hv := variance_decomp p.1 hp.2.1 p.2.1 w₀
  have h1 : ∑ i, p.1 i * sqDist (p.2.1 i) w₀ ≤ ∑ i, p.1 i * r₀ ^ 2 :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hball (p.2.1 i, p.2.2 i) (hp.2.2 i)) (hp.1 i)
  have h2 : ∑ i, p.1 i * r₀ ^ 2 = r₀ ^ 2 := by rw [← Finset.sum_mul, hp.2.1, one_mul]
  have h3 : 0 ≤ ∑ i, p.1 i * sqDist (p.2.1 i) (mean p.1 p.2.1) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hp.1 i) (sqDist_nonneg _ _)
  linarith

/-- One-sided Lipschitz bound on the ball. -/
theorem lip_one {At : Set ((κ → ℝ) × ℝ)} (hAt : IsCompact At) (hne : At.Nonempty) {a : ℝ}
    (ha : 0 < a) (N : ℕ) {w₀ : κ → ℝ} {r₀ : ℝ} (hr₀ : 0 ≤ r₀)
    (hball : ∀ p ∈ At, sqDist p.1 w₀ ≤ r₀ ^ 2) {c c' : κ → ℝ}
    (hc : sqDist c w₀ ≤ r₀ ^ 2) (hc' : sqDist c' w₀ ≤ r₀ ^ 2) :
    envelope At a N c' - envelope At a N c ≤ 8 * a * r₀ * Real.sqrt (sqDist c c') := by
  obtain ⟨q, hq, hqm⟩ := exists_max hAt hne a N c'
  have h1 := le_envelope hAt a N c hq
  have hm := mean_mem_ball hball hq
  set m := mean q.1 q.2.1
  have hdiff : envJ a N q.1 q.2.1 q.2.2 c' - envJ a N q.1 q.2.1 q.2.2 c =
      2 * a * (sqDist c m - sqDist c' m) := by
    rw [envJ_eq, envJ_eq]
    ring
  have hexp : sqDist c m - sqDist c' m = ∑ k, (c k - c' k) * (c k - w₀ k) +
      ∑ k, (c k - c' k) * (c' k - w₀ k) + 2 * ∑ k, (c k - c' k) * (w₀ k - m k) := by
    simp only [sqDist, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hsq : ∀ u v : κ → ℝ, sqDist u v ≤ r₀ ^ 2 → Real.sqrt (∑ k, (u k - v k) ^ 2) ≤ r₀ :=
    fun u v h => (Real.sqrt_le_sqrt h).trans_eq (Real.sqrt_sq hr₀)
  have e1 : ∑ k, (c k - c' k) * (c k - w₀ k) ≤
      Real.sqrt (∑ k, (c k - c' k) ^ 2) * Real.sqrt (∑ k, (c k - w₀ k) ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have e2 : ∑ k, (c k - c' k) * (c' k - w₀ k) ≤
      Real.sqrt (∑ k, (c k - c' k) ^ 2) * Real.sqrt (∑ k, (c' k - w₀ k) ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have e3 : ∑ k, (c k - c' k) * (w₀ k - m k) ≤
      Real.sqrt (∑ k, (c k - c' k) ^ 2) * Real.sqrt (∑ k, (w₀ k - m k) ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have b1 := hsq c w₀ hc
  have b2 := hsq c' w₀ hc'
  have b3 := hsq w₀ m (by rw [sqDist_comm]; exact hm)
  have hsqD : Real.sqrt (sqDist c c') = Real.sqrt (∑ k, (c k - c' k) ^ 2) := rfl
  rw [hsqD]
  set D := Real.sqrt (∑ k, (c k - c' k) ^ 2)
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  have hle : sqDist c m - sqDist c' m ≤ 4 * r₀ * D := by
    rw [hexp]
    have := mul_le_mul_of_nonneg_left b1 hD0
    have := mul_le_mul_of_nonneg_left b2 hD0
    have := mul_le_mul_of_nonneg_left b3 hD0
    linarith
  have := mul_le_mul_of_nonneg_left hle (by positivity : (0 : ℝ) ≤ 2 * a)
  linarith

/-- Part (c): `J ≤ 0` at the center `φ`. -/
theorem envJ_nonpos {At : Set ((κ → ℝ) × ℝ)} {a : ℝ} (ha : 0 < a) (N : ℕ) {φ : κ → ℝ}
    (hφ : ∀ p ∈ At, p.2 ^ N ≤ a * sqDist p.1 φ) {r : ℕ}
    {p : (Fin r → ℝ) × (Fin r → κ → ℝ) × (Fin r → ℝ)} (hp : p ∈ envAdm At r) :
    envJ a N p.1 p.2.1 p.2.2 φ ≤ 0 := by
  have hv := variance_decomp p.1 hp.2.1 p.2.1 φ
  have h1 : ∑ i, p.1 i * p.2.2 i ^ N ≤ ∑ i, p.1 i * (a * sqDist (p.2.1 i) φ) :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hφ (p.2.1 i, p.2.2 i) (hp.2.2 i)) (hp.1 i)
  have h2 : ∑ i, p.1 i * (a * sqDist (p.2.1 i) φ) = a * ∑ i, p.1 i * sqDist (p.2.1 i) φ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hv] at h2
  rw [envJ_eq, sqDist_comm φ]
  have h3 := mul_nonneg ha.le (sqDist_nonneg (mean p.1 p.2.1) φ)
  linarith

end EnvAux

open EnvAux in
/-- **Lemma 6.4** for a ball of radius `r₀ ≥ 0`.  (For `r₀ < 0` the Lipschitz clause of
`envelope_props` is false: see `envelope_lipschitz_false_of_neg_radius`.) -/
theorem envelope_props_of_nonneg (At : Set ((κ → ℝ) × ℝ)) (hAt : IsCompact At)
    (hne : At.Nonempty) (w₀ : κ → ℝ) (r₀ : ℝ) (hr₀ : 0 ≤ r₀)
    (hball : ∀ p ∈ At, sqDist p.1 w₀ ≤ r₀ ^ 2) (a : ℝ) (ha : 0 < a) (N : ℕ) :
    (∀ c, ∃ p ∈ envAdm At (Fintype.card κ + 3),
      envJ a N p.1 p.2.1 p.2.2 c = envelope At a N c) ∧
    ContDiff ℝ 1 (envelope At a N) ∧
    (∀ c, ∀ p ∈ envAdm At (Fintype.card κ + 3),
      envJ a N p.1 p.2.1 p.2.2 c = envelope At a N c →
      ∀ v, fderiv ℝ (envelope At a N) c v =
        4 * a * ∑ k, (∑ i, p.1 i * p.2.1 i k - c k) * v k) ∧
    (∀ c c', sqDist c w₀ ≤ r₀ ^ 2 → sqDist c' w₀ ≤ r₀ ^ 2 →
      |envelope At a N c - envelope At a N c'| ≤ 8 * a * r₀ * Real.sqrt (sqDist c c')) ∧
    (∀ c s, (c, s) ∈ At → s ^ N ≤ envelope At a N c) ∧
    (∀ φ : κ → ℝ, (∀ p ∈ At, p.2 ^ N ≤ a * sqDist p.1 φ) → envelope At a N φ ≤ 0) := by
  classical
  have hR : 0 < Fintype.card κ + 3 := by omega
  choose P hP hPe using exists_max hAt hne a N
  have hderiv : ∀ c, HasFDerivAt (envelope At a N) (gradCLM a (mean (P c).1 (P c).2.1) c) c :=
    fun c => hasFDerivAt_envelope hAt hne ha N (hP c) (hPe c)
  have hfd : fderiv ℝ (envelope At a N) = fun c => gradCLM a (mean (P c).1 (P c).2.1) c :=
    funext fun c => (hderiv c).fderiv
  -- continuity of the common mean `m₁*` of the maximizers
  have hcont : ∀ k, Continuous fun c => mean (P c).1 (P c).2.1 k := by
    intro k
    rw [continuous_iff_continuousAt]
    intro c
    have hb : ∀ c', |mean (P c').1 (P c').2.1 k - mean (P c).1 (P c).2.1 k| ≤
        Real.sqrt (64 * ∑ j, (c' j - c j) ^ 2) := by
      intro c'
      have hq : envJ a N (P c').1 (P c').2.1 (P c').2.2 (c + (c' - c)) =
          envelope At a N (c + (c' - c)) := by
        rw [add_sub_cancel]
        exact hPe c'
      have h64 := (key_bound hAt hne ha N (hP c) (hPe c) (hP c') hq).2
      apply Real.abs_le_sqrt
      calc (mean (P c').1 (P c').2.1 k - mean (P c).1 (P c).2.1 k) ^ 2
          ≤ sqDist (mean (P c').1 (P c').2.1) (mean (P c).1 (P c).2.1) :=
            Finset.single_le_sum
              (f := fun j => (mean (P c').1 (P c').2.1 j - mean (P c).1 (P c).2.1 j) ^ 2)
              (fun j _ => sq_nonneg _) (Finset.mem_univ k)
        _ ≤ 64 * ∑ j, (c' - c) j ^ 2 := h64
        _ = 64 * ∑ j, (c' j - c j) ^ 2 := by simp only [Pi.sub_apply]
    have ht : Tendsto (fun c' => Real.sqrt (64 * ∑ j, (c' j - c j) ^ 2)) (𝓝 c) (𝓝 0) := by
      have : Continuous fun c' : κ → ℝ => Real.sqrt (64 * ∑ j, (c' j - c j) ^ 2) := by fun_prop
      simpa using this.tendsto c
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun c' => by rw [Real.norm_eq_abs]; exact hb c') ht
  refine ⟨fun c => ⟨P c, hP c, hPe c⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [contDiff_one_iff_fderiv, hfd]
    refine ⟨fun c => (hderiv c).differentiableAt, ?_⟩
    unfold gradCLM
    exact continuous_finsetSum _ fun k _ =>
      (continuous_const.mul ((hcont k).sub (continuous_apply k))).smul continuous_const
  · intro c p hp hpe v
    rw [(hasFDerivAt_envelope hAt hne ha N hp hpe).fderiv, gradCLM_apply]
    rfl
  · intro c c' hc hc'
    rw [abs_sub_le_iff]
    constructor
    · have := lip_one hAt hne ha N hr₀ hball hc' hc
      rwa [sqDist_comm c' c] at this
    · exact lip_one hAt hne ha N hr₀ hball hc hc'
  · intro c s hcs
    have h1 := le_envelope hAt a N c (single_mem_envAdm hcs hR)
    dsimp only at h1
    rwa [envJ_single a N hR c s] at h1
  · intro φ hφ
    unfold envelope
    refine csSup_le ((envAdm_nonempty hne hR).image _) ?_
    rintro _ ⟨p, hp, rfl⟩
    exact envJ_nonpos ha N hφ hp

/-- The Lipschitz clause of `envelope_props` fails for a negative "radius" `r₀`: with
`κ = Fin 1`, the single atom `(0, 0)`, `w₀ = 0`, `r₀ = -1`, `a = N = 1`, `c = 0`, `c' = 1`,
all hypotheses hold but the right-hand side `8 a r₀ √|c - c'|² = -8` is negative. -/
theorem envelope_lipschitz_false_of_neg_radius :
    ¬ (∀ (At : Set ((Fin 1 → ℝ) × ℝ)), IsCompact At → At.Nonempty →
      ∀ (w₀ : Fin 1 → ℝ) (r₀ : ℝ), (∀ p ∈ At, sqDist p.1 w₀ ≤ r₀ ^ 2) →
      (∀ p ∈ At, 0 ≤ p.2 ∧ p.2 ≤ 1) → ∀ a : ℝ, 0 < a → ∀ N : ℕ, 1 ≤ N →
      ∀ c c', sqDist c w₀ ≤ r₀ ^ 2 → sqDist c' w₀ ≤ r₀ ^ 2 →
        |envelope At a N c - envelope At a N c'| ≤ 8 * a * r₀ * Real.sqrt (sqDist c c')) := by
  intro h
  have h1 : sqDist (0 : Fin 1 → ℝ) 1 = 1 := by simp [sqDist]
  have := h {((0 : Fin 1 → ℝ), (0 : ℝ))} isCompact_singleton (singleton_nonempty _) 0 (-1)
    (by simp [sqDist]) (by simp) 1 one_pos 1 le_rfl 0 1 (by simp [sqDist]) (by simp [sqDist])
  rw [h1, Real.sqrt_one] at this
  have := abs_nonneg (envelope {((0 : Fin 1 → ℝ), (0 : ℝ))} 1 1 0 -
    envelope {((0 : Fin 1 → ℝ), (0 : ℝ))} 1 1 1)
  linarith

/-- **Lemma 6.4**, with the standing assumptions: `At` is compact and nonempty, its atoms have
`ω ∈ closedBall w₀ r₀` (Euclidean, `r₀ ≥ 0`) and `0 ≤ s ≤ 1`; `a > 0`, `N ≥ 1`.  (The
hypotheses `0 ≤ s ≤ 1` and `N ≥ 1` of the paper are not needed.) -/
theorem envelope_props (At : Set ((κ → ℝ) × ℝ)) (hAt : IsCompact At) (hne : At.Nonempty)
    (w₀ : κ → ℝ) (r₀ : ℝ) (hr₀ : 0 ≤ r₀) (hball : ∀ p ∈ At, sqDist p.1 w₀ ≤ r₀ ^ 2)
    (_hs : ∀ p ∈ At, 0 ≤ p.2 ∧ p.2 ≤ 1) (a : ℝ) (ha : 0 < a) (N : ℕ) (_hN : 1 ≤ N) :
    -- the maximum is attained
    (∀ c, ∃ p ∈ envAdm At (Fintype.card κ + 3),
      envJ a N p.1 p.2.1 p.2.2 c = envelope At a N c) ∧
    -- (a) continuously differentiable, with the gradient formula
    ContDiff ℝ 1 (envelope At a N) ∧
    (∀ c, ∀ p ∈ envAdm At (Fintype.card κ + 3),
      envJ a N p.1 p.2.1 p.2.2 c = envelope At a N c →
      ∀ v, fderiv ℝ (envelope At a N) c v =
        4 * a * ∑ k, (∑ i, p.1 i * p.2.1 i k - c k) * v k) ∧
    -- (a) Lipschitz on the ball
    (∀ c c', sqDist c w₀ ≤ r₀ ^ 2 → sqDist c' w₀ ≤ r₀ ^ 2 →
      |envelope At a N c - envelope At a N c'| ≤ 8 * a * r₀ * Real.sqrt (sqDist c c')) ∧
    -- (b)
    (∀ c s, (c, s) ∈ At → s ^ N ≤ envelope At a N c) ∧
    -- (c)
    (∀ φ : κ → ℝ, (∀ p ∈ At, p.2 ^ N ≤ a * sqDist p.1 φ) → envelope At a N φ ≤ 0) := by
  exact envelope_props_of_nonneg At hAt hne w₀ r₀ hr₀ hball a ha N

end ClassSep
