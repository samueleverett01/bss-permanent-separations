import ClassSeparations.SA.Lemmas
import ClassSeparations.Basic.Circuits

/-!
# From real approximations to approximating circuits (§3.2, Lemma 3.3)

**Lemma 3.3.**  Fix finitely many circuit graphs.  Let `f ∈ ℝ[X]`, and suppose that for every
`η > 0` one of the graphs computes, for suitable real values of its constants, a polynomial all
of whose coefficients are within `η` of the corresponding coefficients of `f`.  Then one of the
graphs, with suitable constants in `ℝ((ε))`, approximates `f` in the sense of Definition 2.2.

## Proof outline

* `Shape.values_map`: the gate polynomials of `(Γ, c)` are the images of the *generic* gate
  polynomials (constants as variables, over `MvPolynomial ℕ ℝ`) under the evaluation map
  induced by `c`.  So each coefficient of a gate is a polynomial function of the constants.
* `exists_forall_of_list`: pigeonhole; one graph and one gate work for every `η`.
* `HasPSExp`, `HasExp`: asymptotic expansions at `0⁺` by formal power / Laurent series; they
  are compatible with sums and products (`HasExp.add`, `HasExp.mul`, `hasExp_eval`), and the
  expansion of a function with a limit at `0⁺` has no terms of negative order and the limit
  as constant term (`HasExp.coeff_of_tendsto`).
* `hasExp_of_puiseux`: (S7) gives such expansions for semialgebraic functions after the
  substitution `η = s^M`.
* `closure_core`: definable choice (S2) of the constants as functions of `η`, then Puiseux.
-/

noncomputable section

open MvPolynomial Filter Topology Asymptotics Set

namespace ClassSep

/-! ### Generic circuit polynomials -/

section Generic

variable {σ : Type*} {A B : Type*} [CommRing A] [CommRing B]

theorem Gate.eval_map (φ : A →+* B) (c : ℕ → A) (c' : ℕ → B) (hc : ∀ k, φ (c k) = c' k)
    (vals : List (MvPolynomial σ A)) (g : Gate σ) :
    g.eval c' (vals.map (MvPolynomial.map φ)) = MvPolynomial.map φ (g.eval c vals) := by
  have hget : ∀ j, (vals.map (MvPolynomial.map φ)).getD j 0 =
      MvPolynomial.map φ (vals.getD j 0) := by
    intro j
    simpa using List.getD_map (MvPolynomial.map φ) (l := vals) (d := 0) (n := j)
  cases g with
  | var i => simp [Gate.eval]
  | const k => simp [Gate.eval, hc]
  | add j k => simp only [Gate.eval, hget, map_add]
  | mul j k => simp only [Gate.eval, hget, map_mul]

theorem Shape.foldl_map (φ : A →+* B) (c : ℕ → A) (c' : ℕ → B) (hc : ∀ k, φ (c k) = c' k)
    (Γ : Shape σ) : ∀ init : List (MvPolynomial σ A),
    Γ.foldl (fun vals g => vals ++ [g.eval c' vals]) (init.map (MvPolynomial.map φ)) =
      (Γ.foldl (fun vals g => vals ++ [g.eval c vals]) init).map (MvPolynomial.map φ) := by
  induction Γ with
  | nil => intro init; simp
  | cons g Γ ih =>
    intro init
    simp only [List.foldl_cons]
    rw [← ih]
    congr 1
    simp [Gate.eval_map φ c c' hc]

/-- The gate polynomials of `(Γ, c')` are the images of those of `(Γ, c)` under a ring
homomorphism mapping `c` to `c'`. -/
theorem Shape.values_map (φ : A →+* B) (c : ℕ → A) (c' : ℕ → B) (hc : ∀ k, φ (c k) = c' k)
    (Γ : Shape σ) : Γ.values c' = (Γ.values c).map (MvPolynomial.map φ) := by
  have := Shape.foldl_map φ c c' hc Γ []
  simpa [Shape.values] using this

end Generic

/-! ### Pigeonhole -/

/-- If for every `η > 0` one of finitely many upward closed properties holds at `η`, then one
of them holds at every `η > 0`. -/
theorem exists_forall_of_list {ι : Type*} (T : List ι) (S : ι → ℝ → Prop)
    (hmono : ∀ p η η', η ≤ η' → S p η → S p η') (h : ∀ η > 0, ∃ p ∈ T, S p η) :
    ∃ p ∈ T, ∀ η > 0, S p η := by
  induction T with
  | nil =>
    obtain ⟨p, hp, -⟩ := h 1 one_pos
    simp at hp
  | cons q T ih =>
    by_cases hq : ∀ η > 0, S q η
    · exact ⟨q, List.mem_cons_self .., hq⟩
    · push Not at hq
      obtain ⟨η₁, hη₁, hn⟩ := hq
      obtain ⟨p, hp, hpS⟩ := ih (fun η hη => by
        obtain ⟨p, hp, hpS⟩ := h (min η η₁) (lt_min hη hη₁)
        rcases List.mem_cons.mp hp with rfl | hp
        · exact absurd (hmono _ _ _ (min_le_right _ _) hpS) hn
        · exact ⟨p, hp, hmono _ _ _ (min_le_left _ _) hpS⟩)
      exact ⟨p, List.mem_cons_of_mem _ hp, hpS⟩

/-! ### Asymptotic expansions at `0⁺` -/

/-- `g` has the formal power series `F` as asymptotic expansion at `0⁺`: for every `n`, some
polynomial agreeing with `F` up to degree `n - 1` approximates `g` up to `O(s^n)`. -/
def HasPSExp (g : ℝ → ℝ) (F : PowerSeries ℝ) : Prop :=
  ∀ n : ℕ, ∃ p : Polynomial ℝ, (∀ i < n, p.coeff i = PowerSeries.coeff i F) ∧
    (fun s => g s - p.eval s) =O[𝓝[>] 0] (fun s => s ^ n)

theorem poly_isBigO_one (p : Polynomial ℝ) :
    (fun s => p.eval s) =O[𝓝[>] (0 : ℝ)] (fun _ => (1 : ℝ)) :=
  ((p.continuous.tendsto 0).mono_left nhdsWithin_le_nhds).isBigO_one ℝ

theorem poly_isBigO_pow (p : Polynomial ℝ) (n : ℕ) (h : ∀ i < n, p.coeff i = 0) :
    (fun s => p.eval s) =O[𝓝[>] (0 : ℝ)] (fun s => s ^ n) := by
  obtain ⟨q, rfl⟩ := Polynomial.X_pow_dvd_iff.mpr h
  have := (isBigO_refl (fun s : ℝ => s ^ n) (𝓝[>] 0)).mul (poly_isBigO_one q)
  simpa using this

theorem isBigO_pow_pow_of_le {a b : ℕ} (h : b ≤ a) :
    (fun s : ℝ => s ^ a) =O[𝓝[>] (0 : ℝ)] (fun s => s ^ b) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [Ioo_mem_nhdsGT one_pos] with s hs
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (pow_pos hs.1 _),
    abs_of_pos (pow_pos hs.1 _), one_mul]
  exact pow_le_pow_of_le_one hs.1.le hs.2.le h

theorem tendsto_pow_nhdsGT {N : ℕ} (hN : 0 < N) :
    Tendsto (fun s : ℝ => s ^ N) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have : Tendsto (fun s : ℝ => s ^ N) (𝓝 0) (𝓝 (0 ^ N)) := (continuous_pow N).tendsto 0
    rw [zero_pow hN.ne'] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
    exact pow_pos hs N

theorem HasPSExp.congr {g g' : ℝ → ℝ} {F F' : PowerSeries ℝ} (h : HasPSExp g F)
    (hg : ∀ s, g s = g' s) (hF : F = F') : HasPSExp g' F' := by
  obtain rfl : g = g' := funext hg
  exact hF ▸ h

theorem HasPSExp.poly (p : Polynomial ℝ) : HasPSExp (fun s => p.eval s) (p : PowerSeries ℝ) := by
  intro n
  refine ⟨p, fun i _ => (Polynomial.coeff_coe p i).symm, ?_⟩
  simp only [sub_self]
  exact isBigO_zero _ _

theorem HasPSExp.isBigO_one {g : ℝ → ℝ} {F : PowerSeries ℝ} (h : HasPSExp g F) :
    g =O[𝓝[>] (0 : ℝ)] (fun _ => (1 : ℝ)) := by
  obtain ⟨p, -, hp⟩ := h 0
  have := hp.add (poly_isBigO_one p)
  simpa using this

theorem HasPSExp.add {g h : ℝ → ℝ} {F G : PowerSeries ℝ} (hg : HasPSExp g F)
    (hh : HasPSExp h G) : HasPSExp (fun s => g s + h s) (F + G) := by
  intro n
  obtain ⟨p, hpc, hp⟩ := hg n
  obtain ⟨q, hqc, hq⟩ := hh n
  refine ⟨p + q, fun i hi => by simp [hpc i hi, hqc i hi], ?_⟩
  refine (hp.add hq).congr_left (fun s => ?_)
  simp only [Polynomial.eval_add]
  ring

theorem HasPSExp.mul {g h : ℝ → ℝ} {F G : PowerSeries ℝ} (hg : HasPSExp g F)
    (hh : HasPSExp h G) : HasPSExp (fun s => g s * h s) (F * G) := by
  intro n
  obtain ⟨p, hpc, hp⟩ := hg n
  obtain ⟨q, hqc, hq⟩ := hh n
  refine ⟨p * q, fun i hi => ?_, ?_⟩
  · rw [Polynomial.coeff_mul, PowerSeries.coeff_mul]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    have h1 := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    rw [hpc _ (by omega), hqc _ (by omega)]
  · have h1 := hp.mul hh.isBigO_one
    have h2 := (poly_isBigO_one p).mul hq
    have := h1.add (h2.congr_right (fun s => by ring))
    refine (this.congr_left (fun s => ?_)).congr_right (fun s => by ring)
    simp only [Polynomial.eval_mul]
    ring

/-- `u` has the formal Laurent series `A` as asymptotic expansion at `0⁺`. -/
def HasExp (u : ℝ → ℝ) (A : LaurentSeries ℝ) : Prop :=
  ∃ (K : ℕ) (F : PowerSeries ℝ),
    A = HahnSeries.single (-(K : ℤ)) (1 : ℝ) * HahnSeries.ofPowerSeries ℤ ℝ F ∧
      HasPSExp (fun s => s ^ K * u s) F

theorem hasExp_const (r : ℝ) : HasExp (fun _ => r) (HahnSeries.C r) := by
  refine ⟨0, PowerSeries.C r, by simp, ?_⟩
  refine (HasPSExp.poly (Polynomial.C r)).congr (fun s => by simp) (Polynomial.coe_C r)

theorem HasExp.mul {u v : ℝ → ℝ} {A B : LaurentSeries ℝ} (hu : HasExp u A) (hv : HasExp v B) :
    HasExp (fun s => u s * v s) (A * B) := by
  obtain ⟨K, F, rfl, hF⟩ := hu
  obtain ⟨K', G, rfl, hG⟩ := hv
  refine ⟨K + K', F * G, ?_, ?_⟩
  · rw [map_mul]
    have : HahnSeries.single (-((K + K' : ℕ) : ℤ)) (1 : ℝ) =
        HahnSeries.single (-(K : ℤ)) (1 : ℝ) * HahnSeries.single (-(K' : ℤ)) (1 : ℝ) := by
      rw [HahnSeries.single_mul_single, one_mul,
        show -((K + K' : ℕ) : ℤ) = -(K : ℤ) + -(K' : ℤ) by push_cast; ring]
    rw [this]
    ring
  · refine (hF.mul hG).congr (fun s => by ring) rfl

theorem HasExp.add {u v : ℝ → ℝ} {A B : LaurentSeries ℝ} (hu : HasExp u A) (hv : HasExp v B) :
    HasExp (fun s => u s + v s) (A + B) := by
  obtain ⟨K, F, rfl, hF⟩ := hu
  obtain ⟨K', G, rfl, hG⟩ := hv
  refine ⟨K + K', PowerSeries.X ^ K' * F + PowerSeries.X ^ K * G, ?_, ?_⟩
  · rw [map_add, map_mul, map_mul, HahnSeries.ofPowerSeries_X_pow,
      HahnSeries.ofPowerSeries_X_pow, mul_add, ← mul_assoc, ← mul_assoc,
      HahnSeries.single_mul_single, HahnSeries.single_mul_single, one_mul,
      show -((K + K' : ℕ) : ℤ) + (K' : ℤ) = -(K : ℤ) by push_cast; ring,
      show -((K + K' : ℕ) : ℤ) + (K : ℤ) = -(K' : ℤ) by push_cast; ring]
  · have hX : ∀ j : ℕ, HasPSExp (fun s => s ^ j) (PowerSeries.X ^ j) := fun j =>
      (HasPSExp.poly (Polynomial.X ^ j)).congr (fun s => by simp) (by simp)
    refine (((hX K').mul hF).add ((hX K).mul hG)).congr (fun s => by ring) rfl

theorem hasExp_zero : HasExp (fun _ => 0) 0 := by
  simpa using hasExp_const 0

/-- Polynomials in functions with asymptotic expansions have the corresponding expansion. -/
theorem hasExp_eval {ι : Type*} (b : ℝ → ι → ℝ) (B : ι → LaurentSeries ℝ)
    (hb : ∀ k, HasExp (fun s => b s k) (B k)) (p : MvPolynomial ι ℝ) :
    HasExp (fun s => eval (b s) p) (eval₂Hom HahnSeries.C B p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using hasExp_const a
  | add p q hp hq => simpa using hp.add hq
  | mul_X p n hp => simpa using hp.mul (hb n)

/-- If `HasPSExp g F` and the coefficients of `F` below `i` vanish, then `g s / s^i` tends to
the `i`-th coefficient. -/
theorem HasPSExp.tendsto_div {g : ℝ → ℝ} {F : PowerSeries ℝ} (hg : HasPSExp g F) (i : ℕ)
    (hz : ∀ j < i, PowerSeries.coeff j F = 0) :
    Tendsto (fun s => g s / s ^ i) (𝓝[>] 0) (𝓝 (PowerSeries.coeff i F)) := by
  obtain ⟨p, hpc, hp⟩ := hg (i + 1)
  set a := PowerSeries.coeff i F
  have h1 : (fun s => p.eval s - a * s ^ i) =O[𝓝[>] 0] (fun s => s ^ (i + 1)) := by
    have := poly_isBigO_pow (p - Polynomial.C a * Polynomial.X ^ i) (i + 1) (fun j hj => by
      rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X_pow]
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hj | rfl
      · rw [ite_eq_right_iff.mpr (fun h => absurd h hj.ne), hpc j (by omega), hz j hj, sub_zero]
      · rw [ite_eq_left_iff.mpr (fun h => absurd rfl h), hpc _ (by omega), sub_self])
    simpa using this
  have h2 : (fun s => g s - a * s ^ i) =O[𝓝[>] 0] (fun s => s ^ (i + 1)) :=
    (hp.add h1).congr_left (fun s => by ring)
  have h3 : (fun s => g s / s ^ i - a) =O[𝓝[>] 0] (fun s => s) := by
    have := h2.mul (isBigO_refl (fun s : ℝ => (s ^ i)⁻¹) (𝓝[>] 0))
    refine this.congr' ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
      have : s ^ i ≠ 0 := pow_ne_zero _ (ne_of_gt hs)
      field_simp
    · filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
      have : s ^ i ≠ 0 := pow_ne_zero _ (ne_of_gt hs)
      field_simp
      ring
  have h4 : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  exact tendsto_sub_nhds_zero_iff.mp (h3.trans_tendsto h4)

/-- A formal Laurent series that is the expansion of a function with a limit at `0⁺` has no
terms of negative order, and its constant term is the limit. -/
theorem HasExp.coeff_of_tendsto {u : ℝ → ℝ} {A : LaurentSeries ℝ} (hA : HasExp u A) {L : ℝ}
    (hu : Tendsto u (𝓝[>] 0) (𝓝 L)) : A.coeff 0 = L ∧ ∀ j : ℤ, j < 0 → A.coeff j = 0 := by
  obtain ⟨K, F, rfl, hF⟩ := hA
  have hdiv : ∀ i ≤ K, Tendsto (fun s => (s ^ K * u s) / s ^ i) (𝓝[>] 0)
      (𝓝 ((0 : ℝ) ^ (K - i) * L)) := by
    intro i hi
    have : Tendsto (fun s : ℝ => s ^ (K - i) * u s) (𝓝[>] 0) (𝓝 ((0 : ℝ) ^ (K - i) * L)) :=
      (((continuous_pow (K - i)).tendsto 0).mono_left nhdsWithin_le_nhds).mul hu
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
    have : s ^ i ≠ 0 := pow_ne_zero _ (ne_of_gt hs)
    have hK : s ^ K = s ^ (K - i) * s ^ i := by rw [← pow_add, Nat.sub_add_cancel hi]
    rw [hK]
    field_simp
  have hzero : ∀ i < K, PowerSeries.coeff i F = 0 := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      have h1 := hF.tendsto_div i (fun j hj => ih j hj (hj.trans hi))
      have h2 := hdiv i hi.le
      rw [zero_pow (by omega), zero_mul] at h2
      exact tendsto_nhds_unique h1 h2
  have hK : PowerSeries.coeff K F = L := by
    have h1 := hF.tendsto_div K hzero
    have h2 := hdiv K le_rfl
    simp only [Nat.sub_self, pow_zero, one_mul] at h2
    exact tendsto_nhds_unique h1 h2
  have hcoeff : ∀ j : ℤ, (HahnSeries.single (-(K : ℤ)) (1 : ℝ) *
      HahnSeries.ofPowerSeries ℤ ℝ F).coeff j =
      if j + K < 0 then 0 else PowerSeries.coeff (j + K).natAbs F := by
    intro j
    have := HahnSeries.coeff_single_mul_add (r := (1 : ℝ))
      (x := HahnSeries.ofPowerSeries ℤ ℝ F) (a := j + K) (b := -(K : ℤ))
    rw [show j + K + -(K : ℤ) = j by ring, one_mul] at this
    rw [this]
    exact PowerSeries.coeff_coe _ _
  refine ⟨?_, fun j hj => ?_⟩
  · rw [hcoeff, ite_eq_right_iff.mpr (fun h => absurd h (by omega))]
    simpa using hK
  · rw [hcoeff]
    split_ifs with h
    · rfl
    · exact hzero _ (by omega)

/-- **(S7) in the form used**: from the Puiseux expansion of `a(t^M)` and a multiplier
`N ≥ 1`, the function `s ↦ a(s^(MN))` has an asymptotic expansion by a Laurent series. -/
theorem hasExp_of_puiseux {a : ℝ → ℝ} {M : ℕ} {j₀ : ℤ} {c : ℕ → ℝ} {N : ℕ} (hN : 0 < N)
    (h : ∀ J : ℕ, (fun s : ℝ => a (s ^ M) - ∑ i ∈ Finset.range J, c i * s ^ (j₀ + i)) =O[𝓝[>] 0]
      (fun s : ℝ => s ^ (j₀ + J))) :
    ∃ A, HasExp (fun s => a (s ^ (M * N))) A := by
  set K : ℕ := N * j₀.natAbs with hKdef
  set d : ℕ := ((K : ℤ) + N * j₀).toNat with hddef
  have hd : (d : ℤ) = K + N * j₀ := by
    rw [hddef, Int.toNat_of_nonneg]
    rw [hKdef]
    push_cast
    have : (0 : ℤ) ≤ |j₀| + j₀ := by cases abs_cases j₀ <;> linarith
    nlinarith [Int.natCast_natAbs j₀]
  have key : ∀ s : ℝ, 0 < s → ∀ e : ℕ, s ^ K * (s ^ N) ^ (j₀ + (e : ℤ)) = s ^ (d + N * e) := by
    intro s hs e
    rw [← zpow_natCast s N, ← zpow_mul, ← zpow_natCast s K, ← zpow_add₀ hs.ne', ← zpow_natCast]
    congr 1
    push_cast
    rw [hd]
    ring
  let P : ℕ → Polynomial ℝ := fun J =>
    ∑ i ∈ Finset.range J, Polynomial.C (c i) * Polynomial.X ^ (d + N * i)
  have hstab : ∀ m J, m < J → (P J).coeff m = (P (m + 1)).coeff m := by
    intro m J hJ
    induction J with
    | zero => omega
    | succ J ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hJ with hJ | rfl
      · have hP : P (J + 1) = P J + Polynomial.C (c J) * Polynomial.X ^ (d + N * J) :=
          Finset.sum_range_succ _ _
        have hle : J ≤ N * J := Nat.le_mul_of_pos_left J hN
        rw [hP, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
          ite_eq_right_iff.mpr (fun h => absurd h (by omega)), add_zero,
          ih hJ]
      · rfl
  let F : PowerSeries ℝ := PowerSeries.mk fun m => (P (m + 1)).coeff m
  refine ⟨HahnSeries.single (-(K : ℤ)) 1 * HahnSeries.ofPowerSeries ℤ ℝ F, K, F, rfl, ?_⟩
  intro n
  refine ⟨P n, fun i hi => by rw [PowerSeries.coeff_mk, hstab i n hi], ?_⟩
  have h1 := (h n).comp_tendsto (tendsto_pow_nhdsGT hN)
  have h2 := (isBigO_refl (fun s : ℝ => s ^ K) (𝓝[>] 0)).mul h1
  have h3 : (fun s : ℝ => s ^ (d + N * n)) =O[𝓝[>] 0] (fun s => s ^ n) :=
    isBigO_pow_pow_of_le (by nlinarith)
  refine (h2.congr' ?_ ?_).trans h3
  · filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
    simp only [Function.comp, P, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rw [mul_sub, Finset.mul_sum, ← pow_mul, mul_comm N M]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← key s hs i]
    ring
  · filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
    exact key s hs n

/-! ### Semialgebraic sets used in the proof -/

theorem isSA_finset_forall {α : Type} {ι : Type*} (s : Finset ι) (S : ι → Set (α → ℝ))
    (h : ∀ i ∈ s, IsSA (S i)) : IsSA {w | ∀ i ∈ s, w ∈ S i} := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isSA_univ : IsSA (Set.univ : Set (α → ℝ)))
  | insert i s hi ih =>
    have := (h i (Finset.mem_insert_self _ _)).inter
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))
    convert this using 1
    ext w
    simp

/-- A coordinate of a semialgebraic map `ℝ → ℝ^β`, restricted to `(0, 1)`, is semialgebraic.
(A special case of `isSAFunOn_iff_coord` and `IsSAFunOn.mono`, proved directly.) -/
theorem isSAFun₁₁_coord {β : Type} [Fintype β] {g : (Unit → ℝ) → (β → ℝ)}
    (hg : IsSAFunOn Set.univ g) (k : β) :
    IsSAFun₁₁ (Ioo 0 1) (fun η => g (fun _ => η) k) := by
  have hD : IsSA {v : Unit → ℝ | v () ∈ Ioo (0 : ℝ) 1} := by
    have := (isSA_pos (X () : MvPolynomial Unit ℝ)).inter
      (isSA_pos (1 - X () : MvPolynomial Unit ℝ))
    convert this using 1
    ext v
    simp
  refine ⟨hD, ?_⟩
  let e : Unit ⊕ β → (Unit ⊕ Unit) ⊕ β := Sum.elim (fun _ => Sum.inl (Sum.inl ())) Sum.inr
  have h1 := hg.2.preimage_comp e
  have h2 := isSA_zero
    (X (Sum.inl (Sum.inr ())) - X (Sum.inr k) : MvPolynomial ((Unit ⊕ Unit) ⊕ β) ℝ)
  have h3 := (h1.inter h2).exists_sum (γ := β)
  have h4 := hD.preimage_comp (Sum.inl : Unit → Unit ⊕ Unit)
  convert h4.inter h3 using 1
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_univ, true_and, map_sub, eval_X,
    Function.comp_def, Sum.elim_inl, Sum.elim_inr, sub_eq_zero]
  constructor
  · rintro ⟨hv, hgr⟩
    refine ⟨hv, g (fun _ => v (Sum.inl ())), ?_, ?_⟩
    · funext b
      simp [e]
    · exact (congrFun hgr ()).symm
  · rintro ⟨hv, z, hz, h0⟩
    refine ⟨hv, funext fun u => ?_⟩
    have hz' : g (fun _ => v (Sum.inl ())) = z := by
      simpa [e] using hz
    rw [hz', h0]

/-! ### The core argument -/

/-- The core of Lemma 3.3, for one generic gate polynomial `G` whose coefficients are
polynomials in the constants. -/
theorem closure_core (hS : SAFacts) {σ : Type*} (G : MvPolynomial σ (MvPolynomial ℕ ℝ))
    (f : MvPolynomial σ ℝ)
    (h : ∀ η > 0, ∃ a : ℕ → ℝ, ∀ m, |eval a (G.coeff m) - f.coeff m| < η) :
    ∃ c : ℕ → LaurentSeries ℝ, ∀ m,
      (eval₂Hom HahnSeries.C c (G.coeff m)).coeff 0 = f.coeff m ∧
      ∀ j : ℤ, j < 0 → (eval₂Hom HahnSeries.C c (G.coeff m)).coeff j = 0 := by
  classical
  -- the relevant monomials `𝒜` and the constants `V` that occur
  set 𝒜 : Finset (σ →₀ ℕ) := G.support ∪ f.support with h𝒜
  set V : Finset ℕ := 𝒜.biUnion (fun m => (G.coeff m).vars) with hV
  let ext : (V → ℝ) → ℕ → ℝ := fun v k => if hk : k ∈ V then v ⟨k, hk⟩ else 0
  have hext : ∀ a : ℕ → ℝ, ∀ m ∈ 𝒜,
      eval (ext (fun k : V => a k)) (G.coeff m) = eval a (G.coeff m) := by
    intro a m hm
    refine eval₂Hom_congr' rfl (fun k hk _ => ?_) rfl
    have hkV : k ∈ V := Finset.mem_biUnion.mpr ⟨m, hm, hk⟩
    simp [ext, hkV]
  -- the semialgebraic set of `(η, a)` with `max_{α ∈ 𝒜} |ψ_α(a) - f_α| < η`, `0 < η < 1`
  let R : (σ →₀ ℕ) → MvPolynomial (Unit ⊕ V) ℝ := fun m =>
    bind₁ (fun k => if hk : k ∈ V then X (Sum.inr ⟨k, hk⟩) else 0) (G.coeff m)
  have hR : ∀ m w, eval w (R m) = eval (ext (w ∘ Sum.inr)) (G.coeff m) := by
    intro m w
    rw [eval_bind₁']
    exact congrArg (fun v => eval v (G.coeff m))
      (funext fun k => by by_cases hk : k ∈ V <;> simp [ext, hk])
  let E : Set (Unit ⊕ V → ℝ) := {w | 0 < w (Sum.inl ()) ∧ w (Sum.inl ()) < 1 ∧
    ∀ m ∈ 𝒜, |eval (ext (w ∘ Sum.inr)) (G.coeff m) - f.coeff m| < w (Sum.inl ())}
  have hE : IsSA E := by
    have h0 := isSA_pos (X (Sum.inl ()) : MvPolynomial (Unit ⊕ V) ℝ)
    have h1 := isSA_pos (1 - X (Sum.inl ()) : MvPolynomial (Unit ⊕ V) ℝ)
    have h2 := isSA_finset_forall 𝒜 (fun m =>
      {w : Unit ⊕ V → ℝ | 0 < eval w (X (Sum.inl ()) - R m + C (f.coeff m))} ∩
        {w | 0 < eval w (X (Sum.inl ()) + R m - C (f.coeff m))})
      (fun m _ => (isSA_pos _).inter (isSA_pos _))
    convert (h0.inter h1).inter h2 using 1
    ext w
    simp only [E, Set.mem_ofPred_eq, Set.mem_inter_iff, eval_X, map_sub, map_one, map_add,
      eval_C, hR, abs_lt]
    constructor
    · rintro ⟨h0, h1, h2⟩
      refine ⟨⟨h0, by linarith⟩, fun m hm => ?_⟩
      obtain ⟨h3, h4⟩ := h2 m hm
      constructor <;> linarith
    · rintro ⟨⟨h0, h1⟩, h2⟩
      refine ⟨h0, by linarith, fun m hm => ?_⟩
      obtain ⟨h3, h4⟩ := h2 m hm
      constructor <;> linarith
  -- (S2) definable choice: a semialgebraic section `η ↦ a(η)`
  obtain ⟨sec, hsec, hsecE⟩ := hS.choice E hE
  have hgood : ∀ η ∈ Ioo (0 : ℝ) 1, ∀ m ∈ 𝒜,
      |eval (ext (sec (fun _ => η))) (G.coeff m) - f.coeff m| < η := by
    intro η hη m hm
    have hmem := hsecE (fun _ => η) (by
      obtain ⟨a, ha⟩ := h η hη.1
      refine ⟨fun k => a k, hη.1, hη.2, fun m hm => ?_⟩
      have h1 : (Sum.elim (fun _ : Unit => η) (fun k : V => a k)) ∘ Sum.inr =
        (fun k : V => a k) := Sum.elim_comp_inr _ _
      simp only [h1, Sum.elim_inl]
      rw [hext a m hm]
      exact ha m)
    have := hmem.2.2 m hm
    simpa using this
  have hSA : ∀ k : V, IsSAFun₁₁ (Ioo 0 1) (fun η => sec (fun _ => η) k) :=
    isSAFun₁₁_coord hsec
  -- (S7) Puiseux, with a common denominator `Mt` of the exponents
  have hP := fun k => hS.puiseux (fun η => sec (fun _ => η) k) 1 one_pos (hSA k)
  choose M j₀ cc hM hexp using hP
  set Mt : ℕ := ∏ k, M k with hMtdef
  have hMt : 0 < Mt := Finset.prod_pos (fun k _ => hM k)
  have hA : ∀ k : V, ∃ A, HasExp (fun s => sec (fun _ => s ^ Mt) k) A := by
    intro k
    obtain ⟨N, hN⟩ : M k ∣ Mt := Finset.dvd_prod_of_mem _ (Finset.mem_univ k)
    have hNpos : 0 < N := by
      rcases Nat.eq_zero_or_pos N with h0 | h0
      · rw [h0, mul_zero] at hN; omega
      · exact h0
    obtain ⟨A, hA⟩ := hasExp_of_puiseux (a := fun η => sec (fun _ => η) k) hNpos (hexp k)
    exact ⟨A, by rw [hN]; exact hA⟩
  choose A hA using hA
  let c : ℕ → LaurentSeries ℝ := fun k => if hk : k ∈ V then A ⟨k, hk⟩ else 0
  refine ⟨c, fun m => ?_⟩
  by_cases hm : m ∈ 𝒜
  · have hexpm := hasExp_eval (fun s => ext (sec (fun _ => s ^ Mt))) c (fun k => by
      by_cases hk : k ∈ V
      · simpa [ext, c, hk] using hA ⟨k, hk⟩
      · simpa [ext, c, hk] using hasExp_zero) (G.coeff m)
    have hpow : Tendsto (fun s : ℝ => s ^ Mt) (𝓝[>] 0) (𝓝 0) :=
      (tendsto_pow_nhdsGT hMt).mono_right nhdsWithin_le_nhds
    have ht : Tendsto (fun s : ℝ => eval (ext (sec (fun _ => s ^ Mt))) (G.coeff m)) (𝓝[>] 0)
        (𝓝 (f.coeff m)) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      filter_upwards [hpow.eventually (gt_mem_nhds hε), Ioo_mem_nhdsGT one_pos] with s hs1 hs2
      rw [Real.dist_eq]
      have hη : s ^ Mt ∈ Ioo (0 : ℝ) 1 :=
        ⟨pow_pos hs2.1 _, pow_lt_one₀ hs2.1.le hs2.2 hMt.ne'⟩
      exact (hgood _ hη m hm).trans hs1
    exact hexpm.coeff_of_tendsto ht
  · have hG : G.coeff m = 0 := by
      by_contra hne
      exact hm (Finset.mem_union_left _ (mem_support_iff.mpr hne))
    have hf : f.coeff m = 0 := by
      by_contra hne
      exact hm (Finset.mem_union_right _ (mem_support_iff.mpr hne))
    simp [hG, hf]

variable {σ : Type} [Fintype σ]

set_option linter.unusedSectionVars false in
/-- **Lemma 3.3.** -/
theorem closure_lemma (hS : SAFacts) (graphs : List (Shape σ)) (f : MvPolynomial σ ℝ)
    (h : ∀ η > 0, ∃ Γ ∈ graphs, ∃ (a : ℕ → ℝ) (P : MvPolynomial σ ℝ), Γ.Computes a P ∧
      ∀ m, |P.coeff m - f.coeff m| < η) :
    ∃ Γ ∈ graphs, ∃ (c : ℕ → LaurentSeries ℝ) (P : MvPolynomial σ (LaurentSeries ℝ)),
      Γ.Computes c P ∧ IsApprox P f := by
  -- generic gate polynomials: the constants are the variables of `MvPolynomial ℕ ℝ`
  let gen : Shape σ → List (MvPolynomial σ (MvPolynomial ℕ ℝ)) := fun Γ =>
    Γ.values (X : ℕ → MvPolynomial ℕ ℝ)
  have hreal : ∀ (Γ : Shape σ) (a : ℕ → ℝ),
      Γ.values a = (gen Γ).map (MvPolynomial.map (eval a)) :=
    fun Γ a => Shape.values_map (eval a) X a (fun k => eval_X _) Γ
  have hlaur : ∀ (Γ : Shape σ) (c : ℕ → LaurentSeries ℝ),
      Γ.values c = (gen Γ).map (MvPolynomial.map (eval₂Hom HahnSeries.C c)) :=
    fun Γ c => Shape.values_map _ X c (fun k => eval₂Hom_X' _ _ _) Γ
  -- pigeonhole over the pairs (graph, gate)
  let T : List (Shape σ × ℕ) :=
    graphs.flatMap (fun Γ => (List.range (gen Γ).length).map (fun i => (Γ, i)))
  let S : Shape σ × ℕ → ℝ → Prop := fun p η =>
    ∃ a : ℕ → ℝ, ∀ m, |eval a (((gen p.1).getD p.2 0).coeff m) - f.coeff m| < η
  obtain ⟨⟨Γ, i⟩, hp, hSp⟩ := exists_forall_of_list T S
    (fun p η η' hle ⟨a, ha⟩ => ⟨a, fun m => (ha m).trans_le hle⟩) (by
      intro η hη
      obtain ⟨Γ, hΓ, a, P, hP, hPf⟩ := h η hη
      rw [Shape.Computes, hreal, List.mem_map] at hP
      obtain ⟨Q, hQ, rfl⟩ := hP
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hQ
      refine ⟨(Γ, i), ?_, a, fun m => ?_⟩
      · simp only [T, List.mem_flatMap, List.mem_map, List.mem_range]
        exact ⟨Γ, hΓ, i, hi, rfl⟩
      · have := hPf m
        rw [coeff_map] at this
        rwa [List.getD_eq_getElem _ _ hi])
  simp only [T, List.mem_flatMap, List.mem_map, List.mem_range, Prod.mk.injEq] at hp
  obtain ⟨Γ', hΓ', i', hi', rfl, rfl⟩ := hp
  obtain ⟨c, hc⟩ := closure_core hS ((gen Γ').getD i' 0) f hSp
  refine ⟨Γ', hΓ', c, MvPolynomial.map (eval₂Hom HahnSeries.C c) ((gen Γ').getD i' 0), ?_,
    fun m => ?_⟩
  · rw [Shape.Computes, hlaur, List.mem_map]
    exact ⟨_, by rw [List.getD_eq_getElem _ _ hi']; exact List.getElem_mem hi', rfl⟩
  · rw [coeff_map]
    exact hc m

/-- Lemma 3.3 in terms of border complexity. -/
theorem borderLE_of_approx (hS : SAFacts) (graphs : List (Shape σ)) (s : ℕ)
    (hs : ∀ Γ ∈ graphs, Γ.length ≤ s) (f : MvPolynomial σ ℝ)
    (h : ∀ η > 0, ∃ Γ ∈ graphs, ∃ (a : ℕ → ℝ) (P : MvPolynomial σ ℝ), Γ.Computes a P ∧
      ∀ m, |P.coeff m - f.coeff m| < η) :
    BorderLE f s := by
  obtain ⟨Γ, hΓ, c, P, hP, happ⟩ := closure_lemma hS graphs f h
  exact ⟨Γ, c, hs Γ hΓ, P, hP, happ⟩

end ClassSep
