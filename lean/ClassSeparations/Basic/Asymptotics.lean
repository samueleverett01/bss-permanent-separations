import ClassSeparations.Cited

/-!
# Asymptotic consequences of the permanent lower bound

If the border complexity of `per_m` is bounded by a polynomial in `m` and `t_m`, then the
lower bound of Theorem 2.3 (`PermLowerBound`) forces `t_m ≥ 2^{c (log₂ m)^{4/3}}` for some
`c > 0` and all large `m`.  This is the last step of Corollaries 4.7, 5.5 and 6.8.

The conclusion is stated in the unfolded form of `ClassSep.SuperPolyLB`
(`ClassSeparations.Cert.Permanent`), so that this file can be imported there.
-/

noncomputable section

open MvPolynomial Filter

namespace ClassSep

/-- Border complexity bounds are monotone in the size. -/
theorem BorderLE.mono {σ : Type*} {f : MvPolynomial σ ℝ} {s s' : ℕ} (h : BorderLE f s)
    (hss : s ≤ s') : BorderLE f s' := by
  obtain ⟨Γ, c, hΓ, P, hP, hPf⟩ := h
  exact ⟨Γ, c, hΓ.trans hss, P, hP, hPf⟩

/-- For `c > 0`, eventually `K + a L ≤ c L^{4/3}` with `L = log₂ m`. -/
theorem eventually_add_mul_logb_le (c K a : ℝ) (hc : 0 < c) :
    ∀ᶠ m : ℕ in atTop, K + a * Real.logb 2 m ≤ c * Real.logb 2 m ^ (4 / 3 : ℝ) := by
  have hL : Tendsto (fun m : ℕ => Real.logb 2 m) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have h1 := hL.eventually_ge_atTop 1
  have h2 := hL.eventually
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).eventually_ge_atTop ((|K| + |a|) / c))
  filter_upwards [h1, h2] with m hm1 hm2
  set L := Real.logb 2 m
  have hL0 : 0 < L := by linarith
  have hpow : L ^ (4 / 3 : ℝ) = L * L ^ (1 / 3 : ℝ) := by
    rw [show (4 / 3 : ℝ) = 1 + 1 / 3 by norm_num, Real.rpow_add hL0, Real.rpow_one]
  rw [hpow]
  have h3 : |K| + |a| ≤ c * L ^ (1 / 3 : ℝ) := by
    rw [div_le_iff₀ hc] at hm2; linarith
  calc K + a * L ≤ |K| * L + |a| * L := by
        nlinarith [le_abs_self K, le_abs_self a, abs_nonneg K, abs_nonneg a,
          mul_nonneg (abs_nonneg K) (sub_nonneg.2 hm1),
          mul_le_mul_of_nonneg_right (le_abs_self a) hL0.le]
    _ = (|K| + |a|) * L := by ring
    _ ≤ c * L ^ (1 / 3 : ℝ) * L := by gcongr
    _ = c * (L * L ^ (1 / 3 : ℝ)) := by ring

/-- **The asymptotic step.**  If `PermLowerBound` holds and for all large `m` the border
complexity of `per_m` is at most `A (m+1)^a (t_m+1)^b`, then `t_m ≥ 2^{c (log₂ m)^{4/3}}` for
some `c > 0` and all large `m` (i.e. `SuperPolyLB fun m => t m`). -/
theorem superPoly_of_borderLE (hLB : PermLowerBound) (t : ℕ → ℕ) (A a b : ℕ)
    (h : ∀ᶠ m in atTop, BorderLE (per m) (A * (m + 1) ^ a * (t m + 1) ^ b)) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ m : ℕ in atTop, (2 : ℝ) ^ (c * Real.logb 2 m ^ (4 / 3 : ℝ)) ≤ t m := by
  obtain ⟨c₀, hc₀, m₀, hm₀⟩ := hLB
  set B : ℕ := b + 1 with hBdef
  have hBpos : (0 : ℝ) < B := by positivity
  refine ⟨c₀ / (2 * B), by positivity, ?_⟩
  filter_upwards [h, eventually_ge_atTop m₀, eventually_ge_atTop 1,
    eventually_add_mul_logb_le (c₀ / 2) (A + a + B) a (by positivity)] with m hB hm₀' hm1 hK
  by_contra hlt
  rw [not_le] at hlt
  set L := Real.logb 2 m with hLdef
  set c := c₀ / (2 * B) with hcdef
  have hlow := hm₀ m hm₀' _ hB
  push_cast at hlow
  have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hL0 : 0 ≤ L := Real.logb_nonneg (by norm_num) hm1'
  have h2L : (2 : ℝ) ^ L = m := Real.rpow_logb (by norm_num) (by norm_num) (by linarith)
  set L' := L ^ (4 / 3 : ℝ) with hL'def
  have hL'0 : 0 ≤ L' := Real.rpow_nonneg hL0 _
  set E := (2 : ℝ) ^ (c * L') with hEdef
  have hE1 : 1 ≤ E := Real.one_le_rpow (by norm_num) (by positivity)
  -- the three factors
  have hA : (A : ℝ) ≤ (2 : ℝ) ^ (A : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast (Nat.lt_two_pow_self).le
  have hmA : ((m : ℝ) + 1) ^ a ≤ (2 : ℝ) ^ ((1 + L) * a) := by
    rw [Real.rpow_mul_natCast (by norm_num)]
    gcongr
    rw [Real.rpow_add (by norm_num), Real.rpow_one, h2L]
    linarith
  have htB : ((t m : ℝ) + 1) ^ b ≤ (2 : ℝ) ^ ((1 + c * L') * B) := by
    have ht1 : (1 : ℝ) ≤ (t m : ℝ) + 1 := by have := (t m).cast_nonneg (α := ℝ); linarith
    calc ((t m : ℝ) + 1) ^ b ≤ ((t m : ℝ) + 1) ^ B := pow_le_pow_right₀ ht1 (by omega)
      _ ≤ (2 * E) ^ B := by gcongr; linarith
      _ = (2 : ℝ) ^ ((1 + c * L') * B) := by
        rw [Real.rpow_mul_natCast (by norm_num), Real.rpow_add (by norm_num), Real.rpow_one]
  have hcB : c * B = c₀ / 2 := by
    rw [hcdef]; field_simp
  have hprod : (A : ℝ) * ((m : ℝ) + 1) ^ a * ((t m : ℝ) + 1) ^ b ≤ (2 : ℝ) ^ (c₀ * L') := by
    calc (A : ℝ) * ((m : ℝ) + 1) ^ a * ((t m : ℝ) + 1) ^ b
        ≤ (2 : ℝ) ^ (A : ℝ) * (2 : ℝ) ^ ((1 + L) * a) * (2 : ℝ) ^ ((1 + c * L') * B) := by
          gcongr
      _ = (2 : ℝ) ^ ((A : ℝ) + (1 + L) * a + (1 + c * L') * B) := by
          rw [Real.rpow_add (by norm_num), Real.rpow_add (by norm_num)]
      _ ≤ (2 : ℝ) ^ (c₀ * L') := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          have : (1 + c * L') * B = B + c₀ / 2 * L' := by rw [← hcB]; ring
          rw [this]
          nlinarith
  linarith

end ClassSep
