import ClassSeparations.Cert.Graph
import ClassSeparations.Cited
import ClassSeparations.Basic.Asymptotics

/-!
# The permanent (§4.5, Lemma 4.6 and Corollary 4.7)

**Lemma 4.6** (Ryser's formula): `per_m(X) = ∑_{S ⊆ [m]} (-1)^{m-|S|} ∏ᵢ ∑_{j∈S} X_{ij}`.
The membership of the three languages in `PAR_ℝ` is proved in
`ClassSeparations.Machines.Ryser`.

**Corollary 4.7** (tree part): trees of depth `t_m` deciding `{Y = per_m(X)}`, `{Y ≤ per_m(X)}`
or `{Y ≥ per_m(X)}` in the existential sense have `t_m ≥ 2^{Ω((log m)^{4/3})}`.  The
class-level consequences (`PERM ∉ NP_ℝ`, `NP_ℝ ⊊ PAR_ℝ`) are in
`ClassSeparations.Machines.Separations`.
-/

noncomputable section

open MvPolynomial Set Filter Topology

namespace ClassSep

/-- The relations `Y = P`, `Y ≤ P`, `Y ≥ P`, `Y < P`, `Y > P` between `Y` and the value `P` of
the permanent. -/
inductive PerRel where
  | eq
  | le
  | ge
  | lt
  | gt

/-- `PerRel.holds r Y P` means `Y r P`. -/
def PerRel.holds : PerRel → ℝ → ℝ → Prop
  | .eq, Y, P => Y = P
  | .le, Y, P => Y ≤ P
  | .ge, Y, P => P ≤ Y
  | .lt, Y, P => Y < P
  | .gt, Y, P => P < Y

/-- The language `{(X, Y) : Y r per_m(X)}`. -/
def perLang (r : PerRel) (m : ℕ) (X : Fin m × Fin m → ℝ) (Y : ℝ) : Prop :=
  r.holds Y (eval X (per m))

/-- A tree on inputs `(X, Y, z)` decides `L` in the existential sense. -/
def ExDecides {α γ : Type} (T : Tree (α ⊕ Unit ⊕ γ)) (L : (α → ℝ) → ℝ → Prop) : Prop :=
  ∀ X Y, (∃ z, T.Accepts (inp3 X Y z)) ↔ L X Y

/-- A tree on inputs `(X, Y, z)` decides `L` in the universal sense. -/
def AllDecides {α γ : Type} (T : Tree (α ⊕ Unit ⊕ γ)) (L : (α → ℝ) → ℝ → Prop) : Prop :=
  ∀ X Y, (∀ z, T.Accepts (inp3 X Y z)) ↔ L X Y

/-- `t_m ≥ 2^{Ω((log m)^{4/3})}`: there is `c > 0` with `t_m ≥ 2^{c (log₂ m)^{4/3}}` for all
large `m`. -/
def SuperPolyLB (t : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ m : ℕ in atTop, (2 : ℝ) ^ (c * Real.logb 2 m ^ (4 / 3 : ℝ)) ≤ t m

/-- Inclusion–exclusion: the alternating sum `∑_{S ⊇ T} (-1)^{|α| - |S|}` is `1` if `T` is
everything and `0` otherwise. -/
theorem sum_superset_neg_one_pow {α R : Type*} [Fintype α] [DecidableEq α] [CommRing R]
    (T : Finset α) :
    ∑ S : Finset α, (if T ⊆ S then (-1 : R) ^ (Fintype.card α - S.card) else 0) =
      if T = Finset.univ then 1 else 0 := by
  -- reindex by complements: `S ↦ Sᶜ`
  rw [← Fintype.sum_equiv (Function.Involutive.toPerm _ compl_compl)
    (fun S : Finset α => if T ⊆ Sᶜ then (-1 : R) ^ (Fintype.card α - Sᶜ.card) else 0) _
    (fun _ => rfl)]
  have h1 : ∀ S : Finset α, (if T ⊆ Sᶜ then (-1 : R) ^ (Fintype.card α - Sᶜ.card) else 0) =
      if S ∈ Tᶜ.powerset then (((-1 : ℤ) ^ S.card : ℤ) : R) else 0 := by
    intro S
    have h : T ⊆ Sᶜ ↔ S ∈ Tᶜ.powerset := by
      rw [Finset.mem_powerset, Finset.subset_compl_comm]
    rw [Finset.card_compl, Nat.sub_sub_self (Finset.card_le_univ S)]
    by_cases hS : S ∈ Tᶜ.powerset
    · rw [ite_eq_left (h.mpr hS), ite_eq_left hS]; push_cast; rfl
    · rw [ite_eq_right (mt h.mp hS), ite_eq_right hS]
  simp_rw [h1]
  rw [Finset.sum_ite_mem, Finset.univ_inter, ← Int.cast_sum,
    Finset.sum_powerset_neg_one_pow_card]
  simp only [Finset.compl_eq_empty_iff]
  split_ifs <;> simp

/-- **Lemma 4.6**, Ryser's formula. -/
theorem ryser (m : ℕ) :
    per m = ∑ S : Finset (Fin m), (-1 : MvPolynomial (Fin m × Fin m) ℝ) ^ (m - S.card) *
      ∏ i : Fin m, ∑ j ∈ S, X (i, j) := by
  classical
  set P : (Fin m → Fin m) → MvPolynomial (Fin m × Fin m) ℝ := fun f => ∏ i, X (i, f i)
  -- expand each product of row sums into a sum over maps `f` with values in `S`
  have hS : ∀ S : Finset (Fin m), (-1 : MvPolynomial (Fin m × Fin m) ℝ) ^ (m - S.card) *
      ∏ i : Fin m, ∑ j ∈ S, X (i, j) =
      ∑ f : Fin m → Fin m, (if Finset.univ.image f ⊆ S then
        (-1 : MvPolynomial (Fin m × Fin m) ℝ) ^ (Fintype.card (Fin m) - S.card) else 0) * P f := by
    intro S
    rw [Finset.prod_univ_sum, Finset.mul_sum, Fintype.card_fin]
    simp_rw [ite_mul, zero_mul]
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext f
    simp [Fintype.mem_piFinset, Finset.image_subset_iff]
  rw [Finset.sum_congr rfl fun S _ => hS S, Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  -- for a fixed map `f`, the alternating sum over `S ⊇ range f` detects bijectivity
  have hc : ∀ f : Fin m → Fin m, (∑ S : Finset (Fin m), if Finset.univ.image f ⊆ S then
      (-1 : MvPolynomial (Fin m × Fin m) ℝ) ^ (Fintype.card (Fin m) - S.card) else 0) =
      if Function.Bijective f then 1 else 0 := by
    intro f
    rw [sum_superset_neg_one_pow]
    refine if_congr ?_ rfl rfl
    rw [← Finite.surjective_iff_bijective]
    simp only [Finset.eq_univ_iff_forall, Finset.mem_image, Finset.mem_univ, true_and,
      Function.Surjective]
  simp_rw [hc, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter, per]
  -- bijective maps are permutations
  exact (Finset.sum_bij (fun p h ↦ Equiv.ofBijective p (Finset.mem_filter.1 h).2)
    (fun _ _ ↦ Finset.mem_univ _) (fun _ _ _ _ h ↦ by injection h)
    (fun b _ ↦ ⟨b, Finset.mem_filter.2 ⟨Finset.mem_univ _, b.bijective⟩,
      DFunLike.coe_injective rfl⟩)
    fun _ _ ↦ rfl).symm

theorem totalDegree_per (m : ℕ) : (per m).totalDegree ≤ m := by
  refine totalDegree_finsetSum_le fun π _ => ?_
  refine (totalDegree_finsetProd _ _).trans ?_
  simp [totalDegree_X]

/-- Negating the first row of `X` negates the permanent. -/
theorem per_negRow (m : ℕ) (i₀ : Fin m) (X : Fin m × Fin m → ℝ) :
    eval (fun p => if p.1 = i₀ then -X p else X p) (per m) = -eval X (per m) := by
  classical
  simp only [per, map_sum, map_prod, eval_X, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun π _ => ?_
  -- exactly one factor of `∏ i, X (i, π i)` lies in row `i₀`
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i₀),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i₀),
    Finset.prod_congr rfl fun i hi => ite_eq_right (Finset.ne_of_mem_erase hi),
    ite_eq_left rfl, neg_mul]

/-- **Corollary 4.7** (tree part). -/
theorem cor_np (hS : SAFacts) (hLB : PermLowerBound) (r : PerRel)
    (hr : r = .eq ∨ r = .le ∨ r = .ge) (t k : ℕ → ℕ)
    (T : ∀ m, Tree ((Fin m × Fin m) ⊕ Unit ⊕ Fin (k m)))
    (hT : ∀ m, (T m).depth ≤ t m) (hdec : ∀ m, ExDecides (T m) (perLang r m)) :
    SuperPolyLB fun m => t m := by
  -- Theorems 4.2 and 4.4 with `n = m²`, `d = m`, `U = ℝ^{m²}`
  obtain ⟨C, hC⟩ : ∃ C : ℕ, ∀ m, 1 ≤ m → BorderLE (per m)
      (C * ((m + 1) ^ 3 * t m + (m + 1) ^ 2 * (min (k m) (2 * t m) + 2) ^ 2 +
        Fintype.card (Fin m × Fin m))) := by
    rcases hr with rfl | rfl | rfl
    · obtain ⟨C, hC⟩ := graph_theorem hS
      exact ⟨C, fun m hm => hC m (t m) (k m) (per m) hm (totalDegree_per m) univ isOpen_univ
        univ_nonempty (T m) (hT m) fun x _ y => hdec m x y⟩
    · obtain ⟨C, hC⟩ := threshold_theorem_le hS
      exact ⟨C, fun m hm => hC m (t m) (k m) (per m) hm (totalDegree_per m) univ isOpen_univ
        univ_nonempty (T m) (hT m) fun x _ y => hdec m x y⟩
    · obtain ⟨C, hC⟩ := threshold_theorem_ge hS
      exact ⟨C, fun m hm => hC m (t m) (k m) (per m) hm (totalDegree_per m) univ isOpen_univ
        univ_nonempty (T m) (hT m) fun x _ y => hdec m x y⟩
  -- the bound is `O(m³ t + m² t²)`, at most `6 C (m+1)³ (t+1)²`
  refine superPoly_of_borderLE hLB t (6 * C) 3 2 ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  refine (hC m hm).mono ?_
  rw [Fintype.card_prod, Fintype.card_fin]
  have hM : 1 ≤ m + 1 := by omega
  have hs : 1 ≤ (t m + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have e1 : (m + 1) ^ 3 * t m ≤ (m + 1) ^ 3 * (t m + 1) ^ 2 := by
    apply Nat.mul_le_mul_left; nlinarith
  have e2 : (m + 1) ^ 2 * (min (k m) (2 * t m) + 2) ^ 2 ≤ 4 * ((m + 1) ^ 3 * (t m + 1) ^ 2) := by
    calc (m + 1) ^ 2 * (min (k m) (2 * t m) + 2) ^ 2 ≤ (m + 1) ^ 2 * (2 * (t m + 1)) ^ 2 := by
          exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
      _ = 4 * ((m + 1) ^ 2 * (t m + 1) ^ 2) := by ring
      _ ≤ 4 * ((m + 1) ^ 3 * (t m + 1) ^ 2) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hM (by norm_num)))
  have e3 : m * m ≤ (m + 1) ^ 3 * (t m + 1) ^ 2 := by
    calc m * m ≤ (m + 1) ^ 3 * 1 := by nlinarith
      _ ≤ (m + 1) ^ 3 * (t m + 1) ^ 2 := Nat.mul_le_mul_left _ hs
  calc C * ((m + 1) ^ 3 * t m + (m + 1) ^ 2 * (min (k m) (2 * t m) + 2) ^ 2 + m * m)
      ≤ C * (6 * ((m + 1) ^ 3 * (t m + 1) ^ 2)) := Nat.mul_le_mul_left _ (by omega)
    _ = 6 * C * (m + 1) ^ 3 * (t m + 1) ^ 2 := by ring

end ClassSep
