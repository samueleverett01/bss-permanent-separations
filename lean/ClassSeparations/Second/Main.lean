import ClassSeparations.Universal.Onesided
import ClassSeparations.Second.Cited
import ClassSeparations.Basic.TreeOps
import ClassSeparations.Basic.Asymptotics
import ClassSeparations.Second.Setup
import ClassSeparations.Second.Conclude

/-!
# An existential and a universal block (§6, Theorem 6.1 and Corollary 6.8)

**Theorem 6.1.**  Let `f ∈ ℝ[X₁, …, Xₙ]` have degree at most `d ≥ 1` and `U ⊆ ℝⁿ` be open and
nonempty.  Suppose that a tree of depth `t` on inputs `(x, y, z, u) ∈ ℝⁿ × ℝ × ℝᵏ × ℝˡ`
satisfies, for all `x ∈ U` and `y ∈ ℝ`,
`(∃ z ∀ u, the tree accepts (x, y, z, u)) ↔ y = f(x)`.
Then the border complexity of `f` is at most a polynomial in `t, k, l, d, n`.

**Corollary 6.8** (tree part).  Trees of depth `t_m` with `k_m` and `l_m` coordinates in `z` and
`u` that decide one of `Y = per_m(X)`, `Y ≤ per_m(X)`, `Y ≥ per_m(X)` with quantifiers
`∃ z ∀ u` have `t_m + k_m + l_m ≥ 2^{Ω((log m)^{4/3})}`.

The proof of Theorem 6.1 uses, in Lemma 6.3 (d), effective quantifier elimination; see
`ClassSeparations.Second.Cited`.
-/

noncomputable section

open MvPolynomial Set Filter

namespace ClassSep

/-- **Theorem 6.1.**  The polynomial bound is `C (t + k + l + d + n + 1)^e` for absolute
constants `C` and `e`. -/
theorem second_level (hS : SAFacts) (hQE : EffectiveQE) :
    ∃ C e : ℕ, ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (d t k l : ℕ) (f : MvPolynomial σ ℝ),
      1 ≤ d → f.totalDegree ≤ d →
      ∀ U : Set (σ → ℝ), IsOpen U → U.Nonempty →
      ∀ T : Tree (σ ⊕ Unit ⊕ Fin k ⊕ Fin l), T.depth ≤ t →
      (∀ x ∈ U, ∀ y : ℝ, (∃ z, ∀ u, T.Accepts (inp4 x y z u)) ↔ y = eval x f) →
      BorderLE f (C * (t + k + l + d + Fintype.card σ + 1) ^ e) := by
  obtain ⟨C₁, e₁, h₁⟩ := sl_setup hS hQE
  obtain ⟨C₂, e₂, h₂⟩ := sl_conclude_proof hS
  refine ⟨C₂ * (6 + 3 * C₁) ^ e₂, max e₁ 1 * e₂, ?_⟩
  intro σ _ _ d t k l f hd hf U hU hUne T hT hdec
  obtain ⟨κ, _, _, M, D, yc, hgood, hκ, hM, hℓ, hN⟩ := h₁ d t k l f hd hf U hU hUne T hT hdec
  refine (h₂ D f yc d hgood hd hf).mono ?_
  set S := t + k + l + d + Fintype.card σ + 1 with hSdef
  have hS1 : 1 ≤ S := by omega
  have hpow : ∀ j, j ≤ max e₁ 1 → S ^ j ≤ S ^ max e₁ 1 := fun j hj =>
    Nat.pow_le_pow_right hS1 hj
  have hS' : S ≤ S ^ max e₁ 1 := by
    calc S = S ^ 1 := (pow_one S).symm
      _ ≤ S ^ max e₁ 1 := hpow 1 (le_max_right _ _)
  have hN' : Nat.log 2 D.N ≤ C₁ * S ^ max e₁ 1 := by
    refine hN.trans (Nat.mul_le_mul_left _ ?_)
    calc (t + Fintype.card σ + k + l + 1) ^ e₁ ≤ S ^ e₁ := Nat.pow_le_pow_left (by omega) _
      _ ≤ S ^ max e₁ 1 := hpow e₁ (le_max_left _ _)
  have h1 : C₁ * (t + 1) ≤ C₁ * S ^ max e₁ 1 := Nat.mul_le_mul_left _ (by omega)
  have hsum : d + Fintype.card κ + M + D.ℓmax + Nat.log 2 D.N + Fintype.card σ + 2 ≤
      (6 + 3 * C₁) * S ^ max e₁ 1 := by
    nlinarith
  calc C₂ * (d + Fintype.card κ + M + D.ℓmax + Nat.log 2 D.N + Fintype.card σ + 2) ^ e₂
      ≤ C₂ * ((6 + 3 * C₁) * S ^ max e₁ 1) ^ e₂ :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsum _)
    _ = C₂ * (6 + 3 * C₁) ^ e₂ * S ^ (max e₁ 1 * e₂) := by rw [mul_pow, ← pow_mul]; ring

/-- A tree on inputs `(X, Y, z, u)` decides `L` with quantifiers `∃ z ∀ u`. -/
def ExAllDecides {α γ δ : Type} (T : Tree (α ⊕ Unit ⊕ γ ⊕ δ)) (L : (α → ℝ) → ℝ → Prop) :
    Prop :=
  ∀ X Y, (∃ z, ∀ u, T.Accepts (inp4 X Y z u)) ↔ L X Y

/-- The conjunction tree of the proof of Corollary 6.8: on inputs `(X, Y, z, u)` with
`z = (z₁, z₂)` and `u = (u₁, u₂)`, it accepts when `T` accepts `(X, Y, z₁, u₁)` and
`(X', -Y, z₂, u₂)`, where `X'` is `X` with row `i₀` negated. -/
def conjTree {m k l : ℕ} (i₀ : Fin m) (T : Tree ((Fin m × Fin m) ⊕ Unit ⊕ Fin k ⊕ Fin l)) :
    Tree ((Fin m × Fin m) ⊕ Unit ⊕ Fin (k + k) ⊕ Fin (l + l)) :=
  (T.renameCert (Sum.map (Fin.castAdd k) (Fin.castAdd l))).andThen
    (T.negRowY i₀ (Sum.map (Fin.natAdd k) (Fin.natAdd l))) 0

theorem conjTree_depth {m k l : ℕ} (i₀ : Fin m)
    (T : Tree ((Fin m × Fin m) ⊕ Unit ⊕ Fin k ⊕ Fin l)) :
    (conjTree i₀ T).depth ≤ T.depth + (T.depth + (m + 1)) := by
  have h := Tree.depth_andThen_le (T.renameCert (Sum.map (Fin.castAdd k) (Fin.castAdd l)))
    (T.negRowY i₀ (Sum.map (Fin.natAdd k) (Fin.natAdd l))) 0
  simpa [conjTree] using h

theorem conjTree_accepts {m k l : ℕ} (i₀ : Fin m)
    (T : Tree ((Fin m × Fin m) ⊕ Unit ⊕ Fin k ⊕ Fin l)) (X : Fin m × Fin m → ℝ) (Y : ℝ)
    (z : Fin (k + k) → ℝ) (u : Fin (l + l) → ℝ) :
    (conjTree i₀ T).Accepts (inp4 X Y z u) ↔
      T.Accepts (inp4 X Y (z ∘ Fin.castAdd k) (u ∘ Fin.castAdd l)) ∧
        T.Accepts (inp4 (negRow i₀ X) (-Y) (z ∘ Fin.natAdd k) (u ∘ Fin.natAdd l)) := by
  rw [conjTree, Tree.accepts_andThen, Tree.Accepts, Tree.Accepts,
    show inp4 X Y z u = inp3 X Y (Sum.elim z u) from rfl, Tree.run_renameCert,
    Tree.run_negRowY, Sum.elim_comp_map, Sum.elim_comp_map]
  rfl

/-- `∃ z ∀ u` acceptance by the conjunction tree splits into the two `∃ ∀` conditions. -/
theorem conjTree_exAll {m k l : ℕ} (i₀ : Fin m)
    (T : Tree ((Fin m × Fin m) ⊕ Unit ⊕ Fin k ⊕ Fin l)) (X : Fin m × Fin m → ℝ) (Y : ℝ) :
    (∃ z, ∀ u, (conjTree i₀ T).Accepts (inp4 X Y z u)) ↔
      (∃ z, ∀ u, T.Accepts (inp4 X Y z u)) ∧
        (∃ z, ∀ u, T.Accepts (inp4 (negRow i₀ X) (-Y) z u)) := by
  simp only [conjTree_accepts]
  exact exists_forall_append_iff (fun z u => T.Accepts (inp4 X Y z u))
    (fun z u => T.Accepts (inp4 (negRow i₀ X) (-Y) z u))

/-- **Corollary 6.8** (tree part). -/
theorem cor_second (hS : SAFacts) (hQE : EffectiveQE) (hLB : PermLowerBound) (r : PerRel)
    (hr : r = .eq ∨ r = .le ∨ r = .ge) (t k l : ℕ → ℕ)
    (T : ∀ m, Tree ((Fin m × Fin m) ⊕ Unit ⊕ Fin (k m) ⊕ Fin (l m)))
    (hT : ∀ m, (T m).depth ≤ t m) (hdec : ∀ m, ExAllDecides (T m) (perLang r m)) :
    SuperPolyLB fun m => (t m + k m + l m : ℕ) := by
  obtain ⟨C, e, hC⟩ := second_level hS hQE
  refine superPoly_of_borderLE hLB (fun m => t m + k m + l m) (C * 2 ^ e) (2 * e) e ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  let i₀ : Fin m := ⟨0, hm⟩
  have hneg : ∀ x, eval (negRow i₀ x) (per m) = -eval x (per m) := fun x => per_negRow m i₀ x
  -- a tree deciding the graph of `per_m` with `∃ z ∀ u`; for the thresholds it is the
  -- conjunction tree, of depth `≤ 2t + m + 1` and with blocks of lengths `2k`, `2l`
  obtain ⟨t', k', l', T', hdepth, hsize, hT'⟩ : ∃ (t' k' l' : ℕ)
      (T' : Tree ((Fin m × Fin m) ⊕ Unit ⊕ Fin k' ⊕ Fin l')),
      T'.depth ≤ t' ∧ t' + k' + l' ≤ 2 * (t m + k m + l m) + (m + 1) ∧
      ∀ x y, (∃ z, ∀ u, T'.Accepts (inp4 x y z u)) ↔ y = eval x (per m) := by
    rcases hr with rfl | rfl | rfl
    · exact ⟨t m, k m, l m, T m, hT m, by omega, hdec m⟩
    · refine ⟨t m + (t m + (m + 1)), k m + k m, l m + l m, conjTree i₀ (T m),
        (conjTree_depth i₀ (T m)).trans (by have := hT m; omega), by omega, fun x y => ?_⟩
      rw [conjTree_exAll, hdec m, hdec m]
      show y ≤ eval x (per m) ∧ -y ≤ eval (negRow i₀ x) (per m) ↔ y = eval x (per m)
      rw [hneg]
      constructor
      · rintro ⟨h₁, h₂⟩; linarith
      · rintro rfl; exact ⟨le_rfl, le_rfl⟩
    · refine ⟨t m + (t m + (m + 1)), k m + k m, l m + l m, conjTree i₀ (T m),
        (conjTree_depth i₀ (T m)).trans (by have := hT m; omega), by omega, fun x y => ?_⟩
      rw [conjTree_exAll, hdec m, hdec m]
      show eval x (per m) ≤ y ∧ eval (negRow i₀ x) (per m) ≤ -y ↔ y = eval x (per m)
      rw [hneg]
      constructor
      · rintro ⟨h₁, h₂⟩; linarith
      · rintro rfl; exact ⟨le_rfl, le_rfl⟩
  -- Theorem 6.1 with `n = m²`, `d = m`, `U = ℝ^{m²}`
  refine (hC m t' k' l' (per m) hm (totalDegree_per m) univ isOpen_univ univ_nonempty T'
    hdepth fun x _ y => hT' x y).mono ?_
  rw [Fintype.card_prod, Fintype.card_fin]
  have hb : t' + k' + l' + m + m * m + 1 ≤ 2 * (m + 1) ^ 2 * (t m + k m + l m + 1) := by
    nlinarith
  calc C * (t' + k' + l' + m + m * m + 1) ^ e
      ≤ C * (2 * (m + 1) ^ 2 * (t m + k m + l m + 1)) ^ e :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb e)
    _ = C * 2 ^ e * (m + 1) ^ (2 * e) * (t m + k m + l m + 1) ^ e := by
        rw [mul_pow, mul_pow, ← pow_mul]; ring

end ClassSep
