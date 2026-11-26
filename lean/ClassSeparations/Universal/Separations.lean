import ClassSeparations.Universal.Complex
import ClassSeparations.Basic.TreeOps
import ClassSeparations.Basic.Asymptotics

/-!
# The separations (§5.7, Corollary 5.5, tree part)

**Corollary 5.5.**  Suppose that for every `m` a tree of depth `t_m` decides one of the
languages `{Y = per_m(X)}`, `{Y ≤ per_m(X)}`, `{Y ≥ per_m(X)}` in the universal sense, or one of
`{Y < per_m(X)}`, `{Y > per_m(X)}` in the existential sense, or that a complex tree of depth
`t_m` decides `{Y = per_m(X)} ⊆ ℂ^{m²+1}` in the existential or in the universal sense.  Then
`t_m ≥ 2^{Ω((log m)^{4/3})}`.

The class-level consequences (a)–(c) are in `ClassSeparations.Machines.Separations`.
-/

noncomputable section

open MvPolynomial Set Filter

namespace ClassSep

/-- An outcome is rejecting exactly when it is not acceptance. -/
theorem mem_rejecting_iff (o : Option Bool) : o ∈ rejecting ↔ o ≠ some true := by
  rcases o with _ | _ | _ <;> simp [rejecting]

/-- Theorem 5.1 with `U = ℝⁿ`, (a) with the rejecting outcomes marked, for a tree that accepts
`(x, f(x), z)` for every `z` and rejects some `(x, y, z)` for every `y > f(x)`, and (b) with the
accepting outcomes marked, for a tree that accepts no `(x, f(x), z)` and some `(x, y, z)` for
every `y > f(x)`. -/
theorem onesided_cases (hS : SAFacts) :
    ∃ C : ℕ, ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (d t k : ℕ) (f : MvPolynomial σ ℝ),
      1 ≤ d → f.totalDegree ≤ d → ∀ T : Tree (σ ⊕ Unit ⊕ Fin k), T.depth ≤ t →
      ((∀ x z, T.Accepts (inp3 x (eval x f) z)) ∧
          ∀ x y, eval x f < y → ∃ z, ¬ T.Accepts (inp3 x y z)) ∨
        ((∀ x z, ¬ T.Accepts (inp3 x (eval x f) z)) ∧
          ∀ x y, eval x f < y → ∃ z, T.Accepts (inp3 x y z)) →
      BorderLE f (C * (d + 1) ^ 6 * ((t + 1) ^ 2 + Fintype.card σ)) := by
  obtain ⟨C, hC⟩ := onesided hS
  refine ⟨C, fun d t k f hd hf T hT h => ?_⟩
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · refine hC d t k f hd hf univ isOpen_univ univ_nonempty T rejecting hT
      (fun x _ z => (mem_rejecting_iff _).not.2 (not_not.2 (h₁ x z)))
      fun x _ => ⟨1, one_pos, fun y hy _ => ?_⟩
    obtain ⟨z, hz⟩ := h₂ x y hy
    exact ⟨z, (mem_rejecting_iff _).2 hz⟩
  · exact hC d t k f hd hf univ isOpen_univ univ_nonempty T {some true} hT
      (fun x _ z => h₁ x z) fun x _ => ⟨1, one_pos, fun y hy _ => h₂ x y hy⟩

/-- The arithmetic of Corollary 5.5: `C (m+1)⁶ ((t+m+2)² + m²) ≤ 5 C (m+1)⁸ (t+1)²`. -/
theorem conp_arith (C m t : ℕ) :
    C * (m + 1) ^ 6 * ((t + (m + 1) + 1) ^ 2 + m * m) ≤ 5 * C * (m + 1) ^ 8 * (t + 1) ^ 2 := by
  have h1 : t + (m + 1) + 1 ≤ 2 * ((m + 1) * (t + 1)) := by nlinarith
  have h2 : m * m ≤ (m + 1) ^ 2 * (t + 1) ^ 2 :=
    calc m * m ≤ (m + 1) ^ 2 * 1 := by nlinarith
      _ ≤ (m + 1) ^ 2 * (t + 1) ^ 2 := Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ (by omega))
  calc C * (m + 1) ^ 6 * ((t + (m + 1) + 1) ^ 2 + m * m)
      ≤ C * (m + 1) ^ 6 * ((2 * ((m + 1) * (t + 1))) ^ 2 + (m + 1) ^ 2 * (t + 1) ^ 2) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.pow_le_pow_left h1 2) h2)
    _ = 5 * C * (m + 1) ^ 8 * (t + 1) ^ 2 := by ring

/-- **Corollary 5.5**, real trees in the universal sense. -/
theorem cor_conp_universal (hS : SAFacts) (hLB : PermLowerBound) (r : PerRel)
    (hr : r = .eq ∨ r = .le ∨ r = .ge) (t k : ℕ → ℕ)
    (T : ∀ m, Tree ((Fin m × Fin m) ⊕ Unit ⊕ Fin (k m)))
    (hT : ∀ m, (T m).depth ≤ t m) (hdec : ∀ m, AllDecides (T m) (perLang r m)) :
    SuperPolyLB fun m => t m := by
  obtain ⟨C, hC⟩ := onesided_cases hS
  refine superPoly_of_borderLE hLB t (5 * C) 8 2 ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  let i₀ : Fin m := ⟨0, hm⟩
  have hneg : ∀ x, eval (negRow i₀ x) (per m) = -eval x (per m) := fun x => per_negRow m i₀ x
  -- a tree of depth `≤ t + m + 1` that verifies `y ≤ per_m(x)` or `y = per_m(x)` universally;
  -- for `Y ≥ per_m(X)` we pass to `(X', -Y)`, which verifies `Y ≤ per_m(X)`
  obtain ⟨T', hdepth, h₁, h₂⟩ : ∃ T' : Tree ((Fin m × Fin m) ⊕ Unit ⊕ Fin (k m)),
      T'.depth ≤ t m + (m + 1) ∧ (∀ x z, T'.Accepts (inp3 x (eval x (per m)) z)) ∧
      ∀ x y, eval x (per m) < y → ∃ z, ¬ T'.Accepts (inp3 x y z) := by
    rcases hr with rfl | rfl | rfl
    · refine ⟨T m, (hT m).trans (by omega), fun x => (hdec m x _).2 rfl, fun x y hy => ?_⟩
      by_contra h
      exact hy.ne' ((hdec m x y).1 fun z => not_not.1 fun hz => h ⟨z, hz⟩)
    · refine ⟨T m, (hT m).trans (by omega), fun x => (hdec m x _).2 le_rfl, fun x y hy => ?_⟩
      by_contra h
      exact (not_le.2 hy) ((hdec m x y).1 fun z => not_not.1 fun hz => h ⟨z, hz⟩)
    · refine ⟨(T m).negRowY i₀ id, by simpa using hT m, fun x z => ?_, fun x y hy => ?_⟩
      · rw [Tree.Accepts, Tree.run_negRowY]
        refine (hdec m _ _).2 ?_ _
        show eval (negRow i₀ x) (per m) ≤ -eval x (per m)
        rw [hneg]
      · by_contra h
        have h' : ∀ z, (T m).Accepts (inp3 (negRow i₀ x) (-y) z) := fun z => by
          have hz := not_not.1 fun hz => h ⟨z, hz⟩
          rwa [Tree.Accepts, Tree.run_negRowY] at hz
        have h'' : eval (negRow i₀ x) (per m) ≤ -y := (hdec m _ _).1 h'
        rw [hneg] at h''
        linarith
  refine (hC m (t m + (m + 1)) (k m) (per m) hm (totalDegree_per m) T' hdepth
    (Or.inl ⟨h₁, h₂⟩)).mono ?_
  rw [Fintype.card_prod, Fintype.card_fin]
  exact conp_arith C m (t m)

/-- **Corollary 5.5**, real trees in the existential sense for the strict thresholds. -/
theorem cor_conp_strict (hS : SAFacts) (hLB : PermLowerBound) (r : PerRel)
    (hr : r = .lt ∨ r = .gt) (t k : ℕ → ℕ)
    (T : ∀ m, Tree ((Fin m × Fin m) ⊕ Unit ⊕ Fin (k m)))
    (hT : ∀ m, (T m).depth ≤ t m) (hdec : ∀ m, ExDecides (T m) (perLang r m)) :
    SuperPolyLB fun m => t m := by
  obtain ⟨C, hC⟩ := onesided_cases hS
  refine superPoly_of_borderLE hLB t (5 * C) 8 2 ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  let i₀ : Fin m := ⟨0, hm⟩
  have hneg : ∀ x, eval (negRow i₀ x) (per m) = -eval x (per m) := fun x => per_negRow m i₀ x
  -- a tree of depth `≤ t + m + 1` that verifies `y > per_m(x)` existentially;
  -- for `Y < per_m(X)` we pass to `(X', -Y)`
  obtain ⟨T', hdepth, h₁, h₂⟩ : ∃ T' : Tree ((Fin m × Fin m) ⊕ Unit ⊕ Fin (k m)),
      T'.depth ≤ t m + (m + 1) ∧ (∀ x z, ¬ T'.Accepts (inp3 x (eval x (per m)) z)) ∧
      ∀ x y, eval x (per m) < y → ∃ z, T'.Accepts (inp3 x y z) := by
    rcases hr with rfl | rfl
    · refine ⟨(T m).negRowY i₀ id, by simpa using hT m, fun x z hz => ?_, fun x y hy => ?_⟩
      · rw [Tree.Accepts, Tree.run_negRowY] at hz
        have h : -eval x (per m) < eval (negRow i₀ x) (per m) := (hdec m _ _).1 ⟨_, hz⟩
        rw [hneg] at h
        exact lt_irrefl _ h
      · have h : -y < eval (negRow i₀ x) (per m) := by rw [hneg]; linarith
        obtain ⟨z, hz⟩ := (hdec m _ _).2 h
        exact ⟨z, by rw [Tree.Accepts, Tree.run_negRowY]; exact hz⟩
    · exact ⟨T m, (hT m).trans (by omega),
        fun x z hz => lt_irrefl _ ((hdec m x _).1 ⟨z, hz⟩), fun x y hy => (hdec m x y).2 hy⟩
  refine (hC m (t m + (m + 1)) (k m) (per m) hm (totalDegree_per m) T' hdepth
    (Or.inr ⟨h₁, h₂⟩)).mono ?_
  rw [Fintype.card_prod, Fintype.card_fin]
  exact conp_arith C m (t m)

/-- The complex permanent language `{(X, Y) ∈ ℂ^{m²} × ℂ : Y = per_m(X)}`. -/
def cperLang (m : ℕ) (X : Fin m × Fin m → ℂ) (Y : ℂ) : Prop :=
  Y = eval X (map (algebraMap ℝ ℂ) (per m))

/-- **Corollary 5.5**, complex trees in the existential or universal sense. -/
theorem cor_conp_complex (hS : SAFacts) (hLB : PermLowerBound) (t k : ℕ → ℕ)
    (T : ∀ m, CTree ((Fin m × Fin m) ⊕ Unit ⊕ Fin (k m)))
    (hT : ∀ m, (T m).depth ≤ t m)
    (hdec : ∀ m, (∀ X Y, (∃ z, (T m).Accepts (cinp3 X Y z)) ↔ cperLang m X Y) ∨
      (∀ X Y, (∀ z, (T m).Accepts (cinp3 X Y z)) ↔ cperLang m X Y)) :
    SuperPolyLB fun m => t m := by
  obtain ⟨C, hC⟩ := complex_field hS
  refine superPoly_of_borderLE hLB t (5 * C) 8 2 ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  refine (hC m (t m) (k m) (per m) hm (totalDegree_per m) (T m) (hT m) (hdec m)).mono ?_
  rw [Fintype.card_prod, Fintype.card_fin]
  refine le_trans ?_ (conp_arith C m (t m))
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.pow_le_pow_left (by omega) 2) _)

end ClassSep
