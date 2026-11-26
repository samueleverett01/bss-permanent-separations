import ClassSeparations.Second.Flatten
import ClassSeparations.Basic.Cells

/-!
# Lemma 6.3 (d): an effective bound for `N`

The function `g(τ) = sup {v(x, w) : x ∈ K, w ∈ B̄, |w - φ(x)| ≤ τ}` of Lemma 6.3 (c) has a graph
defined by the explicit first-order formula `fGraph D` in the two free variables `(τ, y)`:
`y` is the least upper bound of the set of `s` such that

`∃ x w w' ν. x ∈ K ∧ w ∈ B̄ ∧ w' ∈ B̄ ∧ |w - w'|² ≤ τ² ∧ s ≥ 0 ∧ (∃ b, Q_b(x, w, ν, s) = 0) ∧`
`  ∀ ν' s'. s' > 0 → ¬ ∃ b, Q_b(x, w', ν', s') = 0`

(the last line says `w' = φ(x)`, by Lemma 6.2).  Its atoms are the `Q_b` (at most `B` of them,
of degree at most `2^ℓ`) and a few quadratic conditions, it has `O(n + |κ| + M)` quantified
variables and at most `4` quantifier blocks.  Effective quantifier elimination
(`exponent_bound`) then gives `g(τ) ≤ L τ^{1/m}` with `log m` polynomial in
`n, |κ|, M, ℓ, log B`, and Lemma 6.3 (c) gives `N = 2m`.
-/

noncomputable section

open MvPolynomial Set Filter Topology

namespace ClassSep

namespace SetupAux

variable {σ κ : Type} [Fintype σ] [Fintype κ] {M : ℕ}

/-! ### The formula -/

/-- The variables `(x, w, w', ν)` of the existential block. -/
abbrev Vb (σ κ : Type) (M : ℕ) : Type := σ ⊕ κ ⊕ κ ⊕ Fin M

section Defs

variable {β : Type}

/-- The coordinate `xᵢ` of the block. -/
def vx (i : σ) : β ⊕ Vb σ κ M := .inr (.inl i)
/-- The coordinate `w_c` of the block. -/
def vw (c : κ) : β ⊕ Vb σ κ M := .inr (.inr (.inl c))
/-- The coordinate `w'_c` of the block. -/
def vw' (c : κ) : β ⊕ Vb σ κ M := .inr (.inr (.inr (.inl c)))
/-- The coordinate `νⱼ` of the block. -/
def vν (j : Fin M) : β ⊕ Vb σ κ M := .inr (.inr (.inr (.inr j)))

/-- The variables of `Q_b` at `(x, w, ν, s)`, with `s` free. -/
def e1 (vs : β) : σ ⊕ κ ⊕ Option (Fin M) → β ⊕ Vb σ κ M :=
  Sum.elim vx (Sum.elim vw fun o => o.elim (.inl vs) vν)

/-- The variables of `Q_b` at `(x, w', ν', s')`, with `(ν', s')` from the inner block. -/
def e2 : σ ⊕ κ ⊕ Option (Fin M) → (β ⊕ Vb σ κ M) ⊕ (Fin M ⊕ Unit) :=
  Sum.elim (fun i => .inl (vx i))
    (Sum.elim (fun c => .inl (vw' c)) fun o => o.elim (.inr (.inr ())) fun j => .inr (.inl j))

variable (D : SLData σ κ M)

/-- Some `Q_b` vanishes. -/
def fQsol {γ : Type} (e : σ ⊕ κ ⊕ Option (Fin M) → γ) : Fml γ :=
  forF (Fin D.B) fun b => .zero (rename e (D.Q b))

/-- `x ∈ K`. -/
def fK : Fml (β ⊕ Vb σ κ M) :=
  fandF σ fun i => fnonneg (C (D.ρ ^ 2) - (X (vx i) - C (D.x₀ i)) ^ 2)

/-- `w ∈ B̄`. -/
def fB {γ : Type} (ew : κ → γ) : Fml γ :=
  fnonneg (C (D.r₀ ^ 2) - ∑ c, (X (ew c) - C (D.w₀ c)) ^ 2)

/-- `|w - w'|² ≤ τ²`. -/
def fD {γ : Type} (vτ : γ) (ew ew' : κ → γ) : Fml γ :=
  fnonneg (X vτ ^ 2 - ∑ c, (X (ew c) - X (ew' c)) ^ 2)

/-- `w' = φ(x)`, expressed as: no solution with `s' > 0` at `(x, w')`. -/
def fΓ : Fml (β ⊕ Vb σ κ M) :=
  fallT (Fin M ⊕ Unit) (fimp (.pos (X (.inr (.inr ())))) (.not (fQsol D e2)))

/-- The body of `inS`. -/
def inSbody (vτ vs : β) : Fml (β ⊕ Vb σ κ M) :=
  fandL [fK D, fB D vw, fB D vw', fD (.inl vτ) vw vw', fnonneg (X (.inl vs)),
    fQsol D (e1 vs), fΓ D]

/-- `s ∈ gset' τ`, with free variables `τ = vτ` and `s = vs`. -/
def inS (vτ vs : β) : Fml β := fexT (Vb σ κ M) (inSbody D vτ vs)

end Defs

variable (D : SLData σ κ M)

/-- The upper bound condition: `∀ s, ¬ (s ∈ S_τ ∧ y < s)`. -/
def fUB : Fml (Fin 2) :=
  fallT Unit (.not (.and (inS D (.inl 0) (.inr ())) (.pos (X (.inr ()) - X (.inl 1)))))

/-- The approximation condition: `∀ y', y' < y → ∃ s, s ∈ S_τ ∧ y' < s`. -/
def fAP : Fml (Fin 2) :=
  fallT Unit (fimp (.pos (X (.inl 1) - X (.inr ())))
    (fexT Unit (.and (inS D (.inl (.inl 0)) (.inr ())) (.pos (X (.inr ()) - X (.inl (.inr ())))))))

/-- **The formula for the graph of `g`** (Lemma 6.3 (d)). -/
def fGraph : Fml (Fin 2) := .and (fUB D) (fAP D)

/-! ### Semantics -/

/-- The set of `s` defined by `inS`. -/
def gset' (τ : ℝ) : Set ℝ :=
  {s | ∃ x w w' ν, x ∈ D.K ∧ w ∈ D.Bbar ∧ w' ∈ D.Bbar ∧ sqDist w w' ≤ τ ^ 2 ∧ 0 ≤ s ∧
    (∃ b, eval (SLData.pt x w ν s) (D.Q b) = 0) ∧
    ∀ ν' s', 0 < s' → ¬ ∃ b, eval (SLData.pt x w' ν' s') (D.Q b) = 0}

section Sem

variable {β : Type}

theorem holds_fQsol {γ : Type} (e : σ ⊕ κ ⊕ Option (Fin M) → γ) (v : γ → ℝ) :
    (fQsol D e).Holds v ↔ ∃ b, eval (v ∘ e) (D.Q b) = 0 := by
  simp [fQsol, Fml.Holds, eval_rename]

/-- The point of the block. -/
def blk (x : σ → ℝ) (w w' : κ → ℝ) (ν : Fin M → ℝ) : Vb σ κ M → ℝ :=
  Sum.elim x (Sum.elim w (Sum.elim w' ν))

omit [Fintype σ] [Fintype κ] in
theorem comp_e1 (v : β → ℝ) (vs : β) (x : σ → ℝ) (w w' : κ → ℝ) (ν : Fin M → ℝ) :
    Sum.elim v (blk x w w' ν) ∘ e1 vs = SLData.pt x w ν (v vs) := by
  funext a
  rcases a with i | c | _ | j <;> rfl

omit [Fintype σ] [Fintype κ] in
theorem comp_e2 (v : β → ℝ) (x : σ → ℝ) (w w' : κ → ℝ) (ν : Fin M → ℝ) (ν' : Fin M → ℝ)
    (s' : ℝ) : Sum.elim (Sum.elim v (blk x w w' ν)) (Sum.elim ν' fun _ => s') ∘ e2 =
      SLData.pt x w' ν' s' := by
  funext a
  rcases a with i | c | _ | j <;> rfl

theorem mem_K_iff (hρ : 0 ≤ D.ρ) (x : σ → ℝ) :
    x ∈ D.K ↔ ∀ i, 0 ≤ D.ρ ^ 2 - (x i - D.x₀ i) ^ 2 := by
  show x ∈ Metric.closedBall D.x₀ D.ρ ↔ _
  rw [Metric.mem_closedBall, dist_pi_le_iff hρ]
  refine forall_congr' fun i => ?_
  rw [Real.dist_eq, sub_nonneg, ← sq_abs (x i - D.x₀ i)]
  exact (sq_le_sq₀ (abs_nonneg _) hρ).symm

theorem holds_inSbody (hρ : 0 ≤ D.ρ) (vτ vs : β) (v : β → ℝ) (x : σ → ℝ) (w w' : κ → ℝ)
    (ν : Fin M → ℝ) :
    (inSbody D vτ vs).Holds (Sum.elim v (blk x w w' ν)) ↔
      x ∈ D.K ∧ w ∈ D.Bbar ∧ w' ∈ D.Bbar ∧ sqDist w w' ≤ v vτ ^ 2 ∧ 0 ≤ v vs ∧
      (∃ b, eval (SLData.pt x w ν (v vs)) (D.Q b) = 0) ∧
      ∀ ν' s', 0 < s' → ¬ ∃ b, eval (SLData.pt x w' ν' s') (D.Q b) = 0 := by
  simp only [inSbody, holds_fandL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq]
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_
    (and_congr ?_ ?_)))))
  · rw [mem_K_iff D hρ]
    simp [fK, vx, blk]
  · simp [fB, vw, blk, SLData.Bbar, sqDist]
  · simp [fB, vw', blk, SLData.Bbar, sqDist]
  · simp [fD, vw, vw', blk, sqDist]
  · simp
  · rw [holds_fQsol, comp_e1]
  · simp only [fΓ, holds_fallT, holds_fimp, Fml.Holds, holds_fQsol, eval_X]
    constructor
    · intro h ν' s' hs'
      have := h (Sum.elim ν' fun _ => s')
      rw [comp_e2] at this
      exact this hs'
    · intro h z hz
      have hz' : z = Sum.elim (z ∘ Sum.inl) fun _ => z (.inr ()) := by
        funext a; rcases a with a | ⟨⟩ <;> rfl
      rw [hz', comp_e2]
      exact h _ _ hz

omit [Fintype σ] [Fintype κ] in
theorem blk_surj (z : Vb σ κ M → ℝ) :
    z = blk (z ∘ .inl) (z ∘ .inr ∘ .inl) (z ∘ .inr ∘ .inr ∘ .inl) (z ∘ .inr ∘ .inr ∘ .inr) := by
  funext a
  rcases a with a | a | a | a <;> rfl

theorem holds_inS (hρ : 0 ≤ D.ρ) (vτ vs : β) (v : β → ℝ) :
    (inS D vτ vs).Holds v ↔ v vs ∈ gset' D (v vτ) := by
  rw [inS, holds_fexT]
  constructor
  · rintro ⟨z, hz⟩
    rw [blk_surj z, holds_inSbody D hρ] at hz
    exact ⟨_, _, _, _, hz⟩
  · rintro ⟨x, w, w', ν, h⟩
    exact ⟨blk x w w' ν, (holds_inSbody D hρ vτ vs v x w w' ν).2 h⟩

theorem holds_fGraph (hρ : 0 ≤ D.ρ) (τ y : ℝ) :
    (fGraph D).Holds ![τ, y] ↔
      (∀ s ∈ gset' D τ, s ≤ y) ∧ ∀ y' < y, ∃ s ∈ gset' D τ, y' < s := by
  simp only [fGraph, fUB, fAP, Fml.Holds, holds_fallT, holds_fimp, holds_fexT, holds_inS D hρ,
    eval_sub, eval_X, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
    sub_pos, not_and, not_lt]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun s hs => h1 (fun _ => s) hs, fun y' hy' => ?_⟩
    obtain ⟨z, hz1, hz2⟩ := h2 (fun _ => y') hy'
    exact ⟨_, hz1, hz2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun z hz => h1 _ hz, fun z hz => ?_⟩
    obtain ⟨s, hs1, hs2⟩ := h2 _ hz
    exact ⟨fun _ => s, hs1, hs2⟩

end Sem

variable {D}

theorem Pre.gset'_eq (hD : Pre D) (τ : ℝ) : gset' D τ = gset D τ := by
  ext s
  constructor
  · rintro ⟨x, w, w', ν, hx, hw, hw', hd, hs, ⟨b, hb⟩, hΓ⟩
    have hw'φ : w' = D.φ x := by
      by_contra hne
      obtain ⟨b', ν', s', hs', h'⟩ := (hD.rej_iff x hx w' hw').2 hne
      exact hΓ ν' s' hs' ⟨b', h'⟩
    exact ⟨x, w, ν, ⟨hx, hw, hs, b, hb⟩, hw'φ ▸ hd⟩
  · rintro ⟨x, w, ν, ⟨hx, hw, hs, b, hb⟩, hd⟩
    refine ⟨x, w, D.φ x, ν, hx, hw, hD.φ_mem hx, hd, hs, ⟨b, hb⟩, ?_⟩
    rintro ν' s' hs' ⟨b', h'⟩
    exact (hD.rej_iff x hx _ (hD.φ_mem hx)).1 ⟨b', ν', s', hs', h'⟩ rfl

/-- The formula `fGraph D` defines the graph of `g`. -/
theorem Pre.graph_iff [Nonempty κ] (hD : Pre D) (τ y : ℝ) :
    (fGraph D).Holds ![τ, y] ↔ y = gfun D τ := by
  rw [holds_fGraph D hD.ρ_pos.le, hD.gset'_eq]
  have hne := hD.gset_nonempty τ
  have hbdd := hD.bddAbove_gset τ
  have hlub := isLUB_csSup hne hbdd
  constructor
  · rintro ⟨h1, h2⟩
    have : IsLUB (gset D τ) y := by
      refine ⟨h1, fun b hb => ?_⟩
      by_contra hlt
      obtain ⟨s, hs, hbs⟩ := h2 b (lt_of_not_ge hlt)
      exact absurd (hb hs) (not_le.2 hbs)
    exact this.unique hlub
  · rintro rfl
    refine ⟨fun s hs => hlub.1 hs, fun y' hy' => ?_⟩
    by_contra hcon
    push Not at hcon
    exact absurd (hlub.2 hcon) (not_le.2 hy')

/-! ### Complexity of the formula -/

section Measures

variable (D) {β : Type}

theorem totalDegree_sq_sub_le {γ : Type} (p q : MvPolynomial γ ℝ) (hp : p.totalDegree ≤ 1)
    (hq : q.totalDegree ≤ 1) : ((p - q) ^ 2).totalDegree ≤ 2 := by
  refine (totalDegree_pow _ 2).trans ?_
  have := (totalDegree_sub p q).trans (max_le hp hq)
  omega

theorem totalDegree_X_le {γ : Type} (a : γ) : (X a : MvPolynomial γ ℝ).totalDegree ≤ 1 := by
  rw [totalDegree_X]

theorem totalDegree_C_le {γ : Type} (c : ℝ) : (C c : MvPolynomial γ ℝ).totalDegree ≤ 1 := by
  rw [totalDegree_C]; omega

theorem totalDegree_C_sub_sum_le {γ : Type} (c : ℝ) (F : κ → MvPolynomial γ ℝ)
    (hF : ∀ i, (F i).totalDegree ≤ 2) : (C c - ∑ i, F i).totalDegree ≤ 2 := by
  refine (totalDegree_sub _ _).trans (max_le (by rw [totalDegree_C]; omega) ?_)
  exact (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ => hF i)

theorem size_fQsol {γ : Type} (e : σ ⊕ κ ⊕ Option (Fin M) → γ) :
    (fQsol D e).size ≤ D.B + 1 := by
  have := size_forF_le (ι := Fin D.B) (fun b => (Fml.zero (rename e (D.Q b)) : Fml γ)) (s := 1)
    fun _ => le_rfl
  simpa [fQsol] using this

theorem numBound_fQsol {γ : Type} (e : σ ⊕ κ ⊕ Option (Fin M) → γ) :
    (fQsol D e).numBound = 0 := by
  have := numBound_forF_le (ι := Fin D.B) (fun b => (Fml.zero (rename e (D.Q b)) : Fml γ))
    (s := 0) fun _ => le_rfl
  simp only [mul_zero, nonpos_iff_eq_zero] at this
  exact this

theorem maxDeg_fQsol {γ : Type} (e : σ ⊕ κ ⊕ Option (Fin M) → γ) {d : ℕ}
    (hd : ∀ b, (D.Q b).totalDegree ≤ d) : (fQsol D e).maxDeg ≤ d :=
  maxDeg_forF_le _ fun b => (totalDegree_rename_le e _).trans (hd b)

theorem bb_fQsol {γ : Type} (e : σ ⊕ κ ⊕ Option (Fin M) → γ) (a b : ℕ) : BB (fQsol D e) a b :=
  BB.forF fun _ => BB.zero _ _ _

theorem size_inS (vτ vs : β) :
    (inS D vτ vs).size ≤ 2 * Fintype.card σ + 2 * D.B + 13 := by
  rw [inS, size_fexT, inSbody, size_fandL]
  have hK : (fK (β := β) D).size ≤ Fintype.card σ * 2 + 1 :=
    size_fandF_le _ fun _ => le_rfl
  have hΓ : (fΓ (β := β) D).size ≤ D.B + 2 := by
    rw [fΓ, size_fallT, size_fimp]
    have := size_fQsol D (e2 (β := β))
    simp only [Fml.size]
    omega
  have h1 := size_fQsol D (e1 (β := β) vs)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fB, fD, size_fnonneg]
  omega

theorem numBound_inS (vτ vs : β) :
    (inS D vτ vs).numBound = Fintype.card σ + 2 * Fintype.card κ + 2 * M + 1 := by
  rw [inS, numBound_fexT, inSbody, numBound_fandL]
  have hK : (fK (β := β) D).numBound = 0 := by
    have := numBound_fandF_le (α := β ⊕ Vb σ κ M) (ι := σ)
      (fun i => fnonneg (C (D.ρ ^ 2) - (X (vx i) - C (D.x₀ i)) ^ 2)) (s := 0) fun _ => le_rfl
    simp only [mul_zero, nonpos_iff_eq_zero] at this
    exact this
  have hΓ : (fΓ (β := β) D).numBound = M + 1 := by
    rw [fΓ, numBound_fallT, numBound_fimp]
    simp [Fml.numBound, numBound_fQsol]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fB, fD, numBound_fnonneg,
    hK, hΓ, numBound_fQsol, Fintype.card_sum, Fintype.card_fin]
  ring

theorem maxDeg_inS (vτ vs : β) {d : ℕ} (hd2 : 2 ≤ d) (hd : ∀ b, (D.Q b).totalDegree ≤ d) :
    (inS D vτ vs).maxDeg ≤ d := by
  refine (maxDeg_fexT_le _).trans ?_
  refine maxDeg_fandL_le _ fun φ hφ => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hφ
  rcases hφ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine maxDeg_fandF_le _ fun i => ?_
    rw [maxDeg_fnonneg]
    refine (totalDegree_sub _ _).trans (max_le (by rw [totalDegree_C]; omega) ?_)
    exact (totalDegree_sq_sub_le _ _ (totalDegree_X_le _) (totalDegree_C_le _)).trans hd2
  · rw [fB, maxDeg_fnonneg]
    exact (totalDegree_C_sub_sum_le _ _ fun c =>
      totalDegree_sq_sub_le _ _ (totalDegree_X_le _) (totalDegree_C_le _)).trans hd2
  · rw [fB, maxDeg_fnonneg]
    exact (totalDegree_C_sub_sum_le _ _ fun c =>
      totalDegree_sq_sub_le _ _ (totalDegree_X_le _) (totalDegree_C_le _)).trans hd2
  · rw [fD, maxDeg_fnonneg]
    refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · refine (totalDegree_pow _ 2).trans ?_
      have := totalDegree_X_le (γ := β ⊕ Vb σ κ M) (.inl vτ)
      omega
    · exact ((totalDegree_finsetSum _ _).trans (Finset.sup_le fun c _ =>
        totalDegree_sq_sub_le _ _ (totalDegree_X_le _) (totalDegree_X_le _))).trans hd2
  · rw [maxDeg_fnonneg]
    have := totalDegree_X_le (γ := β ⊕ Vb σ κ M) (.inl vs)
    omega
  · exact maxDeg_fQsol D _ hd
  · refine (maxDeg_fallT_le _).trans ?_
    simp only [maxDeg_fimp, Fml.maxDeg]
    refine max_le ?_ (maxDeg_fQsol D _ hd)
    have := totalDegree_X_le (γ := (β ⊕ Vb σ κ M) ⊕ (Fin M ⊕ Unit)) (.inr (.inr ()))
    omega

theorem bb_inS (vτ vs : β) : BB (inS D vτ vs) 2 3 := by
  refine BB.fexT ?_ (by norm_num) (by norm_num) (a := 1)
  refine BB.fandL fun φ hφ => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hφ
  rcases hφ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact BB.fandF fun _ => BB.fnonneg _ _ _
  · exact BB.fnonneg _ _ _
  · exact BB.fnonneg _ _ _
  · exact BB.fnonneg _ _ _
  · exact BB.fnonneg _ _ _
  · exact bb_fQsol D _ _ _
  · exact BB.fallT (BB.fimp (BB.pos _ 1 1) (bb_fQsol D _ 1 1).not) le_rfl (by norm_num)

theorem size_fGraph : (fGraph D).size ≤ 4 * Fintype.card σ + 4 * D.B + 29 := by
  have h1 := size_inS D (β := Fin 2 ⊕ Unit) (.inl 0) (.inr ())
  have h2 := size_inS D (β := (Fin 2 ⊕ Unit) ⊕ Unit) (.inl (.inl 0)) (.inr ())
  simp only [fGraph, fUB, fAP, Fml.size, size_fallT, size_fimp, size_fexT]
  omega

theorem numBound_fGraph :
    (fGraph D).numBound = 2 * Fintype.card σ + 4 * Fintype.card κ + 4 * M + 5 := by
  have h1 := numBound_inS D (β := Fin 2 ⊕ Unit) (.inl 0) (.inr ())
  have h2 := numBound_inS D (β := (Fin 2 ⊕ Unit) ⊕ Unit) (.inl (.inl 0)) (.inr ())
  simp only [fGraph, fUB, fAP, Fml.numBound, numBound_fallT, numBound_fimp, numBound_fexT, h1, h2,
    Fintype.card_unit]
  ring

theorem maxDeg_fGraph {d : ℕ} (hd2 : 2 ≤ d) (hd : ∀ b, (D.Q b).totalDegree ≤ d) :
    (fGraph D).maxDeg ≤ d := by
  have h1 := maxDeg_inS D (β := Fin 2 ⊕ Unit) (.inl 0) (.inr ()) hd2 hd
  have h2 := maxDeg_inS D (β := (Fin 2 ⊕ Unit) ⊕ Unit) (.inl (.inl 0)) (.inr ()) hd2 hd
  have hX : ∀ {γ : Type} (a b : γ), ((X a - X b : MvPolynomial γ ℝ)).totalDegree ≤ d :=
    fun a b => ((totalDegree_sub _ _).trans (max_le (totalDegree_X_le a)
      (totalDegree_X_le b))).trans (by omega)
  simp only [fGraph, fUB, fAP, Fml.maxDeg]
  refine max_le ((maxDeg_fallT_le _).trans ?_) ((maxDeg_fallT_le _).trans ?_)
  · simp only [Fml.maxDeg]
    exact max_le h1 (hX _ _)
  · simp only [maxDeg_fimp, Fml.maxDeg]
    exact max_le (hX _ _) ((maxDeg_fexT_le _).trans (by simp only [Fml.maxDeg]; exact max_le h2 (hX _ _)))

theorem blocks_fGraph : (fGraph D).blocks ≤ 4 := by
  refine BB.blocks_le (a := 3) ?_
  have h1 := bb_inS D (β := Fin 2 ⊕ Unit) (.inl 0) (.inr ())
  have h2 := bb_inS D (β := (Fin 2 ⊕ Unit) ⊕ Unit) (.inl (.inl 0)) (.inr ())
  have hUB : BB (fUB D) 3 2 :=
    BB.fallT (h1.and (BB.pos _ _ _)).not (by norm_num) le_rfl
  have hAP : BB (fAP D) 4 3 :=
    BB.fallT (BB.fimp (BB.pos _ _ _) (BB.fexT (h2.and (BB.pos _ _ _)) (by norm_num) le_rfl))
      (by norm_num) (by norm_num)
  exact (hUB.mono (by norm_num) (by norm_num)).and hAP

end Measures

/-! ### Lemma 6.3 (d) -/

theorem totalDegree_progOutput_le {V : Type} (prog : SLP V ℕ) (c : ℕ → ℝ) (o : Operand V ℕ) :
    (progOutput prog c o).totalDegree ≤ 2 ^ prog.length := by
  have h := SLP.totalDegree_le (P := prog.instantiate c) (q := progOutput prog c o) ⟨_, rfl⟩
  rwa [SLP.instantiate, List.length_map] at h

theorem qeBound_le (C₀ : ℕ) (φ : Fml (Fin 2)) {A E bl : ℕ} (hA : φ.size + φ.maxDeg + 2 ≤ A)
    (hE : φ.numBound + 2 + 2 ≤ E) (hbl : φ.blocks ≤ bl) :
    qeBound C₀ φ ≤ A ^ (E ^ (C₀ * (bl + 1))) := by
  unfold qeBound
  have hA1 : 1 ≤ A := le_trans (by omega) hA
  have hE1 : 1 ≤ E := le_trans (by omega) hE
  calc (φ.size + φ.maxDeg + 2) ^ ((φ.numBound + 2 + 2) ^ (C₀ * (φ.blocks + 1)))
      ≤ A ^ ((φ.numBound + 2 + 2) ^ (C₀ * (φ.blocks + 1))) := Nat.pow_le_pow_left hA _
    _ ≤ A ^ (E ^ (C₀ * (φ.blocks + 1))) :=
        Nat.pow_le_pow_right hA1 (Nat.pow_le_pow_left hE _)
    _ ≤ A ^ (E ^ (C₀ * (bl + 1))) :=
        Nat.pow_le_pow_right hA1 (Nat.pow_le_pow_right hE1 (Nat.mul_le_mul_left _ (by omega)))

/-- **Lemma 6.3 (d).**  `N` can be chosen with `log N` bounded by a polynomial in
`n, |κ|, M, ℓ, t'`, where `ℓ` bounds the lengths of the programs of the `Q_b` and `B ≤ 4^{t'}`. -/
theorem lemma_6_3_d (hS : SAFacts) (hQE : EffectiveQE) :
    ∃ C e : ℕ, ∀ {σ κ : Type} [Fintype σ] [Fintype κ] [Nonempty κ] {M : ℕ} (D : SLData σ κ M),
      Pre D → ∀ ℓ t' : ℕ, (∀ b, (D.prog b).length ≤ ℓ) → D.B ≤ 4 ^ t' →
      ∃ (N : ℕ) (a : ℝ), 1 ≤ N ∧ 0 < a ∧
        (∀ x ∈ D.K, ∀ w ∈ D.Bbar, D.v x w ^ N ≤ a * sqDist w (D.φ x)) ∧
        Nat.log 2 N ≤ C * (Fintype.card σ + Fintype.card κ + M + ℓ + t' + 1) ^ e := by
  obtain ⟨C₀, hC₀⟩ := exponent_bound hS hQE
  refine ⟨1 + 14 * 9 ^ (5 * C₀), 5 * C₀ + 1, ?_⟩
  intro σ κ _ _ _ M D hD ℓ t' hℓ hB
  -- the rate given by effective quantifier elimination
  obtain ⟨L, σ₁, hσ₁, hL⟩ := hC₀ (fGraph D) (gfun D) 1 one_pos
    (fun τ _ y => hD.graph_iff τ y) (fun τ _ => hD.gfun_nonneg τ) hD.gfun_tendsto
  set qB := qeBound C₀ (fGraph D) with hqB
  have hqB1 : 1 ≤ qB := by rw [hqB]; unfold qeBound; exact Nat.one_le_pow _ _ (by omega)
  obtain ⟨a, ha, hflat⟩ := hD.flat_of_rate (qB * qB) (Nat.one_le_iff_ne_zero.2
    (Nat.mul_ne_zero (by omega) (by omega))) L σ₁ hσ₁ (by
      intro τ hτ
      have := hL τ hτ
      push_cast
      exact this)
  refine ⟨2 * (qB * qB), a, by nlinarith, ha, hflat, ?_⟩
  -- bookkeeping
  set S := Fintype.card σ + Fintype.card κ + M + ℓ + t' + 1 with hS_def
  have hS1 : 1 ≤ S := by omega
  have hdeg : ∀ b, (D.Q b).totalDegree ≤ 2 ^ (ℓ + 1) := fun b =>
    (totalDegree_progOutput_le _ _ _).trans
      (Nat.pow_le_pow_right (by norm_num) ((hℓ b).trans (Nat.le_succ _)))
  have hd2 : 2 ≤ 2 ^ (ℓ + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (ℓ + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hA : (fGraph D).size + (fGraph D).maxDeg + 2 ≤ 2 ^ (7 * S) := by
    have h1 := size_fGraph D
    have h2 := maxDeg_fGraph D hd2 hdeg
    have h4 : 2 ^ (2 * S + 3) = 4 * 2 ^ (2 * S + 1) := by
      rw [show 2 * S + 3 = (2 * S + 1) + 2 by omega, pow_add]; ring
    have e1 : 4 * Fintype.card σ ≤ 2 ^ (2 * S + 3) := by
      have : Fintype.card σ < 2 ^ Fintype.card σ := Nat.lt_two_pow_self
      have h3 : 2 ^ Fintype.card σ ≤ 2 ^ (2 * S + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have e2 : 4 * D.B ≤ 2 ^ (2 * S + 3) := by
      have h3 : 4 ^ t' = 2 ^ (2 * t') := by rw [pow_mul]; norm_num
      have h5 : 2 ^ (2 * t') ≤ 2 ^ (2 * S + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have e3 : 2 ^ (ℓ + 1) ≤ 2 ^ (2 * S + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have e4 : 31 ≤ 2 ^ (2 * S + 3) := by
      calc 31 ≤ 2 ^ 5 := by norm_num
        _ ≤ 2 ^ (2 * S + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have e5 : 4 * 2 ^ (2 * S + 3) ≤ 2 ^ (7 * S) := by
      calc 4 * 2 ^ (2 * S + 3) = 2 ^ (2 * S + 5) := by rw [pow_add, pow_add]; ring
        _ ≤ 2 ^ (7 * S) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hE : (fGraph D).numBound + 2 + 2 ≤ 9 * S := by
    rw [numBound_fGraph]; omega
  have hq : qB ≤ 2 ^ (7 * S * (9 * S) ^ (5 * C₀)) := by
    have := qeBound_le C₀ (fGraph D) hA hE (blocks_fGraph D)
    rw [← pow_mul] at this
    calc qB ≤ 2 ^ (7 * S * (9 * S) ^ (C₀ * (4 + 1))) := this
      _ = 2 ^ (7 * S * (9 * S) ^ (5 * C₀)) := by ring_nf
  have hN : 2 * (qB * qB) ≤ 2 ^ (1 + 14 * 9 ^ (5 * C₀) * S ^ (5 * C₀ + 1)) := by
    have hsq : qB * qB ≤ 2 ^ (7 * S * (9 * S) ^ (5 * C₀)) * 2 ^ (7 * S * (9 * S) ^ (5 * C₀)) :=
      Nat.mul_le_mul hq hq
    have : 1 + 14 * 9 ^ (5 * C₀) * S ^ (5 * C₀ + 1) =
        1 + (7 * S * (9 * S) ^ (5 * C₀) + 7 * S * (9 * S) ^ (5 * C₀)) := by
      rw [mul_pow, pow_succ]; ring
    rw [this, pow_add, pow_add, pow_one]
    exact Nat.mul_le_mul_left _ hsq
  calc Nat.log 2 (2 * (qB * qB)) ≤ Nat.log 2 (2 ^ (1 + 14 * 9 ^ (5 * C₀) * S ^ (5 * C₀ + 1))) :=
        Nat.log_mono_right hN
    _ = 1 + 14 * 9 ^ (5 * C₀) * S ^ (5 * C₀ + 1) := Nat.log_pow (by norm_num) _
    _ ≤ (1 + 14 * 9 ^ (5 * C₀)) * S ^ (5 * C₀ + 1) := by
        have : 1 ≤ S ^ (5 * C₀ + 1) := Nat.one_le_pow _ _ hS1
        nlinarith

end SetupAux

end ClassSep
