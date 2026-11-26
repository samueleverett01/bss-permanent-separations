import ClassSeparations.Universal.Margin
import ClassSeparations.Second.Goodz

/-!
# The margin systems of the rejecting cells (§6.2)

For a cell `B` of the tree (on inputs `(x, y, z, u)`), with the fixed coordinates `z♭` of the
certificate substituted by constants, `w = (y, z')`, and the coordinates of `u` occurring in
the cell renamed into `Fin (2t)` (the others set to `0`), we form the margin system (6) of §5.3
with parameters `(x, w)` (`Margin.exists_margin`).  Padding the list of positivity conditions
with the condition `1 > 0` makes the number of unknowns the same, `M = 4t + 2`, for all cells.

`cell_data`: the resulting polynomial `Q(x, w, ν, s)` has a program graph with at most
`50t + 11` operations, is nonnegative, has a solution with `s > 0` at `(x, w)` iff some
`(x, y, zOf w, u)` lies in the cell (Lemma 5.2 (a)), its solutions have `s ≤ 1`, and its
solutions with `s ≥ 0` are bounded over bounded sets of parameters.
-/

noncomputable section

open MvPolynomial Set Filter Topology

namespace ClassSep

namespace SetupAux

/-! ### Generic facts -/

theorem eval_congr_vars' {α : Type} {p : MvPolynomial α ℝ} {v v' : α → ℝ}
    (h : ∀ i ∈ p.vars, v i = v' i) : eval v p = eval v' p :=
  eval₂Hom_congr' rfl (fun i hi _ => h i hi) rfl

theorem mem_carrier_congr' {α : Type} (B : Cell α) {Iv : Finset α}
    (hv : ∀ p ∈ B.eqs ++ B.poss, p.vars ⊆ Iv) {v v' : α → ℝ} (h : ∀ a ∈ Iv, v a = v' a) :
    v ∈ B.carrier ↔ v' ∈ B.carrier := by
  have he : ∀ p ∈ B.eqs ++ B.poss, eval v p = eval v' p :=
    fun p hp => eval_congr_vars' (fun i hi => h i (hv p hp hi))
  show ((∀ p ∈ B.eqs, eval v p = 0) ∧ ∀ q ∈ B.poss, 0 < eval v q) ↔
    ((∀ p ∈ B.eqs, eval v' p = 0) ∧ ∀ q ∈ B.poss, 0 < eval v' q)
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun p hp => (he p (List.mem_append_left _ hp)) ▸ h1 p hp,
      fun q hq => (he q (List.mem_append_right _ hq)) ▸ h2 q hq⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun p hp => (he p (List.mem_append_left _ hp)).symm ▸ h1 p hp,
      fun q hq => (he q (List.mem_append_right _ hq)).symm ▸ h2 q hq⟩

/-- A program over `ℝ` gives a program graph with the same number of operations. -/
theorem exists_progOutput' {β : Type} {P : SLP β ℝ} {q : MvPolynomial β ℝ} (h : P.Computes q) :
    ∃ (prog : SLP β ℕ) (oQ : Operand β ℕ) (cQ : ℕ → ℝ),
      prog.length = P.length ∧ progOutput prog cQ oQ = q := by
  obtain ⟨o, rfl⟩ := h
  refine ⟨BaurStrassen.graphOf (BaurStrassen.allConsts P o) P,
    BaurStrassen.toSlot (BaurStrassen.allConsts P o) o,
    fun m => (BaurStrassen.allConsts P o).getD m 0, BaurStrassen.length_graphOf _ _, ?_⟩
  rw [progOutput, BaurStrassen.graphOf_instantiate, BaurStrassen.toSlot_out_instantiate]

/-- Renaming the inputs of a program. -/
theorem computes_rename {β β' : Type} (g : β → β') {P : SLP β ℝ} {q : MvPolynomial β ℝ}
    (h : P.Computes q) :
    ∃ P' : SLP β' ℝ, P'.length = P.length ∧ P'.Computes (rename g q) := by
  have hρ : Margin.NoPrev (fun v : β => (Operand.input (g v) : Operand β' ℝ)) :=
    fun _ _ h => by cases h
  refine ⟨Margin.SLP.substIn (fun v => .input (g v)) P, Margin.SLP.length_substIn _ _, ?_⟩
  have := Margin.SLP.computes_substIn hρ h
  rwa [show Margin.ρpoly (fun v : β => (Operand.input (g v) : Operand β' ℝ)) =
    fun v => X (g v) from rfl, Margin.bind₁_X_comp] at this

/-! ### Padding the positivity conditions -/

/-- Append the trivial conditions `1 > 0` so that there are exactly `m` of them. -/
def padCell {α : Type} (m : ℕ) (B : Cell α) : Cell α :=
  ⟨B.prog, B.eqs, B.poss ++ List.replicate (m - B.poss.length) 1⟩

theorem padCell_carrier {α : Type} (m : ℕ) (B : Cell α) : (padCell m B).carrier = B.carrier := by
  ext w
  simp only [Cell.carrier, padCell, Set.mem_ofPred_eq, List.mem_append, List.mem_replicate]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun q hq => h2 q (Or.inl hq)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun q hq => ?_⟩
    rcases hq with hq | ⟨-, rfl⟩
    · exact h2 q hq
    · simp

theorem padCell_poss_length {α : Type} {m : ℕ} (B : Cell α) (h : B.poss.length ≤ m) :
    (padCell m B).poss.length = m := by
  simp only [padCell, List.length_append, List.length_replicate]
  omega

theorem padCell_computes {α : Type} (m : ℕ) (B : Cell α)
    (h : ∀ p ∈ B.eqs ++ B.poss, B.prog.Computes p) :
    ∀ p ∈ (padCell m B).eqs ++ (padCell m B).poss, (padCell m B).prog.Computes p := by
  intro p hp
  simp only [padCell, List.mem_append, List.mem_replicate] at hp
  rcases hp with hp | hp | ⟨-, rfl⟩
  · exact h p (List.mem_append_left _ hp)
  · exact h p (List.mem_append_right _ hp)
  · exact ⟨.const 1, by simp [Operand.eval]⟩

/-! ### The margin polynomial of a cell, with a fixed number of unknowns -/

theorem comp_mapE {π γ γ' : Type} (e : γ ≃ γ') (ξ : π → ℝ) (s : ℝ) (ν : γ' → ℝ) :
    Sum.elim ξ (extendVal s ν) ∘ Sum.map id (Option.map e) = Sum.elim ξ (extendVal s (ν ∘ e)) := by
  funext a
  rcases a with a | _ | a <;> rfl

/-- The margin system of a cell with `m₀` certificate coordinates and at most `m₁` positivity
conditions, with `m₀ + m₁ + 2` unknowns `ν` and the unknown `s`. -/
theorem margin_data {π : Type} (m₀ m₁ : ℕ) (B : Cell (π ⊕ Fin m₀))
    (hcomp : ∀ p ∈ B.eqs ++ B.poss, B.prog.Computes p) (hposs : B.poss.length ≤ m₁) :
    ∃ (Q : MvPolynomial (π ⊕ Option (Fin (m₀ + m₁ + 2))) ℝ)
      (P : SLP (π ⊕ Option (Fin (m₀ + m₁ + 2))) ℝ),
      P.length ≤ 4 * B.prog.length + 2 * m₀ + 2 * B.eqs.length + 5 * m₁ + 11 ∧ P.Computes Q ∧
      (∀ p, 0 ≤ eval p Q) ∧
      (∀ ξ : π → ℝ, (∃ z : Fin m₀ → ℝ, Sum.elim ξ z ∈ B.carrier) ↔
        ∃ s > 0, ∃ ν, eval (Sum.elim ξ (extendVal s ν)) Q = 0) ∧
      (∀ ξ s ν, eval (Sum.elim ξ (extendVal s ν)) Q = 0 → s ≤ 1) ∧
      (∀ K : Set (π → ℝ), IsCompact K → ∃ R, ∀ ξ ∈ K, ∀ s ν, 0 ≤ s →
        eval (Sum.elim ξ (extendVal s ν)) Q = 0 → ∀ i, |ν i| ≤ R) := by
  set B₂ := padCell m₁ B with hB₂
  have hlen₂ : B₂.poss.length = m₁ := padCell_poss_length B hposs
  obtain ⟨pS, qS, hH, P, o, hPlen, ho⟩ := Margin.exists_margin B₂ (padCell_computes m₁ B hcomp)
  have hcard : Fintype.card (Margin.MVar (Fin m₀) B₂.poss.length) = m₀ + m₁ + 2 := by
    simp only [Margin.MVar, Fintype.card_sum, Fintype.card_option, Fintype.card_fin, hlen₂]
    ring
  set e := Fintype.equivFinOfCardEq hcard with he
  set g : π ⊕ Option (Margin.MVar (Fin m₀) B₂.poss.length) → π ⊕ Option (Fin (m₀ + m₁ + 2)) :=
    Sum.map id (Option.map e) with hg
  obtain ⟨P', hP'len, hP'⟩ := computes_rename g (P := P) ⟨o, ho.symm⟩
  have hev : ∀ (ξ : π → ℝ) (s : ℝ) (ν : Fin (m₀ + m₁ + 2) → ℝ),
      eval (Sum.elim ξ (extendVal s ν)) (rename g (Margin.marginPoly pS qS)) =
        eval (Sum.elim ξ (extendVal s (ν ∘ e))) (Margin.marginPoly pS qS) := by
    intro ξ s ν
    rw [eval_rename, hg, comp_mapE]
  refine ⟨rename g (Margin.marginPoly pS qS), P', ?_, hP', ?_, ?_, ?_, ?_⟩
  · rw [hP'len]
    refine hPlen.trans ?_
    rw [Fintype.card_fin, hlen₂]
    exact le_rfl
  · intro p
    rw [eval_rename]
    exact Margin.marginPoly_nonneg pS qS _
  · intro ξ
    rw [← padCell_carrier m₁ B, Margin.margin_cert_iff hH ξ]
    constructor
    · rintro ⟨s, hs, ν, h⟩
      refine ⟨s, hs, ν ∘ e.symm, ?_⟩
      rw [hev]
      have : (ν ∘ e.symm) ∘ e = ν := by funext i; simp
      rw [this]; exact h
    · rintro ⟨s, hs, ν, h⟩
      exact ⟨s, hs, ν ∘ e, by rw [hev] at h; exact h⟩
  · intro ξ s ν h
    rw [hev] at h
    exact Margin.margin_s_le_one pS qS h
  · intro K hK
    obtain ⟨R, -, hR⟩ := Margin.margin_bounded pS qS hK
    refine ⟨R, fun ξ hξ s ν hs h i => ?_⟩
    rw [hev] at h
    have := hR ξ hξ s (ν ∘ e) hs h (e.symm i)
    simpa using this

/-! ### Substituting the fixed coordinates and renaming the universal ones -/

section Subst

variable {σ : Type} {k l m : ℕ}

/-- The substitution of the inputs of a cell: `x`, `y` are kept, `z♭` becomes the constants
`z₀`, `z'` the corresponding coordinates of `w`, the coordinates `u_j` with `j ∈ J` are renamed
along `emb`, and the others become `0`. -/
def rhoB (I : Finset (Fin k)) (z₀ : Fin k → ℝ) (J : Finset (Fin l)) (emb : J → Fin m) :
    σ ⊕ Unit ⊕ Fin k ⊕ Fin l → Operand ((σ ⊕ κI I) ⊕ Fin m) ℝ :=
  Sum.elim (fun i => .input (.inl (.inl i)))
    (Sum.elim (fun _ => .input (.inl (.inr (.inl ()))))
      (Sum.elim (fun i => if h : i ∈ I then .const (z₀ i) else .input (.inl (.inr (.inr ⟨i, h⟩))))
        (fun j => if h : j ∈ J then .input (.inr (emb ⟨j, h⟩)) else .const 0)))

/-- The universal coordinates determined by the renamed ones. -/
def uOf (J : Finset (Fin l)) (emb : J → Fin m) (z : Fin m → ℝ) : Fin l → ℝ :=
  fun j => if h : j ∈ J then z (emb ⟨j, h⟩) else 0

theorem noPrev_rhoB (I : Finset (Fin k)) (z₀ : Fin k → ℝ) (J : Finset (Fin l)) (emb : J → Fin m) :
    Margin.NoPrev (rhoB (σ := σ) I z₀ J emb) := by
  intro a j
  rcases a with i | _ | i | i
  · simp [rhoB]
  · simp [rhoB]
  · simp only [rhoB, Sum.elim_inr, Sum.elim_inl]
    split_ifs <;> simp
  · simp only [rhoB, Sum.elim_inr]
    split_ifs <;> simp

theorem eval_rhoB (I : Finset (Fin k)) (z₀ : Fin k → ℝ) (J : Finset (Fin l)) (emb : J → Fin m)
    (x : σ → ℝ) (w : κI I → ℝ) (z : Fin m → ℝ) :
    (fun a => eval (Sum.elim (Sum.elim x w) z) (Margin.ρpoly (rhoB I z₀ J emb) a)) =
      inp4 x (w (.inl ())) (zOf z₀ w) (uOf J emb z) := by
  funext a
  rcases a with i | _ | i | j
  · simp [rhoB, Margin.ρpoly, Operand.eval, inp4]
  · simp [rhoB, Margin.ρpoly, Operand.eval, inp4]
  · by_cases h : i ∈ I
    · simp [rhoB, Margin.ρpoly, Operand.eval, inp4, zOf, h]
    · simp [rhoB, Margin.ρpoly, Operand.eval, inp4, zOf, h]
  · by_cases h : j ∈ J
    · simp [rhoB, Margin.ρpoly, Operand.eval, inp4, uOf, h]
    · simp [rhoB, Margin.ρpoly, Operand.eval, inp4, uOf, h]

end Subst

/-! ### The data of one cell -/

theorem comp_sumAssoc {σ κ γ : Type} (x : σ → ℝ) (w : κ → ℝ) (v : γ → ℝ) :
    Sum.elim x (Sum.elim w v) ∘ (Equiv.sumAssoc σ κ γ) = Sum.elim (Sum.elim x w) v := by
  funext a
  rcases a with (a | a) | a <;> rfl

/-- **The margin system of a cell**, in the variables `(x, w, ν, s)` of `SLData`. -/
theorem cell_data {σ : Type} [Fintype σ] [DecidableEq σ] {k l : ℕ} (I : Finset (Fin k))
    (z₀ : Fin k → ℝ) (t : ℕ) (Kc : Set ℝ) (B : Cell (σ ⊕ Unit ⊕ Fin k ⊕ Fin l))
    (hB : B.Bounded t Kc) :
    ∃ (prog : SLP (σ ⊕ κI I ⊕ Option (Fin (2 * t + 2 * t + 2))) ℕ)
      (out : Operand (σ ⊕ κI I ⊕ Option (Fin (2 * t + 2 * t + 2))) ℕ) (cst : ℕ → ℝ),
      prog.length ≤ 50 * t + 11 ∧
      (∀ p, 0 ≤ eval p (progOutput prog cst out)) ∧
      (∀ (x : σ → ℝ) (w : κI I → ℝ),
        (∃ ν, ∃ s > 0, eval (SLData.pt x w ν s) (progOutput prog cst out) = 0) ↔
          ∃ u, inp4 x (w (.inl ())) (zOf z₀ w) u ∈ B.carrier) ∧
      (∀ x w ν s, eval (SLData.pt x w ν s) (progOutput prog cst out) = 0 → s ≤ 1) ∧
      (∀ R₀ : ℝ, ∃ R, ∀ (x : σ → ℝ) (w : κI I → ℝ) ν s, (∀ i, |x i| ≤ R₀) → (∀ c, |w c| ≤ R₀) →
        0 ≤ s → eval (SLData.pt x w ν s) (progOutput prog cst out) = 0 → ∀ i, |ν i| ≤ R) := by
  classical
  -- the coordinates of `u` occurring in the cell
  obtain ⟨Iv, hIvcard, -, hIv⟩ := hB.vars
  set J : Finset (Fin l) := Finset.univ.filter
    (fun j => (Sum.inr (Sum.inr (Sum.inr j)) : σ ⊕ Unit ⊕ Fin k ⊕ Fin l) ∈ Iv) with hJ
  have hJcard : J.card ≤ 2 * t := by
    refine (Finset.card_le_card_of_injOn (fun j => (Sum.inr (Sum.inr (Sum.inr j)) :
      σ ⊕ Unit ⊕ Fin k ⊕ Fin l)) (fun j hj => by simpa [hJ] using hj)
      (fun a _ b _ h => by simpa using h)).trans hIvcard
  set emb : J → Fin (2 * t) := fun j => Fin.castLE hJcard (J.equivFin j) with hemb
  have hembinj : Function.Injective emb := by
    intro a b h
    simp only [hemb, Fin.castLE_inj] at h
    exact J.equivFin.injective h
  -- the substituted cell
  set ρ := rhoB (σ := σ) I z₀ J emb with hρ
  have hρnp : Margin.NoPrev ρ := noPrev_rhoB I z₀ J emb
  set B₁ := Margin.Cell.substIn ρ B with hB₁
  have hcomp₁ : ∀ p ∈ B₁.eqs ++ B₁.poss, B₁.prog.Computes p :=
    Margin.Cell.computes_substIn hρnp B fun p hp => by
      rcases List.mem_append.1 hp with hp | hp
      · exact hB.computes_eqs p hp
      · exact hB.computes_poss p hp
  have hposs₁ : B₁.poss.length ≤ 2 * t := by
    simp only [hB₁, Margin.Cell.substIn, List.length_map]; exact hB.poss_len
  have hcert : ∀ (x : σ → ℝ) (w : κI I → ℝ),
      (∃ z : Fin (2 * t) → ℝ, Sum.elim (Sum.elim x w) z ∈ B₁.carrier) ↔
        ∃ u, inp4 x (w (.inl ())) (zOf z₀ w) u ∈ B.carrier := by
    intro x w
    simp only [hB₁, Margin.Cell.mem_carrier_substIn, hρ, eval_rhoB]
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨_, hz⟩
    · rintro ⟨u, hu⟩
      refine ⟨Function.extend emb (fun j => u j.1) 0, ?_⟩
      refine (mem_carrier_congr' B hIv ?_).2 hu
      intro a ha
      rcases a with i | _ | i | j
      · rfl
      · rfl
      · rfl
      · have hj : j ∈ J := by simp [hJ, ha]
        simp only [inp4, Sum.elim_inr, uOf, hj, ↓reduceDIte]
        exact hembinj.extend_apply _ _ ⟨j, hj⟩
  -- the margin system
  obtain ⟨Q, P, hPlen, hPQ, hQnn, hQcert, hQs, hQb⟩ := margin_data (2 * t) (2 * t) B₁ hcomp₁ hposs₁
  obtain ⟨P', hP'len, hP'⟩ := computes_rename
    (Equiv.sumAssoc σ (κI I) (Option (Fin (2 * t + 2 * t + 2)))) hPQ
  obtain ⟨prog, out, cst, hlen, hout⟩ := exists_progOutput' hP'
  have hev : ∀ x w ν s, eval (SLData.pt x w ν s) (progOutput prog cst out) =
      eval (Sum.elim (Sum.elim x w) (extendVal s ν)) Q := by
    intro x w ν s
    rw [hout, eval_rename, SLData.pt, comp_sumAssoc]
  refine ⟨prog, out, cst, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hlen, hP'len]
    refine hPlen.trans ?_
    have h1 : B₁.prog.length ≤ 8 * t := by
      simp only [hB₁, Margin.Cell.substIn, Margin.SLP.length_substIn]; exact hB.prog_len
    have h2 : B₁.eqs.length ≤ 2 * t := by
      simp only [hB₁, Margin.Cell.substIn, List.length_map]; exact hB.eqs_len
    omega
  · intro p
    rw [hout, eval_rename]
    exact hQnn _
  · intro x w
    rw [← hcert, hQcert]
    simp only [hev]
    constructor
    · rintro ⟨ν, s, hs, h⟩; exact ⟨s, hs, ν, h⟩
    · rintro ⟨s, hs, ν, h⟩; exact ⟨ν, s, hs, h⟩
  · intro x w ν s h
    rw [hev] at h
    exact hQs _ s ν h
  · intro R₀
    obtain ⟨R, hR⟩ := hQb (Metric.closedBall 0 (max R₀ 0)) (isCompact_closedBall _ _)
    refine ⟨R, fun x w ν s hx hw hs h i => ?_⟩
    rw [hev] at h
    refine hR _ ?_ s ν hs h i
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (le_max_right _ _)]
    intro a
    rw [Real.norm_eq_abs]
    rcases a with a | a
    · exact (hx a).trans (le_max_left _ _)
    · exact (hw a).trans (le_max_left _ _)

end SetupAux

end ClassSep
