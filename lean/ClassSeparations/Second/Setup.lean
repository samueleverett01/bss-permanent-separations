import ClassSeparations.Second.Data
import ClassSeparations.Second.Exponent
import ClassSeparations.Cert.Isolate
import ClassSeparations.Basic.Cells
import ClassSeparations.Basic.TreeOps
import ClassSeparations.Second.Goodz
import ClassSeparations.Second.MarginData
import ClassSeparations.Second.FlattenD

/-!
# Part 1 of the proof of Theorem 6.1 (§6.1–6.2, Lemmas 6.2 and 6.3)

**Lemma 6.2.**  After isolating a certificate (Lemma 4.1) and fixing its coordinates `z♭`, there
are `r₀ > 0` and a closed ball `K` about `x₀` such that `|φ(x) - w₀| ≤ r₀/2` on `K` and, for
`x ∈ K` and `w ∈ B̄`: some `u` is rejected at `(x, y, (z♭, z'))` iff `w ≠ φ(x)`.

**Lemma 6.3.**  For the margin `v` of the rejecting cells:
(a) the fiber of `𝒴` over every `(x, w) ∈ K × B̄` is nonempty, `0 ≤ v ≤ 1`, and `v(x, w) = 0`
exactly when `w = φ(x)`; (b) `v` is upper semicontinuous; (c) there are `N ≥ 1` and `a > 0`
with `v(x, w)^N ≤ a |w - φ(x)|²` on `K × B̄`; (d) `N` can be chosen with `log N` bounded by a
polynomial in `t, n, k, l`.

`sl_setup` packages these results as `SLData` with the bounds needed in Part 2.

The proofs are in
* `ClassSeparations.Second.Goodz`: the set `F`, Lemma 6.2 (`SetupAux.lemma_6_2`);
* `ClassSeparations.Second.MarginData`: the margin systems of the cells (`SetupAux.cell_data`);
* `ClassSeparations.Second.Flatten`: Lemma 6.3 (a)–(c) (`SetupAux.lemma_6_3_a`, `_b`, `_c`) for
  data satisfying `SetupAux.Pre`;
* `ClassSeparations.Second.FlattenD`: Lemma 6.3 (d) (`SetupAux.lemma_6_3_d`), with the formula
  builders of `ClassSeparations.Second.Formula`.
-/

noncomputable section

open MvPolynomial Set Filter Topology

namespace ClassSep

namespace SetupAux

/-- Rejection is a marked outcome. -/
theorem not_accepts_iff {ι : Type} (T : Tree ι) (v : ι → ℝ) :
    ¬ T.Accepts v ↔ T.run v ∈ ({none, some false} : Set (Option Bool)) := by
  unfold Tree.Accepts
  rcases T.run v with _ | _ | _ <;> simp

end SetupAux

open SetupAux in
/-- **Part 1** of the proof of Theorem 6.1: Lemmas 6.2 and 6.3 in packaged form. -/
theorem sl_setup (hS : SAFacts) (hQE : EffectiveQE) :
    ∃ C e : ℕ, ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (d t k l : ℕ) (f : MvPolynomial σ ℝ),
      1 ≤ d → f.totalDegree ≤ d →
      ∀ U : Set (σ → ℝ), IsOpen U → U.Nonempty →
      ∀ T : Tree (σ ⊕ Unit ⊕ Fin k ⊕ Fin l), T.depth ≤ t →
      (∀ x ∈ U, ∀ y : ℝ, (∃ z, ∀ u, T.Accepts (inp4 x y z u)) ↔ y = eval x f) →
      ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ) (M : ℕ) (D : SLData σ κ M) (yc : κ),
        D.Good f yc ∧ Fintype.card κ ≤ k + 1 ∧ M ≤ C * (t + 1) ∧ D.ℓmax ≤ C * (t + 1) ∧
        Nat.log 2 D.N ≤ C * (t + Fintype.card σ + k + l + 1) ^ e := by
  obtain ⟨Cd, ed, hCd⟩ := lemma_6_3_d hS hQE
  refine ⟨50 + Cd * 56 ^ ed, ed, ?_⟩
  intro σ _ _ d t k l f _ _ U hU hUne T hT hdec
  -- restrict `U` to a ball
  obtain ⟨xc, hxc⟩ := hUne
  obtain ⟨rc, hrc, hball⟩ := Metric.isOpen_iff.1 hU xc hxc
  -- the set `F` and Lemma 4.1
  have hFsub : ∀ v ∈ Fset T f xc rc, v ∘ Sum.inl ∈ Metric.ball xc rc := fun v hv => hv.1
  have hproj : ∀ x ∈ Metric.ball xc rc, ∃ z, Sum.elim x z ∈ Fset T f xc rc := by
    intro x hx
    obtain ⟨z, hz⟩ := (hdec x (hball hx) (eval x f)).2 rfl
    exact ⟨z, (mem_Fset x z).2 ⟨hx, hz⟩⟩
  obtain ⟨x₀, z₀, N, I, r₃, ζ, -, hN, hx₀N, hr₃, hsub, hζ₀, hζ, hiso⟩ :=
    isolate hS xc rc hrc (Fset T f xc rc) (isSA_Fset T f xc rc) hFsub hproj
  -- Lemma 6.2
  obtain ⟨ρ, r₀, hρ, hr₀, hKsub, hφnear, hrej⟩ := lemma_6_2 T f U hdec xc rc hball x₀ z₀ N I r₃
    ζ hN hx₀N hr₃ hsub hζ₀ hζ.continuousOn hiso
  -- the cells of the rejecting outcomes (Lemma 2.5)
  obtain ⟨L, hLb, hLeq, hLlen⟩ := cells_length T t hT ({none, some false} : Set (Option Bool))
  -- the margin system of each cell
  have hcell := fun b : Fin L.length =>
    cell_data I z₀ t T.consts (L.get b) (hLb _ (List.get_mem L b))
  choose prog out cst hlen hnn hcert hs1 hbd using hcell
  set φ := phiOf I f ζ with hφ

  let D₀ : SLData σ (κI I) (2 * t + 2 * t + 2) := ⟨x₀, ρ, φ x₀, r₀, φ, L.length, prog, out, cst, 1, 1⟩
  have hK : D₀.K = Metric.closedBall x₀ ρ := rfl
  -- the properties before Lemma 6.3
  have hPre : Pre D₀ := by
    refine ⟨hρ, hr₀, (continuousOn_phiOf I f hζ.continuousOn).mono hKsub, hφnear,
      fun b p => hnn b p, ?_, ?_⟩
    · -- boundedness
      set R₀ := ‖x₀‖ + ρ + ‖φ x₀‖ + r₀ with hR₀
      choose R hR using fun b => hbd b R₀
      refine ⟨∑ b, |R b|, fun x w ν s hY => ?_⟩
      obtain ⟨hx, hw, hs, b, hb⟩ := hY
      refine ⟨fun i => ?_, hs1 b x w ν s hb⟩
      have hxb : ∀ i, |x i| ≤ R₀ := by
        intro i
        have h1 : |x i - x₀ i| ≤ ρ := by
          have := (dist_le_pi_dist x x₀ i).trans (Metric.mem_closedBall.1 hx)
          rwa [Real.dist_eq] at this
        have h2 : |x₀ i| ≤ ‖x₀‖ := by
          have := norm_le_pi_norm x₀ i
          rwa [Real.norm_eq_abs] at this
        have h3 : |x i| ≤ |x i - x₀ i| + |x₀ i| := by
          have := abs_add_le (x i - x₀ i) (x₀ i)
          rwa [sub_add_cancel] at this
        have h4 : 0 ≤ ‖φ x₀‖ := norm_nonneg _
        linarith
      have hwb : ∀ c, |w c| ≤ R₀ := by
        intro c
        have h1 : |w c - φ x₀ c| ≤ r₀ := sqd_abs_le' hr₀.le hw c
        have h2 : |φ x₀ c| ≤ ‖φ x₀‖ := by
          have := norm_le_pi_norm (φ x₀) c
          rwa [Real.norm_eq_abs] at this
        have h3 : |w c| ≤ |w c - φ x₀ c| + |φ x₀ c| := by
          have := abs_add_le (w c - φ x₀ c) (φ x₀ c)
          rwa [sub_add_cancel] at this
        have h4 : 0 ≤ ‖x₀‖ := norm_nonneg _
        linarith
      have := hR b x w ν s hxb hwb hs hb i
      exact this.trans ((le_abs_self _).trans
        (Finset.single_le_sum (f := fun b => |R b|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ b)))
    · -- Lemma 6.2 and Lemma 5.2 (a)
      intro x hx w hw
      rw [← hrej x hx w hw]
      constructor
      · rintro ⟨b, ν, s, hs, h⟩
        obtain ⟨u, hu⟩ := (hcert b x w).1 ⟨ν, s, hs, h⟩
        refine ⟨u, (not_accepts_iff _ _).2 ?_⟩
        have := Set.ext_iff.1 hLeq (inp4 x (w (.inl ())) (zOf z₀ w) u)
        simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop] at this
        exact this.2 ⟨_, List.get_mem L b, hu⟩
      · rintro ⟨u, hu⟩
        rw [not_accepts_iff] at hu
        have := Set.ext_iff.1 hLeq (inp4 x (w (.inl ())) (zOf z₀ w) u)
        simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop] at this
        obtain ⟨B, hB, hu'⟩ := this.1 hu
        obtain ⟨b, rfl⟩ := List.mem_iff_get.1 hB
        obtain ⟨ν, s, hs, h⟩ := (hcert b x w).2 ⟨u, hu'⟩
        exact ⟨b, ν, s, hs, h⟩
  -- Lemma 6.3 (a)–(d)
  obtain ⟨N', a, hN1, ha, hflat, hlog⟩ := hCd D₀ hPre (50 * t + 11) t hlen hLlen
  obtain ⟨hfib, -, hzero⟩ := lemma_6_3_a hPre
  let D : SLData σ (κI I) (2 * t + 2 * t + 2) := ⟨x₀, ρ, φ x₀, r₀, φ, L.length, prog, out, cst, N', a⟩
  refine ⟨κI I, inferInstance, inferInstance, 2 * t + 2 * t + 2, D, .inl (), ?_, ?_, ?_, ?_, ?_⟩
  · exact
      { ρ_pos := hρ
        r₀_pos := hr₀
        N_pos := hN1
        a_pos := ha
        φ_cont := hPre.φ_cont
        φ_near := hPre.φ_near
        φ_f := fun x _ => rfl
        nonneg := hPre.nonneg
        fiber_ne := hfib
        bounded := hPre.bounded
        zero_iff := hzero
        flat := hflat }
  · -- `|κ| ≤ k + 1`
    rw [Fintype.card_sum, Fintype.card_unit]
    have := Fintype.card_subtype_le (fun i : Fin k => i ∉ I)
    rw [Fintype.card_fin] at this
    omega
  · -- `M ≤ C (t + 1)`
    have : 0 ≤ Cd * 56 ^ ed * (t + 1) := Nat.zero_le _
    nlinarith
  · -- `ℓ ≤ C (t + 1)`
    have h1 : D.ℓmax ≤ 50 * t + 11 := Finset.sup_le fun b _ => hlen b
    have : 0 ≤ Cd * 56 ^ ed * (t + 1) := Nat.zero_le _
    nlinarith
  · -- `log N ≤ C (t + n + k + l + 1)^e`
    set S := t + Fintype.card σ + k + l + 1 with hS
    have hκ : Fintype.card (κI I) ≤ k + 1 := by
      rw [Fintype.card_sum, Fintype.card_unit]
      have := Fintype.card_subtype_le (fun i : Fin k => i ∉ I)
      rw [Fintype.card_fin] at this
      omega
    have hsum : Fintype.card σ + Fintype.card (κI I) + (2 * t + 2 * t + 2) + (50 * t + 11) + t + 1 ≤ 56 * S := by
      omega
    calc Nat.log 2 D.N = Nat.log 2 N' := rfl
      _ ≤ Cd * (Fintype.card σ + Fintype.card (κI I) + (2 * t + 2 * t + 2) + (50 * t + 11) + t + 1) ^ ed := hlog
      _ ≤ Cd * (56 * S) ^ ed := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsum _)
      _ = Cd * 56 ^ ed * S ^ ed := by rw [mul_pow, mul_assoc]
      _ ≤ (50 + Cd * 56 ^ ed) * S ^ ed := Nat.mul_le_mul_right _ (by omega)

end ClassSep
