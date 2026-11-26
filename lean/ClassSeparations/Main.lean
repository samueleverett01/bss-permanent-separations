import ClassSeparations.Machines.AMNP
import ClassSeparations.Machines.Perm
import ClassSeparations.Machines.Glue
import ClassSeparations.Second.Main
import ClassSeparations.Universal.Separations

/-!
# The main theorems A–F

Each theorem is proved from the hypotheses that collect the results the paper cites:
`SAFacts` ((S2)–(S8)), `PermLowerBound` (Theorem 2.3), `BurgisserThm` (Theorem 2.5),
`EffectiveQE` ([BPR06], Lemma 6.3 (d)), `CountingBound` ((C), Lemma 7.7) and `ClassFacts`
(known inclusions between classes).

The class-level statements follow the same pattern: a machine witnessing a membership unrolls
into trees of polynomial depth (`ClassSeparations.Machines.Glue`), the tree corollaries give a
lower bound `2^{Ω((log m)^{4/3})}` on their depth, and a polynomial is eventually below it
(`not_superPolyLB`).
-/

noncomputable section

open MvPolynomial Set Filter

namespace ClassSep

/-- Corollary 5.5 for the complement of the graph (the tree part of `PERM ∉ coNP_ℝ`): trees of
depth `t_m` deciding `{Y ≠ per_m(X)}` in the existential sense have
`t_m ≥ 2^{Ω((log m)^{4/3})}`.  This is Theorem 5.1 with the accepting outcomes marked. -/
theorem cor_ne (hS : SAFacts) (hLB : PermLowerBound) (t k : ℕ → ℕ)
    (T : ∀ m, Tree ((Fin m × Fin m) ⊕ Unit ⊕ Fin (k m)))
    (hT : ∀ m, (T m).depth ≤ t m)
    (hdec : ∀ m, ExDecides (T m) (fun X Y => Y ≠ eval X (per m))) :
    SuperPolyLB fun m => t m := by
  obtain ⟨C, hC⟩ := onesided_cases hS
  refine superPoly_of_borderLE hLB t (5 * C) 8 2 ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  refine (hC m (t m) (k m) (per m) hm (totalDegree_per m) (T m) (hT m)
    (Or.inr ⟨fun x z hz => (hdec m x _).1 ⟨z, hz⟩ rfl,
      fun x y hy => (hdec m x y).2 hy.ne'⟩)).mono ?_
  rw [Fintype.card_prod, Fintype.card_fin]
  refine le_trans ?_ (conp_arith C m (t m))
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.pow_le_pow_left (by omega) 2) _)

/-- The tree part of `permLang r ∉ NP_ℝ`: an `NP_ℝ` machine gives trees of polynomial depth
deciding `perLang r` in the existential sense. -/
theorem permLang_np_family {r : PerRel} (h : permLang r ∈ NP_R) :
    ∃ (t k : ℕ → ℕ) (T : ∀ m, Tree ((Fin m × Fin m) ⊕ Unit ⊕ Fin (k m))),
      PolyBounded t ∧ (∀ m, (T m).depth ≤ t m) ∧ ∀ m, ExDecides (T m) (perLang r m) :=
  np_family h (perLang r) (fun _ hm X Y => permEnc_mem_permLang r hm X Y)
    (perLang_zero_trees r)

/-- **Theorem A** (`NP_ℝ ≠ PAR_ℝ`).  `PERM` is in `PAR_ℝ` and not in `NP_ℝ`; the same holds for
the thresholds `{Y ≤ per_m(X)}` and `{Y ≥ per_m(X)}`; consequently `NP_ℝ ⊊ PAR_ℝ`.  (The
quantitative tree bound is `cor_np`.) -/
theorem theorem_A (hS : SAFacts) (hLB : PermLowerBound) (hF : ClassFacts) :
    (∀ r : PerRel, (r = .eq ∨ r = .le ∨ r = .ge) → permLang r ∈ PAR_R ∧ permLang r ∉ NP_R) ∧
      NP_R ⊂ PAR_R := by
  have key : ∀ r : PerRel, (r = .eq ∨ r = .le ∨ r = .ge) →
      permLang r ∈ PAR_R ∧ permLang r ∉ NP_R := by
    intro r hr
    refine ⟨permLang_mem_PAR r hr, fun h => ?_⟩
    obtain ⟨t, k, T, ht, hT, hdec⟩ := permLang_np_family h
    exact not_superPolyLB ht (cor_np hS hLB r hr t k T hT hdec)
  exact ⟨key, (Set.ssubset_iff_of_subset hF.np_sub_par).2
    ⟨permLang .eq, (key .eq (Or.inl rfl)).1, (key .eq (Or.inl rfl)).2⟩⟩

/-- **Theorem B** (universal certificates and the second level).  The graph and the closed
thresholds are in neither `coNP_ℝ` nor `Σ₂^ℝ`; consequently `coNP_ℝ ⊊ PAR_ℝ` and
`Σ₂^ℝ ⊊ PAR_ℝ`.  (The quantitative tree bounds are `cor_conp_universal` and `cor_second`.) -/
theorem theorem_B (hS : SAFacts) (hLB : PermLowerBound) (hQE : EffectiveQE) (hF : ClassFacts) :
    (∀ r : PerRel, (r = .eq ∨ r = .le ∨ r = .ge) →
      permLang r ∉ coNP_R ∧ permLang r ∉ Sigma2_R) ∧
    coNP_R ⊂ PAR_R ∧ Sigma2_R ⊂ PAR_R := by
  -- `coNP`: the complement is in `NP`, i.e. decided existentially; for the graph this is
  -- `{Y ≠ per_m(X)}`, for the closed thresholds it is a strict threshold
  have hco : ∀ r : PerRel, (r = .eq ∨ r = .le ∨ r = .ge) → permLang r ∉ coNP_R := by
    intro r hr h
    have h' : (permLang r).compl ∈ NP_R := h
    rcases hr with rfl | rfl | rfl
    · obtain ⟨t, k, T, ht, hT, hdec⟩ := np_family h' (fun m X Y => Y ≠ eval X (per m))
        (fun m hm X Y => by
          simp only [Lang.compl, Set.mem_compl_iff]
          rw [permEnc_mem_permLang _ hm]
          rfl)
        ne_zero_trees
      exact not_superPolyLB ht (cor_ne hS hLB t k T hT hdec)
    · obtain ⟨t, k, T, ht, hT, hdec⟩ := np_family h' (perLang .gt)
        (fun m hm X Y => by
          simp only [Lang.compl, Set.mem_compl_iff]
          rw [permEnc_mem_permLang _ hm]
          exact not_le)
        (perLang_zero_trees .gt)
      exact not_superPolyLB ht (cor_conp_strict hS hLB .gt (Or.inr rfl) t k T hT hdec)
    · obtain ⟨t, k, T, ht, hT, hdec⟩ := np_family h' (perLang .lt)
        (fun m hm X Y => by
          simp only [Lang.compl, Set.mem_compl_iff]
          rw [permEnc_mem_permLang _ hm]
          exact not_le)
        (perLang_zero_trees .lt)
      exact not_superPolyLB ht (cor_conp_strict hS hLB .lt (Or.inl rfl) t k T hT hdec)
  -- `Σ₂`: trees with quantifiers `∃ z ∀ u` and Corollary 6.8
  have hs2 : ∀ r : PerRel, (r = .eq ∨ r = .le ∨ r = .ge) → permLang r ∉ Sigma2_R := by
    intro r hr h
    obtain ⟨t, k, l, T, ht, hT, hdec⟩ := sigma2_family h (perLang r)
      (fun _ hm X Y => permEnc_mem_permLang r hm X Y) (perLang_zero_trees r)
    exact not_superPolyLB ht (cor_second hS hQE hLB r hr t k l T hT hdec)
  have hpar := permLang_mem_PAR .eq (Or.inl rfl)
  exact ⟨fun r hr => ⟨hco r hr, hs2 r hr⟩,
    (Set.ssubset_iff_of_subset hF.conp_sub_par).2 ⟨_, hpar, hco .eq (Or.inl rfl)⟩,
    (Set.ssubset_iff_of_subset hF.sigma2_sub_par).2 ⟨_, hpar, hs2 .eq (Or.inl rfl)⟩⟩

/-- Corollary 5.5 (a), second half: the strict thresholds are not in `NP_ℝ`. -/
theorem strict_thresholds_not_NP (hS : SAFacts) (hLB : PermLowerBound) (r : PerRel)
    (hr : r = .lt ∨ r = .gt) : permLang r ∉ NP_R := by
  intro h
  obtain ⟨t, k, T, ht, hT, hdec⟩ := permLang_np_family h
  exact not_superPolyLB ht (cor_conp_strict hS hLB r hr t k T hT hdec)

/-- **Theorem C** (the complex numbers).  The graph of the complex permanent is in `PAR_ℂ` and
in neither `NP_ℂ` nor `coNP_ℂ`; consequently `NP_ℂ ⊊ PAR_ℂ` and `coNP_ℂ ⊊ PAR_ℂ`. -/
theorem theorem_C (hS : SAFacts) (hLB : PermLowerBound) (hF : ClassFacts) :
    cpermLang ∈ PAR_C ∧ cpermLang ∉ NP_C ∧ cpermLang ∉ coNP_C ∧
      NP_C ⊂ PAR_C ∧ coNP_C ⊂ PAR_C := by
  have hnp : cpermLang ∉ NP_C := fun h => by
    obtain ⟨t, k, T, ht, hT, hdec⟩ := npc_perm_family h
    exact not_superPolyLB ht (cor_conp_complex hS hLB t k T hT fun m => Or.inl (hdec m))
  have hconp : cpermLang ∉ coNP_C := fun h => by
    obtain ⟨t, k, T, ht, hT, hdec⟩ := conpc_perm_family h
    exact not_superPolyLB ht (cor_conp_complex hS hLB t k T hT fun m => Or.inr (hdec m))
  exact ⟨cpermLang_mem_PAR, hnp, hconp,
    (Set.ssubset_iff_of_subset hF.npc_sub_parc).2 ⟨_, cpermLang_mem_PAR, hnp⟩,
    (Set.ssubset_iff_of_subset hF.conpc_sub_parc).2 ⟨_, cpermLang_mem_PAR, hconp⟩⟩

/-- **Theorem D** (Boolean messages).  `PERM ∉ BIP_ℝ`, and `BIP_ℝ ⊊ PAR_ℝ`.  (The quantitative
bound on verifier trees is `bip_lower`.) -/
theorem theorem_D (hLB : PermLowerBound) (hB : BurgisserThm) (hF : ClassFacts) :
    permLang .eq ∉ BIP_R ∧ BIP_R ⊂ PAR_R := by
  have hnot : permLang .eq ∉ BIP_R := fun h => by
    obtain ⟨t, V, ht, hV, hdec⟩ := bip_perm_family h
    exact not_superPolyLB ht (bip_lower hLB hB t V hV hdec)
  exact ⟨hnot, (Set.ssubset_iff_of_subset hF.bip_sub_par).2
    ⟨_, permLang_mem_PAR .eq (Or.inl rfl), hnot⟩⟩

/-- **Theorem E** (rounds of real interaction).
(i) `AM_ℝ[c] = NP_ℝ` for every constant `c ≥ 1`, and `AM_ℝ[O(1)] = NP_ℝ ⊊ AM_ℝ[poly] = IP_ℝ`.
(ii) `PERM ∉ AM_ℝ[O(1)]`.  (The `Ω(log log m)` bound on rounds is `am_rounds`.) -/
theorem theorem_E (hS : SAFacts) (hLB : PermLowerBound) (hC : CountingBound)
    (hF : ClassFacts) :
    (∀ c, 1 ≤ c → AM_R c = NP_R) ∧ AM_R_const = NP_R ∧ NP_R ⊂ AM_R_poly ∧
      AM_R_poly = IP_R ∧ permLang .eq ∉ AM_R_const := by
  obtain ⟨h₁, h₂, h₃⟩ := am_const_eq_np hC hF
  refine ⟨fun c hc => am_eq_np hC c hc, h₁, h₂, h₃, ?_⟩
  rw [h₁]
  exact ((theorem_A hS hLB hF).1 .eq (Or.inl rfl)).2

/-- **Theorem F** (certificates and border complexity).  Let `f` have degree `≤ d` and `U` be
open and nonempty.  If a tree of depth `t` verifies `y = f(x)` on `U × ℝ` (i) existentially,
(ii) universally, or (iii) with an existential block of length `k` followed by a universal
block of length `l`, then the border complexity of `f` is polynomially bounded in `t, d, n`
(resp. `t + k + l, d, n`).  (Case (i) for thresholds is `threshold_theorem_le/ge`; case (ii)
for thresholds follows from `onesided`.) -/
theorem theorem_F (hS : SAFacts) (hQE : EffectiveQE) :
    ∃ C e : ℕ, ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (d t k l : ℕ) (f : MvPolynomial σ ℝ),
      1 ≤ d → f.totalDegree ≤ d → ∀ U : Set (σ → ℝ), IsOpen U → U.Nonempty →
      (∀ T : Tree (σ ⊕ Unit ⊕ Fin k), T.depth ≤ t →
        (∀ x ∈ U, ∀ y : ℝ, (∃ z, T.Accepts (inp3 x y z)) ↔ y = eval x f) →
        BorderLE f (C * (t + d + Fintype.card σ + 1) ^ e)) ∧
      (∀ T : Tree (σ ⊕ Unit ⊕ Fin k), T.depth ≤ t →
        (∀ x ∈ U, ∀ y : ℝ, (∀ z, T.Accepts (inp3 x y z)) ↔ y = eval x f) →
        BorderLE f (C * (t + d + Fintype.card σ + 1) ^ e)) ∧
      (∀ T : Tree (σ ⊕ Unit ⊕ Fin k ⊕ Fin l), T.depth ≤ t →
        (∀ x ∈ U, ∀ y : ℝ, (∃ z, ∀ u, T.Accepts (inp4 x y z u)) ↔ y = eval x f) →
        BorderLE f (C * (t + k + l + d + Fintype.card σ + 1) ^ e)) := by
  obtain ⟨C₁, h₁⟩ := graph_theorem hS
  obtain ⟨C₂, h₂⟩ := onesided_universal_eq hS
  obtain ⟨C₃, e₃, h₃⟩ := second_level hS hQE
  refine ⟨6 * C₁ + 2 * C₂ + C₃, 8 + e₃, ?_⟩
  intro σ _ _ d t k l f hd hf U hU hne
  set n := Fintype.card σ with hn
  -- with `S = t + d + n + 1`, all bounds are at most `S ^ (8 + e₃)` times a constant
  set S := t + d + n + 1 with hSdef
  have hS1 : 1 ≤ S := by omega
  have hdS : d + 1 ≤ S := by omega
  have htS : t + 1 ≤ S := by omega
  have hnS : n ≤ S := by omega
  have hpow : ∀ a, a ≤ 8 + e₃ → S ^ a ≤ S ^ (8 + e₃) := fun a ha => Nat.pow_le_pow_right hS1 ha
  have hC : ∀ (A a : ℕ), A ≤ 6 * C₁ + 2 * C₂ + C₃ → a ≤ 8 + e₃ →
      A * S ^ a ≤ (6 * C₁ + 2 * C₂ + C₃) * S ^ (8 + e₃) :=
    fun A a hA ha => Nat.mul_le_mul hA (hpow a ha)
  refine ⟨fun T hT hdec => ?_, fun T hT hdec => ?_, fun T hT hdec => ?_⟩
  · -- (i): the graph theorem
    refine (h₁ d t k f hd hf U hU hne T hT hdec).mono ?_
    have a1 : (d + 1) ^ 3 * t ≤ S ^ 4 := by
      calc (d + 1) ^ 3 * t ≤ S ^ 3 * S :=
            Nat.mul_le_mul (Nat.pow_le_pow_left hdS 3) (by omega)
        _ = S ^ 4 := by ring
    have a2 : (d + 1) ^ 2 * (min k (2 * t) + 2) ^ 2 ≤ 4 * S ^ 4 := by
      have hm : min k (2 * t) + 2 ≤ 2 * S := by have := min_le_right k (2 * t); omega
      calc (d + 1) ^ 2 * (min k (2 * t) + 2) ^ 2 ≤ S ^ 2 * (2 * S) ^ 2 :=
            Nat.mul_le_mul (Nat.pow_le_pow_left hdS 2) (Nat.pow_le_pow_left hm 2)
        _ = 4 * S ^ 4 := by ring
    have a3 : n ≤ S ^ 4 := hnS.trans (Nat.le_self_pow (by norm_num) S)
    calc C₁ * ((d + 1) ^ 3 * t + (d + 1) ^ 2 * (min k (2 * t) + 2) ^ 2 + n)
        ≤ C₁ * (6 * S ^ 4) := Nat.mul_le_mul_left _ (by omega)
      _ = (6 * C₁) * S ^ 4 := by ring
      _ ≤ (6 * C₁ + 2 * C₂ + C₃) * S ^ (8 + e₃) := hC _ _ (by omega) (by omega)
  · -- (ii): one-sided certificates
    refine (h₂ d t k f hd hf U hU hne T hT hdec).mono ?_
    have a1 : (d + 1) ^ 6 ≤ S ^ 6 := Nat.pow_le_pow_left hdS 6
    have a2 : (t + 1) ^ 2 + n ≤ 2 * S ^ 2 := by
      have b1 : (t + 1) ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left htS 2
      have b2 : n ≤ S ^ 2 := hnS.trans (Nat.le_self_pow (by norm_num) S)
      omega
    calc C₂ * (d + 1) ^ 6 * ((t + 1) ^ 2 + n) ≤ C₂ * S ^ 6 * (2 * S ^ 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ a1) a2
      _ = (2 * C₂) * S ^ 8 := by ring
      _ ≤ (6 * C₁ + 2 * C₂ + C₃) * S ^ (8 + e₃) := hC _ _ (by omega) (by omega)
  · -- (iii): an existential and a universal block
    refine (h₃ d t k l f hd hf U hU hne T hT hdec).mono ?_
    have hS'1 : 1 ≤ t + k + l + d + n + 1 := by omega
    exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right hS'1 (by omega))

end ClassSep
