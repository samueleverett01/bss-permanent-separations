import ClassSeparations.Machines.AMNP
import ClassSeparations.Machines.Perm
import ClassSeparations.Second.Main
import ClassSeparations.Universal.Separations

/-!
# From machines to families of trees

General glue between the machine classes of `ClassSeparations.Machines` and the tree
corollaries (`cor_np`, `cor_conp_strict`, `cor_conp_complex`, `cor_second`, `bip_lower`).

A polynomial-time machine witnessing the membership of a language `L` in `NP_ℝ` (resp. `Σ₂^ℝ`,
`NP_ℂ`, `coNP_ℂ`, `BIP_ℝ`) unrolls, at the input size `n = m² + 1`, into a tree of polynomial
depth (`Machine.unroll`, `CMachine.unroll`, `IMachine.unroll_bool`).  Renaming its inputs from
`Fin (n + q n)` to `(Fin m × Fin m) ⊕ Unit ⊕ Fin (q n)` (the matrix `X` row-major, then `Y`, then
the certificate) gives a tree deciding the slice of `L` at `m` in the sense of the corollaries.
For `m = 0` (where `PERM` is empty but `per₀ = 1`) we use small explicit trees.

Finally a polynomial in `m` is eventually below `2^{c (log₂ m)^{4/3}}`
(`not_superPolyLB`), which contradicts the corollaries.
-/

set_option autoImplicit false

noncomputable section

open MvPolynomial Set Filter Classical

namespace ClassSep

/-! ## Polynomial bounds -/

theorem PolyBounded.add {f g : ℕ → ℕ} (hf : PolyBounded f) (hg : PolyBounded g) :
    PolyBounded fun n => f n + g n := by
  obtain ⟨C₁, e₁, h₁⟩ := hf
  obtain ⟨C₂, e₂, h₂⟩ := hg
  refine ⟨C₁ + C₂, e₁ + e₂, fun n => ?_⟩
  have hn : 1 ≤ n + 1 := by omega
  have a₁ : (n + 1) ^ e₁ ≤ (n + 1) ^ (e₁ + e₂) := Nat.pow_le_pow_right hn (by omega)
  have a₂ : (n + 1) ^ e₂ ≤ (n + 1) ^ (e₁ + e₂) := Nat.pow_le_pow_right hn (by omega)
  calc f n + g n ≤ C₁ * (n + 1) ^ e₁ + C₂ * (n + 1) ^ e₂ := Nat.add_le_add (h₁ n) (h₂ n)
    _ ≤ C₁ * (n + 1) ^ (e₁ + e₂) + C₂ * (n + 1) ^ (e₁ + e₂) := by gcongr
    _ = (C₁ + C₂) * (n + 1) ^ (e₁ + e₂) := by ring

theorem PolyBounded.const (c : ℕ) : PolyBounded fun _ => c :=
  ⟨c, 0, fun n => by simp⟩

theorem PolyBounded.mono {f g : ℕ → ℕ} (hg : PolyBounded g) (h : ∀ n, f n ≤ g n) :
    PolyBounded f := by
  obtain ⟨C, e, hC⟩ := hg
  exact ⟨C, e, fun n => (h n).trans (hC n)⟩

/-- A polynomial bound in `n` gives a polynomial bound in `m` for `n = m² + 1`. -/
theorem PolyBounded.comp_sq {p : ℕ → ℕ} (hp : PolyBounded p) :
    PolyBounded fun m => p (m * m + 1) := by
  obtain ⟨C, e, h⟩ := hp
  refine ⟨C * 2 ^ e, 2 * e, fun m => ?_⟩
  have h1 : m * m + 1 + 1 ≤ 2 * (m + 1) ^ 2 := by nlinarith
  calc p (m * m + 1) ≤ C * (m * m + 1 + 1) ^ e := h _
    _ ≤ C * (2 * (m + 1) ^ 2) ^ e := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 e)
    _ = C * 2 ^ e * (m + 1) ^ (2 * e) := by rw [mul_pow, ← pow_mul]; ring

/-- **A polynomial is not super-polynomial**: a polynomially bounded `t` does not satisfy
`t_m ≥ 2^{c (log₂ m)^{4/3}}` for all large `m`. -/
theorem not_superPolyLB {t : ℕ → ℕ} (ht : PolyBounded t) : ¬ SuperPolyLB fun m => (t m : ℝ) := by
  rintro ⟨c, hc, hev⟩
  obtain ⟨C, e, hC⟩ := ht
  obtain ⟨m, hm, hK, hm1⟩ := (hev.and ((eventually_add_mul_logb_le (c / 2) ((C : ℝ) + e + 1) e
    (by positivity)).and (eventually_ge_atTop 1))).exists
  set L := Real.logb 2 (m : ℝ) with hLdef
  have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hL0 : 0 ≤ L := Real.logb_nonneg (by norm_num) hm1'
  have h2L : (2 : ℝ) ^ L = m := Real.rpow_logb (by norm_num) (by norm_num) (by linarith)
  have hA : (C : ℝ) ≤ (2 : ℝ) ^ (C : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast (Nat.lt_two_pow_self).le
  have hmA : ((m : ℝ) + 1) ^ e ≤ (2 : ℝ) ^ ((1 + L) * e) := by
    rw [Real.rpow_mul_natCast (by norm_num)]
    gcongr
    rw [Real.rpow_add (by norm_num), Real.rpow_one, h2L]
    linarith
  have htm : (t m : ℝ) ≤ (2 : ℝ) ^ ((C : ℝ) + (1 + L) * e) := by
    calc (t m : ℝ) ≤ (C : ℝ) * ((m : ℝ) + 1) ^ e := by exact_mod_cast hC m
      _ ≤ (2 : ℝ) ^ (C : ℝ) * (2 : ℝ) ^ ((1 + L) * e) := by gcongr
      _ = (2 : ℝ) ^ ((C : ℝ) + (1 + L) * e) := by rw [Real.rpow_add (by norm_num)]
  have h := hm.trans htm
  rw [Real.rpow_le_rpow_left_iff (by norm_num)] at h
  have hL' : 0 ≤ L ^ (4 / 3 : ℝ) := Real.rpow_nonneg hL0 _
  have := mul_nonneg hc.le hL'
  nlinarith

/-! ## Encoding `(X, Y)` as a vector of length `m² + 1` -/

theorem comp_finAppend {α β : Type*} {a b : ℕ} (g : α → β) (u : Fin a → α) (v : Fin b → α) :
    g ∘ Fin.append u v = Fin.append (g ∘ u) (g ∘ v) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp

/-- The vector `(X, Y) ∈ α^{m²+1}`: the matrix `X` row-major, then `Y`. -/
def permEnc {α : Type*} (m : ℕ) (X : Fin m × Fin m → α) (Y : α) : Fin (m * m + 1) → α :=
  Fin.append (fun i => X (finProdFinEquiv.symm i)) (fun _ => Y)

theorem permEnc_index (m : ℕ) (p : Fin m × Fin m) : p.1.val * m + p.2.val < m * m + 1 := by
  have h1 := p.1.2
  have h2 := p.2.2
  nlinarith

theorem permEnc_apply_index {α : Type*} (m : ℕ) (X : Fin m × Fin m → α) (Y : α)
    (p : Fin m × Fin m) (h : p.1.val * m + p.2.val < m * m + 1) :
    permEnc m X Y ⟨p.1.val * m + p.2.val, h⟩ = X p := by
  have : (⟨p.1.val * m + p.2.val, h⟩ : Fin (m * m + 1)) = Fin.castAdd 1 (finProdFinEquiv p) := by
    ext
    simp only [Fin.val_castAdd, finProdFinEquiv_apply_val]
    ring
  rw [this, permEnc, Fin.append_left, Equiv.symm_apply_apply]

theorem permEnc_last {α : Type*} (m : ℕ) (X : Fin m × Fin m → α) (Y : α)
    (h : m * m < m * m + 1) : permEnc m X Y ⟨m * m, h⟩ = Y := by
  have : (⟨m * m, h⟩ : Fin (m * m + 1)) = Fin.natAdd (m * m) (0 : Fin 1) := by
    ext
    simp
  rw [this, permEnc, Fin.append_right]

theorem permX_permEnc (m : ℕ) (X : Fin m × Fin m → ℝ) (Y : ℝ) :
    permX m (permEnc m X Y) = X := by
  funext p
  simp only [permX, permEnc_index m p, ↓reduceDIte, permEnc_apply_index]

theorem permY_permEnc (m : ℕ) (X : Fin m × Fin m → ℝ) (Y : ℝ) :
    permY m (permEnc m X Y) = Y := by
  simp only [permY, show m * m < m * m + 1 by omega, ↓reduceDIte, permEnc_last]

theorem permXC_permEnc (m : ℕ) (X : Fin m × Fin m → ℂ) (Y : ℂ) :
    permXC m (permEnc m X Y) = X := by
  funext p
  simp only [permXC, permEnc_index m p, ↓reduceDIte, permEnc_apply_index]

theorem permYC_permEnc (m : ℕ) (X : Fin m × Fin m → ℂ) (Y : ℂ) :
    permYC m (permEnc m X Y) = Y := by
  simp only [permYC, show m * m < m * m + 1 by omega, ↓reduceDIte, permEnc_last]

theorem permEnc_mem_permLang (r : PerRel) {m : ℕ} (hm : 1 ≤ m) (X : Fin m × Fin m → ℝ)
    (Y : ℝ) : permEnc m X Y ∈ permLang r (m * m + 1) ↔ perLang r m X Y := by
  constructor
  · rintro ⟨m', -, he, h⟩
    have hmm : m' = m := Nat.mul_self_inj.1 (Nat.add_right_cancel he).symm
    subst hmm
    rwa [permX_permEnc, permY_permEnc] at h
  · intro h
    exact ⟨m, hm, rfl, by rwa [permX_permEnc, permY_permEnc]⟩

theorem permEnc_mem_cpermLang {m : ℕ} (hm : 1 ≤ m) (X : Fin m × Fin m → ℂ) (Y : ℂ) :
    permEnc m X Y ∈ cpermLang (m * m + 1) ↔ cperLang m X Y := by
  constructor
  · rintro ⟨m', -, he, h⟩
    have hmm : m' = m := Nat.mul_self_inj.1 (Nat.add_right_cancel he).symm
    subst hmm
    rwa [permXC_permEnc, permYC_permEnc] at h
  · intro h
    exact ⟨m, hm, rfl, by rwa [permXC_permEnc, permYC_permEnc]⟩

/-- The coordinates `(X, Y)` among the inputs `(X, Y, z)`. -/
def encMap (m : ℕ) (β : Type) : Fin (m * m + 1) → (Fin m × Fin m) ⊕ Unit ⊕ β :=
  Fin.append (fun i => Sum.inl (finProdFinEquiv.symm i)) (fun _ => Sum.inr (Sum.inl ()))

theorem inp3_comp_encMap {m : ℕ} {β : Type} (X : Fin m × Fin m → ℝ) (Y : ℝ) (z : β → ℝ) :
    inp3 X Y z ∘ encMap m β = permEnc m X Y := by
  rw [encMap, comp_finAppend]
  rfl

theorem cinp3_comp_encMap {m : ℕ} {β : Type} (X : Fin m × Fin m → ℂ) (Y : ℂ) (z : β → ℂ) :
    cinp3 X Y z ∘ encMap m β = permEnc m X Y := by
  rw [encMap, comp_finAppend]
  rfl

/-- The renaming of the inputs `Fin (m² + 1 + K)` of an unrolled `NP` machine. -/
def npMap (m K : ℕ) : Fin (m * m + 1 + K) → (Fin m × Fin m) ⊕ Unit ⊕ Fin K :=
  Fin.append (encMap m (Fin K)) (fun j => Sum.inr (Sum.inr j))

theorem inp3_comp_npMap {m K : ℕ} (X : Fin m × Fin m → ℝ) (Y : ℝ) (z : Fin K → ℝ) :
    inp3 X Y z ∘ npMap m K = Fin.append (permEnc m X Y) z := by
  rw [npMap, comp_finAppend, inp3_comp_encMap]
  rfl

theorem cinp3_comp_npMap {m K : ℕ} (X : Fin m × Fin m → ℂ) (Y : ℂ) (z : Fin K → ℂ) :
    cinp3 X Y z ∘ npMap m K = Fin.append (permEnc m X Y) z := by
  rw [npMap, comp_finAppend, cinp3_comp_encMap]
  rfl

/-- The renaming of the inputs `Fin (m² + 1 + k + l)` of an unrolled `Σ₂` machine. -/
def s2Map (m k l : ℕ) : Fin (m * m + 1 + k + l) → (Fin m × Fin m) ⊕ Unit ⊕ Fin k ⊕ Fin l :=
  Fin.append (Fin.append (encMap m (Fin k ⊕ Fin l)) (fun j => Sum.inr (Sum.inr (Sum.inl j))))
    (fun j => Sum.inr (Sum.inr (Sum.inr j)))

theorem inp4_comp_s2Map {m k l : ℕ} (X : Fin m × Fin m → ℝ) (Y : ℝ) (z : Fin k → ℝ)
    (u : Fin l → ℝ) :
    inp4 X Y z u ∘ s2Map m k l = Fin.append (Fin.append (permEnc m X Y) z) u := by
  rw [s2Map, comp_finAppend, comp_finAppend,
    show inp4 X Y z u = inp3 X Y (Sum.elim z u) from rfl, inp3_comp_encMap]
  rfl

/-- The renaming of the inputs `Fin (m² + 1)` of a verifier, for inputs on
`Option (Fin m × Fin m)` (`Y` is `none`). -/
def bipMap (m : ℕ) : Fin (m * m + 1) → Option (Fin m × Fin m) :=
  Fin.append (fun i => some (finProdFinEquiv.symm i)) (fun _ => none)

theorem comp_bipMap {m : ℕ} (w : Option (Fin m × Fin m) → ℝ) :
    w ∘ bipMap m = permEnc m (w ∘ some) (w none) := by
  rw [bipMap, comp_finAppend]
  rfl

/-! ## The case `m = 0`

`per₀ = 1`, so the slices at `m = 0` are conditions on `Y` alone, decided by small trees. -/

theorem eval_per_zero (X : Fin 0 × Fin 0 → ℝ) : eval X (per 0) = 1 := by
  simp [per]

theorem eval_cper_zero (X : Fin 0 × Fin 0 → ℂ) : eval X (map (algebraMap ℝ ℂ) (per 0)) = 1 := by
  simp [per]

/-- Compute `y - 1` and branch on its sign: `bn`, `bz`, `bp`. -/
def zeroTree {ι : Type} (y : ι) (bn bz bp : Bool) : Tree ι :=
  .comp .sub (.input y) (.const 1)
    (.test .eq (.val 0) (.leaf bz) (.test .ge (.val 0) (.leaf bp) (.leaf bn)))

theorem zeroTree_depth {ι : Type} (y : ι) (bn bz bp : Bool) :
    (zeroTree y bn bz bp).depth = 4 := rfl

theorem zeroTree_accepts {ι : Type} (y : ι) (bn bz bp : Bool) (Q : ℝ → Prop)
    (hn : ∀ v : ℝ, v < 1 → (bn = true ↔ Q v)) (hz : bz = true ↔ Q 1)
    (hp : ∀ v : ℝ, 1 < v → (bp = true ↔ Q v)) (w : ι → ℝ) :
    (zeroTree y bn bz bp).Accepts w ↔ Q (w y) := by
  simp only [Tree.Accepts, Tree.run, zeroTree, Tree.runFrom, TArg.eval, List.nil_append,
    List.getD_cons_zero, TestKind.holds]
  rcases lt_trichotomy (w y) 1 with h | h | h
  · rw [ite_eq_right (sub_ne_zero.2 h.ne), ite_eq_right (not_le.2 (by linarith)), Option.some_inj]
    exact hn _ h
  · rw [ite_eq_left (sub_eq_zero.2 h), Option.some_inj, h]
    exact hz
  · rw [ite_eq_right (sub_ne_zero.2 h.ne'), ite_eq_left (by linarith), Option.some_inj]
    exact hp _ h

/-- Small trees for a slice at `m = 0` that depends on the sign of `Y - 1` only. -/
theorem zero_trees (Q : (Fin 0 × Fin 0 → ℝ) → ℝ → Prop) (Q' : ℝ → Prop)
    (hQ : ∀ X Y, Q X Y ↔ Q' Y) (bn bz bp : Bool)
    (hn : ∀ v : ℝ, v < 1 → (bn = true ↔ Q' v)) (hz : bz = true ↔ Q' 1)
    (hp : ∀ v : ℝ, 1 < v → (bp = true ↔ Q' v)) (γ : Type) :
    ∃ T₀ : Tree ((Fin 0 × Fin 0) ⊕ Unit ⊕ γ), T₀.depth ≤ 4 ∧
      ∀ X Y z, T₀.Accepts (inp3 X Y z) ↔ Q X Y :=
  ⟨zeroTree (Sum.inr (Sum.inl ())) bn bz bp, le_of_eq rfl, fun X Y z => by
    rw [zeroTree_accepts _ _ _ _ Q' hn hz hp, hQ]
    rfl⟩

theorem perLang_zero_trees (r : PerRel) (γ : Type) :
    ∃ T₀ : Tree ((Fin 0 × Fin 0) ⊕ Unit ⊕ γ), T₀.depth ≤ 4 ∧
      ∀ X Y z, T₀.Accepts (inp3 X Y z) ↔ perLang r 0 X Y := by
  have hQ : ∀ X Y, perLang r 0 X Y ↔ r.holds Y 1 := fun X Y => by
    rw [perLang, eval_per_zero]
  cases r
  · exact zero_trees _ _ hQ false true false (fun v hv => by simp [PerRel.holds, hv.ne])
      (by simp [PerRel.holds]) (fun v hv => by simp [PerRel.holds, hv.ne']) γ
  · exact zero_trees _ _ hQ true true false (fun v hv => by simp [PerRel.holds, hv.le])
      (by simp [PerRel.holds]) (fun v hv => by simp [PerRel.holds, hv]) γ
  · exact zero_trees _ _ hQ false true true (fun v hv => by simp [PerRel.holds, hv])
      (by simp [PerRel.holds]) (fun v hv => by simp [PerRel.holds, hv.le]) γ
  · exact zero_trees _ _ hQ true false false (fun v hv => by simp [PerRel.holds, hv])
      (by simp [PerRel.holds]) (fun v hv => by simp [PerRel.holds, hv.le]) γ
  · exact zero_trees _ _ hQ false false true (fun v hv => by simp [PerRel.holds, hv.le])
      (by simp [PerRel.holds]) (fun v hv => by simp [PerRel.holds, hv]) γ

theorem ne_zero_trees (γ : Type) :
    ∃ T₀ : Tree ((Fin 0 × Fin 0) ⊕ Unit ⊕ γ), T₀.depth ≤ 4 ∧
      ∀ X Y z, T₀.Accepts (inp3 X Y z) ↔ Y ≠ eval X (per 0) := by
  have hQ : ∀ X Y, Y ≠ eval X (per 0) ↔ Y ≠ 1 := fun X Y => by rw [eval_per_zero]
  exact zero_trees _ _ hQ true false true (fun v hv => by simp [hv.ne]) (by simp)
    (fun v hv => by simp [hv.ne']) γ

/-! ## `NP_ℝ` -/

/-- **Unrolling an `NP_ℝ` machine**: at each input size `n`, a tree of depth `≤ p(n) + 1` on
`(x, z) ∈ ℝ^{n + q(n)}` accepts `(x, z)` for some `z` exactly on `L`. -/
theorem np_unroll {L : Lang} (hL : L ∈ NP_R) :
    ∃ p q : ℕ → ℕ, PolyBounded p ∧ PolyBounded q ∧ ∀ n, ∃ τ : Tree (Fin (n + q n)),
      τ.depth ≤ p n + 1 ∧ ∀ x : Fin n → ℝ, x ∈ L n ↔ ∃ z, τ.Accepts (Fin.append x z) := by
  obtain ⟨M, p, q, hp, hq, hM⟩ := hL
  refine ⟨p, q, hp, hq, fun n => ?_⟩
  obtain ⟨τ, hd, -, hτ⟩ := M.unroll [n, q n] (n + q n) (p n)
  refine ⟨τ, hd, fun x => (hM n x).2.trans (exists_congr fun z => ?_)⟩
  obtain ⟨o, ho⟩ := (hM n x).1 z
  have h1 : τ.run (Fin.append x z) = o := hτ _ o ho
  simp only [Machine.HaltsWith] at ho ⊢
  rw [Tree.Accepts, h1, ho, Option.some_inj]

/-- **`NP_ℝ` gives tree families.**  If `L ∈ NP_ℝ` and, for `m ≥ 1`, the slice of `L` at
`n = m² + 1` is `Q m` (in the coordinates `(X, Y)`), and the slice `Q 0` is decided by small
trees, then trees of polynomial depth decide `Q m` in the existential sense for all `m`. -/
theorem np_family {L : Lang} (hL : L ∈ NP_R) (Q : ∀ m : ℕ, (Fin m × Fin m → ℝ) → ℝ → Prop)
    (hQ : ∀ m, 1 ≤ m → ∀ X Y, permEnc m X Y ∈ L (m * m + 1) ↔ Q m X Y)
    (h0 : ∀ γ : Type, ∃ T₀ : Tree ((Fin 0 × Fin 0) ⊕ Unit ⊕ γ), T₀.depth ≤ 4 ∧
      ∀ X Y z, T₀.Accepts (inp3 X Y z) ↔ Q 0 X Y) :
    ∃ (t k : ℕ → ℕ) (T : ∀ m, Tree ((Fin m × Fin m) ⊕ Unit ⊕ Fin (k m))),
      PolyBounded t ∧ (∀ m, (T m).depth ≤ t m) ∧ ∀ m, ExDecides (T m) (Q m) := by
  obtain ⟨p, q, hp, -, hτ⟩ := np_unroll hL
  have key : ∀ m, ∃ T : Tree ((Fin m × Fin m) ⊕ Unit ⊕ Fin (q (m * m + 1))),
      T.depth ≤ p (m * m + 1) + 5 ∧ ExDecides T (Q m) := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · obtain ⟨T₀, hd, hT₀⟩ := h0 (Fin (q (0 * 0 + 1)))
      exact ⟨T₀, by omega, fun X Y =>
        ⟨fun ⟨z, hz⟩ => (hT₀ X Y z).1 hz, fun h => ⟨0, (hT₀ X Y 0).2 h⟩⟩⟩
    · obtain ⟨τ, hd, hτ'⟩ := hτ (m * m + 1)
      refine ⟨τ.rename (npMap m _), by rw [Tree.depth_rename]; omega, fun X Y => ?_⟩
      rw [← hQ m hm, hτ']
      refine exists_congr fun z => ?_
      rw [Tree.Accepts, Tree.Accepts, Tree.run_rename, inp3_comp_npMap]
  choose T hT hdec using key
  exact ⟨fun m => p (m * m + 1) + 5, fun m => q (m * m + 1), T,
    hp.comp_sq.add (PolyBounded.const 5), hT, hdec⟩

/-! ## `Σ₂^ℝ` -/

/-- **Unrolling a `Σ₂^ℝ` machine.** -/
theorem sigma2_unroll {L : Lang} (hL : L ∈ Sigma2_R) :
    ∃ p q₁ q₂ : ℕ → ℕ, PolyBounded p ∧ PolyBounded q₁ ∧ PolyBounded q₂ ∧ ∀ n,
      ∃ τ : Tree (Fin (n + q₁ n + q₂ n)), τ.depth ≤ p n + 1 ∧ ∀ x : Fin n → ℝ,
        x ∈ L n ↔ ∃ z, ∀ u, τ.Accepts (Fin.append (Fin.append x z) u) := by
  obtain ⟨M, p, q₁, q₂, hp, hq₁, hq₂, hM⟩ := hL
  refine ⟨p, q₁, q₂, hp, hq₁, hq₂, fun n => ?_⟩
  obtain ⟨τ, hd, -, hτ⟩ := M.unroll [n, q₁ n, q₂ n] (n + q₁ n + q₂ n) (p n)
  refine ⟨τ, hd, fun x => (hM n x).2.trans (exists_congr fun z => forall_congr' fun u => ?_)⟩
  obtain ⟨o, ho⟩ := (hM n x).1 z u
  have h1 : τ.run (Fin.append (Fin.append x z) u) = o := hτ _ o ho
  simp only [Machine.HaltsWith] at ho ⊢
  rw [Tree.Accepts, h1, ho, Option.some_inj]

/-- **`Σ₂^ℝ` gives tree families** (as `np_family`, with quantifiers `∃ z ∀ u`). -/
theorem sigma2_family {L : Lang} (hL : L ∈ Sigma2_R)
    (Q : ∀ m : ℕ, (Fin m × Fin m → ℝ) → ℝ → Prop)
    (hQ : ∀ m, 1 ≤ m → ∀ X Y, permEnc m X Y ∈ L (m * m + 1) ↔ Q m X Y)
    (h0 : ∀ γ : Type, ∃ T₀ : Tree ((Fin 0 × Fin 0) ⊕ Unit ⊕ γ), T₀.depth ≤ 4 ∧
      ∀ X Y z, T₀.Accepts (inp3 X Y z) ↔ Q 0 X Y) :
    ∃ (t k l : ℕ → ℕ) (T : ∀ m, Tree ((Fin m × Fin m) ⊕ Unit ⊕ Fin (k m) ⊕ Fin (l m))),
      PolyBounded (fun m => t m + k m + l m) ∧ (∀ m, (T m).depth ≤ t m) ∧
      ∀ m, ExAllDecides (T m) (Q m) := by
  obtain ⟨p, q₁, q₂, hp, hq₁, hq₂, hτ⟩ := sigma2_unroll hL
  have key : ∀ m, ∃ T : Tree ((Fin m × Fin m) ⊕ Unit ⊕ Fin (q₁ (m * m + 1)) ⊕
      Fin (q₂ (m * m + 1))), T.depth ≤ p (m * m + 1) + 5 ∧ ExAllDecides T (Q m) := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · obtain ⟨T₀, hd, hT₀⟩ := h0 (Fin (q₁ (0 * 0 + 1)) ⊕ Fin (q₂ (0 * 0 + 1)))
      exact ⟨T₀, by omega, fun X Y =>
        ⟨fun ⟨z, hz⟩ => (hT₀ X Y (Sum.elim z 0)).1 (hz 0),
          fun h => ⟨0, fun u => (hT₀ X Y (Sum.elim 0 u)).2 h⟩⟩⟩
    · obtain ⟨τ, hd, hτ'⟩ := hτ (m * m + 1)
      refine ⟨τ.rename (s2Map m _ _), by rw [Tree.depth_rename]; omega, fun X Y => ?_⟩
      rw [← hQ m hm, hτ']
      refine exists_congr fun z => forall_congr' fun u => ?_
      rw [Tree.Accepts, Tree.Accepts, Tree.run_rename, inp4_comp_s2Map]
  choose T hT hdec using key
  exact ⟨fun m => p (m * m + 1) + 5, fun m => q₁ (m * m + 1), fun m => q₂ (m * m + 1), T,
    ((hp.comp_sq.add (PolyBounded.const 5)).add hq₁.comp_sq).add hq₂.comp_sq, hT, hdec⟩

/-! ## Complex trees: renaming and the complement -/

/-- Rename the input of a complex operand. -/
def CArg.rename {ι ι' : Type} (f : ι → ι') : CArg ι → CArg ι'
  | .input i => .input (f i)
  | .const c => .const c
  | .val j => .val j

/-- Rename the inputs of a complex tree. -/
def CTree.rename {ι ι' : Type} (f : ι → ι') : CTree ι → CTree ι'
  | .leaf b => .leaf b
  | .comp op a b next => .comp op (a.rename f) (b.rename f) (next.rename f)
  | .test v yes no => .test (v.rename f) (yes.rename f) (no.rename f)

theorem CTree.argEval_rename {ι ι' : Type} (f : ι → ι') (w : ι' → ℂ) (vals : List ℂ)
    (a : CArg ι) : CTree.argEval w vals (a.rename f) = CTree.argEval (w ∘ f) vals a := by
  cases a <;> rfl

@[simp] theorem CTree.depth_rename {ι ι' : Type} (f : ι → ι') (T : CTree ι) :
    (T.rename f).depth = T.depth := by
  induction T with
  | leaf b => rfl
  | comp op a b next ih => simp [CTree.rename, CTree.depth, ih]
  | test v yes no ih₁ ih₂ => simp [CTree.rename, CTree.depth, ih₁, ih₂]

theorem CTree.runFrom_rename {ι ι' : Type} (f : ι → ι') (T : CTree ι) (w : ι' → ℂ)
    (vals : List ℂ) : (T.rename f).runFrom w vals = T.runFrom (w ∘ f) vals := by
  induction T generalizing vals with
  | leaf b => rfl
  | comp op a b next ih =>
    cases op <;> simp only [CTree.rename, CTree.runFrom, CTree.argEval_rename, ih]
  | test v yes no ih₁ ih₂ =>
    simp only [CTree.rename, CTree.runFrom, CTree.argEval_rename, ih₁, ih₂]

theorem CTree.accepts_rename {ι ι' : Type} (f : ι → ι') (T : CTree ι) (w : ι' → ℂ) :
    (T.rename f).Accepts w ↔ T.Accepts (w ∘ f) := by
  rw [CTree.Accepts, CTree.Accepts, CTree.runFrom_rename]

/-- The complement of a complex tree that also accepts on a division by zero: before each
division, the divisor is tested and the tree accepts if it vanishes. -/
def CTree.neg {ι : Type} : CTree ι → CTree ι
  | .leaf b => .leaf (!b)
  | .comp .div a b next => .test b (.leaf true) (.comp .div a b next.neg)
  | .comp op a b next => .comp op a b next.neg
  | .test v yes no => .test v yes.neg no.neg

theorem CTree.runFrom_neg {ι : Type} (w : ι → ℂ) (T : CTree ι) (vals : List ℂ) :
    T.neg.runFrom w vals = some true ↔ T.runFrom w vals ≠ some true := by
  induction T generalizing vals with
  | leaf b => cases b <;> simp [CTree.neg, CTree.runFrom]
  | comp op a b next ih =>
    cases op
    · exact ih _
    · exact ih _
    · exact ih _
    · simp only [CTree.neg, CTree.runFrom]
      split_ifs with h
      · simp
      · exact ih _
  | test v yes no ih₁ ih₂ =>
    simp only [CTree.neg, CTree.runFrom]
    split_ifs
    · exact ih₁ _
    · exact ih₂ _

theorem CTree.accepts_neg {ι : Type} (T : CTree ι) (w : ι → ℂ) :
    T.neg.Accepts w ↔ ¬ T.Accepts w :=
  CTree.runFrom_neg w T []

theorem CTree.depth_neg {ι : Type} (T : CTree ι) : T.neg.depth ≤ 2 * T.depth := by
  induction T with
  | leaf b => simp [CTree.neg, CTree.depth]
  | comp op a b next ih => cases op <;> simp [CTree.neg, CTree.depth] <;> omega
  | test v yes no ih₁ ih₂ => simp only [CTree.neg, CTree.depth]; omega

/-- Compute `y - 1` and accept iff it vanishes. -/
def czeroTree {ι : Type} (y : ι) : CTree ι :=
  .comp .sub (.input y) (.const 1) (.test (.val 0) (.leaf true) (.leaf false))

theorem czeroTree_depth {ι : Type} (y : ι) : (czeroTree y).depth = 3 := rfl

theorem czeroTree_accepts {ι : Type} (y : ι) (w : ι → ℂ) :
    (czeroTree y).Accepts w ↔ w y = 1 := by
  simp [czeroTree, CTree.Accepts, CTree.runFrom, CTree.argEval, sub_eq_zero]

theorem cperLang_zero (X : Fin 0 × Fin 0 → ℂ) (Y : ℂ) : cperLang 0 X Y ↔ Y = 1 := by
  rw [cperLang, eval_cper_zero]

/-! ## `NP_ℂ` and `coNP_ℂ` -/

/-- **Unrolling an `NP_ℂ` machine.** -/
theorem npc_unroll {L : LangC} (hL : L ∈ NP_C) :
    ∃ p q : ℕ → ℕ, PolyBounded p ∧ PolyBounded q ∧ ∀ n, ∃ τ : CTree (Fin (n + q n)),
      τ.depth ≤ p n + 1 ∧ ∀ x : Fin n → ℂ, x ∈ L n ↔ ∃ z, τ.Accepts (Fin.append x z) := by
  obtain ⟨M, p, q, hp, hq, hM⟩ := hL
  refine ⟨p, q, hp, hq, fun n => ?_⟩
  obtain ⟨τ, hd, hτ⟩ := M.unroll [n, q n] (n + q n) (p n)
  refine ⟨τ, hd, fun x => (hM n x).2.trans (exists_congr fun z => ?_)⟩
  obtain ⟨o, ho⟩ := (hM n x).1 z
  rw [CTree.Accepts, hτ _ o ho, ho, Option.some_inj]

/-- **`NP_ℂ` gives tree families** for the graph of the complex permanent. -/
theorem npc_perm_family (h : cpermLang ∈ NP_C) :
    ∃ (t k : ℕ → ℕ) (T : ∀ m, CTree ((Fin m × Fin m) ⊕ Unit ⊕ Fin (k m))),
      PolyBounded t ∧ (∀ m, (T m).depth ≤ t m) ∧
      ∀ m X Y, (∃ z, (T m).Accepts (cinp3 X Y z)) ↔ cperLang m X Y := by
  obtain ⟨p, q, hp, -, hτ⟩ := npc_unroll h
  have key : ∀ m, ∃ T : CTree ((Fin m × Fin m) ⊕ Unit ⊕ Fin (q (m * m + 1))),
      T.depth ≤ p (m * m + 1) + 5 ∧
      ∀ X Y, (∃ z, T.Accepts (cinp3 X Y z)) ↔ cperLang m X Y := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · refine ⟨czeroTree (Sum.inr (Sum.inl ())), by rw [czeroTree_depth]; omega, fun X Y => ?_⟩
      rw [cperLang_zero]
      exact ⟨fun ⟨z, hz⟩ => (czeroTree_accepts _ _).1 hz,
        fun hY => ⟨0, (czeroTree_accepts _ _).2 hY⟩⟩
    · obtain ⟨τ, hd, hτ'⟩ := hτ (m * m + 1)
      refine ⟨τ.rename (npMap m _), by rw [CTree.depth_rename]; omega, fun X Y => ?_⟩
      rw [← permEnc_mem_cpermLang hm, hτ']
      refine exists_congr fun z => ?_
      rw [CTree.accepts_rename, cinp3_comp_npMap]
  choose T hT hdec using key
  exact ⟨fun m => p (m * m + 1) + 5, fun m => q (m * m + 1), T,
    hp.comp_sq.add (PolyBounded.const 5), hT, hdec⟩

/-- **`coNP_ℂ` gives tree families** (universal sense) for the graph of the complex
permanent: the unrolled `NP_ℂ` tree of the complement is complemented with `CTree.neg`. -/
theorem conpc_perm_family (h : cpermLang ∈ coNP_C) :
    ∃ (t k : ℕ → ℕ) (T : ∀ m, CTree ((Fin m × Fin m) ⊕ Unit ⊕ Fin (k m))),
      PolyBounded t ∧ (∀ m, (T m).depth ≤ t m) ∧
      ∀ m X Y, (∀ z, (T m).Accepts (cinp3 X Y z)) ↔ cperLang m X Y := by
  obtain ⟨p, q, hp, -, hτ⟩ := npc_unroll h
  have key : ∀ m, ∃ T : CTree ((Fin m × Fin m) ⊕ Unit ⊕ Fin (q (m * m + 1))),
      T.depth ≤ p (m * m + 1) + p (m * m + 1) + 5 ∧
      ∀ X Y, (∀ z, T.Accepts (cinp3 X Y z)) ↔ cperLang m X Y := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · refine ⟨czeroTree (Sum.inr (Sum.inl ())), by rw [czeroTree_depth]; omega, fun X Y => ?_⟩
      rw [cperLang_zero]
      exact ⟨fun hz => (czeroTree_accepts _ _).1 (hz 0),
        fun hY z => (czeroTree_accepts _ _).2 hY⟩
    · obtain ⟨τ, hd, hτ'⟩ := hτ (m * m + 1)
      refine ⟨τ.neg.rename (npMap m _), ?_, fun X Y => ?_⟩
      · rw [CTree.depth_rename]
        have := CTree.depth_neg τ
        omega
      · rw [← permEnc_mem_cpermLang hm]
        have h1 := hτ' (permEnc m X Y)
        simp only [LangC.compl, Set.mem_compl_iff] at h1
        rw [← not_iff_not, h1, not_forall]
        refine exists_congr fun z => ?_
        rw [CTree.accepts_rename, cinp3_comp_npMap, CTree.accepts_neg, not_not]
  choose T hT hdec using key
  exact ⟨fun m => p (m * m + 1) + p (m * m + 1) + 5, fun m => q (m * m + 1), T,
    (hp.comp_sq.add hp.comp_sq).add (PolyBounded.const 5), hT, hdec⟩

/-! ## Verifier trees: renaming -/

/-- Rename the input of an operand. -/
def TArg.ren {ι ι' : Type} (f : ι → ι') : TArg ι → TArg ι'
  | .input i => .input (f i)
  | .const c => .const c
  | .val j => .val j

theorem TArg.eval_ren {ι ι' : Type} (f : ι → ι') (w : ι' → ℝ) (vals : List ℝ) (a : TArg ι) :
    (a.ren f).eval w vals = a.eval (w ∘ f) vals := by
  cases a <;> rfl

/-- Rename the inputs of a verifier tree. -/
def VTree.rename {ι ι' : Type} (f : ι → ι') : VTree ι → VTree ι'
  | .leaf b => .leaf b
  | .comp op a b next => .comp op (a.ren f) (b.ren f) (next.rename f)
  | .test k v yes no => .test k (v.ren f) (yes.rename f) (no.rename f)
  | .coin c₀ c₁ => .coin (c₀.rename f) (c₁.rename f)
  | .send b next => .send b (next.rename f)
  | .recv r₀ r₁ => .recv (r₀.rename f) (r₁.rename f)

@[simp] theorem VTree.depth_rename {ι ι' : Type} (f : ι → ι') (V : VTree ι) :
    (V.rename f).depth = V.depth := by
  induction V with
  | leaf b => rfl
  | comp op a b next ih => simp [VTree.rename, VTree.depth, ih]
  | test k v yes no ih₁ ih₂ => simp [VTree.rename, VTree.depth, ih₁, ih₂]
  | coin c₀ c₁ ih₀ ih₁ => simp [VTree.rename, VTree.depth, ih₀, ih₁]
  | send b next ih => simp [VTree.rename, VTree.depth, ih]
  | recv r₀ r₁ ih₀ ih₁ => simp [VTree.rename, VTree.depth, ih₀, ih₁]

theorem VTree.runFrom_rename {ι ι' : Type} (f : ι → ι') (V : VTree ι) (w : ι' → ℝ)
    (P : VTree.Prover ι') (r : ℕ → Bool) :
    ∀ vals s j, (V.rename f).runFrom w P r vals s j =
      V.runFrom (w ∘ f) (fun _ => P w) r vals s j := by
  induction V with
  | leaf b => intro vals s j; rfl
  | comp op a b next ih =>
    intro vals s j
    cases op <;> simp only [VTree.rename, VTree.runFrom, TArg.eval_ren, ih]
  | test k v yes no ih₁ ih₂ =>
    intro vals s j
    simp only [VTree.rename, VTree.runFrom, TArg.eval_ren, ih₁, ih₂]
  | coin c₀ c₁ ih₀ ih₁ =>
    intro vals s j
    simp only [VTree.rename, VTree.runFrom, ih₀, ih₁]
  | send b next ih =>
    intro vals s j
    simp only [VTree.rename, VTree.runFrom, ih]
  | recv r₀ r₁ ih₀ ih₁ =>
    intro vals s j
    simp only [VTree.rename, VTree.runFrom, ih₀, ih₁]

/-- The acceptance probability depends only on the depth and on the accepted coin tapes. -/
theorem VTree.accProb_congr {ι ι' : Type} (V₁ : VTree ι) (V₂ : VTree ι') (w₁ : ι → ℝ)
    (w₂ : ι' → ℝ) (P₁ : VTree.Prover ι) (P₂ : VTree.Prover ι') (hd : V₁.depth = V₂.depth)
    (h : ∀ r, V₁.AcceptsWith w₁ P₁ r ↔ V₂.AcceptsWith w₂ P₂ r) :
    V₁.accProb w₁ P₁ = V₂.accProb w₂ P₂ := by
  have key : ∀ (d₁ d₂ : ℕ), d₁ = d₂ → ∀ (A₁ A₂ : (ℕ → Bool) → Prop), (∀ r, A₁ r ↔ A₂ r) →
      ((Finset.univ.filter fun r : Fin d₁ → Bool =>
          A₁ (fun j => if h : j < d₁ then r ⟨j, h⟩ else false)).card : ℝ) / 2 ^ d₁ =
        ((Finset.univ.filter fun r : Fin d₂ → Bool =>
          A₂ (fun j => if h : j < d₂ then r ⟨j, h⟩ else false)).card : ℝ) / 2 ^ d₂ := by
    rintro d₁ d₂ rfl A₁ A₂ hA
    simp_rw [hA]
  exact key _ _ hd _ _ h

theorem VTree.accProb_rename {ι ι' : Type} (f : ι → ι') (V : VTree ι) (w : ι' → ℝ)
    (P : VTree.Prover ι') : (V.rename f).accProb w P = V.accProb (w ∘ f) (fun _ => P w) :=
  VTree.accProb_congr _ _ _ _ _ _ (VTree.depth_rename f V) fun r => by
    rw [VTree.AcceptsWith, VTree.AcceptsWith, VTree.runFrom_rename]

/-- The verifier tree for `m = 0`: accept iff `Y = 1`. -/
def vzeroTree : VTree (Option (Fin 0 × Fin 0)) :=
  .comp .sub (.input none) (.const 1) (.test .eq (.val 0) (.leaf true) (.leaf false))

theorem vzeroTree_depth : vzeroTree.depth = 3 := rfl

theorem vzeroTree_accProb (w : Option (Fin 0 × Fin 0) → ℝ)
    (P : VTree.Prover (Option (Fin 0 × Fin 0))) :
    vzeroTree.accProb w P = if w none = 1 then 1 else 0 := by
  have hA : ∀ r, vzeroTree.AcceptsWith w P r ↔ w none = 1 := by
    intro r
    simp [vzeroTree, VTree.AcceptsWith, VTree.runFrom, TArg.eval, TestKind.holds, sub_eq_zero]
  unfold VTree.accProb
  simp only [hA]
  by_cases h : w none = 1
  · simp only [h, ite_true, Finset.filter_true]
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, vzeroTree_depth]
    norm_num
  · simp [h]

/-! ## `BIP_ℝ` -/

/-- **`BIP_ℝ` gives verifier tree families** for `PERM`. -/
theorem bip_perm_family (h : permLang .eq ∈ BIP_R) :
    ∃ (t : ℕ → ℕ) (V : ∀ m, VTree (Option (Fin m × Fin m))), PolyBounded t ∧
      (∀ m, (V m).depth ≤ t m) ∧
      ∀ m, (V m).DecidesOn {w | w none = eval (w ∘ some) (per m)} univ := by
  obtain ⟨M, p, hp, hM⟩ := h
  have key : ∀ m, ∃ V : VTree (Option (Fin m × Fin m)),
      V.depth ≤ p (m * m + 1) + p (m * m + 1) + 5 ∧
      V.DecidesOn {w | w none = eval (w ∘ some) (per m)} univ := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · refine ⟨vzeroTree, by rw [vzeroTree_depth]; omega,
        fun w _ => ⟨fun hw => ?_, fun hw P => ?_⟩⟩
      · have h1 : w none = 1 := hw.trans (eval_per_zero _)
        exact ⟨fun _ _ => true, by rw [vzeroTree_accProb, ite_eq_left h1]; norm_num⟩
      · have h1 : w none ≠ 1 := fun h1 => hw (h1.trans (eval_per_zero _).symm)
        rw [vzeroTree_accProb, ite_eq_right h1]
        norm_num
    · obtain ⟨V₀, hd, hV₀⟩ := M.unroll_bool (m * m + 1) (p (m * m + 1))
      refine ⟨V₀.rename (bipMap m), by rw [VTree.depth_rename]; omega, fun w _ => ?_⟩
      have hmem : w ∈ {w : Option (Fin m × Fin m) → ℝ | w none = eval (w ∘ some) (per m)} ↔
          w ∘ bipMap m ∈ permLang .eq (m * m + 1) := by
        rw [comp_bipMap, permEnc_mem_permLang .eq hm]
        rfl
      obtain ⟨hhalt, hin, hout⟩ := hM (m * m + 1) (w ∘ bipMap m)
      refine ⟨fun hw => ?_, fun hw P => ?_⟩
      · obtain ⟨RP, hRP, hacc⟩ := hin (hmem.1 hw)
        refine ⟨fun _ s => decide (RP (w ∘ bipMap m)
          (s.map fun p => (p.1, if p.2 then 1 else 0)) ≠ 0), ?_⟩
        rw [VTree.accProb_rename, hV₀ _ hhalt RP hRP]
        exact hacc
      · let RP : RProver (m * m + 1) := fun _ s =>
          if P w (s.map fun p => (p.1, decide (p.2 ≠ 0))) then 1 else 0
        have hRP : ∀ s, RP (w ∘ bipMap m) s ∈ ({0, 1} : Set ℝ) := fun s => by
          simp only [RP]
          split_ifs <;> simp
        have hP := hout (fun h => hw (hmem.2 h)) RP hRP
        rw [← hV₀ _ hhalt RP hRP] at hP
        rw [VTree.accProb_rename]
        convert hP using 2
        funext y s
        have hs : ((s.map fun p => (p.1, if p.2 then (1 : ℝ) else 0)).map
            fun p => (p.1, decide (p.2 ≠ 0))) = s := by
          rw [List.map_map]
          conv_rhs => rw [← List.map_id s]
          refine List.map_congr_left fun p _ => ?_
          rcases p with ⟨a, b⟩
          cases b <;> simp
        simp only [RP, hs]
        cases P w s <;> simp
  choose V hV hdec using key
  exact ⟨fun m => p (m * m + 1) + p (m * m + 1) + 5, V,
    (hp.comp_sq.add hp.comp_sq).add (PolyBounded.const 5), hV, hdec⟩

end ClassSep
