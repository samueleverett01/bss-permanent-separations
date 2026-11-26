import ClassSeparations.Basic.TreeOps
import ClassSeparations.Interaction.Boolean
import ClassSeparations.Interaction.Cited

/-!
# Constant-round Arthur–Merlin proofs (§7.2, Definition 7.5, Lemma 7.7, Theorem 7.8)

**Definition 7.5.**  A `c`-round public-coin protocol on inputs `x ∈ ℝⁿ`: in round `i` Arthur
sends `rᵢ ∈ {0,1}^ρ` (fair coins) and Merlin answers `zᵢ ∈ ℝ^μ`; then a tree `V` of depth `t`
accepts or rejects `(x, r₁, z₁, …, r_c, z_c)`.  With `val_{c+1}(x, h) = [V accepts (x, h)]` and
`valᵢ(x, h) = 𝔼_{rᵢ} sup_{zᵢ} val_{i+1}(x, h, rᵢ, zᵢ)`, the protocol decides `L` if
`val₁(x) ≥ 2/3` on `L` and `val₁(x) ≤ 1/3` off `L`.

The coin bits are fed to `V` as real inputs `0` or `1`.  Rounds are numbered `0, …, c-1`.

**Lemma 7.7 (fixing the coins).**  There are multisets `R₁, …, R_c ⊆ {0,1}^ρ` of sizes
`qᵢ ≥ 2` with `q₁⋯q_c ≤ A^{3^c}`, `A = O(c²(n + cμ)μ(ρc + t))`, such that the sampled values
`val'` (expectations replaced by averages over `Rᵢ`) satisfy `|val'₁(x) - val₁(x)| ≤ 1/8`.

**Equation (12).**  `val'₁(x) ≥ 1/2` exactly when, for some strategy tree, at least half of
the sampled leaves accept; this is decided by a tree `T` of depth `O(P₁ t)` on inputs `(x, z)`
with at most `2μP₁` certificate coordinates.

**Theorem 7.8.**  A public-coin protocol with `c_m` rounds, real messages and a verifier running
in time polynomial in `m` that decides `{Y = per_m(X)}` has `c_m ≥ Ω(log log m)` rounds.
-/

noncomputable section

open MvPolynomial Set Filter Topology Classical

namespace ClassSep

/-- The inputs of the verifier of a `c`-round protocol: `x`, the coins, and the messages. -/
abbrev AMInput (σ : Type) (c ρ μ : ℕ) := σ ⊕ (Fin c × Fin ρ) ⊕ (Fin c × Fin μ)

/-- A `c`-round public-coin protocol on inputs `x : σ → ℝ`. -/
structure AMProtocol (σ : Type) where
  c : ℕ
  ρ : ℕ
  μ : ℕ
  V : Tree (AMInput σ c ρ μ)

namespace AMProtocol

variable {σ : Type} (Pr : AMProtocol σ)

/-- The input of the verifier tree. -/
def verInput (x : σ → ℝ) (r : Fin Pr.c → Fin Pr.ρ → Bool) (z : Fin Pr.c → Fin Pr.μ → ℝ) :
    AMInput σ Pr.c Pr.ρ Pr.μ → ℝ :=
  Sum.elim x (Sum.elim (fun p => if r p.1 p.2 then 1 else 0) (fun p => z p.1 p.2))

/-- `val_{i}` of (10), with rounds `i, i+1, …, c-1` still to be played; the entries of `r` and
`z` for rounds `≥ i` are ignored. -/
def valFrom (x : σ → ℝ) (i : ℕ) (r : Fin Pr.c → Fin Pr.ρ → Bool)
    (z : Fin Pr.c → Fin Pr.μ → ℝ) : ℝ :=
  if h : i < Pr.c then
    (2 ^ Pr.ρ : ℝ)⁻¹ * ∑ b : Fin Pr.ρ → Bool,
      ⨆ y : Fin Pr.μ → ℝ, valFrom x (i + 1) (Function.update r ⟨i, h⟩ b)
        (Function.update z ⟨i, h⟩ y)
  else if Pr.V.Accepts (Pr.verInput x r z) then 1 else 0
termination_by Pr.c - i

/-- `val₁(x)`, the largest acceptance probability over Merlin's strategies. -/
def val (x : σ → ℝ) : ℝ := Pr.valFrom x 0 (fun _ _ => false) (fun _ _ => 0)

/-- The protocol decides `L`. -/
def Decides (L : Set (σ → ℝ)) : Prop :=
  ∀ x, (x ∈ L → 2 / 3 ≤ Pr.val x) ∧ (x ∉ L → Pr.val x ≤ 1 / 3)

/-- The sampled values (11): expectations over coins replaced by averages over the lists
`R i` (with multiplicities). -/
def sValFrom (R : Fin Pr.c → List (Fin Pr.ρ → Bool)) (x : σ → ℝ) (i : ℕ)
    (r : Fin Pr.c → Fin Pr.ρ → Bool) (z : Fin Pr.c → Fin Pr.μ → ℝ) : ℝ :=
  if h : i < Pr.c then
    ((R ⟨i, h⟩).length : ℝ)⁻¹ * ((R ⟨i, h⟩).map fun b =>
      ⨆ y : Fin Pr.μ → ℝ, sValFrom R x (i + 1) (Function.update r ⟨i, h⟩ b)
        (Function.update z ⟨i, h⟩ y)).sum
  else if Pr.V.Accepts (Pr.verInput x r z) then 1 else 0
termination_by Pr.c - i

/-- `val'₁(x)`. -/
def sVal (R : Fin Pr.c → List (Fin Pr.ρ → Bool)) (x : σ → ℝ) : ℝ :=
  Pr.sValFrom R x 0 (fun _ _ => false) (fun _ _ => 0)

end AMProtocol

/-! ## Auxiliary constructions

* The tree `T` of equation (12) runs `V` on every sampled leaf in turn and counts the accepting
  runs (`AMAux.thr`; a division by zero counts as a rejection, `AMAux.branch`).  Its
  strategy-tree coordinates are laid out round by round (`AMAux.sD`), and `AMAux.cnt_spec`
  proves equation (12) by downward induction on the round.
* Lemma 7.7: `AMAux.error_bound` (accumulated error), `AMAux.exists_good_sample` (Hoeffding's
  inequality for uniform samples, from Hoeffding's lemma in Mathlib, and the union bound),
  `AMAux.family_bound` (the counting bound on `|𝔉ᵢ|`: `g_{x,h}` is determined by the coins and
  the sign vectors realized on the fiber over `(x, z)` by the cell polynomials of the sampled
  leaves, Lemma 2.5) and `AMAux.union_bound_arith` (the choice `qᵢ = A P_{i+1}²`).
* Theorem 7.8: degenerate protocols (`ρ = 0` or `μ = 0`) are padded (`AMAux.pad`); the case
  `c = 0` needs no coins. -/

namespace AMAux

variable {ι : Type}

/-! ### Running a tree and branching on its outcome -/

/-- Run `T`; at the accepting leaves continue with `A`, at the rejecting leaves and before a
division by zero continue with `B`.  `q` is the number of values computed so far. -/
def branch : Tree ι → Tree ι → Tree ι → ℕ → Tree ι
  | .leaf true, A, _, q => A.shift q
  | .leaf false, _, B, q => B.shift q
  | .comp .add a b next, A, B, q => .comp .add a b (branch next A B (q + 1))
  | .comp .sub a b next, A, B, q => .comp .sub a b (branch next A B (q + 1))
  | .comp .mul a b next, A, B, q => .comp .mul a b (branch next A B (q + 1))
  | .comp .div a b next, A, B, q =>
      .test .eq b (B.shift q) (.comp .div a b (branch next A B (q + 1)))
  | .test k v yes no, A, B, q => .test k v (branch yes A B q) (branch no A B q)

theorem runFrom_shift' (T : Tree ι) (w : ι → ℝ) (vals : List ℝ) :
    (T.shift vals.length).runFrom w vals = T.run w := by
  have h := Tree.runFrom_shift T w vals []
  rwa [List.append_nil] at h

theorem runFrom_branch (T A B : Tree ι) (w : ι → ℝ) (q : ℕ) (vals : List ℝ)
    (hq : vals.length = q) :
    (branch T A B q).runFrom w vals =
      if T.runFrom w vals = some true then A.run w else B.run w := by
  induction T generalizing q vals with
  | leaf b =>
    subst hq
    cases b <;> simp [branch, Tree.runFrom, runFrom_shift']
  | comp op a b next ih =>
    have hq' : ∀ x : ℝ, (vals ++ [x]).length = q + 1 := by simp [hq]
    cases op
    · simp only [branch, Tree.runFrom]; exact ih _ _ (hq' _)
    · simp only [branch, Tree.runFrom]; exact ih _ _ (hq' _)
    · simp only [branch, Tree.runFrom]; exact ih _ _ (hq' _)
    · simp only [branch, Tree.runFrom, TestKind.holds]
      by_cases hy : TArg.eval w vals b = 0
      · subst hq; simp [hy, runFrom_shift']
      · simp only [hy, ite_false]
        exact ih _ _ (hq' _)
  | test k v yes no ih₁ ih₂ =>
    simp only [branch, Tree.runFrom]
    by_cases hk : k.holds (TArg.eval w vals v)
    · simp only [hk, ite_true]; exact ih₁ _ _ hq
    · simp only [hk, ite_false]; exact ih₂ _ _ hq

theorem depth_branch (T A B : Tree ι) (q : ℕ) :
    (branch T A B q).depth ≤ 2 * T.depth + max A.depth B.depth := by
  induction T generalizing q with
  | leaf b => cases b <;> simp [branch, Tree.depth] <;> omega
  | comp op a b next ih =>
    have := ih (q + 1)
    cases op <;> simp [branch, Tree.depth] <;> omega
  | test k v yes no ih₁ ih₂ =>
    have h₁ := ih₁ q
    have h₂ := ih₂ q
    simp only [branch, Tree.depth]
    omega

/-- A tree that runs the trees of the list in turn and accepts when at least `k` of them
accept. -/
def thr : List (Tree ι) → ℕ → Tree ι
  | [], k => .leaf (decide (k = 0))
  | T :: Ts, k => branch T (thr Ts (k - 1)) (thr Ts k) 0

theorem run_thr (Ts : List (Tree ι)) (k : ℕ) (w : ι → ℝ) :
    (thr Ts k).run w = some (decide (k ≤ Ts.countP fun T => T.run w = some true)) := by
  induction Ts generalizing k with
  | nil => simp [thr, Tree.run, Tree.runFrom]
  | cons T Ts ih =>
    rw [thr, Tree.run, runFrom_branch T _ _ w 0 [] rfl, List.countP_cons]
    by_cases hT : T.run w = some true
    · have hT' : T.runFrom w [] = some true := hT
      simp only [hT', ite_true, ih]
      simp only [hT, decide_true, ite_true, Option.some.injEq, decide_eq_decide]
      omega
    · have hT' : ¬ T.runFrom w [] = some true := hT
      simp only [hT', ite_false, ih]
      simp [hT]

theorem depth_thr (Ts : List (Tree ι)) (k : ℕ) :
    (thr Ts k).depth ≤ 2 * (Ts.map Tree.depth).sum + 1 := by
  induction Ts generalizing k with
  | nil => simp [thr, Tree.depth]
  | cons T Ts ih =>
    have h := depth_branch T (thr Ts (k - 1)) (thr Ts k) 0
    have h1 := ih (k - 1)
    have h2 := ih k
    simp only [thr, List.map_cons, List.sum_cons]
    omega




end AMAux

namespace AMAux

/-! ### Strategy trees -/

section Strategy

variable {σ : Type} (Pr : AMProtocol σ) (R : Fin Pr.c → List (Fin Pr.ρ → Bool))

/-- The number of reals of a strategy tree for the rounds `i, …, c-1`. -/
def sD (i : ℕ) : ℕ :=
  if h : i < Pr.c then (R ⟨i, h⟩).length * (Pr.μ + sD (i + 1)) else 0
termination_by Pr.c - i

/-- The number of sampled leaves below round `i`: `qᵢ ⋯ q_{c-1}`. -/
def sP (i : ℕ) : ℕ :=
  if h : i < Pr.c then (R ⟨i, h⟩).length * sP (i + 1) else 1
termination_by Pr.c - i

theorem sD_succ (i : ℕ) (h : i < Pr.c) :
    sD Pr R i = (R ⟨i, h⟩).length * (Pr.μ + sD Pr R (i + 1)) := by
  rw [sD, dite_eq_left h]

theorem sD_of_le (i : ℕ) (h : Pr.c ≤ i) : sD Pr R i = 0 := by
  rw [sD, dite_eq_right (by omega)]

theorem sP_succ (i : ℕ) (h : i < Pr.c) : sP Pr R i = (R ⟨i, h⟩).length * sP Pr R (i + 1) := by
  rw [sP, dite_eq_left h]

theorem sP_of_le (i : ℕ) (h : Pr.c ≤ i) : sP Pr R i = 1 := by
  rw [sP, dite_eq_right (by omega)]

theorem sP_eq_prod (i : ℕ) :
    sP Pr R i = ∏ j ∈ Finset.univ.filter (fun j : Fin Pr.c => i ≤ j.val), (R j).length := by
  by_cases h : i < Pr.c
  · rw [sP_succ Pr R i h, sP_eq_prod (i + 1)]
    have hs : Finset.univ.filter (fun j : Fin Pr.c => i ≤ j.val) =
        insert ⟨i, h⟩ (Finset.univ.filter (fun j : Fin Pr.c => i + 1 ≤ j.val)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
      omega
    rw [hs, Finset.prod_insert (by simp)]
  · rw [sP_of_le Pr R i (by omega)]
    symm
    apply Finset.prod_eq_one
    intro j hj
    simp only [Finset.mem_filter] at hj
    omega
termination_by Pr.c - i

theorem sP_zero : sP Pr R 0 = ∏ j, (R j).length := by
  rw [sP_eq_prod]
  congr 1
  ext j
  simp

theorem sP_pos (hR : ∀ i, 0 < (R i).length) (i : ℕ) : 0 < sP Pr R i := by
  rw [sP_eq_prod]
  exact Finset.prod_pos fun j _ => hR j

theorem sD_bound (hR : ∀ i, 2 ≤ (R i).length) (i : ℕ) :
    sD Pr R i + 2 * Pr.μ ≤ 2 * Pr.μ * sP Pr R i := by
  by_cases h : i < Pr.c
  · rw [sD_succ Pr R i h, sP_succ Pr R i h]
    have ih := sD_bound hR (i + 1)
    have hq := hR ⟨i, h⟩
    generalize (R ⟨i, h⟩).length = q at *
    generalize sD Pr R (i + 1) = D at *
    generalize sP Pr R (i + 1) = P at *
    nlinarith
  · rw [sD_of_le Pr R i (by omega), sP_of_le Pr R i (by omega)]
    omega
termination_by Pr.c - i

/-- The inputs `(x, z, S)` of the trees below: `x`, a history `z` of messages and a strategy
tree `S`. -/
def stInput (x : σ → ℝ) (z : Fin Pr.c → Fin Pr.μ → ℝ) {N : ℕ} (S : Fin N → ℝ) :
    σ ⊕ (Fin Pr.c × Fin Pr.μ) ⊕ Fin N → ℝ :=
  Sum.elim x (Sum.elim (fun p => z p.1 p.2) S)

/-- The operands replacing the inputs of `V` at a leaf with coins `r`. -/
def leafArg (r : Fin Pr.c → Fin Pr.ρ → Bool) {N : ℕ} :
    AMInput σ Pr.c Pr.ρ Pr.μ → TArg (σ ⊕ (Fin Pr.c × Fin Pr.μ) ⊕ Fin N) :=
  Sum.elim (fun s => .input (.inl s))
    (Sum.elim (fun p => .const (if r p.1 p.2 then 1 else 0)) (fun p => .input (.inr (.inl p))))

/-- Position of the message of round `i` for the `a`-th element of `Rᵢ` in a strategy tree. -/
def msgIdx (i : ℕ) (h : i < Pr.c) (a : Fin (R ⟨i, h⟩).length) (k : Fin Pr.μ) :
    Fin (sD Pr R i) :=
  Fin.cast (sD_succ Pr R i h).symm (finProdFinEquiv (a, Fin.castAdd (sD Pr R (i + 1)) k))

/-- Position of the coordinates of the subtree for the `a`-th element of `Rᵢ`. -/
def subIdx (i : ℕ) (h : i < Pr.c) (a : Fin (R ⟨i, h⟩).length) (d : Fin (sD Pr R (i + 1))) :
    Fin (sD Pr R i) :=
  Fin.cast (sD_succ Pr R i h).symm (finProdFinEquiv (a, Fin.natAdd Pr.μ d))

/-- The renaming of inputs from round `i + 1` to round `i`, for the `a`-th element of `Rᵢ`. -/
def stepMap (i : ℕ) (h : i < Pr.c) (a : Fin (R ⟨i, h⟩).length) :
    σ ⊕ (Fin Pr.c × Fin Pr.μ) ⊕ Fin (sD Pr R (i + 1)) →
      σ ⊕ (Fin Pr.c × Fin Pr.μ) ⊕ Fin (sD Pr R i) :=
  Sum.elim Sum.inl (Sum.elim
    (fun p => if p.1 = ⟨i, h⟩ then .inr (.inr (msgIdx Pr R i h a p.2)) else .inr (.inl p))
    (fun d => .inr (.inr (subIdx Pr R i h a d))))

/-- The copies of `V`, one for each sampled leaf below round `i`. -/
def LT (i : ℕ) (r : Fin Pr.c → Fin Pr.ρ → Bool) :
    List (Tree (σ ⊕ (Fin Pr.c × Fin Pr.μ) ⊕ Fin (sD Pr R i))) :=
  if h : i < Pr.c then
    (List.finRange (R ⟨i, h⟩).length).flatMap fun a =>
      (LT (i + 1) (Function.update r ⟨i, h⟩ (R ⟨i, h⟩)[a])).map
        (Tree.rename (stepMap Pr R i h a))
  else [Pr.V.subst (leafArg Pr r) 0]
termination_by Pr.c - i

theorem LT_succ (i : ℕ) (h : i < Pr.c) (r : Fin Pr.c → Fin Pr.ρ → Bool) :
    LT Pr R i r = (List.finRange (R ⟨i, h⟩).length).flatMap fun a =>
      (LT Pr R (i + 1) (Function.update r ⟨i, h⟩ (R ⟨i, h⟩)[a])).map
        (Tree.rename (stepMap Pr R i h a)) := by
  rw [LT, dite_eq_left h]

theorem LT_of_le (i : ℕ) (h : Pr.c ≤ i) (r : Fin Pr.c → Fin Pr.ρ → Bool) :
    LT Pr R i r = [Pr.V.subst (leafArg Pr r) 0] := by
  rw [LT, dite_eq_right (by omega)]

theorem length_LT (i : ℕ) (r : Fin Pr.c → Fin Pr.ρ → Bool) :
    (LT Pr R i r).length = sP Pr R i := by
  by_cases h : i < Pr.c
  · rw [LT_succ Pr R i h, sP_succ Pr R i h, List.length_flatMap]
    simp only [List.length_map, length_LT (i + 1)]
    rw [← Fin.sum_univ_def]
    simp
  · rw [LT_of_le Pr R i (by omega), sP_of_le Pr R i (by omega)]
    rfl
termination_by Pr.c - i

theorem depth_LT (i : ℕ) (r : Fin Pr.c → Fin Pr.ρ → Bool) :
    ∀ T ∈ LT Pr R i r, T.depth = Pr.V.depth := by
  by_cases h : i < Pr.c
  · rw [LT_succ Pr R i h]
    intro T hT
    simp only [List.mem_flatMap, List.mem_map] at hT
    obtain ⟨a, -, T', hT', rfl⟩ := hT
    rw [Tree.depth_rename]
    exact depth_LT (i + 1) _ T' hT'
  · rw [LT_of_le Pr R i (by omega)]
    intro T hT
    rw [List.mem_singleton] at hT
    subst hT
    exact Tree.depth_subst _ _ _
termination_by Pr.c - i

/-- The number of accepting sampled leaves below round `i`. -/
def cnt (x : σ → ℝ) (i : ℕ) (r : Fin Pr.c → Fin Pr.ρ → Bool) (z : Fin Pr.c → Fin Pr.μ → ℝ)
    (S : Fin (sD Pr R i) → ℝ) : ℕ :=
  (LT Pr R i r).countP fun T => T.run (stInput Pr x z S) = some true

theorem cnt_le (x : σ → ℝ) (i : ℕ) (r : Fin Pr.c → Fin Pr.ρ → Bool)
    (z : Fin Pr.c → Fin Pr.μ → ℝ) (S : Fin (sD Pr R i) → ℝ) : cnt Pr R x i r z S ≤ sP Pr R i := by
  rw [← length_LT Pr R i r]
  exact List.countP_le_length

theorem stInput_comp_stepMap (x : σ → ℝ) (i : ℕ) (h : i < Pr.c) (a : Fin (R ⟨i, h⟩).length)
    (z : Fin Pr.c → Fin Pr.μ → ℝ) (S : Fin (sD Pr R i) → ℝ) :
    stInput Pr x z S ∘ stepMap Pr R i h a =
      stInput Pr x (Function.update z ⟨i, h⟩ fun k => S (msgIdx Pr R i h a k))
        (S ∘ subIdx Pr R i h a) := by
  funext p
  rcases p with s | ⟨j, k⟩ | d
  · rfl
  · by_cases hj : j = ⟨i, h⟩
    · subst hj
      simp [stepMap, stInput]
    · simp [stepMap, stInput, hj]
  · rfl

theorem cnt_succ (x : σ → ℝ) (i : ℕ) (h : i < Pr.c) (r : Fin Pr.c → Fin Pr.ρ → Bool)
    (z : Fin Pr.c → Fin Pr.μ → ℝ) (S : Fin (sD Pr R i) → ℝ) :
    cnt Pr R x i r z S = ∑ a : Fin (R ⟨i, h⟩).length,
      cnt Pr R x (i + 1) (Function.update r ⟨i, h⟩ (R ⟨i, h⟩)[a])
        (Function.update z ⟨i, h⟩ fun k => S (msgIdx Pr R i h a k)) (S ∘ subIdx Pr R i h a) := by
  rw [cnt, LT_succ Pr R i h, List.countP_flatMap, ← Fin.sum_univ_def]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Function.comp_apply, List.countP_map, cnt]
  congr 1
  funext T
  simp only [Function.comp_apply, Tree.run_rename, stInput_comp_stepMap]

theorem leaf_run (x : σ → ℝ) (r : Fin Pr.c → Fin Pr.ρ → Bool) (z : Fin Pr.c → Fin Pr.μ → ℝ)
    {N : ℕ} (S : Fin N → ℝ) :
    (Pr.V.subst (leafArg Pr r) 0).run (stInput Pr x z S) = Pr.V.run (Pr.verInput x r z) := by
  have h := Tree.runFrom_subst (leafArg Pr r (N := N)) (stInput Pr x z S) []
    (by rintro (s | p | p) <;> trivial) Pr.V []
  simp only [List.nil_append, List.length_nil] at h
  rw [Tree.run, h, Tree.run]
  congr 1
  funext p
  rcases p with s | p | p <;> rfl

/-- A function with values in `N⁻¹ {0, …, N}` attains its supremum. -/
theorem exists_eq_ciSup {α : Type} [Nonempty α] (f : α → ℝ) (N : ℕ)
    (hf : ∀ y, ∃ k : ℕ, k ≤ N ∧ (k : ℝ) = N * f y) (hN : 0 < N) :
    BddAbove (range f) ∧ ∃ y, f y = ⨆ y, f y := by
  have hfin : (range f).Finite := by
    refine ((Set.finite_Iic N).image fun k : ℕ => (k : ℝ) / N).subset ?_
    rintro _ ⟨y, rfl⟩
    obtain ⟨k, hk, hky⟩ := hf y
    refine ⟨k, hk, ?_⟩
    show (k : ℝ) / N = f y
    rw [hky]
    field_simp
  refine ⟨hfin.bddAbove, ?_⟩
  obtain ⟨y, hy⟩ := (Set.range_nonempty f).csSup_mem hfin
  exact ⟨y, hy⟩

theorem sum_map_eq_sum_fin {α : Type} (l : List α) (f : α → ℝ) :
    (l.map f).sum = ∑ a : Fin l.length, f l[a] :=
  (Fin.sum_univ_fun_getElem l f).symm

/-- **Equation (12)**, by downward induction on the round: `P_i val'_i` is the largest number
of accepting sampled leaves over the strategy trees. -/
theorem cnt_spec (hR : ∀ i, 0 < (R i).length) (x : σ → ℝ) (i : ℕ)
    (r : Fin Pr.c → Fin Pr.ρ → Bool) (z : Fin Pr.c → Fin Pr.μ → ℝ) :
    (∀ S, (cnt Pr R x i r z S : ℝ) ≤ sP Pr R i * Pr.sValFrom R x i r z) ∧
      ∃ S, (cnt Pr R x i r z S : ℝ) = sP Pr R i * Pr.sValFrom R x i r z := by
  by_cases h : i < Pr.c
  · have hq : (0 : ℝ) < (R ⟨i, h⟩).length := by exact_mod_cast hR ⟨i, h⟩
    -- the functions whose suprema are taken
    set f : Fin (R ⟨i, h⟩).length → (Fin Pr.μ → ℝ) → ℝ := fun a y =>
      Pr.sValFrom R x (i + 1) (Function.update r ⟨i, h⟩ (R ⟨i, h⟩)[a])
        (Function.update z ⟨i, h⟩ y) with hfdef
    have hmax : ∀ a, BddAbove (range (f a)) ∧ ∃ y, f a y = ⨆ y, f a y := by
      intro a
      refine exists_eq_ciSup (f a) (sP Pr R (i + 1)) (fun y => ?_) (sP_pos Pr R hR _)
      obtain ⟨S, hS⟩ := (cnt_spec hR x (i + 1) (Function.update r ⟨i, h⟩ (R ⟨i, h⟩)[a])
        (Function.update z ⟨i, h⟩ y)).2
      exact ⟨_, cnt_le Pr R x _ _ _ S, hS⟩
    have hval : (sP Pr R i : ℝ) * Pr.sValFrom R x i r z =
        sP Pr R (i + 1) * ∑ a : Fin (R ⟨i, h⟩).length, ⨆ y, f a y := by
      rw [AMProtocol.sValFrom, dite_eq_left h, sP_succ Pr R i h, sum_map_eq_sum_fin]
      push_cast
      field_simp
      rfl
    rw [hval]
    constructor
    · intro S
      rw [cnt_succ Pr R x i h, Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun a _ => ?_
      refine ((cnt_spec hR x (i + 1) _ _).1 _).trans ?_
      exact mul_le_mul_of_nonneg_left (le_ciSup (hmax a).1 _) (by positivity)
    · choose y hy using fun a => (hmax a).2
      choose S' hS' using fun a => (cnt_spec hR x (i + 1)
        (Function.update r ⟨i, h⟩ (R ⟨i, h⟩)[a]) (Function.update z ⟨i, h⟩ (y a))).2
      let S : Fin (sD Pr R i) → ℝ := fun d =>
        Fin.append (y (finProdFinEquiv.symm (Fin.cast (sD_succ Pr R i h) d)).1)
          (S' (finProdFinEquiv.symm (Fin.cast (sD_succ Pr R i h) d)).1)
          (finProdFinEquiv.symm (Fin.cast (sD_succ Pr R i h) d)).2
      have hSm : ∀ a, (fun k => S (msgIdx Pr R i h a k)) = y a := by
        intro a
        funext k
        simp only [S, msgIdx, Fin.cast_cast, Fin.cast_refl, id, Equiv.symm_apply_apply,
          Fin.append_left]
      have hSs : ∀ a, S ∘ subIdx Pr R i h a = S' a := by
        intro a
        funext d
        simp only [S, subIdx, Fin.cast_cast, Fin.cast_refl, id, Equiv.symm_apply_apply,
          Fin.append_right, Function.comp_apply]
      refine ⟨S, ?_⟩
      rw [cnt_succ Pr R x i h, Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hSm a, hSs a, hS' a, ← hy a]
  · have hS : ∀ S, (cnt Pr R x i r z S : ℝ) = sP Pr R i * Pr.sValFrom R x i r z := by
      intro S
      rw [cnt, LT_of_le Pr R i (by omega), sP_of_le Pr R i (by omega), AMProtocol.sValFrom,
        dite_eq_right h, List.countP_singleton, leaf_run]
      by_cases hV : Pr.V.Accepts (Pr.verInput x r z)
      · have hV' : Pr.V.run (Pr.verInput x r z) = some true := hV
        simp [hV, hV']
      · have hV' : ¬ Pr.V.run (Pr.verInput x r z) = some true := hV
        simp [hV, hV']
    exact ⟨fun S => (hS S).le, ⟨fun _ => 0, hS _⟩⟩
termination_by Pr.c - i

end Strategy

end AMAux

/-! ### Fixing the coins (Lemma 7.7) -/

namespace AMAux

section Fixing

variable {σ : Type} (Pr : AMProtocol σ)

/-- `sValFrom` at round `i` only depends on the lists of the rounds `≥ i`. -/
theorem sValFrom_congr (R R' : Fin Pr.c → List (Fin Pr.ρ → Bool)) (x : σ → ℝ) (i : ℕ)
    (hRR : ∀ j : Fin Pr.c, i ≤ j.val → R j = R' j) (r : Fin Pr.c → Fin Pr.ρ → Bool)
    (z : Fin Pr.c → Fin Pr.μ → ℝ) : Pr.sValFrom R x i r z = Pr.sValFrom R' x i r z := by
  by_cases h : i < Pr.c
  · rw [AMProtocol.sValFrom.eq_1 Pr R, dite_eq_left h, AMProtocol.sValFrom.eq_1 Pr R',
      dite_eq_left h, hRR ⟨i, h⟩ le_rfl]
    congr 2
    refine List.map_congr_left fun b _ => ?_
    congr 1
    funext y
    exact sValFrom_congr R R' x (i + 1) (fun j hj => hRR j (by omega)) _ _
  · rw [AMProtocol.sValFrom.eq_1 Pr R, dite_eq_right h, AMProtocol.sValFrom.eq_1 Pr R',
      dite_eq_right h]
termination_by Pr.c - i

theorem sP_congr (R R' : Fin Pr.c → List (Fin Pr.ρ → Bool)) (i : ℕ)
    (hRR : ∀ j : Fin Pr.c, i ≤ j.val → R j = R' j) : sP Pr R i = sP Pr R' i := by
  rw [sP_eq_prod, sP_eq_prod]
  exact Finset.prod_congr rfl fun j hj => by
    rw [hRR j (Finset.mem_filter.1 hj).2]

theorem ciSup_mem_Icc {α : Type} [Nonempty α] (f : α → ℝ) (hf : ∀ a, f a ∈ Icc (0 : ℝ) 1) :
    BddAbove (range f) ∧ (⨆ a, f a) ∈ Icc (0 : ℝ) 1 := by
  have hb : BddAbove (range f) := ⟨1, by rintro _ ⟨a, rfl⟩; exact (hf a).2⟩
  refine ⟨hb, ?_, ciSup_le fun a => (hf a).2⟩
  obtain ⟨a⟩ := (inferInstance : Nonempty α)
  exact (hf a).1.trans (le_ciSup hb a)

theorem valFrom_mem (x : σ → ℝ) (i : ℕ) (r : Fin Pr.c → Fin Pr.ρ → Bool)
    (z : Fin Pr.c → Fin Pr.μ → ℝ) : Pr.valFrom x i r z ∈ Icc (0 : ℝ) 1 := by
  by_cases h : i < Pr.c
  · rw [AMProtocol.valFrom.eq_1, dite_eq_left h]
    have hg : ∀ b : Fin Pr.ρ → Bool, (⨆ y : Fin Pr.μ → ℝ, Pr.valFrom x (i + 1)
        (Function.update r ⟨i, h⟩ b) (Function.update z ⟨i, h⟩ y)) ∈ Icc (0 : ℝ) 1 :=
      fun b => (ciSup_mem_Icc _ fun y => valFrom_mem x (i + 1) _ _).2
    have hcard : (∑ _b : Fin Pr.ρ → Bool, (1 : ℝ)) = 2 ^ Pr.ρ := by simp
    constructor
    · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun b _ => (hg b).1)
    · rw [inv_mul_le_iff₀ (by positivity), mul_one, ← hcard]
      exact Finset.sum_le_sum fun b _ => (hg b).2
  · rw [AMProtocol.valFrom.eq_1, dite_eq_right h]
    split_ifs <;> norm_num
termination_by Pr.c - i

theorem sValFrom_mem (R : Fin Pr.c → List (Fin Pr.ρ → Bool)) (x : σ → ℝ) (i : ℕ)
    (r : Fin Pr.c → Fin Pr.ρ → Bool) (z : Fin Pr.c → Fin Pr.μ → ℝ) :
    Pr.sValFrom R x i r z ∈ Icc (0 : ℝ) 1 := by
  by_cases h : i < Pr.c
  · rw [AMProtocol.sValFrom.eq_1, dite_eq_left h]
    have hg : ∀ b : Fin Pr.ρ → Bool, (⨆ y : Fin Pr.μ → ℝ, Pr.sValFrom R x (i + 1)
        (Function.update r ⟨i, h⟩ b) (Function.update z ⟨i, h⟩ y)) ∈ Icc (0 : ℝ) 1 :=
      fun b => (ciSup_mem_Icc _ fun y => sValFrom_mem R x (i + 1) _ _).2
    set l := R ⟨i, h⟩
    set f := fun b : Fin Pr.ρ → Bool => ⨆ y : Fin Pr.μ → ℝ, Pr.sValFrom R x (i + 1)
      (Function.update r ⟨i, h⟩ b) (Function.update z ⟨i, h⟩ y) with hf
    have hs0 : 0 ≤ (l.map f).sum := List.sum_nonneg (by
      intro v hv
      obtain ⟨b, -, rfl⟩ := List.mem_map.1 hv
      exact (hg b).1)
    have hs1 : (l.map f).sum ≤ l.length := by
      have := List.sum_le_length_nsmul (l.map f) 1 (by
        intro v hv
        obtain ⟨b, -, rfl⟩ := List.mem_map.1 hv
        exact (hg b).2)
      simpa using this
    rcases Nat.eq_zero_or_pos l.length with h0 | h0
    · simp [h0]
    · have hl : (0 : ℝ) < l.length := by exact_mod_cast h0
      refine ⟨mul_nonneg (by positivity) hs0, ?_⟩
      rw [inv_mul_le_iff₀ hl, mul_one]
      exact hs1
  · rw [AMProtocol.sValFrom.eq_1, dite_eq_right h]
    split_ifs <;> norm_num
termination_by Pr.c - i

theorem abs_ciSup_sub_le {α : Type} [Nonempty α] (f g : α → ℝ) (hf : BddAbove (range f))
    (hg : BddAbove (range g)) (ε : ℝ) (h : ∀ a, |f a - g a| ≤ ε) :
    |(⨆ a, f a) - ⨆ a, g a| ≤ ε := by
  rw [abs_le]
  constructor
  · have : ⨆ a, g a ≤ (⨆ a, f a) + ε := ciSup_le fun a =>
      (show g a ≤ (⨆ a, f a) + ε by
        have := (abs_le.1 (h a)).1; have := le_ciSup hf a; linarith)
    linarith
  · have : ⨆ a, f a ≤ (⨆ a, g a) + ε := ciSup_le fun a =>
      (show f a ≤ (⨆ a, g a) + ε by
        have := (abs_le.1 (h a)).2; have := le_ciSup hg a; linarith)
    linarith

/-- The function `g_{x,h}` of the proof of Lemma 7.7 at round `i`. -/
def gFun (R : Fin Pr.c → List (Fin Pr.ρ → Bool)) (x : σ → ℝ) (i : ℕ) (h : i < Pr.c)
    (r : Fin Pr.c → Fin Pr.ρ → Bool) (z : Fin Pr.c → Fin Pr.μ → ℝ) (b : Fin Pr.ρ → Bool) : ℝ :=
  ⨆ y : Fin Pr.μ → ℝ, Pr.sValFrom R x (i + 1) (Function.update r ⟨i, h⟩ b)
    (Function.update z ⟨i, h⟩ y)

/-- The list `Rᵢ` is a good sample for round `i`. -/
def GoodSample (R : Fin Pr.c → List (Fin Pr.ρ → Bool)) (γ : ℝ) (i : ℕ) (h : i < Pr.c) : Prop :=
  ∀ x r z, |((R ⟨i, h⟩).map (gFun Pr R x i h r z)).sum / (R ⟨i, h⟩).length -
    (Fintype.card (Fin Pr.ρ → Bool) : ℝ)⁻¹ * ∑ b, gFun Pr R x i h r z b| ≤ γ

/-- **Accumulated error.** -/
theorem error_bound (R : Fin Pr.c → List (Fin Pr.ρ → Bool)) (γ : ℝ)
    (hgood : ∀ i (h : i < Pr.c), GoodSample Pr R γ i h) (x : σ → ℝ) (i : ℕ)
    (r : Fin Pr.c → Fin Pr.ρ → Bool) (z : Fin Pr.c → Fin Pr.μ → ℝ) :
    |Pr.sValFrom R x i r z - Pr.valFrom x i r z| ≤ (Pr.c - i : ℕ) * γ := by
  by_cases h : i < Pr.c
  · rw [AMProtocol.sValFrom.eq_1, dite_eq_left h, AMProtocol.valFrom.eq_1, dite_eq_left h]
    change |((R ⟨i, h⟩).length : ℝ)⁻¹ * ((R ⟨i, h⟩).map (gFun Pr R x i h r z)).sum - _| ≤ _
    set g' := gFun Pr R x i h r z with hg'
    set g : (Fin Pr.ρ → Bool) → ℝ := fun b => ⨆ y : Fin Pr.μ → ℝ, Pr.valFrom x (i + 1)
      (Function.update r ⟨i, h⟩ b) (Function.update z ⟨i, h⟩ y) with hg
    have hγ : 0 ≤ γ := by
      have := hgood i h x r z
      exact (abs_nonneg _).trans this
    have hcard : (Fintype.card (Fin Pr.ρ → Bool) : ℝ) = 2 ^ Pr.ρ := by simp
    have hdiff : ∀ b, |g' b - g b| ≤ (Pr.c - (i + 1) : ℕ) * γ := by
      intro b
      refine abs_ciSup_sub_le _ _ (ciSup_mem_Icc _ fun y => sValFrom_mem Pr R x _ _ _).1
        (ciSup_mem_Icc _ fun y => valFrom_mem Pr x _ _ _).1 _ fun y => ?_
      exact error_bound R γ hgood x (i + 1) _ _
    have h1 := hgood i h x r z
    rw [← hg', hcard] at h1
    have h2 : |(2 ^ Pr.ρ : ℝ)⁻¹ * ∑ b, g' b - (2 ^ Pr.ρ : ℝ)⁻¹ * ∑ b, g b| ≤
        (Pr.c - (i + 1) : ℕ) * γ := by
      rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (by positivity)]
      rw [inv_mul_le_iff₀ (by positivity)]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ b, |g' b - g b| ≤ ∑ _b : Fin Pr.ρ → Bool, ((Pr.c - (i + 1) : ℕ) * γ) :=
            Finset.sum_le_sum fun b _ => hdiff b
        _ = 2 ^ Pr.ρ * ((Pr.c - (i + 1) : ℕ) * γ) := by simp
    have hci : ((Pr.c - i : ℕ) : ℝ) = ((Pr.c - (i + 1) : ℕ) : ℝ) + 1 := by
      rw [show Pr.c - i = Pr.c - (i + 1) + 1 by omega]; push_cast; ring
    rw [hci, add_mul, one_mul]
    have e : ((R ⟨i, h⟩).length : ℝ)⁻¹ * ((R ⟨i, h⟩).map g').sum =
        ((R ⟨i, h⟩).map g').sum / (R ⟨i, h⟩).length := by ring
    rw [e]
    calc |((R ⟨i, h⟩).map g').sum / (R ⟨i, h⟩).length - (2 ^ Pr.ρ : ℝ)⁻¹ * ∑ b, g b|
        ≤ |((R ⟨i, h⟩).map g').sum / (R ⟨i, h⟩).length - (2 ^ Pr.ρ : ℝ)⁻¹ * ∑ b, g' b| +
          |(2 ^ Pr.ρ : ℝ)⁻¹ * ∑ b, g' b - (2 ^ Pr.ρ : ℝ)⁻¹ * ∑ b, g b| := abs_sub_le _ _ _
      _ ≤ γ + (Pr.c - (i + 1) : ℕ) * γ := add_le_add h1 h2
      _ = (Pr.c - (i + 1) : ℕ) * γ + γ := by ring
  · rw [AMProtocol.sValFrom.eq_1, dite_eq_right h, AMProtocol.valFrom.eq_1, dite_eq_right h,
      sub_self, abs_zero]
    have : Pr.c - i = 0 := by omega
    rw [this]
    simp
termination_by Pr.c - i

/-- The sizes `qᵢ = A P_{i+1}²` give `P₁ ≤ A^{3^c}`. -/
theorem sP_le_pow (R : Fin Pr.c → List (Fin Pr.ρ → Bool)) (A : ℕ) (hA : 1 ≤ A)
    (hlen : ∀ j : Fin Pr.c, (R j).length = A * sP Pr R (j.val + 1) ^ 2) (i : ℕ) :
    A * sP Pr R i ^ 2 ≤ A ^ (3 ^ (Pr.c - i)) := by
  by_cases h : i < Pr.c
  · have ih := sP_le_pow R A hA hlen (i + 1)
    rw [sP_succ Pr R i h, hlen ⟨i, h⟩]
    have e : Pr.c - i = (Pr.c - (i + 1)) + 1 := by omega
    rw [e, pow_succ 3, pow_mul]
    calc A * (A * sP Pr R (i + 1) ^ 2 * sP Pr R (i + 1)) ^ 2 = (A * sP Pr R (i + 1) ^ 2) ^ 3 := by
          ring
      _ ≤ (A ^ 3 ^ (Pr.c - (i + 1))) ^ 3 := Nat.pow_le_pow_left ih 3
  · rw [sP_of_le Pr R i (by omega), show Pr.c - i = 0 by omega]
    simp
termination_by Pr.c - i

end Fixing

end AMAux

section Hoeffding

open MeasureTheory ProbabilityTheory Real

namespace AMAux

/-- Hoeffding's lemma for the uniform distribution on a finite set. -/
theorem hoeffding_lemma_fin {B : Type} [Fintype B] [Nonempty B] (g : B → ℝ)
    (hg : ∀ b, g b ∈ Set.Icc (0 : ℝ) 1) (t : ℝ) :
    (Fintype.card B : ℝ)⁻¹ * ∑ b, exp (t * (g b - (Fintype.card B : ℝ)⁻¹ * ∑ b, g b)) ≤
      exp (t ^ 2 / 8) := by
  let _ : MeasurableSpace B := ⊤
  have : MeasurableSingletonClass B := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  set μ : Measure B := (Fintype.card B : ENNReal)⁻¹ • Measure.count with hμ
  have hcard : (0 : ℝ) < Fintype.card B := by exact_mod_cast Fintype.card_pos
  have : IsProbabilityMeasure μ := by
    constructor
    rw [hμ, smul_apply, Measure.count_univ, smul_eq_mul]
    rw [ENat.card_eq_coe_fintype_card]
    simp only [ENat.toENNReal_coe]
    exact ENNReal.inv_mul_cancel (by simp) (by simp)
  have hint : ∀ f : B → ℝ, ∫ b, f b ∂μ = (Fintype.card B : ℝ)⁻¹ * ∑ b, f b := by
    intro f
    rw [hμ, integral_smul_measure, integral_count, smul_eq_mul]
    simp
  have h := (hasSubgaussianMGF_of_mem_Icc (μ := μ) (X := g) (a := 0) (b := 1)
    measurable_from_top.aemeasurable (ae_of_all _ hg)).mgf_le t
  rw [mgf, hint, hint] at h
  convert h using 2
  simp
  ring

theorem card_filter_mul_le_sum {α : Type} (s : Finset α) (p : α → Prop) [DecidablePred p]
    (f : α → ℝ) (c : ℝ) (hf : ∀ a, 0 ≤ f a) (hp : ∀ a ∈ s, p a → c ≤ f a) :
    ((s.filter p).card : ℝ) * c ≤ ∑ a ∈ s, f a := by
  calc ((s.filter p).card : ℝ) * c = ∑ a ∈ s.filter p, c := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ a ∈ s.filter p, f a := Finset.sum_le_sum fun a ha =>
        hp a (Finset.mem_filter.1 ha).1 (Finset.mem_filter.1 ha).2
    _ ≤ ∑ a ∈ s, f a := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun a _ _ => hf a)

/-- **Hoeffding's inequality** for `q` independent uniform samples from a finite set, in
counting form. -/
theorem hoeffding_count {B : Type} [Fintype B] [Nonempty B] (g : B → ℝ)
    (hg : ∀ b, g b ∈ Set.Icc (0 : ℝ) 1) (q : ℕ) (γ : ℝ) (hγ : 0 ≤ γ) :
    ((Finset.univ.filter fun s : Fin q → B =>
        q * γ ≤ ∑ j, (g (s j) - (Fintype.card B : ℝ)⁻¹ * ∑ b, g b)).card : ℝ) ≤
      (Fintype.card B : ℝ) ^ q * exp (-2 * q * γ ^ 2) := by
  have hN : (0 : ℝ) < Fintype.card B := by exact_mod_cast Fintype.card_pos
  have hH := hoeffding_lemma_fin g hg (4 * γ)
  have hsum : ∑ s : Fin q → B,
      exp (4 * γ * ∑ j, (g (s j) - (Fintype.card B : ℝ)⁻¹ * ∑ b, g b)) =
      (∑ b, exp (4 * γ * (g b - (Fintype.card B : ℝ)⁻¹ * ∑ b, g b))) ^ q := by
    rw [← Fin.prod_const, Fintype.prod_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum, Real.exp_sum]
  have h1 := card_filter_mul_le_sum Finset.univ
    (fun s : Fin q → B => q * γ ≤ ∑ j, (g (s j) - (Fintype.card B : ℝ)⁻¹ * ∑ b, g b))
    (fun s => exp (4 * γ * ∑ j, (g (s j) - (Fintype.card B : ℝ)⁻¹ * ∑ b, g b)))
    (exp (4 * γ * (q * γ))) (fun _ => (exp_pos _).le)
    (fun s _ hs => exp_le_exp.2 (mul_le_mul_of_nonneg_left hs (by linarith)))
  rw [hsum] at h1
  have h2 : (∑ b, exp (4 * γ * (g b - (Fintype.card B : ℝ)⁻¹ * ∑ b, g b))) ^ q ≤
      ((Fintype.card B : ℝ) * exp ((4 * γ) ^ 2 / 8)) ^ q := by
    have h0 : 0 ≤ ∑ b, exp (4 * γ * (g b - (Fintype.card B : ℝ)⁻¹ * ∑ b, g b)) :=
      Finset.sum_nonneg fun _ _ => (exp_pos _).le
    rw [inv_mul_le_iff₀ hN] at hH
    exact pow_le_pow_left₀ h0 hH q
  have h3 : ((Fintype.card B : ℝ) * exp ((4 * γ) ^ 2 / 8)) ^ q =
      (Fintype.card B : ℝ) ^ q * exp (-2 * q * γ ^ 2) * exp (4 * γ * (q * γ)) := by
    rw [mul_pow, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have h4 := h1.trans h2
  rw [h3] at h4
  exact le_of_mul_le_mul_right h4 (exp_pos _)

/-- **Sampling** (the union bound over Hoeffding's inequality): if `2 |F| e^{-2qγ²} < 1`,
some list of `q` elements has, for every `g ∈ F`, a sample mean within `γ` of the mean. -/
theorem exists_good_sample {B : Type} [Fintype B] [Nonempty B] (F : Finset (B → ℝ))
    (hF : ∀ g ∈ F, ∀ b, g b ∈ Set.Icc (0 : ℝ) 1) (q : ℕ) (hq : 0 < q) (γ : ℝ) (hγ : 0 < γ)
    (hFq : 2 * F.card * exp (-2 * q * γ ^ 2) < 1) :
    ∃ L : List B, L.length = q ∧ ∀ g ∈ F,
      |(L.map g).sum / q - (Fintype.card B : ℝ)⁻¹ * ∑ b, g b| ≤ γ := by
  set N := (Fintype.card B : ℝ) with hNdef
  have hN : 0 < N := by rw [hNdef]; exact_mod_cast Fintype.card_pos
  -- the bad sequences for `g`
  let badU : (B → ℝ) → Finset (Fin q → B) := fun g => Finset.univ.filter fun s =>
    q * γ ≤ ∑ j, (g (s j) - N⁻¹ * ∑ b, g b)
  let badL : (B → ℝ) → Finset (Fin q → B) := fun g => Finset.univ.filter fun s =>
    q * γ ≤ ∑ j, ((1 - g (s j)) - N⁻¹ * ∑ b, (1 - g b))
  have hU : ∀ g ∈ F, ((badU g).card : ℝ) ≤ N ^ q * exp (-2 * q * γ ^ 2) :=
    fun g hg => hoeffding_count g (hF g hg) q γ hγ.le
  have hL : ∀ g ∈ F, ((badL g).card : ℝ) ≤ N ^ q * exp (-2 * q * γ ^ 2) := by
    intro g hg
    refine hoeffding_count (fun b => 1 - g b) (fun b => ?_) q γ hγ.le
    have := hF g hg b
    constructor <;> linarith [this.1, this.2]
  set bad := F.biUnion fun g => badU g ∪ badL g with hbad
  have hcard : (bad.card : ℝ) < N ^ q := by
    have h1 : (bad.card : ℝ) ≤ ∑ g ∈ F, ((badU g ∪ badL g).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    have h2 : ∀ g ∈ F, ((badU g ∪ badL g).card : ℝ) ≤ 2 * (N ^ q * exp (-2 * q * γ ^ 2)) := by
      intro g hg
      have := Finset.card_union_le (badU g) (badL g)
      have h' : ((badU g ∪ badL g).card : ℝ) ≤ (badU g).card + (badL g).card := by
        exact_mod_cast this
      linarith [hU g hg, hL g hg]
    have h3 := Finset.sum_le_sum h2
    rw [Finset.sum_const, nsmul_eq_mul] at h3
    have hNq : 0 < N ^ q := pow_pos hN q
    nlinarith
  obtain ⟨s, hs⟩ : ∃ s : Fin q → B, s ∉ bad := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    have : (Finset.univ : Finset (Fin q → B)) ⊆ bad := fun s _ => hall s
    have h := Finset.card_le_card this
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at h
    have h' : (N ^ q : ℝ) ≤ bad.card := by rw [hNdef]; exact_mod_cast h
    linarith
  refine ⟨List.ofFn s, List.length_ofFn, fun g hg => ?_⟩
  have hsU : s ∉ badU g := fun h => hs (Finset.mem_biUnion.2 ⟨g, hg, Finset.mem_union_left _ h⟩)
  have hsL : s ∉ badL g := fun h => hs (Finset.mem_biUnion.2 ⟨g, hg, Finset.mem_union_right _ h⟩)
  simp only [badU, badL, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hsU hsL
  rw [List.map_ofFn, List.sum_ofFn]
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have e1 : ∑ j, (g (s j) - N⁻¹ * ∑ b, g b) = ∑ j, g (s j) - q * (N⁻¹ * ∑ b, g b) := by
    rw [Finset.sum_sub_distrib]; simp
  have e2 : ∑ j, ((1 - g (s j)) - N⁻¹ * ∑ b, (1 - g b)) =
      q * (N⁻¹ * ∑ b, g b) - ∑ j, g (s j) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [hNdef]
    field_simp
    ring
  rw [e1] at hsU
  rw [e2] at hsL
  have e3 : (∑ j, g (s j)) / q - N⁻¹ * ∑ b, g b = ((∑ j, g (s j)) - q * (N⁻¹ * ∑ b, g b)) / q := by
    field_simp
  show |(∑ j, g (s j)) / q - N⁻¹ * ∑ b, g b| ≤ γ
  rw [e3, abs_div, abs_of_pos hq', div_le_iff₀ hq', abs_le]
  constructor <;> linarith

end AMAux

end Hoeffding

namespace AMAux

/-- `|γ| Δ + 2 ≤ 2^{ρ + 11t + 3} P` for the sizes of the counting argument. -/
theorem X_bound (ρ t P : ℕ) (hP : 1 ≤ P) :
    2 ^ ρ * P * 4 ^ t * (4 * t) * 2 ^ (8 * t) + 2 ≤ 2 ^ (ρ + 11 * t + 3) * P := by
  have h4t : 4 * t ≤ 4 * 2 ^ t := Nat.mul_le_mul_left _ (Nat.lt_two_pow_self).le
  have h4 : (4 : ℕ) ^ t = 2 ^ (2 * t) := by rw [pow_mul]; norm_num
  have h2 : 2 ≤ 2 ^ (ρ + 11 * t + 2) * P := by
    have : 1 ≤ 2 ^ (ρ + 11 * t + 2) := Nat.one_le_two_pow
    have : 4 ≤ 2 ^ (ρ + 11 * t + 2) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (ρ + 11 * t + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    nlinarith
  calc 2 ^ ρ * P * 4 ^ t * (4 * t) * 2 ^ (8 * t) + 2
      ≤ 2 ^ ρ * P * 4 ^ t * (4 * 2 ^ t) * 2 ^ (8 * t) + 2 := by gcongr
    _ = 2 ^ (ρ + 11 * t + 2) * P + 2 := by rw [h4]; ring
    _ ≤ 2 ^ (ρ + 11 * t + 2) * P + 2 ^ (ρ + 11 * t + 2) * P := by omega
    _ = 2 ^ (ρ + 11 * t + 3) * P := by ring

/-- The arithmetic of Lemma 7.7: with `qᵢ = A P_{i+1}²` the union bound applies. -/
theorem union_bound_arith (C c n μ ρ t P D : ℕ) (hc : 1 ≤ c) (hμ : 1 ≤ μ) (ht : 1 ≤ t)
    (hP : 1 ≤ P) (hD : D + 2 * μ ≤ 2 * μ * P) :
    2 * ((2 ^ (ρ * c) * (2 ^ ρ * P * 4 ^ t * (4 * t) * 2 ^ (8 * t) + 2) ^
        (C * (n + c * μ + 1) * (μ + D + 1)) : ℕ) : ℝ) *
      Real.exp (-2 * (((2048 * C + 96) * (c ^ 2 * (n + c * μ) * μ * (ρ * c + t)) * P ^ 2 : ℕ) : ℝ)
        * (1 / (8 * c : ℝ)) ^ 2) < 1 := by
  set X : ℕ := 2 ^ ρ * P * 4 ^ t * (4 * t) * 2 ^ (8 * t) + 2 with hX
  set E : ℕ := C * (n + c * μ + 1) * (μ + D + 1) with hE
  set a : ℕ := ρ * c + t with ha
  set W : ℕ := (n + c * μ) * μ * a * P ^ 2 with hW
  have ha1 : 1 ≤ a := by omega
  have hcμ : 1 ≤ c * μ := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hW1 : 1 ≤ W := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hXpos : 0 < X := by omega
  have hlog2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; norm_num at this; linarith
  have hlog2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hPr : (1 : ℝ) ≤ P := by exact_mod_cast hP
  -- `log X ≤ 16 a P`
  have hlogX : Real.log X ≤ 16 * a * P := by
    have hXle : (X : ℝ) ≤ 2 ^ (ρ + 11 * t + 3) * P := by exact_mod_cast X_bound ρ t P hP
    have h1 := Real.log_le_log (by positivity) hXle
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at h1
    have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < P by linarith)
    have h3 : ((ρ + 11 * t + 3 : ℕ) : ℝ) ≤ 15 * a := by
      have : ρ ≤ ρ * c := Nat.le_mul_of_pos_right _ hc
      have : ρ + 11 * t + 3 ≤ 15 * a := by omega
      exact_mod_cast this
    have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha1
    nlinarith
  -- `E ≤ 4 C (n + cμ) μ P`
  have hEle : (E : ℝ) ≤ 4 * C * ((n + c * μ) * μ * P : ℕ) := by
    have h1 : n + c * μ + 1 ≤ 2 * (n + c * μ) := by omega
    have h2 : μ + D + 1 ≤ 2 * μ * P := by omega
    have : E ≤ 4 * C * ((n + c * μ) * μ * P) := by
      calc E = C * (n + c * μ + 1) * (μ + D + 1) := rfl
        _ ≤ C * (2 * (n + c * μ)) * (2 * μ * P) := by gcongr
        _ = 4 * C * ((n + c * μ) * μ * P) := by ring
    exact_mod_cast this
  -- `log (2 N) ≤ (64 C + 2) W`
  have hlogN : Real.log (2 * ((2 ^ (ρ * c) * X ^ E : ℕ) : ℝ)) ≤ (64 * C + 2) * W := by
    push_cast
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow]
    have hW' : ((W : ℕ) : ℝ) = ((n + c * μ) * μ * P : ℕ) * a * P := by
      rw [hW]; push_cast; ring
    have hlogX0 : 0 ≤ Real.log X := Real.log_nonneg (by exact_mod_cast hXpos)
    have hEX : (E : ℝ) * Real.log X ≤ 4 * C * ((n + c * μ) * μ * P : ℕ) * (16 * a * P) := by
      have hE0 : (0 : ℝ) ≤ E := by positivity
      calc (E : ℝ) * Real.log X ≤ (E : ℝ) * (16 * a * P) := by gcongr
        _ ≤ 4 * C * ((n + c * μ) * μ * P : ℕ) * (16 * a * P) := by gcongr
    have hρc : ((ρ * c : ℕ) : ℝ) + 1 ≤ 2 * W := by
      have : ρ * c + 1 ≤ 2 * W := by
        have : a ≤ W := by
          rw [hW]
          calc a = 1 * 1 * a * 1 := by ring
            _ ≤ (n + c * μ) * μ * a * P ^ 2 := by
              gcongr
              · omega
              · exact Nat.one_le_pow _ _ hP
        omega
      exact_mod_cast this
    have : (4 : ℝ) * C * ((n + c * μ) * μ * P : ℕ) * (16 * a * P) = 64 * C * W := by
      rw [hW']; ring
    have hρc0 : (0 : ℝ) ≤ ((ρ * c : ℕ) : ℝ) := by positivity
    nlinarith
  -- conclude
  have hq : (((2048 * C + 96) * (c ^ 2 * (n + c * μ) * μ * a) * P ^ 2 : ℕ) : ℝ) *
      (1 / (8 * c : ℝ)) ^ 2 * 2 = (64 * C + 3) * W := by
    have hc' : (c : ℝ) ≠ 0 := by positivity
    rw [hW, ha]
    push_cast
    field_simp
    ring
  have hN0 : (0 : ℝ) < 2 * ((2 ^ (ρ * c) * X ^ E : ℕ) : ℝ) := by positivity
  rw [← Real.exp_log hN0, ← Real.exp_add]
  have hW0 : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have key : Real.log (2 * ((2 ^ (ρ * c) * X ^ E : ℕ) : ℝ)) +
      -2 * (((2048 * C + 96) * (c ^ 2 * (n + c * μ) * μ * a) * P ^ 2 : ℕ) : ℝ) *
        (1 / (8 * c : ℝ)) ^ 2 < 0 := by nlinarith
  calc _ < Real.exp 0 := Real.exp_lt_exp.2 key
    _ = 1 := Real.exp_zero

end AMAux

namespace AMAux

/-! ### The counting bound for polynomials indexed by finite types -/

/-- The sign vectors realized on the fiber over `y`, for polynomials indexed by a finite type
in the variables `α ⊕ β`. -/
def rSigns {α β γ : Type} (p : γ → MvPolynomial (α ⊕ β) ℝ) (y : α → ℝ) : Set (γ → SignType) :=
  {s | ∃ u : β → ℝ, ∀ k, SignType.sign (eval (Sum.elim y u) (p k)) = s k}

/-- The counting bound (C), for finite index types. -/
theorem counting_bound' (hC : CountingBound) :
    ∃ C : ℕ, ∀ {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ] (Δ : ℕ)
      (p : γ → MvPolynomial (α ⊕ β) ℝ), (∀ k, (p k).totalDegree ≤ Δ) →
      (Set.range (rSigns p)).encard ≤
        ((Fintype.card γ * Δ + 2) ^ (C * (Fintype.card α + 1) * (Fintype.card β + 1)) : ℕ) := by
  obtain ⟨C, hC⟩ := hC
  refine ⟨C, fun {α β γ} _ _ _ Δ p hp => ?_⟩
  let eα := Fintype.equivFin α
  let eβ := Fintype.equivFin β
  let eγ := Fintype.equivFin γ
  let p' : Fin (Fintype.card γ) → MvPolynomial (Fin (Fintype.card α) ⊕ Fin (Fintype.card β)) ℝ :=
    fun k => rename (Sum.map eα eβ) (p (eγ.symm k))
  have hp' : ∀ k, (p' k).totalDegree ≤ Δ := fun k => (totalDegree_rename_le _ _).trans (hp _)
  have hb := hC _ _ _ Δ p' hp'
  have hsub : Set.range (rSigns p) ⊆
      (fun S : Set (Fin (Fintype.card γ) → SignType) => (fun s' => s' ∘ eγ) '' S) ''
        Set.range (realizedSigns p') := by
    rintro _ ⟨y, rfl⟩
    refine ⟨realizedSigns p' (y ∘ eα.symm), ⟨_, rfl⟩, ?_⟩
    have hpt : ∀ u : β → ℝ, Sum.elim (y ∘ eα.symm) (u ∘ eβ.symm) ∘ Sum.map eα eβ =
        Sum.elim y u := by
      intro u
      rw [Sum.elim_comp_map]
      simp [Function.comp_assoc]
    ext s
    constructor
    · rintro ⟨s', ⟨u', hu'⟩, rfl⟩
      refine ⟨u' ∘ eβ, fun k => ?_⟩
      have h := hu' (eγ k)
      simp only [p', eval_rename, Equiv.symm_apply_apply] at h
      have e : Sum.elim (y ∘ eα.symm) u' ∘ Sum.map eα eβ = Sum.elim y (u' ∘ eβ) := by
        rw [Sum.elim_comp_map]
        congr 1
        funext v
        simp
      rw [e] at h
      exact h
    · rintro ⟨u, hu⟩
      refine ⟨s ∘ eγ.symm, ⟨u ∘ eβ.symm, fun k => ?_⟩, ?_⟩
      · simp only [p', eval_rename, hpt, Function.comp_apply]
        exact hu _
      · funext k
        simp
  have hfin := (Set.encard_le_encard hsub).trans (Set.encard_image_le _ _)
  refine hfin.trans ?_
  simpa using hb

/-! ### The polynomials of the sampled leaves below round `i` -/

/-- An empty cell (the whole space). -/
def emptyCell {ι : Type} : Cell ι := ⟨[], [], []⟩

/-- The cells of Lemma 2.5 for the accepting outcome of a tree of depth `≤ t`. -/
def cellsOf {ι : Type} (t : ℕ) (T : Tree ι) : List (Cell ι) :=
  if h : T.depth ≤ t then Classical.choose (cells_length T t h {some true}) else []

theorem cellsOf_spec {ι : Type} (t : ℕ) (T : Tree ι) (h : T.depth ≤ t) :
    (∀ B ∈ cellsOf t T, B.Bounded t T.consts) ∧
      ({w | T.run w ∈ ({some true} : Set (Option Bool))} = ⋃ B ∈ cellsOf t T, B.carrier) ∧
      (cellsOf t T).length ≤ 4 ^ t := by
  rw [cellsOf, dite_eq_left h]
  exact Classical.choose_spec (cells_length T t h {some true})

section Count

variable {σ : Type} (Pr : AMProtocol σ) (R : Fin Pr.c → List (Fin Pr.ρ → Bool)) (t i : ℕ)
  (hi : i < Pr.c)

/-- The variables of the trees below round `i`: `x`, the history and the strategy tree of the
rounds `> i`, are mapped to the free variables `(x, z)` and the quantified variables
`(y, S)` (the message of round `i` and the strategy tree). -/
def varMap : σ ⊕ (Fin Pr.c × Fin Pr.μ) ⊕ Fin (sD Pr R (i + 1)) →
    (σ ⊕ (Fin Pr.c × Fin Pr.μ)) ⊕ (Fin Pr.μ ⊕ Fin (sD Pr R (i + 1))) :=
  Sum.elim (fun s => .inl (.inl s)) (Sum.elim
    (fun p => if p.1 = ⟨i, hi⟩ then .inr (.inl p.2) else .inl (.inr p))
    (fun d => .inr (.inr d)))

theorem stInput_eq_comp (x : σ → ℝ) (z : Fin Pr.c → Fin Pr.μ → ℝ) (y : Fin Pr.μ → ℝ)
    (S : Fin (sD Pr R (i + 1)) → ℝ) :
    stInput Pr x (Function.update z ⟨i, hi⟩ y) S =
      Sum.elim (Sum.elim x fun p => z p.1 p.2) (Sum.elim y S) ∘ varMap Pr R i hi := by
  funext p
  rcases p with s | ⟨j, k⟩ | d
  · rfl
  · by_cases hj : j = ⟨i, hi⟩
    · subst hj
      simp [varMap, stInput]
    · simp [varMap, stInput, hj]
  · rfl

/-- The `κ`-th sampled leaf below round `i`, for the coins `r` and `b` in round `i`. -/
def treeAt (r : Fin Pr.c → Fin Pr.ρ → Bool) (b : Fin Pr.ρ → Bool) (κ : ℕ) :
    Tree (σ ⊕ (Fin Pr.c × Fin Pr.μ) ⊕ Fin (sD Pr R (i + 1))) :=
  (LT Pr R (i + 1) (Function.update r ⟨i, hi⟩ b)).getD κ (.leaf false)

theorem depth_treeAt (ht : Pr.V.depth ≤ t) (ht1 : 1 ≤ t) (r : Fin Pr.c → Fin Pr.ρ → Bool)
    (b : Fin Pr.ρ → Bool) (κ : ℕ) : (treeAt Pr R i hi r b κ).depth ≤ t := by
  unfold treeAt
  by_cases hκ : κ < (LT Pr R (i + 1) (Function.update r ⟨i, hi⟩ b)).length
  · rw [List.getD_eq_getElem _ _ hκ, depth_LT Pr R _ _ _ (List.getElem_mem hκ)]
    exact ht
  · rw [List.getD_eq_default _ _ (not_lt.1 hκ)]
    exact ht1

/-- The `j`-th cell of the `κ`-th sampled leaf. -/
def cellAt (r : Fin Pr.c → Fin Pr.ρ → Bool) (b : Fin Pr.ρ → Bool) (κ j : ℕ) :
    Cell (σ ⊕ (Fin Pr.c × Fin Pr.μ) ⊕ Fin (sD Pr R (i + 1))) :=
  (cellsOf t (treeAt Pr R i hi r b κ)).getD j emptyCell

/-- The index set of the polynomials. -/
abbrev Idx := (Fin Pr.ρ → Bool) × Fin (sP Pr R (i + 1)) × Fin (4 ^ t) × (Fin (2 * t) ⊕ Fin (2 * t))

/-- The polynomials of all cells of all sampled leaves below round `i`, for the coins `r`. -/
def polyR (r : Fin Pr.c → Fin Pr.ρ → Bool) (k : Idx Pr R t i) :
    MvPolynomial ((σ ⊕ (Fin Pr.c × Fin Pr.μ)) ⊕ (Fin Pr.μ ⊕ Fin (sD Pr R (i + 1)))) ℝ :=
  rename (varMap Pr R i hi) (Sum.elim
    (fun l : Fin (2 * t) => (cellAt Pr R t i hi r k.1 k.2.1 k.2.2.1).eqs.getD l 0)
    (fun l : Fin (2 * t) => (cellAt Pr R t i hi r k.1 k.2.1 k.2.2.1).poss.getD l 0) k.2.2.2)

/-- The sign condition saying that the `κ`-th sampled leaf accepts. -/
def accS (r : Fin Pr.c → Fin Pr.ρ → Bool) (b : Fin Pr.ρ → Bool) (κ : Fin (sP Pr R (i + 1)))
    (s : Idx Pr R t i → SignType) : Prop :=
  ∃ j : Fin (4 ^ t), j.val < (cellsOf t (treeAt Pr R i hi r b κ)).length ∧
    (∀ l : Fin (2 * t), l.val < (cellAt Pr R t i hi r b κ j).eqs.length →
      s (b, κ, j, .inl l) = 0) ∧
    (∀ l : Fin (2 * t), l.val < (cellAt Pr R t i hi r b κ j).poss.length →
      s (b, κ, j, .inr l) = 1)

/-- The number of accepting sampled leaves, read off a sign vector. -/
def valS (r : Fin Pr.c → Fin Pr.ρ → Bool) (b : Fin Pr.ρ → Bool) (s : Idx Pr R t i → SignType) :
    ℕ :=
  (Finset.univ.filter fun κ => accS Pr R t i hi r b κ s).card

/-- The sign vector of the polynomials at `((x, z), u)`. -/
def signVec (r : Fin Pr.c → Fin Pr.ρ → Bool) (xz : σ ⊕ (Fin Pr.c × Fin Pr.μ) → ℝ)
    (u : Fin Pr.μ ⊕ Fin (sD Pr R (i + 1)) → ℝ) : Idx Pr R t i → SignType :=
  fun k => SignType.sign (eval (Sum.elim xz u) (polyR Pr R t i hi r k))

/-- A sampled leaf accepts exactly when its sign condition holds. -/
theorem run_treeAt_iff (ht : Pr.V.depth ≤ t) (ht1 : 1 ≤ t) (r : Fin Pr.c → Fin Pr.ρ → Bool)
    (b : Fin Pr.ρ → Bool) (κ : Fin (sP Pr R (i + 1))) (x : σ → ℝ)
    (z : Fin Pr.c → Fin Pr.μ → ℝ) (y : Fin Pr.μ → ℝ) (S : Fin (sD Pr R (i + 1)) → ℝ) :
    (treeAt Pr R i hi r b κ).run (stInput Pr x (Function.update z ⟨i, hi⟩ y) S) = some true ↔
      accS Pr R t i hi r b κ
        (signVec Pr R t i hi r (Sum.elim x fun p => z p.1 p.2) (Sum.elim y S)) := by
  set T := treeAt Pr R i hi r b κ with hT
  set w := stInput Pr x (Function.update z ⟨i, hi⟩ y) S with hw
  have hdT := depth_treeAt Pr R t i hi ht ht1 r b κ
  obtain ⟨hbd, hset, hlen⟩ := cellsOf_spec t T hdT
  have hrun : T.run w = some true ↔ ∃ B ∈ cellsOf t T, w ∈ B.carrier := by
    have := congrArg (w ∈ ·) hset
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.mem_iUnion, exists_prop] at this
    exact Iff.of_eq this
  have hev : ∀ q, eval (Sum.elim (Sum.elim x fun p => z p.1 p.2) (Sum.elim y S))
      (rename (varMap Pr R i hi) q) = eval w q := by
    intro q
    rw [eval_rename, hw, stInput_eq_comp]
  rw [hrun]
  constructor
  · rintro ⟨B, hB, hwB⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hB
    have hcell : cellAt Pr R t i hi r b κ j = (cellsOf t T)[j] := by
      rw [cellAt, ← hT, List.getD_eq_getElem _ _ hj]
    have hbB := hbd _ hB
    refine ⟨⟨j, hj.trans_le hlen⟩, hj, fun l hl => ?_, fun l hl => ?_⟩
    · simp only [signVec, polyR, Sum.elim_inl, hev]
      rw [hcell] at hl ⊢
      rw [List.getD_eq_getElem _ _ hl, sign_eq_zero_iff]
      exact hwB.1 _ (List.getElem_mem hl)
    · simp only [signVec, polyR, Sum.elim_inr, hev]
      rw [hcell] at hl ⊢
      rw [List.getD_eq_getElem _ _ hl, sign_eq_one_iff]
      exact hwB.2 _ (List.getElem_mem hl)
  · rintro ⟨j, hj, heq, hpos⟩
    have hcell : cellAt Pr R t i hi r b κ j = (cellsOf t T)[j.val] := by
      rw [cellAt, ← hT, List.getD_eq_getElem _ _ hj]
    refine ⟨(cellsOf t T)[j.val], List.getElem_mem hj, fun p hp => ?_, fun p hp => ?_⟩
    · obtain ⟨l, hl, rfl⟩ := List.mem_iff_getElem.1 hp
      have hl2 : l < 2 * t := hl.trans_le (hbd _ (List.getElem_mem hj)).eqs_len
      have := heq ⟨l, hl2⟩ (by rw [hcell]; exact hl)
      simp only [signVec, polyR, Sum.elim_inl, hev] at this
      rw [hcell, List.getD_eq_getElem _ _ hl, sign_eq_zero_iff] at this
      exact this
    · obtain ⟨l, hl, rfl⟩ := List.mem_iff_getElem.1 hp
      have hl2 : l < 2 * t := hl.trans_le (hbd _ (List.getElem_mem hj)).poss_len
      have := hpos ⟨l, hl2⟩ (by rw [hcell]; exact hl)
      simp only [signVec, polyR, Sum.elim_inr, hev] at this
      rw [hcell, List.getD_eq_getElem _ _ hl, sign_eq_one_iff] at this
      exact this

theorem countP_eq_card_filter {α : Type} (l : List α) (P : ℕ) (hP : l.length = P) (d : α)
    (p : α → Bool) :
    l.countP p = (Finset.univ.filter fun κ : Fin P => p (l.getD κ d) = true).card := by
  subst hP
  have h1 : l.countP p = (l.map fun a => if p a = true then 1 else 0).sum := by
    induction l with
    | nil => simp
    | cons a l ih =>
      rw [List.countP_cons, ih, List.map_cons, List.sum_cons]
      by_cases ha : p a <;> simp [ha, add_comm]
  rw [h1, ← Fin.sum_univ_fun_getElem, Finset.card_filter]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [List.getD_eq_getElem _ _ κ.isLt]

/-- The number of accepting sampled leaves is read off the sign vector. -/
theorem cnt_eq_valS (ht : Pr.V.depth ≤ t) (ht1 : 1 ≤ t) (r : Fin Pr.c → Fin Pr.ρ → Bool)
    (b : Fin Pr.ρ → Bool) (x : σ → ℝ) (z : Fin Pr.c → Fin Pr.μ → ℝ) (y : Fin Pr.μ → ℝ)
    (S : Fin (sD Pr R (i + 1)) → ℝ) :
    cnt Pr R x (i + 1) (Function.update r ⟨i, hi⟩ b) (Function.update z ⟨i, hi⟩ y) S =
      valS Pr R t i hi r b
        (signVec Pr R t i hi r (Sum.elim x fun p => z p.1 p.2) (Sum.elim y S)) := by
  rw [cnt, countP_eq_card_filter _ _ (length_LT Pr R _ _) (.leaf false)
    (fun T => decide (T.run (stInput Pr x (Function.update z ⟨i, hi⟩ y) S) = some true)), valS]
  congr 1
  ext κ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
  exact run_treeAt_iff Pr R t i hi ht ht1 r b κ x z y S

/-- `P_{i+1} g_{x,h}(b)` is the largest count over the sign vectors realized on the fiber. -/
theorem gFun_isGreatest (hR : ∀ j, 0 < (R j).length) (ht : Pr.V.depth ≤ t) (ht1 : 1 ≤ t)
    (r : Fin Pr.c → Fin Pr.ρ → Bool) (b : Fin Pr.ρ → Bool) (x : σ → ℝ)
    (z : Fin Pr.c → Fin Pr.μ → ℝ) :
    IsGreatest {v : ℝ | ∃ s ∈ rSigns (polyR Pr R t i hi r) (Sum.elim x fun p => z p.1 p.2),
      v = valS Pr R t i hi r b s} ((sP Pr R (i + 1) : ℝ) * gFun Pr R x i hi r z b) := by
  set f : (Fin Pr.μ → ℝ) → ℝ := fun y => Pr.sValFrom R x (i + 1)
    (Function.update r ⟨i, hi⟩ b) (Function.update z ⟨i, hi⟩ y) with hf
  have hmax : BddAbove (range f) ∧ ∃ y, f y = ⨆ y, f y := by
    refine exists_eq_ciSup f (sP Pr R (i + 1)) (fun y => ?_) (sP_pos Pr R hR _)
    obtain ⟨S, hS⟩ := (cnt_spec Pr R hR x (i + 1) (Function.update r ⟨i, hi⟩ b)
      (Function.update z ⟨i, hi⟩ y)).2
    exact ⟨_, cnt_le Pr R x _ _ _ S, hS⟩
  have hg : gFun Pr R x i hi r z b = ⨆ y, f y := rfl
  constructor
  · obtain ⟨y, hy⟩ := hmax.2
    obtain ⟨S, hS⟩ := (cnt_spec Pr R hR x (i + 1) (Function.update r ⟨i, hi⟩ b)
      (Function.update z ⟨i, hi⟩ y)).2
    refine ⟨signVec Pr R t i hi r (Sum.elim x fun p => z p.1 p.2) (Sum.elim y S),
      ⟨Sum.elim y S, fun k => rfl⟩, ?_⟩
    rw [← cnt_eq_valS Pr R t i hi ht ht1, hS, hg, ← hy]
  · rintro v ⟨s, ⟨u, hu⟩, rfl⟩
    have hs : s = signVec Pr R t i hi r (Sum.elim x fun p => z p.1 p.2) u :=
      funext fun k => (hu k).symm
    subst hs
    rw [← Sum.elim_comp_inl_inr u, ← cnt_eq_valS Pr R t i hi ht ht1, hg]
    refine ((cnt_spec Pr R hR x (i + 1) _ _).1 _).trans ?_
    exact mul_le_mul_of_nonneg_left (le_ciSup hmax.1 _) (by positivity)

/-- `g_{x,h}` is determined by the coins and the sign vectors realized on the fiber. -/
theorem gFun_eq_of_rSigns (hR : ∀ j, 0 < (R j).length) (ht : Pr.V.depth ≤ t) (ht1 : 1 ≤ t)
    (r : Fin Pr.c → Fin Pr.ρ → Bool) (x x' : σ → ℝ) (z z' : Fin Pr.c → Fin Pr.μ → ℝ)
    (h : rSigns (polyR Pr R t i hi r) (Sum.elim x fun p => z p.1 p.2) =
      rSigns (polyR Pr R t i hi r) (Sum.elim x' fun p => z' p.1 p.2)) :
    gFun Pr R x i hi r z = gFun Pr R x' i hi r z' := by
  funext b
  have h1 := gFun_isGreatest Pr R t i hi hR ht ht1 r b x z
  have h2 := gFun_isGreatest Pr R t i hi hR ht ht1 r b x' z'
  rw [h] at h1
  have := h1.unique h2
  have hP : (0 : ℝ) < sP Pr R (i + 1) := by exact_mod_cast sP_pos Pr R hR _
  exact mul_left_cancel₀ hP.ne' this

theorem totalDegree_cell_getD {ι : Type} (T : Tree ι) (hT : T.depth ≤ t) (j l : ℕ) :
    (((cellsOf t T).getD j emptyCell).eqs.getD l 0).totalDegree ≤ 2 ^ (8 * t) ∧
      (((cellsOf t T).getD j emptyCell).poss.getD l 0).totalDegree ≤ 2 ^ (8 * t) := by
  obtain ⟨hbd, -, -⟩ := cellsOf_spec t T hT
  by_cases hj : j < (cellsOf t T).length
  · rw [List.getD_eq_getElem _ _ hj]
    have hB := hbd _ (List.getElem_mem hj)
    have hdeg : ∀ p, (cellsOf t T)[j].prog.Computes p →
        p.totalDegree ≤ 2 ^ (8 * t) := fun p hp =>
      (SLP.totalDegree_le hp).trans (Nat.pow_le_pow_right (by norm_num) hB.prog_len)
    constructor
    · by_cases hl : l < (cellsOf t T)[j].eqs.length
      · rw [List.getD_eq_getElem _ _ hl]
        exact hdeg _ (hB.computes_eqs _ (List.getElem_mem hl))
      · rw [List.getD_eq_default _ _ (not_lt.1 hl), totalDegree_zero]; exact Nat.zero_le _
    · by_cases hl : l < (cellsOf t T)[j].poss.length
      · rw [List.getD_eq_getElem _ _ hl]
        exact hdeg _ (hB.computes_poss _ (List.getElem_mem hl))
      · rw [List.getD_eq_default _ _ (not_lt.1 hl), totalDegree_zero]; exact Nat.zero_le _
  · rw [List.getD_eq_default _ _ (not_lt.1 hj)]
    simp [emptyCell]

theorem totalDegree_polyR (ht : Pr.V.depth ≤ t) (ht1 : 1 ≤ t) (r : Fin Pr.c → Fin Pr.ρ → Bool)
    (k : Idx Pr R t i) : (polyR Pr R t i hi r k).totalDegree ≤ 2 ^ (8 * t) := by
  refine (totalDegree_rename_le _ _).trans ?_
  have h := totalDegree_cell_getD t (treeAt Pr R i hi r k.1 k.2.1)
    (depth_treeAt Pr R t i hi ht ht1 r k.1 k.2.1) k.2.2.1
  rcases k with ⟨b, κ, j, l | l⟩
  · exact (h l).1
  · exact (h l).2

end Count

/-- **Counting** (the family `𝔉ᵢ` is small), from the counting bound (C). -/
theorem family_bound (hC : CountingBound) :
    ∃ C : ℕ, ∀ {σ : Type} [Fintype σ] (Pr : AMProtocol σ) (R : Fin Pr.c → List (Fin Pr.ρ → Bool)),
      (∀ j, 0 < (R j).length) → ∀ t : ℕ, Pr.V.depth ≤ t → ∀ (i : ℕ) (h : i < Pr.c),
      ∃ F : Finset ((Fin Pr.ρ → Bool) → ℝ),
        F.card ≤ 2 ^ (Pr.ρ * Pr.c) * (2 ^ Pr.ρ * sP Pr R (i + 1) * 4 ^ t * (4 * t) * 2 ^ (8 * t) + 2) ^
          (C * (Fintype.card σ + Pr.c * Pr.μ + 1) * (Pr.μ + sD Pr R (i + 1) + 1)) ∧
        ∀ x r z, gFun Pr R x i h r z ∈ F := by
  obtain ⟨C, hC'⟩ := counting_bound' hC
  refine ⟨C, fun {σ} _ Pr R hR t ht i hi => ?_⟩
  have ht1 : 1 ≤ t := (CellsAux.depth_pos Pr.V).trans ht
  set N := (2 ^ Pr.ρ * sP Pr R (i + 1) * 4 ^ t * (4 * t) * 2 ^ (8 * t) + 2) ^
    (C * (Fintype.card σ + Pr.c * Pr.μ + 1) * (Pr.μ + sD Pr R (i + 1) + 1)) with hN
  have hcard : Fintype.card (Idx Pr R t i) = 2 ^ Pr.ρ * sP Pr R (i + 1) * 4 ^ t * (4 * t) := by
    simp only [Idx, Fintype.card_prod, Fintype.card_sum, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin]
    ring
  -- for fixed coins `r`, the functions `g_{x,h}` form a set of size at most `N`
  let G : (Fin Pr.c → Fin Pr.ρ → Bool) → Set ((Fin Pr.ρ → Bool) → ℝ) := fun r =>
    {g | ∃ x z, g = gFun Pr R x i hi r z}
  have hG : ∀ r, (G r).encard ≤ N := by
    intro r
    have hb := hC' (2 ^ (8 * t)) (polyR Pr R t i hi r)
      (totalDegree_polyR Pr R t i hi ht ht1 r)
    rw [hcard] at hb
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] at hb
    let Φ : Set (Idx Pr R t i → SignType) → ((Fin Pr.ρ → Bool) → ℝ) := fun SS =>
      if h : ∃ xz, rSigns (polyR Pr R t i hi r) xz = SS then
        gFun Pr R (Classical.choose h ∘ Sum.inl) i hi r
          (fun j k => Classical.choose h (Sum.inr (j, k)))
      else 0
    have hsub : G r ⊆ Φ '' Set.range (rSigns (polyR Pr R t i hi r)) := by
      rintro g ⟨x, z, rfl⟩
      refine ⟨_, ⟨Sum.elim x fun p => z p.1 p.2, rfl⟩, ?_⟩
      have h : ∃ xz, rSigns (polyR Pr R t i hi r) xz =
          rSigns (polyR Pr R t i hi r) (Sum.elim x fun p => z p.1 p.2) := ⟨_, rfl⟩
      simp only [Φ, dite_eq_left h]
      apply gFun_eq_of_rSigns Pr R t i hi hR ht ht1
      have e : (Sum.elim (Classical.choose h ∘ Sum.inl) fun p =>
          Classical.choose h (Sum.inr (p.1, p.2))) = Classical.choose h := by
        funext v
        rcases v with v | v <;> rfl
      rw [e]
      exact Classical.choose_spec h
    refine (Set.encard_le_encard hsub).trans ((Set.encard_image_le _ _).trans ?_)
    refine hb.trans ?_
    rw [hN]
  have hfin : ∀ r, (G r).Finite := fun r => Set.finite_of_encard_le_coe (hG r)
  refine ⟨Finset.univ.biUnion fun r => (hfin r).toFinset, ?_, fun x r z => ?_⟩
  · refine Finset.card_biUnion_le.trans ?_
    have hr : ∀ r, (hfin r).toFinset.card ≤ N := by
      intro r
      have := hG r
      rw [(hfin r).encard_eq_coe_toFinset_card] at this
      exact_mod_cast this
    calc ∑ r, (hfin r).toFinset.card ≤ ∑ _r : Fin Pr.c → Fin Pr.ρ → Bool, N :=
          Finset.sum_le_sum fun r _ => hr r
      _ = 2 ^ (Pr.ρ * Pr.c) * N := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_bool, pow_mul]
  · exact Finset.mem_biUnion.2 ⟨r, Finset.mem_univ _, (hfin r).mem_toFinset.2 ⟨x, z, rfl⟩⟩

end AMAux

open AMAux in
/-- **Lemma 7.7 (fixing the coins).**  The counting bound (C) is the hypothesis
`CountingBound`. -/
theorem fixing_coins (hC : CountingBound) :
    ∃ C₀ : ℕ, ∀ {σ : Type} [Fintype σ] (Pr : AMProtocol σ) (t : ℕ), 1 ≤ Pr.c → 1 ≤ Pr.ρ →
      1 ≤ Pr.μ → Pr.V.depth ≤ t →
      ∃ R : Fin Pr.c → List (Fin Pr.ρ → Bool), (∀ i, 2 ≤ (R i).length) ∧
        ∏ i, (R i).length ≤ (C₀ * (Pr.c ^ 2 * (Fintype.card σ + Pr.c * Pr.μ) * Pr.μ *
          (Pr.ρ * Pr.c + t))) ^ (3 ^ Pr.c) ∧
        ∀ x, |Pr.sVal R x - Pr.val x| ≤ 1 / 8 := by
  obtain ⟨C, hCF⟩ := family_bound hC
  refine ⟨2048 * C + 96, fun {σ} _ Pr t hc hρ hμ ht => ?_⟩
  set A := (2048 * C + 96) * (Pr.c ^ 2 * (Fintype.card σ + Pr.c * Pr.μ) * Pr.μ *
    (Pr.ρ * Pr.c + t)) with hAdef
  have ht1 : 1 ≤ t := (CellsAux.depth_pos Pr.V).trans ht
  have hA : 2 ≤ A := by
    have : 1 ≤ Pr.c ^ 2 * (Fintype.card σ + Pr.c * Pr.μ) * Pr.μ * (Pr.ρ * Pr.c + t) :=
      Nat.one_le_iff_ne_zero.2 (by
        have : 1 ≤ Pr.c * Pr.μ := Nat.one_le_iff_ne_zero.2 (by positivity)
        apply Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero (by positivity) (by omega))
          (by omega)) (by omega))
    rw [hAdef]
    nlinarith
  set γ : ℝ := 1 / (8 * Pr.c : ℝ) with hγdef
  have hγ : 0 < γ := by positivity
  -- the construction, from the last round to the first
  have key : ∀ k ≤ Pr.c, ∃ R : Fin Pr.c → List (Fin Pr.ρ → Bool), (∀ j, 2 ≤ (R j).length) ∧
      ∀ j : Fin Pr.c, Pr.c - k ≤ j.val →
        (R j).length = A * sP Pr R (j.val + 1) ^ 2 ∧ GoodSample Pr R γ j.val j.isLt := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨fun _ => [fun _ => false, fun _ => false], fun _ => by simp,
        fun j hj => absurd j.isLt (by omega)⟩
    | succ k ih =>
      intro hk
      obtain ⟨R, hR2, hRg⟩ := ih (by omega)
      have hR0 : ∀ j, 0 < (R j).length := fun j => by have := hR2 j; omega
      set i := Pr.c - (k + 1) with hidef
      have hi : i < Pr.c := by omega
      obtain ⟨F, hFcard, hFmem⟩ := hCF Pr R hR0 t ht i hi
      set F' := F.filter (fun g => ∀ b, g b ∈ Icc (0 : ℝ) 1) with hF'
      have hF'mem : ∀ x r z, gFun Pr R x i hi r z ∈ F' := by
        intro x r z
        rw [hF', Finset.mem_filter]
        exact ⟨hFmem x r z, fun b =>
          (ciSup_mem_Icc _ fun y => sValFrom_mem Pr R x _ _ _).2⟩
      have hP1 : 1 ≤ sP Pr R (i + 1) := sP_pos Pr R hR0 _
      set q := A * sP Pr R (i + 1) ^ 2 with hqdef
      have hq0 : 0 < q := by positivity
      have hDb : sD Pr R (i + 1) + 2 * Pr.μ ≤ 2 * Pr.μ * sP Pr R (i + 1) :=
        sD_bound Pr R hR2 (i + 1)
      have hunion : 2 * (F'.card : ℝ) * Real.exp (-2 * q * γ ^ 2) < 1 := by
        have h := union_bound_arith C Pr.c (Fintype.card σ) Pr.μ Pr.ρ t (sP Pr R (i + 1))
          (sD Pr R (i + 1)) hc hμ ht1 hP1 hDb
        have hF'F : (F'.card : ℝ) ≤ F.card := by exact_mod_cast Finset.card_filter_le _ _
        have hFc : (F.card : ℝ) ≤ ((2 ^ (Pr.ρ * Pr.c) * (2 ^ Pr.ρ * sP Pr R (i + 1) * 4 ^ t *
            (4 * t) * 2 ^ (8 * t) + 2) ^ (C * (Fintype.card σ + Pr.c * Pr.μ + 1) *
            (Pr.μ + sD Pr R (i + 1) + 1)) : ℕ) : ℝ) := by exact_mod_cast hFcard
        have hq' : (q : ℝ) = (((2048 * C + 96) * (Pr.c ^ 2 * (Fintype.card σ + Pr.c * Pr.μ) *
            Pr.μ * (Pr.ρ * Pr.c + t)) * sP Pr R (i + 1) ^ 2 : ℕ) : ℝ) := by
          rw [hqdef, hAdef]
        rw [hq']
        have he : 0 < Real.exp (-2 * (((2048 * C + 96) * (Pr.c ^ 2 * (Fintype.card σ +
            Pr.c * Pr.μ) * Pr.μ * (Pr.ρ * Pr.c + t)) * sP Pr R (i + 1) ^ 2 : ℕ) : ℝ) *
            γ ^ 2) := Real.exp_pos _
        calc _ ≤ 2 * ((2 ^ (Pr.ρ * Pr.c) * (2 ^ Pr.ρ * sP Pr R (i + 1) * 4 ^ t *
            (4 * t) * 2 ^ (8 * t) + 2) ^ (C * (Fintype.card σ + Pr.c * Pr.μ + 1) *
            (Pr.μ + sD Pr R (i + 1) + 1)) : ℕ) : ℝ) * Real.exp (-2 * (((2048 * C + 96) *
            (Pr.c ^ 2 * (Fintype.card σ + Pr.c * Pr.μ) * Pr.μ * (Pr.ρ * Pr.c + t)) *
            sP Pr R (i + 1) ^ 2 : ℕ) : ℝ) * γ ^ 2) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hF'F.trans hFc)
                (by norm_num)) he.le
          _ < 1 := h
      obtain ⟨L, hLlen, hLgood⟩ := exists_good_sample F' (fun g hg => by
        rw [hF', Finset.mem_filter] at hg; exact hg.2) q hq0 γ hγ hunion
      refine ⟨Function.update R ⟨i, hi⟩ L, fun j => ?_, fun j hj => ?_⟩
      · by_cases hj : j = ⟨i, hi⟩
        · subst hj; rw [Function.update_self, hLlen, hqdef]; nlinarith
        · rw [Function.update_of_ne hj]; exact hR2 j
      · -- the rounds `> i` are unchanged
        have hcongr : ∀ l : ℕ, i + 1 ≤ l → ∀ j' : Fin Pr.c, l ≤ j'.val →
            Function.update R ⟨i, hi⟩ L j' = R j' := by
          intro l hl j' hj'
          rw [Function.update_of_ne]
          intro h; rw [Fin.ext_iff] at h; simp at h; omega
        have hg : ∀ (l : ℕ) (hl : l < Pr.c), i ≤ l → ∀ x r z,
            gFun Pr (Function.update R ⟨i, hi⟩ L) x l hl r z = gFun Pr R x l hl r z := by
          intro l hl hil x r z
          funext b
          unfold gFun
          congr 1
          funext y
          exact sValFrom_congr Pr _ _ x (l + 1) (hcongr (l + 1) (by omega)) _ _
        by_cases hji : j.val = i
        · have hj' : j = ⟨i, hi⟩ := Fin.ext hji
          subst hj'
          refine ⟨?_, ?_⟩
          · rw [Function.update_self, hLlen, hqdef,
              sP_congr Pr _ _ (i + 1) (hcongr (i + 1) le_rfl)]
          · intro x r z
            rw [hg i hi le_rfl x r z, Function.update_self, hLlen]
            exact hLgood _ (hF'mem x r z)
        · have hji' : Pr.c - k ≤ j.val := by omega
          obtain ⟨h1, h2⟩ := hRg j hji'
          have hjR : Function.update R ⟨i, hi⟩ L j = R j :=
            hcongr j.val (by omega) j le_rfl
          refine ⟨?_, ?_⟩
          · rw [hjR, h1, sP_congr Pr _ _ (j.val + 1) (hcongr (j.val + 1) (by omega))]
          · intro x r z
            rw [hg j.val j.isLt (by omega) x r z, hjR]
            exact h2 x r z
  obtain ⟨R, hR2, hRg⟩ := key Pr.c le_rfl
  have hR0 : ∀ j, 0 < (R j).length := fun j => by have := hR2 j; omega
  have hlen : ∀ j : Fin Pr.c, (R j).length = A * sP Pr R (j.val + 1) ^ 2 :=
    fun j => (hRg j (by omega)).1
  refine ⟨R, fun j => ?_, ?_, fun x => ?_⟩
  · rw [hlen j]
    have := sP_pos Pr R hR0 (j.val + 1)
    nlinarith
  · rw [← sP_zero]
    have h := sP_le_pow Pr R A (by omega) hlen 0
    have h0 := sP_pos Pr R hR0 0
    simp only [Nat.sub_zero] at h
    calc sP Pr R 0 ≤ A * sP Pr R 0 ^ 2 := by nlinarith
      _ ≤ A ^ 3 ^ Pr.c := h
  · have h := error_bound Pr R γ (fun i hi => (hRg ⟨i, hi⟩ (by simp)).2) x 0
      (fun _ _ => false) (fun _ _ => 0)
    unfold AMProtocol.sVal AMProtocol.val
    refine h.trans (le_of_eq ?_)
    rw [hγdef, Nat.sub_zero]
    field_simp


open AMAux in
/-- **Equation (12)** and the tree `T`: for lists `R` of sizes `qᵢ ≥ 2` with product `P₁`, there is
a tree of depth `≤ C₀ P₁ (t + 1)` on inputs `(x, z)` with `2μP₁` certificate coordinates that
accepts `(x, z)` for some `z` exactly when `val'₁(x) ≥ 1/2`. -/
theorem strategy_tree :
    ∃ C₀ : ℕ, ∀ {σ : Type} [Fintype σ] (Pr : AMProtocol σ) (t : ℕ) (R : Fin Pr.c → List
      (Fin Pr.ρ → Bool)), Pr.V.depth ≤ t → (∀ i, 2 ≤ (R i).length) →
      ∃ T : Tree (σ ⊕ Fin (2 * Pr.μ * ∏ i, (R i).length)),
        T.depth ≤ C₀ * (∏ i, (R i).length) * (t + 1) ∧
        ∀ x, (∃ z, T.Accepts (Sum.elim x z)) ↔ 1 / 2 ≤ Pr.sVal R x := by
  refine ⟨3, fun {σ} _ Pr t R ht hR => ?_⟩
  have hR0 : ∀ i, 0 < (R i).length := fun i => by have := hR i; omega
  set P := ∏ i, (R i).length with hPdef
  have hP : sP Pr R 0 = P := sP_zero Pr R
  have hPpos : 0 < P := hP ▸ sP_pos Pr R hR0 0
  have hle : sD Pr R 0 ≤ 2 * Pr.μ * P := by
    have := sD_bound Pr R hR 0
    rw [hP] at this
    omega
  let g : σ ⊕ (Fin Pr.c × Fin Pr.μ) ⊕ Fin (sD Pr R 0) → TArg (σ ⊕ Fin (2 * Pr.μ * P)) :=
    Sum.elim (fun s => .input (.inl s)) (Sum.elim (fun _ => .const 0)
      (fun d => .input (.inr (Fin.castLE hle d))))
  let r₀ : Fin Pr.c → Fin Pr.ρ → Bool := fun _ _ => false
  refine ⟨(thr (LT Pr R 0 r₀) ((P + 1) / 2)).subst g 0, ?_, ?_⟩
  · rw [Tree.depth_subst]
    refine (depth_thr _ _).trans ?_
    have hsum : ((LT Pr R 0 r₀).map Tree.depth).sum ≤ P * t := by
      have := List.sum_le_length_nsmul ((LT Pr R 0 r₀).map Tree.depth) t (by
        intro d hd
        obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hd
        rw [depth_LT Pr R 0 r₀ T hT]
        exact ht)
      simpa [length_LT, hP] using this
    nlinarith
  · intro x
    have hrun : ∀ z : Fin (2 * Pr.μ * P) → ℝ,
        ((thr (LT Pr R 0 r₀) ((P + 1) / 2)).subst g 0).Accepts (Sum.elim x z) ↔
          P ≤ 2 * cnt Pr R x 0 r₀ (fun _ _ => 0) (z ∘ Fin.castLE hle) := by
      intro z
      have h := Tree.runFrom_subst g (Sum.elim x z) [] (by rintro (s | p | d) <;> trivial)
        (thr (LT Pr R 0 r₀) ((P + 1) / 2)) []
      simp only [List.nil_append, List.length_nil] at h
      have hw : (fun i => (g i).eval (Sum.elim x z) []) =
          stInput Pr x (fun _ _ => 0) (z ∘ Fin.castLE hle) := by
        funext p
        rcases p with s | p | d <;> rfl
      rw [Tree.Accepts, Tree.run, h, hw, ← Tree.run, run_thr]
      simp only [Option.some.injEq, decide_eq_true_eq]
      change (P + 1) / 2 ≤ cnt Pr R x 0 r₀ _ _ ↔ _
      omega
    have hspec := cnt_spec Pr R hR0 x 0 r₀ (fun _ _ => 0)
    rw [hP] at hspec
    have hPr : (0 : ℝ) < P := by exact_mod_cast hPpos
    constructor
    · rintro ⟨z, hz⟩
      rw [hrun] at hz
      have h1 := hspec.1 (z ∘ Fin.castLE hle)
      have h2 : (P : ℝ) ≤ 2 * (cnt Pr R x 0 r₀ (fun _ _ => 0) (z ∘ Fin.castLE hle) : ℝ) := by
        exact_mod_cast hz
      unfold AMProtocol.sVal
      nlinarith
    · intro hv
      obtain ⟨S, hS⟩ := hspec.2
      refine ⟨fun j => if hj : j.val < sD Pr R 0 then S ⟨j.val, hj⟩ else 0, ?_⟩
      rw [hrun]
      have hcomp : ((fun j : Fin (2 * Pr.μ * P) =>
          if hj : j.val < sD Pr R 0 then S ⟨j.val, hj⟩ else 0) ∘ Fin.castLE hle) = S := by
        funext d
        simp [Fin.castLE]
      rw [hcomp]
      have : (P : ℝ) ≤ 2 * (cnt Pr R x 0 r₀ (fun _ _ => 0) S : ℝ) := by
        rw [hS]
        unfold AMProtocol.sVal at hv
        nlinarith
      exact_mod_cast this

/-- The input `(X, Y)` of the permanent language, for protocols on `Option (Fin m × Fin m)`. -/
def perGraph (m : ℕ) : Set (Option (Fin m × Fin m) → ℝ) :=
  {w | w none = eval (w ∘ some) (per m)}

namespace AMAux

/-! ### Padding a protocol with one more coin and one more message coordinate per round -/

section Pad

variable {σ : Type}

/-- The embedding of the inputs of `V` into the inputs of the padded verifier. -/
def padMap (c ρ μ : ℕ) : AMInput σ c ρ μ → AMInput σ c (ρ + 1) (μ + 1) :=
  Sum.map id (Sum.map (Prod.map id Fin.castSucc) (Prod.map id Fin.castSucc))

/-- The protocol with one more (ignored) coin and message coordinate per round. -/
abbrev pad (Pr : AMProtocol σ) : AMProtocol σ :=
  ⟨Pr.c, Pr.ρ + 1, Pr.μ + 1, Pr.V.rename (padMap Pr.c Pr.ρ Pr.μ)⟩

variable (Pr : AMProtocol σ)

theorem pad_verInput (x : σ → ℝ) (r : Fin Pr.c → Fin (Pr.ρ + 1) → Bool)
    (z : Fin Pr.c → Fin (Pr.μ + 1) → ℝ) :
    (pad Pr).verInput x r z ∘ padMap Pr.c Pr.ρ Pr.μ =
      Pr.verInput x (fun j => Fin.init (r j)) (fun j => Fin.init (z j)) := by
  funext p
  rcases p with s | p | p <;> rfl

theorem pad_accepts (x : σ → ℝ) (r : Fin Pr.c → Fin (Pr.ρ + 1) → Bool)
    (z : Fin Pr.c → Fin (Pr.μ + 1) → ℝ) :
    (pad Pr).V.Accepts ((pad Pr).verInput x r z) ↔
      Pr.V.Accepts (Pr.verInput x (fun j => Fin.init (r j)) (fun j => Fin.init (z j))) := by
  show (Pr.V.rename (padMap Pr.c Pr.ρ Pr.μ)).run _ = _ ↔ _
  rw [Tree.run_rename, pad_verInput]
  rfl

theorem init_update {α : Type} {n : ℕ} (f : Fin Pr.c → Fin (n + 1) → α) (j : Fin Pr.c)
    (b : Fin (n + 1) → α) :
    (fun k => Fin.init (Function.update f j b k)) =
      Function.update (fun k => Fin.init (f k)) j (Fin.init b) := by
  funext k
  by_cases hk : k = j
  · subst hk; simp
  · simp [Function.update_of_ne hk]

theorem init_surjective {α : Type} [Nonempty α] {n : ℕ} :
    Function.Surjective (fun y : Fin (n + 1) → α => Fin.init y) := by
  intro y
  obtain ⟨a⟩ := (inferInstance : Nonempty α)
  exact ⟨Fin.snoc y a, Fin.init_snoc _ _⟩

theorem sum_init {n : ℕ} (G : (Fin n → Bool) → ℝ) :
    ∑ b : Fin (n + 1) → Bool, G (Fin.init b) = 2 * ∑ b : Fin n → Bool, G b := by
  rw [← (Fin.snocEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.snocEquiv_apply, Fin.init_snoc, Finset.sum_const, Finset.card_univ,
    Fintype.card_bool, nsmul_eq_mul]
  push_cast
  ring

theorem pad_valFrom (x : σ → ℝ) (i : ℕ) (r : Fin Pr.c → Fin (Pr.ρ + 1) → Bool)
    (z : Fin Pr.c → Fin (Pr.μ + 1) → ℝ) :
    (pad Pr).valFrom x i r z =
      Pr.valFrom x i (fun j => Fin.init (r j)) (fun j => Fin.init (z j)) := by
  by_cases h : i < Pr.c
  · rw [AMProtocol.valFrom.eq_1 (pad Pr), dite_eq_left (show i < (pad Pr).c from h),
      AMProtocol.valFrom.eq_1 Pr, dite_eq_left h]
    have hinner : ∀ b : Fin (Pr.ρ + 1) → Bool,
        (⨆ y : Fin ((pad Pr).μ) → ℝ, (pad Pr).valFrom x (i + 1) (Function.update r ⟨i, h⟩ b)
          (Function.update z ⟨i, h⟩ y)) =
        ⨆ y : Fin Pr.μ → ℝ, Pr.valFrom x (i + 1)
          (Function.update (fun j => Fin.init (r j)) ⟨i, h⟩ (Fin.init b))
          (Function.update (fun j => Fin.init (z j)) ⟨i, h⟩ y) := by
      intro b
      simp only [pad_valFrom x (i + 1), init_update]
      exact init_surjective.iSup_comp (fun y => Pr.valFrom x (i + 1)
          (Function.update (fun j => Fin.init (r j)) ⟨i, h⟩ (Fin.init b))
          (Function.update (fun j => Fin.init (z j)) ⟨i, h⟩ y))
    simp only [hinner]
    rw [sum_init (fun b => ⨆ y : Fin Pr.μ → ℝ,
      Pr.valFrom x (i + 1) (Function.update (fun j => Fin.init (r j)) ⟨i, h⟩ b)
        (Function.update (fun j => Fin.init (z j)) ⟨i, h⟩ y))]
    rw [pow_succ]
    field_simp
  · rw [AMProtocol.valFrom.eq_1 (pad Pr), dite_eq_right (show ¬ i < (pad Pr).c from h),
      AMProtocol.valFrom.eq_1 Pr, dite_eq_right h]
    have hacc := pad_accepts Pr x r z
    split_ifs with h1 h2 h2 <;> first | rfl | exact absurd (hacc.1 h1) h2 | exact absurd (hacc.2 h2) h1
termination_by Pr.c - i

theorem pad_val (x : σ → ℝ) : (pad Pr).val x = Pr.val x :=
  pad_valFrom Pr x 0 _ _

theorem pad_sValFrom (R : Fin Pr.c → List (Fin (Pr.ρ + 1) → Bool)) (x : σ → ℝ) (i : ℕ)
    (r : Fin Pr.c → Fin (Pr.ρ + 1) → Bool) (z : Fin Pr.c → Fin (Pr.μ + 1) → ℝ) :
    (pad Pr).sValFrom R x i r z =
      Pr.sValFrom (fun j => (R j).map Fin.init) x i (fun j => Fin.init (r j))
        (fun j => Fin.init (z j)) := by
  by_cases h : i < Pr.c
  · rw [AMProtocol.sValFrom.eq_1 (pad Pr), dite_eq_left (show i < (pad Pr).c from h),
      AMProtocol.sValFrom.eq_1 Pr, dite_eq_left h]
    have hinner : ∀ b : Fin (Pr.ρ + 1) → Bool,
        (⨆ y : Fin ((pad Pr).μ) → ℝ, (pad Pr).sValFrom R x (i + 1)
          (Function.update r ⟨i, h⟩ b) (Function.update z ⟨i, h⟩ y)) =
        ⨆ y : Fin Pr.μ → ℝ, Pr.sValFrom (fun j => (R j).map Fin.init) x (i + 1)
          (Function.update (fun j => Fin.init (r j)) ⟨i, h⟩ (Fin.init b))
          (Function.update (fun j => Fin.init (z j)) ⟨i, h⟩ y) := by
      intro b
      simp only [pad_sValFrom R x (i + 1), init_update]
      exact init_surjective.iSup_comp (fun y => Pr.sValFrom (fun j => (R j).map Fin.init) x
          (i + 1) (Function.update (fun j => Fin.init (r j)) ⟨i, h⟩ (Fin.init b))
          (Function.update (fun j => Fin.init (z j)) ⟨i, h⟩ y))
    simp only [hinner, List.length_map, List.map_map]
    rfl
  · rw [AMProtocol.sValFrom.eq_1 (pad Pr), dite_eq_right (show ¬ i < (pad Pr).c from h),
      AMProtocol.sValFrom.eq_1 Pr, dite_eq_right h]
    have hacc := pad_accepts Pr x r z
    split_ifs with h1 h2 h2 <;> first | rfl | exact absurd (hacc.1 h1) h2 | exact absurd (hacc.2 h2) h1
termination_by Pr.c - i

theorem pad_sVal (R : Fin Pr.c → List (Fin (Pr.ρ + 1) → Bool)) (x : σ → ℝ) :
    (pad Pr).sVal R x = Pr.sVal (fun j => (R j).map Fin.init) x :=
  pad_sValFrom Pr R x 0 _ _

end Pad

end AMAux

/-- Lemma 7.7 without the assumptions `ρ, μ ≥ 1` (pad the protocol). -/
theorem fixing_coins_gen (hC : CountingBound) :
    ∃ C₀ : ℕ, ∀ {σ : Type} [Fintype σ] (Pr : AMProtocol σ) (t : ℕ), 1 ≤ Pr.c →
      Pr.V.depth ≤ t →
      ∃ R : Fin Pr.c → List (Fin Pr.ρ → Bool), (∀ i, 2 ≤ (R i).length) ∧
        ∏ i, (R i).length ≤ (C₀ * (Pr.c ^ 2 * (Fintype.card σ + Pr.c * (Pr.μ + 1)) *
          (Pr.μ + 1) * ((Pr.ρ + 1) * Pr.c + t))) ^ (3 ^ Pr.c) ∧
        ∀ x, |Pr.sVal R x - Pr.val x| ≤ 1 / 8 := by
  obtain ⟨C₀, hC₀⟩ := fixing_coins hC
  refine ⟨C₀, fun {σ} _ Pr t hc ht => ?_⟩
  obtain ⟨R, hR2, hRP, hRv⟩ := hC₀ (AMAux.pad Pr) t hc (by simp) (by simp)
    (by simpa [AMAux.pad] using ht)
  refine ⟨fun j => (R j).map Fin.init, fun i => by simpa using hR2 i, by simpa using hRP,
    fun x => ?_⟩
  rw [← AMAux.pad_sVal, ← AMAux.pad_val]
  exact hRv x

namespace AMAux

/-- The size bound of Lemma 7.7 is polynomial when `c ≤ m` and `ρ, μ, t ≤ B (m+1)^e`. -/
theorem A_bound (C₀ c n μ ρ t m B e : ℕ) (hc : c ≤ m + 1) (hn : n ≤ (m + 1) ^ 2)
    (hμ : μ ≤ B * (m + 1) ^ e) (hρ : ρ ≤ B * (m + 1) ^ e) (ht : t ≤ B * (m + 1) ^ e) :
    C₀ * (c ^ 2 * (n + c * (μ + 1)) * (μ + 1) * ((ρ + 1) * c + t)) ≤
      (4 * C₀ * (B + 1) ^ 3 + 1) * (m + 1) ^ (5 + 3 * e) := by
  set M := m + 1 with hM
  have hM1 : 1 ≤ M := by omega
  have hMe : 1 ≤ M ^ e := Nat.one_le_pow _ _ hM1
  set N := (B + 1) * M ^ e with hN
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hμN : μ + 1 ≤ N := by rw [hN]; nlinarith
  have hρN : ρ + 1 ≤ N := by rw [hN]; nlinarith
  have htN : t ≤ N := by rw [hN]; nlinarith
  have h1 : c ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left hc 2
  have h2 : n + c * (μ + 1) ≤ 2 * M ^ 2 * N := by
    have : c * (μ + 1) ≤ M * N := Nat.mul_le_mul hc hμN
    have a1 : M ^ 2 ≤ M ^ 2 * N := Nat.le_mul_of_pos_right _ hN1
    have a2 : M * N ≤ M ^ 2 * N := Nat.mul_le_mul_right _ (by nlinarith)
    linarith
  have h4 : (ρ + 1) * c + t ≤ 2 * M * N := by
    have : (ρ + 1) * c ≤ N * M := Nat.mul_le_mul hρN hc
    nlinarith
  calc C₀ * (c ^ 2 * (n + c * (μ + 1)) * (μ + 1) * ((ρ + 1) * c + t))
      ≤ C₀ * (M ^ 2 * (2 * M ^ 2 * N) * N * (2 * M * N)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h1 h2) hμN) h4)
    _ = 4 * C₀ * (B + 1) ^ 3 * M ^ (5 + 3 * e) := by rw [hN]; ring
    _ ≤ (4 * C₀ * (B + 1) ^ 3 + 1) * M ^ (5 + 3 * e) := Nat.mul_le_mul_right _ (by omega)

/-- The bound of the graph theorem, made explicit. -/
theorem graph_bound (Cg C₁ P t m B e k : ℕ) (ht : t ≤ B * (m + 1) ^ e) :
    Cg * ((m + 1) ^ 3 * (C₁ * P * (t + 1)) +
      (m + 1) ^ 2 * (min k (2 * (C₁ * P * (t + 1))) + 2) ^ 2 + m * m) ≤
      6 * Cg * (C₁ + 2) ^ 2 * (B + 1) ^ 2 * (m + 1) ^ (3 + 2 * e) * (P + 1) ^ 2 := by
  set M := m + 1 with hM
  have hM1 : 1 ≤ M := by omega
  have hMe : 1 ≤ M ^ e := Nat.one_le_pow _ _ hM1
  set Z := (C₁ + 2) * (B + 1) * M ^ e * (P + 1) with hZ
  have ht1 : t + 1 ≤ (B + 1) * M ^ e := by nlinarith
  have hZ1 : 1 ≤ Z := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hT : C₁ * P * (t + 1) + 1 ≤ Z := by
    have : (C₁ + 2) * (P + 1) * (t + 1) ≤ (C₁ + 2) * (P + 1) * ((B + 1) * M ^ e) :=
      Nat.mul_le_mul_left _ ht1
    have h' : C₁ * P * (t + 1) + 1 ≤ (C₁ + 2) * (P + 1) * (t + 1) := by nlinarith
    calc C₁ * P * (t + 1) + 1 ≤ (C₁ + 2) * (P + 1) * ((B + 1) * M ^ e) := h'.trans this
      _ = Z := by rw [hZ]; ring
  have hmin : min k (2 * (C₁ * P * (t + 1))) + 2 ≤ 2 * Z := by
    have := min_le_right k (2 * (C₁ * P * (t + 1)))
    omega
  have e1 : M ^ 3 * (C₁ * P * (t + 1)) ≤ M ^ 3 * Z ^ 2 :=
    Nat.mul_le_mul_left _ (by nlinarith)
  have e2 : M ^ 2 * (min k (2 * (C₁ * P * (t + 1))) + 2) ^ 2 ≤ 4 * (M ^ 3 * Z ^ 2) := by
    calc M ^ 2 * (min k (2 * (C₁ * P * (t + 1))) + 2) ^ 2 ≤ M ^ 2 * (2 * Z) ^ 2 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hmin 2)
      _ = 4 * (M ^ 2 * Z ^ 2) := by ring
      _ ≤ 4 * (M ^ 3 * Z ^ 2) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hM1 (by norm_num)))
  have e3 : m * m ≤ M ^ 3 * Z ^ 2 := by
    have : m * m ≤ M ^ 3 := by rw [hM]; nlinarith
    exact this.trans (Nat.le_mul_of_pos_right _ (by positivity))
  calc Cg * (M ^ 3 * (C₁ * P * (t + 1)) + M ^ 2 * (min k (2 * (C₁ * P * (t + 1))) + 2) ^ 2 +
        m * m) ≤ Cg * (6 * (M ^ 3 * Z ^ 2)) := Nat.mul_le_mul_left _ (by omega)
    _ = 6 * Cg * (C₁ + 2) ^ 2 * (B + 1) ^ 2 * M ^ (3 + 2 * e) * (P + 1) ^ 2 := by
        rw [hZ]; ring

end AMAux

/-- **Theorem 7.8.**  If protocols with `c_m` rounds and polynomially bounded `ρ`, `μ` and
verifier depth `t` decide `{Y = per_m(X)}`, then `c_m ≥ Ω(log log m)`. -/
theorem am_rounds (hS : SAFacts) (hLB : PermLowerBound) (hC : CountingBound)
    (Pr : ∀ m, AMProtocol (Option (Fin m × Fin m))) (t : ℕ → ℕ) (B e : ℕ)
    (hpoly : ∀ m, (Pr m).ρ + (Pr m).μ + t m ≤ B * (m + 1) ^ e) (ht : ∀ m, (Pr m).V.depth ≤ t m)
    (hdec : ∀ m, (Pr m).Decides (perGraph m)) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ᶠ m : ℕ in atTop, c' * Real.log (Real.log m) ≤ (Pr m).c := by
  obtain ⟨C₀, hC₀⟩ := fixing_coins_gen hC
  obtain ⟨C₁, hC₁⟩ := strategy_tree
  obtain ⟨Cg, hCg⟩ := graph_theorem hS
  set K : ℕ := 4 * C₀ * (B + 1) ^ 3 + 1 with hK
  set E : ℕ := 5 + 3 * e with hE
  have hK1 : 1 ≤ K := by omega
  -- Step 1: fixing the coins
  have hR : ∀ m, ∃ R : Fin (Pr m).c → List (Fin (Pr m).ρ → Bool), (∀ i, 2 ≤ (R i).length) ∧
      ((Pr m).c ≤ m → ∏ i, (R i).length ≤ (K * (m + 1) ^ E) ^ (3 ^ (Pr m).c)) ∧
      ∀ x, |(Pr m).sVal R x - (Pr m).val x| ≤ 1 / 8 := by
    intro m
    rcases Nat.eq_zero_or_pos (Pr m).c with hc | hc
    · have : IsEmpty (Fin (Pr m).c) := by rw [hc]; infer_instance
      refine ⟨fun i => isEmptyElim i, fun i => isEmptyElim i, fun _ => ?_, fun x => ?_⟩
      · rw [Finset.univ_eq_empty, Finset.prod_empty, hc, pow_zero, pow_one]
        exact Nat.one_le_iff_ne_zero.2 (by positivity)
      · have hsv : (Pr m).sVal (fun i => isEmptyElim i) x = (Pr m).val x := by
          unfold AMProtocol.sVal AMProtocol.val
          rw [AMProtocol.sValFrom.eq_1, AMProtocol.valFrom.eq_1, dite_eq_right (by omega),
            dite_eq_right (by omega)]
        rw [hsv, sub_self, abs_zero]
        norm_num
    · obtain ⟨R, h1, h2, h3⟩ := hC₀ (Pr m) (t m) hc (ht m)
      refine ⟨R, h1, fun hcm => h2.trans (Nat.pow_le_pow_left ?_ _), h3⟩
      have hp := hpoly m
      refine AMAux.A_bound C₀ _ _ _ _ _ m B e (by omega) ?_ (by omega) (by omega) (by omega)
      simp only [Fintype.card_option, Fintype.card_prod, Fintype.card_fin]
      nlinarith
  choose R hR2 hRP hRv using hR
  set P : ℕ → ℕ := fun m => ∏ i, (R m i).length with hPdef
  -- Step 2: the tree `T` and the graph theorem
  have hB : ∀ m, 1 ≤ m → BorderLE (per m)
      (6 * Cg * (C₁ + 2) ^ 2 * (B + 1) ^ 2 * (m + 1) ^ (3 + 2 * e) * (P m + 1) ^ 2) := by
    intro m hm
    obtain ⟨T, hTd, hT⟩ := hC₁ (Pr m) (t m) (R m) (ht m) (hR2 m)
    let f : Option (Fin m × Fin m) ⊕ Fin (2 * (Pr m).μ * ∏ i, (R m i).length) →
        (Fin m × Fin m) ⊕ Unit ⊕ Fin (2 * (Pr m).μ * ∏ i, (R m i).length) :=
      Sum.elim (fun o => Option.elim o (Sum.inr (Sum.inl ())) Sum.inl)
        (fun j => Sum.inr (Sum.inr j))
    have hdec' : ∀ x : Fin m × Fin m → ℝ, ∀ y : ℝ,
        (∃ z, (T.rename f).Accepts (inp3 x y z)) ↔ y = eval x (per m) := by
      intro x y
      let w : Option (Fin m × Fin m) → ℝ := fun o => Option.elim o y x
      have hw : ∀ z, inp3 x y z ∘ f = Sum.elim w z := by
        intro z
        funext p
        rcases p with (_ | p) | j <;> rfl
      have hacc : ∀ z, (T.rename f).Accepts (inp3 x y z) ↔ T.Accepts (Sum.elim w z) := by
        intro z
        rw [Tree.Accepts, Tree.run_rename, hw]
        rfl
      simp only [hacc]
      rw [hT w]
      have hmem : w ∈ perGraph m ↔ y = eval x (per m) := Iff.rfl
      rw [← hmem]
      have hv := hRv m w
      rw [abs_le] at hv
      constructor
      · intro h
        by_contra hn
        have := (hdec m w).2 hn
        linarith
      · intro h
        have := (hdec m w).1 h
        linarith
    have hg := hCg m (C₁ * P m * (t m + 1)) _ (per m) hm (totalDegree_per m) univ isOpen_univ
      univ_nonempty (T.rename f) (by rw [Tree.depth_rename]; exact hTd)
      (fun x _ y => hdec' x y)
    refine hg.mono ?_
    rw [Fintype.card_prod, Fintype.card_fin]
    exact AMAux.graph_bound Cg C₁ (P m) (t m) m B e _ (by have := hpoly m; omega)
  -- Step 3: the lower bound for the permanent
  obtain ⟨c₀, hc₀, hev⟩ := superPoly_of_borderLE hLB P
    (6 * Cg * (C₁ + 2) ^ 2 * (B + 1) ^ 2) (3 + 2 * e) 2
    (by filter_upwards [eventually_ge_atTop 1] with m hm; exact hB m hm)
  -- Step 4: the asymptotics
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hloglog : Tendsto (fun m : ℕ => Real.log (Real.log m)) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  refine ⟨1 / (6 * Real.log 3), by positivity, ?_⟩
  filter_upwards [hev, eventually_ge_atTop 3, eventually_ge_atTop (K * 2 ^ E),
    hloglog.eventually_ge_atTop (6 * (Real.log ((E : ℝ) + 1) - Real.log c₀))]
    with m hm hm3 hmK hmlog
  have hm1 : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  have hlogm : 0 < Real.log m := Real.log_pos hm1
  by_cases hcm : (Pr m).c ≤ m
  · set c := (Pr m).c with hcdef
    have hPle := hRP m hcm
    have hKm : K * (m + 1) ^ E ≤ m ^ (E + 1) := by
      have h2m : (m + 1) ^ E ≤ 2 ^ E * m ^ E := by
        rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) E
      calc K * (m + 1) ^ E ≤ K * (2 ^ E * m ^ E) := Nat.mul_le_mul_left _ h2m
        _ = K * 2 ^ E * m ^ E := by ring
        _ ≤ m * m ^ E := Nat.mul_le_mul_right _ hmK
        _ = m ^ (E + 1) := by ring
    have hPm : (P m : ℝ) ≤ (m : ℝ) ^ ((E + 1) * 3 ^ c) := by
      have : P m ≤ m ^ ((E + 1) * 3 ^ c) := by
        rw [pow_mul]
        exact hPle.trans (Nat.pow_le_pow_left hKm _)
      exact_mod_cast this
    set L := Real.logb 2 m with hLdef
    have hL : 0 < L := Real.logb_pos (by norm_num) hm1
    have h1 : c₀ * L ^ (4 / 3 : ℝ) ≤ (((E + 1) * 3 ^ c : ℕ) : ℝ) * L := by
      have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) (hm.trans hPm)
      rwa [Real.logb_rpow (by norm_num) (by norm_num), Real.logb_pow] at this
    have hL43 : L ^ (4 / 3 : ℝ) = L * L ^ (1 / 3 : ℝ) := by
      rw [show (4 / 3 : ℝ) = 1 + 1 / 3 by norm_num, Real.rpow_add hL, Real.rpow_one]
    have h2 : c₀ * L ^ (1 / 3 : ℝ) ≤ ((E : ℝ) + 1) * 3 ^ c := by
      rw [hL43] at h1
      push_cast at h1
      have h1' : L * (c₀ * L ^ (1 / 3 : ℝ)) ≤ L * (((E : ℝ) + 1) * 3 ^ c) := by linarith
      exact le_of_mul_le_mul_left h1' hL
    have h3 : Real.log c₀ + 1 / 3 * Real.log L ≤ Real.log ((E : ℝ) + 1) + c * Real.log 3 := by
      have := Real.log_le_log (by positivity) h2
      rwa [Real.log_mul (by positivity) (by positivity), Real.log_rpow hL,
        Real.log_mul (by positivity) (by positivity), Real.log_pow] at this
    have h4 : Real.log (Real.log m) ≤ Real.log L := by
      refine Real.log_le_log hlogm ?_
      rw [hLdef, Real.logb]
      rw [le_div_iff₀ (Real.log_pos (by norm_num))]
      have : Real.log 2 < 1 := by have := Real.log_two_lt_d9; norm_num at this; linarith
      nlinarith
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    nlinarith
  · replace hcm := not_le.1 hcm
    have hll : Real.log (Real.log m) ≤ m := by
      have h1 := Real.log_le_sub_one_of_pos hlogm
      have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < m by linarith)
      linarith
    have hc' : 1 / (6 * Real.log 3) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : Real.log 2 ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
      have := Real.log_two_gt_d9
      norm_num at this
      linarith
    have hcm' : (m : ℝ) ≤ (Pr m).c := by exact_mod_cast hcm.le
    by_cases hneg : Real.log (Real.log m) ≤ 0
    · have : 1 / (6 * Real.log 3) * Real.log (Real.log m) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg
      have h0 : (0 : ℝ) ≤ (Pr m).c := by positivity
      linarith
    · replace hneg := not_le.1 hneg
      nlinarith

end ClassSep
