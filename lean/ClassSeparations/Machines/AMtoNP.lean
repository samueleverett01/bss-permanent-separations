import ClassSeparations.Machines.Gather
import ClassSeparations.Machines.NPtoAM

/-!
# `AM_ℝ[c] ⊆ NP_ℝ` (the hard half of Theorem 7.6)

Let `M` be the verifier machine of a `c`-round protocol.  For each input size `n`:

* `M` unrolls into a tree (`Machine.unroll`); renaming its inputs along the layout of `amVec`
  gives a tree-level protocol `amPr` whose values are those of the machine-level protocol
  (`amPr_val`).
* Lemma 7.7 (`fixing_coins_gen`) gives lists `R` of coin strings with `|val' - val| ≤ 1/8`, so
  `x ∈ L ↔ val'(x) ≥ 1/2 ↔` some strategy tree `S` has at least half of the sampled leaves
  accepted (equation (12), `AMAux.cnt_spec`).
* The sampled leaves are enumerated explicitly (`leafD`): at each leaf, the input of `M` is
  gathered from `x`, the strategy tree `S` and the constants `0`, `1` (`posList`).

The machine that runs `M` at every leaf and counts acceptances is `gather_count`; it reads the
leaves (advice) from one real constant.
-/

set_option autoImplicit false

noncomputable section

open Classical

namespace ClassSep

namespace AMNPAux

open AMAux

/-! ## The layout of the verifier's input -/

/-- The input of the verifier tree held by the `j`-th register of `amVec`. -/
def amIdx (n c ρ μ : ℕ) (j : Fin (n + c * ρ + c * μ)) : AMInput (Fin n) c ρ μ :=
  if h : j.val < n then .inl ⟨j.val, h⟩
  else if h' : j.val < n + c * ρ then
    .inr (.inl (finProdFinEquiv.symm ⟨j.val - n, by omega⟩))
  else .inr (.inr (finProdFinEquiv.symm ⟨j.val - n - c * ρ, by have := j.isLt; omega⟩))

theorem amVec_apply {n c ρ μ : ℕ} (x : Fin n → ℝ) (r : Fin c → Fin ρ → Bool)
    (z : Fin c → Fin μ → ℝ) (j : Fin (n + c * ρ + c * μ)) :
    amVec x r z j = Sum.elim x (Sum.elim (fun p => if r p.1 p.2 then 1 else 0)
      (fun p => z p.1 p.2)) (amIdx n c ρ μ j) := by
  have h0 := vecReg_of_lt (amVec x r z) j.isLt
  simp only [Fin.eta] at h0
  rw [← h0]
  unfold amVec
  rw [vecReg_append, vecReg_append]
  unfold amIdx
  by_cases h1 : j.val < n
  · simp [h1, show j.val < n + c * ρ by omega, vecReg_of_lt _ h1]
  · by_cases h2 : j.val < n + c * ρ
    · rw [if_pos h2, if_neg h1, dif_neg h1, dif_pos h2]
      simp only [Sum.elim_inr, Sum.elim_inl]
      rw [vecReg_of_lt _ (show j.val - n < c * ρ by omega)]
    · rw [if_neg h2, dif_neg h1, dif_neg h2]
      simp only [Sum.elim_inr]
      rw [vecReg_of_lt _ (show j.val - (n + c * ρ) < c * μ by have := j.isLt; omega)]
      congr 3 <;> ext <;> simp <;> omega

/-! ## The tree-level protocol of a verifier machine -/

/-- The tree-level protocol of the verifier machine at size `n`, from an unrolling `τ`. -/
abbrev amPr (c : ℕ) (ρ μ : ℕ → ℕ) (τ : ∀ n, Tree (Fin (n + c * ρ n + c * μ n))) (n : ℕ) :
    AMProtocol (Fin n) :=
  ⟨c, ρ n, μ n, (τ n).rename (amIdx n c (ρ n) (μ n))⟩

theorem amPr_run (c : ℕ) (ρ μ : ℕ → ℕ) (τ : ∀ n, Tree (Fin (n + c * ρ n + c * μ n))) (n : ℕ)
    (x : Fin n → ℝ) (r : Fin c → Fin (ρ n) → Bool) (z : Fin c → Fin (μ n) → ℝ) :
    (amPr c ρ μ τ n).V.run ((amPr c ρ μ τ n).verInput x r z) = (τ n).run (amVec x r z) := by
  simp only [amPr, Tree.run_rename]
  congr 1
  funext j
  rw [amVec_apply]
  rfl

theorem amPr_valFrom (M : Machine) (c : ℕ) (ρ μ p : ℕ → ℕ)
    (τ : ∀ n, Tree (Fin (n + c * ρ n + c * μ n)))
    (hτ : ∀ n (w : Fin (n + c * ρ n + c * μ n) → ℝ) (o : Option Bool),
      M.run (p n) (initConfig [n, c * ρ n, c * μ n] (vecReg w)) = some o → (τ n).run w = o)
    (n : ℕ) (x : Fin n → ℝ)
    (hhalt : ∀ (r : Fin c → Fin (ρ n) → Bool) (z : Fin c → Fin (μ n) → ℝ),
      M.HaltsWithin (p n) [n, c * ρ n, c * μ n] (amVec x r z)) :
    ∀ m i, c - i = m → ∀ (r : Fin c → Fin (ρ n) → Bool) (z : Fin c → Fin (μ n) → ℝ),
      (amPr c ρ μ τ n).valFrom x i r z =
      amValFrom c (ρ n) (μ n) (fun r z => M.HaltsWith (p n) [n, c * ρ n, c * μ n]
        (amVec x r z) (some true)) i r z := by
  intro m
  induction m with
  | zero =>
    intro i hm r z
    rw [AMProtocol.valFrom]
    rw [amValFrom]
    simp only [show (amPr c ρ μ τ n).c = c from rfl, dif_neg (show ¬ i < c by omega)]
    obtain ⟨o, ho⟩ := hhalt r z
    have hrun := amPr_run c ρ μ τ n x r z
    rw [hτ n _ o ho] at hrun
    have : (amPr c ρ μ τ n).V.Accepts ((amPr c ρ μ τ n).verInput x r z) ↔
        M.HaltsWith (p n) [n, c * ρ n, c * μ n] (amVec x r z) (some true) := by
      unfold Tree.Accepts Machine.HaltsWith
      rw [hrun]
      unfold Machine.HaltsWith at ho
      rw [ho]
      simp
    simp only [this]
  | succ m ih =>
    intro i hm r z
    rw [AMProtocol.valFrom, amValFrom]
    simp only [show (amPr c ρ μ τ n).c = c from rfl, dif_pos (show i < c by omega)]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    congr 1
    funext y
    exact ih (i + 1) (by omega) _ _

/-! ## The sampled leaves -/

section Leaves

variable {σ : Type} (Pr : AMProtocol σ) (R : Fin Pr.c → List (Fin Pr.ρ → Bool))

/-- Where a message of a leaf below round `i + 1` sits, seen from round `i` (for the `a`-th
element of `Rᵢ`): the message of round `i` is in the strategy tree. -/
def stepMsg (i : ℕ) (h : i < Pr.c) (a : Fin (R ⟨i, h⟩).length) :
    (Fin Pr.c × Fin Pr.μ) ⊕ Fin (sD Pr R (i + 1)) → (Fin Pr.c × Fin Pr.μ) ⊕ Fin (sD Pr R i) :=
  Sum.elim (fun p => if p.1 = ⟨i, h⟩ then .inr (msgIdx Pr R i h a p.2) else .inl p)
    (fun d => .inr (subIdx Pr R i h a d))

/-- The sampled leaves below round `i`: the coins and, for every message, where it sits (in the
history `z`, or in the strategy tree). -/
def leafD (i : ℕ) (r : Fin Pr.c → Fin Pr.ρ → Bool) :
    List ((Fin Pr.c → Fin Pr.ρ → Bool) ×
      (Fin Pr.c → Fin Pr.μ → (Fin Pr.c × Fin Pr.μ) ⊕ Fin (sD Pr R i))) :=
  if h : i < Pr.c then
    (List.finRange (R ⟨i, h⟩).length).flatMap fun a =>
      (leafD (i + 1) (Function.update r ⟨i, h⟩ (R ⟨i, h⟩)[a])).map fun lf =>
        (lf.1, fun j k => stepMsg Pr R i h a (lf.2 j k))
  else [(r, fun j k => .inl (j, k))]
termination_by Pr.c - i

theorem leafD_succ (i : ℕ) (h : i < Pr.c) (r : Fin Pr.c → Fin Pr.ρ → Bool) :
    leafD Pr R i r = (List.finRange (R ⟨i, h⟩).length).flatMap fun a =>
      (leafD Pr R (i + 1) (Function.update r ⟨i, h⟩ (R ⟨i, h⟩)[a])).map fun lf =>
        (lf.1, fun j k => stepMsg Pr R i h a (lf.2 j k)) := by
  rw [leafD, dif_pos h]

theorem leafD_of_le (i : ℕ) (h : Pr.c ≤ i) (r : Fin Pr.c → Fin Pr.ρ → Bool) :
    leafD Pr R i r = [(r, fun j k => .inl (j, k))] := by
  rw [leafD, dif_neg (by omega)]

theorem length_leafD (i : ℕ) (r : Fin Pr.c → Fin Pr.ρ → Bool) :
    (leafD Pr R i r).length = sP Pr R i := by
  by_cases h : i < Pr.c
  · rw [leafD_succ Pr R i h, sP_succ Pr R i h, List.length_flatMap]
    simp only [List.length_map, length_leafD (i + 1)]
    rw [← Fin.sum_univ_def]
    simp
  · rw [leafD_of_le Pr R i (by omega), sP_of_le Pr R i (by omega)]
    rfl
termination_by Pr.c - i

/-- The messages at a leaf, from the history `z` and the strategy tree `S`. -/
def leafMsg {N : ℕ} (z : Fin Pr.c → Fin Pr.μ → ℝ) (S : Fin N → ℝ)
    (m : Fin Pr.c → Fin Pr.μ → (Fin Pr.c × Fin Pr.μ) ⊕ Fin N) : Fin Pr.c → Fin Pr.μ → ℝ :=
  fun j k => Sum.elim (fun p => z p.1 p.2) S (m j k)

theorem leafMsg_stepMsg (z : Fin Pr.c → Fin Pr.μ → ℝ) (i : ℕ) (h : i < Pr.c)
    (a : Fin (R ⟨i, h⟩).length) (S : Fin (sD Pr R i) → ℝ)
    (m : Fin Pr.c → Fin Pr.μ → (Fin Pr.c × Fin Pr.μ) ⊕ Fin (sD Pr R (i + 1))) :
    leafMsg Pr z S (fun j k => stepMsg Pr R i h a (m j k)) =
      leafMsg Pr (Function.update z ⟨i, h⟩ fun k => S (msgIdx Pr R i h a k))
        (S ∘ subIdx Pr R i h a) m := by
  funext j k
  simp only [leafMsg]
  rcases m j k with p | d
  · by_cases hp : p.1 = ⟨i, h⟩
    · simp [stepMsg, hp]
    · simp [stepMsg, hp, Function.update_of_ne hp]
  · simp [stepMsg]

/-- The number of accepting sampled leaves, as a count over the explicit leaves. -/
theorem cnt_eq_countP (x : σ → ℝ) (i : ℕ) (r : Fin Pr.c → Fin Pr.ρ → Bool)
    (z : Fin Pr.c → Fin Pr.μ → ℝ) (S : Fin (sD Pr R i) → ℝ) :
    cnt Pr R x i r z S = (leafD Pr R i r).countP fun lf =>
      decide (Pr.V.Accepts (Pr.verInput x lf.1 (leafMsg Pr z S lf.2))) := by
  by_cases h : i < Pr.c
  · rw [cnt_succ Pr R x i h, leafD_succ Pr R i h, List.countP_flatMap, ← Fin.sum_univ_def]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [cnt_eq_countP x (i + 1)]
    simp only [Function.comp_apply, List.countP_map]
    congr 1
    funext lf
    simp only [Function.comp_apply, leafMsg_stepMsg]
  · rw [cnt, LT_of_le Pr R i (by omega), leafD_of_le Pr R i (by omega), List.countP_singleton,
      List.countP_singleton, leaf_run]
    have hz : leafMsg Pr z S (fun j k => .inl (j, k)) = z := rfl
    simp only [hz, Tree.Accepts]
termination_by Pr.c - i

end Leaves

/-! ## Positions of the gathered inputs -/

/-- The source position of the `j`-th input of the verifier at a leaf: `x` is at `0, …, n-1`,
the strategy tree at `n, …, n+q-1`, and the constants `0`, `1` at `n+q`, `n+q+1`. -/
def posOf (n c ρ μ q : ℕ) (lf : (Fin c → Fin ρ → Bool) × (Fin c → Fin μ → (Fin c × Fin μ) ⊕ Fin q))
    (j : Fin (n + c * ρ + c * μ)) : ℕ :=
  match amIdx n c ρ μ j with
  | .inl i => i.val
  | .inr (.inl p) => n + q + (if lf.1 p.1 p.2 then 1 else 0)
  | .inr (.inr p) => match lf.2 p.1 p.2 with
    | .inl _ => n + q
    | .inr d => n + d.val

/-- The positions of all inputs at a leaf. -/
def posList (n c ρ μ q : ℕ)
    (lf : (Fin c → Fin ρ → Bool) × (Fin c → Fin μ → (Fin c × Fin μ) ⊕ Fin q)) : List ℕ :=
  List.ofFn (posOf n c ρ μ q lf)

theorem posOf_le (n c ρ μ q : ℕ) (lf) (j : Fin (n + c * ρ + c * μ)) :
    posOf n c ρ μ q lf j ≤ n + q + 1 := by
  unfold posOf
  split
  · rename_i i _; have := i.isLt; omega
  · split_ifs <;> omega
  · split
    · omega
    · rename_i d _; have := d.isLt; omega

theorem srcVal_posOf {n c ρ μ q : ℕ} (x : Fin n → ℝ) (S : Fin q → ℝ)
    (lf : (Fin c → Fin ρ → Bool) × (Fin c → Fin μ → (Fin c × Fin μ) ⊕ Fin q))
    (j : Fin (n + c * ρ + c * μ)) :
    srcVal x S (posOf n c ρ μ q lf j) = amVec x lf.1
      (fun a b => Sum.elim (fun _ => (0 : ℝ)) S (lf.2 a b)) j := by
  rw [amVec_apply]
  unfold posOf
  split
  · rename_i i hi
    rw [hi]
    simp only [Sum.elim_inl, srcVal, if_pos (show i.val < n + q by omega), vecReg_append,
      if_pos i.isLt, vecReg_of_lt _ i.isLt]
  · rename_i p hp
    rw [hp]
    simp only [Sum.elim_inr, Sum.elim_inl, srcVal]
    split_ifs <;> first | omega | rfl
  · rename_i p hp
    rw [hp]
    simp only [Sum.elim_inr]
    split
    · rename_i w hw
      simp [srcVal, hw]
    · rename_i d hd
      simp only [hd, Sum.elim_inr, srcVal, if_pos (show n + d.val < n + q by omega),
        vecReg_append, if_neg (show ¬ n + d.val < n by omega), Nat.add_sub_cancel_left,
        vecReg_of_lt _ d.isLt]

theorem gather_posList {n c ρ μ q : ℕ} (x : Fin n → ℝ) (S : Fin q → ℝ)
    (lf : (Fin c → Fin ρ → Bool) × (Fin c → Fin μ → (Fin c × Fin μ) ⊕ Fin q)) :
    gather x S (n + c * ρ + c * μ) (posList n c ρ μ q lf) =
      amVec x lf.1 (fun a b => Sum.elim (fun _ => (0 : ℝ)) S (lf.2 a b)) := by
  funext j
  rw [← srcVal_posOf]
  simp only [gather, posList]
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

/-! ## Polynomial bounds -/

theorem pb_pow {f : ℕ → ℕ} (hf : PolyBounded f) (k : ℕ) : PolyBounded fun n => f n ^ k := by
  induction k with
  | zero => simpa using pb_const 1
  | succ k ih => simpa [pow_succ] using pb_mul ih hf

/-! ## The theorem -/

/-- **`AM_ℝ[c] ⊆ NP_ℝ`**, from the counting bound (C) (via Lemma 7.7). -/
theorem am_sub_np (hC : CountingBound) (c : ℕ) (hc : 1 ≤ c) : AM_R c ⊆ NP_R := by
  rintro L ⟨M, ρ, μ, p, hρ, hμ, hp, hprot⟩
  -- unrolling
  have hU := fun n => M.unroll [n, c * ρ n, c * μ n] (n + c * ρ n + c * μ n) (p n)
  choose τ hτd _hτc hτ using hU
  set Pr := amPr c ρ μ τ with hPr
  have hval : ∀ n (x : Fin n → ℝ), (Pr n).val x = amValFrom c (ρ n) (μ n)
      (fun r z => M.HaltsWith (p n) [n, c * ρ n, c * μ n] (amVec x r z) (some true)) 0
      (fun _ _ => false) (fun _ _ => 0) := fun n x =>
    amPr_valFrom M c ρ μ p τ (fun n w o h => hτ n w o h) n x (hprot n x).1 c 0 (by omega) _ _
  -- fixing the coins
  obtain ⟨C₀, hC₀⟩ := fixing_coins_gen hC
  have hR := fun n => hC₀ (Pr n) (p n + 1) hc (by
    show ((τ n).rename _).depth ≤ p n + 1
    rw [Tree.depth_rename]; exact hτd n)
  choose R hR2 hRP hRv using hR
  have hR0 : ∀ n i, 0 < (R n i).length := fun n i => by have := hR2 n i; omega
  -- equation (12): `x ∈ L ↔ ∃ S, P ≤ 2 cnt S`
  set r₀ : ∀ n, Fin c → Fin (ρ n) → Bool := fun n _ _ => false
  set z₀ : ∀ n, Fin c → Fin (μ n) → ℝ := fun n _ _ => 0
  have hmem : ∀ n (x : Fin n → ℝ), x ∈ L n ↔ ∃ S : Fin (sD (Pr n) (R n) 0) → ℝ,
      sP (Pr n) (R n) 0 ≤ 2 * cnt (Pr n) (R n) x 0 (r₀ n) (z₀ n) S := by
    intro n x
    have hv := hRv n x
    have hprotx := (hprot n x).2
    simp only at hprotx
    rw [← hval n x] at hprotx
    have hspec := cnt_spec (Pr n) (R n) (hR0 n) x 0 (r₀ n) (z₀ n)
    have hPpos : (0 : ℝ) < sP (Pr n) (R n) 0 := by exact_mod_cast sP_pos _ _ (hR0 n) 0
    have hs : (Pr n).sVal (R n) x = (Pr n).sValFrom (R n) x 0 (r₀ n) (z₀ n) := rfl
    constructor
    · intro hx
      have h1 := hprotx.1 hx
      obtain ⟨S, hS⟩ := hspec.2
      refine ⟨S, ?_⟩
      have : (sP (Pr n) (R n) 0 : ℝ) ≤ 2 * (cnt (Pr n) (R n) x 0 (r₀ n) (z₀ n) S : ℝ) := by
        rw [hS, ← hs]
        have := abs_le.1 hv
        nlinarith
      exact_mod_cast this
    · rintro ⟨S, hS⟩
      by_contra hx
      have h1 := hprotx.2 hx
      have h2 := hspec.1 S
      have h3 : (sP (Pr n) (R n) 0 : ℝ) ≤ 2 * (cnt (Pr n) (R n) x 0 (r₀ n) (z₀ n) S : ℝ) := by
        exact_mod_cast hS
      rw [← hs] at h2
      have := abs_le.1 hv
      nlinarith
  -- the leaves
  set q : ℕ → ℕ := fun n => sD (Pr n) (R n) 0 with hqdef
  set leaves : ℕ → List (List ℕ) := fun n =>
    (leafD (Pr n) (R n) 0 (r₀ n)).map (posList n c (ρ n) (μ n) (q n)) with hleaves
  have hcount : ∀ n (x : Fin n → ℝ) (S : Fin (q n) → ℝ),
      cnt (Pr n) (R n) x 0 (r₀ n) (z₀ n) S = (leaves n).countP fun ℓ =>
        decide (M.HaltsWith (p n) [n, c * ρ n, c * μ n]
          (gather x S (n + c * ρ n + c * μ n) ℓ) (some true)) := by
    intro n x S
    rw [cnt_eq_countP, List.countP_map]
    congr 1
    funext lf
    simp only [Function.comp_apply, gather_posList]
    congr 1
    obtain ⟨o, ho⟩ := (hprot n x).1 lf.1 (fun a b => Sum.elim (fun _ => (0 : ℝ)) S (lf.2 a b))
    have hrun := amPr_run c ρ μ τ n x lf.1 (fun a b => Sum.elim (fun _ => (0 : ℝ)) S (lf.2 a b))
    rw [hτ n _ o ho] at hrun
    have hlm : leafMsg (Pr n) (z₀ n) S lf.2 =
        fun a b => Sum.elim (fun _ => (0 : ℝ)) S (lf.2 a b) := by
      funext a b
      simp only [leafMsg]
      rcases lf.2 a b <;> rfl
    rw [hlm]
    unfold Tree.Accepts Machine.HaltsWith
    rw [hrun]
    unfold Machine.HaltsWith at ho
    rw [ho]
    simp
  -- polynomial bounds
  have hPb : PolyBounded fun n => sP (Pr n) (R n) 0 := by
    refine pb_mono (g := fun n => (C₀ * (c ^ 2 * (n + c * (μ n + 1)) * (μ n + 1) *
      ((ρ n + 1) * c + (p n + 1)))) ^ 3 ^ c) ?_ fun n => ?_
    · refine pb_pow ?_ _
      pb_tac
    · rw [sP_zero]
      have := hRP n
      simpa [Pr, amPr] using this
  have hqb : PolyBounded q := by
    refine pb_mono (g := fun n => 2 * μ n * sP (Pr n) (R n) 0) ?_ fun n => ?_
    · pb_tac
    · have : sD (Pr n) (R n) 0 + 2 * μ n ≤ 2 * μ n * sP (Pr n) (R n) 0 :=
        sD_bound (Pr n) (R n) (hR2 n) 0
      simp only [hqdef]
      omega
  -- the counting machine
  obtain ⟨N, p', hp', hN⟩ := gather_count M (fun n => c * ρ n) (fun n => c * μ n) p q leaves
    (fun n => (sP (Pr n) (R n) 0 + 1) / 2) (by pb_tac) (by pb_tac) hp hqb
    (by
      refine pb_mono hPb fun n => ?_
      simp only [hleaves, List.length_map]
      exact (length_leafD (Pr n) (R n) 0 (r₀ n)).le)
    (by
      intro n ℓ hℓ
      simp only [hleaves, List.mem_map] at hℓ
      obtain ⟨lf, -, rfl⟩ := hℓ
      simp [posList])
    (by
      intro n ℓ hℓ k hk
      simp only [hleaves, List.mem_map] at hℓ
      obtain ⟨lf, -, rfl⟩ := hℓ
      simp only [posList, List.mem_ofFn] at hk
      obtain ⟨j, rfl⟩ := hk
      exact posOf_le _ _ _ _ _ _ _)
    (by
      intro n
      simp only [hleaves, List.length_map]
      rw [length_leafD (Pr n) (R n) 0 (r₀ n)]
      omega)
    (by
      intro n x S ℓ hℓ
      simp only [hleaves, List.mem_map] at hℓ
      obtain ⟨lf, -, rfl⟩ := hℓ
      rw [gather_posList]
      exact (hprot n x).1 _ _)
  refine ⟨N, p', q, hp', hqb, fun n x => ⟨fun S => (hN n x S).1, ?_⟩⟩
  rw [hmem n x]
  refine exists_congr fun S => ?_
  rw [(hN n x S).2, ← hcount n x S]
  omega

end AMNPAux

end ClassSep
