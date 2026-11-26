import ClassSeparations.Machines.RyserCircuit
import ClassSeparations.Machines.Complex
import ClassSeparations.Cert.Permanent

/-!
# The Ryser circuits: evaluation, validity, depth

* Circuits given by a gate function `g : ℕ → AGate` (the list `(List.range N).map g`) are
  evaluated gate by gate (`GateEval.val`), uniformly over `ℝ` (sign gates) and `ℂ` (the gates
  mapped by `AGate.toC`, zero tests): `ACircuit.values_range`, `CCircuit.values_range`.
* Depths: `ACircuit.depth_range_le`, `CCircuit.depth_range_le`.
* For the Ryser circuits `Ryser.circ m last`: all gates are valid (`Ryser.gate_valid`), the
  gate values are given by Ryser's formula (`Ryser.val_root`), and the depth is `≤ 3m + 4`.
-/

noncomputable section

open Classical MvPolynomial

namespace ClassSep

/-! ## Circuits given by a gate function -/

/-- A gate that is valid at position `i`: no division, operands refer to earlier gates. -/
def AGate.ValidAt (i : ℕ) : AGate → Prop
  | .input _ => True
  | .const _ => True
  | .arith op j k => op ≠ .div ∧ j < i ∧ k < i
  | .sign j => j < i

/-- The complex gate corresponding to a real gate (sign gates become zero tests). -/
def AGate.toC : AGate → CGate
  | .input i => .input i
  | .const c => .const (c : ℂ)
  | .arith op j k => .arith op j k
  | .sign j => .isZero j

namespace GateEval

variable {K : Type*} [CommRing K] (e : ℝ → K) (τ : K → K) (x : ℕ → K)

/-- The value of a gate given the values of the earlier gates. -/
def eval1 (g : AGate) (vals : List K) : K :=
  match g with
  | .input t => x t
  | .const c => e c
  | .arith .add j k => vals.getD j 0 + vals.getD k 0
  | .arith .sub j k => vals.getD j 0 - vals.getD k 0
  | .arith .mul j k => vals.getD j 0 * vals.getD k 0
  | .arith .div _ _ => 0
  | .sign j => τ (vals.getD j 0)

/-- The values of the first `N` gates. -/
def vlist (g : ℕ → AGate) : ℕ → List K
  | 0 => []
  | N + 1 => vlist g N ++ [eval1 e τ x (g N) (vlist g N)]

/-- The value of gate `i`. -/
def val (g : ℕ → AGate) (i : ℕ) : K := eval1 e τ x (g i) (vlist e τ x g i)

variable (g : ℕ → AGate)

@[simp] theorem length_vlist (N : ℕ) : (vlist e τ x g N).length = N := by
  induction N with
  | zero => rfl
  | succ N ih => simp [vlist, ih]

theorem vlist_getD {N i : ℕ} (h : i < N) : (vlist e τ x g N).getD i 0 = val e τ x g i := by
  induction N with
  | zero => omega
  | succ N ih =>
    rw [vlist]
    rcases Nat.lt_or_ge i N with h' | h'
    · rw [List.getD_append _ _ _ _ (by simp [h']), ih h']
    · have hi : i = N := by omega
      subst hi
      rw [List.getD_append_right _ _ _ _ (by simp)]
      simp [val]

theorem vlist_getLast (N : ℕ) : (vlist e τ x g (N + 1)).getLast? = some (val e τ x g N) := by
  rw [vlist, List.getLast?_concat]
  rfl

variable {e τ x g}

theorem val_input {i t : ℕ} (h : g i = .input t) : val e τ x g i = x t := by
  simp [val, h, eval1]

theorem val_const {i : ℕ} {c : ℝ} (h : g i = .const c) : val e τ x g i = e c := by
  simp [val, h, eval1]

theorem val_add {i j k : ℕ} (h : g i = .arith .add j k) (hj : j < i) (hk : k < i) :
    val e τ x g i = val e τ x g j + val e τ x g k := by
  show eval1 e τ x (g i) (vlist e τ x g i) = _
  rw [h]
  simp only [eval1]
  rw [vlist_getD e τ x g hj, vlist_getD e τ x g hk]

theorem val_sub {i j k : ℕ} (h : g i = .arith .sub j k) (hj : j < i) (hk : k < i) :
    val e τ x g i = val e τ x g j - val e τ x g k := by
  show eval1 e τ x (g i) (vlist e τ x g i) = _
  rw [h]
  simp only [eval1]
  rw [vlist_getD e τ x g hj, vlist_getD e τ x g hk]

theorem val_mul {i j k : ℕ} (h : g i = .arith .mul j k) (hj : j < i) (hk : k < i) :
    val e τ x g i = val e τ x g j * val e τ x g k := by
  show eval1 e τ x (g i) (vlist e τ x g i) = _
  rw [h]
  simp only [eval1]
  rw [vlist_getD e τ x g hj, vlist_getD e τ x g hk]

theorem val_sign {i j : ℕ} (h : g i = .sign j) (hj : j < i) :
    val e τ x g i = τ (val e τ x g j) := by
  show eval1 e τ x (g i) (vlist e τ x g i) = _
  rw [h]
  simp only [eval1]
  rw [vlist_getD e τ x g hj]

end GateEval

/-- The sign test as a function. -/
def signTest (v : ℝ) : ℝ := if 0 ≤ v then 1 else 0

/-- The zero test as a function. -/
def zeroTest (v : ℂ) : ℂ := if v = 0 then 1 else 0

theorem ACircuit.values_append (C : ACircuit) (a : AGate) (x : ℕ → ℝ) :
    ACircuit.values (C ++ [a]) x = (ACircuit.values C x).bind fun vals =>
      match a with
      | .input i => some (vals ++ [x i])
      | .const c => some (vals ++ [c])
      | .arith op j k =>
          if hj : j < vals.length then if hk : k < vals.length then
            (op.apply? vals[j] vals[k]).map fun v => vals ++ [v]
          else none else none
      | .sign j => if hj : j < vals.length then
          some (vals ++ [if 0 ≤ vals[j] then 1 else 0]) else none := by
  unfold ACircuit.values
  rw [List.foldl_append]
  rfl

theorem ACircuit.values_range (g : ℕ → AGate) (N : ℕ) (x : ℕ → ℝ)
    (hv : ∀ i < N, (g i).ValidAt i) :
    ACircuit.values ((List.range N).map g) x = some (GateEval.vlist id signTest x g N) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, ACircuit.values_append,
      ih (fun i hi => hv i (by omega)), Option.bind_some]
    have hvN := hv N (by omega)
    simp only [GateEval.vlist]
    rcases hg : g N with t | c | ⟨op, j, k⟩ | j <;> rw [hg] at hvN
    · simp [GateEval.eval1]
    · simp [GateEval.eval1]
    · obtain ⟨hop, hj, hk⟩ := hvN
      simp only [GateEval.length_vlist, dif_pos hj, dif_pos hk]
      rw [← List.getD_eq_getElem _ 0, ← List.getD_eq_getElem _ 0]
      cases op with
      | add => simp [TOp.apply?, GateEval.eval1]
      | sub => simp [TOp.apply?, GateEval.eval1]
      | mul => simp [TOp.apply?, GateEval.eval1]
      | div => exact absurd rfl hop
    · have hj : j < N := hvN
      simp only [GateEval.length_vlist, dif_pos hj]
      rw [← List.getD_eq_getElem _ 0]
      simp [GateEval.eval1, signTest]

theorem CCircuit.values_append (C : CCircuit) (a : CGate) (x : ℕ → ℂ) :
    CCircuit.values (C ++ [a]) x = (CCircuit.values C x).bind fun vals =>
      match a with
      | .input i => some (vals ++ [x i])
      | .const c => some (vals ++ [c])
      | .arith op j k =>
          if hj : j < vals.length then if hk : k < vals.length then
            (op.applyC? vals[j] vals[k]).map fun v => vals ++ [v]
          else none else none
      | .isZero j => if hj : j < vals.length then
          some (vals ++ [if vals[j] = 0 then 1 else 0]) else none := by
  unfold CCircuit.values
  rw [List.foldl_append]
  rfl

theorem CCircuit.values_range (g : ℕ → AGate) (N : ℕ) (x : ℕ → ℂ)
    (hv : ∀ i < N, (g i).ValidAt i) :
    CCircuit.values ((List.range N).map fun i => (g i).toC) x =
      some (GateEval.vlist (fun c : ℝ => (c : ℂ)) zeroTest x g N) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, CCircuit.values_append,
      ih (fun i hi => hv i (by omega)), Option.bind_some]
    have hvN := hv N (by omega)
    simp only [GateEval.vlist]
    rcases hg : g N with t | c | ⟨op, j, k⟩ | j <;> rw [hg] at hvN
    · simp [GateEval.eval1, AGate.toC]
    · simp [GateEval.eval1, AGate.toC]
    · obtain ⟨hop, hj, hk⟩ := hvN
      simp only [AGate.toC, GateEval.length_vlist, dif_pos hj, dif_pos hk]
      rw [← List.getD_eq_getElem _ 0, ← List.getD_eq_getElem _ 0]
      cases op with
      | add => simp [TOp.applyC?, GateEval.eval1]
      | sub => simp [TOp.applyC?, GateEval.eval1]
      | mul => simp [TOp.applyC?, GateEval.eval1]
      | div => exact absurd rfl hop
    · have hj : j < N := hvN
      simp only [AGate.toC, GateEval.length_vlist, dif_pos hj]
      rw [← List.getD_eq_getElem _ 0]
      simp [GateEval.eval1, zeroTest]

/-! ## Depths -/

namespace GateDepth

/-- The depth of a gate given the depths of the earlier gates. -/
def dep1 (g : AGate) (ds : List ℕ) : ℕ :=
  match g with
  | .input _ => 0
  | .const _ => 0
  | .arith _ j k => max (ds.getD j 0) (ds.getD k 0) + 1
  | .sign j => ds.getD j 0 + 1

/-- The depths of the first `N` gates. -/
def dlist (g : ℕ → AGate) : ℕ → List ℕ
  | 0 => []
  | N + 1 => dlist g N ++ [dep1 (g N) (dlist g N)]

/-- The depth of gate `i`. -/
def dep (g : ℕ → AGate) (i : ℕ) : ℕ := dep1 (g i) (dlist g i)

variable (g : ℕ → AGate)

@[simp] theorem length_dlist (N : ℕ) : (dlist g N).length = N := by
  induction N with
  | zero => rfl
  | succ N ih => simp [dlist, ih]

theorem dlist_getD {N i : ℕ} (h : i < N) : (dlist g N).getD i 0 = dep g i := by
  induction N with
  | zero => omega
  | succ N ih =>
    rw [dlist]
    rcases Nat.lt_or_ge i N with h' | h'
    · rw [List.getD_append _ _ _ _ (by simp [h']), ih h']
    · have hi : i = N := by omega
      subst hi
      rw [List.getD_append_right _ _ _ _ (by simp)]
      simp [dep]

theorem mem_dlist {N d : ℕ} (h : d ∈ dlist g N) : ∃ i < N, d = dep g i := by
  induction N with
  | zero => simp [dlist] at h
  | succ N ih =>
    rw [dlist, List.mem_append, List.mem_singleton] at h
    rcases h with h | h
    · obtain ⟨i, hi, rfl⟩ := ih h
      exact ⟨i, by omega, rfl⟩
    · exact ⟨N, by omega, h⟩

variable {g}

theorem dep_input {i t : ℕ} (h : g i = .input t) : dep g i = 0 := by
  simp [dep, dep1, h]

theorem dep_const {i : ℕ} {c : ℝ} (h : g i = .const c) : dep g i = 0 := by
  simp [dep, dep1, h]

theorem dep_arith {i j k : ℕ} {op : TOp} (h : g i = .arith op j k) (hj : j < i) (hk : k < i) :
    dep g i = max (dep g j) (dep g k) + 1 := by
  show dep1 (g i) (dlist g i) = _
  rw [h]
  simp only [dep1]
  rw [dlist_getD g hj, dlist_getD g hk]

theorem dep_sign {i j : ℕ} (h : g i = .sign j) (hj : j < i) : dep g i = dep g j + 1 := by
  show dep1 (g i) (dlist g i) = _
  rw [h]
  simp only [dep1]
  rw [dlist_getD g hj]

end GateDepth

theorem foldl_max_le {l : List ℕ} {a D : ℕ} (ha : a ≤ D) (h : ∀ d ∈ l, d ≤ D) :
    l.foldl max a ≤ D := by
  induction l generalizing a with
  | nil => simpa
  | cons b l ih =>
    simp only [List.foldl_cons]
    exact ih (max_le ha (h b (by simp))) (fun d hd => h d (by simp [hd]))

theorem ACircuit.gateDepths_range (g : ℕ → AGate) (N : ℕ) :
    ACircuit.gateDepths ((List.range N).map g) = GateDepth.dlist g N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.map_singleton]
    unfold ACircuit.gateDepths at ih ⊢
    rw [List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, GateDepth.dlist]
    congr 2

theorem CCircuit.gateDepths_range (g : ℕ → AGate) (N : ℕ) :
    CCircuit.gateDepths ((List.range N).map fun i => (g i).toC) = GateDepth.dlist g N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.map_singleton]
    unfold CCircuit.gateDepths at ih ⊢
    rw [List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, GateDepth.dlist]
    congr 2
    rcases g N with t | c | ⟨op, j, k⟩ | j <;> rfl

theorem ACircuit.depth_range_le (g : ℕ → AGate) (N D : ℕ)
    (h : ∀ i < N, GateDepth.dep g i ≤ D) : ACircuit.depth ((List.range N).map g) ≤ D := by
  unfold ACircuit.depth
  rw [ACircuit.gateDepths_range]
  refine foldl_max_le (Nat.zero_le _) fun d hd => ?_
  obtain ⟨i, hi, rfl⟩ := GateDepth.mem_dlist g hd
  exact h i hi

theorem CCircuit.depth_range_le (g : ℕ → AGate) (N D : ℕ)
    (h : ∀ i < N, GateDepth.dep g i ≤ D) :
    CCircuit.depth ((List.range N).map fun i => (g i).toC) ≤ D := by
  unfold CCircuit.depth
  rw [CCircuit.gateDepths_range]
  refine foldl_max_le (Nat.zero_le _) fun d hd => ?_
  obtain ⟨i, hi, rfl⟩ := GateDepth.mem_dlist g hd
  exact h i hi

/-! ## Validity of the Ryser circuits -/

namespace Ryser

theorem idx_mono {m t F I J k F' I' J' k' : ℕ} (hF : F ≤ F') (hI : I ≤ I') (hJ : J ≤ J')
    (hk : k ≤ k') : idx m t F I J k ≤ idx m t F' I' J' k' := by
  unfold idx
  gcongr

theorem two_mul_mod_add_one_lt' {m : ℕ} (hm : 1 ≤ m) (J : ℕ) : 2 * J % 2 ^ m + 1 < 2 ^ m := by
  have h1 : 2 ^ m = 2 * 2 ^ (m - 1) := by rw [← pow_succ']; congr 1; omega
  have h2 : 2 * J % 2 ^ m = 2 * (J % 2 ^ (m - 1)) := by rw [h1, Nat.mul_mod_mul_left]
  have h3 := Nat.mod_lt J (Nat.two_pow_pos (m - 1))
  omega

/-- The fields of an index, and its decomposition. -/
theorem idx_fields (m i : ℕ) :
    i = idx m (tagOf m i) (fOf m i) (iOf m i) (jOf m i) (kindOf i) := (idx_decomp m i).symm

theorem gate_valid {m i : ℕ} (hm : 1 ≤ m) (hi : i < 2 ^ (3 * m + 5)) : (gate m i).ValidAt i := by
  have hk := kindOf_lt i
  have hJ := jOf_lt m i
  have hI := iOf_lt m i
  have hF := fOf_lt m i
  have ht := tagOf_lt hi
  have hdec := idx_fields m i
  set t := tagOf m i
  set k := kindOf i
  set J := jOf m i
  set I := iOf m i
  set F := fOf m i
  have h2m : 0 < 2 ^ m := Nat.two_pow_pos m
  have hpos : ∀ X : ℕ, X.testBit 0 = true → 1 ≤ X := by
    intro X hX; rcases Nat.eq_zero_or_pos X with rfl | h
    · simp at hX
    · exact h
  have hfin : ∀ k' < k, t = 2 → fin m k' < i := by
    intro k' hk' ht2
    rw [hdec, ht2]
    exact lt_of_lt_of_le (idx_lt_of_kind hk') (idx_mono (Nat.zero_le _) (Nat.zero_le _)
      (Nat.zero_le _) le_rfl)
  unfold gate
  by_cases h0 : t = 0
  · rw [if_pos h0]
    by_cases hk0 : k = 0
    · rw [if_pos hk0]
      by_cases hJ0 : J.testBit 0 = true
      · rw [if_pos hJ0]
        have h1 := hpos J hJ0
        have hlt1 : idx m 0 F I (J / 2) 0 < i := by
          rw [hdec, h0, hk0]; exact idx_lt_of_J (by omega) (by norm_num)
        have hlt2 : idx m 0 F I (J / 2) 1 < i := by
          rw [hdec, h0, hk0]; exact idx_lt_of_J (by omega) (by norm_num)
        refine ⟨by simp, hlt1, ?_⟩
        split_ifs <;> omega
      · rw [if_neg hJ0]; trivial
    rw [if_neg hk0]
    by_cases hk1 : k = 1
    · rw [if_pos hk1]; trivial
    rw [if_neg hk1]
    by_cases hk2 : k = 2
    · rw [if_pos hk2]
      by_cases hI0 : I.testBit 0 = true
      · rw [if_pos hI0]
        have h1 := hpos I hI0
        have hlt : ∀ k' < 8, idx m 0 F (I / 2) J k' < i := by
          intro k' hk'; rw [hdec, h0]; exact idx_lt_of_I (by omega) hJ hk'
        exact ⟨by simp, hlt 2 (by norm_num), hlt 0 (by norm_num)⟩
      · rw [if_neg hI0]; trivial
    · rw [if_neg hk2]; trivial
  rw [if_neg h0]
  by_cases h1 : t = 1
  · rw [if_pos h1]
    by_cases hI0 : I.testBit 0 = true
    · rw [if_pos hI0]
      have hI1 := hpos I hI0
      have hlt : ∀ J' < 2 ^ m, idx m 1 0 (I / 2) J' 0 < i := by
        intro J' hJ'
        rw [hdec, h1]
        rcases Nat.eq_zero_or_pos F with hF0 | hF0
        · rw [hF0]; exact idx_lt_of_I (by omega) hJ' (by norm_num)
        · exact idx_lt_of_F hF0 (by omega) hJ' (by norm_num)
      exact ⟨by simp, hlt _ (two_mul_mod_add_one_lt' hm _), hlt _ (Nat.mod_lt _ h2m)⟩
    · rw [if_neg hI0]
      have hlt : idx m 0 J (2 ^ m - 1) (2 ^ m - 1) 2 < i := by
        rw [hdec, h1]; exact idx_lt_of_tag (by norm_num) hJ (by omega) (by omega) (by norm_num)
      exact ⟨by simp, hlt, by omega⟩
  rw [if_neg h1]
  by_cases h2 : t = 2
  · rw [if_pos h2]
    have hroot : root m < i := by
      rw [hdec, h2]; exact idx_lt_of_tag (by norm_num) (by omega) (by omega) h2m (by norm_num)
    have hY : yIdx m < i := by
      rw [hdec, h2]; exact idx_lt_of_tag (by norm_num) h2m (by omega) h2m (by norm_num)
    by_cases hk0 : k = 0
    · rw [if_pos hk0]; exact ⟨by simp, hroot, hY⟩
    rw [if_neg hk0]
    by_cases hk1 : k = 1
    · rw [if_pos hk1]; exact ⟨by simp, hY, hroot⟩
    rw [if_neg hk1]
    by_cases hk2 : k = 2
    · rw [if_pos hk2]; exact hfin 0 (by omega) h2
    rw [if_neg hk2]
    by_cases hk3 : k = 3
    · rw [if_pos hk3]; exact hfin 1 (by omega) h2
    rw [if_neg hk3]
    by_cases hk4 : k = 4
    · rw [if_pos hk4]; exact ⟨by simp, hfin 2 (by omega) h2, hfin 3 (by omega) h2⟩
    rw [if_neg hk4]; trivial
  · rw [if_neg h2]; trivial

/-! ## Depth of the Ryser circuits -/

/-- The number of binary digits. -/
def blen (J : ℕ) : ℕ := if J = 0 then 0 else blen (J / 2) + 1
decreasing_by omega

theorem blen_succ {J : ℕ} (h : 1 ≤ J) : blen J = blen (J / 2) + 1 := by
  rw [blen, if_neg (by omega)]

theorem blen_le {J m : ℕ} (h : J < 2 ^ m) : blen J ≤ m := by
  induction m generalizing J with
  | zero =>
    have : J = 0 := by simpa using h
    subst this; simp [blen]
  | succ m ih =>
    rcases Nat.eq_zero_or_pos J with rfl | hJ
    · simp [blen]
    · rw [blen_succ hJ]
      have := ih (J := J / 2) (by rw [pow_succ] at h; omega)
      omega

theorem pos_of_testBit_zero {X : ℕ} (hX : X.testBit 0 = true) : 1 ≤ X := by
  rcases Nat.eq_zero_or_pos X with rfl | h
  · simp at hX
  · exact h

section depth

variable {m : ℕ}

/-- The gate at an index with given fields. -/
theorem gate_idx {t F I J k : ℕ} (hk : k < 8) (hJ : J < 2 ^ m) (hI : I < 2 ^ m) (hF : F < 2 ^ m) :
    gate m (idx m t F I J k) =
      if t = 0 then
        if k = 0 then
          if J.testBit 0 then
            .arith .add (idx m 0 F I (J / 2) 0)
              (if look m F J then idx m 0 F I (J / 2) 1 else 0)
          else .const 0
        else if k = 1 then .input (pc m I * m + pc m J)
        else if k = 2 then
          if I.testBit 0 then
            .arith .mul (idx m 0 F (I / 2) J 2) (idx m 0 F (I / 2) J 0)
          else .const (sgn m F)
        else .const 0
      else if t = 1 then
        if I.testBit 0 then
          .arith .add (idx m 1 0 (I / 2) (2 * J % 2 ^ m + 1) 0) (idx m 1 0 (I / 2) (2 * J % 2 ^ m) 0)
        else .arith .add (idx m 0 J (2 ^ m - 1) (2 ^ m - 1) 2) 0
      else if t = 2 then
        if k = 0 then .arith .sub (root m) (yIdx m)
        else if k = 1 then .arith .sub (yIdx m) (root m)
        else if k = 2 then .sign (fin m 0)
        else if k = 3 then .sign (fin m 1)
        else if k = 4 then .arith .mul (fin m 2) (fin m 3)
        else .const 0
      else .const 0 := by
  rw [gate, tagOf_idx hk hJ hI hF, kindOf_idx hk, jOf_idx hk hJ, iOf_idx hk hJ hI,
    fOf_idx hk hJ hI hF]

theorem gate_zero : gate m 0 = .const 0 := by
  have h := gate_idx (m := m) (t := 0) (F := 0) (I := 0) (J := 0) (k := 0) (by norm_num)
    (Nat.two_pow_pos m) (Nat.two_pow_pos m) (Nat.two_pow_pos m)
  simpa [idx] using h

/-- The depth of the gates of the Ryser circuit. -/
abbrev dp (m i : ℕ) : ℕ := GateDepth.dep (gate m) i

theorem dp_zero : dp m 0 = 0 := GateDepth.dep_const gate_zero

theorem dp_In {F I J : ℕ} (hJ : J < 2 ^ m) (hI : I < 2 ^ m) (hF : F < 2 ^ m) :
    dp m (idx m 0 F I J 1) = 0 :=
  GateDepth.dep_input (t := pc m I * m + pc m J) (by rw [gate_idx (by norm_num) hJ hI hF]; simp)

theorem dp_A {F I : ℕ} (hI : I < 2 ^ m) (hF : F < 2 ^ m) :
    ∀ J < 2 ^ m, dp m (idx m 0 F I J 0) ≤ blen J := by
  intro J
  induction J using Nat.strong_induction_on with
  | _ J ih =>
    intro hJ
    by_cases hJ0 : J.testBit 0 = true
    · have h1 := pos_of_testBit_zero hJ0
      have hJ2 : J / 2 < 2 ^ m := by omega
      have hg := gate_idx (m := m) (t := 0) (k := 0) (by norm_num) hJ hI hF
      simp only [if_true, hJ0] at hg
      rw [dp, GateDepth.dep_arith hg (idx_lt_of_J (by omega) (by norm_num)) ?_, blen_succ h1]
      · have h1' := ih (J / 2) (by omega) hJ2
        have h2' : dp m (if look m F J then idx m 0 F I (J / 2) 1 else 0) = 0 := by
          split_ifs
          · exact dp_In hJ2 hI hF
          · exact dp_zero
        simp only [dp] at h1' h2'
        omega
      · split_ifs
        · exact idx_lt_of_J (by omega) (by norm_num)
        · exact lt_of_le_of_lt (Nat.zero_le _)
            (idx_lt_of_J (J := 0) (k := 0) (by omega) (by norm_num))
    · have hg := gate_idx (m := m) (t := 0) (k := 0) (by norm_num) hJ hI hF
      simp only [if_true, hJ0, Bool.false_eq_true, if_false] at hg
      rw [dp, GateDepth.dep_const hg]
      exact Nat.zero_le _

theorem dp_P {F J : ℕ} (hJ : J < 2 ^ m) (hF : F < 2 ^ m) :
    ∀ I < 2 ^ m, dp m (idx m 0 F I J 2) ≤ m + blen I := by
  intro I
  induction I using Nat.strong_induction_on with
  | _ I ih =>
    intro hI
    by_cases hI0 : I.testBit 0 = true
    · have h1 := pos_of_testBit_zero hI0
      have hI2 : I / 2 < 2 ^ m := by omega
      have hg := gate_idx (m := m) (t := 0) (k := 2) (by norm_num) hJ hI hF
      simp only [if_true, hI0, show (2 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 1 by norm_num,
        if_false] at hg
      rw [dp, GateDepth.dep_arith hg (idx_lt_of_I (by omega) hJ (by norm_num))
        (idx_lt_of_I (by omega) hJ (by norm_num)), blen_succ h1]
      have h1' := ih (I / 2) (by omega) hI2
      have h2' := dp_A hI2 hF J hJ
      have h3' := blen_le hJ
      simp only [dp] at h1' h2'
      omega
    · have hg := gate_idx (m := m) (t := 0) (k := 2) (by norm_num) hJ hI hF
      simp only [if_true, hI0, Bool.false_eq_true, show (2 : ℕ) ≠ 0 by norm_num,
        show (2 : ℕ) ≠ 1 by norm_num, if_false] at hg
      rw [dp, GateDepth.dep_const hg]
      exact Nat.zero_le _

theorem dp_T (hm : 1 ≤ m) {F k : ℕ} (hk : k < 8) (hF : F < 2 ^ m) :
    ∀ L < 2 ^ m, ∀ p < 2 ^ m, dp m (idx m 1 F L p k) ≤ 2 * m + 1 + blen L := by
  intro L
  induction L using Nat.strong_induction_on generalizing F k with
  | _ L ih =>
    intro hL p hp
    have h2m := Nat.two_pow_pos m
    by_cases hL0 : L.testBit 0 = true
    · have h1 := pos_of_testBit_zero hL0
      have hL2 : L / 2 < 2 ^ m := by omega
      have hg := gate_idx (m := m) (t := 1) (F := F) (k := k) hk hp hL hF
      simp only [hL0, if_true, show (1 : ℕ) ≠ 0 by norm_num, if_false] at hg
      have hlt : ∀ J' < 2 ^ m, idx m 1 0 (L / 2) J' 0 < idx m 1 F L p k := by
        intro J' hJ'
        rcases Nat.eq_zero_or_pos F with hF0 | hF0
        · rw [hF0]; exact idx_lt_of_I (by omega) hJ' (by norm_num)
        · exact idx_lt_of_F hF0 (by omega) hJ' (by norm_num)
      have hJa := two_mul_mod_add_one_lt' hm p
      have hJb := Nat.mod_lt (2 * p) h2m
      rw [dp, GateDepth.dep_arith hg (hlt _ hJa) (hlt _ hJb), blen_succ h1]
      have ha := ih (L / 2) (by omega) (F := 0) (k := 0) (by norm_num) h2m hL2 _ hJa
      have hb := ih (L / 2) (by omega) (F := 0) (k := 0) (by norm_num) h2m hL2 _ hJb
      simp only [dp] at ha hb
      omega
    · have hg := gate_idx (m := m) (t := 1) (F := F) (k := k) hk hp hL hF
      simp only [hL0, Bool.false_eq_true, if_false, show (1 : ℕ) ≠ 0 by norm_num,
        if_true] at hg
      have hlt : idx m 0 p (2 ^ m - 1) (2 ^ m - 1) 2 < idx m 1 F L p k :=
        idx_lt_of_tag (by norm_num) hp (by omega) (by omega) (by norm_num)
      rw [dp, GateDepth.dep_arith hg hlt (lt_of_le_of_lt (Nat.zero_le _) hlt)]
      have ha := dp_P (m := m) (J := 2 ^ m - 1) (F := p) (by omega) hp (2 ^ m - 1) (by omega)
      have hb := blen_le (show 2 ^ m - 1 < 2 ^ m by omega)
      have hc : dp m 0 = 0 := dp_zero
      simp only [dp] at ha hc
      omega

theorem dp_root (hm : 1 ≤ m) : dp m (root m) ≤ 3 * m + 1 := by
  have h2m := Nat.two_pow_pos m
  have h := dp_T hm (F := 0) (k := 0) (by norm_num) h2m (2 ^ m - 1) (by omega) 0 h2m
  have := blen_le (show 2 ^ m - 1 < 2 ^ m by omega)
  unfold root; omega

theorem gate_fin {k : ℕ} (hk : k < 8) : gate m (fin m k) =
    if k = 0 then .arith .sub (root m) (yIdx m)
    else if k = 1 then .arith .sub (yIdx m) (root m)
    else if k = 2 then .sign (fin m 0)
    else if k = 3 then .sign (fin m 1)
    else if k = 4 then .arith .mul (fin m 2) (fin m 3)
    else .const 0 := by
  have h2m := Nat.two_pow_pos m
  have hg := gate_idx (m := m) (t := 2) (F := 0) (I := 0) (J := 0) (k := k) hk h2m h2m h2m
  simp only [show (2 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 1 by norm_num, if_true,
    if_false] at hg
  exact hg

theorem root_lt_fin (hm : 1 ≤ m) (k : ℕ) : root m < fin m k :=
  idx_lt_of_tag (by norm_num) (Nat.two_pow_pos m) (by have := Nat.two_pow_pos m; omega)
    (Nat.two_pow_pos m) (by norm_num)

theorem yIdx_lt_fin (k : ℕ) : yIdx m < fin m k :=
  idx_lt_of_tag (by norm_num) (Nat.two_pow_pos m) (by have := Nat.two_pow_pos m; omega)
    (Nat.two_pow_pos m) (by norm_num)

theorem dp_yIdx : dp m (yIdx m) = 0 :=
  dp_In (Nat.two_pow_pos m) (by have := Nat.two_pow_pos m; omega) (Nat.two_pow_pos m)

theorem dp_fin01 (hm : 1 ≤ m) {k : ℕ} (hk : k < 2) : dp m (fin m k) ≤ 3 * m + 2 := by
  have hr := dp_root hm
  have hY := dp_yIdx (m := m)
  have hg := gate_fin (m := m) (k := k) (by omega)
  simp only [dp] at hr hY
  interval_cases k
  · simp only [if_true] at hg
    rw [dp, GateDepth.dep_arith hg (root_lt_fin hm 0) (yIdx_lt_fin 0)]; omega
  · simp only [show (1 : ℕ) ≠ 0 by norm_num, if_true, if_false] at hg
    rw [dp, GateDepth.dep_arith hg (yIdx_lt_fin 1) (root_lt_fin hm 1)]; omega

theorem dp_fin23 (hm : 1 ≤ m) {k : ℕ} (hk : 2 ≤ k) (hk' : k < 4) :
    dp m (fin m k) ≤ 3 * m + 3 := by
  have h0 := dp_fin01 hm (k := 0) (by norm_num)
  have h1 := dp_fin01 hm (k := 1) (by norm_num)
  have hg := gate_fin (m := m) (k := k) (by omega)
  simp only [dp] at h0 h1
  interval_cases k
  · simp only [show (2 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 1 by norm_num, if_true,
      if_false] at hg
    rw [dp, GateDepth.dep_sign hg (idx_lt_of_kind (by norm_num))]; omega
  · simp only [show (3 : ℕ) ≠ 0 by norm_num, show (3 : ℕ) ≠ 1 by norm_num,
      show (3 : ℕ) ≠ 2 by norm_num, if_true, if_false] at hg
    rw [dp, GateDepth.dep_sign hg (idx_lt_of_kind (by norm_num))]; omega

theorem dp_fin4 (hm : 1 ≤ m) : dp m (fin m 4) ≤ 3 * m + 4 := by
  have h2 := dp_fin23 hm (k := 2) (by norm_num) (by norm_num)
  have h3 := dp_fin23 hm (k := 3) (by norm_num) (by norm_num)
  have hg := gate_fin (m := m) (k := 4) (by norm_num)
  simp only [show (4 : ℕ) ≠ 0 by norm_num, show (4 : ℕ) ≠ 1 by norm_num,
    show (4 : ℕ) ≠ 2 by norm_num, show (4 : ℕ) ≠ 3 by norm_num, if_true, if_false] at hg
  simp only [dp] at h2 h3
  rw [dp, GateDepth.dep_arith hg (idx_lt_of_kind (by norm_num)) (idx_lt_of_kind (by norm_num))]
  omega

/-- **Depth.**  Every gate of the Ryser circuit has depth `≤ 3m + 4`. -/
theorem dp_le (hm : 1 ≤ m) {i : ℕ} (hi : i < 2 ^ (3 * m + 5)) : dp m i ≤ 3 * m + 4 := by
  have hk := kindOf_lt i
  have hJ := jOf_lt m i
  have hI := iOf_lt m i
  have hF := fOf_lt m i
  have ht := tagOf_lt hi
  have hbI := blen_le hI
  have hbJ := blen_le hJ
  have hdec := idx_decomp m i
  set t := tagOf m i
  set k := kindOf i
  set J := jOf m i
  set I := iOf m i
  set F := fOf m i
  rw [← hdec]
  have hg := gate_idx (m := m) (t := t) hk hJ hI hF
  interval_cases t
  · -- blocks
    by_cases hk0 : k = 0
    · rw [hk0]; have := dp_A hI hF J hJ; omega
    by_cases hk1 : k = 1
    · rw [hk1, dp_In hJ hI hF]; omega
    by_cases hk2 : k = 2
    · rw [hk2]; have := dp_P hJ hF I hI; omega
    · simp only [if_true, hk0, hk1, hk2, if_false] at hg
      rw [dp, GateDepth.dep_const hg]; omega
  · have := dp_T hm hk hF I hI J hJ; omega
  · -- the comparison
    have h01 := dp_fin01 hm (k := 0) (by norm_num)
    have h01' := dp_fin01 hm (k := 1) (by norm_num)
    have h23 := dp_fin23 hm (k := 2) (by norm_num) (by norm_num)
    have h23' := dp_fin23 hm (k := 3) (by norm_num) (by norm_num)
    have h4 := dp_fin4 hm
    simp only [dp] at h01 h01' h23 h23' h4
    have hroot := dp_root hm
    have hY := dp_yIdx (m := m)
    simp only [dp] at hroot hY
    simp only [show (2 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 1 by norm_num, if_true,
      if_false] at hg
    have hlt : ∀ k' < k, fin m k' < idx m 2 F I J k := fun k' hk' =>
      lt_of_lt_of_le (idx_lt_of_kind hk') (idx_mono (Nat.zero_le _) (Nat.zero_le _)
        (Nat.zero_le _) le_rfl)
    have hroot' : root m < idx m 2 F I J k :=
      idx_lt_of_tag (by norm_num) (by omega) (by omega) (Nat.two_pow_pos m) (by norm_num)
    have hY' : yIdx m < idx m 2 F I J k :=
      idx_lt_of_tag (by norm_num) (Nat.two_pow_pos m) (by omega) (Nat.two_pow_pos m) (by norm_num)
    interval_cases k
    · simp only [if_true] at hg
      rw [dp, GateDepth.dep_arith hg hroot' hY']; omega
    · simp only [show (1 : ℕ) ≠ 0 by norm_num, if_true, if_false] at hg
      rw [dp, GateDepth.dep_arith hg hY' hroot']; omega
    · simp only [show (2 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 1 by norm_num, if_true,
        if_false] at hg
      rw [dp, GateDepth.dep_sign hg (hlt 0 (by norm_num))]; omega
    · simp only [show (3 : ℕ) ≠ 0 by norm_num, show (3 : ℕ) ≠ 1 by norm_num,
        show (3 : ℕ) ≠ 2 by norm_num, if_true, if_false] at hg
      rw [dp, GateDepth.dep_sign hg (hlt 1 (by norm_num))]; omega
    · simp only [show (4 : ℕ) ≠ 0 by norm_num, show (4 : ℕ) ≠ 1 by norm_num,
        show (4 : ℕ) ≠ 2 by norm_num, show (4 : ℕ) ≠ 3 by norm_num, if_true, if_false] at hg
      rw [dp, GateDepth.dep_arith hg (hlt 2 (by norm_num)) (hlt 3 (by norm_num))]; omega
    all_goals
      simp at hg
      rw [dp, GateDepth.dep_const hg]; omega
  · simp at hg
    rw [dp, GateDepth.dep_const hg]; omega

end depth

/-! ## Values of the Ryser circuits -/

theorem two_pow_succ_sub_one_div (j : ℕ) : (2 ^ (j + 1) - 1) / 2 = 2 ^ j - 1 := by
  have := Nat.one_le_two_pow (n := j)
  rw [pow_succ]; omega

theorem two_pow_sub_one_lt {j m : ℕ} (h : j ≤ m) : 2 ^ j - 1 < 2 ^ m := by
  have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h
  have := Nat.one_le_two_pow (n := j)
  omega

theorem pc_two_pow_sub_one (q j : ℕ) : pc q (2 ^ j - 1) = min q j := by
  induction q with
  | zero => simp [pc]
  | succ q ih =>
    simp only [pc, ih, Nat.testBit_two_pow_sub_one]
    by_cases h : q < j
    · simp [h]; omega
    · simp [h]; omega

theorem pc_zero (q : ℕ) : pc q 0 = 0 := by
  induction q with
  | zero => rfl
  | succ q ih => simp [pc, ih]

theorem look_two_pow_sub_one {q j : ℕ} (F : ℕ) (h : j < q) :
    look q F (2 ^ (j + 1) - 1) = F.testBit j := by
  induction q with
  | zero => omega
  | succ q ih =>
    simp only [look, Nat.testBit_two_pow_sub_one]
    rcases Nat.lt_or_ge j q with h' | h'
    · rw [if_neg (by simp; omega)]; exact ih h'
    · have : j = q := by omega
      subst this; simp

section values

variable {K : Type*} [CommRing K] {e : ℝ → K} {τ : K → K} {x : ℕ → K} {m : ℕ}

theorem V_zero (he : e 0 = 0) : GateEval.val e τ x (gate m) 0 = 0 := by
  rw [GateEval.val_const gate_zero, he]

theorem V_In {F I J : ℕ} (hJ : J < 2 ^ m) (hI : I < 2 ^ m) (hF : F < 2 ^ m) :
    GateEval.val e τ x (gate m) (idx m 0 F I J 1) = x (pc m I * m + pc m J) :=
  GateEval.val_input (by rw [gate_idx (by norm_num) hJ hI hF]; simp)

/-- The row sums. -/
theorem V_A (he : e 0 = 0) {F I : ℕ} (hI : I < 2 ^ m) (hF : F < 2 ^ m) :
    ∀ j ≤ m, GateEval.val e τ x (gate m) (idx m 0 F I (2 ^ j - 1) 0) =
      ∑ q ∈ Finset.range j, if F.testBit q then x (pc m I * m + q) else 0 := by
  intro j
  induction j with
  | zero =>
    intro _
    have hg := gate_idx (m := m) (t := 0) (F := F) (I := I) (J := 0) (k := 0) (by norm_num)
      (Nat.two_pow_pos m) hI hF
    simp only [if_true, Nat.zero_testBit, Bool.false_eq_true, if_false] at hg
    simp [GateEval.val_const hg, he]
  | succ j ih =>
    intro hj
    have hJ := two_pow_sub_one_lt hj
    have hJ' := two_pow_sub_one_lt (show j ≤ m by omega)
    have hg := gate_idx (m := m) (t := 0) (F := F) (I := I) (J := 2 ^ (j + 1) - 1) (k := 0)
      (by norm_num) hJ hI hF
    simp only [if_true, Nat.testBit_two_pow_sub_one, show 0 < j + 1 by omega, decide_true,
      two_pow_succ_sub_one_div, look_two_pow_sub_one F (show j < m by omega)] at hg
    have hlt1 : idx m 0 F I (2 ^ j - 1) 0 < idx m 0 F I (2 ^ (j + 1) - 1) 0 :=
      idx_lt_of_J (by rw [pow_succ]; have := Nat.one_le_two_pow (n := j); omega) (by norm_num)
    have hlt2 : idx m 0 F I (2 ^ j - 1) 1 < idx m 0 F I (2 ^ (j + 1) - 1) 0 :=
      idx_lt_of_J (by rw [pow_succ]; have := Nat.one_le_two_pow (n := j); omega) (by norm_num)
    rw [Finset.sum_range_succ, ← ih (by omega)]
    by_cases hFj : F.testBit j = true
    · simp only [hFj, if_true] at hg ⊢
      rw [GateEval.val_add hg hlt1 hlt2, V_In hJ' hI hF, pc_two_pow_sub_one,
        min_eq_right (by omega)]
    · simp only [hFj, Bool.false_eq_true, if_false] at hg ⊢
      rw [GateEval.val_add hg hlt1 (lt_of_le_of_lt (Nat.zero_le _) hlt1)]
      rw [show GateEval.val e τ x (gate m) 0 = 0 from V_zero he, add_zero]

/-- The row sum of row `s` for the subset `F`. -/
def rowSum (x : ℕ → K) (m F s : ℕ) : K :=
  ∑ q ∈ Finset.range m, if F.testBit q then x (s * m + q) else 0

/-- The products. -/
theorem V_P (he : e 0 = 0) {F : ℕ} (hF : F < 2 ^ m) :
    ∀ r ≤ m, GateEval.val e τ x (gate m) (idx m 0 F (2 ^ r - 1) (2 ^ m - 1) 2) =
      e (sgn m F) * ∏ s ∈ Finset.range r, rowSum x m F s := by
  have hJ := two_pow_sub_one_lt (le_refl m)
  intro r
  induction r with
  | zero =>
    intro _
    have hg := gate_idx (m := m) (t := 0) (F := F) (I := 0) (J := 2 ^ m - 1) (k := 2)
      (by norm_num) hJ (Nat.two_pow_pos m) hF
    simp only [if_true, show (2 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 1 by norm_num, if_false,
      Nat.zero_testBit, Bool.false_eq_true] at hg
    simp [GateEval.val_const hg]
  | succ r ih =>
    intro hr
    have hI := two_pow_sub_one_lt hr
    have hI' := two_pow_sub_one_lt (show r ≤ m by omega)
    have hg := gate_idx (m := m) (t := 0) (F := F) (I := 2 ^ (r + 1) - 1) (J := 2 ^ m - 1)
      (k := 2) (by norm_num) hJ hI hF
    simp only [if_true, show (2 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 1 by norm_num, if_false,
      Nat.testBit_two_pow_sub_one, show 0 < r + 1 by omega, decide_true,
      two_pow_succ_sub_one_div] at hg
    have hlt : ∀ k' < 8, idx m 0 F (2 ^ r - 1) (2 ^ m - 1) k' <
        idx m 0 F (2 ^ (r + 1) - 1) (2 ^ m - 1) 2 := fun k' hk' =>
      idx_lt_of_I (by rw [pow_succ]; have := Nat.one_le_two_pow (n := r); omega) hJ hk'
    rw [GateEval.val_mul hg (hlt 2 (by norm_num)) (hlt 0 (by norm_num))]
    rw [show GateEval.val e τ x (gate m) (idx m 0 F (2 ^ r - 1) (2 ^ m - 1) 2) = _ from
      ih (by omega), Finset.prod_range_succ]
    rw [show GateEval.val e τ x (gate m) (idx m 0 F (2 ^ r - 1) (2 ^ m - 1) 0) = _ from
      V_A he hI' hF m le_rfl, pc_two_pow_sub_one, min_eq_right (by omega)]
    rw [mul_assoc]
    rfl

/-- The term of Ryser's formula for the subset `F`. -/
def term (e : ℝ → K) (x : ℕ → K) (m F : ℕ) : K :=
  e (sgn m F) * ∏ s ∈ Finset.range m, rowSum x m F s

theorem V_term (he : e 0 = 0) {F : ℕ} (hF : F < 2 ^ m) :
    GateEval.val e τ x (gate m) (idx m 0 F (2 ^ m - 1) (2 ^ m - 1) 2) = term e x m F :=
  V_P he hF m le_rfl

/-- The addition tree. -/
theorem V_T (hm : 1 ≤ m) (he : e 0 = 0) :
    ∀ l ≤ m, ∀ p < 2 ^ (m - l), GateEval.val e τ x (gate m) (idx m 1 0 (2 ^ l - 1) p 0) =
      ∑ t ∈ Finset.range (2 ^ l), term e x m (p * 2 ^ l + t) := by
  have h2m := Nat.two_pow_pos m
  intro l
  induction l with
  | zero =>
    intro _ p hp
    have hp' : p < 2 ^ m := by simpa using hp
    have hg := gate_idx (m := m) (t := 1) (F := 0) (I := 0) (J := p) (k := 0) (by norm_num) hp'
      h2m h2m
    simp only [show (1 : ℕ) ≠ 0 by norm_num, if_false, if_true, Nat.zero_testBit,
      Bool.false_eq_true] at hg
    have hlt : idx m 0 p (2 ^ m - 1) (2 ^ m - 1) 2 < idx m 1 0 0 p 0 :=
      idx_lt_of_tag (by norm_num) hp' (by omega) (by omega) (by norm_num)
    simp only [pow_zero, Nat.sub_self, Finset.range_one, Finset.sum_singleton, mul_one,
      add_zero]
    rw [GateEval.val_add hg hlt (lt_of_le_of_lt (Nat.zero_le _) hlt),
      show GateEval.val e τ x (gate m) 0 = 0 from V_zero he, add_zero]
    exact V_term he hp'
  | succ l ih =>
    intro hl p hp
    have hL := two_pow_sub_one_lt hl
    have hL' := two_pow_sub_one_lt (show l ≤ m by omega)
    have hpow : 2 ^ (m - l) = 2 * 2 ^ (m - (l + 1)) := by
      rw [← pow_succ']; congr 1; omega
    have hpm : 2 ^ (m - l) ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hp' : p < 2 ^ m := by
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show m - (l + 1) ≤ m by omega)
      omega
    have hg := gate_idx (m := m) (t := 1) (F := 0) (I := 2 ^ (l + 1) - 1) (J := p) (k := 0)
      (by norm_num) hp' hL h2m
    simp only [show (1 : ℕ) ≠ 0 by norm_num, if_false, if_true, Nat.testBit_two_pow_sub_one,
      show 0 < l + 1 by omega, decide_true, two_pow_succ_sub_one_div] at hg
    have h2p : 2 * p + 1 < 2 ^ m := by omega
    rw [Nat.mod_eq_of_lt (by omega : 2 * p < 2 ^ m)] at hg
    have hlt : ∀ J' < 2 ^ m, idx m 1 0 (2 ^ l - 1) J' 0 < idx m 1 0 (2 ^ (l + 1) - 1) p 0 :=
      fun J' hJ' => idx_lt_of_I (by rw [pow_succ]; have := Nat.one_le_two_pow (n := l); omega)
        hJ' (by norm_num)
    rw [GateEval.val_add hg (hlt _ h2p) (hlt _ (by omega))]
    rw [show GateEval.val e τ x (gate m) (idx m 1 0 (2 ^ l - 1) (2 * p + 1) 0) = _ from
      ih (by omega) (2 * p + 1) (by omega),
      show GateEval.val e τ x (gate m) (idx m 1 0 (2 ^ l - 1) (2 * p) 0) = _ from
      ih (by omega) (2 * p) (by omega)]
    rw [pow_succ, mul_two, Finset.sum_range_add, add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun t _ => ?_
      congr 1; ring
    · refine Finset.sum_congr rfl fun t _ => ?_
      congr 1; ring

theorem V_root (hm : 1 ≤ m) (he : e 0 = 0) :
    GateEval.val e τ x (gate m) (root m) = ∑ t ∈ Finset.range (2 ^ m), term e x m t := by
  have := V_T (τ := τ) (x := x) hm he m le_rfl 0 (by simp)
  simpa [root] using this

theorem V_yIdx : GateEval.val e τ x (gate m) (yIdx m) = x (m * m) := by
  rw [yIdx, V_In (Nat.two_pow_pos m) (two_pow_sub_one_lt le_rfl) (Nat.two_pow_pos m),
    pc_two_pow_sub_one, pc_zero, min_self, Nat.add_zero]

theorem V_fin0 (hm : 1 ≤ m) : GateEval.val e τ x (gate m) (fin m 0) = GateEval.val e τ x (gate m) (root m) - GateEval.val e τ x (gate m) (yIdx m) :=
  GateEval.val_sub (by rw [gate_fin (by norm_num)]; simp) (root_lt_fin hm 0) (yIdx_lt_fin 0)

theorem V_fin1 (hm : 1 ≤ m) : GateEval.val e τ x (gate m) (fin m 1) = GateEval.val e τ x (gate m) (yIdx m) - GateEval.val e τ x (gate m) (root m) :=
  GateEval.val_sub (by rw [gate_fin (by norm_num)]; simp) (yIdx_lt_fin 1) (root_lt_fin hm 1)

theorem V_fin2 : GateEval.val e τ x (gate m) (fin m 2) = τ (GateEval.val e τ x (gate m) (fin m 0)) :=
  GateEval.val_sign (by rw [gate_fin (by norm_num)]; simp) (idx_lt_of_kind (by norm_num))

theorem V_fin3 : GateEval.val e τ x (gate m) (fin m 3) = τ (GateEval.val e τ x (gate m) (fin m 1)) :=
  GateEval.val_sign (by rw [gate_fin (by norm_num)]; simp) (idx_lt_of_kind (by norm_num))

theorem V_fin4 : GateEval.val e τ x (gate m) (fin m 4) = GateEval.val e τ x (gate m) (fin m 2) * GateEval.val e τ x (gate m) (fin m 3) :=
  GateEval.val_mul (by rw [gate_fin (by norm_num)]; simp) (idx_lt_of_kind (by norm_num))
    (idx_lt_of_kind (by norm_num))

end values

/-! ## Ryser's formula -/

theorem sgn_eq_prod (m F : ℕ) :
    sgn m F = ∏ q ∈ Finset.range m, if F.testBit q then (1 : ℝ) else -1 := by
  induction m with
  | zero => simp [sgn]
  | succ m ih =>
    rw [sgn, Finset.prod_range_succ, ← ih]
    split_ifs <;> ring

/-- **Ryser's formula** as a sum over the numbers `t < 2^m` (the subsets are the sets of ones of
the binary digits). -/
theorem ryser_sum {K : Type*} [CommRing K] (m : ℕ) (X : Fin m × Fin m → K) :
    ∑ t ∈ Finset.range (2 ^ m), (∏ q : Fin m, if t.testBit q then (1 : K) else -1) *
      ∏ s : Fin m, ∑ q : Fin m, (if t.testBit q then X (s, q) else 0) =
    ∑ S : Finset (Fin m), (-1 : K) ^ (m - S.card) * ∏ i : Fin m, ∑ j ∈ S, X (i, j) := by
  set φ : ℕ → Finset (Fin m) := fun t => Finset.univ.filter fun q : Fin m => t.testBit q
  have hinj : Set.InjOn φ (Finset.range (2 ^ m)) := by
    intro t ht t' ht' h
    simp only [Finset.coe_range, Set.mem_Iio] at ht ht'
    apply Nat.eq_of_testBit_eq
    intro q
    by_cases hq : q < m
    · have := congrArg (fun S => (⟨q, hq⟩ : Fin m) ∈ S) h
      simpa [φ] using this
    · have h1 : 2 ^ m ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]
  have himg : (Finset.range (2 ^ m)).image φ = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn hinj, Finset.card_range, Fintype.card_finset,
      Fintype.card_fin]
  have hterm : ∀ t, (∏ q : Fin m, if t.testBit q then (1 : K) else -1) *
      ∏ s : Fin m, ∑ q : Fin m, (if t.testBit q then X (s, q) else 0) =
      (-1 : K) ^ (m - (φ t).card) * ∏ i : Fin m, ∑ j ∈ φ t, X (i, j) := by
    intro t
    congr 1
    · rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
      congr 1
      have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
        (fun q : Fin m => t.testBit q = true)
      simp only [Finset.card_univ, Fintype.card_fin] at this
      simp only [φ]
      omega
    · refine Finset.prod_congr rfl fun s _ => ?_
      rw [Finset.sum_filter]
  simp_rw [hterm]
  rw [← Finset.sum_image (f := fun S => (-1 : K) ^ (m - S.card) * ∏ i : Fin m, ∑ j ∈ S, X (i, j))
    hinj, himg]

/-- The permanent over an `ℝ`-algebra, expanded by Ryser's formula. -/
theorem eval_map_per {K : Type*} [CommRing K] [Algebra ℝ K] (m : ℕ) (X : Fin m × Fin m → K) :
    eval X (map (algebraMap ℝ K) (per m)) =
      ∑ S : Finset (Fin m), (-1 : K) ^ (m - S.card) * ∏ i : Fin m, ∑ j ∈ S, X (i, j) := by
  rw [ryser]
  simp [map_sum, map_mul, map_pow, map_neg, map_one, map_prod, map_X, eval_X]

/-- **The root computes the permanent.** -/
theorem V_root_eq {K : Type*} [CommRing K] [Algebra ℝ K] {e : ℝ → K}
    (he : ∀ c, e c = algebraMap ℝ K c) {τ : K → K} {x : ℕ → K} {m : ℕ} (hm : 1 ≤ m) :
    GateEval.val e τ x (gate m) (root m) =
      eval (fun p : Fin m × Fin m => x (p.1 * m + p.2)) (map (algebraMap ℝ K) (per m)) := by
  have he0 : e 0 = 0 := by rw [he, map_zero]
  rw [V_root hm he0, eval_map_per]
  refine Eq.trans ?_ (ryser_sum m (fun p : Fin m × Fin m => x (p.1 * m + p.2)))
  refine Finset.sum_congr rfl fun t _ => ?_
  beta_reduce
  unfold term rowSum
  rw [he, sgn_eq_prod, map_prod, Finset.prod_range]
  congr 1
  · refine Finset.prod_congr rfl fun q _ => ?_
    split_ifs <;> simp
  · rw [Finset.prod_range]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [Finset.sum_range]

end Ryser

end ClassSep
