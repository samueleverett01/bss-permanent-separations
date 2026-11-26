import ClassSeparations.Machines.Simulate

/-!
# Advice in one real constant

An infinite bit stream `b : ℕ → Bool` (with infinitely many zeros) is stored in the real number
`tailVal b 0 = ∑ⱼ b(j) 2^{-(j+1)} ∈ [0, 1)`.  A machine reads the bits one after the other by
*doubling and comparing*: if `A = tailVal b k` then `2A = b(k) + tailVal b (k+1)` with
`tailVal b (k+1) < 1`, so `b(k) = 1` iff `2A - 1 ≥ 0`, and `A` becomes `tailVal b (k+1)`.

Natural numbers are written in unary (`v` ones and a zero, `encNum`); `readNum` reads one of
them into an index register.  A stream made of infinitely many nonempty blocks
(`streamOf`) contains each block at a known position (`streamOf_has`).
-/

set_option autoImplicit false

noncomputable section

open Classical

namespace ClassSep

namespace AMNPAux

open Prog

/-! ## The value of a bit stream -/

/-- The value of the bit stream `b` from position `k` on. -/
def tailVal (b : ℕ → Bool) (k : ℕ) : ℝ := ∑' j, bitR (b (k + j)) * (1 / 2) ^ (j + 1)

theorem bitR_nonneg (x : Bool) : 0 ≤ bitR x := by cases x <;> simp [bitR]

theorem bitR_le_one (x : Bool) : bitR x ≤ 1 := by cases x <;> simp [bitR]

theorem summable_geom1 : Summable fun j : ℕ => ((1 : ℝ) / 2) ^ (j + 1) := by
  exact (summable_geometric_two.mul_right (1 / 2)).congr fun j => (pow_succ _ _).symm

theorem tsum_geom1 : ∑' j : ℕ, ((1 : ℝ) / 2) ^ (j + 1) = 1 := by
  simp only [pow_succ]
  rw [tsum_mul_right, tsum_geometric_two]
  norm_num

theorem tailVal_summable (b : ℕ → Bool) (k : ℕ) :
    Summable fun j => bitR (b (k + j)) * ((1 : ℝ) / 2) ^ (j + 1) :=
  Summable.of_nonneg_of_le (fun j => mul_nonneg (bitR_nonneg _) (by positivity))
    (fun j => by
      have := bitR_le_one (b (k + j))
      have h : (0 : ℝ) ≤ (1 / 2) ^ (j + 1) := by positivity
      nlinarith) summable_geom1

theorem tailVal_succ (b : ℕ → Bool) (k : ℕ) :
    tailVal b k = (bitR (b k) + tailVal b (k + 1)) / 2 := by
  unfold tailVal
  rw [(tailVal_summable b k).tsum_eq_zero_add]
  have : ∀ j, bitR (b (k + (j + 1))) * ((1 : ℝ) / 2) ^ (j + 1 + 1) =
      (1 / 2) * (bitR (b (k + 1 + j)) * (1 / 2) ^ (j + 1)) := by
    intro j
    rw [show k + (j + 1) = k + 1 + j by omega, pow_succ]
    ring
  simp only [this, tsum_mul_left, Nat.add_zero]
  ring

theorem tailVal_nonneg (b : ℕ → Bool) (k : ℕ) : 0 ≤ tailVal b k :=
  tsum_nonneg fun j => mul_nonneg (bitR_nonneg _) (by positivity)

theorem tailVal_lt_one (b : ℕ → Bool) (k : ℕ) (h : ∃ j, k ≤ j ∧ b j = false) :
    tailVal b k < 1 := by
  obtain ⟨j, hkj, hj⟩ := h
  rw [← tsum_geom1]
  refine Summable.tsum_lt_tsum_of_nonneg (i := j - k)
    (fun j => mul_nonneg (bitR_nonneg _) (by positivity)) (fun j => ?_) ?_ summable_geom1
  · have := bitR_le_one (b (k + j))
    have h : (0 : ℝ) ≤ (1 / 2) ^ (j + 1) := by positivity
    nlinarith
  · rw [show k + (j - k) = j by omega, hj]
    simp only [bitR_false, zero_mul]
    positivity

/-! ## Bit lists in a stream -/

/-- The stream `b` contains the list `l` at position `k`. -/
def Has (b : ℕ → Bool) (k : ℕ) (l : List Bool) : Prop :=
  ∀ i (h : i < l.length), b (k + i) = l[i]

theorem Has.append {b : ℕ → Bool} {k : ℕ} {l₁ l₂ : List Bool} :
    Has b k (l₁ ++ l₂) ↔ Has b k l₁ ∧ Has b (k + l₁.length) l₂ := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rw [h i (by simp; omega), List.getElem_append_left hi]
    · rw [Nat.add_assoc, h (l₁.length + i) (by simp; omega),
        List.getElem_append_right (by omega)]
      simp
  · rintro ⟨h₁, h₂⟩ i hi
    by_cases hi' : i < l₁.length
    · rw [h₁ i hi', List.getElem_append_left hi']
    · have := h₂ (i - l₁.length) (by simp at hi; omega)
      rw [show k + l₁.length + (i - l₁.length) = k + i by omega] at this
      rw [this, List.getElem_append_right (by omega)]

/-- Unary code of a natural number: `v` ones and a zero. -/
def encNum (v : ℕ) : List Bool := List.replicate v true ++ [false]

@[simp] theorem length_encNum (v : ℕ) : (encNum v).length = v + 1 := by simp [encNum]

/-- Unary codes of a list of numbers. -/
def encList (l : List ℕ) : List Bool := l.flatMap encNum

@[simp] theorem encList_nil : encList [] = [] := rfl

@[simp] theorem encList_cons (v : ℕ) (l : List ℕ) :
    encList (v :: l) = encNum v ++ encList l := rfl

theorem encList_append (l₁ l₂ : List ℕ) : encList (l₁ ++ l₂) = encList l₁ ++ encList l₂ := by
  simp [encList]

theorem length_encList (l : List ℕ) : (encList l).length = (l.map (· + 1)).sum := by
  induction l with
  | nil => rfl
  | cons v l ih => simp [ih]

theorem Has.encNum {b : ℕ → Bool} {k v : ℕ} (h : Has b k (AMNPAux.encNum v)) :
    (∀ i < v, b (k + i) = true) ∧ b (k + v) = false := by
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [h i (by simp; omega)]
    simp [AMNPAux.encNum, List.getElem_append_left (show i < (List.replicate v true).length by
      simp; omega)]
  · rw [h v (by simp)]
    simp [AMNPAux.encNum]

/-! ## Streams made of blocks -/

/-- The stream made of the blocks `blocks 0, blocks 1, …`. -/
def streamOf (blocks : ℕ → List Bool) (k : ℕ) : Bool :=
  ((List.range (k + 1)).flatMap blocks).getD k false

/-- The position of the block `m`. -/
def blockOff (blocks : ℕ → List Bool) (m : ℕ) : ℕ := ((List.range m).flatMap blocks).length

theorem blockOff_ge (blocks : ℕ → List Bool) (hne : ∀ m, blocks m ≠ []) (m : ℕ) :
    m ≤ blockOff blocks m := by
  induction m with
  | zero => simp [blockOff]
  | succ m ih =>
    simp only [blockOff, List.range_succ, List.flatMap_append, List.length_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil] at ih ⊢
    have := List.length_pos_iff.2 (hne m)
    omega

theorem blockOff_succ (blocks : ℕ → List Bool) (m : ℕ) :
    blockOff blocks (m + 1) = blockOff blocks m + (blocks m).length := by
  simp [blockOff, List.range_succ]

theorem range_flatMap_prefix (blocks : ℕ → List Bool) (a d : ℕ) :
    ∃ l, (List.range (a + d)).flatMap blocks = (List.range a).flatMap blocks ++ l := by
  induction d with
  | zero => exact ⟨[], by simp⟩
  | succ d ih =>
    obtain ⟨l, hl⟩ := ih
    refine ⟨l ++ blocks (a + d), ?_⟩
    rw [show a + (d + 1) = a + d + 1 by omega, List.range_succ, List.flatMap_append, hl]
    simp

theorem streamOf_has (blocks : ℕ → List Bool) (hne : ∀ m, blocks m ≠ []) (m : ℕ) :
    Has (streamOf blocks) (blockOff blocks m) (blocks m) := by
  intro i hi
  have hge := blockOff_ge blocks hne m
  unfold streamOf
  set K := blockOff blocks m + i + 1
  obtain ⟨l, hl⟩ := range_flatMap_prefix blocks (m + 1) (K - (m + 1))
  rw [show m + 1 + (K - (m + 1)) = K by omega] at hl
  rw [hl, List.range_succ, List.flatMap_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
  rw [List.getD_append_right _ _ _ _ (by simp [blockOff]), List.getD_append _ _ _ _ (by
    simp [blockOff]; omega)]
  simp [blockOff, List.getElem?_eq_getElem hi]

theorem streamOf_inf (blocks : ℕ → List Bool) (hne : ∀ m, blocks m ≠ [])
    (hz : ∀ m, false ∈ blocks m) (k : ℕ) : ∃ j, k ≤ j ∧ streamOf blocks j = false := by
  obtain ⟨i, hi, hfi⟩ := List.getElem_of_mem (hz k)
  refine ⟨blockOff blocks k + i, by have := blockOff_ge blocks hne k; omega, ?_⟩
  rw [streamOf_has blocks hne k i hi, hfi]

/-! ## Reading a number -/

/-- Read a unary number from the stream held in `R[I aP]` and add it to `I k` (constant `1` in
`R[I oneP]`, scratch `R[I tmpP]`, flag register `flag`, `I z = 0`). -/
def readNum (k flag aP oneP tmpP z : ℕ) : Stmt :=
  .seq (.op (.inc flag)) (.loop (.idxEq flag z) (.seqs [
    .op (.arith .add aP aP aP),
    .op (.arith .sub tmpP aP oneP),
    .ite (.nonneg tmpP) (.seq (.op (.copy aP tmpP)) (.op (.inc k))) (.op (.dec flag))]))

/-- Registers of `readNum`. -/
structure ReadOk (k flag aP oneP tmpP z : ℕ) : Prop where
  kf : k ≠ flag
  kz : k ≠ z
  fz : flag ≠ z
  ka : k ≠ aP
  ko : k ≠ oneP
  kt : k ≠ tmpP
  fa : flag ≠ aP
  fo : flag ≠ oneP
  ft : flag ≠ tmpP

theorem readNum_spec {b : ℕ → Bool} (hinf : ∀ k, ∃ j, k ≤ j ∧ b j = false) {pos v : ℕ}
    (hb : Has b pos (encNum v)) {st : St} {k flag aP oneP tmpP z : ℕ}
    (hr : ReadOk k flag aP oneP tmpP z)
    (hat : st.I aP ≠ st.I tmpP) (hot : st.I oneP ≠ st.I tmpP) (hao : st.I aP ≠ st.I oneP)
    (hone : st.R (st.I oneP) = 1) (hA : st.R (st.I aP) = tailVal b pos)
    (hflag : st.I flag = 0) (hz : st.I z = 0) :
    Runs (readNum k flag aP oneP tmpP z) st (fun st' =>
      st'.I = Function.update st.I k (st.I k + v) ∧
      st'.R (st.I aP) = tailVal b (pos + v + 1) ∧
      ∀ i, i ≠ st.I aP → i ≠ st.I tmpP → st'.R i = st.R i) (8 * v + 10) := by
  obtain ⟨hones, hzero⟩ := hb.encNum
  obtain ⟨R₀, I₀⟩ := st
  simp only at hat hot hao hone hA hflag hz ⊢
  set a := I₀ aP
  set o := I₀ oneP
  set t := I₀ tmpP
  -- the state before the iteration `j ≤ v`
  let Inv : ℕ → St → Prop := fun j st' =>
    (∀ i, i ≠ a → i ≠ t → st'.R i = R₀ i) ∧
    (j ≤ v → st'.I = Function.update (Function.update I₀ k (I₀ k + j)) flag 1 ∧
      st'.R a = tailVal b (pos + j)) ∧
    (v < j → st'.I = Function.update I₀ k (I₀ k + v) ∧ st'.R a = tailVal b (pos + v + 1))
  have hIa : ∀ j, (Function.update (Function.update I₀ k (I₀ k + j)) flag 1) aP = a := by
    intro j; simp [Function.update_of_ne hr.fa.symm, Function.update_of_ne hr.ka.symm, a]
  have hIo : ∀ j, (Function.update (Function.update I₀ k (I₀ k + j)) flag 1) oneP = o := by
    intro j; simp [Function.update_of_ne hr.fo.symm, Function.update_of_ne hr.ko.symm, o]
  have hIt : ∀ j, (Function.update (Function.update I₀ k (I₀ k + j)) flag 1) tmpP = t := by
    intro j; simp [Function.update_of_ne hr.ft.symm, Function.update_of_ne hr.kt.symm, t]
  have hloop : Runs (.loop (.idxEq flag z) (.seqs [
      .op (.arith .add aP aP aP),
      .op (.arith .sub tmpP aP oneP),
      .ite (.nonneg tmpP) (.seq (.op (.copy aP tmpP)) (.op (.inc k))) (.op (.dec flag))]))
      ⟨R₀, Function.update I₀ flag (I₀ flag + 1)⟩ (Inv (v + 1)) ((v + 1) * (6 + 2) + 1) := by
    refine Spec.loop Inv (v + 1) ?_ ?_ ?_ ?_
    · rintro st' ⟨-, -, h⟩
      obtain ⟨hI, -⟩ := h (by omega)
      simp [hI, Function.update_of_ne hr.fz.symm, Function.update_of_ne hr.kz.symm, hz, hflag,
        Function.update_of_ne hr.kf.symm]
    · rintro j hj st' ⟨-, h, -⟩
      obtain ⟨hI, -⟩ := h (by omega)
      simp [hI, Function.update_of_ne hr.fz.symm, Function.update_of_ne hr.kz.symm, hz]
    · rintro j hj st' ⟨hR, h, -⟩
      obtain ⟨hI, hAj⟩ := h (by omega)
      obtain ⟨R₁, I₁⟩ := st'
      simp only at hI hAj hR
      subst hI
      have hone' : R₁ o = 1 := by rw [hR o hao.symm hot, hone]
      have hstep := tailVal_succ b (pos + j)
      -- after `A := A + A` and `TMP := A - 1`
      have hA2 : R₁ a + R₁ a = bitR (b (pos + j)) + tailVal b (pos + j + 1) := by
        rw [hAj, hstep]; ring
      show Spec (.seq (.op (.arith .add aP aP aP)) (.seq (.op (.arith .sub tmpP aP oneP))
        (.seq (.ite (.nonneg tmpP) (.seq (.op (.copy aP tmpP)) (.op (.inc k))) (.op (.dec flag)))
        .skip))) _ (Inv (j + 1)) _ (1 + (1 + (4 + 0)))
      refine Spec.seq_op (st :=⟨R₁, Function.update (Function.update I₀ k (I₀ k + j)) flag 1⟩)
        (o := .arith .add aP aP aP) (st' := ⟨Function.update R₁ a (R₁ a + R₁ a),
        Function.update (Function.update I₀ k (I₀ k + j)) flag 1⟩) (by simp [hIa]) ?_
      refine Spec.seq_op (st := ⟨Function.update R₁ a (R₁ a + R₁ a),
        Function.update (Function.update I₀ k (I₀ k + j)) flag 1⟩)
        (o := .arith .sub tmpP aP oneP) (st' := ⟨Function.update (Function.update R₁ a (R₁ a + R₁ a)) t
        (R₁ a + R₁ a - 1), Function.update (Function.update I₀ k (I₀ k + j)) flag 1⟩)
        (by simp [hIa, hIo, hIt, Function.update_of_ne hao.symm, hone', Function.update_of_ne hat]) ?_
      refine Spec.seq (T₁ := 4) (T₂ := 0) (Spec.ite (T := 2) (fun hc => ?_) (fun hc => ?_))
        fun st₁ h₁ => Spec.skip h₁
      · -- a one: `A := TMP; I k += 1`
        simp only [Cond.holds_nonneg, hIt, Function.update_self] at hc
        have hbit : b (pos + j) = true := by
          by_contra hb'
          have hb0 : b (pos + j) = false := by simpa using hb'
          rw [hb0, bitR_false, zero_add] at hA2
          have := tailVal_lt_one b (pos + j + 1) (hinf _)
          linarith
        have hjv : j < v := by
          by_contra hjv
          have : j = v := by omega
          subst this
          rw [hzero] at hbit
          cases hbit
        refine Spec.seq_op rfl (Spec.inc ?_ le_rfl)
        refine ⟨fun i hia hit => ?_, fun _ => ⟨?_, ?_⟩, fun h => absurd h (by omega)⟩
        · simp [hIa, hIt, Function.update_of_ne hia, Function.update_of_ne hit, hR i hia hit]
        · funext l
          by_cases hl1 : l = k
          · subst hl1
            simp [Function.update_of_ne hr.kf]
            omega
          · by_cases hl2 : l = flag
            · subst hl2
              simp [Function.update_of_ne hr.kf.symm]
            · simp [Function.update_of_ne hl1, Function.update_of_ne hl2]
        · simp only [hIa, hIt, Function.update_self, Function.update_of_ne hat]
          rw [hA2, hbit, bitR_true]
          ring_nf
      · -- a zero: the number ends
        simp only [Cond.holds_nonneg, hIt, Function.update_self, not_le] at hc
        have hbit : b (pos + j) = false := by
          by_contra hb'
          have hb1 : b (pos + j) = true := by simpa using hb'
          rw [hb1, bitR_true] at hA2
          have := tailVal_nonneg b (pos + j + 1)
          linarith
        have hjv : j = v := by
          by_contra hjv
          have := hones j (by omega)
          rw [this] at hbit
          cases hbit
        subst hjv
        refine Spec.dec ?_ (by norm_num)
        refine ⟨fun i hia hit => ?_, fun h => absurd h (by omega), fun _ => ⟨?_, ?_⟩⟩
        · simp [Function.update_of_ne hia, Function.update_of_ne hit, hR i hia hit]
        · funext l
          by_cases hl : l = flag
          · subst hl
            simp [Function.update_of_ne hr.kf.symm, hflag]
          · simp [Function.update_of_ne hl]
        · simp only [Function.update_of_ne hat, Function.update_self]
          rw [hA2, hbit, bitR_false, zero_add]
    · refine ⟨fun i _ _ => rfl, fun _ => ⟨?_, by simpa using hA⟩, fun h => absurd h (by omega)⟩
      funext l
      by_cases hl : l = flag
      · subst hl
        simp [Function.update_of_ne hr.kf.symm, hflag]
      · by_cases hl' : l = k
        · subst hl'
          simp [Function.update_of_ne hl]
        · simp [Function.update_of_ne hl, Function.update_of_ne hl']
  refine (Spec.seq_op rfl hloop).mono_post ?_ |>.mono_time (by omega)
  rintro st' ⟨hR, -, h⟩
  obtain ⟨hI, hAv⟩ := h (by omega)
  exact ⟨hI, hAv, hR⟩

end AMNPAux

end ClassSep
