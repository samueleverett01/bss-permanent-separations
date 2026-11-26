import ClassSeparations.Machines.Advice

/-!
# Counting accepting runs of a machine on gathered inputs, with advice

The machine-construction lemma behind `AM_ℝ[c] ⊆ NP_ℝ`.  For each input size `n` we are given a
list of *leaves*; a leaf is a list of positions, and the input of the machine `M` at a leaf is
*gathered* from the input `x`, the certificate `S` and the constants `0`, `1` at these
positions.  We build a machine that, on `(x, S)`, runs `M` at every leaf and accepts iff at
least `K(n)` of the runs accept.  The leaves (and all other data that depend on `n`) are
advice; they are stored in one real constant and read by doubling and comparing
(`Machines/Advice.lean`).

Layout.  Index registers `< b = idxBd M + 3` belong to `M`; the host uses `b, b+1, …, b+26`:
`b` zero, `b+1..b+3` interpreter, `b+4` `n` (`b+5` unused), `b+6`/`b+7`/`b+8` addresses of the
stream value `A`, of the constant `1` and of a scratch register, `b+9` flag of `readNum`,
`b+10` scratch counter, `b+11`/`b+12`/`b+13` block counter, block length, junk, `b+14` the
high-water mark `Hm`, `b+15`/`b+16` the block sizes of `M`, `b+17` the input length `N` of `M`,
`b+18` the number of accepting leaves still needed, `b+19` the source address, `b+20` the leaf
marker, `b+21`/`b+22` gather counter and source pointer, `b+23..b+25` scratch, `b+26` the
length of the relocated area.  Real registers `< Hm` belong to `M`; above `Hm` the host keeps
`x`, `S`, `0`, `1`, `A` and a scratch register.
-/

set_option autoImplicit false

noncomputable section

open Classical

namespace ClassSep

namespace AMNPAux

open Prog

/-! ## Gathered inputs -/

/-- The source registers of a gather: `x`, the certificate `S`, then the constants `0`, `1`. -/
def srcVal {n q : ℕ} (x : Fin n → ℝ) (S : Fin q → ℝ) (k : ℕ) : ℝ :=
  if k < n + q then vecReg (Fin.append x S) k else if k = n + q + 1 then 1 else 0

/-- The input of length `N` gathered from the positions `ℓ`. -/
def gather {n q : ℕ} (x : Fin n → ℝ) (S : Fin q → ℝ) (N : ℕ) (ℓ : List ℕ) : Fin N → ℝ :=
  fun j => srcVal x S (ℓ.getD j 0)

/-! ## The advice -/

/-- The numbers describing the leaves: `1` and the positions, for each leaf, then `0`. -/
def leafNums (LV : List (List ℕ)) : List ℕ := LV.flatMap (fun ℓ => 1 :: ℓ) ++ [0]

/-- The block of advice for one input size, preceded by its length. -/
def blockNums (Hm s₁ s₂ K : ℕ) (N : ℕ) (LV : List (List ℕ)) : List ℕ :=
  let l := [Hm, s₁, s₂, N, K] ++ leafNums LV
  l.length :: l

/-! ## The program -/

/-- Read a number from the advice into `I k`. -/
def rdN (b k : ℕ) : Stmt := readNum k (b + 9) (b + 6) (b + 7) (b + 8) b

/-- Phase 0: copy the sizes; the stream registers sit right after the input. -/
def initS (b : ℕ) (α : ℝ) : Stmt :=
  Stmt.seqs [loadIdx (b + 4) 0, loadIdx (b + 7) 0, addIdx (b + 7) 1 (b + 10) b,
    .op (.inc (b + 7)), loadIdx (b + 6) (b + 7), .op (.inc (b + 6)), loadIdx (b + 8) (b + 6),
    .op (.inc (b + 8)), .op (.const (b + 7) 1), .op (.const (b + 6) α)]

/-- Skip one block of advice. -/
def skipBlockS (b : ℕ) : Stmt :=
  Stmt.seqs [rdN b (b + 12), .loop (.idxEq (b + 12) b)
    (Stmt.seqs [rdN b (b + 13), clearIdx (b + 13) b, .op (.dec (b + 12))])]

/-- Phase 1: skip the blocks of the sizes `< n`. -/
def skipS (b : ℕ) : Stmt :=
  .loop (.idxEq (b + 11) (b + 4)) (.seq (skipBlockS b) (.op (.inc (b + 11))))

/-- Phase 2: read the header of the block of size `n` (its length is skipped). -/
def headerS (b : ℕ) : Stmt :=
  Stmt.seqs [rdN b (b + 13), clearIdx (b + 13) b, rdN b (b + 14), rdN b (b + 15),
    rdN b (b + 16), rdN b (b + 17), rdN b (b + 18)]

/-- Phase 3: copy the input and the stream registers above the high-water mark. -/
def relocS (b : ℕ) : Stmt :=
  Stmt.seqs [loadIdx (b + 26) (b + 8), .op (.inc (b + 26)),
    copyRange b (b + 14) (b + 26) (b + 23) (b + 24) (b + 25) b,
    addIdx (b + 6) (b + 14) (b + 10) b, addIdx (b + 7) (b + 14) (b + 10) b,
    addIdx (b + 8) (b + 14) (b + 10) b, loadIdx (b + 19) (b + 14)]

/-- Reset the index registers of `M`: `I k := 0` for `k < b`, then the block sizes. -/
def resetS (b : ℕ) : Stmt :=
  .seq (Stmt.seqs ((List.range b).map fun k => clearIdx k b))
    (Stmt.seqs [loadIdx 0 (b + 4), loadIdx 1 (b + 15), loadIdx 2 (b + 16)])

/-- The gather loop: `R[j] := R[I srcP + ℓⱼ]` for `j < N`. -/
def gatherS (b : ℕ) : Stmt :=
  .loop (.idxEq (b + 21) (b + 17)) (Stmt.seqs [loadIdx (b + 22) (b + 19), rdN b (b + 22),
    .op (.copy (b + 21) (b + 22)), clearIdx (b + 22) b, .op (.inc (b + 21))])

/-- One leaf: clear `M`'s registers, gather its input, run it, count. -/
def leafS (M : Machine) (b : ℕ) : Stmt :=
  Stmt.seqs [fillRange b (b + 14) 0 (b + 24) (b + 25) b, gatherS b, clearIdx (b + 21) b,
    resetS b, simStmt M (b + 1) (b + 2) (b + 3) b,
    .ite (.idxEq (b + 3) b) .skip (.seq (.op (.dec (b + 3))) (.op (.dec (b + 18))))]

/-- The leaf loop. -/
def leavesS (M : Machine) (b : ℕ) : Stmt :=
  .loop (.idxEq (b + 20) b) (Stmt.seqs [leafS M b, clearIdx (b + 20) b, rdN b (b + 20)])

/-- The machine (as a structured program), with the advice constant `α`. -/
def gStmt (M : Machine) (α : ℝ) : Stmt :=
  Stmt.seqs [initS (idxBd M + 3) α, skipS (idxBd M + 3), headerS (idxBd M + 3),
    relocS (idxBd M + 3), rdN (idxBd M + 3) (idxBd M + 3 + 20), leavesS M (idxBd M + 3),
    .ite (.idxEq (idxBd M + 3 + 18) (idxBd M + 3)) (.halt true) (.halt false)]

/-! ## Generic lemmas -/

theorem clearList_spec (z : ℕ) : ∀ (l : List ℕ) (st : St) (B : ℕ), z ∉ l → st.I z = 0 →
    l.Nodup → (∀ k ∈ l, st.I k ≤ B) →
    Runs (Stmt.seqs (l.map fun k => clearIdx k z)) st
      (fun st' => st'.R = st.R ∧ ∀ k, st'.I k = if k ∈ l then 0 else st.I k)
      (l.length * (3 * B + 1))
  | [], st, B, _, _, _, _ => Spec.skip ⟨rfl, fun k => by simp⟩
  | k :: l, st, B, hz, hz0, hnd, hB => by
    simp only [List.map_cons, Stmt.seqs_cons]
    have hkz : k ≠ z := fun h => hz (h ▸ List.mem_cons_self ..)
    have hzl : z ∉ l := fun h => hz (List.mem_cons_of_mem _ h)
    have hkl : k ∉ l := (List.nodup_cons.1 hnd).1
    have ih := clearList_spec z l ⟨st.R, Function.update st.I k 0⟩ B hzl
      (by simp [Function.update_of_ne hkz.symm, hz0]) (List.nodup_cons.1 hnd).2
      (fun k' hk' => by
        have hne : k' ≠ k := fun h => hkl (h ▸ hk')
        simp only [Function.update_of_ne hne]
        exact hB k' (List.mem_cons_of_mem _ hk'))
    refine (Spec.seq_eq (clearIdx_spec hkz hz0) ih).mono_time ?_ |>.mono_post ?_
    · have := hB k (List.mem_cons_self ..)
      simp only [List.length_cons]
      nlinarith
    · rintro st' ⟨hR, hI⟩
      refine ⟨hR, fun k' => ?_⟩
      rw [hI k']
      by_cases h1 : k' ∈ l
      · simp [h1]
      · by_cases h2 : k' = k
        · subst h2; simp
        · simp [h1, h2, Function.update_of_ne h2]

/-- The host registers `≥ b` are given by `F`. -/
def HostEq (b : ℕ) (st : St) (F : ℕ → ℕ) : Prop := ∀ k, b ≤ k → st.I k = F k

theorem HostEq.upd {b : ℕ} {st : St} {F : ℕ → ℕ} (h : HostEq b st F) (R' : ℕ → ℝ) (k v : ℕ) :
    HostEq b ⟨R', Function.update st.I k v⟩ (Function.update F k v) := by
  intro k' hk'
  by_cases h' : k' = k
  · subst h'; simp
  · simp [Function.update_of_ne h', h k' hk']

theorem HostEq.upd_low {b : ℕ} {st : St} {F : ℕ → ℕ} (h : HostEq b st F) (R' : ℕ → ℝ) {k : ℕ}
    (hk : k < b) (v : ℕ) : HostEq b ⟨R', Function.update st.I k v⟩ F := by
  intro k' hk'
  simp [Function.update_of_ne (show k' ≠ k by omega), h k' hk']

/-- The values of the host registers during the leaf loop. -/
structure FOk (b n q Hm s₁ s₂ N : ℕ) (F : ℕ → ℕ) : Prop where
  z : F b = 0
  pc : F (b + 1) = 0
  run : F (b + 2) = 0
  acc : F (b + 3) = 0
  nR : F (b + 4) = n
  aP : F (b + 6) = Hm + n + q + 2
  oneP : F (b + 7) = Hm + n + q + 1
  tmpP : F (b + 8) = Hm + n + q + 3
  flag : F (b + 9) = 0
  hm : F (b + 14) = Hm
  s1 : F (b + 15) = s₁
  s2 : F (b + 16) = s₂
  NR : F (b + 17) = N
  src : F (b + 19) = Hm
  jR : F (b + 21) = 0
  posP : F (b + 22) = 0
  sq : F (b + 24) = 0
  sc : F (b + 25) = 0

theorem FOk.upd {b n q Hm s₁ s₂ N : ℕ} {F : ℕ → ℕ} (h : FOk b n q Hm s₁ s₂ N F) {k : ℕ}
    (hk : k = b + 18 ∨ k = b + 20) (v : ℕ) : FOk b n q Hm s₁ s₂ N (Function.update F k v) := by
  rcases hk with rfl | rfl <;>
  exact ⟨by simp [h.z], by simp [h.pc], by simp [h.run], by simp [h.acc], by simp [h.nR],
    by simp [h.aP], by simp [h.oneP], by simp [h.tmpP], by simp [h.flag], by simp [h.hm],
    by simp [h.s1], by simp [h.s2], by simp [h.NR], by simp [h.src], by simp [h.jR],
    by simp [h.posP], by simp [h.sq], by simp [h.sc]⟩

theorem rdN_ok (b k : ℕ) (hk : b + 10 ≤ k) : ReadOk k (b + 9) (b + 6) (b + 7) (b + 8) b :=
  ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem encList_take_succ (ℓ : List ℕ) (t : ℕ) (h : t < ℓ.length) :
    encList (ℓ.take (t + 1)) = encList (ℓ.take t) ++ encNum ℓ[t] := by
  rw [List.take_succ, encList_append, List.getElem?_eq_getElem h]
  simp [encList]

theorem has_split {str : ℕ → Bool} {pos : ℕ} {ℓ rest : List ℕ} (t : ℕ) (h : t < ℓ.length)
    (hs : Has str pos (encList (ℓ ++ rest))) :
    Has str (pos + (encList (ℓ.take t)).length) (encNum ℓ[t]) := by
  have e : ℓ ++ rest = ℓ.take t ++ (ℓ[t] :: (ℓ.drop (t + 1) ++ rest)) := by
    rw [← List.cons_append, ← List.append_assoc, ← List.drop_eq_getElem_cons h,
      List.take_append_drop]
  rw [e, encList_append, encList_cons] at hs
  exact (Has.append.1 (Has.append.1 hs).2).1

theorem srcVal_one {n q : ℕ} (x : Fin n → ℝ) (S : Fin q → ℝ) : srcVal x S (n + q + 1) = 1 := by
  simp [srcVal]

theorem srcVal_zero {n q : ℕ} (x : Fin n → ℝ) (S : Fin q → ℝ) : srcVal x S (n + q) = 0 := by
  simp [srcVal]

/-! ## The gather loop -/

/-- The time bound of one gather step. -/
def gTime (n q Hm : ℕ) : ℕ := 6 * Hm + 11 * (n + q) + 30

section Gather

variable {b n q Hm s₁ s₂ N : ℕ} {x : Fin n → ℝ} {S : Fin q → ℝ} {str : ℕ → Bool}

theorem gather_spec (hinf : ∀ k, ∃ j, k ≤ j ∧ str j = false) {F : ℕ → ℕ}
    (hF : FOk b n q Hm s₁ s₂ N F) (ℓ rest : List ℕ) (hℓ : ℓ.length = N)
    (hpos : ∀ k ∈ ℓ, k ≤ n + q + 1) (hNH : N ≤ Hm) (pos : ℕ)
    (st : St) (hI : HostEq b st F) (hR : ∀ i ≤ n + q + 1, st.R (Hm + i) = srcVal x S i)
    (hA : st.R (Hm + n + q + 2) = tailVal str pos) (hzero : ∀ i < Hm, st.R i = 0)
    (hstr : Has str pos (encList (ℓ ++ rest))) :
    Runs (gatherS b) st (fun st' => HostEq b st' (Function.update F (b + 21) N) ∧
      (∀ k < b, st'.I k = st.I k) ∧ (∀ i ≤ n + q + 1, st'.R (Hm + i) = srcVal x S i) ∧
      st'.R (Hm + n + q + 2) = tailVal str (pos + (encList ℓ).length) ∧
      (∀ i < N, st'.R i = srcVal x S (ℓ.getD i 0)) ∧ (∀ i, N ≤ i → i < Hm → st'.R i = 0))
      (N * (gTime n q Hm + 2) + 1) := by
  let Inv : ℕ → St → Prop := fun t st' => HostEq b st' (Function.update F (b + 21) t) ∧
      (∀ k < b, st'.I k = st.I k) ∧ (∀ i ≤ n + q + 1, st'.R (Hm + i) = srcVal x S i) ∧
      st'.R (Hm + n + q + 2) = tailVal str (pos + (encList (ℓ.take t)).length) ∧
      (∀ i < t, st'.R i = srcVal x S (ℓ.getD i 0)) ∧ (∀ i, t ≤ i → i < Hm → st'.R i = 0)
  have hloop : Runs (gatherS b) st (Inv N) (N * (gTime n q Hm + 2) + 1) := by
    refine Spec.loop Inv N ?_ ?_ ?_ ?_
    · rintro st' ⟨hI', -⟩
      simp [hI' (b + 21) (by omega), hI' (b + 17) (by omega), hF.NR]
    · rintro t ht st' ⟨hI', -⟩
      simp [hI' (b + 21) (by omega), hI' (b + 17) (by omega), hF.NR]
      omega
    · rintro t ht st' ⟨hI', hlow, hR', hA', hdone, hzero'⟩
      have htl : t < ℓ.length := by omega
      set v := ℓ[t] with hv
      have hvle : v ≤ n + q + 1 := hpos v (List.getElem_mem htl)
      set p' := pos + (encList (ℓ.take t)).length with hp'
      have hval : ∀ k, b ≤ k → k ≠ b + 21 → st'.I k = F k := fun k hk hk' => by
        rw [hI' k hk, Function.update_of_ne hk']
      obtain ⟨R₁, I₁⟩ := st'
      simp only at hval hlow hR' hA' hdone hzero' hI'
      have h19 : I₁ (b + 19) = Hm := by rw [hval _ (by omega) (by omega), hF.src]
      have h21 : I₁ (b + 21) = t := by have := hI' (b + 21) (by omega); simpa using this
      -- the five steps
      refine (show Runs _ _ _ ((3 * Hm + 1) + ((8 * v + 10) + (1 + ((3 * (Hm + v) + 1) +
          (1 + 0))))) from ?_).mono_time (by simp only [gTime]; omega)
      refine Spec.seq ((loadIdx_spec (st := ⟨R₁, I₁⟩) (k := b + 22) (a := b + 19) (by omega)
        (by simp [hval (b + 22) (by omega) (by omega), hF.posP])).mono_time (by simp [h19])) ?_
      rintro _ rfl
      set I₂ := Function.update I₁ (b + 22) (I₁ (b + 19)) with hI₂
      have hI₂v : ∀ k, k ≠ b + 22 → I₂ k = I₁ k := fun k hk => by
        simp [hI₂, Function.update_of_ne hk]
      have h6 : I₂ (b + 6) = Hm + n + q + 2 := by
        rw [hI₂v _ (by omega), hval _ (by omega) (by omega), hF.aP]
      have h7 : I₂ (b + 7) = Hm + n + q + 1 := by
        rw [hI₂v _ (by omega), hval _ (by omega) (by omega), hF.oneP]
      have h8 : I₂ (b + 8) = Hm + n + q + 3 := by
        rw [hI₂v _ (by omega), hval _ (by omega) (by omega), hF.tmpP]
      have hrd := readNum_spec hinf (pos := p') (v := v) (has_split t htl hstr)
        (st := ⟨R₁, I₂⟩) (rdN_ok b (b + 22) (by omega)) (by simp [h6, h8])
        (by simp [h7, h8]) (by simp [h6, h7])
        (by simp only [h7]; rw [show Hm + n + q + 1 = Hm + (n + q + 1) by omega,
          hR' _ le_rfl, srcVal_one])
        (by simp only [h6]; exact hA')
        (by show I₂ (b + 9) = 0; rw [hI₂v _ (by omega), hval (b + 9) (by omega) (by omega), hF.flag])
        (by show I₂ b = 0; rw [hI₂v _ (by omega), hval b le_rfl (by omega), hF.z])
      refine Spec.seq hrd ?_
      rintro ⟨R₃, I₃⟩ ⟨hI₃, hA₃, hR₃⟩
      simp only [h6, h8] at hA₃ hR₃ hI₃
      have h22 : I₃ (b + 22) = Hm + v := by
        rw [hI₃]; simp [hI₂, h19]
      have h21' : I₃ (b + 21) = t := by
        rw [hI₃]; simp [hI₂, Function.update_of_ne (show b + 21 ≠ b + 22 by omega), h21]
      have hsrc : R₃ (Hm + v) = srcVal x S v := by
        rw [hR₃ _ (by omega) (by omega)]
        exact hR' v hvle
      refine Spec.seq (Spec.copy (Q := (· = ⟨Function.update R₃ t (srcVal x S v), I₃⟩))
        (by simp [h21', h22, hsrc]) le_rfl) ?_
      rintro _ rfl
      refine Spec.seq ((clearIdx_spec (st := ⟨Function.update R₃ t (srcVal x S v), I₃⟩)
        (k := b + 22) (z := b) (by omega) (by
          rw [hI₃]; simp [hI₂, Function.update_of_ne (show b ≠ b + 22 by omega),
            hval _ le_rfl (by omega), hF.z])).mono_time (by simp [h22])) ?_
      rintro _ rfl
      refine Spec.seq (T₂ := 0) (Spec.inc (Q := (· = ⟨Function.update R₃ t (srcVal x S v),
        Function.update (Function.update I₃ (b + 22) 0) (b + 21) (t + 1)⟩))
        (by simp [Function.update_of_ne (show b + 21 ≠ b + 22 by omega), h21']) le_rfl) ?_
      rintro _ rfl
      refine Spec.skip ⟨fun k hk => ?_, fun k hk => ?_, fun i hi => ?_, ?_, fun i hi => ?_,
        fun i hi1 hi2 => ?_⟩
      · by_cases e21 : k = b + 21
        · subst e21; simp
        · by_cases e22 : k = b + 22
          · subst e22; simp [Function.update_of_ne e21, hF.posP]
          · simp only [Function.update_of_ne e21, Function.update_of_ne e22]
            rw [hI₃]
            simp [Function.update_of_ne e22, hI₂, hval k hk e21]
      · simp only [Function.update_of_ne (show k ≠ b + 21 by omega),
          Function.update_of_ne (show k ≠ b + 22 by omega)]
        rw [hI₃]
        simp [Function.update_of_ne (show k ≠ b + 22 by omega), hI₂, hlow k hk]
      · simp only [Function.update_of_ne (show Hm + i ≠ t by omega)]
        rw [hR₃ _ (by omega) (by omega)]
        exact hR' i hi
      · simp only [Function.update_of_ne (show Hm + n + q + 2 ≠ t by omega), hA₃,
          encList_take_succ ℓ t htl, List.length_append, length_encNum, hp', hv]
        congr 1
        omega
      · by_cases hit : i = t
        · subst hit
          simp only [Function.update_self]
          rw [List.getD_eq_getElem _ _ htl]
        · simp only [Function.update_of_ne hit]
          rw [hR₃ _ (by omega) (by omega)]
          exact hdone i (by omega)
      · simp only [Function.update_of_ne (show i ≠ t by omega)]
        rw [hR₃ _ (by omega) (by omega)]
        exact hzero' i (by omega) hi2
    · refine ⟨fun k hk => ?_, fun k _ => rfl, hR, by simpa using hA, fun i hi => absurd hi
        (by omega), fun i _ hi => hzero i hi⟩
      rw [hI k hk]
      by_cases e : k = b + 21
      · subst e; simp [hF.jR]
      · simp [Function.update_of_ne e]
  refine hloop.mono_post ?_
  rintro st' ⟨h1, h2, h3, h4, h5, h6⟩
  rw [List.take_of_length_le (by omega)] at h4
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- The time bound of one leaf. -/
def leafTime (M : Machine) (b n q Hm s₁ s₂ N T : ℕ) : ℕ :=
  11 * Hm + N * (gTime n q Hm + 2) + 3 * N + b * (3 * Hm + 1) + 3 * (n + s₁ + s₂) +
    simTime M T + 20

theorem leaf_spec (M : Machine) (hb : b = idxBd M + 3)
    (hinf : ∀ k, ∃ j, k ≤ j ∧ str j = false) {F : ℕ → ℕ}
    (hF : FOk b n q Hm s₁ s₂ N F) (hN : N = n + s₁ + s₂) (ℓ rest : List ℕ)
    (hℓ : ℓ.length = N) (hpos : ∀ k ∈ ℓ, k ≤ n + q + 1) {T : ℕ} (hNT : N + T ≤ Hm) (pos : ℕ)
    {o : Option Bool}
    (hrun : M.run T (initConfig [n, s₁, s₂] (vecReg (gather x S N ℓ))) = some o)
    (st : St) (hI : HostEq b st F) (hlow : ∀ k < b, st.I k ≤ Hm)
    (hR : ∀ i ≤ n + q + 1, st.R (Hm + i) = srcVal x S i)
    (hA : st.R (Hm + n + q + 2) = tailVal str pos) (hstr : Has str pos (encList (ℓ ++ rest))) :
    Runs (leafS M b) st (fun st' =>
      HostEq b st' (Function.update F (b + 18) (F (b + 18) - (if o = some true then 1 else 0))) ∧
      (∀ k < b, st'.I k ≤ Hm) ∧ (∀ i ≤ n + q + 1, st'.R (Hm + i) = srcVal x S i) ∧
      st'.R (Hm + n + q + 2) = tailVal str (pos + (encList ℓ).length))
      (leafTime M b n q Hm s₁ s₂ N T) := by
  have hb3 : 3 ≤ b := by omega
  obtain ⟨R₀, I₀⟩ := st
  simp only at hlow hR hA
  have hIv : ∀ k, b ≤ k → I₀ k = F k := hI
  -- step 1: clear `M`'s real registers
  have s1 := fillRange_spec (st := ⟨R₀, I₀⟩) (dst := b) (len := b + 14) (v := 0) (q := b + 24)
    (c := b + 25) (z := b) (by omega) (by omega) (by omega) ⟨by omega, by omega⟩
    ⟨by omega, by omega⟩ (by simp [hIv _ (show b ≤ b + 24 by omega), hF.sq])
    (by simp [hIv _ (show b ≤ b + 25 by omega), hF.sc]) (by simp [hIv b le_rfl, hF.z])
  simp only [hIv b le_rfl, hF.z, hIv (b + 14) (by omega), hF.hm] at s1
  -- step 2: gather
  have s2 := gather_spec (S := S) (x := x) hinf hF ℓ rest hℓ hpos (by omega) pos
    ⟨fillR R₀ 0 Hm 0, I₀⟩ hI
    (fun i hi => by simp only; rw [fillR_of_not_mem (by omega)]; exact hR i hi)
    (by simp only; rw [fillR_of_not_mem (by omega)]; exact hA)
    (fun i hi => fillR_of_mem ⟨by omega, by omega⟩) hstr
  refine (show Runs _ _ _ ((11 * Hm + 4) + ((N * (gTime n q Hm + 2) + 1) + ((3 * N + 1) +
      ((b * (3 * Hm + 1) + ((3 * n + 1) + ((3 * s₁ + 1) + ((3 * s₂ + 1) + 0)))) +
      (simTime M T + (4 + 0)))))) from ?_).mono_time (by simp only [leafTime]; omega)
  refine Spec.seq_eq (s1.mono_time (by omega)) (Spec.seq s2 ?_)
  rintro ⟨R₂, I₂⟩ ⟨hI₂, hlow₂, hR₂, hA₂, hg₂, hz₂⟩
  simp only at hI₂ hlow₂ hR₂ hA₂ hg₂ hz₂
  have hI₂v : ∀ k, b ≤ k → I₂ k = Function.update F (b + 21) N k := hI₂
  -- step 3: `I jR := 0`
  have s3 := clearIdx_spec (st := ⟨R₂, I₂⟩) (k := b + 21) (z := b) (by omega)
    (by show I₂ b = 0; rw [hI₂v b le_rfl]; simp [hF.z])
  have e21 : I₂ (b + 21) = N := by rw [hI₂v _ (by omega)]; simp
  simp only [e21] at s3
  refine Spec.seq_eq s3 ?_
  set I₃ := Function.update I₂ (b + 21) 0 with hI₃
  have hI₃v : ∀ k, b ≤ k → I₃ k = F k := by
    intro k hk
    by_cases e : k = b + 21
    · subst e; simp [hI₃, hF.jR]
    · simp [hI₃, Function.update_of_ne e, hI₂v k hk]
  have hlow₃ : ∀ k < b, I₃ k = I₀ k := fun k hk => by
    simp [hI₃, Function.update_of_ne (show k ≠ b + 21 by omega), hlow₂ k hk]
  -- step 4: reset `M`'s index registers
  have s4a := clearList_spec b (List.range b) ⟨R₂, I₃⟩ Hm (by simp) (by simp [hI₃v b le_rfl, hF.z])
    (List.nodup_range) (fun k hk => by
      simp only [List.mem_range] at hk
      simp only; rw [hlow₃ k hk]; exact hlow k hk)
  simp only [List.length_range] at s4a
  set I₄ : ℕ → ℕ := fun k => if k ∈ List.range b then 0 else I₃ k with hI₄
  set I₅ := Function.update (Function.update (Function.update I₄ 0 n) 1 s₁) 2 s₂ with hI₅
  have h0 : I₄ 0 = 0 := by simp [hI₄]; omega
  have h1 : I₄ 1 = 0 := by simp [hI₄]; omega
  have h2 : I₄ 2 = 0 := by simp [hI₄]; omega
  have hI₄v : ∀ k, b ≤ k → I₄ k = F k := fun k hk => by
    simp [hI₄, show ¬ k < b by omega, hI₃v k hk]
  have hb4 : I₄ (b + 4) = n := by rw [hI₄v _ (by omega), hF.nR]
  have hb15 : I₄ (b + 15) = s₁ := by rw [hI₄v _ (by omega), hF.s1]
  have hb16 : I₄ (b + 16) = s₂ := by rw [hI₄v _ (by omega), hF.s2]
  have hreset : Runs (resetS b) ⟨R₂, I₃⟩ (· = ⟨R₂, I₅⟩)
      (b * (3 * Hm + 1) + ((3 * n + 1) + ((3 * s₁ + 1) + ((3 * s₂ + 1) + 0)))) := by
    refine Spec.seq (Q₁ := (· = ⟨R₂, I₄⟩)) (s4a.mono_post ?_) ?_
    · rintro ⟨R₄, I₄'⟩ ⟨hR₄, hI₄'⟩
      simp only at hR₄ hI₄'
      subst hR₄
      congr 1
      funext k
      exact hI₄' k
    rintro _ rfl
    have l0 := loadIdx_spec (st := ⟨R₂, I₄⟩) (k := 0) (a := b + 4) (by omega) h0
    simp only [hb4] at l0
    refine Spec.seq_eq l0 ?_
    have l1 := loadIdx_spec (st := ⟨R₂, Function.update I₄ 0 n⟩) (k := 1) (a := b + 15)
      (by omega) (by simp [h1])
    simp only [Function.update_of_ne (show b + 15 ≠ 0 by omega), hb15] at l1
    refine Spec.seq_eq l1 ?_
    have l2 := loadIdx_spec (st := ⟨R₂, Function.update (Function.update I₄ 0 n) 1 s₁⟩) (k := 2)
      (a := b + 16) (by omega) (by simp [h2])
    simp only [Function.update_of_ne (show b + 16 ≠ 0 by omega),
      Function.update_of_ne (show b + 16 ≠ 1 by omega), hb16] at l2
    exact Spec.seq_eq l2 (Spec.skip rfl)
  refine Spec.seq_eq hreset ?_
  -- step 5: run `M`
  have hI₅lo : ∀ k < b, I₅ k = [n, s₁, s₂].getD k 0 := by
    intro k hk
    simp only [hI₅, Function.update_apply]
    split_ifs with e2 e1 e0
    · subst e2; rfl
    · subst e1; rfl
    · subst e0; rfl
    · simp only [hI₄, List.mem_range, hk, if_true]
      rw [List.getD_eq_default _ _ (by simp; omega)]
  have hI₅hi : ∀ k, b ≤ k → I₅ k = F k := fun k hk => by
    simp [hI₅, Function.update_of_ne (show k ≠ 2 by omega),
      Function.update_of_ne (show k ≠ 1 by omega), Function.update_of_ne (show k ≠ 0 by omega),
      hI₄v k hk]
  have hok : SimOk b (b + 1) (b + 2) (b + 3) b :=
    ⟨by omega, by omega, by omega, le_rfl, by omega, by omega, by omega, by omega, by omega,
      by omega⟩
  have hag : Agree b Hm (initConfig [n, s₁, s₂] (vecReg (gather x S N ℓ))) ⟨R₂, I₅⟩ := by
    refine ⟨fun k hk => hI₅lo k hk, fun i hi => ?_⟩
    show R₂ i = vecReg (gather x S N ℓ) i
    by_cases hiN : i < N
    · rw [hg₂ i hiN]; simp only [vecReg, hiN, dite_true]
      rfl
    · rw [hz₂ i (by omega) hi]; simp [vecReg, hiN]
  have s5 := sim_spec M hok (by omega) (c₀ := initConfig [n, s₁, s₂] (vecReg (gather x S N ℓ)))
    (B := N) (H := Hm) (T := T) rfl hrun
    (fun k hk => by
      simp only [initConfig]
      rcases Nat.lt_or_ge k 3 with h | h
      · interval_cases k <;> simp <;> omega
      · rw [List.getD_eq_default _ _ (by simp; omega)]; omega)
    hNT ⟨R₂, I₅⟩ hag (by simp [hI₅hi (b + 1) (by omega), hF.pc])
    (by simp [hI₅hi (b + 2) (by omega), hF.run]) (by simp [hI₅hi (b + 3) (by omega), hF.acc])
    (by simp [hI₅hi b le_rfl, hF.z])
  refine Spec.seq s5 ?_
  rintro ⟨R₆, I₆⟩ ⟨hI₆, hacc₆, hlo₆, hR₆⟩
  simp only at hI₆ hacc₆ hlo₆ hR₆
  -- step 6: count
  have hz6 : I₆ b = 0 := by rw [hI₆ b le_rfl (by omega), hI₅hi b le_rfl, hF.z]
  have hpost : ∀ I₇ : ℕ → ℕ, (∀ k, b ≤ k → k ≠ b + 3 → k ≠ b + 18 → I₇ k = I₆ k) →
      I₇ (b + 3) = 0 → I₇ (b + 18) = F (b + 18) - (if o = some true then 1 else 0) →
      (∀ k < b, I₇ k = I₆ k) →
      HostEq b ⟨R₆, I₇⟩ (Function.update F (b + 18)
        (F (b + 18) - (if o = some true then 1 else 0))) ∧
      (∀ k < b, (⟨R₆, I₇⟩ : St).I k ≤ Hm) ∧
      (∀ i ≤ n + q + 1, (⟨R₆, I₇⟩ : St).R (Hm + i) = srcVal x S i) ∧
      (⟨R₆, I₇⟩ : St).R (Hm + n + q + 2) = tailVal str (pos + (encList ℓ).length) := by
    intro I₇ h1 h2 h3 h4
    refine ⟨fun k hk => ?_, fun k hk => ?_, fun i hi => ?_, ?_⟩
    · by_cases e18 : k = b + 18
      · subst e18; simp [h3]
      · rw [Function.update_of_ne e18]
        by_cases e3 : k = b + 3
        · subst e3; simp [h2, hF.acc]
        · simp only
          rw [h1 k hk e3 e18, hI₆ k hk e3, hI₅hi k hk]
    · simp only; rw [h4 k hk]; exact (hlo₆ k hk).trans hNT
    · simp only; rw [hR₆ _ (by omega)]; exact hR₂ i hi
    · simp only; rw [hR₆ _ (by omega)]; exact hA₂
  have h18 : I₆ (b + 18) = F (b + 18) := by
    rw [hI₆ (b + 18) (by omega) (by omega), hI₅hi (b + 18) (by omega)]
  by_cases ho : o = some true
  · simp only [ho, if_true] at hacc₆
    set I₇ := Function.update (Function.update I₆ (b + 3) (I₆ (b + 3) - 1)) (b + 18)
      (Function.update I₆ (b + 3) (I₆ (b + 3) - 1) (b + 18) - 1) with hI₇
    have hc : ¬ (Cond.idxEq (b + 3) b).holds ⟨R₆, I₆⟩ := by simp [hacc₆, hz6]
    refine Spec.seq (T₁ := 4) (T₂ := 0) (Spec.ite_neg (T := 2) hc
      (Spec.seq_op rfl (Spec.dec (Q := (· = ⟨R₆, I₇⟩)) rfl le_rfl))) ?_
    rintro _ rfl
    refine Spec.skip ?_
    refine hpost I₇ (fun k _ e3 e18 => ?_) (by simp [hI₇, hacc₆]) ?_ (fun k hk => ?_)
    · simp [hI₇, Function.update_of_ne e3, Function.update_of_ne e18]
    · simp [hI₇, Function.update_of_ne (show b + 18 ≠ b + 3 by omega), h18, ho]
    · simp [hI₇, Function.update_of_ne (show k ≠ b + 3 by omega),
        Function.update_of_ne (show k ≠ b + 18 by omega)]
  · simp only [ho, if_false] at hacc₆
    have hc : (Cond.idxEq (b + 3) b).holds ⟨R₆, I₆⟩ := by simp [hacc₆, hz6]
    refine Spec.seq (T₁ := 4) (T₂ := 0) ((Spec.ite_pos (T := 2) hc
      (Spec.skip (Q := (· = ⟨R₆, I₆⟩)) rfl))) ?_
    rintro _ rfl
    refine Spec.skip ?_
    refine hpost _ (fun k _ _ _ => rfl) hacc₆ ?_ (fun k _ => rfl)
    simp [h18, ho]

end Gather

/-! ## The leaf loop -/

/-- The leaf marker read before the leaf `j` (`1` if there is a leaf `j`, else `0`). -/
def markAt (LV : List (List ℕ)) (j : ℕ) : ℕ := if j < LV.length then 1 else 0

/-- The advice still to be read after the marker of the leaf `j`. -/
def restAt (LV : List (List ℕ)) (j : ℕ) : List ℕ :=
  match LV.drop j with
  | [] => []
  | ℓ :: LV' => ℓ ++ leafNums LV'

theorem leafNums_drop (LV : List (List ℕ)) (j : ℕ) :
    leafNums (LV.drop j) = markAt LV j :: restAt LV j := by
  unfold restAt markAt
  rcases h : LV.drop j with _ | ⟨ℓ, LV'⟩
  · have : LV.length ≤ j := List.drop_eq_nil_iff.1 h
    simp [leafNums, show ¬ j < LV.length by omega]
  · have : j < LV.length := by
      by_contra hc
      rw [List.drop_eq_nil_of_le (by omega)] at h
      cases h
    simp [leafNums, this]

theorem restAt_of_lt (LV : List (List ℕ)) (j : ℕ) (h : j < LV.length) :
    restAt LV j = LV[j] ++ leafNums (LV.drop (j + 1)) := by
  unfold restAt
  rw [List.drop_eq_getElem_cons h]

/-- The number of accepting leaves. -/
def accCount (M : Machine) (T n s₁ s₂ N : ℕ) {q : ℕ} (x : Fin n → ℝ) (S : Fin q → ℝ)
    (LV : List (List ℕ)) : ℕ :=
  LV.countP fun ℓ => decide (M.HaltsWith T [n, s₁, s₂] (gather x S N ℓ) (some true))

section Loop

variable {b n q Hm s₁ s₂ N : ℕ} {x : Fin n → ℝ} {S : Fin q → ℝ} {str : ℕ → Bool}

theorem leaves_spec (M : Machine) (hb : b = idxBd M + 3)
    (hinf : ∀ k, ∃ j, k ≤ j ∧ str j = false) {F : ℕ → ℕ}
    (hF : FOk b n q Hm s₁ s₂ N F) (hN : N = n + s₁ + s₂) (LV : List (List ℕ))
    (hℓ : ∀ ℓ ∈ LV, ℓ.length = N) (hpos : ∀ ℓ ∈ LV, ∀ k ∈ ℓ, k ≤ n + q + 1) {T : ℕ}
    (hNT : N + T ≤ Hm)
    (hhalt : ∀ ℓ ∈ LV, ∃ o, M.run T (initConfig [n, s₁, s₂] (vecReg (gather x S N ℓ))) = some o)
    (K : ℕ) (st : St)
    (hI : HostEq b st (Function.update (Function.update F (b + 18) K) (b + 20) (markAt LV 0)))
    (hlow : ∀ k < b, st.I k ≤ Hm) (hR : ∀ i ≤ n + q + 1, st.R (Hm + i) = srcVal x S i)
    (pos : ℕ) (hA : st.R (Hm + n + q + 2) = tailVal str pos)
    (hstr : Has str pos (encList (restAt LV 0))) :
    Runs (leavesS M b) st (fun st' => st'.I (b + 18) = K - accCount M T n s₁ s₂ N x S LV ∧
      st'.I b = 0)
      (LV.length * (leafTime M b n q Hm s₁ s₂ N T + 22 + 2) + 1) := by
  let Fj : ℕ → ℕ → ℕ := fun j => Function.update (Function.update F (b + 18)
    (K - accCount M T n s₁ s₂ N x S (LV.take j))) (b + 20) (markAt LV j)
  let Inv : ℕ → St → Prop := fun j st' => HostEq b st' (Fj j) ∧ (∀ k < b, st'.I k ≤ Hm) ∧
    (∀ i ≤ n + q + 1, st'.R (Hm + i) = srcVal x S i) ∧
    ∃ pos, st'.R (Hm + n + q + 2) = tailVal str pos ∧ Has str pos (encList (restAt LV j))
  have hFj : ∀ j, FOk b n q Hm s₁ s₂ N (Fj j) := fun j =>
    (hF.upd (Or.inl rfl) _).upd (Or.inr rfl) _
  have hloop := Spec.loop (s := Stmt.seqs [leafS M b, clearIdx (b + 20) b, rdN b (b + 20)])
    (c := .idxEq (b + 20) b) (H := fun _ _ => False)
    (T := leafTime M b n q Hm s₁ s₂ N T + 22) (st := st) Inv LV.length ?_ ?_ ?_ ?_
  · refine hloop.mono_post ?_
    rintro st' ⟨hI', -⟩
    refine ⟨?_, by rw [hI' b le_rfl]; simp [Fj, hF.z]⟩
    rw [hI' (b + 18) (by omega)]
    simp [Fj, List.take_of_length_le le_rfl, accCount]
  · rintro st' ⟨hI', -⟩
    simp [hI' (b + 20) (by omega), hI' b le_rfl, Fj, markAt, (hFj 0).z, hF.z]
  · rintro j hj st' ⟨hI', -⟩
    simp [hI' (b + 20) (by omega), hI' b le_rfl, Fj, markAt, hj, hF.z]
  · rintro j hj st' ⟨hI', hlow', hR', pos', hA', hstr'⟩
    set ℓ := LV[j] with hℓdef
    have hℓmem : ℓ ∈ LV := List.getElem_mem hj
    obtain ⟨o, ho⟩ := hhalt ℓ hℓmem
    rw [restAt_of_lt LV j hj] at hstr'
    have hmark1 : Fj j (b + 20) = 1 := by simp [Fj, markAt, hj]
    have s1 := leaf_spec M hb hinf (hFj j) hN ℓ (leafNums (LV.drop (j + 1))) (hℓ ℓ hℓmem)
      (hpos ℓ hℓmem) hNT pos' ho st' hI' hlow' hR' hA' hstr'
    refine (show Runs _ _ _ (leafTime M b n q Hm s₁ s₂ N T + ((3 * 1 + 1) +
        ((8 * markAt LV (j + 1) + 10) + 0))) from ?_).mono_time (by simp [markAt]; split_ifs <;> omega)
    refine Spec.seq s1 ?_
    rintro ⟨R₁, I₁⟩ ⟨hI₁, hlow₁, hR₁, hA₁⟩
    simp only at hlow₁ hR₁ hA₁
    have hI₁v : ∀ k, b ≤ k → I₁ k = Function.update (Fj j) (b + 18)
        (Fj j (b + 18) - if o = some true then 1 else 0) k := hI₁
    have e20 : I₁ (b + 20) = 1 := by rw [hI₁v _ (by omega)]; simp [hmark1]
    have s2 := clearIdx_spec (st := ⟨R₁, I₁⟩) (k := b + 20) (z := b) (by omega)
      (by show I₁ b = 0; rw [hI₁v b le_rfl]; simp [(hFj j).z])
    simp only [e20] at s2
    refine Spec.seq_eq s2 ?_
    set I₂ := Function.update I₁ (b + 20) 0 with hI₂
    have hI₂v : ∀ k, b ≤ k → k ≠ b + 20 → I₂ k = I₁ k := fun k _ hk => by
      simp [hI₂, Function.update_of_ne hk]
    have hstr2 : Has str (pos' + (encList ℓ).length)
        (encNum (markAt LV (j + 1)) ++ encList (restAt LV (j + 1))) := by
      have := (Has.append.1 (show Has str pos' (encList ℓ ++ encList (leafNums (LV.drop (j + 1))))
        by rwa [← encList_append])).2
      rwa [leafNums_drop, encList_cons] at this
    have h6 : I₂ (b + 6) = Hm + n + q + 2 := by
      rw [hI₂v _ (by omega) (by omega), hI₁v _ (by omega)]; simp [(hFj j).aP]
    have h7 : I₂ (b + 7) = Hm + n + q + 1 := by
      rw [hI₂v _ (by omega) (by omega), hI₁v _ (by omega)]; simp [(hFj j).oneP]
    have h8 : I₂ (b + 8) = Hm + n + q + 3 := by
      rw [hI₂v _ (by omega) (by omega), hI₁v _ (by omega)]; simp [(hFj j).tmpP]
    have s3 := readNum_spec hinf (Has.append.1 hstr2).1 (st := ⟨R₁, I₂⟩)
      (rdN_ok b (b + 20) (by omega)) (by simp [h6, h8]) (by simp [h7, h8]) (by simp [h6, h7])
      (by simp only [h7]; rw [show Hm + n + q + 1 = Hm + (n + q + 1) by omega,
          hR₁ _ le_rfl, srcVal_one])
      (by simp only [h6]; exact hA₁)
      (by show I₂ (b + 9) = 0
          rw [hI₂v _ (by omega) (by omega), hI₁v _ (by omega)]; simp [(hFj j).flag])
      (by show I₂ b = 0; rw [hI₂v _ le_rfl (by omega), hI₁v _ le_rfl]; simp [(hFj j).z])
    refine Spec.seq s3 ?_
    rintro ⟨R₃, I₃⟩ ⟨hI₃, hA₃, hR₃⟩
    simp only [h6, h8] at hI₃ hA₃ hR₃
    refine Spec.skip ⟨fun k hk => ?_, fun k hk => ?_, fun i hi => ?_, _, hA₃, ?_⟩
    · show I₃ k = Fj (j + 1) k
      rw [hI₃]
      by_cases e20 : k = b + 20
      · subst e20
        simp [hI₂, Fj]
      · rw [Function.update_of_ne e20, hI₂v k hk e20, hI₁v k hk]
        by_cases e18 : k = b + 18
        · subst e18
          have hcnt : accCount M T n s₁ s₂ N x S (LV.take (j + 1)) =
              accCount M T n s₁ s₂ N x S (LV.take j) + (if o = some true then 1 else 0) := by
            simp only [accCount]
            rw [List.take_succ, List.getElem?_eq_getElem hj, Option.toList_some,
              List.countP_append, List.countP_singleton]
            congr 1
            rw [← hℓdef]
            simp [Machine.HaltsWith, ho]
          simp [Fj, hcnt]
          omega
        · simp [Fj, Function.update_of_ne e18, Function.update_of_ne e20]
    · show I₃ k ≤ Hm
      rw [hI₃, Function.update_of_ne (show k ≠ b + 20 by omega)]
      simp only [hI₂, Function.update_of_ne (show k ≠ b + 20 by omega)]
      exact hlow₁ k hk
    · show R₃ (Hm + i) = _
      rw [hR₃ _ (by omega) (by omega)]
      exact hR₁ i hi
    · have := (Has.append.1 hstr2).2
      simpa [Nat.add_assoc] using this
  · refine ⟨hI, hlow, hR, pos, hA, hstr⟩

end Loop

/-! ## Initialization and skipping the advice of the smaller sizes -/

theorem init_spec {b n q : ℕ} (hb3 : 3 ≤ b) (α : ℝ) (R₀ : ℕ → ℝ) :
    Runs (initS b α) ⟨R₀, fun k => [n, q].getD k 0⟩ (fun st' =>
      st'.R = Function.update (Function.update R₀ (n + q + 1) 1) (n + q + 2) α ∧
      ∀ k, st'.I k = if k = b + 4 then n else if k = b + 6 then n + q + 2 else
        if k = b + 7 then n + q + 1 else if k = b + 8 then n + q + 3 else [n, q].getD k 0)
      (20 * (n + q + 2)) := by
  set I₀ : ℕ → ℕ := fun k => [n, q].getD k 0 with hI₀
  have z : ∀ k, b ≤ k → I₀ k = 0 := fun k hk => by
    simp only [hI₀]; rw [List.getD_eq_default _ _ (by simp; omega)]
  set J1 := Function.update I₀ (b + 4) (I₀ 0) with hJ1
  have h1 : Runs (loadIdx (b + 4) 0) ⟨R₀, I₀⟩ (· = ⟨R₀, J1⟩) (3 * I₀ 0 + 1) :=
    loadIdx_spec (by omega) (z (b + 4) (by omega))
  set J2 := Function.update J1 (b + 7) (J1 0) with hJ2
  have h2 : Runs (loadIdx (b + 7) 0) ⟨R₀, J1⟩ (· = ⟨R₀, J2⟩) (3 * J1 0 + 1) :=
    loadIdx_spec (by omega) (by simp [hJ1, z (b + 7) (by omega)])
  set J3 := Function.update J2 (b + 7) (J2 (b + 7) + J2 1) with hJ3
  have h3 : Runs (addIdx (b + 7) 1 (b + 10) b) ⟨R₀, J2⟩ (· = ⟨R₀, J3⟩) (7 * J2 1 + 2) :=
    addIdx_spec (by omega) (by omega) (by omega) (by omega) (by omega)
      (by simp [hJ2, hJ1, z (b + 10) (by omega)]) (by simp [hJ2, hJ1, z b le_rfl])
  set J4 := Function.update J3 (b + 7) (J3 (b + 7) + 1) with hJ4
  have h4 : Runs (.op (.inc (b + 7))) ⟨R₀, J3⟩ (· = ⟨R₀, J4⟩) 1 := Spec.inc rfl le_rfl
  set J5 := Function.update J4 (b + 6) (J4 (b + 7)) with hJ5
  have h5 : Runs (loadIdx (b + 6) (b + 7)) ⟨R₀, J4⟩ (· = ⟨R₀, J5⟩) (3 * J4 (b + 7) + 1) :=
    loadIdx_spec (by omega) (by simp [hJ4, hJ3, hJ2, hJ1, z (b + 6) (by omega)])
  set J6 := Function.update J5 (b + 6) (J5 (b + 6) + 1) with hJ6
  have h6 : Runs (.op (.inc (b + 6))) ⟨R₀, J5⟩ (· = ⟨R₀, J6⟩) 1 := Spec.inc rfl le_rfl
  set J7 := Function.update J6 (b + 8) (J6 (b + 6)) with hJ7
  have h7 : Runs (loadIdx (b + 8) (b + 6)) ⟨R₀, J6⟩ (· = ⟨R₀, J7⟩) (3 * J6 (b + 6) + 1) :=
    loadIdx_spec (by omega) (by simp [hJ6, hJ5, hJ4, hJ3, hJ2, hJ1, z (b + 8) (by omega)])
  set J8 := Function.update J7 (b + 8) (J7 (b + 8) + 1) with hJ8
  have h8 : Runs (.op (.inc (b + 8))) ⟨R₀, J7⟩ (· = ⟨R₀, J8⟩) 1 := Spec.inc rfl le_rfl
  set R1 := Function.update R₀ (J8 (b + 7)) 1 with hR1
  have h9 : Runs (.op (.const (b + 7) 1)) ⟨R₀, J8⟩ (· = ⟨R1, J8⟩) 1 := Spec.const rfl le_rfl
  set R2 := Function.update R1 (J8 (b + 6)) α with hR2
  have h10 : Runs (.op (.const (b + 6) α)) ⟨R1, J8⟩ (· = ⟨R2, J8⟩) 1 := Spec.const rfl le_rfl
  have hall := Spec.seq_eq h1 (Spec.seq_eq h2 (Spec.seq_eq h3 (Spec.seq_eq h4 (Spec.seq_eq h5
    (Spec.seq_eq h6 (Spec.seq_eq h7 (Spec.seq_eq h8 (Spec.seq_eq h9 (Spec.seq_eq h10
    (Spec.skip (T := 0) (Q := (· = ⟨R2, J8⟩)) rfl))))))))))
  have v0 : I₀ 0 = n := rfl
  have v0' : I₀ 1 = q := rfl
  have v1 : J1 0 = n := by simp [hJ1, v0]
  have v2 : J2 1 = q := by simp [hJ2, hJ1, show (1 : ℕ) ≠ b + 7 by omega,
    show (1 : ℕ) ≠ b + 4 by omega, v0']
  have v4 : J4 (b + 7) = n + q + 1 := by simp [hJ4, hJ3, v2, hJ2, hJ1, v0, v0']
  have v6 : J6 (b + 6) = n + q + 2 := by simp [hJ6, hJ5, v4]
  have w7 : J8 (b + 7) = n + q + 1 := by simp [hJ8, hJ7, hJ6, hJ5, v4]
  have w6 : J8 (b + 6) = n + q + 2 := by simp [hJ8, hJ7, v6]
  refine (hall.mono_time ?_).mono_post ?_
  · rw [v0, v1, v2, v4, v6]; omega
  · rintro st' rfl
    refine ⟨by simp [hR2, hR1, w7, w6], fun k => ?_⟩
    show J8 k = _
    by_cases k4 : k = b + 4
    · subst k4; simp [hJ8, hJ7, hJ6, hJ5, hJ4, hJ3, hJ2, hJ1, v0]
    · by_cases k6 : k = b + 6
      · subst k6; simp [hJ8, hJ7, v6]
      · by_cases k7 : k = b + 7
        · subst k7; simp [hJ8, hJ7, hJ6, hJ5, v4]
        · by_cases k8 : k = b + 8
          · subst k8; simp [hJ8, hJ7, v6]
          · simp [hJ8, hJ7, hJ6, hJ5, hJ4, hJ3, hJ2, hJ1, Function.update_of_ne k4,
              Function.update_of_ne k6, Function.update_of_ne k7, Function.update_of_ne k8, k4,
              k6, k7, k8, hI₀]

theorem skipBlock_spec {b : ℕ} {str : ℕ → Bool} (hinf : ∀ k, ∃ j, k ≤ j ∧ str j = false)
    (l : List ℕ) (V : ℕ) (hV : ∀ v ∈ l, v ≤ V) (hL : l.length ≤ V) (pos : ℕ)
    (hs : Has str pos (encList (l.length :: l))) (st : St) {a o t : ℕ}
    (ha : st.I (b + 6) = a) (ho : st.I (b + 7) = o) (ht : st.I (b + 8) = t) (hat : a ≠ t)
    (hot : o ≠ t) (hao : a ≠ o) (hone : st.R o = 1) (hA : st.R a = tailVal str pos)
    (h9 : st.I (b + 9) = 0) (hz : st.I b = 0) (h12 : st.I (b + 12) = 0)
    (h13 : st.I (b + 13) = 0) :
    Runs (skipBlockS b) st (fun st' => st'.I = st.I ∧
      st'.R a = tailVal str (pos + (encList (l.length :: l)).length) ∧
      ∀ i, i ≠ a → i ≠ t → st'.R i = st.R i)
      ((8 * V + 10) + ((V * (11 * V + 12 + 2) + 1) + 0)) := by
  set L := l.length with hLdef
  rw [encList_cons] at hs
  obtain ⟨hsL, hsl⟩ := Has.append.1 hs
  rw [length_encNum] at hsl
  have s1 := readNum_spec hinf hsL (st := st) (rdN_ok b (b + 12) (by omega))
    (by rw [ha, ht]; exact hat) (by rw [ho, ht]; exact hot) (by rw [ha, ho]; exact hao)
    (by rw [ho]; exact hone) (by rw [ha]; exact hA) h9 hz
  refine (Spec.seq (T₂ := (L * (11 * V + 12 + 2) + 1) + 0) s1 fun st₁ hst₁ => ?_).mono_time (by
    have : L * (11 * V + 12 + 2) ≤ V * (11 * V + 12 + 2) := Nat.mul_le_mul_right _ hL
    omega)
  obtain ⟨hI₁, hA₁, hR₁⟩ := hst₁
  rw [ha] at hA₁ hR₁
  rw [ht] at hR₁
  simp only [h12, Nat.zero_add] at hI₁
  -- the inner loop
  let Inv : ℕ → St → Prop := fun u st' => st'.I = Function.update st.I (b + 12) (L - u) ∧
    st'.R a = tailVal str (pos + L + 1 + (encList (l.take u)).length) ∧
    ∀ i, i ≠ a → i ≠ t → st'.R i = st.R i
  have hloop := Spec.loop (s := Stmt.seqs [rdN b (b + 13), clearIdx (b + 13) b,
    .op (.dec (b + 12))]) (c := .idxEq (b + 12) b) (H := fun _ _ => False)
    (T := 11 * V + 12) (st := st₁) Inv L ?_ ?_ ?_ ?_
  · refine (Spec.seq (T₂ := 0) hloop fun st₂ hst₂ => Spec.skip ?_)
    obtain ⟨hI₂, hA₂, hR₂⟩ := hst₂
    refine ⟨by rw [hI₂]; simp [h12], ?_, hR₂⟩
    rw [hA₂, List.take_of_length_le le_rfl, encList_cons, List.length_append, length_encNum]
    congr 1
    omega
  · rintro st' ⟨hI', -⟩
    simp [hI', Function.update_of_ne (show b ≠ b + 12 by omega), hz]
  · rintro u hu st' ⟨hI', -⟩
    simp [hI', Function.update_of_ne (show b ≠ b + 12 by omega), hz]
    omega
  · rintro u hu st' ⟨hI', hA', hR'⟩
    have hsplit := has_split (rest := []) u hu (by simpa using hsl)
    have hvle : l[u] ≤ V := hV _ (List.getElem_mem hu)
    have e6 : st'.I (b + 6) = a := by simp [hI', ha]
    have e7 : st'.I (b + 7) = o := by simp [hI', ho]
    have e8 : st'.I (b + 8) = t := by simp [hI', ht]
    have s2 := readNum_spec hinf (pos := pos + L + 1 + (encList (l.take u)).length) (by
        simpa [Nat.add_assoc] using hsplit) (st := st') (rdN_ok b (b + 13) (by omega))
      (by rw [e6, e8]; exact hat) (by rw [e7, e8]; exact hot) (by rw [e6, e7]; exact hao)
      (by rw [e7, hR' o hao.symm hot]; exact hone) (by rw [e6]; exact hA')
      (by simp [hI', h9])
      (by simp [hI', hz])
    refine (Spec.seq s2 fun st₃ hst₃ => ?_).mono_time (by
      show 8 * l[u] + 10 + (3 * (0 + l[u]) + 1 + (1 + 0)) ≤ 11 * V + 12
      omega)
    obtain ⟨hI₃, hA₃, hR₃⟩ := hst₃
    rw [e6] at hA₃
    rw [e6, e8] at hR₃
    have e13 : st₃.I (b + 13) = 0 + l[u] := by
      rw [hI₃, Function.update_self, hI', Function.update_of_ne (by omega), h13]
    have s3 := clearIdx_spec (st := st₃) (k := b + 13) (z := b) (by omega)
      (by rw [hI₃, Function.update_of_ne (by omega), hI', Function.update_of_ne (by omega), hz])
    rw [e13] at s3
    refine Spec.seq_eq s3 (Spec.seq_op rfl (Spec.skip ?_))
    refine ⟨?_, ?_, fun i hi1 hi2 => ?_⟩
    · funext k
      simp only [Function.update_apply]
      rw [hI₃, hI']
      by_cases k12 : k = b + 12
      · subst k12; simp; omega
      · by_cases k13 : k = b + 13
        · subst k13; simp [h13]
        · simp [k12, k13]
    · show st₃.R a = _
      rw [hA₃, encList_take_succ l u hu, List.length_append, length_encNum]
      congr 1
      omega
    · show st₃.R i = _
      rw [hR₃ i hi1 hi2, hR' i hi1 hi2]
  · refine ⟨by rw [hI₁]; simp, by simpa using hA₁, hR₁⟩

/-- The position of the block `m` in the stream. -/
theorem blockOff_eq_sum (blocks : ℕ → List Bool) (m : ℕ) :
    blockOff blocks m = ∑ j ∈ Finset.range m, (blocks j).length := by
  induction m with
  | zero => simp [blockOff]
  | succ m ih => rw [blockOff_succ, ih, Finset.sum_range_succ]

theorem skip_spec {b n : ℕ} {str : ℕ → Bool} (hinf : ∀ k, ∃ j, k ≤ j ∧ str j = false)
    (bl : ℕ → List ℕ) (V : ℕ) (hV : ∀ m < n, ∀ v ∈ bl m, v ≤ V)
    (hL : ∀ m < n, (bl m).length ≤ V)
    (hs : ∀ m, Has str (blockOff (fun m => encList ((bl m).length :: bl m)) m)
      (encList ((bl m).length :: bl m)))
    (st : St) {a o t : ℕ}
    (ha : st.I (b + 6) = a) (ho : st.I (b + 7) = o) (ht : st.I (b + 8) = t) (hat : a ≠ t)
    (hot : o ≠ t) (hao : a ≠ o) (hone : st.R o = 1)
    (hA : st.R a = tailVal str 0) (h4 : st.I (b + 4) = n)
    (h9 : st.I (b + 9) = 0) (hz : st.I b = 0) (h11 : st.I (b + 11) = 0)
    (h12 : st.I (b + 12) = 0) (h13 : st.I (b + 13) = 0) :
    Runs (skipS b) st (fun st' => st'.I = Function.update st.I (b + 11) n ∧
      st'.R a = tailVal str (blockOff (fun m => encList ((bl m).length :: bl m)) n) ∧
      ∀ i, i ≠ a → i ≠ t → st'.R i = st.R i)
      (n * ((8 * V + 10) + ((V * (11 * V + 12 + 2) + 1) + 0) + 1 + 2) + 1) := by
  set blocks : ℕ → List Bool := fun m => encList ((bl m).length :: bl m) with hblocks
  let Inv : ℕ → St → Prop := fun m st' => st'.I = Function.update st.I (b + 11) m ∧
    st'.R a = tailVal str (blockOff blocks m) ∧ ∀ i, i ≠ a → i ≠ t → st'.R i = st.R i
  refine Spec.loop Inv n ?_ ?_ ?_ ?_
  · rintro st' ⟨hI', -⟩
    simp [hI', Function.update_of_ne (show b + 4 ≠ b + 11 by omega), h4]
  · rintro m hm st' ⟨hI', -⟩
    simp [hI', Function.update_of_ne (show b + 4 ≠ b + 11 by omega), h4]
    omega
  · rintro m hm st' ⟨hI', hA', hR'⟩
    have hupd : ∀ k, k ≠ b + 11 → st'.I k = st.I k := fun k hk => by
      rw [hI', Function.update_of_ne hk]
    have s1 := skipBlock_spec hinf (bl m) V (hV m hm) (hL m hm) (blockOff blocks m) (hs m) st'
      (by rw [hupd (b + 6) (by omega), ha]) (by rw [hupd (b + 7) (by omega), ho])
      (by rw [hupd (b + 8) (by omega), ht]) hat hot hao (by rw [hR' o hao.symm hot]; exact hone)
      hA' (by rw [hupd (b + 9) (by omega), h9]) (by rw [hupd b (by omega), hz])
      (by rw [hupd (b + 12) (by omega), h12]) (by rw [hupd (b + 13) (by omega), h13])
    refine Spec.seq s1 fun st₁ hst₁ => ?_
    obtain ⟨hI₁, hA₁, hR₁⟩ := hst₁
    refine Spec.inc ⟨?_, ?_, fun i hi1 hi2 => ?_⟩ le_rfl
    · rw [hI₁, hI']
      funext k
      by_cases k11 : k = b + 11
      · subst k11; simp
      · simp [Function.update_of_ne k11]
    · show st₁.R a = _
      rw [hA₁, blockOff_succ]
    · show st₁.R i = _
      rw [hR₁ i hi1 hi2, hR' i hi1 hi2]
  · refine ⟨?_, by simpa [blockOff] using hA, fun i _ _ => rfl⟩
    funext k
    by_cases k11 : k = b + 11
    · subst k11; simp [h11]
    · simp [Function.update_of_ne k11]

theorem rdN_step {b k : ℕ} {str : ℕ → Bool} (hinf : ∀ k, ∃ j, k ≤ j ∧ str j = false)
    (hk : b + 10 ≤ k) {a o t : ℕ} (st : St) (ha : st.I (b + 6) = a) (ho : st.I (b + 7) = o)
    (ht : st.I (b + 8) = t) (hat : a ≠ t) (hot : o ≠ t) (hao : a ≠ o) (hone : st.R o = 1)
    (h9 : st.I (b + 9) = 0) (hz : st.I b = 0) {pos v : ℕ} {rest : List ℕ}
    (hA : st.R a = tailVal str pos) (hs : Has str pos (encList (v :: rest))) :
    Runs (rdN b k) st (fun st' => st'.I = Function.update st.I k (st.I k + v) ∧
      st'.R a = tailVal str (pos + v + 1) ∧ Has str (pos + v + 1) (encList rest) ∧
      ∀ i, i ≠ a → i ≠ t → st'.R i = st.R i) (8 * v + 10) := by
  rw [encList_cons] at hs
  obtain ⟨h1, h2⟩ := Has.append.1 hs
  have := readNum_spec hinf h1 (st := st) (rdN_ok b k hk) (by rw [ha, ht]; exact hat)
    (by rw [ho, ht]; exact hot) (by rw [ha, ho]; exact hao) (by rw [ho]; exact hone)
    (by rw [ha]; exact hA) h9 hz
  refine this.mono_post ?_
  rintro st' ⟨hI, hA', hR'⟩
  rw [ha] at hA' hR'
  rw [ht] at hR'
  exact ⟨hI, hA', by simpa [Nat.add_assoc] using h2, hR'⟩

theorem streamOf_ok (bl : ℕ → List ℕ) :
    ∀ k, ∃ j, k ≤ j ∧ streamOf (fun m => encList ((bl m).length :: bl m)) j = false := by
  refine streamOf_inf _ (fun m => by simp [encNum]) (fun m => by simp [encNum])

theorem header_spec {b : ℕ} {str : ℕ → Bool} (hinf : ∀ k, ∃ j, k ≤ j ∧ str j = false)
    {a o t : ℕ} (hat : a ≠ t) (hot : o ≠ t) (hao : a ≠ o) (st : St) (ha : st.I (b + 6) = a)
    (ho : st.I (b + 7) = o) (ht : st.I (b + 8) = t) (hone : st.R o = 1)
    (h9 : st.I (b + 9) = 0) (hz : st.I b = 0)
    (hzero : ∀ k, b + 13 ≤ k → k ≤ b + 18 → st.I k = 0)
    {pos L Hm s₁ s₂ N K : ℕ} {rest : List ℕ} (hA : st.R a = tailVal str pos)
    (hs : Has str pos (encList (L :: Hm :: s₁ :: s₂ :: N :: K :: rest))) :
    Runs (headerS b) st (fun st' => st'.I = Function.update (Function.update (Function.update
      (Function.update (Function.update st.I (b + 14) Hm) (b + 15) s₁) (b + 16) s₂) (b + 17) N)
      (b + 18) K ∧ ∃ pos', st'.R a = tailVal str pos' ∧ Has str pos' (encList rest) ∧
      ∀ i, i ≠ a → i ≠ t → st'.R i = st.R i)
      ((8 * L + 10) + ((3 * L + 1) + ((8 * Hm + 10) + ((8 * s₁ + 10) + ((8 * s₂ + 10) +
        ((8 * N + 10) + ((8 * K + 10) + 0))))))) := by
  -- the frame of the registers used by `rdN`
  have hfr : ∀ (st' : St) (k v : ℕ), b + 10 ≤ k → st'.I = Function.update st.I k v →
      st'.I (b + 6) = a ∧ st'.I (b + 7) = o ∧ st'.I (b + 8) = t ∧ st'.I (b + 9) = 0 ∧
      st'.I b = 0 := by
    intro st' k v hk h
    rw [h]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [Function.update_of_ne (show b + 6 ≠ k by omega), Function.update_of_ne (show b + 7 ≠ k by omega), Function.update_of_ne (show b + 8 ≠ k by omega), Function.update_of_ne (show b + 9 ≠ k by omega), Function.update_of_ne (show b ≠ k by omega), ha, ho, ht, h9, hz]
  have s1 := rdN_step hinf (k := b + 13) (by omega) st ha ho ht hat hot hao hone h9 hz hA hs
  refine Spec.seq s1 ?_
  rintro ⟨R₁, I₁⟩ ⟨hI₁, hA₁, hs₁, hR₁⟩
  simp only at hI₁ hA₁ hR₁
  rw [hzero (b + 13) le_rfl (by omega), Nat.zero_add] at hI₁
  subst hI₁
  have s2 := clearIdx_spec (st := ⟨R₁, Function.update st.I (b + 13) L⟩) (k := b + 13) (z := b)
    (by omega) (by simp [hz])
  simp only [Function.update_self] at s2
  refine Spec.seq_eq s2 ?_
  have e : Function.update (Function.update st.I (b + 13) L) (b + 13) 0 = st.I := by
    rw [Function.update_idem, ← hzero (b + 13) le_rfl (by omega), Function.update_eq_self]
  rw [e]
  have hone₁ : R₁ o = 1 := by rw [hR₁ o hao.symm hot, hone]
  have s3 := rdN_step hinf (k := b + 14) (by omega) ⟨R₁, st.I⟩ ha ho ht hat hot hao hone₁ h9 hz
    hA₁ hs₁
  refine Spec.seq s3 ?_
  rintro ⟨R₃, I₃⟩ ⟨hI₃, hA₃, hs₃, hR₃⟩
  simp only at hI₃ hA₃ hR₃
  rw [hzero (b + 14) (by omega) (by omega), Nat.zero_add] at hI₃
  obtain ⟨g6, g7, g8, g9, gz⟩ := hfr ⟨R₃, I₃⟩ (b + 14) Hm (by omega) hI₃
  simp only at g6 g7 g8 g9 gz
  have s4 := rdN_step hinf (k := b + 15) (by omega) ⟨R₃, I₃⟩ g6 g7 g8 hat hot hao
    (by simp only; rw [hR₃ o hao.symm hot, hone₁]) g9 gz hA₃ hs₃
  refine Spec.seq s4 ?_
  rintro ⟨R₄, I₄⟩ ⟨hI₄, hA₄, hs₄, hR₄⟩
  simp only at hI₄ hA₄ hR₄
  have e15 : I₃ (b + 15) = 0 := by
    rw [hI₃, Function.update_of_ne (by omega), hzero (b + 15) (by omega) (by omega)]
  rw [e15, Nat.zero_add] at hI₄
  have hI₄' : I₄ = Function.update st.I (b + 15) s₁ ∨ True := Or.inr trivial
  clear hI₄'
  have g4 : I₄ (b + 6) = a ∧ I₄ (b + 7) = o ∧ I₄ (b + 8) = t ∧ I₄ (b + 9) = 0 ∧ I₄ b = 0 := by
    rw [hI₄]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [g6, g7, g8, g9, gz]
  have s5 := rdN_step hinf (k := b + 16) (by omega) ⟨R₄, I₄⟩ g4.1 g4.2.1 g4.2.2.1 hat hot hao
    (by simp only; rw [hR₄ o hao.symm hot, hR₃ o hao.symm hot, hone₁]) g4.2.2.2.1 g4.2.2.2.2
    hA₄ hs₄
  refine Spec.seq s5 ?_
  rintro ⟨R₅, I₅⟩ ⟨hI₅, hA₅, hs₅, hR₅⟩
  simp only at hI₅ hA₅ hR₅
  have e16 : I₄ (b + 16) = 0 := by
    rw [hI₄, Function.update_of_ne (by omega), hI₃, Function.update_of_ne (by omega),
      hzero (b + 16) (by omega) (by omega)]
  rw [e16, Nat.zero_add] at hI₅
  have g5 : I₅ (b + 6) = a ∧ I₅ (b + 7) = o ∧ I₅ (b + 8) = t ∧ I₅ (b + 9) = 0 ∧ I₅ b = 0 := by
    rw [hI₅]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [g4]
  have s6 := rdN_step hinf (k := b + 17) (by omega) ⟨R₅, I₅⟩ g5.1 g5.2.1 g5.2.2.1 hat hot hao
    (by simp only; rw [hR₅ o hao.symm hot, hR₄ o hao.symm hot, hR₃ o hao.symm hot, hone₁])
    g5.2.2.2.1 g5.2.2.2.2 hA₅ hs₅
  refine Spec.seq s6 ?_
  rintro ⟨R₆, I₆⟩ ⟨hI₆, hA₆, hs₆, hR₆⟩
  simp only at hI₆ hA₆ hR₆
  have e17 : I₅ (b + 17) = 0 := by
    rw [hI₅, Function.update_of_ne (by omega), hI₄, Function.update_of_ne (by omega), hI₃,
      Function.update_of_ne (by omega), hzero (b + 17) (by omega) (by omega)]
  rw [e17, Nat.zero_add] at hI₆
  have g6' : I₆ (b + 6) = a ∧ I₆ (b + 7) = o ∧ I₆ (b + 8) = t ∧ I₆ (b + 9) = 0 ∧ I₆ b = 0 := by
    rw [hI₆]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [g5]
  have s7 := rdN_step hinf (k := b + 18) (by omega) ⟨R₆, I₆⟩ g6'.1 g6'.2.1 g6'.2.2.1 hat hot hao
    (by simp only; rw [hR₆ o hao.symm hot, hR₅ o hao.symm hot, hR₄ o hao.symm hot,
      hR₃ o hao.symm hot, hone₁]) g6'.2.2.2.1 g6'.2.2.2.2 hA₆ hs₆
  refine Spec.seq s7 ?_
  rintro ⟨R₇, I₇⟩ ⟨hI₇, hA₇, hs₇, hR₇⟩
  simp only at hI₇ hA₇ hR₇
  have e18 : I₆ (b + 18) = 0 := by
    rw [hI₆, Function.update_of_ne (by omega), hI₅, Function.update_of_ne (by omega), hI₄,
      Function.update_of_ne (by omega), hI₃, Function.update_of_ne (by omega),
      hzero (b + 18) (by omega) le_rfl]
  rw [e18, Nat.zero_add] at hI₇
  refine Spec.skip ⟨by rw [hI₇, hI₆, hI₅, hI₄, hI₃], _, hA₇, hs₇, fun i hi1 hi2 => ?_⟩
  show R₇ i = st.R i
  rw [hR₇ i hi1 hi2, hR₆ i hi1 hi2, hR₅ i hi1 hi2, hR₄ i hi1 hi2, hR₃ i hi1 hi2,
    hR₁ i hi1 hi2]

theorem reloc_spec {b n q Hm : ℕ} (hHm : n + q + 4 ≤ Hm) (st : St)
    (h6 : st.I (b + 6) = n + q + 2) (h7 : st.I (b + 7) = n + q + 1)
    (h8 : st.I (b + 8) = n + q + 3) (h14 : st.I (b + 14) = Hm) (hz : st.I b = 0)
    (h10 : st.I (b + 10) = 0) (h19 : st.I (b + 19) = 0) (h23 : st.I (b + 23) = 0)
    (h24 : st.I (b + 24) = 0) (h25 : st.I (b + 25) = 0) (h26 : st.I (b + 26) = 0) :
    Runs (relocS b) st (fun st' => st'.R = copyR st.R 0 Hm (n + q + 4) ∧
      st'.I = Function.update (Function.update (Function.update (Function.update
        (Function.update st.I (b + 26) (n + q + 4)) (b + 6) (Hm + n + q + 2)) (b + 7)
        (Hm + n + q + 1)) (b + 8) (Hm + n + q + 3)) (b + 19) Hm)
      ((3 * (n + q + 3) + 1) + (1 + ((15 * (n + q + 4) + 6 * Hm + 6) + ((7 * Hm + 2) +
        ((7 * Hm + 2) + ((7 * Hm + 2) + ((3 * Hm + 1) + 0))))))) := by
  obtain ⟨R₀, I₀⟩ := st
  simp only at h6 h7 h8 h14 hz h10 h19 h23 h24 h25 h26 ⊢
  have s1 := loadIdx_spec (st := ⟨R₀, I₀⟩) (k := b + 26) (a := b + 8) (by omega) h26
  simp only [h8] at s1
  refine Spec.seq_eq s1 ?_
  set J1 := Function.update I₀ (b + 26) (n + q + 3) with hJ1
  refine Spec.seq_op (st' := ⟨R₀, Function.update J1 (b + 26) (n + q + 4)⟩) (by simp [hJ1]) ?_
  set J2 := Function.update J1 (b + 26) (n + q + 4) with hJ2
  have g : ∀ k, k ≠ b + 26 → J2 k = I₀ k := fun k hk => by
    simp [hJ2, hJ1, Function.update_of_ne hk]
  have s3 := copyRange_spec (st := ⟨R₀, J2⟩) (src := b) (dst := b + 14) (len := b + 26)
    (p := b + 23) (q := b + 24) (c := b + 25) (z := b) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) ⟨by omega, by omega, by omega⟩
    ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega⟩
    (by simp only; rw [g _ (by omega), h23]) (by simp only; rw [g _ (by omega), h24])
    (by simp only; rw [g _ (by omega), h25]) (by simp only; rw [g _ (by omega), hz])
    (by simp only; rw [g _ (by omega), g _ (by omega), hz, h14, show J2 (b + 26) = n + q + 4 by
      simp [hJ2]]; omega)
  simp only [g b (by omega), g (b + 14) (by omega), hz, h14,
    show J2 (b + 26) = n + q + 4 by simp [hJ2]] at s3
  refine Spec.seq_eq (s3.mono_time (T' := 15 * (n + q + 4) + 6 * Hm + 6) (by omega)) ?_
  set R₃ := copyR R₀ 0 Hm (n + q + 4) with hR₃
  have s4 := addIdx_spec (st := ⟨R₃, J2⟩) (k := b + 6) (a := b + 14) (cnt := b + 10) (z := b)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by simp only; rw [g _ (by omega), h10]) (by simp only; rw [g _ (by omega), hz])
  simp only [g (b + 6) (by omega), g (b + 14) (by omega), h6, h14] at s4
  refine Spec.seq_eq s4 ?_
  set J4 := Function.update J2 (b + 6) (n + q + 2 + Hm) with hJ4
  have g4 : ∀ k, k ≠ b + 26 → k ≠ b + 6 → J4 k = I₀ k := fun k hk hk' => by
    simp [hJ4, Function.update_of_ne hk', g k hk]
  have s5 := addIdx_spec (st := ⟨R₃, J4⟩) (k := b + 7) (a := b + 14) (cnt := b + 10) (z := b)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by simp only; rw [g4 _ (by omega) (by omega), h10])
    (by simp only; rw [g4 _ (by omega) (by omega), hz])
  simp only [g4 (b + 7) (by omega) (by omega), g4 (b + 14) (by omega) (by omega), h7, h14] at s5
  refine Spec.seq_eq s5 ?_
  set J5 := Function.update J4 (b + 7) (n + q + 1 + Hm) with hJ5
  have g5 : ∀ k, k ≠ b + 26 → k ≠ b + 6 → k ≠ b + 7 → J5 k = I₀ k := fun k hk hk' hk'' => by
    simp [hJ5, Function.update_of_ne hk'', g4 k hk hk']
  have s6 := addIdx_spec (st := ⟨R₃, J5⟩) (k := b + 8) (a := b + 14) (cnt := b + 10) (z := b)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by simp only; rw [g5 _ (by omega) (by omega) (by omega), h10])
    (by simp only; rw [g5 _ (by omega) (by omega) (by omega), hz])
  simp only [g5 (b + 8) (by omega) (by omega) (by omega),
    g5 (b + 14) (by omega) (by omega) (by omega), h8, h14] at s6
  refine Spec.seq_eq s6 ?_
  set J6 := Function.update J5 (b + 8) (n + q + 3 + Hm) with hJ6
  have s7 := loadIdx_spec (st := ⟨R₃, J6⟩) (k := b + 19) (a := b + 14) (by omega)
    (by simp [hJ6, hJ5, hJ4, g (b + 19) (by omega), h19])
  have e14 : J6 (b + 14) = Hm := by simp [hJ6, hJ5, hJ4, g (b + 14) (by omega), h14]
  simp only [e14] at s7
  refine Spec.seq_eq s7 (Spec.skip (T := 0) ⟨rfl, ?_⟩)
  show Function.update J6 (b + 19) Hm = _
  simp only [hJ6, hJ5, hJ4, hJ2, hJ1, Function.update_idem]
  congr 1
  rw [show n + q + 3 + Hm = Hm + n + q + 3 by omega, show n + q + 1 + Hm = Hm + n + q + 1 by omega,
    show n + q + 2 + Hm = Hm + n + q + 2 by omega]

/-- The running time of the machine, phase by phase. -/
def gTotal (M : Machine) (b n q Hm s₁ s₂ N K T V L P mk : ℕ) : ℕ :=
  20 * (n + q + 2) + ((n * ((8 * V + 10) + ((V * (11 * V + 12 + 2) + 1) + 0) + 1 + 2) + 1) +
    (((8 * L + 10) + ((3 * L + 1) + ((8 * Hm + 10) + ((8 * s₁ + 10) + ((8 * s₂ + 10) +
      ((8 * N + 10) + ((8 * K + 10) + 0))))))) +
    (((3 * (n + q + 3) + 1) + (1 + ((15 * (n + q + 4) + 6 * Hm + 6) + ((7 * Hm + 2) +
      ((7 * Hm + 2) + ((7 * Hm + 2) + ((3 * Hm + 1) + 0))))))) +
    ((8 * mk + 10) + ((P * (leafTime M b n q Hm s₁ s₂ N T + 22 + 2) + 1) + (2 + 0))))))

/-- **The machine at one input size.** -/
theorem gmain_spec (M : Machine) {n q : ℕ} (x : Fin n → ℝ) (S : Fin q → ℝ) (bl : ℕ → List ℕ)
    {Hm s₁ s₂ N K T V : ℕ} (LV : List (List ℕ))
    (hbl : bl n = [Hm, s₁, s₂, N, K] ++ leafNums LV) (hN : N = n + s₁ + s₂)
    (hHm : N + T + q + 4 ≤ Hm)
    (hℓ : ∀ ℓ ∈ LV, ℓ.length = N) (hpos : ∀ ℓ ∈ LV, ∀ k ∈ ℓ, k ≤ n + q + 1)
    (hhalt : ∀ ℓ ∈ LV, ∃ o, M.run T (initConfig [n, s₁, s₂] (vecReg (gather x S N ℓ))) = some o)
    (hV : ∀ m < n, ∀ v ∈ bl m, v ≤ V) (hL : ∀ m < n, (bl m).length ≤ V) :
    Halts (gStmt M (tailVal (streamOf fun m => encList ((bl m).length :: bl m)) 0))
      (St.init [n, q] (vecReg (Fin.append x S)))
      (fun _ r => r = some (decide (K ≤ accCount M T n s₁ s₂ N x S LV)))
      (gTotal M (idxBd M + 3) n q Hm s₁ s₂ N K T V (bl n).length LV.length (markAt LV 0)) := by
  set b := idxBd M + 3 with hbdef
  have hb3 : 3 ≤ b := by omega
  set blocks : ℕ → List Bool := fun m => encList ((bl m).length :: bl m) with hblocks
  set str := streamOf blocks with hstr
  have hinf : ∀ k, ∃ j, k ≤ j ∧ str j = false := streamOf_ok bl
  have hhas : ∀ m, Has str (blockOff blocks m) (blocks m) :=
    streamOf_has blocks (fun m => by simp [hblocks, encNum])
  set R₀ := vecReg (Fin.append x S) with hR₀
  -- the addresses of the stream registers before the relocation
  set a := n + q + 2
  set o := n + q + 1
  set t := n + q + 3
  -- phase 0
  set I₁ : ℕ → ℕ := fun k => if k = b + 4 then n else if k = b + 6 then n + q + 2 else
    if k = b + 7 then n + q + 1 else if k = b + 8 then n + q + 3 else [n, q].getD k 0 with hI₁
  set R₁ := Function.update (Function.update R₀ (n + q + 1) 1) (n + q + 2)
    (tailVal str 0) with hR₁
  have p0 : Runs (initS b (tailVal str 0)) ⟨R₀, fun k => [n, q].getD k 0⟩ (· = ⟨R₁, I₁⟩)
      (20 * (n + q + 2)) := by
    refine (init_spec hb3 _ R₀).mono_post ?_
    rintro ⟨R', I'⟩ ⟨hR', hI'⟩
    simp only at hR' hI'
    rw [hR']
    congr 1
    funext k
    rw [hI' k]
  have hI₁hi : ∀ k, b ≤ k → k ≠ b + 4 → k ≠ b + 6 → k ≠ b + 7 → k ≠ b + 8 → I₁ k = 0 := by
    intro k hk h4 h6 h7 h8
    simp only [hI₁, h4, h6, h7, h8, if_false]
    rw [List.getD_eq_default _ _ (by simp; omega)]
  have hI₁lo : ∀ k < b, I₁ k ≤ Hm := by
    intro k hk
    simp only [hI₁, show k ≠ b + 4 by omega, show k ≠ b + 6 by omega, show k ≠ b + 7 by omega,
      show k ≠ b + 8 by omega, if_false]
    rcases Nat.lt_or_ge k 2 with h | h
    · interval_cases k <;> simp <;> omega
    · rw [List.getD_eq_default _ _ (by simp; omega)]; omega
  have hR₁o : R₁ o = 1 := by simp [hR₁, o]
  have hR₁a : R₁ a = tailVal str 0 := by simp [hR₁, a]
  have hR₁lo : ∀ i ≤ n + q + 1, R₁ i = srcVal x S i := by
    intro i hi
    by_cases hio : i = n + q + 1
    · subst hio; rw [hR₁o, srcVal_one]
    · rw [hR₁, Function.update_of_ne (by omega), Function.update_of_ne hio]
      unfold srcVal
      by_cases hi' : i < n + q
      · rw [if_pos hi']
      · rw [if_neg hi', if_neg (by omega), hR₀]
        simp [vecReg, show ¬ i < n + q by omega]
  have hI₁v6 : I₁ (b + 6) = n + q + 2 := by simp [hI₁]
  have hI₁v7 : I₁ (b + 7) = n + q + 1 := by simp [hI₁]
  have hI₁v8 : I₁ (b + 8) = n + q + 3 := by simp [hI₁]
  have hI₁v4 : I₁ (b + 4) = n := by simp [hI₁]
  have hI₁z : ∀ k, b ≤ k → k ≠ b + 4 → k ≠ b + 6 → k ≠ b + 7 → k ≠ b + 8 → I₁ k = 0 := hI₁hi
  have hat : n + q + 2 ≠ n + q + 3 := by omega
  have hot : n + q + 1 ≠ n + q + 3 := by omega
  have hao : n + q + 2 ≠ n + q + 1 := by omega
  show Spec (Stmt.seq (initS b _) (Stmt.seq (skipS b) (Stmt.seq (headerS b) (Stmt.seq (relocS b)
    (Stmt.seq (rdN b (b + 20)) (Stmt.seq (leavesS M b) (Stmt.seq (.ite (.idxEq (b + 18) b)
    (.halt true) (.halt false)) .skip))))))) _ _ _ _
  unfold gTotal
  -- phase 0
  refine Spec.seq_eq (Spec.of_runs p0) ?_
  -- phase 1: skip the blocks of the sizes `< n`
  have p1 := skip_spec hinf bl V hV hL hhas ⟨R₁, I₁⟩ (a := n + q + 2) (o := n + q + 1)
    (t := n + q + 3) hI₁v6 hI₁v7 hI₁v8 hat hot hao hR₁o hR₁a hI₁v4
    (hI₁z _ (by omega) (by omega) (by omega) (by omega) (by omega))
    (hI₁z _ le_rfl (by omega) (by omega) (by omega) (by omega))
    (hI₁z _ (by omega) (by omega) (by omega) (by omega) (by omega))
    (hI₁z _ (by omega) (by omega) (by omega) (by omega) (by omega))
    (hI₁z _ (by omega) (by omega) (by omega) (by omega) (by omega))
  refine Spec.seq (Spec.of_runs p1) ?_
  rintro ⟨R₂, I₂⟩ ⟨hI₂, hA₂, hR₂⟩
  simp only at hI₂ hA₂ hR₂
  subst hI₂
  -- phase 2: the header of the block of size `n`
  have hsn : Has str (blockOff blocks n) (encList ((bl n).length :: Hm :: s₁ :: s₂ :: N :: K ::
      leafNums LV)) := by
    have h := hhas n
    have e : blocks n = encNum (bl n).length ++ encList (bl n) := rfl
    rw [e] at h
    rw [encList_cons]
    have e2 : encList (bl n) = encList (Hm :: s₁ :: s₂ :: N :: K :: leafNums LV) := by
      rw [hbl]; rfl
    rw [← e2]
    exact h
  have p2 := header_spec (b := b) hinf hat hot hao ⟨R₂, Function.update I₁ (b + 11) n⟩
    (by simp [hI₁v6]) (by simp [hI₁v7]) (by simp [hI₁v8])
    (by simp only; rw [hR₂ _ hao.symm hot, hR₁o])
    (by simp [hI₁z (b + 9) (by omega) (by omega) (by omega) (by omega) (by omega)])
    (by simp [hI₁z b le_rfl (by omega) (by omega) (by omega) (by omega)])
    (fun k hk1 hk2 => by
      simp [Function.update_of_ne (show k ≠ b + 11 by omega),
        hI₁z k (by omega) (by omega) (by omega) (by omega) (by omega)])
    hA₂ hsn
  refine Spec.seq (Spec.of_runs p2) ?_
  rintro ⟨R₃, I₃⟩ ⟨hI₃, pos₃, hA₃, hs₃, hR₃⟩
  simp only at hI₃ hA₃ hR₃
  subst hI₃
  -- phase 3: relocation
  have hJ : ∀ k, b ≤ k → k ≠ b + 4 → k ≠ b + 6 → k ≠ b + 7 → k ≠ b + 8 → k ≠ b + 11 →
      k ≠ b + 14 → k ≠ b + 15 → k ≠ b + 16 → k ≠ b + 17 → k ≠ b + 18 →
      Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update I₁ (b + 11) n) (b + 14) Hm) (b + 15) s₁) (b + 16) s₂) (b + 17) N)
        (b + 18) K k = 0 := by
    intro k hk h4 h6 h7 h8 h11 h14 h15 h16 h17 h18
    simp [Function.update_of_ne h11, Function.update_of_ne h14, Function.update_of_ne h15,
      Function.update_of_ne h16, Function.update_of_ne h17, Function.update_of_ne h18,
      hI₁z k hk h4 h6 h7 h8]
  set I₃ := Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update I₁ (b + 11) n) (b + 14) Hm) (b + 15) s₁) (b + 16) s₂) (b + 17) N)
    (b + 18) K with hI₃def
  have hJ0 : ∀ k, b ≤ k → b + 18 < k → I₃ k = 0 := fun k hk hk' =>
    hJ k hk (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
  have p3 := reloc_spec (b := b) (n := n) (q := q) (Hm := Hm) (by omega) ⟨R₃, I₃⟩
    (by simp [hI₃def, hI₁v6]) (by simp [hI₃def, hI₁v7]) (by simp [hI₃def, hI₁v8])
    (by simp [hI₃def])
    (hJ b le_rfl (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega))
    (hJ (b + 10) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega))
    (hJ0 (b + 19) (by omega) (by omega)) (hJ0 (b + 23) (by omega) (by omega))
    (hJ0 (b + 24) (by omega) (by omega)) (hJ0 (b + 25) (by omega) (by omega))
    (hJ0 (b + 26) (by omega) (by omega))
  refine Spec.seq (Spec.of_runs p3) ?_
  rintro ⟨R₄, I₄⟩ ⟨hR₄, hI₄⟩
  simp only at hR₄ hI₄
  subst hR₄ hI₄
  -- phase 4: the first leaf marker
  set I₄ := Function.update (Function.update (Function.update (Function.update
    (Function.update I₃ (b + 26) (n + q + 4)) (b + 6) (Hm + n + q + 2)) (b + 7)
    (Hm + n + q + 1)) (b + 8) (Hm + n + q + 3)) (b + 19) Hm with hI₄def
  have hR₃src : ∀ i ≤ n + q + 1, R₃ i = srcVal x S i := fun i hi => by
    rw [hR₃ i (by omega) (by omega), hR₂ i (by omega) (by omega), hR₁lo i hi]
  have hcopy : ∀ i < n + q + 4, copyR R₃ 0 Hm (n + q + 4) (Hm + i) = R₃ i := fun i hi => by
    rw [copyR_of_mem ⟨by omega, by omega⟩]
    congr 1
    omega
  have hs₄ : Has str pos₃ (encList (markAt LV 0 :: restAt LV 0)) := by
    have := leafNums_drop LV 0
    rw [List.drop_zero] at this
    rwa [← this]
  have hI₄z : ∀ k, b ≤ k → b + 18 < k → k ≠ b + 19 → k ≠ b + 26 → I₄ k = 0 := by
    intro k hk hk' h19 h26
    simp [hI₄def, Function.update_of_ne h19, Function.update_of_ne h26,
      Function.update_of_ne (show k ≠ b + 6 by omega), Function.update_of_ne (show k ≠ b + 7 by omega),
      Function.update_of_ne (show k ≠ b + 8 by omega), hJ0 k hk hk']
  have p4 := rdN_step (b := b) hinf (k := b + 20) (by omega)
    ⟨copyR R₃ 0 Hm (n + q + 4), I₄⟩ (a := Hm + n + q + 2) (o := Hm + n + q + 1)
    (t := Hm + n + q + 3) (by simp [hI₄def]) (by simp [hI₄def]) (by simp [hI₄def])
    (by omega) (by omega) (by omega)
    (by simp only; rw [show Hm + n + q + 1 = Hm + (n + q + 1) by omega, hcopy _ (by omega),
      hR₃src _ le_rfl, srcVal_one])
    (by simp [hI₄def, hI₃def, hI₁z (b + 9) (by omega) (by omega) (by omega) (by omega)
      (by omega)])
    (by simp [hI₄def, hI₃def, hI₁z b le_rfl (by omega) (by omega) (by omega) (by omega)])
    (by simp only; rw [show Hm + n + q + 2 = Hm + (n + q + 2) by omega, hcopy _ (by omega)];
        exact hA₃) hs₄
  refine Spec.seq (Spec.of_runs p4) ?_
  rintro ⟨R₅, I₅⟩ ⟨hI₅, hA₅, hs₅, hR₅⟩
  simp only at hI₅ hA₅ hR₅
  rw [hI₄z (b + 20) (by omega) (by omega) (by omega) (by omega), Nat.zero_add] at hI₅
  subst hI₅
  -- phase 5: the leaves
  set F := Function.update I₄ (b + 20) (markAt LV 0) with hFdef
  have hFz : ∀ k, b ≤ k → b + 18 < k → k ≠ b + 19 → k ≠ b + 20 → k ≠ b + 26 → F k = 0 :=
    fun k hk hk' h19 h20 h26 => by
      simp [hFdef, Function.update_of_ne h20, hI₄z k hk hk' h19 h26]
  have hFlo : ∀ k, b ≤ k → k ≤ b + 3 → F k = 0 := fun k hk hk' => by
    simp [hFdef, hI₄def, hI₃def, Function.update_of_ne (show k ≠ b + 20 by omega),
      Function.update_of_ne (show k ≠ b + 19 by omega),
      Function.update_of_ne (show k ≠ b + 8 by omega), Function.update_of_ne (show k ≠ b + 7 by omega),
      Function.update_of_ne (show k ≠ b + 6 by omega), Function.update_of_ne (show k ≠ b + 26 by omega),
      Function.update_of_ne (show k ≠ b + 18 by omega), Function.update_of_ne (show k ≠ b + 17 by omega),
      Function.update_of_ne (show k ≠ b + 16 by omega), Function.update_of_ne (show k ≠ b + 15 by omega),
      Function.update_of_ne (show k ≠ b + 14 by omega), Function.update_of_ne (show k ≠ b + 11 by omega),
      hI₁z k hk (by omega) (by omega) (by omega) (by omega)]
  have hF9 : F (b + 9) = 0 := by
    simp [hFdef, hI₄def, hI₃def, hI₁z (b + 9) (by omega) (by omega) (by omega) (by omega)
      (by omega)]
  have hFok : FOk b n q Hm s₁ s₂ N F :=
    ⟨hFlo b le_rfl (by omega), hFlo (b + 1) (by omega) (by omega),
      hFlo (b + 2) (by omega) (by omega), hFlo (b + 3) (by omega) le_rfl,
      by simp [hFdef, hI₄def, hI₃def, hI₁v4], by simp [hFdef, hI₄def],
      by simp [hFdef, hI₄def], by simp [hFdef, hI₄def], hF9,
      by simp [hFdef, hI₄def, hI₃def], by simp [hFdef, hI₄def, hI₃def],
      by simp [hFdef, hI₄def, hI₃def], by simp [hFdef, hI₄def, hI₃def],
      by simp [hFdef, hI₄def],
      hFz (b + 21) (by omega) (by omega) (by omega) (by omega) (by omega),
      hFz (b + 22) (by omega) (by omega) (by omega) (by omega) (by omega),
      hFz (b + 24) (by omega) (by omega) (by omega) (by omega) (by omega),
      hFz (b + 25) (by omega) (by omega) (by omega) (by omega) (by omega)⟩
  have hF18 : F (b + 18) = K := by simp [hFdef, hI₄def, hI₃def]
  have hFF : Function.update (Function.update F (b + 18) K) (b + 20) (markAt LV 0) = F := by
    rw [← hF18, Function.update_eq_self]
    simp [hFdef]
  have p5 := leaves_spec M rfl hinf hFok hN LV hℓ hpos (by omega) hhalt K ⟨R₅, F⟩
    (by rw [hFF]; exact fun k _ => rfl)
    (fun k hk => by
      simp only [hFdef, hI₄def, hI₃def]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hI₁lo k hk)
    (fun i hi => by
      simp only
      rw [hR₅ _ (by omega) (by omega), hcopy i (by omega)]
      exact hR₃src i hi)
    (pos₃ + markAt LV 0 + 1) hA₅ hs₅
  refine Spec.seq (Spec.of_runs p5) ?_
  rintro ⟨R₆, I₆⟩ ⟨h18, hz6⟩
  simp only [← hbdef] at h18 hz6
  -- phase 6: accept iff enough leaves accepted
  refine Spec.seq (Q₁ := fun _ => False) (T₁ := 0 + 2) (T₂ := 0)
    (Spec.ite (T := 0) (fun hc => Spec.halt ?_) (fun hc => Spec.halt ?_)) fun _ h => h.elim
  · simp only [Cond.holds_idxEq, h18, hz6] at hc
    simp only [Option.some.injEq]
    symm
    simp only [decide_eq_true_eq]
    omega
  · simp only [Cond.holds_idxEq, h18, hz6] at hc
    simp only [Option.some.injEq]
    symm
    simp only [decide_eq_false_iff_not]
    omega

/-! ## The machine-construction lemma -/

/-- **The gather-count machine.** -/
theorem gather_count (M : Machine) (s₁ s₂ T q : ℕ → ℕ) (leaves : ℕ → List (List ℕ))
    (K : ℕ → ℕ) (hs₁ : PolyBounded s₁) (hs₂ : PolyBounded s₂) (hT : PolyBounded T)
    (hq : PolyBounded q) (hP : PolyBounded fun n => (leaves n).length)
    (hlen : ∀ n, ∀ ℓ ∈ leaves n, ℓ.length = n + s₁ n + s₂ n)
    (hpos : ∀ n, ∀ ℓ ∈ leaves n, ∀ k ∈ ℓ, k ≤ n + q n + 1)
    (hK : ∀ n, K n ≤ (leaves n).length)
    (hhalt : ∀ n (x : Fin n → ℝ) (S : Fin (q n) → ℝ), ∀ ℓ ∈ leaves n,
      M.HaltsWithin (T n) [n, s₁ n, s₂ n] (gather x S (n + s₁ n + s₂ n) ℓ)) :
    ∃ (N : Machine) (p : ℕ → ℕ), PolyBounded p ∧ ∀ n (x : Fin n → ℝ) (S : Fin (q n) → ℝ),
      N.HaltsWithin (p n) [n, q n] (Fin.append x S) ∧
      (N.HaltsWith (p n) [n, q n] (Fin.append x S) (some true) ↔
        K n ≤ (leaves n).countP fun ℓ =>
          decide (M.HaltsWith (T n) [n, s₁ n, s₂ n] (gather x S (n + s₁ n + s₂ n) ℓ)
            (some true))) := by
  -- the advice
  set N : ℕ → ℕ := fun n => n + s₁ n + s₂ n with hNdef
  set Hm : ℕ → ℕ := fun n => N n + T n + q n + 4 with hHmdef
  set bl : ℕ → List ℕ := fun n => [Hm n, s₁ n, s₂ n, N n, K n] ++ leafNums (leaves n) with hbl
  set blocks : ℕ → List Bool := fun m => encList ((bl m).length :: bl m) with hblocks
  set α := tailVal (streamOf blocks) 0 with hα
  set V : ℕ → ℕ := fun n => blockOff blocks n with hVdef
  set b := idxBd M + 3 with hb
  set p : ℕ → ℕ := fun n => gTotal M b n (q n) (Hm n) (s₁ n) (s₂ n) (N n) (K n) (T n) (V n)
    (bl n).length (leaves n).length (markAt (leaves n) 0) + 1 with hpdef
  refine ⟨(gStmt M α).toMachine, p, ?_, fun n x S => ?_⟩
  · -- polynomial bounds
    have hN : PolyBounded N := by simp only [hNdef]; pb_tac
    have hHm : PolyBounded Hm := by simp only [hHmdef]; pb_tac
    have hK' : PolyBounded K := pb_mono hP hK
    have hlen' : ∀ n, (bl n).length ≤ 6 + (leaves n).length * (1 + N n) := by
      intro n
      simp only [hbl, leafNums, List.length_append, List.length_flatMap, List.length_cons,
        List.length_nil]
      have : ((leaves n).map fun ℓ => ℓ.length + 1).sum ≤ (leaves n).length * (1 + N n) := by
        have := List.sum_le_card_nsmul ((leaves n).map fun ℓ => ℓ.length + 1) (1 + N n) (by
          intro v hv
          obtain ⟨ℓ, hℓ, rfl⟩ := List.mem_map.1 hv
          rw [hlen n ℓ hℓ]; simp only [hNdef]; omega)
        simpa using this
      have e : (List.map (List.length ∘ fun ℓ => 1 :: ℓ) (leaves n)).sum =
          ((leaves n).map fun ℓ => ℓ.length + 1).sum := by
        congr 1
      simp only [Function.comp_def, List.length_cons] at e ⊢
      omega
    have hL : PolyBounded fun n => (bl n).length :=
      pb_mono (g := fun n => 6 + (leaves n).length * (1 + N n)) (by pb_tac) hlen'
    -- the length of the blocks
    have henc : ∀ (l : List ℕ) (B : ℕ), (∀ v ∈ l, v ≤ B) → (encList l).length ≤ l.length * (B + 1) := by
      intro l B hB
      induction l with
      | nil => simp
      | cons v l ih =>
        simp only [encList_cons, List.length_append, length_encNum, List.length_cons]
        have := hB v (List.mem_cons_self ..)
        have := ih (fun w hw => hB w (List.mem_cons_of_mem _ hw))
        nlinarith
    have hbB : ∀ m, ∀ v ∈ bl m, v ≤ Hm m + K m + m + q m + 2 := by
      intro m v hv
      have e1 : Hm m = m + s₁ m + s₂ m + T m + q m + 4 := rfl
      simp only [hbl, List.mem_append, leafNums, List.mem_flatMap] at hv
      rcases hv with hv | (⟨ℓ, hℓ, hv⟩ | hv)
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · omega
        · rw [e1]; omega
        · rw [e1]; omega
        · rw [e1]; show m + s₁ m + s₂ m ≤ _; omega
        · omega
      · simp only [List.mem_cons] at hv
        rcases hv with rfl | hv
        · omega
        · have := hpos m ℓ hℓ v hv; omega
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
        omega
    have hblk : ∀ m, (blocks m).length ≤ ((bl m).length + 1) * (Hm m + K m + m + q m + 2 + 2) := by
      intro m
      simp only [hblocks, encList_cons, List.length_append, length_encNum]
      have := henc (bl m) _ (hbB m)
      nlinarith
    have hBb : PolyBounded fun m => ((bl m).length + 1) * (Hm m + K m + m + q m + 2 + 2) := by
      pb_tac
    have hV : PolyBounded V := by
      refine pb_mono (pb_sum hBb) fun n => ?_
      simp only [hVdef, blockOff_eq_sum]
      calc ∑ j ∈ Finset.range n, (blocks j).length ≤ ∑ j ∈ Finset.range (n + 1), (blocks j).length :=
            Finset.sum_le_sum_of_subset (by simp)
        _ ≤ _ := Finset.sum_le_sum fun j _ => hblk j
    have hmk : PolyBounded fun n => markAt (leaves n) 0 :=
      pb_mono (pb_const 1) fun n => by simp only [markAt]; split_ifs <;> omega
    simp only [hpdef, gTotal, leafTime, gTime, simTime]
    clear_value p V α blocks bl Hm N b
    pb_tac
  · -- the run at size `n`
    have hhalt' : ∀ ℓ ∈ leaves n, ∃ o, M.run (T n)
        (initConfig [n, s₁ n, s₂ n] (vecReg (gather x S (N n) ℓ))) = some o :=
      fun ℓ hℓ => hhalt n x S ℓ hℓ
    have hVm : ∀ m < n, ∀ v ∈ bl m, v ≤ V n := by
      intro m hm v hv
      have h1 : v + 1 ≤ (encList (bl m)).length := by
        rw [length_encList]
        exact List.le_sum_of_mem (List.mem_map_of_mem (f := (· + 1)) hv)
      have h2 : (blocks m).length ≤ V n := by
        simp only [hVdef, blockOff_eq_sum]
        exact Finset.single_le_sum (f := fun j => (blocks j).length) (fun _ _ => Nat.zero_le _)
          (Finset.mem_range.2 hm)
      have h3 : (encList (bl m)).length ≤ (blocks m).length := by
        simp [hblocks, encList_cons]
      omega
    have hLm : ∀ m < n, (bl m).length ≤ V n := by
      intro m hm
      have h2 : (blocks m).length ≤ V n := by
        simp only [hVdef, blockOff_eq_sum]
        exact Finset.single_le_sum (f := fun j => (blocks j).length) (fun _ _ => Nat.zero_le _)
          (Finset.mem_range.2 hm)
      have h3 : (bl m).length + 1 ≤ (blocks m).length := by
        simp [hblocks, encList_cons]
      omega
    have hspec := gmain_spec M x S bl (leaves n) (Hm := Hm n) (s₁ := s₁ n) (s₂ := s₂ n)
      (N := N n) (K := K n) (T := T n) (V := V n) rfl rfl (by simp only [hHmdef]; omega)
      (hlen n) (hpos n) hhalt' hVm hLm
    obtain ⟨st', r, hr, hrun⟩ := Halts.run hspec
    have hrun0 := hrun 0
    rw [St.init_at, Nat.add_zero] at hrun0
    refine ⟨⟨r, hrun0⟩, ?_⟩
    unfold Machine.HaltsWith
    rw [hrun0, hr]
    simp only [accCount, Option.some.injEq]
    exact decide_eq_true_iff

end AMNPAux

end ClassSep
