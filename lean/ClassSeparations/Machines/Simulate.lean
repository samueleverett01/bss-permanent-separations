import ClassSeparations.Machines.Program

/-!
# Running an arbitrary machine as a subroutine

A machine `M` is run inside a structured program (`Prog.Stmt`) by an *interpreter*: the program
counter of `M` is kept in a host index register `pcR`, and one iteration of a while loop
executes one instruction of `M` by a dispatch on `pcR` (a chain of tests `pcR = 0` with
decrements).  The instructions of `M` act directly on the registers of the host: the index
registers named by `M` (all `< idxBd M`) and the real registers below a *high-water mark* `H`
that `M` cannot exceed within its time bound.  Host data live in index registers `≥ idxBd M`
and in real registers `≥ H`, and are left intact.

* Accepting, rejecting, falling off the end of the program and a division by zero (guarded by a
  zero test) end the loop; the host register `accR` records acceptance.
* `sim_spec`: if `M` halts within `T` steps with outcome `o` from a configuration that agrees
  with the host state on `M`'s registers, the interpreter falls through within
  `simTime M T = O(T)` steps with `accR = [o = some true]`.
-/

set_option autoImplicit false

noncomputable section

open Classical

namespace ClassSep

namespace AMNPAux

open Prog

/-! ## Facts about runs -/

theorem run_exists_halt {M : Machine} : ∀ {T : ℕ} {c : MConfig} {o : Option Bool},
    M.run T c = some o → ∃ k < T, ∃ c', M.Reaches k c c' ∧ M.step c' = .inr o
  | 0, c, o, h => by simp [Machine.run] at h
  | T + 1, c, o, h => by
    rw [Machine.run] at h
    cases hs : M.step c with
    | inl c₁ =>
      simp only [hs] at h
      obtain ⟨k, hk, c', hr, hst⟩ := run_exists_halt h
      exact ⟨k + 1, by omega, c', ⟨c₁, hs, hr⟩, hst⟩
    | inr o' =>
      simp only [hs, Option.some.injEq] at h
      exact ⟨0, by omega, c, rfl, by rw [hs, h]⟩

theorem reaches_det {M : Machine} : ∀ {a b : ℕ} {c x y : MConfig},
    M.Reaches a c x → M.Reaches (a + b) c y → M.Reaches b x y
  | 0, b, c, x, y, h1, h2 => by
    have : c = x := h1
    subst this
    simpa using h2
  | a + 1, b, c, x, y, h1, h2 => by
    obtain ⟨c₁, hs, h1⟩ := h1
    rw [show a + 1 + b = (a + b) + 1 by omega] at h2
    obtain ⟨c₁', hs', h2⟩ := h2
    rw [hs] at hs'
    cases hs'
    exact reaches_det h1 h2

theorem run_mono {M : Machine} {T T' : ℕ} {c : MConfig} {o : Option Bool}
    (h : M.run T c = some o) (hT : T ≤ T') : M.run T' c = some o := by
  obtain ⟨k, hk, c', hr, hs⟩ := run_exists_halt h
  have := hr.run_halt hs (T' - k - 1)
  rwa [show k + 1 + (T' - k - 1) = T' by omega] at this

/-! ## One step of a machine, instruction by instruction -/

/-- The effect of the instruction `ins` at the configuration `c` (as in `Machine.step`). -/
def stepOne (ins : MInstr) (c : MConfig) : MConfig ⊕ Option Bool :=
  match ins with
  | .arith op d a b =>
      match op.apply? (c.R (c.I a)) (c.R (c.I b)) with
      | none => .inr none
      | some v => .inl { c with pc := c.pc + 1, R := Function.update c.R (c.I d) v }
  | .const d v => .inl { c with pc := c.pc + 1, R := Function.update c.R (c.I d) v }
  | .copy d a => .inl { c with pc := c.pc + 1, R := Function.update c.R (c.I d) (c.R (c.I a)) }
  | .jumpGe a t => .inl { c with pc := if 0 ≤ c.R (c.I a) then t else c.pc + 1 }
  | .jumpEq a t => .inl { c with pc := if c.R (c.I a) = 0 then t else c.pc + 1 }
  | .inc k => .inl { c with pc := c.pc + 1, I := Function.update c.I k (c.I k + 1) }
  | .dec k => .inl { c with pc := c.pc + 1, I := Function.update c.I k (c.I k - 1) }
  | .jumpIdx k l t => .inl { c with pc := if c.I k = c.I l then t else c.pc + 1 }
  | .accept => .inr (some true)
  | .reject => .inr (some false)

theorem step_eq_stepOne {M : Machine} {c : MConfig} {ins : MInstr}
    (h : M.prog[c.pc]? = some ins) : M.step c = stepOne ins c := by
  unfold Machine.step
  rw [h]
  rfl

theorem step_of_none {M : Machine} {c : MConfig} (h : M.prog[c.pc]? = none) :
    M.step c = .inr (some false) := by
  unfold Machine.step
  rw [h]

/-- One more than the largest index register named by an instruction. -/
def instrIdx : MInstr → ℕ
  | .arith _ d a b => d + a + b + 1
  | .const d _ => d + 1
  | .copy d a => d + a + 1
  | .jumpGe a _ => a + 1
  | .jumpEq a _ => a + 1
  | .inc k => k + 1
  | .dec k => k + 1
  | .jumpIdx k l _ => k + l + 1
  | .accept => 0
  | .reject => 0

/-- The jump target of an instruction (`0` if none). -/
def instrTgt : MInstr → ℕ
  | .jumpGe _ t => t
  | .jumpEq _ t => t
  | .jumpIdx _ _ t => t
  | _ => 0

/-- A bound on the index registers named by a machine. -/
def idxBd (M : Machine) : ℕ := (M.prog.map instrIdx).sum

/-- A bound on the program counters reachable by a machine. -/
def pcMax (M : Machine) : ℕ := M.prog.length + (M.prog.map instrTgt).sum

theorem idxBd_le {M : Machine} {ins : MInstr} (h : ins ∈ M.prog) : instrIdx ins ≤ idxBd M :=
  List.le_sum_of_mem (List.mem_map_of_mem h)

theorem tgt_le {M : Machine} {ins : MInstr} (h : ins ∈ M.prog) : instrTgt ins ≤ pcMax M :=
  (List.le_sum_of_mem (List.mem_map_of_mem h)).trans (Nat.le_add_left _ _)

theorem stepOne_I_le {ins : MInstr} {c c₁ : MConfig} (h : stepOne ins c = .inl c₁) (k : ℕ) :
    c₁.I k ≤ c.I k + 1 := by
  cases ins with
  | arith op d a b =>
    simp only [stepOne] at h
    split at h
    · simp at h
    · simp only [Sum.inl.injEq] at h; subst h; simp
  | inc k' =>
    simp only [stepOne, Sum.inl.injEq] at h; subst h
    by_cases hk : k = k'
    · subst hk; simp
    · simp [Function.update_of_ne hk]
  | dec k' =>
    simp only [stepOne, Sum.inl.injEq] at h; subst h
    by_cases hk : k = k'
    · subst hk; simp; omega
    · simp [Function.update_of_ne hk]
  | accept => simp [stepOne] at h
  | reject => simp [stepOne] at h
  | _ => simp only [stepOne, Sum.inl.injEq] at h; subst h; simp

theorem stepOne_I_eq {ins : MInstr} {c c₁ : MConfig} (h : stepOne ins c = .inl c₁) (k : ℕ)
    (hk : instrIdx ins ≤ k) : c₁.I k = c.I k := by
  cases ins with
  | arith op d a b =>
    simp only [stepOne] at h
    split at h
    · simp at h
    · simp only [Sum.inl.injEq] at h; subst h; rfl
  | inc k' =>
    simp only [stepOne, Sum.inl.injEq] at h; subst h
    simp only [instrIdx] at hk
    exact Function.update_of_ne (show k ≠ k' by omega) _ _
  | dec k' =>
    simp only [stepOne, Sum.inl.injEq] at h; subst h
    simp only [instrIdx] at hk
    exact Function.update_of_ne (show k ≠ k' by omega) _ _
  | accept => simp [stepOne] at h
  | reject => simp [stepOne] at h
  | _ => simp only [stepOne, Sum.inl.injEq] at h; subst h; rfl

theorem stepOne_pc {ins : MInstr} {c c₁ : MConfig} (h : stepOne ins c = .inl c₁) :
    c₁.pc = c.pc + 1 ∨ c₁.pc = instrTgt ins := by
  cases ins with
  | arith op d a b =>
    simp only [stepOne] at h
    split at h
    · simp at h
    · simp only [Sum.inl.injEq] at h; subst h; simp
  | jumpGe a t =>
    simp only [stepOne, Sum.inl.injEq] at h; subst h
    simp only [instrTgt]; split_ifs <;> simp_all
  | jumpEq a t =>
    simp only [stepOne, Sum.inl.injEq] at h; subst h
    simp only [instrTgt]; split_ifs <;> simp_all
  | jumpIdx k l t =>
    simp only [stepOne, Sum.inl.injEq] at h; subst h
    simp only [instrTgt]; split_ifs <;> simp_all
  | accept => simp [stepOne] at h
  | reject => simp [stepOne] at h
  | _ => simp only [stepOne, Sum.inl.injEq] at h; subst h; simp

theorem step_I_le {M : Machine} {c c₁ : MConfig} (h : M.step c = .inl c₁) (k : ℕ) :
    c₁.I k ≤ c.I k + 1 := by
  rcases hp : M.prog[c.pc]? with _ | ins
  · rw [step_of_none hp] at h; cases h
  · rw [step_eq_stepOne hp] at h; exact stepOne_I_le h k

theorem step_I_eq {M : Machine} {c c₁ : MConfig} (h : M.step c = .inl c₁) (k : ℕ)
    (hk : idxBd M ≤ k) : c₁.I k = c.I k := by
  rcases hp : M.prog[c.pc]? with _ | ins
  · rw [step_of_none hp] at h; cases h
  · rw [step_eq_stepOne hp] at h
    exact stepOne_I_eq h k ((idxBd_le (List.mem_of_getElem? hp)).trans hk)

theorem step_pc_le {M : Machine} {c c₁ : MConfig} (h : M.step c = .inl c₁) :
    c₁.pc ≤ pcMax M := by
  rcases hp : M.prog[c.pc]? with _ | ins
  · rw [step_of_none hp] at h; cases h
  · rw [step_eq_stepOne hp] at h
    have hlt : c.pc < M.prog.length := by
      rcases Nat.lt_or_ge c.pc M.prog.length with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none h'] at hp; cases hp
    rcases stepOne_pc h with h' | h'
    · rw [h']; unfold pcMax; omega
    · rw [h']; exact tgt_le (List.mem_of_getElem? hp)

/-! ## The interpreter -/

/-- `I pcR := I pcR + t`. -/
def setPc (pcR t : ℕ) : Stmt := (Stmt.op (.inc pcR)).rep t

/-- An arithmetic instruction; a division by zero ends the run (as a rejection). -/
def arithStmt (pcR runR j : ℕ) (op : TOp) (d a b : ℕ) : Stmt :=
  match op with
  | .add => .seq (.op (.arith .add d a b)) (setPc pcR (j + 1))
  | .sub => .seq (.op (.arith .sub d a b)) (setPc pcR (j + 1))
  | .mul => .seq (.op (.arith .mul d a b)) (setPc pcR (j + 1))
  | .div => .ite (.zero b) (.op (.dec runR)) (.seq (.op (.arith .div d a b)) (setPc pcR (j + 1)))

/-- One instruction at address `j` (with `I pcR = 0` on entry). -/
def stepInstr (pcR runR accR j : ℕ) : MInstr → Stmt
  | .arith op d a b => arithStmt pcR runR j op d a b
  | .const d v => .seq (.op (.const d v)) (setPc pcR (j + 1))
  | .copy d a => .seq (.op (.copy d a)) (setPc pcR (j + 1))
  | .jumpGe a t => .ite (.nonneg a) (setPc pcR t) (setPc pcR (j + 1))
  | .jumpEq a t => .ite (.zero a) (setPc pcR t) (setPc pcR (j + 1))
  | .inc k => .seq (.op (.inc k)) (setPc pcR (j + 1))
  | .dec k => .seq (.op (.dec k)) (setPc pcR (j + 1))
  | .jumpIdx k l t => .ite (.idxEq k l) (setPc pcR t) (setPc pcR (j + 1))
  | .accept => .seq (.op (.dec runR)) (.op (.inc accR))
  | .reject => .op (.dec runR)

/-- Dispatch on the program counter: the instructions `l` sit at the addresses `j, j+1, …`. -/
def dispatch (pcR runR accR z : ℕ) : List MInstr → ℕ → Stmt
  | [], _ => .op (.dec runR)
  | ins :: rest, j => .ite (.idxEq pcR z) (stepInstr pcR runR accR j ins)
      (.seq (.op (.dec pcR)) (dispatch pcR runR accR z rest (j + 1)))

/-- The interpreter: run `M` until it halts; on exit `I accR` is `1` iff `M` accepted (for
`I runR = I accR = I pcR = 0` on entry). -/
def simStmt (M : Machine) (pcR runR accR z : ℕ) : Stmt :=
  .seqs [.op (.inc runR), .loop (.idxEq runR z) (dispatch pcR runR accR z M.prog 0),
    clearIdx pcR z]

/-- The running time of the interpreter for `T` steps of `M`. -/
def simTime (M : Machine) (T : ℕ) : ℕ := T * (4 * pcMax M + 10) + 3 * pcMax M + 3

/-- Conditions on the host registers of the interpreter. -/
structure SimOk (b pcR runR accR z : ℕ) : Prop where
  pc : b ≤ pcR
  run : b ≤ runR
  acc : b ≤ accR
  zz : b ≤ z
  pr : pcR ≠ runR
  pa : pcR ≠ accR
  pz : pcR ≠ z
  ra : runR ≠ accR
  rz : runR ≠ z
  az : accR ≠ z

/-- The host state agrees with the configuration `c` on the index registers `< b` and on the
real registers `< H`. -/
def Agree (b H : ℕ) (c : MConfig) (st : St) : Prop :=
  (∀ k < b, st.I k = c.I k) ∧ (∀ i < H, st.R i = c.R i)

/-- The host registers are unchanged (except the interpreter's registers). -/
def Frame (b H pcR runR accR : ℕ) (st st' : St) : Prop :=
  (∀ k, b ≤ k → k ≠ pcR → k ≠ runR → k ≠ accR → st'.I k = st.I k) ∧
    (∀ i, H ≤ i → st'.R i = st.R i)

/-- The state after one iteration of the interpreter, for the step result `r` of `M`. -/
def SimPost (b H pcR runR accR pm : ℕ) (st : St) : MConfig ⊕ Option Bool → St → Prop
  | .inl c₁, st' => (Agree b H c₁ st' ∧ st'.I pcR = c₁.pc ∧ st'.I runR = st.I runR ∧
      st'.I accR = st.I accR) ∧ Frame b H pcR runR accR st st'
  | .inr o, st' => (st'.I runR = st.I runR - 1 ∧
      st'.I accR = st.I accR + (if o = some true then 1 else 0) ∧
      (∀ k < b, st'.I k = st.I k) ∧ st'.I pcR ≤ pm) ∧ Frame b H pcR runR accR st st'

theorem setPc_spec (pcR t : ℕ) (st : St) {H : St → Option Bool → Prop} :
    Spec (setPc pcR t) st (· = ⟨st.R, Function.update st.I pcR (st.I pcR + t)⟩) H t := by
  have := Spec.rep (s := .op (.inc pcR)) (H := H) (T := 1) (st := st)
    (fun q st' => st' = ⟨st.R, Function.update st.I pcR (st.I pcR + q)⟩) t
    (fun q _ st' h => Spec.inc (by subst h; simp [Nat.add_assoc]) le_rfl) (by simp)
  simpa [setPc] using this

theorem setPc_runs {pcR t : ℕ} {st : St} {Q : St → Prop} {H : St → Option Bool → Prop}
    {T : ℕ} (h : Q ⟨st.R, Function.update st.I pcR (st.I pcR + t)⟩) (hT : t ≤ T) :
    Spec (setPc pcR t) st Q H T :=
  ((setPc_spec pcR t st).mono_post fun _ e => e ▸ h).mono_time hT

section StepInstr

variable {b H pcR runR accR z pm : ℕ}

/-- The update of the real registers at an address below `H` agrees with the update in `M`. -/
theorem agree_updR {c : MConfig} {st : St} (hag : Agree b H c st) {a : ℕ} (ha : a < H) (v : ℝ)
    (I' : ℕ → ℕ) (cI : ℕ → ℕ) (hI : ∀ k < b, I' k = cI k) :
    Agree b H { c with R := Function.update c.R a v, I := cI } ⟨Function.update st.R a v, I'⟩ := by
  refine ⟨fun k hk => hI k hk, fun i hi => ?_⟩
  simp only [Function.update_apply]
  split_ifs
  · rfl
  · exact hag.2 i hi

theorem frame_updR {st : St} (hok : SimOk b pcR runR accR z) {a : ℕ} (ha : a < H) (v : ℝ)
    (I' : ℕ → ℕ) (hI : ∀ k, b ≤ k → k ≠ pcR → k ≠ runR → k ≠ accR → I' k = st.I k) :
    Frame b H pcR runR accR st ⟨Function.update st.R a v, I'⟩ :=
  ⟨hI, fun i hi => by simp [Function.update_of_ne (show i ≠ a by omega)]⟩

theorem stepInstr_spec (hok : SimOk b pcR runR accR z) (ins : MInstr) (hb : instrIdx ins ≤ b)
    (htg : instrTgt ins ≤ pm) (c : MConfig) (hcpm : c.pc + 1 ≤ pm) (st : St) (hag : Agree b H c st)
    (haddr : ∀ k < b, c.I k < H) (hpc : st.I pcR = 0) :
    Runs (stepInstr pcR runR accR c.pc ins) st (SimPost b H pcR runR accR pm st (stepOne ins c))
      (pm + 5) := by
  have hI : ∀ k < b, st.I k = c.I k := hag.1
  have hR : ∀ i < H, st.R i = c.R i := hag.2
  have npc : ∀ k < b, k ≠ pcR := fun k hk => by have := hok.pc; omega
  have nrun : ∀ k < b, k ≠ runR := fun k hk => by have := hok.run; omega
  have nacc : ∀ k < b, k ≠ accR := fun k hk => by have := hok.acc; omega
  -- the generic case: an operation followed by `setPc (j + 1)`
  have hgen : ∀ (o : BOp) (st₁ : St) (c₁ : MConfig), o.exec st = some st₁ →
      c₁.pc = c.pc + 1 → Agree b H c₁ ⟨st₁.R, Function.update st₁.I pcR (c.pc + 1)⟩ →
      st₁.I runR = st.I runR → st₁.I accR = st.I accR →
      Frame b H pcR runR accR st ⟨st₁.R, Function.update st₁.I pcR (c.pc + 1)⟩ →
      st₁.I pcR = 0 →
      Runs (.seq (.op o) (setPc pcR (c.pc + 1))) st
        (SimPost b H pcR runR accR pm st (.inl c₁)) (pm + 3) := by
    intro o st₁ c₁ he hpc₁ hag₁ hr hacc hfr hp0
    refine (Spec.seq_op he (setPc_runs (T := pm) ?_ (by omega))).mono_time (by omega)
    rw [hp0, Nat.zero_add]
    refine ⟨⟨hag₁, ?_, ?_, ?_⟩, hfr⟩
    · simp [hpc₁]
    · simp [Function.update_of_ne hok.pr.symm, hr]
    · simp [Function.update_of_ne hok.pa.symm, hacc]
  -- jumps: `setPc t`
  have hjump : ∀ (t : ℕ) (c₁ : MConfig), c₁.pc = t → t ≤ pm → c₁.R = c.R → c₁.I = c.I →
      Runs (setPc pcR t) st (SimPost b H pcR runR accR pm st (.inl c₁)) (pm + 1) := by
    intro t c₁ hpc₁ htp hR₁ hI₁
    refine setPc_runs ?_ (by omega)
    refine ⟨⟨⟨fun k hk => ?_, fun i hi => ?_⟩, ?_, ?_, ?_⟩, ?_, fun i _ => rfl⟩
    · simp [Function.update_of_ne (npc k hk), hI k hk, hI₁]
    · simp [hR i hi, hR₁]
    · simp [hpc, hpc₁]
    · simp [Function.update_of_ne hok.pr.symm]
    · simp [Function.update_of_ne hok.pa.symm]
    · intro k _ hk _ _; simp [Function.update_of_ne hk]
  cases ins with
  | arith op d a b' =>
    simp only [instrIdx] at hb
    have ha : st.R (st.I a) = c.R (c.I a) := by rw [hI a (by omega), hR _ (haddr a (by omega))]
    have hb' : st.R (st.I b') = c.R (c.I b') := by
      rw [hI b' (by omega), hR _ (haddr b' (by omega))]
    have hd : st.I d = c.I d := hI d (by omega)
    have hdH : c.I d < H := haddr d (by omega)
    have hcase : ∀ v : ℝ,
        Agree b H { c with pc := c.pc + 1, R := Function.update c.R (c.I d) v }
          ⟨Function.update st.R (st.I d) v, Function.update st.I pcR (c.pc + 1)⟩ ∧
        Frame b H pcR runR accR st
          ⟨Function.update st.R (st.I d) v, Function.update st.I pcR (c.pc + 1)⟩ := by
      intro v
      rw [hd]
      refine ⟨agree_updR hag hdH v _ c.I fun k hk => ?_, frame_updR hok hdH v _ fun k _ hk _ _ => ?_⟩
      · simp [Function.update_of_ne (npc k hk), hI k hk]
      · simp [Function.update_of_ne hk]
    have hgen' : ∀ v : ℝ, (BOp.arith op d a b').exec st =
        some ⟨Function.update st.R (st.I d) v, st.I⟩ →
        Runs (.seq (.op (.arith op d a b')) (setPc pcR (c.pc + 1))) st
          (SimPost b H pcR runR accR pm st
            (.inl { c with pc := c.pc + 1, R := Function.update c.R (c.I d) v })) (pm + 3) :=
      fun v he => hgen _ _ _ he rfl (hcase v).1 rfl rfl (hcase v).2 hpc
    cases op with
    | add =>
      have := (hgen' (c.R (c.I a) + c.R (c.I b')) (by simp [ha, hb'])).mono_time
        (show pm + 3 ≤ pm + 5 by omega)
      simpa [stepInstr, arithStmt, stepOne, TOp.apply?] using this
    | sub =>
      have := (hgen' (c.R (c.I a) - c.R (c.I b')) (by simp [ha, hb'])).mono_time
        (show pm + 3 ≤ pm + 5 by omega)
      simpa [stepInstr, arithStmt, stepOne, TOp.apply?] using this
    | mul =>
      have := (hgen' (c.R (c.I a) * c.R (c.I b')) (by simp [ha, hb'])).mono_time
        (show pm + 3 ≤ pm + 5 by omega)
      simpa [stepInstr, arithStmt, stepOne, TOp.apply?] using this
    | div =>
      simp only [stepInstr, arithStmt]
      by_cases h0 : c.R (c.I b') = 0
      · have hst : stepOne (.arith .div d a b') c = .inr none := by
          simp [stepOne, TOp.apply?, h0]
        rw [hst]
        refine (Spec.ite_pos ?_ (Spec.op rfl ?_ le_rfl)).mono_time ?_
        · simp [hb', h0]
        · refine ⟨⟨by simp, ?_, fun k hk => ?_, ?_⟩, fun k _ _ hk _ => ?_, fun i _ => rfl⟩
          · simp [Function.update_of_ne hok.ra.symm]
          · simp [Function.update_of_ne (nrun k hk)]
          · simp [Function.update_of_ne hok.pr, hpc]
          · simp [Function.update_of_ne hk]
        · omega
      · obtain ⟨v, hv⟩ : ∃ v, v = c.R (c.I a) / c.R (c.I b') := ⟨_, rfl⟩
        have hst : stepOne (.arith .div d a b') c =
            .inl { c with pc := c.pc + 1, R := Function.update c.R (c.I d) v } := by
          simp [stepOne, TOp.apply?, h0, hv]
        rw [hst]
        refine (Spec.ite_neg ?_ (hgen' v ?_)).mono_time ?_
        · simp [hb', h0]
        · simp [BOp.exec, TOp.apply?, ha, hb', h0, hv]
        · omega
  | const d v =>
    simp only [instrIdx] at hb
    have hd : st.I d = c.I d := hI d (by omega)
    have hdH : c.I d < H := haddr d (by omega)
    refine (hgen _ ⟨Function.update st.R (st.I d) v, st.I⟩ { c with pc := c.pc + 1, R := Function.update c.R (c.I d) v } rfl rfl ?_
      rfl rfl ?_ hpc).mono_time (by omega)
    · simp only [hd]
      exact agree_updR hag hdH v _ c.I fun k hk => by
        simp [Function.update_of_ne (npc k hk), hI k hk]
    · simp only [hd]
      exact frame_updR hok hdH v _ fun k _ hk _ _ => by simp [Function.update_of_ne hk]
  | copy d a =>
    simp only [instrIdx] at hb
    have hd : st.I d = c.I d := hI d (by omega)
    have hdH : c.I d < H := haddr d (by omega)
    have ha : st.R (st.I a) = c.R (c.I a) := by rw [hI a (by omega), hR _ (haddr a (by omega))]
    refine (hgen _ ⟨Function.update st.R (st.I d) (st.R (st.I a)), st.I⟩ { c with pc := c.pc + 1, R := Function.update c.R (c.I d) (c.R (c.I a)) }
      rfl rfl ?_ rfl rfl ?_ hpc).mono_time (by omega)
    · simp only [hd, ha]
      exact agree_updR hag hdH _ _ c.I fun k hk => by
        simp [Function.update_of_ne (npc k hk), hI k hk]
    · simp only [hd]
      exact frame_updR hok hdH _ _ fun k _ hk _ _ => by simp [Function.update_of_ne hk]
  | jumpGe a t =>
    simp only [instrIdx] at hb
    simp only [instrTgt] at htg
    have ha : st.R (st.I a) = c.R (c.I a) := by rw [hI a (by omega), hR _ (haddr a (by omega))]
    simp only [stepInstr, stepOne]
    by_cases hc : 0 ≤ c.R (c.I a)
    · simp only [hc, ↓reduceIte]
      refine (Spec.ite_pos ?_ (hjump t { c with pc := t } rfl htg rfl rfl)).mono_time ?_
      · simpa [ha] using hc
      · omega
    · simp only [hc, ↓reduceIte]
      refine (Spec.ite_neg ?_ (hjump (c.pc + 1) { c with pc := c.pc + 1 } rfl (by omega) rfl rfl)).mono_time ?_
      · simpa [ha] using hc
      · omega
  | jumpEq a t =>
    simp only [instrIdx] at hb
    simp only [instrTgt] at htg
    have ha : st.R (st.I a) = c.R (c.I a) := by rw [hI a (by omega), hR _ (haddr a (by omega))]
    simp only [stepInstr, stepOne]
    by_cases hc : c.R (c.I a) = 0
    · simp only [hc, ↓reduceIte]
      refine (Spec.ite_pos ?_ (hjump t { c with pc := t } rfl htg rfl rfl)).mono_time ?_
      · simpa [ha] using hc
      · omega
    · simp only [hc, ↓reduceIte]
      refine (Spec.ite_neg ?_ (hjump (c.pc + 1) { c with pc := c.pc + 1 } rfl (by omega) rfl rfl)).mono_time ?_
      · simpa [ha] using hc
      · omega
  | inc k =>
    simp only [instrIdx] at hb
    have hk' : st.I k = c.I k := hI k (by omega)
    simp only [stepInstr, stepOne]
    refine (hgen _ ⟨st.R, Function.update st.I k (st.I k + 1)⟩ { c with pc := c.pc + 1, I := Function.update c.I k (c.I k + 1) }
      rfl rfl ⟨fun k' hk'' => ?_, fun i hi => hR i hi⟩ ?_ ?_ ?_ ?_).mono_time (by omega)
    · by_cases h1 : k' = k
      · subst h1
        simp [Function.update_of_ne (npc k' hk''), hk']
      · simp [Function.update_of_ne (npc k' hk''), Function.update_of_ne h1, hI k' hk'']
    · simp [Function.update_of_ne (show runR ≠ k by have := hok.run; omega)]
    · simp [Function.update_of_ne (show accR ≠ k by have := hok.acc; omega)]
    · refine ⟨fun k' hk1 hk2 _ _ => ?_, fun i _ => rfl⟩
      simp [Function.update_of_ne hk2, Function.update_of_ne (show k' ≠ k by omega)]
    · simp [Function.update_of_ne (show pcR ≠ k by have := hok.pc; omega), hpc]
  | dec k =>
    simp only [instrIdx] at hb
    have hk' : st.I k = c.I k := hI k (by omega)
    simp only [stepInstr, stepOne]
    refine (hgen _ ⟨st.R, Function.update st.I k (st.I k - 1)⟩ { c with pc := c.pc + 1, I := Function.update c.I k (c.I k - 1) }
      rfl rfl ⟨fun k' hk'' => ?_, fun i hi => hR i hi⟩ ?_ ?_ ?_ ?_).mono_time (by omega)
    · by_cases h1 : k' = k
      · subst h1
        simp [Function.update_of_ne (npc k' hk''), hk']
      · simp [Function.update_of_ne (npc k' hk''), Function.update_of_ne h1, hI k' hk'']
    · simp [Function.update_of_ne (show runR ≠ k by have := hok.run; omega)]
    · simp [Function.update_of_ne (show accR ≠ k by have := hok.acc; omega)]
    · refine ⟨fun k' hk1 hk2 _ _ => ?_, fun i _ => rfl⟩
      simp [Function.update_of_ne hk2, Function.update_of_ne (show k' ≠ k by omega)]
    · simp [Function.update_of_ne (show pcR ≠ k by have := hok.pc; omega), hpc]
  | jumpIdx k l t =>
    simp only [instrIdx] at hb
    simp only [instrTgt] at htg
    have hk' : st.I k = c.I k := hI k (by omega)
    have hl' : st.I l = c.I l := hI l (by omega)
    simp only [stepInstr, stepOne]
    by_cases hc : c.I k = c.I l
    · simp only [hc, ↓reduceIte]
      refine (Spec.ite_pos ?_ (hjump t { c with pc := t } rfl htg rfl rfl)).mono_time ?_
      · simpa [hk', hl'] using hc
      · omega
    · simp only [hc, ↓reduceIte]
      refine (Spec.ite_neg ?_ (hjump (c.pc + 1) { c with pc := c.pc + 1 } rfl (by omega) rfl rfl)).mono_time ?_
      · simpa [hk', hl'] using hc
      · omega
  | accept =>
    simp only [stepInstr, stepOne]
    refine (Spec.seq_op rfl (Spec.inc ?_ le_rfl)).mono_time (by omega)
    refine ⟨⟨?_, ?_, fun k hk => ?_, ?_⟩, fun k _ h1 h2 h3 => ?_, fun i _ => rfl⟩
    · simp [Function.update_of_ne hok.ra]
    · simp [Function.update_of_ne hok.ra.symm]
    · simp [Function.update_of_ne (nrun k hk), Function.update_of_ne (nacc k hk)]
    · simp [Function.update_of_ne hok.pa, Function.update_of_ne hok.pr, hpc]
    · simp [Function.update_of_ne h2, Function.update_of_ne h3]
  | reject =>
    simp only [stepInstr, stepOne]
    refine (Spec.op rfl ?_ le_rfl).mono_time (by omega)
    refine ⟨⟨by simp, ?_, fun k hk => ?_, ?_⟩, fun k _ _ hk _ => ?_, fun i _ => rfl⟩
    · simp [Function.update_of_ne hok.ra.symm]
    · simp [Function.update_of_ne (nrun k hk)]
    · simp [Function.update_of_ne hok.pr, hpc]
    · simp [Function.update_of_ne hk]

end StepInstr

theorem dispatch_spec {pcR runR accR z : ℕ} (hpz : pcR ≠ z) (hpr : pcR ≠ runR) :
    ∀ (l : List MInstr) (j : ℕ) (st : St) (Q : St → Prop) (T : ℕ), st.I z = 0 →
    (∀ (h : st.I pcR < l.length), Runs (stepInstr pcR runR accR (j + st.I pcR) l[st.I pcR])
      ⟨st.R, Function.update st.I pcR 0⟩ Q T) →
    (l.length ≤ st.I pcR → Q ⟨st.R, Function.update (Function.update st.I pcR
      (st.I pcR - l.length)) runR (st.I runR - 1)⟩) →
    Runs (dispatch pcR runR accR z l j) st Q (T + 3 * st.I pcR + 3)
  | [], j, st, Q, T, hz, hin, hout => by
    simp only [dispatch]
    refine (Spec.op rfl ?_ le_rfl).mono_time (by omega)
    have := hout (by simp)
    simpa [Function.update_eq_self] using this
  | ins :: rest, j, st, Q, T, hz, hin, hout => by
    simp only [dispatch]
    by_cases hd : st.I pcR = 0
    · refine (Spec.ite_pos (T := T) ?_ ?_).mono_time ?_
      · simp [hd, hz]
      · have := hin (by simp [hd])
        have hst : (⟨st.R, Function.update st.I pcR 0⟩ : St) = st := by
          ext k <;> simp [Function.update_apply]; intro h; subst h; exact hd.symm
        simp only [hd, List.getElem_cons_zero, Nat.add_zero, hst] at this
        exact this
      · omega
    · have hz1 : (Function.update st.I pcR (st.I pcR - 1)) z = 0 := by
        simp [Function.update_of_ne hpz.symm, hz]
      have ih := dispatch_spec (accR := accR) hpz hpr rest (j + 1)
        ⟨st.R, Function.update st.I pcR (st.I pcR - 1)⟩ Q T hz1 ?_ ?_
      · refine (Spec.ite_neg ?_ (Spec.seq_op rfl ih)).mono_time ?_
        · simp [hz, hd]
        · simp only [Function.update_self]
          omega
      · intro h
        simp only [Function.update_self, Function.update_idem] at h ⊢
        have := hin (by simp; omega)
        have e1 : (ins :: rest)[st.I pcR]'(by simp; omega) = rest[st.I pcR - 1] := by
          rw [List.getElem_cons]; simp [hd]
        rw [e1, show j + st.I pcR = j + 1 + (st.I pcR - 1) by omega] at this
        exact this
      · intro h
        simp only [Function.update_self, Function.update_idem] at h ⊢
        have := hout (by simp; omega)
        rw [Function.update_of_ne hpr.symm] at *
        rwa [show st.I pcR - 1 - rest.length = st.I pcR - (rest.length + 1) by omega]

theorem simPost_congr {b H pcR runR accR z pm : ℕ} (hok : SimOk b pcR runR accR z)
    {st st' : St} (hR : st'.R = st.R) (hI : ∀ k, k ≠ pcR → st'.I k = st.I k)
    (r : MConfig ⊕ Option Bool) (st'' : St) :
    SimPost b H pcR runR accR pm st' r st'' → SimPost b H pcR runR accR pm st r st'' := by
  have hfr : Frame b H pcR runR accR st' st'' → Frame b H pcR runR accR st st'' :=
    fun h => ⟨fun k h1 h2 h3 h4 => by rw [h.1 k h1 h2 h3 h4, hI k h2],
      fun i hi => by rw [h.2 i hi, hR]⟩
  cases r with
  | inl c₁ =>
    rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩
    exact ⟨⟨h1, h2, by rw [h3, hI _ hok.pr.symm], by rw [h4, hI _ hok.pa.symm]⟩, hfr h5⟩
  | inr o =>
    rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩
    refine ⟨⟨by rw [h1, hI _ hok.pr.symm], by rw [h2, hI _ hok.pa.symm], fun k hk => ?_, h4⟩,
      hfr h5⟩
    rw [h3 k hk, hI k (by have := hok.pc; omega)]

theorem body_spec (M : Machine) {b H pcR runR accR z : ℕ} (hok : SimOk b pcR runR accR z)
    (hb : idxBd M ≤ b) (c : MConfig) (hcpm : c.pc ≤ pcMax M) (st : St) (hag : Agree b H c st)
    (haddr : ∀ k < b, c.I k < H) (hpc : st.I pcR = c.pc) (hz : st.I z = 0) :
    Runs (dispatch pcR runR accR z M.prog 0) st
      (SimPost b H pcR runR accR (pcMax M) st (M.step c)) (4 * pcMax M + 8) := by
  have key := dispatch_spec (accR := accR) hok.pz hok.pr M.prog 0 st
    (SimPost b H pcR runR accR (pcMax M) st (M.step c)) (pcMax M + 5) hz ?_ ?_
  · exact key.mono_time (by rw [hpc]; omega)
  · intro h
    have hget : M.prog[c.pc]? = some M.prog[st.I pcR] := by
      rw [← hpc]; exact List.getElem?_eq_getElem h
    have hmem : M.prog[st.I pcR] ∈ M.prog := List.getElem_mem h
    rw [step_eq_stepOne hget, Nat.zero_add]
    have hag' : Agree b H c ⟨st.R, Function.update st.I pcR 0⟩ :=
      ⟨fun k hk => by
        simp only [Function.update_of_ne (show k ≠ pcR by have := hok.pc; omega)]; exact hag.1 k hk,
        hag.2⟩
    have hs := stepInstr_spec (H := H) (pm := pcMax M) hok M.prog[st.I pcR]
      ((idxBd_le hmem).trans hb) (tgt_le hmem) c (by unfold pcMax; omega) _ hag' haddr
      (by simp)
    rw [← hpc] at hs
    exact hs.mono_post (simPost_congr (st := st) (st' := ⟨st.R, Function.update st.I pcR 0⟩) hok rfl
      (fun k hk => Function.update_of_ne hk _ _) _)
  · intro h
    have hnone : M.prog[c.pc]? = none := by
      rw [← hpc]; exact List.getElem?_eq_none h
    rw [step_of_none hnone]
    refine ⟨⟨by simp, ?_, fun k hk => ?_, ?_⟩, fun k _ h1 h2 _ => ?_, fun i _ => rfl⟩
    · simp [Function.update_of_ne hok.ra.symm, Function.update_of_ne hok.pa.symm]
    · simp [Function.update_of_ne (show k ≠ runR by have := hok.run; omega),
        Function.update_of_ne (show k ≠ pcR by have := hok.pc; omega)]
    · simp [Function.update_of_ne hok.pr]; omega
    · simp [Function.update_of_ne h1, Function.update_of_ne h2]

theorem frame_trans {b H pcR runR accR : ℕ} {st st' st'' : St}
    (h1 : Frame b H pcR runR accR st st') (h2 : Frame b H pcR runR accR st' st'') :
    Frame b H pcR runR accR st st'' :=
  ⟨fun k a b c d => by rw [h2.1 k a b c d, h1.1 k a b c d],
    fun i hi => by rw [h2.2 i hi, h1.2 i hi]⟩

/-- **Simulation.**  If `M` halts within `T` steps with outcome `o` from `c₀` (with program
counter `0`, index registers `≤ B`), and the host state agrees with `c₀` on the index registers
`< b` and the real registers `< H`, where `B + T ≤ H`, then the interpreter falls through within
`simTime M T` steps with `I accR = [o = some true]`; the host registers (index registers
`≥ b` other than `accR`, real registers `≥ H`) are unchanged and `M`'s index registers are at
most `B + T`. -/
theorem sim_spec (M : Machine) {b pcR runR accR z : ℕ} (hok : SimOk b pcR runR accR z)
    (hb : idxBd M ≤ b) {c₀ : MConfig} {B H T : ℕ} {o : Option Bool} (hpc0 : c₀.pc = 0)
    (hrun : M.run T c₀ = some o) (hB : ∀ k < b, c₀.I k ≤ B) (hH : B + T ≤ H)
    (st : St) (hag : Agree b H c₀ st) (h0 : st.I pcR = 0) (h1 : st.I runR = 0)
    (h2 : st.I accR = 0) (h3 : st.I z = 0) :
    Runs (simStmt M pcR runR accR z) st (fun st' =>
      (∀ k, b ≤ k → k ≠ accR → st'.I k = st.I k) ∧
      st'.I accR = (if o = some true then 1 else 0) ∧ (∀ k < b, st'.I k ≤ B + T) ∧
      (∀ i, H ≤ i → st'.R i = st.R i)) (simTime M T) := by
  obtain ⟨k, hkT, ck, hreach, hstep⟩ := run_exists_halt hrun
  let st₁ : St := ⟨st.R, Function.update st.I runR (st.I runR + 1)⟩
  let Inv : ℕ → St → Prop := fun q st' => Frame b H pcR runR accR st st' ∧ st'.I z = 0 ∧
    (q ≤ k → ∃ c, M.Reaches q c₀ c ∧ Agree b H c st' ∧ st'.I pcR = c.pc ∧ st'.I runR = 1 ∧
      st'.I accR = 0 ∧ c.pc ≤ pcMax M ∧ ∀ k' < b, c.I k' ≤ B + q) ∧
    (k < q → st'.I runR = 0 ∧ st'.I accR = (if o = some true then 1 else 0) ∧
      st'.I pcR ≤ pcMax M ∧ ∀ k' < b, st'.I k' ≤ B + T)
  have hzfr : ∀ st' st'', Frame b H pcR runR accR st' st'' → st''.I z = st'.I z :=
    fun st' st'' h => h.1 z hok.zz hok.pz.symm hok.rz.symm hok.az.symm
  have hloop : Runs (.loop (.idxEq runR z) (dispatch pcR runR accR z M.prog 0)) st₁
      (Inv (k + 1)) ((k + 1) * (4 * pcMax M + 8 + 2) + 1) := by
    refine Spec.loop Inv (k + 1) ?_ ?_ ?_ ?_
    · rintro st' ⟨-, hz', -, hfin⟩
      simp [(hfin (by omega)).1, hz']
    · rintro q hq st' ⟨-, hz', hcur, -⟩
      obtain ⟨c, -, -, -, hr, -⟩ := hcur (by omega)
      simp [hr, hz']
    · rintro q hq st' ⟨hfr, hz', hcur, -⟩
      obtain ⟨c, hrc, hag', hpc', hr', ha', hcpm, hcb⟩ := hcur (by omega)
      have haddr : ∀ k' < b, c.I k' < H := fun k' hk' => by have := hcb k' hk'; omega
      have hbody := body_spec M hok hb c hcpm st' hag' haddr hpc' hz'
      have hdet := reaches_det hrc
        (show M.Reaches (q + (k - q)) c₀ ck by rwa [show q + (k - q) = k by omega])
      rcases Nat.lt_or_ge q k with hqk | hqk
      · obtain ⟨c₁, hs1, -⟩ : ∃ c₁, M.step c = .inl c₁ ∧ M.Reaches (k - q - 1) c₁ ck := by
          rw [show k - q = (k - q - 1) + 1 by omega] at hdet
          exact hdet
        rw [hs1] at hbody
        refine hbody.mono_post ?_
        rintro st'' ⟨⟨hag'', hpc'', hr'', ha''⟩, hfr''⟩
        refine ⟨frame_trans hfr hfr'', by rw [hzfr _ _ hfr'', hz'], fun _ => ⟨c₁,
          hrc.trans (Machine.Reaches.single hs1), hag'', hpc'', by rw [hr'', hr'],
          by rw [ha'', ha'], step_pc_le hs1, fun k' hk' => ?_⟩, fun h => absurd h (by omega)⟩
        have := step_I_le hs1 k'
        have := hcb k' hk'
        omega
      · have hqk' : q = k := by omega
        subst hqk'
        have hdet0 : M.Reaches 0 c ck := by simpa using hdet
        have hc : c = ck := hdet0
        subst hc
        rw [hstep] at hbody
        refine hbody.mono_post ?_
        rintro st'' ⟨⟨hr'', ha'', hI'', hpc''⟩, hfr''⟩
        refine ⟨frame_trans hfr hfr'', by rw [hzfr _ _ hfr'', hz'],
          fun h => absurd h (by omega), fun _ => ⟨by rw [hr'', hr'], by rw [ha'', ha']; simp,
          hpc'', fun k' hk' => ?_⟩⟩
        rw [hI'' k' hk', hag'.1 k' hk']
        have := hcb k' hk'
        omega
    · refine ⟨⟨fun k' _ hk1 hk2 _ => ?_, fun i _ => rfl⟩, ?_, fun _ => ⟨c₀, rfl,
        ⟨fun k' hk' => ?_, hag.2⟩, ?_, ?_, ?_, ?_, fun k' hk' => by simpa using hB k' hk'⟩,
        fun h => absurd h (by omega)⟩
      · simp [st₁, Function.update_of_ne hk2]
      · simp [st₁, Function.update_of_ne hok.rz.symm, h3]
      · simp [st₁, Function.update_of_ne (show k' ≠ runR by have := hok.run; omega),
          hag.1 k' hk']
      · simp [st₁, Function.update_of_ne hok.pr, h0, hpc0]
      · simp [st₁, h1]
      · simp [st₁, Function.update_of_ne hok.ra.symm, h2]
      · rw [hpc0]; exact Nat.zero_le _
  simp only [simStmt, Stmt.seqs_cons]
  refine (Spec.seq_op rfl (Spec.seq hloop (T₂ := 3 * pcMax M + 1) fun st₂ hinv => ?_)).mono_time ?_
  · obtain ⟨hfr, hz2, -, hfin⟩ := hinv
    obtain ⟨hr, ha, hp, hmb⟩ := hfin (by omega)
    refine (Spec.seq_eq (clearIdx_spec hok.pz hz2) (Spec.skip (T := 0) ?_)).mono_time
      (by omega)
    refine ⟨fun k' hk' hka => ?_, ?_, fun k' hk' => ?_, fun i hi => ?_⟩
    · by_cases hkp : k' = pcR
      · subst hkp; simp [h0]
      · by_cases hkr : k' = runR
        · subst hkr; simp [Function.update_of_ne hok.pr.symm, hr, h1]
        · simp only [Function.update_of_ne hkp]
          exact hfr.1 k' hk' hkp hkr hka
    · simp [Function.update_of_ne hok.pa.symm, ha]
    · simp only [Function.update_of_ne (show k' ≠ pcR by have := hok.pc; omega)]
      exact hmb k' hk'
    · exact hfr.2 i hi
  · -- the running time
    have := Nat.mul_le_mul (show k + 1 ≤ T by omega)
      (show 4 * pcMax M + 8 + 2 ≤ 4 * pcMax M + 10 by omega)
    simp only [simTime]
    omega

/-! ## Index register arithmetic -/

/-- `I k := I k + I a` (scratch `cnt` with `I cnt = 0`, `I z = 0`). -/
def addIdx (k a cnt z : ℕ) : Stmt :=
  .seq (.loop (.idxEq cnt a) (.seq (.op (.inc k)) (.op (.inc cnt)))) (clearIdx cnt z)

theorem addIdx_spec {st : St} {k a cnt z : ℕ} (hka : k ≠ a) (hkc : k ≠ cnt) (hca : cnt ≠ a)
    (hcz : cnt ≠ z) (hkz : k ≠ z) (hc : st.I cnt = 0) (hz : st.I z = 0) :
    Runs (addIdx k a cnt z) st (· = ⟨st.R, Function.update st.I k (st.I k + st.I a)⟩)
      (7 * st.I a + 2) := by
  obtain ⟨R₀, I₀⟩ := st
  simp only at hc hz ⊢
  have hloop : Runs (.loop (.idxEq cnt a) (.seq (.op (.inc k)) (.op (.inc cnt)))) ⟨R₀, I₀⟩
      (· = ⟨R₀, Function.update (Function.update I₀ k (I₀ k + I₀ a)) cnt (I₀ a)⟩)
      (I₀ a * (2 + 2) + 1) := by
    refine Spec.loop (fun j st' => st' = ⟨R₀, Function.update (Function.update I₀ k (I₀ k + j))
      cnt j⟩) (I₀ a) ?_ ?_ ?_ ?_
    · rintro st' rfl
      simp [Function.update_of_ne hca.symm, Function.update_of_ne hka.symm]
    · rintro j hj st' rfl
      simp [Function.update_of_ne hca.symm, Function.update_of_ne hka.symm]
      omega
    · rintro j hj st' rfl
      refine Spec.seq_op rfl (Spec.inc ?_ le_rfl)
      congr 1
      funext i
      simp only [Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all <;> omega
    · congr 1
      funext i
      simp only [Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
  refine (Spec.seq_eq hloop (clearIdx_spec hcz ?_)).mono_time ?_ |>.mono_post ?_
  · simp [Function.update_of_ne hcz.symm, Function.update_of_ne hkz.symm, hz]
  · simp
    omega
  · rintro st' rfl
    congr 1
    funext i
    simp only [Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all

/-- `I k := I a / c` for `I a` a multiple of `c ≥ 1` (with `I k = I t = 0` initially). -/
def divIdx (k t a c : ℕ) : Stmt :=
  .loop (.idxEq t a) (.seq ((Stmt.op (.inc t)).rep c) (.op (.inc k)))

theorem divIdx_spec {st : St} {k t a c m : ℕ} (hc1 : 1 ≤ c) (hkt : k ≠ t) (hka : k ≠ a)
    (hta : t ≠ a) (hk : st.I k = 0) (ht : st.I t = 0) (ha : st.I a = c * m) :
    Runs (divIdx k t a c) st
      (· = ⟨st.R, Function.update (Function.update st.I t (c * m)) k m⟩) (m * (c + 3) + 1) := by
  obtain ⟨R₀, I₀⟩ := st
  simp only at hk ht ha ⊢
  refine Spec.loop (fun j st' => st' = ⟨R₀, Function.update (Function.update I₀ t (c * j))
    k j⟩) m ?_ ?_ ?_ ?_
  · rintro st' rfl
    simp [Function.update_of_ne hta.symm, Function.update_of_ne hka.symm,
      Function.update_of_ne hkt.symm, ha]
  · rintro j hj st' rfl
    simp only [Cond.holds_idxEq, Function.update_of_ne hkt.symm, Function.update_self,
      Function.update_of_ne hta.symm, Function.update_of_ne hka.symm, ha]
    intro h
    have := Nat.eq_of_mul_eq_mul_left (by omega) h
    omega
  · rintro j hj st' rfl
    have hrep := Spec.rep (s := .op (.inc t)) (H := fun _ _ => False) (T := 1)
      (st := ⟨R₀, Function.update (Function.update I₀ t (c * j)) k j⟩)
      (fun i st' => st' = ⟨R₀, Function.update (Function.update I₀ t (c * j + i)) k j⟩) c
      (fun i _ st' h => Spec.inc (by
        subst h
        congr 1
        funext l
        simp only [Function.update_apply]
        split_ifs <;> subst_vars <;> simp_all <;> omega) le_rfl) (by simp)
    refine (Spec.seq_eq hrep (Spec.inc ?_ le_rfl)).mono_time (by omega)
    congr 1
    funext l
    simp only [Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all <;> ring
  · congr 1
    funext l
    simp only [Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all

/-! ## Polynomial bounds -/

theorem pb_const (c : ℕ) : PolyBounded fun _ => c := ⟨c, 0, fun n => by simp⟩

theorem pb_id : PolyBounded fun n => n := ⟨1, 1, fun n => by simp⟩

theorem pb_mono {f g : ℕ → ℕ} (hg : PolyBounded g) (h : ∀ n, f n ≤ g n) : PolyBounded f := by
  obtain ⟨C, e, hC⟩ := hg
  exact ⟨C, e, fun n => (h n).trans (hC n)⟩

theorem pb_add {f g : ℕ → ℕ} (hf : PolyBounded f) (hg : PolyBounded g) :
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

theorem pb_mul {f g : ℕ → ℕ} (hf : PolyBounded f) (hg : PolyBounded g) :
    PolyBounded fun n => f n * g n := by
  obtain ⟨C₁, e₁, h₁⟩ := hf
  obtain ⟨C₂, e₂, h₂⟩ := hg
  refine ⟨C₁ * C₂, e₁ + e₂, fun n => ?_⟩
  calc f n * g n ≤ (C₁ * (n + 1) ^ e₁) * (C₂ * (n + 1) ^ e₂) := Nat.mul_le_mul (h₁ n) (h₂ n)
    _ = C₁ * C₂ * (n + 1) ^ (e₁ + e₂) := by ring

/-- A sum over the sizes `≤ n` of a polynomially bounded function. -/
theorem pb_sum {f : ℕ → ℕ} (hf : PolyBounded f) :
    PolyBounded fun n => ∑ m ∈ Finset.range (n + 1), f m := by
  obtain ⟨C, e, h⟩ := hf
  refine ⟨C, e + 1, fun n => ?_⟩
  calc ∑ m ∈ Finset.range (n + 1), f m ≤ ∑ _m ∈ Finset.range (n + 1), C * (n + 1) ^ e :=
        Finset.sum_le_sum fun m hm => (h m).trans (Nat.mul_le_mul_left _
          (Nat.pow_le_pow_left (by simp at hm; omega) _))
    _ = C * (n + 1) ^ (e + 1) := by simp; ring

/-- Polynomial bounds of sums and products of polynomially bounded functions. -/
macro "pb_tac" : tactic => `(tactic| repeat' first
  | exact pb_id | exact pb_const _ | assumption | apply pb_add | apply pb_mul)

end AMNPAux

end ClassSep
