import ClassSeparations.Machines.Classes

/-!
# Writing and verifying machine programs

This file is a small library for writing programs of the real random-access machines of
`ClassSeparations.Machines.Machine` and proving them correct, including their running time.

## Overview

* **Reachability.** `M.Reaches k c c'`: started at `c`, the machine is at `c'` after exactly
  `k` steps, without having halted.  `Machine.Reaches.trans`, `Machine.Reaches.run` and
  `Machine.Reaches.runFinal` (`run (k + j) c = run j c'`) connect it with `Machine.run` and
  `Machine.runFinal`.

* **Structured programs.** Instead of writing jump targets by hand, programs are written as
  structured statements `Stmt` (basic instructions `BOp`, sequencing, if-then-else on a
  condition `Cond`, while loops, halting), and compiled to machine code by `Stmt.compile`
  (`Stmt.toMachine s` is the machine whose program is the compiled `s`).  Jump targets are
  computed by the compiler, so programs are relocatable and freely composable.

* **Big-step semantics with exact step counts.** `Exec s st out t`: started in the state `st`
  (real registers `st.R`, index registers `st.I`), the statement `s` either falls through to its
  end in the state `st'` (`out = .next st'`) or halts with outcome `r` in the state `st'`
  (`out = .halt st' r`), in `t` machine steps (for halting outcomes, the halting step itself is
  not counted).  `Exec.sound` shows that compiled code really behaves like this, at any offset
  of any program in which it is embedded (`Embeds`).

* **Hoare-style reasoning.** `Spec s st Q H T`: started in `st`, `s` ends within `T` steps,
  falling through in a state satisfying `Q` or halting with outcome `r` in a state `st'` with
  `H st' r`.  Abbreviations: `Runs s st Q T` (never halts) and `Halts s st H T` (always halts).
  Rules: `Spec.mono`/`mono_time`/`mono_post`, `Spec.skip`, `Spec.op` (and per instruction
  `Spec.const`, `copy`, `inc`, `dec`, `add`, `sub`, `mul`), `Spec.seq`, `Spec.seq_eq`
  (exactly known intermediate state), `Spec.seq_op`, `Spec.ite`/`ite_pos`/`ite_neg`,
  `Spec.ifThen`, `Spec.unless`, `Spec.rep`, `Spec.halt`, `Spec.of_runs`, and
  **`Spec.loop`** (while loops with an invariant `Inv q` indexed by the number `q` of
  iterations; the body may halt).  `Spec.sound` gives the behaviour of compiled code embedded
  at any address; `Halts.runFinal` and `Halts.run` translate a `Halts` statement for `s` into
  statements about `s.toMachine.runFinal` and `s.toMachine.run` (with any fuel `≥ T + 1`), as
  used in the definitions of the complexity classes (use `St.init_at` for `initConfig`).

* **Standard subroutines** (with exact specifications and time bounds).  Convention: scratch
  index registers are `0` before and after a subroutine, so subroutines leave all index
  registers unchanged; one index register `z` with `I z = 0` is needed.
  - index registers: `loadIdx k a` (`I k := I a` from `I k = 0`), `clearIdx k z`,
    `setIdx k a z`, `addConsts l` (add constants to several registers; `addAmt`);
  - ranges of real registers: `copyRange` (`copyR`), `fillRange` (`fillR`), and straight-line
    lists of such operations `FOp.prog` (`FOp.copy`, `FOp.fill`, `FOp.set`; effect
    `FOp.evalList`, spec `FOp.prog_spec`);
  - scanning loops `forScan a b len p q c z body` (`for j < I len`, with pointers
    `I p = I a + j`, `I q = I b + j`; spec `forScan_spec` with an invariant on the real
    registers);
  - bit fields: `bitR`, `writeBits`, binary increment `binInc` (`binInc_spec`).

* **Complex machines** (`ClassSeparations.Machines.ProgramComplex`): `Machine.toC` translates a
  real machine into a complex one; machines without `jumpGe` (e.g. `Stmt.toMachine s` for
  `s.noGe = true`, i.e. no `Cond.nonneg`) run in lockstep with their translation
  (`Machine.toC_runFinal`, `Machine.toC_run`).

Index registers are named by natural numbers; subroutines take the numbers of the registers
they use as parameters, so that the caller can keep all other registers intact.  A worked
example is the describer of the Ryser circuits, `ClassSeparations.Machines.RyserMachine`
(field addresses computed by a setup loop, a dispatch on bits, straight-line field copies,
scanning loops and binary counting).
-/

noncomputable section

open Classical

namespace ClassSep

/-! ## Multi-step reachability -/

/-- `M.Reaches k c c'`: started at `c`, the machine is at `c'` after exactly `k` steps,
without having halted before. -/
def Machine.Reaches (M : Machine) : ℕ → MConfig → MConfig → Prop
  | 0, c, c' => c = c'
  | k + 1, c, c' => ∃ c₁, M.step c = .inl c₁ ∧ M.Reaches k c₁ c'

namespace Machine.Reaches

variable {M : Machine}

theorem refl (c : MConfig) : M.Reaches 0 c c := rfl

theorem single {c c' : MConfig} (h : M.step c = .inl c') : M.Reaches 1 c c' := ⟨c', h, rfl⟩

theorem step {k : ℕ} {c c₁ c' : MConfig} (h : M.step c = .inl c₁) (h' : M.Reaches k c₁ c') :
    M.Reaches (k + 1) c c' := ⟨c₁, h, h'⟩

theorem trans {k l : ℕ} {c c₁ c₂ : MConfig} (h₁ : M.Reaches k c c₁) (h₂ : M.Reaches l c₁ c₂) :
    M.Reaches (k + l) c c₂ := by
  induction k generalizing c with
  | zero => cases h₁; simpa using h₂
  | succ k ih =>
    obtain ⟨c', hs, h⟩ := h₁
    rw [Nat.succ_add]
    exact ⟨c', hs, ih h⟩

theorem run {k : ℕ} {c c' : MConfig} (h : M.Reaches k c c') (j : ℕ) :
    M.run (k + j) c = M.run j c' := by
  induction k generalizing c with
  | zero => cases h; simp
  | succ k ih =>
    obtain ⟨c₁, hs, h⟩ := h
    rw [Nat.succ_add, Machine.run, hs]
    exact ih h

theorem runFinal {k : ℕ} {c c' : MConfig} (h : M.Reaches k c c') (j : ℕ) :
    M.runFinal (k + j) c = M.runFinal j c' := by
  induction k generalizing c with
  | zero => cases h; simp
  | succ k ih =>
    obtain ⟨c₁, hs, h⟩ := h
    rw [Nat.succ_add, Machine.runFinal, hs]
    exact ih h

end Machine.Reaches

theorem Machine.run_of_step_halt {M : Machine} {c : MConfig} {o : Option Bool}
    (h : M.step c = .inr o) (j : ℕ) : M.run (j + 1) c = some o := by
  simp [Machine.run, h]

theorem Machine.runFinal_of_step_halt {M : Machine} {c : MConfig} {o : Option Bool}
    (h : M.step c = .inr o) (j : ℕ) : M.runFinal (j + 1) c = some (c, o) := by
  simp [Machine.runFinal, h]

/-- If the machine reaches `c'` in `k` steps and then halts with outcome `o`, then `runFinal`
with any fuel `≥ k + 1` returns `(c', o)`. -/
theorem Machine.Reaches.runFinal_halt {M : Machine} {k : ℕ} {c c' : MConfig} {o : Option Bool}
    (h : M.Reaches k c c') (hs : M.step c' = .inr o) (j : ℕ) :
    M.runFinal (k + 1 + j) c = some (c', o) := by
  rw [Nat.add_assoc, h.runFinal, Nat.add_comm, Machine.runFinal_of_step_halt hs]

theorem Machine.Reaches.run_halt {M : Machine} {k : ℕ} {c c' : MConfig} {o : Option Bool}
    (h : M.Reaches k c c') (hs : M.step c' = .inr o) (j : ℕ) :
    M.run (k + 1 + j) c = some o := by
  rw [Nat.add_assoc, h.run, Nat.add_comm, Machine.run_of_step_halt hs]

namespace Prog

/-! ## States, basic instructions and conditions -/

/-- The data part of a configuration: real registers and index registers. -/
@[ext]
structure St where
  R : ℕ → ℝ
  I : ℕ → ℕ

/-- The configuration with program counter `pc` and data `st`. -/
def St.at (st : St) (pc : ℕ) : MConfig := ⟨pc, st.R, st.I⟩

@[simp] theorem St.at_pc (st : St) (pc : ℕ) : (st.at pc).pc = pc := rfl
@[simp] theorem St.at_R (st : St) (pc : ℕ) : (st.at pc).R = st.R := rfl
@[simp] theorem St.at_I (st : St) (pc : ℕ) : (st.at pc).I = st.I := rfl

/-- The data of the initial configuration `initConfig sizes w`. -/
def St.init (sizes : List ℕ) (w : ℕ → ℝ) : St := ⟨w, fun k => sizes.getD k 0⟩

theorem St.init_at (sizes : List ℕ) (w : ℕ → ℝ) :
    (St.init sizes w).at 0 = initConfig sizes w := rfl

/-- Basic (non-control) instructions. -/
inductive BOp where
  /-- `R[I d] := R[I a] op R[I b]` -/
  | arith (op : TOp) (d a b : ℕ)
  /-- `R[I d] := c` -/
  | const (d : ℕ) (c : ℝ)
  /-- `R[I d] := R[I a]` -/
  | copy (d a : ℕ)
  /-- `I k := I k + 1` -/
  | inc (k : ℕ)
  /-- `I k := I k - 1` -/
  | dec (k : ℕ)

/-- The machine instruction of a basic instruction. -/
def BOp.instr : BOp → MInstr
  | .arith op d a b => .arith op d a b
  | .const d c => .const d c
  | .copy d a => .copy d a
  | .inc k => .inc k
  | .dec k => .dec k

/-- Effect of a basic instruction (`none`: division by zero). -/
def BOp.exec : BOp → St → Option St
  | .arith op d a b, s =>
      (op.apply? (s.R (s.I a)) (s.R (s.I b))).map fun v =>
        { s with R := Function.update s.R (s.I d) v }
  | .const d c, s => some { s with R := Function.update s.R (s.I d) c }
  | .copy d a, s => some { s with R := Function.update s.R (s.I d) (s.R (s.I a)) }
  | .inc k, s => some { s with I := Function.update s.I k (s.I k + 1) }
  | .dec k, s => some { s with I := Function.update s.I k (s.I k - 1) }

/-- Conditions tested by jumps. -/
inductive Cond where
  /-- `R[I a] = 0` -/
  | zero (a : ℕ)
  /-- `R[I a] ≥ 0` -/
  | nonneg (a : ℕ)
  /-- `I k = I l` -/
  | idxEq (k l : ℕ)

/-- Truth of a condition. -/
def Cond.holds : Cond → St → Prop
  | .zero a, s => s.R (s.I a) = 0
  | .nonneg a, s => 0 ≤ s.R (s.I a)
  | .idxEq k l, s => s.I k = s.I l

/-- The jump instruction "if the condition holds then go to `t`". -/
def Cond.instr : Cond → ℕ → MInstr
  | .zero a, t => .jumpEq a t
  | .nonneg a, t => .jumpGe a t
  | .idxEq k l, t => .jumpIdx k l t

/-- Unconditional jump. -/
def goto (t : ℕ) : MInstr := .jumpIdx 0 0 t

theorem step_bop {M : Machine} {pc : ℕ} {o : BOp} (h : M.prog[pc]? = some o.instr) (st : St) :
    M.step (st.at pc) = match o.exec st with
      | some st' => .inl (st'.at (pc + 1))
      | none => .inr none := by
  cases o with
  | arith op d a b =>
    simp only [Machine.step, St.at, h, BOp.instr, BOp.exec]
    cases op.apply? (st.R (st.I a)) (st.R (st.I b)) <;> rfl
  | const d c => simp [Machine.step, St.at, h, BOp.instr, BOp.exec]
  | copy d a => simp [Machine.step, St.at, h, BOp.instr, BOp.exec]
  | inc k => simp [Machine.step, St.at, h, BOp.instr, BOp.exec]
  | dec k => simp [Machine.step, St.at, h, BOp.instr, BOp.exec]

theorem step_cond {M : Machine} {pc t : ℕ} {c : Cond} (h : M.prog[pc]? = some (c.instr t))
    (st : St) : M.step (st.at pc) = .inl (st.at (if c.holds st then t else pc + 1)) := by
  cases c with
  | zero a =>
    by_cases hc : st.R (st.I a) = 0 <;> simp [Machine.step, St.at, h, Cond.instr, Cond.holds, hc]
  | nonneg a =>
    by_cases hc : 0 ≤ st.R (st.I a) <;> simp [Machine.step, St.at, h, Cond.instr, Cond.holds, hc]
  | idxEq k l =>
    by_cases hc : st.I k = st.I l <;> simp [Machine.step, St.at, h, Cond.instr, Cond.holds, hc]

theorem step_goto {M : Machine} {pc t : ℕ} (h : M.prog[pc]? = some (goto t)) (st : St) :
    M.step (st.at pc) = .inl (st.at t) := by
  simp [Machine.step, St.at, h, goto]

/-! ## Structured programs and their compilation -/

/-- Structured programs. -/
inductive Stmt where
  /-- do nothing -/
  | skip
  /-- a basic instruction -/
  | op (o : BOp)
  /-- sequential composition -/
  | seq (s t : Stmt)
  /-- `if c then s else t` -/
  | ite (c : Cond) (s t : Stmt)
  /-- `while ¬ c do s` -/
  | loop (c : Cond) (s : Stmt)
  /-- halt and accept (`true`) or reject (`false`) -/
  | halt (b : Bool)

/-- Length of the compiled code. -/
def Stmt.size : Stmt → ℕ
  | .skip => 0
  | .op _ => 1
  | .seq s t => s.size + t.size
  | .ite _ s t => t.size + s.size + 2
  | .loop _ s => s.size + 2
  | .halt _ => 1

/-- Compilation of a statement to machine code starting at address `p`:
* `ite c s t`: `[if c goto S] ++ t ++ [goto E] ++ (S:) s ++ (E:)`;
* `loop c s`: `(L:) [if c goto E] ++ s ++ [goto L] ++ (E:)`. -/
def Stmt.compile : Stmt → ℕ → List MInstr
  | .skip, _ => []
  | .op o, _ => [o.instr]
  | .seq s t, p => s.compile p ++ t.compile (p + s.size)
  | .ite c s t, p =>
      [c.instr (p + t.size + 2)] ++ t.compile (p + 1) ++ [goto (p + t.size + 2 + s.size)] ++
        s.compile (p + t.size + 2)
  | .loop c s, p => [c.instr (p + s.size + 2)] ++ s.compile (p + 1) ++ [goto p]
  | .halt b, _ => [if b then .accept else .reject]

@[simp] theorem Stmt.length_compile (s : Stmt) (p : ℕ) : (s.compile p).length = s.size := by
  induction s generalizing p with
  | skip => rfl
  | op o => rfl
  | seq s t ihs iht => simp [Stmt.compile, Stmt.size, ihs, iht]
  | ite c s t ihs iht => simp [Stmt.compile, Stmt.size, ihs, iht]; omega
  | loop c s ih => simp [Stmt.compile, Stmt.size, ih]
  | halt b => rfl

/-- The machine running the statement `s` (from address `0`). -/
def Stmt.toMachine (s : Stmt) : Machine := ⟨s.compile 0⟩

/-- The code `code` sits at address `p` of the program of `M`. -/
def Embeds (M : Machine) (p : ℕ) (code : List MInstr) : Prop :=
  ∀ k (h : k < code.length), M.prog[p + k]? = some code[k]

theorem Embeds.append {M : Machine} {p : ℕ} {l₁ l₂ : List MInstr} (h : Embeds M p (l₁ ++ l₂)) :
    Embeds M p l₁ ∧ Embeds M (p + l₁.length) l₂ := by
  constructor
  · intro k hk
    rw [h k (by simp; omega), List.getElem_append_left hk]
  · intro k hk
    rw [Nat.add_assoc, h (l₁.length + k) (by simp; omega),
      List.getElem_append_right (by omega)]
    simp

theorem Embeds.get {M : Machine} {p : ℕ} {i : MInstr} (h : Embeds M p [i]) :
    M.prog[p]? = some i := by
  simpa using h 0 (by simp)

theorem Embeds.get' {M : Machine} {p q : ℕ} {i : MInstr} (h : Embeds M p [i]) (hq : p = q) :
    M.prog[q]? = some i := hq ▸ h.get

theorem Embeds.toMachine (s : Stmt) : Embeds s.toMachine 0 (s.compile 0) := by
  intro k hk
  simp [Stmt.toMachine]

/-! ## Big-step semantics -/

/-- Outcome of a statement: falling through to the end, or halting. -/
inductive Out where
  | next (st : St)
  | halt (st : St) (r : Option Bool)

/-- `Exec s st out t`: started in `st`, `s` ends with `out` after `t` machine steps (for a
halting outcome, not counting the halting step). -/
inductive Exec : Stmt → St → Out → ℕ → Prop where
  | skip (st : St) : Exec .skip st (.next st) 0
  | op_ok {o : BOp} {st st' : St} : o.exec st = some st' → Exec (.op o) st (.next st') 1
  | op_fail {o : BOp} {st : St} : o.exec st = none → Exec (.op o) st (.halt st none) 0
  | seq_next {s u : Stmt} {st st₁ : St} {out : Out} {t₁ t₂ : ℕ} :
      Exec s st (.next st₁) t₁ → Exec u st₁ out t₂ → Exec (.seq s u) st out (t₁ + t₂)
  | seq_halt {s u : Stmt} {st st' : St} {r : Option Bool} {t : ℕ} :
      Exec s st (.halt st' r) t → Exec (.seq s u) st (.halt st' r) t
  | ite_pos {c : Cond} {s u : Stmt} {st : St} {out : Out} {t : ℕ} :
      c.holds st → Exec s st out t → Exec (.ite c s u) st out (t + 1)
  | ite_neg_next {c : Cond} {s u : Stmt} {st st' : St} {t : ℕ} :
      ¬ c.holds st → Exec u st (.next st') t → Exec (.ite c s u) st (.next st') (t + 2)
  | ite_neg_halt {c : Cond} {s u : Stmt} {st st' : St} {r : Option Bool} {t : ℕ} :
      ¬ c.holds st → Exec u st (.halt st' r) t → Exec (.ite c s u) st (.halt st' r) (t + 1)
  | loop_exit {c : Cond} {s : Stmt} {st : St} : c.holds st → Exec (.loop c s) st (.next st) 1
  | loop_next {c : Cond} {s : Stmt} {st st₁ : St} {out : Out} {t₁ t₂ : ℕ} :
      ¬ c.holds st → Exec s st (.next st₁) t₁ → Exec (.loop c s) st₁ out t₂ →
      Exec (.loop c s) st out (t₁ + t₂ + 2)
  | loop_halt {c : Cond} {s : Stmt} {st st' : St} {r : Option Bool} {t : ℕ} :
      ¬ c.holds st → Exec s st (.halt st' r) t → Exec (.loop c s) st (.halt st' r) (t + 1)
  | halt (b : Bool) (st : St) : Exec (.halt b) st (.halt st (some b)) 0

/-- What compiled code does, for an outcome. -/
def Out.Sound (M : Machine) (p size : ℕ) (st : St) (t : ℕ) : Out → Prop
  | .next st' => M.Reaches t (st.at p) (st'.at (p + size))
  | .halt st' r => ∃ pc, M.Reaches t (st.at p) (st'.at pc) ∧ M.step (st'.at pc) = .inr r

/-- **Soundness of the compiler**: compiled code embedded anywhere in a program behaves as
described by `Exec`. -/
theorem Exec.sound {s : Stmt} {st : St} {out : Out} {t : ℕ} (h : Exec s st out t)
    {M : Machine} {p : ℕ} (hM : Embeds M p (s.compile p)) : out.Sound M p s.size st t := by
  induction h generalizing p with
  | skip st => exact Machine.Reaches.refl (M := M) _
  | @op_ok o st st' he =>
    have hs := step_bop (Embeds.get hM) st
    rw [he] at hs
    exact Machine.Reaches.single hs
  | @op_fail o st he =>
    have hs := step_bop (Embeds.get hM) st
    rw [he] at hs
    exact ⟨p, Machine.Reaches.refl (M := M) _, hs⟩
  | @seq_next s u st st₁ out t₁ t₂ _ _ ih₁ ih₂ =>
    have h := Embeds.append hM
    have h₁ : Machine.Reaches M t₁ (st.at p) (st₁.at (p + s.size)) := ih₁ h.1
    have h₂ := ih₂ (p := p + s.size) (by simpa using h.2)
    cases out with
    | next st' =>
      have h₂' : M.Reaches t₂ (st₁.at (p + s.size)) (st'.at (p + s.size + u.size)) := h₂
      show M.Reaches (t₁ + t₂) (st.at p) (st'.at (p + (s.size + u.size)))
      rw [← Nat.add_assoc]
      exact h₁.trans h₂'
    | halt st' r =>
      obtain ⟨pc, hr, hs⟩ := h₂
      exact ⟨pc, h₁.trans hr, hs⟩
  | @seq_halt s u st st' r t _ ih =>
    obtain ⟨pc, hr, hs⟩ := ih (Embeds.append hM).1
    exact ⟨pc, hr, hs⟩
  | @ite_pos c s u st out t hc _ ih =>
    simp only [Stmt.compile] at hM
    have h₁ := Embeds.append hM
    have h₂ := Embeds.append h₁.1
    have h₃ := Embeds.append h₂.1
    have hj := step_cond (Embeds.get h₃.1) st
    simp only [hc, ↓reduceIte] at hj
    have ih' := ih (p := p + u.size + 2) (by simpa [Nat.add_assoc] using h₁.2)
    cases out with
    | next st' =>
      have ih'' : M.Reaches t (st.at (p + u.size + 2)) (st'.at (p + u.size + 2 + s.size)) := ih'
      show M.Reaches (t + 1) (st.at p) (st'.at (p + (u.size + s.size + 2)))
      rw [Nat.add_comm t 1, show p + (u.size + s.size + 2) = p + u.size + 2 + s.size by omega]
      exact (Machine.Reaches.single hj).trans ih''
    | halt st' r =>
      obtain ⟨pc, hr, hs⟩ := ih'
      exact ⟨pc, by rw [Nat.add_comm t 1]; exact (Machine.Reaches.single hj).trans hr, hs⟩
  | @ite_neg_next c s u st st' t hc _ ih =>
    simp only [Stmt.compile] at hM
    have h₁ := Embeds.append hM
    have h₂ := Embeds.append h₁.1
    have h₃ := Embeds.append h₂.1
    have hj := step_cond (Embeds.get h₃.1) st
    simp only [hc, ↓reduceIte] at hj
    have ih' : M.Reaches t (st.at (p + 1)) (st'.at (p + 1 + u.size)) :=
      ih (p := p + 1) (by simpa using h₃.2)
    have hg := step_goto (M := M) (pc := p + 1 + u.size) (t := p + u.size + 2 + s.size)
      (Embeds.get' h₂.2 (by simp; omega)) st'
    show M.Reaches (t + 2) (st.at p) (st'.at (p + (u.size + s.size + 2)))
    rw [show t + 2 = 1 + t + 1 by omega,
      show p + (u.size + s.size + 2) = p + u.size + 2 + s.size by omega]
    exact ((Machine.Reaches.single hj).trans ih').trans (Machine.Reaches.single hg)
  | @ite_neg_halt c s u st st' r t hc _ ih =>
    simp only [Stmt.compile] at hM
    have h₁ := Embeds.append hM
    have h₂ := Embeds.append h₁.1
    have h₃ := Embeds.append h₂.1
    have hj := step_cond (Embeds.get h₃.1) st
    simp only [hc, ↓reduceIte] at hj
    obtain ⟨pc, hr, hs⟩ := ih (p := p + 1) (by simpa using h₃.2)
    exact ⟨pc, by rw [Nat.add_comm t 1]; exact (Machine.Reaches.single hj).trans hr, hs⟩
  | @loop_exit c s st hc =>
    simp only [Stmt.compile] at hM
    have h₁ := Embeds.append hM
    have h₂ := Embeds.append h₁.1
    have hj := step_cond (Embeds.get h₂.1) st
    simp only [hc, ↓reduceIte] at hj
    show M.Reaches 1 (st.at p) (st.at (p + (s.size + 2)))
    rw [show p + (s.size + 2) = p + s.size + 2 by omega]
    exact Machine.Reaches.single hj
  | @loop_next c s st st₁ out t₁ t₂ hc _ _ ih₁ ih₂ =>
    have hM' := hM
    simp only [Stmt.compile] at hM
    have h₁ := Embeds.append hM
    have h₂ := Embeds.append h₁.1
    have hj := step_cond (Embeds.get h₂.1) st
    simp only [hc, ↓reduceIte] at hj
    have ihb : M.Reaches t₁ (st.at (p + 1)) (st₁.at (p + 1 + s.size)) :=
      ih₁ (p := p + 1) (by simpa using h₂.2)
    have hg := step_goto (M := M) (pc := p + 1 + s.size) (t := p) (Embeds.get' h₁.2 (by simp; omega))
      st₁
    have hfirst : M.Reaches (t₁ + 2) (st.at p) (st₁.at p) := by
      rw [show t₁ + 2 = 1 + t₁ + 1 by omega]
      exact ((Machine.Reaches.single hj).trans ihb).trans (Machine.Reaches.single hg)
    have ih₂' := ih₂ hM'
    rw [show t₁ + t₂ + 2 = t₁ + 2 + t₂ by omega]
    cases out with
    | next st' => exact hfirst.trans ih₂'
    | halt st' r =>
      obtain ⟨pc, hr, hs⟩ := ih₂'
      exact ⟨pc, hfirst.trans hr, hs⟩
  | @loop_halt c s st st' r t hc _ ih =>
    simp only [Stmt.compile] at hM
    have h₁ := Embeds.append hM
    have h₂ := Embeds.append h₁.1
    have hj := step_cond (Embeds.get h₂.1) st
    simp only [hc, ↓reduceIte] at hj
    obtain ⟨pc, hr, hs⟩ := ih (p := p + 1) (by simpa using h₂.2)
    exact ⟨pc, by rw [Nat.add_comm t 1]; exact (Machine.Reaches.single hj).trans hr, hs⟩
  | halt b st =>
    refine ⟨p, Machine.Reaches.refl (M := M) _, ?_⟩
    have := Embeds.get (by simpa [Stmt.compile] using hM)
    cases b <;> simp [Machine.step, St.at, this]

/-! ## Hoare-style specifications -/

/-- Postcondition of an outcome: `Q` for falling through, `H` for halting. -/
def Out.Post (Q : St → Prop) (H : St → Option Bool → Prop) : Out → Prop
  | .next st => Q st
  | .halt st r => H st r

/-- `Spec s st Q H T`: started in `st`, the statement `s` ends within `T` steps, either falling
through in a state satisfying `Q` or halting with outcome `r` in a state `st'` with
`H st' r`. -/
def Spec (s : Stmt) (st : St) (Q : St → Prop) (H : St → Option Bool → Prop) (T : ℕ) : Prop :=
  ∃ out t, Exec s st out t ∧ t ≤ T ∧ out.Post Q H

/-- `Runs s st Q T`: started in `st`, `s` falls through within `T` steps in a state satisfying
`Q` (and does not halt). -/
abbrev Runs (s : Stmt) (st : St) (Q : St → Prop) (T : ℕ) : Prop :=
  Spec s st Q (fun _ _ => False) T

/-- `Halts s st H T`: started in `st`, `s` halts within `T` steps (not counting the halting
step) with outcome `r` in a state `st'` with `H st' r`. -/
abbrev Halts (s : Stmt) (st : St) (H : St → Option Bool → Prop) (T : ℕ) : Prop :=
  Spec s st (fun _ => False) H T

namespace Spec

variable {s u : Stmt} {st : St} {Q Q' : St → Prop} {H H' : St → Option Bool → Prop}
  {T T' : ℕ}

theorem mono (h : Spec s st Q H T) (hQ : ∀ st', Q st' → Q' st')
    (hH : ∀ st' r, H st' r → H' st' r) (hT : T ≤ T') : Spec s st Q' H' T' := by
  obtain ⟨out, t, he, ht, hp⟩ := h
  refine ⟨out, t, he, ht.trans hT, ?_⟩
  cases out with
  | next st' => exact hQ _ hp
  | halt st' r => exact hH _ _ hp

theorem mono_time (h : Spec s st Q H T) (hT : T ≤ T') : Spec s st Q H T' :=
  h.mono (fun _ h => h) (fun _ _ h => h) hT

theorem mono_post (h : Spec s st Q H T) (hQ : ∀ st', Q st' → Q' st') : Spec s st Q' H T :=
  h.mono hQ (fun _ _ h => h) le_rfl

theorem skip (h : Q st) : Spec .skip st Q H T :=
  ⟨_, 0, .skip st, Nat.zero_le _, h⟩

theorem op {o : BOp} {st' : St} (he : o.exec st = some st') (h : Q st') (hT : 1 ≤ T) :
    Spec (.op o) st Q H T :=
  ⟨_, 1, .op_ok he, hT, h⟩

theorem halt {b : Bool} (h : H st (some b)) : Spec (.halt b) st Q H T :=
  ⟨_, 0, .halt b st, Nat.zero_le _, h⟩

/-- Sequential composition. -/
theorem seq {Q₁ : St → Prop} {T₁ T₂ : ℕ} (h₁ : Spec s st Q₁ H T₁)
    (h₂ : ∀ st₁, Q₁ st₁ → Spec u st₁ Q H T₂) : Spec (.seq s u) st Q H (T₁ + T₂) := by
  obtain ⟨out, t₁, he₁, ht₁, hp₁⟩ := h₁
  cases out with
  | next st₁ =>
    obtain ⟨out₂, t₂, he₂, ht₂, hp₂⟩ := h₂ st₁ hp₁
    exact ⟨out₂, t₁ + t₂, .seq_next he₁ he₂, Nat.add_le_add ht₁ ht₂, hp₂⟩
  | halt st' r =>
    exact ⟨_, t₁, .seq_halt he₁, ht₁.trans (Nat.le_add_right _ _), hp₁⟩

/-- If-then-else. -/
theorem ite {c : Cond} (hpos : c.holds st → Spec s st Q H T)
    (hneg : ¬ c.holds st → Spec u st Q H T) : Spec (.ite c s u) st Q H (T + 2) := by
  by_cases hc : c.holds st
  · obtain ⟨out, t, he, ht, hp⟩ := hpos hc
    exact ⟨out, t + 1, .ite_pos hc he, by omega, hp⟩
  · obtain ⟨out, t, he, ht, hp⟩ := hneg hc
    cases out with
    | next st' => exact ⟨_, t + 2, .ite_neg_next hc he, by omega, hp⟩
    | halt st' r => exact ⟨_, t + 1, .ite_neg_halt hc he, by omega, hp⟩

theorem ite_pos {c : Cond} (hc : c.holds st) (h : Spec s st Q H T) :
    Spec (.ite c s u) st Q H (T + 2) :=
  ite (fun _ => h) (fun h' => absurd hc h')

theorem ite_neg {c : Cond} (hc : ¬ c.holds st) (h : Spec u st Q H T) :
    Spec (.ite c s u) st Q H (T + 2) :=
  ite (fun h' => absurd h' hc) (fun _ => h)

/-- **While loops** `while ¬ c do s`, with an invariant `Inv q` after `q` iterations, where
`n` is the number of iterations: the condition fails before the iterations `q < n` and holds
after `n` iterations.  The body may also halt (`H`). -/
theorem loop {c : Cond} (Inv : ℕ → St → Prop) (n : ℕ)
    (hstop : ∀ st', Inv n st' → c.holds st')
    (hgo : ∀ q < n, ∀ st', Inv q st' → ¬ c.holds st')
    (hbody : ∀ q < n, ∀ st', Inv q st' → Spec s st' (Inv (q + 1)) H T)
    (h0 : Inv 0 st) : Spec (.loop c s) st (Inv n) H (n * (T + 2) + 1) := by
  suffices ∀ k, ∀ q, q + k = n → ∀ st', Inv q st' →
      Spec (.loop c s) st' (Inv n) H (k * (T + 2) + 1) from this n 0 (by omega) st h0
  intro k
  induction k with
  | zero =>
    intro q hq st' hi
    rw [Nat.add_zero] at hq
    subst hq
    exact ⟨_, 1, .loop_exit (hstop _ hi), by omega, hi⟩
  | succ k ih =>
    intro q hq st' hi
    have hc := hgo q (by omega) st' hi
    obtain ⟨out, t, he, ht, hp⟩ := hbody q (by omega) st' hi
    cases out with
    | next st₁ =>
      obtain ⟨out₂, t₂, he₂, ht₂, hp₂⟩ := ih (q + 1) (by omega) st₁ hp
      refine ⟨out₂, t + t₂ + 2, .loop_next hc he he₂, ?_, hp₂⟩
      calc t + t₂ + 2 ≤ T + (k * (T + 2) + 1) + 2 := by omega
        _ = (k + 1) * (T + 2) + 1 := by ring
    | halt st₁ r =>
      refine ⟨_, t + 1, .loop_halt hc he, ?_, hp⟩
      calc t + 1 ≤ T + 2 := by omega
        _ ≤ (k + 1) * (T + 2) + 1 := by nlinarith

/-- Soundness for compiled code embedded at address `p` of a machine. -/
theorem sound {M : Machine} {p : ℕ} (h : Spec s st Q H T) (hM : Embeds M p (s.compile p)) :
    (∃ st' t, t ≤ T ∧ Q st' ∧ M.Reaches t (st.at p) (st'.at (p + s.size))) ∨
    (∃ st' r t pc, t ≤ T ∧ H st' r ∧ M.Reaches t (st.at p) (st'.at pc) ∧
      M.step (st'.at pc) = .inr r) := by
  obtain ⟨out, t, he, ht, hp⟩ := h
  have := he.sound hM
  cases out with
  | next st' => exact Or.inl ⟨st', t, ht, hp, this⟩
  | halt st' r =>
    obtain ⟨pc, hr, hs⟩ := this
    exact Or.inr ⟨st', r, t, pc, ht, hp, hr, hs⟩

end Spec

/-- **Running a halting program.**  If `s` halts within `T` steps from `st`, then
`s.toMachine.runFinal` from `st` (with program counter `0`) and any fuel `≥ T + 1` returns the
halting configuration and outcome. -/
theorem Halts.runFinal {s : Stmt} {st : St} {H : St → Option Bool → Prop} {T : ℕ}
    (h : Halts s st H T) :
    ∃ st' r pc, H st' r ∧ ∀ j, s.toMachine.runFinal (T + 1 + j) (st.at 0) = some (st'.at pc, r) := by
  rcases h.sound (Embeds.toMachine s) with ⟨_, _, _, hf, _⟩ | ⟨st', r, t, pc, ht, hH, hr, hs⟩
  · exact hf.elim
  refine ⟨st', r, pc, hH, fun j => ?_⟩
  rw [show T + 1 + j = t + 1 + (T - t + j) by omega]
  exact hr.runFinal_halt hs _

/-- **Running a halting program**: the outcome of `s.toMachine.run`. -/
theorem Halts.run {s : Stmt} {st : St} {H : St → Option Bool → Prop} {T : ℕ}
    (h : Halts s st H T) :
    ∃ st' r, H st' r ∧ ∀ j, s.toMachine.run (T + 1 + j) (st.at 0) = some r := by
  rcases h.sound (Embeds.toMachine s) with ⟨_, _, _, hf, _⟩ | ⟨st', r, t, pc, ht, hH, hr, hs⟩
  · exact hf.elim
  refine ⟨st', r, hH, fun j => ?_⟩
  rw [show T + 1 + j = t + 1 + (T - t + j) by omega]
  exact hr.run_halt hs _

/-! ## Derived statements -/

/-- Sequential composition of a list of statements. -/
def Stmt.seqs : List Stmt → Stmt
  | [] => .skip
  | s :: l => .seq s (Stmt.seqs l)

/-- `n` copies of a statement in sequence. -/
def Stmt.rep (s : Stmt) : ℕ → Stmt
  | 0 => .skip
  | n + 1 => .seq s (s.rep n)

/-- Unconditional "if" with an empty else branch. -/
def Stmt.ifThen (c : Cond) (s : Stmt) : Stmt := .ite c s .skip

/-- `if ¬ c then s`. -/
def Stmt.unless (c : Cond) (s : Stmt) : Stmt := .ite c .skip s

namespace Spec

variable {s : Stmt} {st : St} {Q : St → Prop} {H : St → Option Bool → Prop} {T : ℕ}

theorem ifThen {c : Cond} (hpos : c.holds st → Spec s st Q H T) (hneg : ¬ c.holds st → Q st) :
    Spec (Stmt.ifThen c s) st Q H (T + 2) :=
  ite hpos fun h => skip (hneg h)

theorem «unless» {c : Cond} (hpos : c.holds st → Q st) (hneg : ¬ c.holds st → Spec s st Q H T) :
    Spec (Stmt.unless c s) st Q H (T + 2) :=
  ite (fun h => skip (hpos h)) hneg

/-- `n` repetitions of a statement, with an invariant indexed by the number of repetitions. -/
theorem rep (Inv : ℕ → St → Prop) (n : ℕ)
    (hbody : ∀ q < n, ∀ st', Inv q st' → Spec s st' (Inv (q + 1)) H T) (h0 : Inv 0 st) :
    Spec (s.rep n) st (Inv n) H (n * T) := by
  suffices ∀ k, ∀ q, q + k = n → ∀ st', Inv q st' → Spec (s.rep k) st' (Inv n) H (k * T) from
    this n 0 (by omega) st h0
  intro k
  induction k with
  | zero =>
    intro q hq st' hi
    rw [Nat.add_zero] at hq
    subst hq
    exact skip hi
  | succ k ih =>
    intro q hq st' hi
    have := (hbody q (by omega) st' hi).seq (fun st₁ h₁ => ih (q + 1) (by omega) st₁ h₁)
    exact this.mono_time (by ring_nf; omega)

/-- Sequential composition with an exactly known intermediate state. -/
theorem seq_eq {u : Stmt} {st₁ : St} {T₁ T₂ : ℕ} (h₁ : Spec s st (· = st₁) H T₁)
    (h₂ : Spec u st₁ Q H T₂) : Spec (.seq s u) st Q H (T₁ + T₂) :=
  h₁.seq fun _ h => h ▸ h₂

/-- A statement that falls through can be used in any specification. -/
theorem of_runs (h : Runs s st Q T) : Spec s st Q H T :=
  h.mono (fun _ h => h) (fun _ _ h => h.elim) le_rfl

theorem seqs_nil : Spec (Stmt.seqs []) st Q H T ↔ Spec .skip st Q H T := Iff.rfl

end Spec

@[simp] theorem Stmt.seqs_cons (s : Stmt) (l : List Stmt) :
    Stmt.seqs (s :: l) = .seq s (Stmt.seqs l) := rfl

/-! ## Effects of basic instructions -/

@[simp] theorem BOp.exec_const (d : ℕ) (c : ℝ) (st : St) :
    (BOp.const d c).exec st = some ⟨Function.update st.R (st.I d) c, st.I⟩ := rfl

@[simp] theorem BOp.exec_copy (d a : ℕ) (st : St) :
    (BOp.copy d a).exec st = some ⟨Function.update st.R (st.I d) (st.R (st.I a)), st.I⟩ := rfl

@[simp] theorem BOp.exec_inc (k : ℕ) (st : St) :
    (BOp.inc k).exec st = some ⟨st.R, Function.update st.I k (st.I k + 1)⟩ := rfl

@[simp] theorem BOp.exec_dec (k : ℕ) (st : St) :
    (BOp.dec k).exec st = some ⟨st.R, Function.update st.I k (st.I k - 1)⟩ := rfl

@[simp] theorem BOp.exec_add (d a b : ℕ) (st : St) :
    (BOp.arith .add d a b).exec st =
      some ⟨Function.update st.R (st.I d) (st.R (st.I a) + st.R (st.I b)), st.I⟩ := rfl

@[simp] theorem BOp.exec_sub (d a b : ℕ) (st : St) :
    (BOp.arith .sub d a b).exec st =
      some ⟨Function.update st.R (st.I d) (st.R (st.I a) - st.R (st.I b)), st.I⟩ := rfl

@[simp] theorem BOp.exec_mul (d a b : ℕ) (st : St) :
    (BOp.arith .mul d a b).exec st =
      some ⟨Function.update st.R (st.I d) (st.R (st.I a) * st.R (st.I b)), st.I⟩ := rfl

@[simp] theorem Cond.holds_zero (a : ℕ) (st : St) :
    (Cond.zero a).holds st ↔ st.R (st.I a) = 0 := Iff.rfl

@[simp] theorem Cond.holds_nonneg (a : ℕ) (st : St) :
    (Cond.nonneg a).holds st ↔ 0 ≤ st.R (st.I a) := Iff.rfl

@[simp] theorem Cond.holds_idxEq (k l : ℕ) (st : St) :
    (Cond.idxEq k l).holds st ↔ st.I k = st.I l := Iff.rfl

namespace Spec

variable {st : St} {Q : St → Prop} {H : St → Option Bool → Prop} {T : ℕ}

theorem const {d : ℕ} {c : ℝ} (h : Q ⟨Function.update st.R (st.I d) c, st.I⟩) (hT : 1 ≤ T) :
    Spec (.op (.const d c)) st Q H T := op rfl h hT

theorem copy {d a : ℕ} (h : Q ⟨Function.update st.R (st.I d) (st.R (st.I a)), st.I⟩)
    (hT : 1 ≤ T) : Spec (.op (.copy d a)) st Q H T := op rfl h hT

theorem inc {k : ℕ} (h : Q ⟨st.R, Function.update st.I k (st.I k + 1)⟩) (hT : 1 ≤ T) :
    Spec (.op (.inc k)) st Q H T := op rfl h hT

theorem dec {k : ℕ} (h : Q ⟨st.R, Function.update st.I k (st.I k - 1)⟩) (hT : 1 ≤ T) :
    Spec (.op (.dec k)) st Q H T := op rfl h hT

theorem add {d a b : ℕ}
    (h : Q ⟨Function.update st.R (st.I d) (st.R (st.I a) + st.R (st.I b)), st.I⟩) (hT : 1 ≤ T) :
    Spec (.op (.arith .add d a b)) st Q H T := op rfl h hT

theorem sub {d a b : ℕ}
    (h : Q ⟨Function.update st.R (st.I d) (st.R (st.I a) - st.R (st.I b)), st.I⟩) (hT : 1 ≤ T) :
    Spec (.op (.arith .sub d a b)) st Q H T := op rfl h hT

theorem mul {d a b : ℕ}
    (h : Q ⟨Function.update st.R (st.I d) (st.R (st.I a) * st.R (st.I b)), st.I⟩) (hT : 1 ≤ T) :
    Spec (.op (.arith .mul d a b)) st Q H T := op rfl h hT

/-- A basic instruction followed by a statement (the intermediate state is computed by
`rfl` from `BOp.exec`). -/
theorem seq_op {o : BOp} {u : Stmt} {st' : St} (he : o.exec st = some st')
    (h : Spec u st' Q H T) : Spec (.seq (.op o) u) st Q H (1 + T) :=
  seq (Q₁ := (· = st')) (op he rfl le_rfl) fun _ h' => h' ▸ h

end Spec

/-! ## Index register subroutines

Convention: scratch index registers are `0` before and after each subroutine, so that the
index registers are unchanged by a subroutine call. -/

/-- `I k := I a`, for `I k = 0` initially. -/
def loadIdx (k a : ℕ) : Stmt := .loop (.idxEq k a) (.op (.inc k))

/-- `I k := 0`, given an index register `z` with `I z = 0`. -/
def clearIdx (k z : ℕ) : Stmt := .loop (.idxEq k z) (.op (.dec k))

theorem loadIdx_spec {st : St} {k a : ℕ} (hka : k ≠ a) (hk : st.I k = 0) :
    Runs (loadIdx k a) st (· = ⟨st.R, Function.update st.I k (st.I a)⟩) (3 * st.I a + 1) := by
  have h := Spec.loop (s := .op (.inc k)) (c := .idxEq k a) (H := fun _ _ => False) (T := 1)
    (st := st) (fun q st' => st' = ⟨st.R, Function.update st.I k q⟩) (st.I a) ?_ ?_ ?_ ?_
  · exact h.mono_time (Nat.le_of_eq (by ring))
  · rintro st' rfl
    simp [Function.update_of_ne hka.symm]
  · rintro q hq st' rfl
    simp [Function.update_of_ne hka.symm]
    omega
  · rintro q - st' rfl
    exact Spec.inc (by simp) le_rfl
  · rw [← hk, Function.update_eq_self]

theorem clearIdx_spec {st : St} {k z : ℕ} (hkz : k ≠ z) (hz : st.I z = 0) :
    Runs (clearIdx k z) st (· = ⟨st.R, Function.update st.I k 0⟩) (3 * st.I k + 1) := by
  have h := Spec.loop (s := .op (.dec k)) (c := .idxEq k z) (H := fun _ _ => False) (T := 1)
    (st := st) (fun q st' => st' = ⟨st.R, Function.update st.I k (st.I k - q)⟩) (st.I k)
    ?_ ?_ ?_ ?_
  · refine (h.mono_time (Nat.le_of_eq (by ring))).mono_post ?_
    rintro st' rfl
    simp
  · rintro st' rfl
    simp [Function.update_of_ne hkz.symm, hz]
  · rintro q hq st' rfl
    simp [Function.update_of_ne hkz.symm, hz]
    omega
  · rintro q - st' rfl
    refine Spec.dec ?_ le_rfl
    simp only [Function.update_self, Function.update_idem]
    congr 2
  · simp

/-- `I k := I a` for arbitrary initial `I k` (`k ≠ a`, `k ≠ z`, `I z = 0`). -/
def setIdx (k a z : ℕ) : Stmt := .seq (clearIdx k z) (loadIdx k a)

theorem setIdx_spec {st : St} {k a z : ℕ} (hka : k ≠ a) (hkz : k ≠ z) (hz : st.I z = 0) :
    Runs (setIdx k a z) st (· = ⟨st.R, Function.update st.I k (st.I a)⟩)
      (3 * st.I k + 3 * st.I a + 2) := by
  refine ((clearIdx_spec hkz hz).seq_eq (loadIdx_spec hka (by simp))).mono_time ?_ |>.mono_post ?_
  · simp [Function.update_of_ne hka.symm]; omega
  · rintro st' rfl
    simp [Function.update_of_ne hka.symm]

/-- Add the constants `c` to the index registers `k`, for the pairs `(k, c)` of the list. -/
def addConsts : List (ℕ × ℕ) → Stmt
  | [] => .skip
  | (k, c) :: l => .seq ((Stmt.op (.inc k)).rep c) (addConsts l)

/-- The total amount added to the register `k` by `addConsts l`. -/
def addAmt (l : List (ℕ × ℕ)) (k : ℕ) : ℕ := ((l.filter (·.1 = k)).map (·.2)).sum

@[simp] theorem addAmt_nil (k : ℕ) : addAmt [] k = 0 := rfl

theorem addAmt_cons (a : ℕ × ℕ) (l : List (ℕ × ℕ)) (k : ℕ) :
    addAmt (a :: l) k = (if a.1 = k then a.2 else 0) + addAmt l k := by
  unfold addAmt
  by_cases h : a.1 = k <;> simp [h]

theorem addConsts_spec (l : List (ℕ × ℕ)) (st : St) :
    Runs (addConsts l) st (· = ⟨st.R, fun k => st.I k + addAmt l k⟩) (l.map (·.2)).sum := by
  induction l generalizing st with
  | nil => exact Spec.skip (by simp)
  | cons a l ih =>
    obtain ⟨k, c⟩ := a
    have hrep : Runs ((Stmt.op (.inc k)).rep c) st
        (· = ⟨st.R, Function.update st.I k (st.I k + c)⟩) (c * 1) := by
      have := Spec.rep (s := .op (.inc k)) (H := fun _ _ => False) (T := 1) (st := st)
        (fun q st' => st' = ⟨st.R, Function.update st.I k (st.I k + q)⟩) c
        (fun q _ st' h => Spec.inc (by subst h; simp [Nat.add_assoc]) le_rfl)
        (by simp)
      exact this
    refine (hrep.seq_eq (ih _)).mono_time (by simp) |>.mono_post ?_
    rintro st' rfl
    ext k' <;> simp only [addAmt_cons, Function.update_apply]
    by_cases h : k' = k
    · subst h; simp; omega
    · simp [h, Ne.symm h]

/-! ## Real register subroutines -/

/-- `R` with the range `[b, b + n)` replaced by a copy of `[a, a + n)`. -/
def copyR (R : ℕ → ℝ) (a b n : ℕ) : ℕ → ℝ :=
  fun k => if b ≤ k ∧ k < b + n then R (a + (k - b)) else R k

/-- `R` with the range `[b, b + n)` filled with `v`. -/
def fillR (R : ℕ → ℝ) (b n : ℕ) (v : ℝ) : ℕ → ℝ :=
  fun k => if b ≤ k ∧ k < b + n then v else R k

theorem copyR_of_mem {R : ℕ → ℝ} {a b n k : ℕ} (h : b ≤ k ∧ k < b + n) :
    copyR R a b n k = R (a + (k - b)) := ite_eq_left h

theorem copyR_of_not_mem {R : ℕ → ℝ} {a b n k : ℕ} (h : k < b ∨ b + n ≤ k) :
    copyR R a b n k = R k := ite_eq_right (by omega)

theorem fillR_of_mem {R : ℕ → ℝ} {b n k : ℕ} {v : ℝ} (h : b ≤ k ∧ k < b + n) :
    fillR R b n v k = v := ite_eq_left h

theorem fillR_of_not_mem {R : ℕ → ℝ} {b n k : ℕ} {v : ℝ} (h : k < b ∨ b + n ≤ k) :
    fillR R b n v k = R k := ite_eq_right (by omega)

@[simp] theorem copyR_zero (R : ℕ → ℝ) (a b : ℕ) : copyR R a b 0 = R := by
  funext k; simp [copyR]

@[simp] theorem fillR_zero (R : ℕ → ℝ) (b : ℕ) (v : ℝ) : fillR R b 0 v = R := by
  funext k; simp [fillR]

/-- Copy the `I len` real registers starting at `I src` to those starting at `I dst`
(scratch registers `p q c`, `I z = 0`). -/
def copyRange (src dst len p q c z : ℕ) : Stmt :=
  .seqs [loadIdx p src, loadIdx q dst,
    .loop (.idxEq c len) (.seqs [.op (.copy q p), .op (.inc p), .op (.inc q), .op (.inc c)]),
    clearIdx p z, clearIdx q z, clearIdx c z]

/-- Fill the `I len` real registers starting at `I dst` with `v` (scratch `q c`, `I z = 0`). -/
def fillRange (dst len : ℕ) (v : ℝ) (q c z : ℕ) : Stmt :=
  .seqs [loadIdx q dst,
    .loop (.idxEq c len) (.seqs [.op (.const q v), .op (.inc q), .op (.inc c)]),
    clearIdx q z, clearIdx c z]

theorem copyRange_spec {st : St} {src dst len p q c z : ℕ}
    (hpq : p ≠ q) (hpc : p ≠ c) (hqc : q ≠ c) (hpz : p ≠ z) (hqz : q ≠ z) (hcz : c ≠ z)
    (hsrc : src ≠ p ∧ src ≠ q ∧ src ≠ c) (hdst : dst ≠ p ∧ dst ≠ q ∧ dst ≠ c)
    (hlen : len ≠ p ∧ len ≠ q ∧ len ≠ c)
    (hp : st.I p = 0) (hq : st.I q = 0) (hc : st.I c = 0) (hz : st.I z = 0)
    (hov : st.I dst ≤ st.I src ∨ st.I src + st.I len ≤ st.I dst) :
    Runs (copyRange src dst len p q c z) st
      (· = ⟨copyR st.R (st.I src) (st.I dst) (st.I len), st.I⟩)
      (6 * st.I src + 6 * st.I dst + 15 * st.I len + 6) := by
  obtain ⟨R₀, I₀⟩ := st
  simp only at hp hq hc hz hov ⊢
  -- index registers during the loop
  let J : ℕ → ℕ → ℕ := fun j k =>
    if k = p then I₀ src + j else if k = q then I₀ dst + j else if k = c then j else I₀ k
  have hJ : ∀ j k, k ≠ p → k ≠ q → k ≠ c → J j k = I₀ k := by
    intro j k h1 h2 h3; simp [J, h1, h2, h3]
  have hJp : ∀ j, J j p = I₀ src + j := by intro j; simp [J]
  have hJq : ∀ j, J j q = I₀ dst + j := by intro j; simp [J, hpq.symm]
  have hJc : ∀ j, J j c = j := by intro j; simp [J, hpc.symm, hqc.symm]
  have hJlen : ∀ j, J j len = I₀ len := fun j => hJ j len hlen.1 hlen.2.1 hlen.2.2
  have h2 := loadIdx_spec (st := ⟨R₀, Function.update I₀ p (I₀ src)⟩) (k := q) (a := dst)
    hdst.2.1.symm (by simp [Function.update_of_ne hpq.symm, hq])
  have hloop : Runs (.loop (.idxEq c len)
      (.seqs [.op (.copy q p), .op (.inc p), .op (.inc q), .op (.inc c)])) ⟨R₀, J 0⟩
      (· = ⟨copyR R₀ (I₀ src) (I₀ dst) (I₀ len), J (I₀ len)⟩) (I₀ len * (4 + 2) + 1) := by
    refine Spec.loop (fun j st' => st' = ⟨copyR R₀ (I₀ src) (I₀ dst) j, J j⟩) (I₀ len)
      ?_ ?_ ?_ (by simp)
    · rintro st' rfl
      simp [hJc, hJlen]
    · rintro j hj st' rfl
      simp [hJc, hJlen]
      omega
    · rintro j hj st' rfl
      refine Spec.seq_op rfl (Spec.seq_op rfl (Spec.seq_op rfl (Spec.seq_op rfl
        (Spec.skip (T := 0) ?_)))) |>.mono_time (by norm_num)
      simp only [hJp, hJq, hJc, Function.update_apply, hpq.symm, hpc.symm, hqc.symm, ite_false]
      ext k
      · simp only [Function.update_apply, copyR]
        split_ifs <;> first | omega | (congr 1; omega) | rfl
      · simp only [Function.update_apply, J]
        split_ifs <;> omega
  have hz' : J (I₀ len) z = 0 := by rw [hJ _ z hpz.symm hqz.symm hcz.symm, hz]
  have hJ0 : (⟨R₀, Function.update (Function.update I₀ p (I₀ src)) q
      (Function.update I₀ p (I₀ src) dst)⟩ : St) = ⟨R₀, J 0⟩ := by
    congr 1
    funext k
    simp only [Function.update_apply, J, ite_eq_right hdst.1]
    split_ifs <;> subst_vars <;> simp_all
  set Rc := copyR R₀ (I₀ src) (I₀ dst) (I₀ len)
  set n := I₀ len
  have s6 : Runs (Stmt.seqs [])
      ⟨Rc, Function.update (Function.update (Function.update (J n) p 0) q 0) c 0⟩
      (· = ⟨Rc, I₀⟩) 0 := by
    refine Spec.skip ?_
    congr 1
    funext k
    simp only [Function.update_apply, J]
    split_ifs <;> subst_vars <;> simp_all
  have s5 := Spec.seq_eq (clearIdx_spec (st := ⟨Rc, Function.update (Function.update (J n) p 0)
    q 0⟩) hcz (by simp [Function.update_of_ne hpz.symm, Function.update_of_ne hqz.symm, hz'])) s6
  have s4 := Spec.seq_eq (clearIdx_spec (st := ⟨Rc, Function.update (J n) p 0⟩) hqz
    (by simp [Function.update_of_ne hpz.symm, hz'])) s5
  have s3 := Spec.seq_eq (clearIdx_spec (st := ⟨Rc, J n⟩) hpz hz') s4
  have s2 := Spec.seq_eq hloop s3
  have s1 := Spec.seq_eq (hJ0 ▸ h2) s2
  have s0 := Spec.seq_eq (loadIdx_spec (st := ⟨R₀, I₀⟩) hsrc.1.symm hp) s1
  refine s0.mono_time ?_
  simp only [Function.update_of_ne hpq.symm, Function.update_of_ne hpc.symm,
    Function.update_of_ne hqc.symm, Function.update_of_ne hdst.1, hJp, hJq, hJc]
  omega

theorem fillRange_spec {st : St} {dst len : ℕ} {v : ℝ} {q c z : ℕ}
    (hqc : q ≠ c) (hqz : q ≠ z) (hcz : c ≠ z)
    (hdst : dst ≠ q ∧ dst ≠ c) (hlen : len ≠ q ∧ len ≠ c)
    (hq : st.I q = 0) (hc : st.I c = 0) (hz : st.I z = 0) :
    Runs (fillRange dst len v q c z) st
      (· = ⟨fillR st.R (st.I dst) (st.I len) v, st.I⟩)
      (6 * st.I dst + 11 * st.I len + 4) := by
  obtain ⟨R₀, I₀⟩ := st
  simp only at hq hc hz ⊢
  let J : ℕ → ℕ → ℕ := fun j k => if k = q then I₀ dst + j else if k = c then j else I₀ k
  have hJ : ∀ j k, k ≠ q → k ≠ c → J j k = I₀ k := by
    intro j k h1 h2; simp [J, h1, h2]
  have hJq : ∀ j, J j q = I₀ dst + j := by intro j; simp [J]
  have hJc : ∀ j, J j c = j := by intro j; simp [J, hqc.symm]
  have hJlen : ∀ j, J j len = I₀ len := fun j => hJ j len hlen.1 hlen.2
  have hloop : Runs (.loop (.idxEq c len)
      (.seqs [.op (.const q v), .op (.inc q), .op (.inc c)])) ⟨R₀, J 0⟩
      (· = ⟨fillR R₀ (I₀ dst) (I₀ len) v, J (I₀ len)⟩) (I₀ len * (3 + 2) + 1) := by
    refine Spec.loop (fun j st' => st' = ⟨fillR R₀ (I₀ dst) j v, J j⟩) (I₀ len)
      ?_ ?_ ?_ (by simp)
    · rintro st' rfl
      simp [hJc, hJlen]
    · rintro j hj st' rfl
      simp [hJc, hJlen]
      omega
    · rintro j hj st' rfl
      refine Spec.seq_op rfl (Spec.seq_op rfl (Spec.seq_op rfl
        (Spec.skip (T := 0) ?_))) |>.mono_time (by norm_num)
      simp only [hJq, hJc, Function.update_apply, hqc.symm, ite_false]
      ext k
      · simp only [Function.update_apply, fillR]
        split_ifs <;> first | omega | rfl
      · simp only [Function.update_apply, J]
        split_ifs <;> omega
  have hz' : J (I₀ len) z = 0 := by rw [hJ _ z hqz.symm hcz.symm, hz]
  have hJ0 : (⟨R₀, Function.update I₀ q (I₀ dst)⟩ : St) = ⟨R₀, J 0⟩ := by
    congr 1
    funext k
    simp only [Function.update_apply, J]
    split_ifs <;> subst_vars <;> simp_all
  set Rc := fillR R₀ (I₀ dst) (I₀ len) v
  set n := I₀ len
  have s4 : Runs (Stmt.seqs []) ⟨Rc, Function.update (Function.update (J n) q 0) c 0⟩
      (· = ⟨Rc, I₀⟩) 0 := by
    refine Spec.skip ?_
    congr 1
    funext k
    simp only [Function.update_apply, J]
    split_ifs <;> subst_vars <;> simp_all
  have s3 := Spec.seq_eq (clearIdx_spec (st := ⟨Rc, Function.update (J n) q 0⟩) hcz
    (by simp [Function.update_of_ne hqz.symm, hz'])) s4
  have s2 := Spec.seq_eq (clearIdx_spec (st := ⟨Rc, J n⟩) hqz hz') s3
  have s1 := Spec.seq_eq hloop s2
  have s0 := Spec.seq_eq (hJ0 ▸ loadIdx_spec (st := ⟨R₀, I₀⟩) hdst.1.symm hq) s1
  refine s0.mono_time ?_
  simp only [Function.update_of_ne hqc.symm, hJq, hJc]
  omega

/-! ## Scanning loops -/

/-- The index registers during iteration `j` of `forScan a b len p q c z body`. -/
def scanIdx (I : ℕ → ℕ) (a b p q c j : ℕ) : ℕ → ℕ :=
  fun k => if k = p then I a + j else if k = q then I b + j else if k = c then j else I k

section scanIdx

variable {I : ℕ → ℕ} {a b p q c : ℕ}

theorem scanIdx_p (j : ℕ) : scanIdx I a b p q c j p = I a + j := by simp [scanIdx]

theorem scanIdx_q (hpq : p ≠ q) (j : ℕ) : scanIdx I a b p q c j q = I b + j := by
  simp [scanIdx, hpq.symm]

theorem scanIdx_c (hpc : p ≠ c) (hqc : q ≠ c) (j : ℕ) : scanIdx I a b p q c j c = j := by
  simp [scanIdx, hpc.symm, hqc.symm]

theorem scanIdx_other {k : ℕ} (hp : k ≠ p) (hq : k ≠ q) (hc : k ≠ c) (j : ℕ) :
    scanIdx I a b p q c j k = I k := by simp [scanIdx, hp, hq, hc]

theorem scanIdx_step (hpq : p ≠ q) (hpc : p ≠ c) (hqc : q ≠ c) (j : ℕ) :
    Function.update (Function.update (Function.update (scanIdx I a b p q c j) p (I a + j + 1))
      q (I b + j + 1)) c (j + 1) = scanIdx I a b p q c (j + 1) := by
  funext k
  by_cases h1 : k = c
  · subst h1; simp [scanIdx_c hpc hqc]
  by_cases h2 : k = q
  · subst h2; simp [h1, scanIdx_q hpq, Nat.add_assoc]
  by_cases h3 : k = p
  · subst h3; simp [h1, h2, scanIdx_p, Nat.add_assoc]
  simp [h1, h2, h3, scanIdx_other h3 h2 h1]

theorem scanIdx_zero (hpq : p ≠ q) (hpc : p ≠ c) (hqc : q ≠ c) (hbp : b ≠ p) (hc : I c = 0) :
    Function.update (Function.update I p (I a)) q (Function.update I p (I a) b) =
      scanIdx I a b p q c 0 := by
  funext k
  rw [Function.update_of_ne hbp]
  by_cases h2 : k = q
  · subst h2; simp [scanIdx_q hpq]
  by_cases h3 : k = p
  · subst h3; simp [h2, scanIdx_p]
  by_cases h1 : k = c
  · subst h1; simp [h2, h3, scanIdx_c hpc hqc, hc]
  simp [h2, h3, scanIdx_other h3 h2 h1]

theorem scanIdx_clear (hpq : p ≠ q) (hpc : p ≠ c) (hqc : q ≠ c) (hp : I p = 0) (hq : I q = 0)
    (hc : I c = 0) (j : ℕ) :
    Function.update (Function.update (Function.update (scanIdx I a b p q c j) p 0) q 0) c 0 =
      I := by
  funext k
  by_cases h1 : k = c
  · subst h1; simp [hc]
  by_cases h2 : k = q
  · subst h2; simp [h1, hq]
  by_cases h3 : k = p
  · subst h3; simp [h1, h2, hp]
  simp [h1, h2, h3, scanIdx_other h3 h2 h1]

end scanIdx

/-- `for j < I len do body`, where during iteration `j` the pointer registers hold
`I p = I a + j`, `I q = I b + j` and the counter `I c = j` (scratch `p q c`, `I z = 0`).  Used to
scan one or two ranges of real registers in parallel. -/
def forScan (a b len p q c z : ℕ) (body : Stmt) : Stmt :=
  .seqs [loadIdx p a, loadIdx q b,
    .loop (.idxEq c len) (.seqs [body, .op (.inc p), .op (.inc q), .op (.inc c)]),
    clearIdx p z, clearIdx q z, clearIdx c z]

/-- Specification of `forScan` with an invariant `Inv j` on the real registers after `j`
iterations; the body must restore the index registers. -/
theorem forScan_spec {st : St} {a b len p q c z : ℕ} {body : Stmt} (Inv : ℕ → (ℕ → ℝ) → Prop)
    (T : ℕ) (hpq : p ≠ q) (hpc : p ≠ c) (hqc : q ≠ c) (hpz : p ≠ z) (hqz : q ≠ z) (hcz : c ≠ z)
    (ha : a ≠ p ∧ a ≠ q ∧ a ≠ c) (hb : b ≠ p ∧ b ≠ q ∧ b ≠ c)
    (hlen : len ≠ p ∧ len ≠ q ∧ len ≠ c)
    (hp : st.I p = 0) (hq : st.I q = 0) (hc : st.I c = 0) (hz : st.I z = 0)
    (hbody : ∀ j < st.I len, ∀ R, Inv j R →
      Runs body ⟨R, scanIdx st.I a b p q c j⟩
        (fun st' => st'.I = scanIdx st.I a b p q c j ∧ Inv (j + 1) st'.R) T)
    (h0 : Inv 0 st.R) :
    Runs (forScan a b len p q c z body) st (fun st' => st'.I = st.I ∧ Inv (st.I len) st'.R)
      (6 * st.I a + 6 * st.I b + st.I len * (T + 14) + 6) := by
  obtain ⟨R₀, I₀⟩ := st
  simp only at hp hq hc hz hbody h0 ⊢
  have hJc : ∀ j, scanIdx I₀ a b p q c j c = j := scanIdx_c hpc hqc
  have hJlen : ∀ j, scanIdx I₀ a b p q c j len = I₀ len :=
    scanIdx_other hlen.1 hlen.2.1 hlen.2.2
  have h2 := loadIdx_spec (st := ⟨R₀, Function.update I₀ p (I₀ a)⟩) (k := q) (a := b)
    hb.2.1.symm (by simp [Function.update_of_ne hpq.symm, hq])
  have hloop : Runs (.loop (.idxEq c len)
      (.seqs [body, .op (.inc p), .op (.inc q), .op (.inc c)])) ⟨R₀, scanIdx I₀ a b p q c 0⟩
      (fun st' => st'.I = scanIdx I₀ a b p q c (I₀ len) ∧ Inv (I₀ len) st'.R)
      (I₀ len * ((T + 3) + 2) + 1) := by
    refine Spec.loop (fun j st' => st'.I = scanIdx I₀ a b p q c j ∧ Inv j st'.R) (I₀ len)
      ?_ ?_ ?_ ⟨rfl, h0⟩
    · rintro ⟨R', I'⟩ ⟨hI', -⟩
      simp only at hI'
      subst hI'
      simp [hJc, hJlen]
    · rintro j hj ⟨R', I'⟩ ⟨hI', -⟩
      simp only at hI'
      subst hI'
      simp only [Cond.holds_idxEq, hJc, hJlen]
      omega
    · rintro j hj ⟨R', I'⟩ ⟨hI', hinv⟩
      simp only at hI' hinv
      subst hI'
      refine Spec.seq (hbody j hj R' hinv) fun ⟨R'', I''⟩ ⟨hI'', hinv''⟩ => ?_
      simp only at hI'' hinv''
      subst hI''
      refine Spec.seq_op rfl (Spec.seq_op rfl (Spec.seq_op rfl
        (Spec.skip (T := 0) ⟨?_, hinv''⟩))) |>.mono_time (by omega)
      simp only [Function.update_of_ne hpq.symm,
        Function.update_of_ne hpc.symm, Function.update_of_ne hqc.symm, scanIdx_p,
        scanIdx_q hpq, hJc]
      exact scanIdx_step hpq hpc hqc j
  have hz' : scanIdx I₀ a b p q c (I₀ len) z = 0 := by
    rw [scanIdx_other hpz.symm hqz.symm hcz.symm, hz]
  have hJ0 : (⟨R₀, Function.update (Function.update I₀ p (I₀ a)) q
      (Function.update I₀ p (I₀ a) b)⟩ : St) = ⟨R₀, scanIdx I₀ a b p q c 0⟩ := by
    rw [scanIdx_zero hpq hpc hqc hb.1 hc]
  set n := I₀ len
  set Jn := scanIdx I₀ a b p q c n
  have hfin : ∀ R' : ℕ → ℝ, Inv n R' →
      Runs (Stmt.seqs [clearIdx p z, clearIdx q z, clearIdx c z]) ⟨R', Jn⟩
        (fun st' => st'.I = I₀ ∧ Inv n st'.R) (3 * Jn p + 1 +
          (3 * Function.update Jn p 0 q + 1 +
            (3 * Function.update (Function.update Jn p 0) q 0 c + 1 + 0))) := by
    intro R' hR'
    have s4 : Runs (Stmt.seqs [])
        ⟨R', Function.update (Function.update (Function.update Jn p 0) q 0) c 0⟩
        (fun st' => st'.I = I₀ ∧ Inv n st'.R) 0 :=
      Spec.skip ⟨scanIdx_clear hpq hpc hqc hp hq hc n, hR'⟩
    have s3 := Spec.seq_eq (clearIdx_spec (st := ⟨R', Function.update (Function.update Jn p 0)
      q 0⟩) hcz (by simp [Function.update_of_ne hpz.symm, Function.update_of_ne hqz.symm, Jn,
        hz'])) s4
    have s2 := Spec.seq_eq (clearIdx_spec (st := ⟨R', Function.update Jn p 0⟩) hqz
      (by simp [Function.update_of_ne hpz.symm, Jn, hz'])) s3
    exact Spec.seq_eq (clearIdx_spec (st := ⟨R', Jn⟩) hpz hz') s2
  have s1 := hloop.seq fun ⟨R', I'⟩ ⟨hI', hR'⟩ => by
    simp only at hI' hR'
    subst hI'
    exact hfin R' hR'
  have s0 := Spec.seq_eq (hJ0 ▸ h2) s1
  have s := Spec.seq_eq (loadIdx_spec (st := ⟨R₀, I₀⟩) ha.1.symm hp) s0
  refine s.mono_time ?_
  simp only [Function.update_of_ne hb.1, Function.update_of_ne hpq.symm,
    Function.update_of_ne hpc.symm, Function.update_of_ne hqc.symm, Jn, scanIdx_p,
    scanIdx_q hpq, hJc]
  nlinarith

/-! ## Bit fields

A bit field of width `w` at address `b` holds the binary digits of a number `N` (least
significant first), as reals `0`, `1`, in the registers `b, …, b + w - 1`. -/

/-- The real `1` or `0` for a bit. -/
def bitR (b : Bool) : ℝ := if b then 1 else 0

@[simp] theorem bitR_true : bitR true = 1 := rfl
@[simp] theorem bitR_false : bitR false = 0 := rfl

theorem bitR_eq_zero_iff (b : Bool) : bitR b = 0 ↔ b = false := by
  cases b <;> simp [bitR]

/-- `R` with the registers `[b, b + w)` holding the binary digits of `N`. -/
def writeBits (R : ℕ → ℝ) (b w N : ℕ) : ℕ → ℝ :=
  fun k => if b ≤ k ∧ k < b + w then bitR (N.testBit (k - b)) else R k

theorem writeBits_of_mem {R : ℕ → ℝ} {b w N k : ℕ} (h : b ≤ k ∧ k < b + w) :
    writeBits R b w N k = bitR (N.testBit (k - b)) := ite_eq_left h

theorem writeBits_of_not_mem {R : ℕ → ℝ} {b w N k : ℕ} (h : k < b ∨ b + w ≤ k) :
    writeBits R b w N k = R k := ite_eq_right (by omega)

@[simp] theorem writeBits_writeBits (R : ℕ → ℝ) (b w N N' : ℕ) :
    writeBits (writeBits R b w N) b w N' = writeBits R b w N' := by
  funext k; unfold writeBits; split_ifs <;> rfl

theorem writeBits_zero_of {R : ℕ → ℝ} {b w : ℕ} (h : ∀ q < w, R (b + q) = 0) :
    writeBits R b w 0 = R := by
  funext k
  unfold writeBits
  split_ifs with hk
  · have := h (k - b) (by omega)
    rw [show b + (k - b) = k by omega] at this
    simp [this]
  · rfl

/-- The binary digits of `v + 1`, in terms of the number `t` of trailing ones of `v`. -/
theorem testBit_succ_of_trailing {v t : ℕ} (h₁ : ∀ j < t, v.testBit j = true)
    (h₂ : v.testBit t = false) (j : ℕ) :
    (v + 1).testBit j = if j < t then false else if j = t then true else v.testBit j := by
  have hmod : v % 2 ^ (t + 1) = 2 ^ t - 1 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one]
    rcases lt_trichotomy i t with h | rfl | h
    · simp [h, h₁ i h, show i < t + 1 by omega]
    · simp [h₂]
    · simp [show ¬ i < t + 1 by omega, show ¬ i < t by omega]
  obtain ⟨u, hv⟩ : ∃ u, v = 2 ^ (t + 1) * u + (2 ^ t - 1) :=
    ⟨v / 2 ^ (t + 1), by rw [← hmod, Nat.div_add_mod]⟩
  have hpos : 1 ≤ 2 ^ t := Nat.one_le_two_pow
  have hv1 : v + 1 = 2 ^ (t + 1) * u + 2 ^ t := by omega
  have hlt : 2 ^ t < 2 ^ (t + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  rw [hv1, Nat.testBit_two_pow_mul_add _ hlt, Nat.testBit_two_pow]
  rcases lt_trichotomy j t with h | rfl | h
  · simp [h, show j < t + 1 by omega, show t ≠ j by omega]
  · simp
  · rw [hv, Nat.testBit_two_pow_mul_add _ (by omega : 2 ^ t - 1 < 2 ^ (t + 1))]
    simp [show ¬ j < t + 1 by omega, show ¬ j < t by omega, show j ≠ t by omega]

/-- Binary increment of the bit field at address `I base` (scratch `q`, `I z = 0`):
`while R[q] ≠ 0 do (R[q] := 0; q++)`, then `R[q] := 1`. -/
def binInc (base q z : ℕ) : Stmt :=
  .seqs [loadIdx q base, .loop (.zero q) (.seqs [.op (.const q 0), .op (.inc q)]),
    .op (.const q 1), clearIdx q z]

theorem binInc_spec {st : St} {base q z w v : ℕ} (hqb : q ≠ base) (hqz : q ≠ z)
    (hq : st.I q = 0) (hz : st.I z = 0)
    (hbits : ∀ j < w, st.R (st.I base + j) = bitR (v.testBit j)) (hv : v + 1 < 2 ^ w) :
    Runs (binInc base q z) st (· = ⟨writeBits st.R (st.I base) w (v + 1), st.I⟩)
      (6 * st.I base + 7 * w + 4) := by
  obtain ⟨R₀, I₀⟩ := st
  simp only at hq hz hbits ⊢
  set B := I₀ base
  -- the number of trailing ones of `v`
  have hex : ∃ j, v.testBit j = false := ⟨w, Nat.testBit_lt_two_pow (by omega)⟩
  set t := Nat.find hex with ht
  have ht₂ : v.testBit t = false := Nat.find_spec hex
  have ht₁ : ∀ j < t, v.testBit j = true := fun j hj => by
    simpa using Nat.find_min hex hj
  have htw : t < w := by
    by_contra hcon
    have hmod : v % 2 ^ w = 2 ^ w - 1 := by
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one]
      by_cases hi : i < w
      · simp [hi, ht₁ i (by omega)]
      · simp [hi]
    have := Nat.mod_le v (2 ^ w)
    omega
  let Rj : ℕ → ℕ → ℝ := fun j k => if B ≤ k ∧ k < B + j then 0 else R₀ k
  have hloop : Runs (.loop (.zero q) (.seqs [.op (.const q 0), .op (.inc q)]))
      ⟨R₀, Function.update I₀ q B⟩ (· = ⟨Rj t, Function.update I₀ q (B + t)⟩)
      (t * (2 + 2) + 1) := by
    refine Spec.loop (fun j st' => st' = ⟨Rj j, Function.update I₀ q (B + j)⟩) t ?_ ?_ ?_ ?_
    · rintro st' rfl
      simp [Rj, hbits t htw, ht₂]
    · rintro j hj st' rfl
      simp [Rj, hbits j (by omega), ht₁ j hj]
    · rintro j hj st' rfl
      refine Spec.seq_op rfl (Spec.seq_op rfl (Spec.skip (T := 0) ?_)) |>.mono_time (by norm_num)
      simp only [Function.update_self, Function.update_idem]
      congr 1
      · funext k
        simp only [Rj, Function.update_apply]
        split_ifs <;> first | omega | rfl
    · congr 1
      funext k
      simp only [Rj]
      rw [ite_eq_right (by omega)]
  have s3 : Runs (Stmt.seqs []) ⟨Function.update (Rj t) (B + t) 1,
      Function.update (Function.update I₀ q (B + t)) q 0⟩
      (· = ⟨writeBits R₀ B w (v + 1), I₀⟩) 0 := by
    refine Spec.skip ?_
    congr 1
    · funext k
      simp only [Function.update_apply, Rj, writeBits, testBit_succ_of_trailing ht₁ ht₂]
      by_cases hk : B ≤ k ∧ k < B + w
      · rw [ite_eq_left hk]
        have := hbits (k - B) (by omega)
        rw [show B + (k - B) = k by omega] at this
        split_ifs <;> first | omega | simp_all
      · rw [ite_eq_right hk]
        split_ifs <;> first | omega | rfl
    · simp [← hq]
  have s2 := Spec.seq_eq (clearIdx_spec (st := ⟨Function.update (Rj t) (B + t) 1,
    Function.update I₀ q (B + t)⟩) hqz (by simp [Function.update_of_ne hqz.symm, hz])) s3
  have s1 := Spec.seq_op (st := ⟨Rj t, Function.update I₀ q (B + t)⟩) (o := .const q 1) rfl
    (by simpa using s2)
  have s0 := Spec.seq_eq hloop s1
  have s := Spec.seq_eq (loadIdx_spec (st := ⟨R₀, I₀⟩) hqb hq) s0
  refine s.mono_time ?_
  dsimp only
  omega

/-! ## Straight-line programs on ranges of real registers -/

/-- Operations on ranges of real registers; the addresses and lengths are the values of the
named index registers. -/
inductive FOp where
  /-- copy the `I len` registers from `I src` to `I dst` -/
  | copy (src dst len : ℕ)
  /-- fill the `I len` registers from `I dst` with `v` -/
  | fill (dst len : ℕ) (v : ℝ)
  /-- `R[I dst] := v` -/
  | set (dst : ℕ) (v : ℝ)

/-- The statement executing an operation (scratch index registers `p q c`, `I z = 0`). -/
def FOp.stmt (p q c z : ℕ) : FOp → Stmt
  | .copy src dst len => copyRange src dst len p q c z
  | .fill dst len v => fillRange dst len v q c z
  | .set dst v => .op (.const dst v)

/-- Effect of an operation on the real registers. -/
def FOp.eval (I : ℕ → ℕ) : FOp → (ℕ → ℝ) → ℕ → ℝ
  | .copy src dst len, R => copyR R (I src) (I dst) (I len)
  | .fill dst len v, R => fillR R (I dst) (I len) v
  | .set dst v, R => Function.update R (I dst) v

@[simp] theorem FOp.eval_copy (I : ℕ → ℕ) (src dst len : ℕ) (R : ℕ → ℝ) :
    (FOp.copy src dst len).eval I R = copyR R (I src) (I dst) (I len) := rfl

@[simp] theorem FOp.eval_fill (I : ℕ → ℕ) (dst len : ℕ) (v : ℝ) (R : ℕ → ℝ) :
    (FOp.fill dst len v).eval I R = fillR R (I dst) (I len) v := rfl

@[simp] theorem FOp.eval_set (I : ℕ → ℕ) (dst : ℕ) (v : ℝ) (R : ℕ → ℝ) :
    (FOp.set dst v).eval I R = Function.update R (I dst) v := rfl

/-- Running time of an operation. -/
def FOp.time (I : ℕ → ℕ) : FOp → ℕ
  | .copy src dst len => 6 * I src + 6 * I dst + 15 * I len + 6
  | .fill dst len _ => 6 * I dst + 11 * I len + 4
  | .set _ _ => 1

/-- Side conditions of an operation: no scratch register is an operand, and copies do not
overwrite their source before reading it. -/
def FOp.Ok (p q c : ℕ) (I : ℕ → ℕ) : FOp → Prop
  | .copy src dst len => (src ≠ p ∧ src ≠ q ∧ src ≠ c) ∧ (dst ≠ p ∧ dst ≠ q ∧ dst ≠ c) ∧
      (len ≠ p ∧ len ≠ q ∧ len ≠ c) ∧ (I dst ≤ I src ∨ I src + I len ≤ I dst)
  | .fill dst len _ => (dst ≠ q ∧ dst ≠ c) ∧ (len ≠ q ∧ len ≠ c)
  | .set _ _ => True

/-- Effect of a list of operations. -/
def FOp.evalList (I : ℕ → ℕ) (ops : List FOp) (R : ℕ → ℝ) : ℕ → ℝ :=
  ops.foldl (fun R o => o.eval I R) R

@[simp] theorem FOp.evalList_nil (I : ℕ → ℕ) (R : ℕ → ℝ) : FOp.evalList I [] R = R := rfl

@[simp] theorem FOp.evalList_cons (I : ℕ → ℕ) (o : FOp) (ops : List FOp) (R : ℕ → ℝ) :
    FOp.evalList I (o :: ops) R = FOp.evalList I ops (o.eval I R) := rfl

/-- The program executing a list of operations. -/
def FOp.prog (p q c z : ℕ) (ops : List FOp) : Stmt := Stmt.seqs (ops.map (FOp.stmt p q c z))

theorem FOp.prog_spec {st : St} {p q c z : ℕ}
    (hpq : p ≠ q) (hpc : p ≠ c) (hqc : q ≠ c) (hpz : p ≠ z) (hqz : q ≠ z) (hcz : c ≠ z)
    (hp : st.I p = 0) (hq : st.I q = 0) (hc : st.I c = 0) (hz : st.I z = 0)
    (ops : List FOp) (hok : ∀ o ∈ ops, o.Ok p q c st.I) :
    Runs (FOp.prog p q c z ops) st (· = ⟨FOp.evalList st.I ops st.R, st.I⟩)
      (ops.map (FOp.time st.I)).sum := by
  obtain ⟨R₀, I₀⟩ := st
  simp only at hp hq hc hz hok ⊢
  induction ops generalizing R₀ with
  | nil => exact Spec.skip rfl
  | cons o ops ih =>
    have ih' := ih (o.eval I₀ R₀) (fun o' h => hok o' (List.mem_cons_of_mem _ h))
    have ho := hok o (List.mem_cons_self ..)
    simp only [FOp.prog, List.map_cons, Stmt.seqs_cons, List.sum_cons]
    refine Spec.seq_eq ?_ ih'
    cases o with
    | copy src dst len =>
      exact copyRange_spec hpq hpc hqc hpz hqz hcz ho.1 ho.2.1 ho.2.2.1 hp hq hc hz ho.2.2.2
    | fill dst len v => exact fillRange_spec hqc hqz hcz ho.1 ho.2 hq hc hz
    | set dst v => exact Spec.const rfl le_rfl

end Prog

end ClassSep
