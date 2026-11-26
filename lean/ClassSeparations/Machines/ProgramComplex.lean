import ClassSeparations.Machines.Program
import ClassSeparations.Machines.Complex

/-!
# Running real machine programs on complex machines

A real machine without `jumpGe` instructions translates into a complex machine (`Machine.toC`:
real constants are embedded into `ℂ`); the two run in lockstep on configurations whose real
registers are embedded into `ℂ` (`Machine.toC_runFinal`, `Machine.toC_run`).  Programs written
as structured statements without `Cond.nonneg` (`Prog.Stmt.noGe`) compile to such machines
(`Prog.Stmt.toMachine_noGe`), so that the whole program library of
`ClassSeparations.Machines.Program` can be used for complex machines.
-/

noncomputable section

open Classical

namespace ClassSep

/-- The complex instruction of a real instruction (`jumpGe` has no counterpart and is mapped to
`jumpEq`; the translation is faithful only for machines without `jumpGe`). -/
def MInstr.toC : MInstr → CMInstr
  | .arith op d a b => .arith op d a b
  | .const d c => .const d (c : ℂ)
  | .copy d a => .copy d a
  | .jumpGe a t => .jumpEq a t
  | .jumpEq a t => .jumpEq a t
  | .inc k => .inc k
  | .dec k => .dec k
  | .jumpIdx k l t => .jumpIdx k l t
  | .accept => .accept
  | .reject => .reject

/-- The complex machine of a real machine. -/
def Machine.toC (M : Machine) : CMachine := ⟨M.prog.map MInstr.toC⟩

/-- The complex configuration of a real configuration. -/
def MConfig.toC (c : MConfig) : CMConfig := ⟨c.pc, fun k => (c.R k : ℂ), c.I⟩

/-- The machine has no `jumpGe` instruction. -/
def Machine.NoGe (M : Machine) : Prop := ∀ a t, MInstr.jumpGe a t ∉ M.prog

theorem TOp.applyC?_ofReal (op : TOp) (x y : ℝ) :
    op.applyC? x y = (op.apply? x y).map fun v => (v : ℂ) := by
  cases op <;> simp [TOp.applyC?, TOp.apply?]
  split_ifs <;> simp_all

theorem MConfig.toC_update (R : ℕ → ℝ) (a : ℕ) (v : ℝ) :
    (fun k => ((Function.update R a v k : ℝ) : ℂ)) =
      Function.update (fun k => (R k : ℂ)) a (v : ℂ) := by
  funext k
  by_cases h : k = a
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem Machine.toC_step {M : Machine} (hM : M.NoGe) (c : MConfig) :
    M.toC.step c.toC = match M.step c with
      | .inl c' => .inl c'.toC
      | .inr o => .inr o := by
  unfold CMachine.step Machine.step
  simp only [Machine.toC, List.getElem?_map, MConfig.toC]
  rcases hp : M.prog[c.pc]? with _ | ins
  · rfl
  · cases ins with
    | arith op d a b =>
      simp only [Option.map_some, MInstr.toC, TOp.applyC?_ofReal]
      cases op.apply? (c.R (c.I a)) (c.R (c.I b)) with
      | none => rfl
      | some v => simp [MConfig.toC_update]
    | const d v => simp [MInstr.toC, MConfig.toC_update]
    | copy d a => simp [MInstr.toC, MConfig.toC_update]
    | jumpGe a t => exact absurd (List.mem_of_getElem? hp) (hM a t)
    | jumpEq a t => simp [MInstr.toC, Complex.ofReal_eq_zero]
    | inc k => simp [MInstr.toC]
    | dec k => simp [MInstr.toC]
    | jumpIdx k l t => by_cases h : c.I k = c.I l <;> simp [MInstr.toC, h]
    | accept => simp [MInstr.toC]
    | reject => simp [MInstr.toC]

/-- **Lockstep simulation**: the complex machine of a real machine without `jumpGe`. -/
theorem Machine.toC_runFinal {M : Machine} (hM : M.NoGe) (k : ℕ) (c : MConfig) :
    M.toC.runFinal k c.toC = (M.runFinal k c).map fun p => (p.1.toC, p.2) := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
    rw [CMachine.runFinal, Machine.toC_step hM, Machine.runFinal]
    cases M.step c with
    | inl c' => exact ih c'
    | inr o => rfl

theorem Machine.toC_run {M : Machine} (hM : M.NoGe) (k : ℕ) (c : MConfig) :
    M.toC.run k c.toC = M.run k c := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
    rw [CMachine.run, Machine.toC_step hM, Machine.run]
    cases M.step c with
    | inl c' => exact ih c'
    | inr o => rfl

theorem initConfig_toC (sizes : List ℕ) (w : ℕ → ℝ) :
    (initConfig sizes w).toC = initConfigC sizes fun k => (w k : ℂ) := rfl

namespace Prog

/-- The condition is not a sign test. -/
def Cond.noGe : Cond → Bool
  | .nonneg _ => false
  | _ => true

/-- The statement uses no sign tests (`Cond.nonneg`). -/
def Stmt.noGe : Stmt → Bool
  | .skip => true
  | .op _ => true
  | .seq s t => s.noGe && t.noGe
  | .ite c s t => c.noGe && s.noGe && t.noGe
  | .loop c s => c.noGe && s.noGe
  | .halt _ => true

theorem Cond.instr_ne_jumpGe {c : Cond} (hc : c.noGe = true) (t a t' : ℕ) :
    c.instr t ≠ .jumpGe a t' := by
  cases c <;> simp_all [Cond.noGe, Cond.instr]

theorem Stmt.compile_noGe {s : Stmt} (hs : s.noGe = true) (p a t : ℕ) :
    MInstr.jumpGe a t ∉ s.compile p := by
  induction s generalizing p with
  | skip => simp [Stmt.compile]
  | op o => cases o <;> simp [Stmt.compile, BOp.instr]
  | seq s u ihs ihu =>
    simp only [Stmt.noGe, Bool.and_eq_true] at hs
    simp only [Stmt.compile, List.mem_append, not_or]
    exact ⟨ihs hs.1 _, ihu hs.2 _⟩
  | ite c s u ihs ihu =>
    simp only [Stmt.noGe, Bool.and_eq_true] at hs
    simp only [Stmt.compile, List.mem_append, List.mem_singleton, not_or]
    exact ⟨⟨⟨fun h => Cond.instr_ne_jumpGe hs.1.1 _ _ _ h.symm, ihu hs.2 _⟩,
      fun h => by simp [goto] at h⟩, ihs hs.1.2 _⟩
  | loop c s ih =>
    simp only [Stmt.noGe, Bool.and_eq_true] at hs
    simp only [Stmt.compile, List.mem_append, List.mem_singleton, not_or]
    exact ⟨⟨fun h => Cond.instr_ne_jumpGe hs.1 _ _ _ h.symm, ih hs.2 _⟩,
      fun h => by simp [goto] at h⟩
  | halt b => cases b <;> simp [Stmt.compile]

theorem Stmt.toMachine_noGe {s : Stmt} (hs : s.noGe = true) : s.toMachine.NoGe :=
  fun a t => Stmt.compile_noGe hs 0 a t

end Prog

end ClassSep
