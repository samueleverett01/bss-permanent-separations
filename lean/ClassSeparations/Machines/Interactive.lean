import ClassSeparations.Machines.Classes
import ClassSeparations.Interaction.AM

/-!
# Interactive machines and the classes `BIP_ℝ`, `IP_ℝ`, `AM_ℝ[c]`, `AM_ℝ[poly]` (§7)

An *interactive machine* is a machine with three further instructions: flip a coin (branch on
the next bit of the coin tape), send the value of a register to the prover, and receive a
message from the prover into a register.  A prover is a map from the input and the transcript
(the list of messages exchanged so far, each tagged with its direction) to a message.

* `BIP_ℝ` (Ivanov–de Rougemont [IdR99]): all messages are Boolean.  The verifier sends the bit
  `[v ≠ 0]` of a register value `v`, and the prover's messages are bits (stored as `0`/`1`).
* `IP_ℝ` (Baartse–Meer [BM16]): the messages are real numbers.
* `AM_ℝ[c]` (Definition 7.5 and the paragraph after it): `c`-round public-coin protocols whose
  verifier is a polynomial-time machine on `(x, r₁, z₁, …, r_c, z_c)`.
-/

noncomputable section

open Classical

namespace ClassSep

/-- Instructions of an interactive machine. -/
inductive IInstr where
  | base (ins : MInstr)
  /-- if the next coin is `1` then go to `target` -/
  | coin (target : ℕ)
  /-- send the value of `R[I a]` -/
  | send (a : ℕ)
  /-- receive a message into `R[I d]` -/
  | recv (d : ℕ)

/-- An interactive machine. -/
structure IMachine where
  prog : List IInstr

/-- A transcript: messages with direction (`true` = sent by the verifier). -/
abbrev RTranscript := List (Bool × ℝ)

/-- A prover with real messages. -/
abbrev RProver (n : ℕ) := (Fin n → ℝ) → RTranscript → ℝ

/-- The configuration of an interactive machine: machine configuration, transcript, number of
coins used. -/
structure IConfig where
  m : MConfig
  tr : RTranscript
  coins : ℕ

/-- The base instruction set as a one-instruction machine, to reuse `Machine.step`. -/
def IMachine.baseStep (ins : MInstr) (c : MConfig) : MConfig ⊕ Option Bool :=
  ({ prog := List.replicate c.pc MInstr.reject ++ [ins] } : Machine).step c

/-- One step of an interactive machine, given the message map `msg` (the prover's reply to the
current transcript, already restricted to the allowed message set) and the coin tape `r`;
`sendMap` turns a register value into the message actually sent. -/
def IMachine.step (M : IMachine) (sendMap : ℝ → ℝ) (msg : RTranscript → ℝ) (r : ℕ → Bool)
    (c : IConfig) : IConfig ⊕ Option Bool :=
  match M.prog[c.m.pc]? with
  | none => .inr (some false)
  | some (.base ins) =>
      match IMachine.baseStep ins c.m with
      | .inl m' => .inl { c with m := m' }
      | .inr o => .inr o
  | some (.coin t) =>
      .inl { c with m := { c.m with pc := if r c.coins then t else c.m.pc + 1 },
                    coins := c.coins + 1 }
  | some (.send a) =>
      .inl { c with m := { c.m with pc := c.m.pc + 1 },
                    tr := c.tr ++ [(true, sendMap (c.m.R (c.m.I a)))] }
  | some (.recv d) =>
      let v := msg c.tr
      .inl { c with m := { c.m with pc := c.m.pc + 1,
                                    R := Function.update c.m.R (c.m.I d) v },
                    tr := c.tr ++ [(false, v)] }

/-- Run an interactive machine for at most `n` steps. -/
def IMachine.run (M : IMachine) (sendMap : ℝ → ℝ) (msg : RTranscript → ℝ) (r : ℕ → Bool) :
    ℕ → IConfig → Option (Option Bool)
  | 0, _ => none
  | n + 1, c =>
    match M.step sendMap msg r c with
    | .inl c' => M.run sendMap msg r n c'
    | .inr o => some o

/-- The initial configuration on input `x`. -/
def IMachine.init {n : ℕ} (x : Fin n → ℝ) : IConfig := ⟨initConfig [n] (vecReg x), [], 0⟩

/-- Acceptance probability with coin tapes of length `T` and run time `T`. -/
def IMachine.accProb (M : IMachine) (sendMap : ℝ → ℝ) (T : ℕ) {n : ℕ} (x : Fin n → ℝ)
    (msg : RTranscript → ℝ) : ℝ :=
  ((Finset.univ.filter fun r : Fin T → Bool =>
      M.run sendMap msg (fun j => if h : j < T then r ⟨j, h⟩ else false) T (IMachine.init x) =
        some (some true)).card : ℝ) / 2 ^ T

/-- The machine halts within `T` steps for every coin tape and every prover with messages in
`Msg`. -/
def IMachine.HaltsWithin (M : IMachine) (sendMap : ℝ → ℝ) (Msg : Set ℝ) (T : ℕ) {n : ℕ}
    (x : Fin n → ℝ) : Prop :=
  ∀ (msg : RTranscript → ℝ), (∀ s, msg s ∈ Msg) → ∀ r : ℕ → Bool,
    ∃ o, M.run sendMap msg r T (IMachine.init x) = some o

/-- `BIP_ℝ`: Boolean messages, private coins, polynomial time. -/
def BIP_R : Set Lang :=
  {L | ∃ (M : IMachine) (p : ℕ → ℕ), PolyBounded p ∧ ∀ n (x : Fin n → ℝ),
    M.HaltsWithin (fun v => if v = 0 then 0 else 1) {0, 1} (p n) x ∧
    (x ∈ L n → ∃ P : RProver n, (∀ s, P x s ∈ ({0, 1} : Set ℝ)) ∧
      2 / 3 ≤ M.accProb (fun v => if v = 0 then 0 else 1) (p n) x (P x)) ∧
    (x ∉ L n → ∀ P : RProver n, (∀ s, P x s ∈ ({0, 1} : Set ℝ)) →
      M.accProb (fun v => if v = 0 then 0 else 1) (p n) x (P x) ≤ 1 / 3)}

/-- `IP_ℝ`: real messages, private coins, polynomial time [BM16]. -/
def IP_R : Set Lang :=
  {L | ∃ (M : IMachine) (p : ℕ → ℕ), PolyBounded p ∧ ∀ n (x : Fin n → ℝ),
    M.HaltsWithin id Set.univ (p n) x ∧
    (x ∈ L n → ∃ P : RProver n, 2 / 3 ≤ M.accProb id (p n) x (P x)) ∧
    (x ∉ L n → ∀ P : RProver n, M.accProb id (p n) x (P x) ≤ 1 / 3)}

/-- The `c`-round values (10) for an arbitrary acceptance predicate `acc` on coins and
messages. -/
def amValFrom (c ρ μ : ℕ) (acc : (Fin c → Fin ρ → Bool) → (Fin c → Fin μ → ℝ) → Prop)
    (i : ℕ) (r : Fin c → Fin ρ → Bool) (z : Fin c → Fin μ → ℝ) : ℝ :=
  if h : i < c then
    (2 ^ ρ : ℝ)⁻¹ * ∑ b : Fin ρ → Bool,
      ⨆ y : Fin μ → ℝ, amValFrom c ρ μ acc (i + 1) (Function.update r ⟨i, h⟩ b)
        (Function.update z ⟨i, h⟩ y)
  else if acc r z then 1 else 0
termination_by c - i

/-- The input `(x, r, z)` of an AM verifier machine, as one vector. -/
def amVec {n c ρ μ : ℕ} (x : Fin n → ℝ) (r : Fin c → Fin ρ → Bool) (z : Fin c → Fin μ → ℝ) :
    Fin (n + c * ρ + c * μ) → ℝ :=
  Fin.append (Fin.append x (fun j : Fin (c * ρ) =>
      if r (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2 then 1 else 0))
    (fun j : Fin (c * μ) => z (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2)

/-- The language `L` has a public-coin protocol with `c n` rounds, `ρ n` coins per round,
messages in `ℝ^{μ n}`, and a verifier machine `M` running in time `p n`. -/
def AMProtocolFor (L : Lang) (c : ℕ → ℕ) (M : Machine) (ρ μ p : ℕ → ℕ) : Prop :=
  ∀ n (x : Fin n → ℝ),
    (∀ (r : Fin (c n) → Fin (ρ n) → Bool) (z : Fin (c n) → Fin (μ n) → ℝ),
      M.HaltsWithin (p n) [n, c n * ρ n, c n * μ n] (amVec x r z)) ∧
    let v := amValFrom (c n) (ρ n) (μ n)
      (fun r z => M.HaltsWith (p n) [n, c n * ρ n, c n * μ n] (amVec x r z) (some true))
      0 (fun _ _ => false) (fun _ _ => 0)
    (x ∈ L n → 2 / 3 ≤ v) ∧ (x ∉ L n → v ≤ 1 / 3)

/-- `AM_ℝ[c]`. -/
def AM_R (c : ℕ) : Set Lang :=
  {L | ∃ (M : Machine) (ρ μ p : ℕ → ℕ), PolyBounded ρ ∧ PolyBounded μ ∧ PolyBounded p ∧
    AMProtocolFor L (fun _ => c) M ρ μ p}

/-- `AM_ℝ[O(1)] = ⋃_{c ≥ 1} AM_ℝ[c]`. -/
def AM_R_const : Set Lang := ⋃ c ∈ {c : ℕ | 1 ≤ c}, AM_R c

/-- `AM_ℝ[poly]`: polynomially many rounds. -/
def AM_R_poly : Set Lang :=
  {L | ∃ (M : Machine) (c ρ μ p : ℕ → ℕ), PolyBounded c ∧ PolyBounded ρ ∧ PolyBounded μ ∧
    PolyBounded p ∧ AMProtocolFor L c M ρ μ p}

end ClassSep

namespace ClassSep

/-- The transcript of a verifier tree corresponding to a real transcript with Boolean messages. -/
def RTranscript.toBool (s : RTranscript) : VTree.Transcript :=
  s.map fun p => (p.1, p.2 ≠ 0)

/-! ### Unrolling Boolean-message verifiers

As in `Machine.unroll`, the program counter and the index registers are concrete along a path
of the tree and the real registers are symbolic operands.  A coin instruction becomes a coin
node, `send a` becomes the test `R[I a] = 0` followed by a send node, and `recv d` becomes a
receive node whose two branches store the constants `0`/`1` into the destination register. -/

/-- The symbolic unrolling of an interactive machine with `fuel` steps. -/
private def ivUnroll (M : IMachine) (n : ℕ) :
    ℕ → ℕ → (ℕ → TArg (Fin n)) → (ℕ → ℕ) → ℕ → VTree (Fin n)
  | 0, _, _, _, _ => .leaf false
  | fuel + 1, pc, R, I, m =>
    match M.prog[pc]? with
    | none => .leaf false
    | some (.base (.arith op d a b)) =>
        .comp op (R (I a)) (R (I b))
          (ivUnroll M n fuel (pc + 1) (Function.update R (I d) (.val m)) I (m + 1))
    | some (.base (.const d c)) =>
        ivUnroll M n fuel (pc + 1) (Function.update R (I d) (.const c)) I m
    | some (.base (.copy d a)) =>
        ivUnroll M n fuel (pc + 1) (Function.update R (I d) (R (I a))) I m
    | some (.base (.jumpGe a t)) =>
        .test .ge (R (I a)) (ivUnroll M n fuel t R I m) (ivUnroll M n fuel (pc + 1) R I m)
    | some (.base (.jumpEq a t)) =>
        .test .eq (R (I a)) (ivUnroll M n fuel t R I m) (ivUnroll M n fuel (pc + 1) R I m)
    | some (.base (.inc k)) => ivUnroll M n fuel (pc + 1) R (Function.update I k (I k + 1)) m
    | some (.base (.dec k)) => ivUnroll M n fuel (pc + 1) R (Function.update I k (I k - 1)) m
    | some (.base (.jumpIdx k l t)) =>
        ivUnroll M n fuel (if I k = I l then t else pc + 1) R I m
    | some (.base .accept) => .leaf true
    | some (.base .reject) => .leaf false
    | some (.coin t) => .coin (ivUnroll M n fuel (pc + 1) R I m) (ivUnroll M n fuel t R I m)
    | some (.send a) =>
        .test .eq (R (I a)) (.send false (ivUnroll M n fuel (pc + 1) R I m))
          (.send true (ivUnroll M n fuel (pc + 1) R I m))
    | some (.recv d) =>
        .recv (ivUnroll M n fuel (pc + 1) (Function.update R (I d) (.const 0)) I m)
          (ivUnroll M n fuel (pc + 1) (Function.update R (I d) (.const 1)) I m)

private theorem ivUnroll_depth (M : IMachine) (n fuel : ℕ) :
    ∀ pc R I m, (ivUnroll M n fuel pc R I m).depth ≤ 2 * fuel + 1 := by
  induction fuel with
  | zero => intro pc R I m; simp [ivUnroll, VTree.depth]
  | succ fuel ih =>
    intro pc R I m
    simp only [ivUnroll]
    split
    all_goals try simp only [VTree.depth]
    all_goals first
      | omega
      | exact (ih _ _ _ _).trans (by omega)
      | exact (Nat.succ_le_succ (ih _ _ _ _)).trans (by omega)
      | exact (Nat.succ_le_succ (max_le (ih _ _ _ _) (ih _ _ _ _))).trans (by omega)
      | exact (Nat.succ_le_succ (max_le (Nat.succ_le_succ (ih _ _ _ _))
          (Nat.succ_le_succ (ih _ _ _ _)))).trans (by omega)

/-- A computation node of a verifier tree, with the four operations treated uniformly. -/
private theorem ivUnroll_runFrom_comp {n : ℕ} (w : Fin n → ℝ) (P : VTree.Prover (Fin n))
    (r : ℕ → Bool) (op : TOp) (a b : TArg (Fin n)) (next : VTree (Fin n)) (vals : List ℝ)
    (s : VTree.Transcript) (j : ℕ) :
    (VTree.comp op a b next).runFrom w P r vals s j =
      match op.apply? (a.eval w vals) (b.eval w vals) with
      | none => none
      | some v => next.runFrom w P r (vals ++ [v]) s j := by
  cases op <;> simp only [VTree.runFrom, TOp.apply?]
  split_ifs <;> rfl

private theorem ivUnroll_eval_append {n : ℕ} (x : Fin n → ℝ) (vals : List ℝ) (v : ℝ)
    (t : TArg (Fin n)) (ht : ∀ j, t = .val j → j < vals.length) :
    t.eval x (vals ++ [v]) = t.eval x vals := by
  cases t with
  | input i => rfl
  | const c => rfl
  | val j => exact List.getD_append _ _ _ _ (ht j rfl)

private theorem ivUnroll_baseProg (k : ℕ) (ins : MInstr) :
    (List.replicate k MInstr.reject ++ [ins])[k]? = some ins := by
  rw [List.getElem?_append_right (by simp)]
  simp

/-- The real transcript corresponding to a Boolean transcript. -/
private def boolToReal (s : VTree.Transcript) : RTranscript :=
  s.map fun p => (p.1, if p.2 then 1 else 0)

private theorem ivUnroll_run (M : IMachine) {n : ℕ} (x : Fin n → ℝ) (msg : RTranscript → ℝ)
    (hmsg : ∀ s, msg s ∈ ({0, 1} : Set ℝ)) (r : ℕ → Bool) (fuel : ℕ) :
    ∀ (c : IConfig) (R : ℕ → TArg (Fin n)) (vals : List ℝ) (s : VTree.Transcript)
      (o : Option Bool),
      (∀ i, (R i).eval x vals = c.m.R i) →
      (∀ i j, R i = .val j → j < vals.length) →
      c.tr = boolToReal s →
      M.run (fun v => if v = 0 then 0 else 1) msg r fuel c = some o →
      (ivUnroll M n fuel c.m.pc R c.m.I vals.length).runFrom x
        (fun _ s => decide (msg (boolToReal s) ≠ 0)) r vals s c.coins = o := by
  induction fuel with
  | zero => intro c R vals s o _ _ _ h; simp [IMachine.run] at h
  | succ fuel ih =>
    intro c R vals s o hR hgood htr h
    simp only [IMachine.run, IMachine.step] at h
    rcases hp : M.prog[c.m.pc]? with _ | ins
    · simp only [hp, Option.some_inj] at h
      simp [ivUnroll, hp, VTree.runFrom, h]
    · cases ins with
      | base ins =>
        cases ins with
        | arith op d a b =>
          simp only [hp, IMachine.baseStep, Machine.step, ivUnroll_baseProg] at h
          simp only [ivUnroll, hp]
          rw [ivUnroll_runFrom_comp, hR, hR]
          cases hv : op.apply? (c.m.R (c.m.I a)) (c.m.R (c.m.I b)) with
          | none => simpa [hv] using h
          | some v =>
            simp only [hv] at h ⊢
            have := ih _ (Function.update R (c.m.I d) (.val vals.length)) (vals ++ [v]) s o
              ?_ ?_ (by exact htr) h
            · simpa using this
            · intro i
              by_cases hi : i = c.m.I d
              · subst hi; simp [TArg.eval]
              · simp only [Function.update_of_ne hi]
                rw [ivUnroll_eval_append x vals v _ (hgood i), hR]
            · intro i j hj
              by_cases hi : i = c.m.I d
              · subst hi; simp at hj; subst hj; simp
              · simp only [Function.update_of_ne hi] at hj
                have := hgood i j hj
                simp; omega
        | const d k =>
          simp only [hp, IMachine.baseStep, Machine.step, ivUnroll_baseProg] at h
          simp only [ivUnroll, hp]
          refine ih _ _ vals s o ?_ ?_ (by exact htr) h
          · intro i
            by_cases hi : i = c.m.I d
            · subst hi; simp [TArg.eval]
            · simp [Function.update_of_ne hi, hR]
          · intro i j hj
            by_cases hi : i = c.m.I d
            · subst hi; simp at hj
            · simp only [Function.update_of_ne hi] at hj
              exact hgood i j hj
        | copy d a =>
          simp only [hp, IMachine.baseStep, Machine.step, ivUnroll_baseProg] at h
          simp only [ivUnroll, hp]
          refine ih _ _ vals s o ?_ ?_ (by exact htr) h
          · intro i
            by_cases hi : i = c.m.I d
            · subst hi; simp [hR]
            · simp [Function.update_of_ne hi, hR]
          · intro i j hj
            by_cases hi : i = c.m.I d
            · subst hi; simp at hj; exact hgood _ j hj
            · simp only [Function.update_of_ne hi] at hj
              exact hgood i j hj
        | jumpGe a t =>
          simp only [hp, IMachine.baseStep, Machine.step, ivUnroll_baseProg] at h
          simp only [ivUnroll, hp, VTree.runFrom, TestKind.holds, hR]
          split_ifs with hc
          · rw [ite_eq_left hc] at h
            exact ih { c with m := { c.m with pc := t } } R vals s o hR hgood htr h
          · rw [ite_eq_right hc] at h
            exact ih { c with m := { c.m with pc := c.m.pc + 1 } } R vals s o hR hgood htr h
        | jumpEq a t =>
          simp only [hp, IMachine.baseStep, Machine.step, ivUnroll_baseProg] at h
          simp only [ivUnroll, hp, VTree.runFrom, TestKind.holds, hR]
          split_ifs with hc
          · rw [ite_eq_left hc] at h
            exact ih { c with m := { c.m with pc := t } } R vals s o hR hgood htr h
          · rw [ite_eq_right hc] at h
            exact ih { c with m := { c.m with pc := c.m.pc + 1 } } R vals s o hR hgood htr h
        | inc k =>
          simp only [hp, IMachine.baseStep, Machine.step, ivUnroll_baseProg] at h
          simp only [ivUnroll, hp]
          exact ih _ R vals s o (by exact hR) (by exact hgood) (by exact htr) h
        | dec k =>
          simp only [hp, IMachine.baseStep, Machine.step, ivUnroll_baseProg] at h
          simp only [ivUnroll, hp]
          exact ih _ R vals s o (by exact hR) (by exact hgood) (by exact htr) h
        | jumpIdx k l t =>
          simp only [hp, IMachine.baseStep, Machine.step, ivUnroll_baseProg] at h
          simp only [ivUnroll, hp]
          exact ih _ R vals s o (by exact hR) (by exact hgood) (by exact htr) h
        | accept =>
          simp only [hp, IMachine.baseStep, Machine.step, ivUnroll_baseProg,
            Option.some_inj] at h
          simp [ivUnroll, hp, VTree.runFrom, h]
        | reject =>
          simp only [hp, IMachine.baseStep, Machine.step, ivUnroll_baseProg,
            Option.some_inj] at h
          simp [ivUnroll, hp, VTree.runFrom, h]
      | coin t =>
        simp only [hp] at h
        simp only [ivUnroll, hp, VTree.runFrom]
        cases hc : r c.coins
        · simp only [hc, Bool.false_eq_true, ↓reduceIte] at h ⊢
          exact ih { c with m := { c.m with pc := c.m.pc + 1 }, coins := c.coins + 1 }
            R vals s o hR hgood htr h
        · simp only [hc, ↓reduceIte] at h ⊢
          exact ih { c with m := { c.m with pc := t }, coins := c.coins + 1 }
            R vals s o hR hgood htr h
      | send a =>
        simp only [hp] at h
        simp only [ivUnroll, hp, VTree.runFrom, TestKind.holds, hR]
        by_cases hc : c.m.R (c.m.I a) = 0
        · simp only [hc, ↓reduceIte] at h ⊢
          refine ih _ R vals (s ++ [(true, false)]) o (by exact hR) (by exact hgood) ?_ h
          simp [htr, boolToReal]
        · simp only [hc, ↓reduceIte] at h ⊢
          refine ih _ R vals (s ++ [(true, true)]) o (by exact hR) (by exact hgood) ?_ h
          simp [htr, boolToReal]
      | recv d =>
        simp only [hp] at h
        simp only [ivUnroll, hp, VTree.runFrom]
        rw [← htr]
        rcases hmsg c.tr with hv | hv
        · simp only [hv, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
            ↓reduceIte] at h ⊢
          refine ih _ _ vals (s ++ [(false, false)]) o ?_ ?_ ?_ h
          · intro i
            by_cases hi : i = c.m.I d
            · subst hi; simp [TArg.eval]
            · simp [Function.update_of_ne hi, hR]
          · intro i j hj
            by_cases hi : i = c.m.I d
            · subst hi; simp at hj
            · simp only [Function.update_of_ne hi] at hj
              exact hgood i j hj
          · simp [htr, boolToReal]
        · rw [Set.mem_singleton_iff] at hv
          simp only [hv, ne_eq, one_ne_zero, not_false_eq_true, decide_true, ↓reduceIte] at h ⊢
          refine ih _ _ vals (s ++ [(false, true)]) o ?_ ?_ ?_ h
          · intro i
            by_cases hi : i = c.m.I d
            · subst hi; simp [TArg.eval]
            · simp [Function.update_of_ne hi, hR]
          · intro i j hj
            by_cases hi : i = c.m.I d
            · subst hi; simp at hj
            · simp only [Function.update_of_ne hi] at hj
              exact hgood i j hj
          · simp [htr, boolToReal]

/-- The run of a verifier tree only depends on the coins it can reach. -/
private theorem ivUnroll_tree_congr {ι : Type} (w : ι → ℝ) (P : VTree.Prover ι) (V : VTree ι) :
    ∀ (r r' : ℕ → Bool) (vals : List ℝ) (s : VTree.Transcript) (j : ℕ),
      (∀ i < j + V.depth, r i = r' i) → V.runFrom w P r vals s j = V.runFrom w P r' vals s j := by
  induction V with
  | leaf b => intros; rfl
  | comp op a b next ih =>
    intro r r' vals s j h
    have h' : ∀ vals, next.runFrom w P r vals s j = next.runFrom w P r' vals s j :=
      fun vals => ih r r' vals s j (fun i hi => h i (by simp only [VTree.depth]; omega))
    cases op <;> simp only [VTree.runFrom, h']
  | test k v yes no ihy ihn =>
    intro r r' vals s j h
    simp only [VTree.runFrom]
    rw [ihy r r' vals s j (fun i hi => h i (by simp only [VTree.depth]; omega)),
      ihn r r' vals s j (fun i hi => h i (by simp only [VTree.depth]; omega))]
  | coin c₀ c₁ ih₀ ih₁ =>
    intro r r' vals s j h
    simp only [VTree.runFrom]
    rw [h j (by simp only [VTree.depth]; omega),
      ih₀ r r' vals s (j + 1) (fun i hi => h i (by simp only [VTree.depth]; omega)),
      ih₁ r r' vals s (j + 1) (fun i hi => h i (by simp only [VTree.depth]; omega))]
  | send b next ih =>
    intro r r' vals s j h
    simp only [VTree.runFrom]
    exact ih r r' vals _ j (fun i hi => h i (by simp only [VTree.depth]; omega))
  | recv r₀ r₁ ih₀ ih₁ =>
    intro r r' vals s j h
    simp only [VTree.runFrom]
    rw [ih₀ r r' vals _ j (fun i hi => h i (by simp only [VTree.depth]; omega)),
      ih₁ r r' vals _ j (fun i hi => h i (by simp only [VTree.depth]; omega))]

private theorem ivUnroll_step_coins (M : IMachine) (sm : ℝ → ℝ) (msg : RTranscript → ℝ)
    (r : ℕ → Bool) (c c' : IConfig) (h : M.step sm msg r c = .inl c') :
    c'.coins ≤ c.coins + 1 := by
  unfold IMachine.step at h
  split at h
  · simp at h
  · split at h
    · simp only [Sum.inl.injEq] at h; subst h; simp
    · simp at h
  · simp only [Sum.inl.injEq] at h; subst h; simp
  · simp only [Sum.inl.injEq] at h; subst h; simp
  · simp only [Sum.inl.injEq] at h; subst h; simp

/-- The run of an interactive machine only depends on the coins it can reach. -/
private theorem ivUnroll_machine_congr (M : IMachine) (sm : ℝ → ℝ) (msg : RTranscript → ℝ)
    (fuel : ℕ) : ∀ (c : IConfig) (r r' : ℕ → Bool), (∀ i < c.coins + fuel, r i = r' i) →
      M.run sm msg r fuel c = M.run sm msg r' fuel c := by
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
    intro c r r' h
    have hs : M.step sm msg r c = M.step sm msg r' c := by
      unfold IMachine.step
      rw [h c.coins (by omega)]
    simp only [IMachine.run]
    rw [hs]
    cases hst : M.step sm msg r' c with
    | inl c' =>
      have := ivUnroll_step_coins M sm msg r' c c' hst
      exact ih c' r r' (fun i hi => h i (by omega))
    | inr o => rfl

/-- For an event depending only on the first `a` coins, the fraction of coin tapes of length
`b ≥ a` on which it holds does not depend on `b`. -/
private theorem ivUnroll_frac (E : (ℕ → Bool) → Prop) (a : ℕ)
    (hE : ∀ r r' : ℕ → Bool, (∀ j < a, r j = r' j) → (E r ↔ E r')) (b : ℕ) (hab : a ≤ b) :
    ((Finset.univ.filter fun r : Fin b → Bool =>
        E (fun j => if h : j < b then r ⟨j, h⟩ else false)).card : ℝ) / 2 ^ b =
      ((Finset.univ.filter fun r : Fin a → Bool =>
        E (fun j => if h : j < a then r ⟨j, h⟩ else false)).card : ℝ) / 2 ^ a := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
    rw [← ih]
    have key : ∀ (r' : Fin b → Bool) (cb : Bool),
        (E (fun j => if h : j < b + 1 then (Fin.snoc r' cb : Fin (b + 1) → Bool) ⟨j, h⟩
          else false) ↔ E (fun j => if h : j < b then r' ⟨j, h⟩ else false)) := by
      intro r' cb
      apply hE
      intro j hj
      have hjb : j < b := lt_of_lt_of_le hj hab
      have hjb1 : j < b + 1 := by omega
      simp only [hjb, hjb1, dite_true]
      exact Fin.snoc_castSucc (α := fun _ => Bool) (p := r') (x := cb) (i := ⟨j, hjb⟩)
    have hcard : (Finset.univ.filter fun r : Fin (b + 1) → Bool =>
          E (fun j => if h : j < b + 1 then r ⟨j, h⟩ else false)).card =
        2 * (Finset.univ.filter fun r : Fin b → Bool =>
          E (fun j => if h : j < b then r ⟨j, h⟩ else false)).card := by
      rw [Finset.card_filter, Finset.card_filter,
        ← (Fin.snocEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool]
      simp only [Fin.snocEquiv_apply, key]
      ring
    rw [hcard, pow_succ]
    push_cast
    field_simp

/-- **Unrolling of Boolean-message verifiers.**  For inputs of size `n` and a verifier that
halts within `T` steps for every coin tape and every Boolean prover, there is a verifier tree
of depth `≤ 2T + 1` such that every Boolean prover has the same acceptance probability against
the machine (with coin tapes of length `T`) and against the tree.  (Sending a computed bit is a
test followed by a send node, which at most doubles the depth.) -/
theorem IMachine.unroll_bool (M : IMachine) (n T : ℕ) :
    ∃ V : VTree (Fin n), V.depth ≤ 2 * T + 1 ∧
      ∀ (x : Fin n → ℝ), M.HaltsWithin (fun v => if v = 0 then 0 else 1) {0, 1} T x →
      ∀ P : RProver n, (∀ s, P x s ∈ ({0, 1} : Set ℝ)) →
        V.accProb x (fun y s => decide (P x (s.map fun p => (p.1, if p.2 then 1 else 0)) ≠ 0)) =
          M.accProb (fun v => if v = 0 then 0 else 1) T x (P x) := by
  let R₀ : ℕ → TArg (Fin n) := fun i => if h : i < n then .input ⟨i, h⟩ else .const 0
  let V := ivUnroll M n T 0 R₀ (fun k => [n].getD k 0) 0
  refine ⟨V, ivUnroll_depth M n T _ _ _ _, ?_⟩
  intro x hHalt P hP
  let P' : VTree.Prover (Fin n) := fun _ s => decide (P x (boolToReal s) ≠ 0)
  -- the tree accepts exactly when the machine accepts, for every coin tape
  have hcorr : ∀ r : ℕ → Bool, V.runFrom x P' r [] [] 0 = some true ↔
      M.run (fun v => if v = 0 then 0 else 1) (P x) r T (IMachine.init x) = some (some true) := by
    intro r
    obtain ⟨o, ho⟩ := hHalt (P x) hP r
    have := ivUnroll_run M x (P x) hP r T (IMachine.init x) R₀ [] [] o ?_ ?_ rfl ho
    · change V.runFrom x P' r [] [] 0 = o at this
      rw [this, ho]
      simp
    · intro i
      by_cases h : i < n <;> simp [R₀, h, TArg.eval, IMachine.init, initConfig, vecReg]
    · intro i j hj
      by_cases h : i < n <;> simp [R₀, h] at hj
  let E : (ℕ → Bool) → Prop := fun r => V.runFrom x P' r [] [] 0 = some true
  have hE : ∀ r r' : ℕ → Bool, (∀ j < min T V.depth, r j = r' j) → (E r ↔ E r') := by
    intro r r' h
    rcases le_total T V.depth with hle | hle
    · simp only [E]
      rw [hcorr, hcorr, ivUnroll_machine_congr M _ (P x) T (IMachine.init x) r r'
        (fun j hj => h j (by simp [IMachine.init] at hj; omega))]
    · simp only [E]
      rw [ivUnroll_tree_congr x P' V r r' [] [] 0 (fun j hj => h j (by omega))]
  -- both acceptance probabilities equal the fraction for coin tapes of length `min T V.depth`
  have key₁ := ivUnroll_frac E _ hE V.depth (min_le_right _ _)
  have key₂ := ivUnroll_frac E _ hE T (min_le_left _ _)
  refine (Eq.trans ?_ (key₁.trans key₂.symm)).trans ?_
  · rfl
  · unfold IMachine.accProb
    congr 3
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, E]
    exact hcorr _

end ClassSep
