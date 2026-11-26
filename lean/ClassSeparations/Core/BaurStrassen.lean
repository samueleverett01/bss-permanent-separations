import ClassSeparations.Basic.Circuits

/-!
# The theorem of Baur and Strassen (Theorem 2.4)

**Theorem 2.4** [BS83, Theorem 2]: if a polynomial has a straight-line program with `ℓ`
operations, then the polynomial together with all its first partial derivatives has a
straight-line program with `O(ℓ)` operations.

The paper (proof of Theorem 3.5) uses that the construction transforms the program gate by gate,
so that the graph of the new program depends only on the graph of the old one.  We prove this
uniform version directly (reverse-mode differentiation): for every program graph `prog` there
are a program graph `prog'` with `O(ℓ)` operations and a fixed arrangement `cmap` of constants,
such that for all values `c` of the constants of `prog`, the program `prog'` with constants
`cmap c` computes the polynomial and its partial derivatives.

## The construction

The new program first copies the old one (constant slots shifted by `2`; slot `0` holds `0`
and slot `1` holds `1`).  Then it processes the instructions in reverse order, maintaining for
each instruction `j` and each input `i` an operand (`adjP j`, `adjI i`) holding the current
*adjoint*.  Processing instruction `k`, `v = a ∘ b` with adjoint `g`:
* `+`: `adj a += g`, `adj b += g`;
* `-`: `adj a += g`, `adj b -= g`;
* `×`: `adj a += g * b`, `adj b += g * a`.

Each step appends at most `4` instructions, so the new program has at most `5 ℓ` instructions.

## Correctness

Fix an input `i₀` and write `D = ∂/∂x_{i₀}`, `v_j` for the value of instruction `j`.  The
invariant after processing instructions `ℓ-1, …, k` is
`D(out) = ∑_{j<k} adjP_j · D(v_j) + adjI_{i₀}`;
for `k = ℓ` it holds by the choice of the seeds, and for `k = 0` it says `adjI_{i₀} = D(out)`.
-/

noncomputable section

open MvPolynomial

namespace ClassSep

/-- The polynomial computed at operand `o` by the program graph `prog` with constants `c`. -/
def progOutput {σ : Type} (prog : SLP σ ℕ) (c : ℕ → ℝ) (o : Operand σ ℕ) : MvPolynomial σ ℝ :=
  (o.instantiate c).eval (prog.instantiate c).values

namespace BaurStrassen

variable {σ : Type}

/-! ### Generic facts about the semantics of programs -/

theorem values_append_single (P : SLP σ ℝ) (ins : Instr σ ℝ) :
    SLP.values (P ++ [ins]) = P.values ++ [ins.eval P.values] := by
  simp [SLP.values, List.foldl_append]

theorem length_values (P : SLP σ ℝ) : P.values.length = P.length := by
  induction P using List.reverseRecOn with
  | nil => rfl
  | append_singleton P ins ih => simp [values_append_single, ih]

theorem values_prefix {P Q : SLP σ ℝ} (h : P <+: Q) : P.values <+: Q.values := by
  obtain ⟨t, rfl⟩ := h
  induction t using List.reverseRecOn with
  | nil => simp
  | append_singleton t ins ih =>
    rw [← List.append_assoc, values_append_single]
    exact ih.trans (List.prefix_append _ _)

theorem getD_of_prefix {W W' : List (MvPolynomial σ ℝ)} (h : W <+: W') {j : ℕ}
    (hj : j < W.length) : W'.getD j 0 = W.getD j 0 := by
  obtain ⟨t, rfl⟩ := h
  exact List.getD_append _ _ _ _ hj

/-! ### Evaluation of program graphs -/

/-- Evaluation of an operand of a program graph with constants `c` on a list of values. -/
def ev (c : ℕ → ℝ) (W : List (MvPolynomial σ ℝ)) (o : Operand σ ℕ) : MvPolynomial σ ℝ :=
  (o.instantiate c).eval W

/-- The values of a program graph with constants `c`. -/
def vals (c : ℕ → ℝ) (P : SLP σ ℕ) : List (MvPolynomial σ ℝ) :=
  (P.instantiate c).values

@[simp] theorem ev_input (c : ℕ → ℝ) (W : List (MvPolynomial σ ℝ)) (i : σ) :
    ev c W (.input i) = X i := rfl

@[simp] theorem ev_const (c : ℕ → ℝ) (W : List (MvPolynomial σ ℝ)) (m : ℕ) :
    ev c W (.const m : Operand σ ℕ) = C (c m) := rfl

@[simp] theorem ev_prev (c : ℕ → ℝ) (W : List (MvPolynomial σ ℝ)) (j : ℕ) :
    ev c W (.prev j : Operand σ ℕ) = W.getD j 0 := rfl

theorem vals_append_single (c : ℕ → ℝ) (P : SLP σ ℕ) (ins : Instr σ ℕ) :
    vals c (P ++ [ins]) =
      vals c P ++ [ins.op.apply (ev c (vals c P) ins.a) (ev c (vals c P) ins.b)] := by
  simp only [vals, SLP.instantiate, List.map_append, List.map_cons, List.map_nil]
  rw [values_append_single]
  rfl

theorem length_vals (c : ℕ → ℝ) (P : SLP σ ℕ) : (vals c P).length = P.length := by
  simp [vals, length_values, SLP.instantiate]

theorem vals_prefix (c : ℕ → ℝ) {P Q : SLP σ ℕ} (h : P <+: Q) : vals c P <+: vals c Q :=
  values_prefix (h.map _)

/-- `o` only refers to positions `< n`. -/
def Valid (n : ℕ) : Operand σ ℕ → Prop
  | .prev j => j < n
  | _ => True

theorem Valid.mono {n m : ℕ} {o : Operand σ ℕ} (h : Valid n o) (hnm : n ≤ m) : Valid m o := by
  cases o with
  | prev j => exact lt_of_lt_of_le h hnm
  | _ => trivial

theorem ev_of_prefix (c : ℕ → ℝ) {W W' : List (MvPolynomial σ ℝ)} (h : W <+: W')
    {o : Operand σ ℕ} (ho : Valid W.length o) : ev c W' o = ev c W o := by
  cases o with
  | prev j => exact getD_of_prefix h ho
  | _ => rfl

theorem ev_mono (c : ℕ → ℝ) {P Q : SLP σ ℕ} (h : P <+: Q) {o : Operand σ ℕ}
    (ho : Valid P.length o) : ev c (vals c Q) o = ev c (vals c P) o :=
  ev_of_prefix c (vals_prefix c h) (by rwa [length_vals])

theorem ev_last (c : ℕ → ℝ) (P : SLP σ ℕ) (ins : Instr σ ℕ) :
    ev c (vals c (P ++ [ins])) (.prev P.length) =
      ins.op.apply (ev c (vals c P) ins.a) (ev c (vals c P) ins.b) := by
  rw [ev_prev, vals_append_single, List.getD_append_right _ _ _ _ (by rw [length_vals]),
    length_vals]
  simp

/-! ### The construction -/

/-- The state of the reverse pass: the program built so far and the operands holding the
current adjoints of the instructions and of the inputs. -/
structure St (σ : Type) where
  p : SLP σ ℕ
  adjP : ℕ → Operand σ ℕ
  adjI : σ → Operand σ ℕ

/-- Append an instruction. -/
def push (S : St σ) (ins : Instr σ ℕ) : St σ := ⟨S.p ++ [ins], S.adjP, S.adjI⟩

/-- `adj x := adj x ∘ y` (with `∘ = op`); constants have no adjoint. -/
def accum [DecidableEq σ] (S : St σ) (x : Operand σ ℕ) (op : ArithOp) (y : Operand σ ℕ) :
    St σ :=
  match x with
  | .prev j => ⟨S.p ++ [⟨op, S.adjP j, y⟩], Function.update S.adjP j (.prev S.p.length), S.adjI⟩
  | .input i => ⟨S.p ++ [⟨op, S.adjI i, y⟩], S.adjP, Function.update S.adjI i (.prev S.p.length)⟩
  | .const _ => S

/-- The operand `x` of instruction `k`, as an operand of the new program: constants shifted by
`2`, and forward references (which read `0`) replaced by the constant slot `0`. -/
def normOp (k : ℕ) : Operand σ ℕ → Operand σ ℕ
  | .input i => .input i
  | .const m => .const (m + 2)
  | .prev j => if j < k then .prev j else .const 0

/-- Propagate the adjoint `g` of an instruction `a ∘ b`. -/
def stepCore [DecidableEq σ] (g : Operand σ ℕ) (op : ArithOp) (a b : Operand σ ℕ) (S : St σ) :
    St σ :=
  match op with
  | .add => accum (accum S a .add g) b .add g
  | .sub => accum (accum S a .add g) b .sub g
  | .mul =>
    let S₂ := accum (push S ⟨.mul, g, b⟩) a .add (.prev S.p.length)
    accum (push S₂ ⟨.mul, g, a⟩) b .add (.prev S₂.p.length)

/-- Process instruction `k`. -/
def step [DecidableEq σ] (k : ℕ) (ins : Instr σ ℕ) (S : St σ) : St σ :=
  stepCore (S.adjP k) ins.op (normOp k ins.a) (normOp k ins.b) S

/-- The reverse pass over the instructions `k, k+1, …` (processed from the last one). -/
def back [DecidableEq σ] : ℕ → List (Instr σ ℕ) → St σ → St σ
  | _, [], S => S
  | k, ins :: rest, S => step k ins (back (k + 1) rest S)

/-- The arrangement of constants: slot `0` holds `0`, slot `1` holds `1`, slot `m + 2` holds
the constant `c m` of the original program. -/
def cmap (c : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | m + 2 => c m

/-- Shift the constant slots by `2`. -/
def shiftOp : Operand σ ℕ → Operand σ ℕ
  | .input i => .input i
  | .const m => .const (m + 2)
  | .prev j => .prev j

/-- The forward copy of the program. -/
def fwd (prog : SLP σ ℕ) : SLP σ ℕ :=
  prog.map fun ins => ⟨ins.op, shiftOp ins.a, shiftOp ins.b⟩

/-- Initial adjoints of the instructions: `1` at the output. -/
def seedP : Operand σ ℕ → ℕ → Operand σ ℕ
  | .prev j => Function.update (fun _ => .const 0) j (.const 1)
  | _ => fun _ => .const 0

/-- Initial adjoints of the inputs: `1` at the output. -/
def seedI [DecidableEq σ] : Operand σ ℕ → σ → Operand σ ℕ
  | .input i => Function.update (fun _ => .const 0) i (.const 1)
  | _ => fun _ => .const 0

/-- The initial state of the reverse pass. -/
def init [DecidableEq σ] (prog : SLP σ ℕ) (o : Operand σ ℕ) : St σ :=
  ⟨fwd prog, seedP (normOp prog.length o), seedI (normOp prog.length o)⟩

/-- The final state of the reverse pass. -/
def result [DecidableEq σ] (prog : SLP σ ℕ) (o : Operand σ ℕ) : St σ :=
  back 0 prog (init prog o)

/-! ### Length -/

theorem length_accum [DecidableEq σ] (S : St σ) (x : Operand σ ℕ) (op : ArithOp)
    (y : Operand σ ℕ) : (accum S x op y).p.length ≤ S.p.length + 1 := by
  cases x <;> simp [accum]

theorem length_stepCore [DecidableEq σ] (g : Operand σ ℕ) (op : ArithOp) (a b : Operand σ ℕ)
    (S : St σ) : (stepCore g op a b S).p.length ≤ S.p.length + 4 := by
  cases op with
  | add =>
    have h1 := length_accum S a .add g
    have h2 := length_accum (accum S a .add g) b .add g
    simp only [stepCore]; omega
  | sub =>
    have h1 := length_accum S a .add g
    have h2 := length_accum (accum S a .add g) b .sub g
    simp only [stepCore]; omega
  | mul =>
    have h1 := length_accum (push S ⟨.mul, g, b⟩) a .add (.prev S.p.length)
    have h2 := length_accum (push (accum (push S ⟨.mul, g, b⟩) a .add (.prev S.p.length))
      ⟨.mul, g, a⟩) b .add (.prev (accum (push S ⟨.mul, g, b⟩) a .add (.prev S.p.length)).p.length)
    simp only [stepCore]
    simp only [push, List.length_append, List.length_cons, List.length_nil] at h1 h2 ⊢
    omega

theorem length_back [DecidableEq σ] :
    ∀ (rest : List (Instr σ ℕ)) (k : ℕ) (S : St σ),
      (back k rest S).p.length ≤ S.p.length + 4 * rest.length
  | [], _, S => by simp [back]
  | ins :: rest, k, S => by
    have h1 := length_back rest (k + 1) S
    have h2 := length_stepCore ((back (k + 1) rest S).adjP k) ins.op (normOp k ins.a)
      (normOp k ins.b) (back (k + 1) rest S)
    simp only [back, step, List.length_cons]
    omega

/-! ### Semantics of the state -/

section Sem

variable (c : ℕ → ℝ)

/-- The values of the adjoints of the instructions. -/
def AP (S : St σ) (j : ℕ) : MvPolynomial σ ℝ := ev c (vals c S.p) (S.adjP j)

/-- The values of the adjoints of the inputs. -/
def AI (S : St σ) (i : σ) : MvPolynomial σ ℝ := ev c (vals c S.p) (S.adjI i)

/-- All adjoints refer to existing instructions. -/
def WF (S : St σ) : Prop :=
  (∀ j, Valid S.p.length (S.adjP j)) ∧ ∀ i, Valid S.p.length (S.adjI i)

/-- `D x` for an operand `x`, where `dv j = D (v_j)`. -/
def dOp (i₀ : σ) (dv : ℕ → MvPolynomial σ ℝ) : Operand σ ℕ → MvPolynomial σ ℝ
  | .prev j => dv j
  | .input i => pderiv i₀ (X i)
  | .const _ => 0

/-- The quantity `∑_{j<k} adjP_j · D(v_j) + adjI_{i₀}` of the invariant. -/
def Φ (i₀ : σ) (dv : ℕ → MvPolynomial σ ℝ) (k : ℕ) (S : St σ) : MvPolynomial σ ℝ :=
  ∑ j ∈ Finset.range k, AP c S j * dv j + AI c S i₀

theorem sum_update_mul {k j : ℕ} (hj : j < k) (f d : ℕ → MvPolynomial σ ℝ)
    (v : MvPolynomial σ ℝ) :
    ∑ j' ∈ Finset.range k, Function.update f j v j' * d j' =
      ∑ j' ∈ Finset.range k, f j' * d j' + (v - f j) * d j := by
  have hm : j ∈ Finset.range k := Finset.mem_range.2 hj
  rw [← Finset.add_sum_erase _ _ hm, ← Finset.add_sum_erase _ _ hm, Function.update_self]
  have : ∑ x ∈ (Finset.range k).erase j, Function.update f j v x * d x =
      ∑ x ∈ (Finset.range k).erase j, f x * d x :=
    Finset.sum_congr rfl fun x hx => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
  rw [this]
  ring

/-! #### `push` -/

theorem WF_push {S : St σ} (hS : WF S) (ins : Instr σ ℕ) : WF (push S ins) := by
  refine ⟨fun j => (hS.1 j).mono ?_, fun i => (hS.2 i).mono ?_⟩ <;> simp [push]

theorem prefix_push (S : St σ) (ins : Instr σ ℕ) : S.p <+: (push S ins).p :=
  List.prefix_append _ _

theorem AP_push {S : St σ} (hS : WF S) (ins : Instr σ ℕ) : AP c (push S ins) = AP c S :=
  funext fun j => ev_mono c (prefix_push S ins) (hS.1 j)

theorem AI_push {S : St σ} (hS : WF S) (ins : Instr σ ℕ) : AI c (push S ins) = AI c S :=
  funext fun i => ev_mono c (prefix_push S ins) (hS.2 i)

theorem Φ_push {S : St σ} (hS : WF S) (ins : Instr σ ℕ) (i₀ : σ) (dv : ℕ → MvPolynomial σ ℝ)
    (k : ℕ) : Φ c i₀ dv k (push S ins) = Φ c i₀ dv k S := by
  simp only [Φ, AP_push c hS, AI_push c hS]

/-! #### `accum` -/

theorem prefix_accum [DecidableEq σ] (S : St σ) (x : Operand σ ℕ) (op : ArithOp)
    (y : Operand σ ℕ) : S.p <+: (accum S x op y).p := by
  cases x with
  | const m => exact List.prefix_refl _
  | _ => exact List.prefix_append _ _

theorem WF_accum [DecidableEq σ] {S : St σ} (hS : WF S) (x : Operand σ ℕ) (op : ArithOp)
    (y : Operand σ ℕ) : WF (accum S x op y) := by
  cases x with
  | const m => exact hS
  | prev j =>
    refine ⟨fun j' => ?_, fun i => (hS.2 i).mono (by simp [accum])⟩
    simp only [accum]
    by_cases h : j' = j
    · subst h; simp [Valid]
    · rw [Function.update_of_ne h]; exact (hS.1 j').mono (by simp)
  | input i₁ =>
    refine ⟨fun j => (hS.1 j).mono (by simp [accum]), fun i => ?_⟩
    simp only [accum]
    by_cases h : i = i₁
    · subst h; simp [Valid]
    · rw [Function.update_of_ne h]; exact (hS.2 i).mono (by simp)

theorem ev_accum [DecidableEq σ] {S : St σ} (x : Operand σ ℕ) (op : ArithOp) (y : Operand σ ℕ)
    {o : Operand σ ℕ} (ho : Valid S.p.length o) :
    ev c (vals c (accum S x op y).p) o = ev c (vals c S.p) o :=
  ev_mono c (prefix_accum S x op y) ho

theorem apply_zero {op : ArithOp} (hop : op ≠ .mul) (a : MvPolynomial σ ℝ) :
    op.apply a 0 = a := by
  cases op <;> simp_all [ArithOp.apply]

theorem Φ_accum [DecidableEq σ] {S : St σ} (hS : WF S) {x : Operand σ ℕ} {op : ArithOp}
    {y : Operand σ ℕ} (i₀ : σ) (dv : ℕ → MvPolynomial σ ℝ) {k : ℕ} (hx : Valid k x)
    (hop : op ≠ .mul) :
    Φ c i₀ dv k (accum S x op y) =
      op.apply (Φ c i₀ dv k S) (ev c (vals c S.p) y * dOp i₀ dv x) := by
  cases x with
  | const m => simp only [accum, dOp, mul_zero, apply_zero hop]
  | prev j =>
    have hAP : AP c (accum S (.prev j) op y) =
        Function.update (AP c S) j (op.apply (AP c S j) (ev c (vals c S.p) y)) := by
      funext j'
      by_cases h : j' = j
      · subst h
        simp only [AP, accum, Function.update_self]
        exact ev_last c S.p ⟨op, S.adjP j', y⟩
      · simp only [AP, accum, Function.update_of_ne h]
        exact ev_mono c (List.prefix_append _ _) (hS.1 j')
    have hAI : AI c (accum S (.prev j) op y) = AI c S :=
      funext fun i => ev_mono c (List.prefix_append _ _) (hS.2 i)
    simp only [Φ, hAP, hAI, dOp]
    rw [sum_update_mul hx]
    cases op <;> simp_all [ArithOp.apply] <;> ring
  | input i =>
    have hAP : AP c (accum S (.input i) op y) = AP c S :=
      funext fun j => ev_mono c (List.prefix_append _ _) (hS.1 j)
    have hAI : AI c (accum S (.input i) op y) =
        Function.update (AI c S) i (op.apply (AI c S i) (ev c (vals c S.p) y)) := by
      funext i'
      by_cases h : i' = i
      · subst h
        simp only [AI, accum, Function.update_self]
        exact ev_last c S.p ⟨op, S.adjI i', y⟩
      · simp only [AI, accum, Function.update_of_ne h]
        exact ev_mono c (List.prefix_append _ _) (hS.2 i')
    simp only [Φ, hAP, hAI, dOp]
    by_cases h : i₀ = i
    · subst h
      simp only [Function.update_self, pderiv_X_self, mul_one]
      cases op <;> simp_all [ArithOp.apply] <;> ring
    · rw [Function.update_of_ne h, pderiv_X_of_ne (Ne.symm h), mul_zero, apply_zero hop]

/-! #### One step -/

theorem stepCore_spec [DecidableEq σ] {S : St σ} (hS : WF S) (i₀ : σ)
    (dv : ℕ → MvPolynomial σ ℝ) {k : ℕ}
    (g : Operand σ ℕ) (op : ArithOp) (a b : Operand σ ℕ)
    (hg : Valid S.p.length g) (ha : Valid S.p.length a)
    (hak : Valid k a) (hbk : Valid k b)
    (hda : dOp i₀ dv a = pderiv i₀ (ev c (vals c S.p) a))
    (hdb : dOp i₀ dv b = pderiv i₀ (ev c (vals c S.p) b)) :
    WF (stepCore g op a b S) ∧ S.p <+: (stepCore g op a b S).p ∧
      Φ c i₀ dv k (stepCore g op a b S) = Φ c i₀ dv k S +
        ev c (vals c S.p) g *
          pderiv i₀ (op.apply (ev c (vals c S.p) a) (ev c (vals c S.p) b)) := by
  cases op with
  | add =>
    set S₁ := accum S a .add g with hS₁
    have hS₁wf : WF S₁ := WF_accum hS a .add g
    have hp₁ : S.p <+: S₁.p := prefix_accum S a .add g
    refine ⟨WF_accum hS₁wf b .add g, hp₁.trans (prefix_accum _ _ _ _), ?_⟩
    simp only [stepCore]
    rw [Φ_accum c hS₁wf i₀ dv hbk (by decide), Φ_accum c hS i₀ dv hak (by decide),
      ev_accum c a .add g hg, hda, hdb]
    simp only [ArithOp.apply, map_add]
    ring
  | sub =>
    set S₁ := accum S a .add g with hS₁
    have hS₁wf : WF S₁ := WF_accum hS a .add g
    have hp₁ : S.p <+: S₁.p := prefix_accum S a .add g
    refine ⟨WF_accum hS₁wf b .sub g, hp₁.trans (prefix_accum _ _ _ _), ?_⟩
    simp only [stepCore]
    rw [Φ_accum c hS₁wf i₀ dv hbk (by decide), Φ_accum c hS i₀ dv hak (by decide),
      ev_accum c a .add g hg, hda, hdb]
    simp only [ArithOp.apply, map_sub]
    ring
  | mul =>
    set S₁ := push S ⟨.mul, g, b⟩ with hS₁
    have hS₁wf : WF S₁ := WF_push hS _
    have hp₁ : S.p <+: S₁.p := prefix_push S _
    set S₂ := accum S₁ a .add (.prev S.p.length) with hS₂
    have hS₂wf : WF S₂ := WF_accum hS₁wf a .add _
    have hp₂ : S₁.p <+: S₂.p := prefix_accum _ _ _ _
    set S₃ := push S₂ ⟨.mul, g, a⟩ with hS₃
    have hS₃wf : WF S₃ := WF_push hS₂wf _
    have hp₃ : S₂.p <+: S₃.p := prefix_push _ _
    have hp₁₂ : S.p <+: S₂.p := hp₁.trans hp₂
    refine ⟨WF_accum hS₃wf b .add _, (hp₁₂.trans hp₃).trans (prefix_accum _ _ _ _), ?_⟩
    have e₁ : ev c (vals c S₁.p) (.prev S.p.length) =
        ev c (vals c S.p) g * ev c (vals c S.p) b := ev_last c S.p ⟨.mul, g, b⟩
    have e₂ : ev c (vals c S₃.p) (.prev S₂.p.length) =
        ev c (vals c S.p) g * ev c (vals c S.p) a := by
      have := ev_last c S₂.p ⟨.mul, g, a⟩
      simp only [ArithOp.apply] at this
      rw [ev_mono c hp₁₂ hg, ev_mono c hp₁₂ ha] at this
      exact this
    show Φ c i₀ dv k (accum S₃ b .add (.prev S₂.p.length)) = _
    rw [Φ_accum c hS₃wf i₀ dv hbk (by decide), Φ_push c hS₂wf,
      Φ_accum c hS₁wf i₀ dv hak (by decide), Φ_push c hS, e₁, e₂, hda, hdb]
    simp only [ArithOp.apply, pderiv_mul]
    ring

end Sem

/-! #### The reverse pass -/

theorem prefix_stepCore [DecidableEq σ] (g : Operand σ ℕ) (op : ArithOp) (a b : Operand σ ℕ)
    (S : St σ) : S.p <+: (stepCore g op a b S).p := by
  cases op with
  | add => exact (prefix_accum _ _ _ _).trans (prefix_accum _ _ _ _)
  | sub => exact (prefix_accum _ _ _ _).trans (prefix_accum _ _ _ _)
  | mul =>
    exact (((prefix_push _ _).trans (prefix_accum _ _ _ _)).trans (prefix_push _ _)).trans
      (prefix_accum _ _ _ _)

theorem prefix_back [DecidableEq σ] :
    ∀ (rest : List (Instr σ ℕ)) (k : ℕ) (S : St σ), S.p <+: (back k rest S).p
  | [], _, _ => List.prefix_refl _
  | _ :: rest, k, S => (prefix_back rest (k + 1) S).trans (prefix_stepCore _ _ _ _ _)

theorem valid_normOp (k : ℕ) (x : Operand σ ℕ) : Valid k (normOp k x) := by
  cases x with
  | prev j =>
    simp only [normOp]
    split_ifs with h
    · exact h
    · trivial
  | _ => trivial

theorem ev_normOp (c : ℕ → ℝ) {V W : List (MvPolynomial σ ℝ)} (h : V <+: W)
    (x : Operand σ ℕ) : ev (cmap c) W (normOp V.length x) = ev c V x := by
  cases x with
  | input i => rfl
  | const m => rfl
  | prev j =>
    simp only [normOp]
    split_ifs with hj
    · exact getD_of_prefix h hj
    · simp only [ev_const, ev_prev, cmap, map_zero]
      rw [List.getD_eq_default _ _ (not_lt.1 hj)]

theorem dOp_normOp (c : ℕ → ℝ) (i₀ : σ) {V W : List (MvPolynomial σ ℝ)} (h : V <+: W)
    {k : ℕ} (hk : k ≤ V.length) (x : Operand σ ℕ) :
    dOp i₀ (fun j => pderiv i₀ (V.getD j 0)) (normOp k x) =
      pderiv i₀ (ev c W (normOp k x)) := by
  cases x with
  | input i => rfl
  | const m => simp [normOp, dOp]
  | prev j =>
    simp only [normOp]
    split_ifs with hj
    · simp only [dOp, ev_prev]
      rw [getD_of_prefix h (lt_of_lt_of_le hj hk)]
    · simp [dOp]

theorem vals_fwd (c : ℕ → ℝ) (prog : SLP σ ℕ) : vals (cmap c) (fwd prog) = vals c prog := by
  have h : ∀ x : Operand σ ℕ, (shiftOp x).instantiate (cmap c) = x.instantiate c := by
    intro x; cases x <;> rfl
  simp only [vals, fwd, SLP.instantiate, List.map_map]
  congr 2
  funext ins
  simp [h]

theorem length_fwd (prog : SLP σ ℕ) : (fwd prog).length = prog.length := by
  simp [fwd]

/-- The invariant is preserved by the reverse pass over the instructions `pre.length, …`. -/
theorem back_spec [DecidableEq σ] (c : ℕ → ℝ) (i₀ : σ) (prog : SLP σ ℕ)
    (target : MvPolynomial σ ℝ) :
    ∀ (rest pre : List (Instr σ ℕ)) (S : St σ), pre ++ rest = prog →
      WF S → fwd prog <+: S.p →
      Φ (cmap c) i₀ (fun j => pderiv i₀ ((vals c prog).getD j 0)) (pre.length + rest.length) S
        = target →
      WF (back pre.length rest S) ∧ fwd prog <+: (back pre.length rest S).p ∧
      Φ (cmap c) i₀ (fun j => pderiv i₀ ((vals c prog).getD j 0)) pre.length
        (back pre.length rest S) = target := by
  intro rest
  induction rest with
  | nil =>
    intro pre S _ hS hp hΦ
    simp only [List.length_nil, add_zero] at hΦ
    exact ⟨hS, hp, hΦ⟩
  | cons ins rest ih =>
    intro pre S hpre hS hp hΦ
    have hpre' : (pre ++ [ins]) ++ rest = prog := by simpa using hpre
    have hΦ₀ : Φ (cmap c) i₀ (fun j => pderiv i₀ ((vals c prog).getD j 0))
        ((pre ++ [ins]).length + rest.length) S = target := by
      rw [← hΦ]; congr 1; simp; omega
    obtain ⟨hT, hpT, hΦT⟩ := ih (pre ++ [ins]) S hpre' hS hp hΦ₀
    simp only [List.length_append, List.length_cons, List.length_nil, zero_add] at hT hpT hΦT
    show WF (step pre.length ins (back (pre.length + 1) rest S)) ∧ _
    set T := back (pre.length + 1) rest S with hTdef
    set k := pre.length with hk
    set V := vals c prog with hV
    set dv : ℕ → MvPolynomial σ ℝ := fun j => pderiv i₀ (V.getD j 0) with hdv
    -- the values of the new program extend those of the old one
    have hVW : V <+: vals (cmap c) T.p := by
      rw [hV, ← vals_fwd c prog]; exact vals_prefix _ hpT
    have hlenV : V.length = prog.length := length_vals c prog
    have hkn : k + 1 ≤ prog.length := by
      rw [← hpre]; simp [k]
    have hkV : k ≤ V.length := by omega
    have hkT : k ≤ T.p.length := by
      have := hpT.length_le
      rw [length_fwd] at this
      omega
    -- the values of the first `k` instructions
    have hVpre_len : (vals c pre).length = k := length_vals c pre
    have hVpre1 : vals c (pre ++ [ins]) <+: V := by
      rw [hV, ← hpre']; exact vals_prefix _ (List.prefix_append _ _)
    have hVpre : vals c pre <+: V := by
      refine List.IsPrefix.trans ?_ hVpre1
      rw [vals_append_single]; exact List.prefix_append _ _
    have hvk : V.getD k 0 =
        ins.op.apply (ev c (vals c pre) ins.a) (ev c (vals c pre) ins.b) := by
      rw [getD_of_prefix hVpre1 (by rw [length_vals]; simp [k]), vals_append_single,
        List.getD_append_right _ _ _ _ (by rw [hVpre_len])]
      simp [hVpre_len]
    have hevx : ∀ x : Operand σ ℕ,
        ev (cmap c) (vals (cmap c) T.p) (normOp k x) = ev c (vals c pre) x := by
      intro x
      rw [← hVpre_len]
      exact ev_normOp c (hVpre.trans hVW) x
    have hvalid : ∀ x : Operand σ ℕ, Valid T.p.length (normOp k x) :=
      fun x => (valid_normOp k x).mono hkT
    obtain ⟨hWF, hpref, hΦ'⟩ := stepCore_spec (cmap c) hT i₀ dv (T.adjP k) ins.op
      (normOp k ins.a) (normOp k ins.b) (hT.1 k) (hvalid _)
      (valid_normOp k _) (valid_normOp k _)
      (dOp_normOp (cmap c) i₀ hVW hkV _) (dOp_normOp (cmap c) i₀ hVW hkV _)
    refine ⟨hWF, hpT.trans hpref, ?_⟩
    show Φ (cmap c) i₀ dv k (step k ins T) = target
    rw [step, hΦ', ← hΦT, Φ, Φ, Finset.sum_range_succ, hevx, hevx, ← hvk]
    simp only [AP, dv]
    ring

theorem Φ_init [DecidableEq σ] (c : ℕ → ℝ) (i₀ : σ) (dv : ℕ → MvPolynomial σ ℝ)
    (P : SLP σ ℕ) {k : ℕ} (x : Operand σ ℕ) (hx : Valid k x) :
    Φ (cmap c) i₀ dv k ⟨P, seedP x, seedI x⟩ = dOp i₀ dv x := by
  cases x with
  | prev j =>
    have hj : j < k := hx
    simp only [Φ, AP, AI, seedP, seedI, dOp, ev_const, cmap, map_zero, add_zero]
    rw [Finset.sum_eq_single j]
    · simp [cmap]
    · intro b _ hb
      simp [Function.update_of_ne hb, cmap]
    · intro h; exact absurd (Finset.mem_range.2 hj) h
  | input i =>
    simp only [Φ, AP, AI, seedP, seedI, dOp, ev_const, cmap, map_zero, zero_mul,
      Finset.sum_const_zero, zero_add]
    by_cases h : i₀ = i
    · subst h; simp [cmap]
    · rw [Function.update_of_ne h, pderiv_X_of_ne (Ne.symm h)]; simp [cmap]
  | const m =>
    simp [Φ, AP, AI, seedP, seedI, dOp, cmap]

theorem WF_init [DecidableEq σ] (prog : SLP σ ℕ) (o : Operand σ ℕ) : WF (init prog o) := by
  constructor
  · intro j
    simp only [init]
    cases normOp prog.length o with
    | prev j₁ =>
      simp only [seedP]
      by_cases h : j = j₁
      · subst h; rw [Function.update_self]; trivial
      · rw [Function.update_of_ne h]; trivial
    | _ => trivial
  · intro i
    simp only [init]
    cases normOp prog.length o with
    | input i₁ =>
      simp only [seedI]
      by_cases h : i = i₁
      · subst h; rw [Function.update_self]; trivial
      · rw [Function.update_of_ne h]; trivial
    | _ => trivial

theorem result_spec [DecidableEq σ] (c : ℕ → ℝ) (i₀ : σ) (prog : SLP σ ℕ) (o : Operand σ ℕ) :
    AI (cmap c) (result prog o) i₀ = pderiv i₀ (ev c (vals c prog) o) := by
  set V := vals c prog with hV
  have hlenV : V.length = prog.length := length_vals c prog
  have hinit : Φ (cmap c) i₀ (fun j => pderiv i₀ (V.getD j 0))
      (([] : List (Instr σ ℕ)).length + prog.length) (init prog o) = pderiv i₀ (ev c V o) := by
    simp only [List.length_nil, zero_add, init]
    rw [Φ_init c i₀ _ _ _ (valid_normOp _ _)]
    have hVW : V <+: vals (cmap c) (fwd prog) := by rw [vals_fwd]
    rw [dOp_normOp (cmap c) i₀ hVW hlenV.ge, ← hlenV, ev_normOp c hVW]
  obtain ⟨-, -, hΦ⟩ := back_spec c i₀ prog _ prog [] (init prog o) (by simp)
    (WF_init prog o) (List.prefix_refl _) hinit
  simpa [Φ, result] using hΦ

theorem result_output [DecidableEq σ] (c : ℕ → ℝ) (prog : SLP σ ℕ) (o : Operand σ ℕ) :
    ev (cmap c) (vals (cmap c) (result prog o).p) (normOp prog.length o) =
      ev c (vals c prog) o := by
  have hp : vals c prog <+: vals (cmap c) (result prog o).p := by
    rw [← vals_fwd c prog]; exact vals_prefix _ (prefix_back prog 0 (init prog o))
  have := ev_normOp c hp o
  rwa [length_vals] at this

theorem length_result [DecidableEq σ] (prog : SLP σ ℕ) (o : Operand σ ℕ) :
    (result prog o).p.length ≤ 5 * (prog.length + 1) := by
  have h := length_back prog 0 (init prog o)
  have h' : (init prog o).p.length = prog.length := length_fwd prog
  simp only [result]
  omega

/-! ### From programs to program graphs -/

/-- The constants occurring in an operand. -/
def constList : Operand σ ℝ → List ℝ
  | .const a => [a]
  | _ => []

/-- Replace the constant `a` of an operand by the slot `L.idxOf a`. -/
def toSlot (L : List ℝ) : Operand σ ℝ → Operand σ ℕ
  | .input i => .input i
  | .const a => .const (L.idxOf a)
  | .prev j => .prev j

theorem toSlot_instantiate (L : List ℝ) (x : Operand σ ℝ) (hx : ∀ a ∈ constList x, a ∈ L) :
    (toSlot L x).instantiate (fun m => L.getD m 0) = x := by
  cases x with
  | const a =>
    have ha : a ∈ L := hx a (by simp [constList])
    simp only [toSlot, Operand.instantiate]
    rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem ha), List.getElem_idxOf]
  | _ => rfl

/-- The program graph of a program: every constant `a` is replaced by the slot `L.idxOf a`. -/
def graphOf (L : List ℝ) (P : SLP σ ℝ) : SLP σ ℕ :=
  P.map fun ins => ⟨ins.op, toSlot L ins.a, toSlot L ins.b⟩

/-- The constants occurring in a program and an output operand. -/
def allConsts (P : SLP σ ℝ) (o : Operand σ ℝ) : List ℝ :=
  P.flatMap (fun ins => constList ins.a ++ constList ins.b) ++ constList o

theorem graphOf_instantiate (P : SLP σ ℝ) (o : Operand σ ℝ) :
    (graphOf (allConsts P o) P).instantiate (fun m => (allConsts P o).getD m 0) = P := by
  simp only [graphOf, SLP.instantiate, List.map_map]
  conv_rhs => rw [← List.map_id P]
  apply List.map_congr_left
  intro ins hins
  have hmem : ∀ a, a ∈ constList ins.a ++ constList ins.b → a ∈ allConsts P o := by
    intro a ha
    exact List.mem_append_left _ (List.mem_flatMap.2 ⟨ins, hins, ha⟩)
  simp only [Function.comp_apply, id]
  rw [toSlot_instantiate _ _ fun a ha => hmem a (List.mem_append_left _ ha),
    toSlot_instantiate _ _ fun a ha => hmem a (List.mem_append_right _ ha)]

theorem toSlot_out_instantiate (P : SLP σ ℝ) (o : Operand σ ℝ) :
    (toSlot (allConsts P o) o).instantiate (fun m => (allConsts P o).getD m 0) = o :=
  toSlot_instantiate _ _ fun _ ha => List.mem_append_right _ ha

theorem length_graphOf (L : List ℝ) (P : SLP σ ℝ) : (graphOf L P).length = P.length := by
  simp [graphOf]

end BaurStrassen

open BaurStrassen in
/-- **Theorem 2.4 (Baur–Strassen)**, uniform version. -/
theorem baur_strassen :
    ∃ C : ℕ, ∀ {σ : Type} [DecidableEq σ] (prog : SLP σ ℕ) (o : Operand σ ℕ),
      ∃ (prog' : SLP σ ℕ) (o₀ : Operand σ ℕ) (od : σ → Operand σ ℕ)
        (cmap : (ℕ → ℝ) → ℕ → ℝ),
        prog'.length ≤ C * (prog.length + 1) ∧
        ∀ c : ℕ → ℝ, progOutput prog' (cmap c) o₀ = progOutput prog c o ∧
          ∀ i : σ, progOutput prog' (cmap c) (od i) = pderiv i (progOutput prog c o) :=
  ⟨5, fun {_} _ prog o => ⟨(result prog o).p, normOp prog.length o,
    fun i => (result prog o).adjI i, BaurStrassen.cmap, length_result prog o,
    fun c => ⟨result_output c prog o, fun i => result_spec c i prog o⟩⟩⟩

/-- **Theorem 2.4 (Baur–Strassen)**, as stated in the paper. -/
theorem baur_strassen' :
    ∃ C : ℕ, ∀ {σ : Type} [DecidableEq σ] (q : MvPolynomial σ ℝ) (ℓ : ℕ), HasSLP q ℓ →
      ∃ P : SLP σ ℝ, P.length ≤ C * (ℓ + 1) ∧ P.Computes q ∧ ∀ i, P.Computes (pderiv i q) := by
  obtain ⟨C, hC⟩ := baur_strassen
  refine ⟨C, fun {σ} _ q ℓ ⟨P, hPℓ, o, hq⟩ => ?_⟩
  obtain ⟨prog', o₀, od, cmap, hlen, hspec⟩ :=
    hC (BaurStrassen.graphOf (BaurStrassen.allConsts P o) P)
      (BaurStrassen.toSlot (BaurStrassen.allConsts P o) o)
  set cL : ℕ → ℝ := fun m => (BaurStrassen.allConsts P o).getD m 0 with hcL
  have hout : progOutput (BaurStrassen.graphOf (BaurStrassen.allConsts P o) P) cL
      (BaurStrassen.toSlot (BaurStrassen.allConsts P o) o) = q := by
    rw [progOutput, hcL, BaurStrassen.graphOf_instantiate, BaurStrassen.toSlot_out_instantiate,
      hq]
  obtain ⟨h₀, hd⟩ := hspec cL
  refine ⟨prog'.instantiate (cmap cL), ?_, ⟨o₀.instantiate (cmap cL), ?_⟩,
    fun i => ⟨(od i).instantiate (cmap cL), ?_⟩⟩
  · rw [BaurStrassen.length_graphOf] at hlen
    simp only [SLP.instantiate, List.length_map]
    exact hlen.trans (Nat.mul_le_mul_left _ (Nat.succ_le_succ hPℓ))
  · rw [← hout, ← h₀]; rfl
  · rw [← hout, ← hd i]; rfl

end ClassSep
