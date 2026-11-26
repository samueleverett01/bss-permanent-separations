import Mathlib

/-!
# Straight-line programs, circuits and border complexity

Paper, §2.2 "Circuits and border complexity" and Definition 2.2.

* A *straight-line program* (SLP) over a commutative ring `A` with inputs indexed by `σ`
  is a list of instructions `a ∘ b` with `∘ ∈ {+, -, ×}`; each operand is an input
  coordinate, a constant of `A`, or the result of an earlier instruction.  Its number of
  operations is its length.  Programs whose constants are *slots* `k : ℕ` (to be filled
  later) are programs over the "constant type" `ℕ`; we call them *program graphs*.
* A *circuit* is a list of gates, each a variable, a constant, or the sum or product of
  two earlier gates; its size is its length.  A *circuit graph* (`Shape`) is a circuit whose
  constant gates are slots `k : ℕ`; a circuit is a shape together with a choice of constants
  `c : ℕ → A`.
* A circuit over the Laurent series field `ℝ((ε))` *approximates* `f ∈ ℝ[X]` if it computes
  `f + ε g` with all coefficients of `g` in `ℝ[[ε]]`.
-/

noncomputable section

open MvPolynomial

namespace ClassSep

universe u v w

/-! ## Straight-line programs -/

/-- An operand of a straight-line program: an input coordinate, a constant, or the value of
an earlier instruction (referenced by its position; out-of-range references read `0`). -/
inductive Operand (σ : Type u) (K : Type v) where
  | input (i : σ)
  | const (a : K)
  | prev (j : ℕ)

/-- The three arithmetic operations of a straight-line program. -/
inductive ArithOp where
  | add
  | sub
  | mul
  deriving DecidableEq

/-- One instruction of a straight-line program. -/
structure Instr (σ : Type u) (K : Type v) where
  op : ArithOp
  a : Operand σ K
  b : Operand σ K

/-- A straight-line program; its number of operations is its length. -/
abbrev SLP (σ : Type u) (K : Type v) := List (Instr σ K)

section SLPEval

variable {σ : Type u} {A : Type v} [CommRing A]

/-- Value of an operand, given the values of the earlier instructions. -/
def Operand.eval (vals : List (MvPolynomial σ A)) : Operand σ A → MvPolynomial σ A
  | .input i => X i
  | .const a => C a
  | .prev j => vals.getD j 0

/-- The polynomial operation of an arithmetic operation. -/
def ArithOp.apply {R : Type w} [CommRing R] : ArithOp → R → R → R
  | .add, p, q => p + q
  | .sub, p, q => p - q
  | .mul, p, q => p * q

/-- Value of an instruction, given the values of the earlier instructions. -/
def Instr.eval (vals : List (MvPolynomial σ A)) (ins : Instr σ A) : MvPolynomial σ A :=
  ins.op.apply (ins.a.eval vals) (ins.b.eval vals)

/-- The list of polynomials computed by the instructions of a program, in order. -/
def SLP.values (P : SLP σ A) : List (MvPolynomial σ A) :=
  P.foldl (fun vals ins => vals ++ [ins.eval vals]) []

/-- The program `P` computes `q`: `q` is an input coordinate, a constant, or the value of one
of the instructions of `P`. -/
def SLP.Computes (P : SLP σ A) (q : MvPolynomial σ A) : Prop :=
  ∃ o : Operand σ A, q = o.eval P.values

/-- `q` has a straight-line program with at most `ℓ` operations. -/
def HasSLP (q : MvPolynomial σ A) (ℓ : ℕ) : Prop :=
  ∃ P : SLP σ A, P.length ≤ ℓ ∧ P.Computes q

end SLPEval

/-- Fill the constant slots of a program graph. -/
def Operand.instantiate {σ : Type u} {K : Type v} (c : ℕ → K) : Operand σ ℕ → Operand σ K
  | .input i => .input i
  | .const k => .const (c k)
  | .prev j => .prev j

/-- Fill the constant slots of a program graph. -/
def SLP.instantiate {σ : Type u} {K : Type v} (c : ℕ → K) (P : SLP σ ℕ) : SLP σ K :=
  P.map fun ins => ⟨ins.op, ins.a.instantiate c, ins.b.instantiate c⟩

/-! ## Circuits -/

/-- A gate of a circuit graph.  `const k` is the `k`-th constant slot; `add j k`, `mul j k`
refer to earlier gates by position (out-of-range references read `0`). -/
inductive Gate (σ : Type u) where
  | var (i : σ)
  | const (k : ℕ)
  | add (j k : ℕ)
  | mul (j k : ℕ)

/-- A circuit graph: a list of gates.  Its size is its length. -/
abbrev Shape (σ : Type u) := List (Gate σ)

section CircuitEval

variable {σ : Type u} {A : Type v} [CommRing A]

/-- Value of a gate given the constants and the values of the earlier gates. -/
def Gate.eval (c : ℕ → A) (vals : List (MvPolynomial σ A)) : Gate σ → MvPolynomial σ A
  | .var i => X i
  | .const k => C (c k)
  | .add j k => vals.getD j 0 + vals.getD k 0
  | .mul j k => vals.getD j 0 * vals.getD k 0

/-- The polynomials computed by the gates of the circuit `(Γ, c)`, in order. -/
def Shape.values (Γ : Shape σ) (c : ℕ → A) : List (MvPolynomial σ A) :=
  Γ.foldl (fun vals g => vals ++ [g.eval c vals]) []

/-- The circuit `(Γ, c)` computes `q` at one of its gates. -/
def Shape.Computes (Γ : Shape σ) (c : ℕ → A) (q : MvPolynomial σ A) : Prop :=
  q ∈ Γ.values c

end CircuitEval

/-! ## Border complexity (Definition 2.2) -/

/-- `P ∈ ℝ((ε))[X]` is of the form `f + ε g` where every coefficient of `g` lies in `ℝ[[ε]]`:
every coefficient of `P` has no terms of negative order, and its constant term is the
corresponding coefficient of `f`. -/
def IsApprox {σ : Type u} (P : MvPolynomial σ (LaurentSeries ℝ)) (f : MvPolynomial σ ℝ) :
    Prop :=
  ∀ m, (P.coeff m).coeff 0 = f.coeff m ∧ ∀ j : ℤ, j < 0 → (P.coeff m).coeff j = 0

/-- The border complexity of `f` is at most `s`: some circuit of size at most `s` over the
field `ℝ((ε))` of formal Laurent series approximates `f`. -/
def BorderLE {σ : Type u} (f : MvPolynomial σ ℝ) (s : ℕ) : Prop :=
  ∃ (Γ : Shape σ) (c : ℕ → LaurentSeries ℝ), Γ.length ≤ s ∧ ∃ P, Γ.Computes c P ∧ IsApprox P f

/-- The border complexity of `f`: the least size of an approximating circuit. -/
def borderComplexity {σ : Type u} (f : MvPolynomial σ ℝ) : ℕ :=
  sInf {s | BorderLE f s}

/-! ## The permanent -/

/-- The permanent `per_m` of the `m × m` matrix of variables `X_{ij}`. -/
def per (m : ℕ) : MvPolynomial (Fin m × Fin m) ℝ :=
  ∑ π : Equiv.Perm (Fin m), ∏ i : Fin m, X (i, π i)

end ClassSep
