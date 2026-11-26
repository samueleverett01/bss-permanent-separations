import ClassSeparations.Basic.Circuits

/-!
# Algebraic computation trees (Definition 2.1)

A tree takes an input `w : ι → ℝ`.  A computation node applies `+, -, ×, /` to two operands,
each of which is an earlier value, an input coordinate or a real constant.  A test node
branches on `v ≥ 0` or on `v = 0`.  Leaves accept or reject.  An input that reaches a
division by zero is rejected.  The depth is the largest number of nodes on a path from the
root to a leaf (leaves included).

We record the outcome of a run as an `Option Bool`: `some b` means that the leaf with label
`b` was reached, and `none` means that a division by zero occurred.  An input is *accepted*
when the outcome is `some true`.  Working with outcomes makes the convention of §2.1 that
"every rejection happens at a leaf" unnecessary: a set of *marked outcomes* plays the role of
the marked leaves (e.g. `{none, some false}` for "the rejecting leaves are marked").

We allow a test to be applied to any operand (an earlier value, an input coordinate or a
constant).  This only enlarges the model, so all lower bounds remain valid for the trees of
the paper.
-/

noncomputable section

open Classical

namespace ClassSep

universe u

/-- An operand of a tree node. -/
inductive TArg (ι : Type u) where
  | input (i : ι)
  | const (c : ℝ)
  | val (j : ℕ)

/-- The four arithmetic operations of a tree. -/
inductive TOp where
  | add
  | sub
  | mul
  | div
  deriving DecidableEq

/-- The two kinds of tests: `v ≥ 0` and `v = 0`. -/
inductive TestKind where
  | ge
  | eq
  deriving DecidableEq

/-- An algebraic computation tree on inputs `w : ι → ℝ`. -/
inductive Tree (ι : Type u) where
  | leaf (accept : Bool)
  | comp (op : TOp) (a b : TArg ι) (next : Tree ι)
  | test (kind : TestKind) (v : TArg ι) (yes no : Tree ι)

variable {ι : Type u}

/-- Depth: the largest number of nodes on a path from the root to a leaf. -/
def Tree.depth : Tree ι → ℕ
  | .leaf _ => 1
  | .comp _ _ _ next => next.depth + 1
  | .test _ _ yes no => max yes.depth no.depth + 1

/-- Value of an operand, given the input and the values computed so far. -/
def TArg.eval (w : ι → ℝ) (vals : List ℝ) : TArg ι → ℝ
  | .input i => w i
  | .const c => c
  | .val j => vals.getD j 0

/-- Result of a test. -/
def TestKind.holds : TestKind → ℝ → Prop
  | .ge, v => 0 ≤ v
  | .eq, v => v = 0

/-- Run a tree on input `w`, with `vals` the values computed so far.  The outcome is
`some b` if the leaf labelled `b` is reached and `none` if a division by zero occurs. -/
def Tree.runFrom (w : ι → ℝ) : Tree ι → List ℝ → Option Bool
  | .leaf b, _ => some b
  | .comp op a b next, vals =>
      let x := a.eval w vals
      let y := b.eval w vals
      match op with
      | .add => next.runFrom w (vals ++ [x + y])
      | .sub => next.runFrom w (vals ++ [x - y])
      | .mul => next.runFrom w (vals ++ [x * y])
      | .div => if y = 0 then none else next.runFrom w (vals ++ [x / y])
  | .test k v yes no, vals =>
      if k.holds (v.eval w vals) then yes.runFrom w vals else no.runFrom w vals

/-- The outcome of the tree on input `w`. -/
def Tree.run (T : Tree ι) (w : ι → ℝ) : Option Bool := T.runFrom w []

/-- The tree accepts `w`. -/
def Tree.Accepts (T : Tree ι) (w : ι → ℝ) : Prop := T.run w = some true

/-- The real constants occurring in the tree. -/
def TArg.consts : TArg ι → Set ℝ
  | .const c => {c}
  | _ => ∅

/-- The set of real constants occurring in a tree. -/
def Tree.consts : Tree ι → Set ℝ
  | .leaf _ => ∅
  | .comp _ a b next => a.consts ∪ b.consts ∪ next.consts
  | .test _ v yes no => v.consts ∪ yes.consts ∪ no.consts

/-! ## Inputs `(x, y, z)` and `(x, y, z, u)` -/

/-- The input `(x, y, z) ∈ ℝ^α × ℝ × ℝ^γ` of a tree on `α ⊕ Unit ⊕ γ`. -/
def inp3 {α γ : Type} (x : α → ℝ) (y : ℝ) (z : γ → ℝ) : α ⊕ Unit ⊕ γ → ℝ :=
  Sum.elim x (Sum.elim (fun _ => y) z)

/-- The input `(x, y, z, u)` of a tree on `α ⊕ Unit ⊕ γ ⊕ δ`. -/
def inp4 {α γ δ : Type} (x : α → ℝ) (y : ℝ) (z : γ → ℝ) (u : δ → ℝ) :
    α ⊕ Unit ⊕ γ ⊕ δ → ℝ :=
  Sum.elim x (Sum.elim (fun _ => y) (Sum.elim z u))

end ClassSep
