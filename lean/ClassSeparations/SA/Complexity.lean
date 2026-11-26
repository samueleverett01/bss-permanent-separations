import ClassSeparations.SA.Formula

/-!
# Complexity measures of formulas

Used to state effective quantifier elimination (BPR06, Theorem 14.16), which the paper uses in
Lemma 6.3 (d), and the counting bound (C) of Lemma 7.7.

* `size`: the number of atom occurrences (polynomial sign conditions);
* `maxDeg`: the largest total degree of an atom polynomial;
* `numBound`: the total number of quantified variables;
* `blocks`: the number of quantifier blocks of a prenex form whose first block is
  existential (alternation depth);
* `IsQF`: the formula is quantifier-free.
-/

noncomputable section

namespace ClassSep

/-- Number of atom occurrences. -/
def Fml.size : {α : Type} → Fml α → ℕ
  | _, .pos _ => 1
  | _, .zero _ => 1
  | _, .not φ => φ.size
  | _, .and φ ψ => φ.size + ψ.size
  | _, .ex φ => φ.size

/-- Largest total degree of an atom polynomial. -/
def Fml.maxDeg : {α : Type} → Fml α → ℕ
  | _, .pos p => p.totalDegree
  | _, .zero p => p.totalDegree
  | _, .not φ => φ.maxDeg
  | _, .and φ ψ => max φ.maxDeg ψ.maxDeg
  | _, .ex φ => φ.maxDeg

/-- Total number of quantified variables. -/
def Fml.numBound : {α : Type} → Fml α → ℕ
  | _, .pos _ => 0
  | _, .zero _ => 0
  | _, .not φ => φ.numBound
  | _, .and φ ψ => φ.numBound + ψ.numBound
  | _, .ex φ => φ.numBound + 1

/-- `(e, a)`: the number of quantifier blocks of a prenex form of the formula whose first block
is existential (`e`), respectively universal (`a`).  Empty leading blocks are allowed. -/
def Fml.blockPair : {α : Type} → Fml α → ℕ × ℕ
  | _, .pos _ => (0, 0)
  | _, .zero _ => (0, 0)
  | _, .not φ => ((φ.blockPair).2, (φ.blockPair).1)
  | _, .and φ ψ => (max φ.blockPair.1 ψ.blockPair.1, max φ.blockPair.2 ψ.blockPair.2)
  | _, .ex φ => (max 1 φ.blockPair.1, max 1 φ.blockPair.1 + 1)

/-- The number of quantifier blocks (alternation depth) of a formula. -/
def Fml.blocks {α : Type} (φ : Fml α) : ℕ := φ.blockPair.1

/-- The formula is quantifier-free. -/
def Fml.IsQF : {α : Type} → Fml α → Prop
  | _, .pos _ => True
  | _, .zero _ => True
  | _, .not φ => φ.IsQF
  | _, .and φ ψ => φ.IsQF ∧ ψ.IsQF
  | _, .ex _ => False

end ClassSep
