import ClassSeparations.Machines.Machine

/-!
# Complexity classes over the reals (§2.1)

A *language* is a set `L ⊆ ℝ^∞ = ⊔ₙ ℝⁿ`, i.e. a family of sets `L n ⊆ ℝⁿ`.

* `P_R`: decided by a machine in polynomial time.
* `NP_R`: `x ∈ L ↔ ∃ z ∈ ℝ^{q(|x|)}, M accepts (x, z)`, with `M` running in polynomial time
  (on all certificates).
* `coNP_R`: complements of `NP_R` languages.
* `Sigma2_R`: `x ∈ L ↔ ∃ z ∀ u, M accepts (x, z, u)`.
* `PAR_R`: decided by P-uniform families of algebraic circuits with sign gates of polynomial
  depth (and hence of at most exponential size) [BCSS98, Ch. 18].

The machine receives the block sizes in its index registers `I 0, I 1, …` and the concatenated
blocks in `R 0, R 1, …`.
-/

noncomputable section

open Classical

namespace ClassSep

/-- A language over the reals: a subset of each `ℝⁿ`. -/
abbrev Lang := ∀ n : ℕ, Set (Fin n → ℝ)

/-- The complement of a language. -/
def Lang.compl (L : Lang) : Lang := fun n => (L n)ᶜ

/-- `p` is bounded by a polynomial. -/
def PolyBounded (p : ℕ → ℕ) : Prop := ∃ C e : ℕ, ∀ n, p n ≤ C * (n + 1) ^ e

/-- The machine halts within `T` steps on the input with block sizes `sizes` and contents
`x`, with outcome `o`. -/
def Machine.HaltsWith (M : Machine) (T : ℕ) (sizes : List ℕ) {N : ℕ} (x : Fin N → ℝ)
    (o : Option Bool) : Prop :=
  M.run T (initConfig sizes (vecReg x)) = some o

/-- The machine halts within `T` steps. -/
def Machine.HaltsWithin (M : Machine) (T : ℕ) (sizes : List ℕ) {N : ℕ} (x : Fin N → ℝ) :
    Prop :=
  ∃ o, M.HaltsWith T sizes x o

/-- `P_ℝ`. -/
def P_R : Set Lang :=
  {L | ∃ (M : Machine) (p : ℕ → ℕ), PolyBounded p ∧ ∀ n (x : Fin n → ℝ),
    M.HaltsWithin (p n) [n] x ∧ (M.HaltsWith (p n) [n] x (some true) ↔ x ∈ L n)}

/-- `NP_ℝ`. -/
def NP_R : Set Lang :=
  {L | ∃ (M : Machine) (p q : ℕ → ℕ), PolyBounded p ∧ PolyBounded q ∧ ∀ n (x : Fin n → ℝ),
    (∀ z : Fin (q n) → ℝ, M.HaltsWithin (p n) [n, q n] (Fin.append x z)) ∧
    (x ∈ L n ↔ ∃ z : Fin (q n) → ℝ, M.HaltsWith (p n) [n, q n] (Fin.append x z) (some true))}

/-- `coNP_ℝ`. -/
def coNP_R : Set Lang := {L | L.compl ∈ NP_R}

/-- `Σ₂^ℝ`, the second existential level of the real polynomial hierarchy. -/
def Sigma2_R : Set Lang :=
  {L | ∃ (M : Machine) (p q₁ q₂ : ℕ → ℕ), PolyBounded p ∧ PolyBounded q₁ ∧ PolyBounded q₂ ∧
    ∀ n (x : Fin n → ℝ),
    (∀ (z : Fin (q₁ n) → ℝ) (u : Fin (q₂ n) → ℝ),
      M.HaltsWithin (p n) [n, q₁ n, q₂ n] (Fin.append (Fin.append x z) u)) ∧
    (x ∈ L n ↔ ∃ z : Fin (q₁ n) → ℝ, ∀ u : Fin (q₂ n) → ℝ,
      M.HaltsWith (p n) [n, q₁ n, q₂ n] (Fin.append (Fin.append x z) u) (some true))}

/-! ## Parallel polynomial time -/

/-- A gate of an algebraic circuit with sign gates. -/
inductive AGate where
  | input (i : ℕ)
  | const (c : ℝ)
  | arith (op : TOp) (j k : ℕ)
  /-- `1` if the value of gate `j` is `≥ 0`, else `0` -/
  | sign (j : ℕ)

/-- An algebraic circuit with sign gates: a list of gates referring to earlier gates. -/
abbrev ACircuit := List AGate

/-- The values of the gates on input `x` (`none` on a division by zero or an invalid
reference). -/
def ACircuit.values (C : ACircuit) (x : ℕ → ℝ) : Option (List ℝ) :=
  C.foldl (fun acc g => acc.bind fun vals =>
    match g with
    | .input i => some (vals ++ [x i])
    | .const c => some (vals ++ [c])
    | .arith op j k =>
        if hj : j < vals.length then if hk : k < vals.length then
          (op.apply? vals[j] vals[k]).map fun v => vals ++ [v]
        else none else none
    | .sign j => if hj : j < vals.length then
        some (vals ++ [if 0 ≤ vals[j] then 1 else 0]) else none) (some [])

/-- Depth of each gate (longest path from an input or constant); the depth of the circuit is
the maximum. -/
def ACircuit.gateDepths (C : ACircuit) : List ℕ :=
  C.foldl (fun ds g =>
    ds ++ [match g with
      | .input _ => 0
      | .const _ => 0
      | .arith _ j k => max (ds.getD j 0) (ds.getD k 0) + 1
      | .sign j => ds.getD j 0 + 1]) []

/-- The depth of a circuit. -/
def ACircuit.depth (C : ACircuit) : ℕ := C.gateDepths.foldl max 0

/-- The circuit decides `S ⊆ ℝⁿ`: its last gate takes the value `1` on `S` and `0` off `S`. -/
def ACircuit.Decides {n : ℕ} (C : ACircuit) (S : Set (Fin n → ℝ)) : Prop :=
  ∀ x : Fin n → ℝ, ∃ vals, C.values (vecReg x) = some vals ∧
    vals.getLast? = some (if x ∈ S then 1 else 0)

/-- Type code of a gate. -/
def AGate.code : AGate → ℝ
  | .input _ => 0
  | .const _ => 1
  | .arith .add _ _ => 2
  | .arith .sub _ _ => 3
  | .arith .mul _ _ => 4
  | .arith .div _ _ => 5
  | .sign _ => 6

/-- First operand of a gate (the input index for an input gate). -/
def AGate.op₁ : AGate → ℕ
  | .input i => i
  | .const _ => 0
  | .arith _ j _ => j
  | .sign j => j

/-- Second operand of a gate. -/
def AGate.op₂ : AGate → ℕ
  | .arith _ _ k => k
  | _ => 0

/-- Constant of a gate. -/
def AGate.cst : AGate → ℝ
  | .const c => c
  | _ => 0

/-- The description of a gate in the registers `R 0, …, R (2b+1)`: the type code, the `b`
binary digits (least significant first, as reals `0, 1`) of each operand, and the constant. -/
def AGate.describe (b : ℕ) (g : AGate) (k : ℕ) : ℝ :=
  if k = 0 then g.code
  else if k ≤ b then (if g.op₁.testBit (k - 1) then 1 else 0)
  else if k ≤ 2 * b then (if g.op₂.testBit (k - 1 - b) then 1 else 0)
  else g.cst

/-- The binary digits of `i` (least significant first), as reals `0`, `1`. -/
def bitsOf (b i : ℕ) : Fin b → ℝ := fun j => if i.testBit j then 1 else 0

/-- The machine `U` describes the circuit family `C` with index length `b` within time `p`: on
input `(n, i)` (block sizes `[n, b n]`, contents the binary digits of the gate index `i`) it
accepts within `p n` steps with the description of gate `i` of `C n` in its registers. -/
def Machine.Describes (U : Machine) (C : ℕ → ACircuit) (b p : ℕ → ℕ) : Prop :=
  ∀ n, ∀ i (hi : i < (C n).length), ∃ cfg : MConfig,
    U.runFinal (p n) (initConfig [n, b n] (vecReg (bitsOf (b n) i))) = some (cfg, some true) ∧
    ∀ k ≤ 2 * b n + 1, cfg.R k = ((C n)[i]'hi).describe (b n) k

/-- `PAR_ℝ`: languages decided by P-uniform families of algebraic circuits with sign gates of
polynomial depth (and size at most `2^{b(n)}`, all indices fitting in `b(n)` bits). -/
def PAR_R : Set Lang :=
  {L | ∃ (C : ℕ → ACircuit) (U : Machine) (b d p : ℕ → ℕ),
    PolyBounded b ∧ PolyBounded d ∧ PolyBounded p ∧ U.Describes C b p ∧
    ∀ n, (C n).length ≤ 2 ^ b n ∧ (∀ g ∈ C n, g.op₁ < 2 ^ b n ∧ g.op₂ < 2 ^ b n) ∧
      (C n).depth ≤ d n ∧ (C n).Decides (L n)}

end ClassSep
