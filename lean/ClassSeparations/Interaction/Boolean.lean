import ClassSeparations.Cert.Permanent
import ClassSeparations.Basic.Asymptotics

/-!
# Boolean messages (§7.1, Definition 7.1, Lemma 7.2, Theorem 7.3)

**Definition 7.1.**  A *verifier tree* is a tree as in Definition 2.1 with three further kinds
of nodes: coin nodes (two children), send nodes (labelled by a bit, one child) and receive
nodes (two children; the path continues with the bit received from the prover).  A *prover*
assigns a bit to every input and every transcript.  Given the input `w`, a prover and a coin
tape `r ∈ {0,1}^t` (`t` the depth), the verifier follows a path; at the `j`-th coin node it
uses `r_j`.  The acceptance probability is the probability over uniform `r` that the path
ends at an accepting leaf.  A protocol *decides* `L` on `W` if every `w ∈ W ∩ L` has a prover
with acceptance probability `≥ 2/3` and every `w ∈ W \ L` has acceptance probability `≤ 1/3`
for every prover.

**Lemma 7.2 (boundary test).**  If a Boolean-message protocol with a verifier tree of depth `t`
decides `{Y = f(X)}` or `{Y ≤ f(X)}` on an open set `W` that contains `(x, f(x))` for every `x`
in a nonempty open set `U`, then some nonzero multiple of `Y - f(X)` has a straight-line program
with at most `4t` operations.

**Theorem 7.3** (tree part).  A Boolean-message protocol deciding `{Y = per_m(X)}` on
`ℝ^{m²} × ℝ` has depth `t_m ≥ 2^{Ω((log m)^{4/3})}`.
-/

noncomputable section

open MvPolynomial Set Filter Topology Classical

namespace ClassSep

/-- A verifier tree (Definition 7.1). -/
inductive VTree (ι : Type) where
  | leaf (accept : Bool)
  | comp (op : TOp) (a b : TArg ι) (next : VTree ι)
  | test (kind : TestKind) (v : TArg ι) (yes no : VTree ι)
  | coin (c₀ c₁ : VTree ι)
  | send (bit : Bool) (next : VTree ι)
  | recv (r₀ r₁ : VTree ι)

namespace VTree

variable {ι : Type}

/-- Depth of a verifier tree. -/
def depth : VTree ι → ℕ
  | .leaf _ => 1
  | .comp _ _ _ next => next.depth + 1
  | .test _ _ yes no => max yes.depth no.depth + 1
  | .coin c₀ c₁ => max c₀.depth c₁.depth + 1
  | .send _ next => next.depth + 1
  | .recv r₀ r₁ => max r₀.depth r₁.depth + 1

/-- A transcript: the bits sent (`true`) and received (`false`), in order. -/
abbrev Transcript := List (Bool × Bool)

/-- A prover assigns a bit to every input and every transcript. -/
abbrev Prover (ι : Type) := (ι → ℝ) → Transcript → Bool

/-- Run a verifier tree.  `vals`: values computed so far; `s`: transcript so far; `j`: number of
coins used so far.  `none` signals a division by zero (rejection). -/
def runFrom (w : ι → ℝ) (P : Prover ι) (r : ℕ → Bool) :
    VTree ι → List ℝ → Transcript → ℕ → Option Bool
  | .leaf b, _, _, _ => some b
  | .comp op a b next, vals, s, j =>
      let x := a.eval w vals
      let y := b.eval w vals
      match op with
      | .add => next.runFrom w P r (vals ++ [x + y]) s j
      | .sub => next.runFrom w P r (vals ++ [x - y]) s j
      | .mul => next.runFrom w P r (vals ++ [x * y]) s j
      | .div => if y = 0 then none else next.runFrom w P r (vals ++ [x / y]) s j
  | .test k v yes no, vals, s, j =>
      if k.holds (v.eval w vals) then yes.runFrom w P r vals s j
      else no.runFrom w P r vals s j
  | .coin c₀ c₁, vals, s, j =>
      if r j then c₁.runFrom w P r vals s (j + 1) else c₀.runFrom w P r vals s (j + 1)
  | .send b next, vals, s, j => next.runFrom w P r vals (s ++ [(true, b)]) j
  | .recv r₀ r₁, vals, s, j =>
      if P w s then r₁.runFrom w P r vals (s ++ [(false, true)]) j
      else r₀.runFrom w P r vals (s ++ [(false, false)]) j

/-- The verifier accepts `w` with prover `P` and coin tape `r`. -/
def AcceptsWith (V : VTree ι) (w : ι → ℝ) (P : Prover ι) (r : ℕ → Bool) : Prop :=
  V.runFrom w P r [] [] 0 = some true

/-- The acceptance probability of `P` at `w`: the fraction of coin tapes `r ∈ {0,1}^t`,
`t` the depth, for which the verifier accepts. -/
def accProb (V : VTree ι) (w : ι → ℝ) (P : Prover ι) : ℝ :=
  ((Finset.univ.filter fun r : Fin V.depth → Bool =>
      V.AcceptsWith w P (fun j => if h : j < V.depth then r ⟨j, h⟩ else false)).card : ℝ) /
    2 ^ V.depth

/-- The Boolean-message protocol given by `V` decides `L` on `W`. -/
def DecidesOn (V : VTree ι) (L W : Set (ι → ℝ)) : Prop :=
  ∀ w ∈ W, (w ∈ L → ∃ P, 2 / 3 ≤ V.accProb w P) ∧ (w ∉ L → ∀ P, V.accProb w P ≤ 1 / 3)

end VTree

/-- The input `(x, y)` for the variables `Option σ` (`y = none`). -/
def inpXY {σ : Type} (x : σ → ℝ) (y : ℝ) : Option σ → ℝ := extendVal y x

/-! ### Auxiliary constructions for the proof of Lemma 7.2

We follow the paths of a verifier tree symbolically, representing every computed value as a
fraction `P/D` of polynomials (§2.4).  The *tested numerators* are the numerators of the tested
values and of the divisors; `tnums T fr` lists the tested numerators on all paths of `T` (coins
and replies are not fixed; this only makes the list longer).  Two facts are used:

* every tested numerator has a straight-line program with at most `4t` operations
  (`BIP.tnums_slp`);
* if no tested numerator is a nonzero polynomial vanishing at `w₀`, then for a prover whose
  replies do not depend on the input and for every coin tape, the outcome of the verifier is
  constant near `w₀` (`BIP.loc`).
-/

namespace BIP

variable {ι : Type}

/-! #### Straight-line programs -/

theorem foldl_prefix (Q : SLP ι ℝ) : ∀ vs : List (MvPolynomial ι ℝ),
    ∃ R, Q.foldl (fun vals ins => vals ++ [ins.eval vals]) vs = vs ++ R := by
  induction Q with
  | nil => intro vs; exact ⟨[], by simp⟩
  | cons ins Q ih =>
    intro vs
    obtain ⟨R, hR⟩ := ih (vs ++ [ins.eval vs])
    exact ⟨[ins.eval vs] ++ R, by simp [List.foldl_cons, hR]⟩

theorem length_foldl (Q : SLP ι ℝ) : ∀ vs : List (MvPolynomial ι ℝ),
    (Q.foldl (fun vals ins => vals ++ [ins.eval vals]) vs).length = vs.length + Q.length := by
  induction Q with
  | nil => simp
  | cons ins Q ih => intro vs; simp [ih]; omega

theorem length_values (P : SLP ι ℝ) : P.values.length = P.length := by
  unfold SLP.values
  rw [length_foldl]
  simp

theorem values_append (P Q : SLP ι ℝ) : ∃ R, (P ++ Q).values = P.values ++ R := by
  unfold SLP.values
  rw [List.foldl_append]
  exact foldl_prefix Q _

theorem values_snoc (P : SLP ι ℝ) (ins : Instr ι ℝ) :
    (P ++ [ins]).values = P.values ++ [ins.eval P.values] := by
  unfold SLP.values
  rw [List.foldl_append]
  simp

/-- A computed polynomial is computed by an operand that is unaffected by later
instructions. -/
theorem computes_good {P : SLP ι ℝ} {q : MvPolynomial ι ℝ} (h : P.Computes q) :
    ∃ o : Operand ι ℝ, q = o.eval P.values ∧ ∀ R, o.eval (P.values ++ R) = o.eval P.values := by
  obtain ⟨o, rfl⟩ := h
  cases o with
  | input i => exact ⟨.input i, rfl, fun _ => rfl⟩
  | const a => exact ⟨.const a, rfl, fun _ => rfl⟩
  | prev j =>
    by_cases hj : j < P.values.length
    · refine ⟨.prev j, rfl, fun R => ?_⟩
      simp only [Operand.eval]
      rw [List.getD_append _ _ _ _ hj]
    · refine ⟨.const 0, ?_, fun _ => rfl⟩
      simp only [Operand.eval]
      rw [List.getD_eq_default _ _ (not_lt.1 hj), C_0]

theorem computes_append {P : SLP ι ℝ} {q : MvPolynomial ι ℝ} (h : P.Computes q)
    (Q : SLP ι ℝ) : (P ++ Q).Computes q := by
  obtain ⟨o, rfl, ho⟩ := computes_good h
  obtain ⟨R, hR⟩ := values_append P Q
  exact ⟨o, by rw [hR, ho]⟩

theorem computes_X (P : SLP ι ℝ) (i : ι) : P.Computes (X i) := ⟨.input i, rfl⟩

theorem computes_C (P : SLP ι ℝ) (c : ℝ) : P.Computes (C c) := ⟨.const c, rfl⟩

theorem computes_one (P : SLP ι ℝ) : P.Computes 1 := ⟨.const 1, by simp [Operand.eval]⟩

theorem computes_zero (P : SLP ι ℝ) : P.Computes 0 := ⟨.const 0, by simp [Operand.eval]⟩

/-- One more instruction. -/
theorem step {P : SLP ι ℝ} {q₁ q₂ : MvPolynomial ι ℝ} (h₁ : P.Computes q₁)
    (h₂ : P.Computes q₂) (op : ArithOp) :
    ∃ P' : SLP ι ℝ, P'.length = P.length + 1 ∧ (∀ q, P.Computes q → P'.Computes q) ∧
      P'.Computes (op.apply q₁ q₂) := by
  obtain ⟨o₁, rfl, -⟩ := computes_good h₁
  obtain ⟨o₂, rfl, -⟩ := computes_good h₂
  refine ⟨P ++ [⟨op, o₁, o₂⟩], by simp, fun q hq => computes_append hq _,
    .prev P.values.length, ?_⟩
  simp only [Operand.eval, values_snoc]
  rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
  rfl

theorem hasSLP_mono {q : MvPolynomial ι ℝ} {ℓ ℓ' : ℕ} (h : HasSLP q ℓ) (hle : ℓ ≤ ℓ') :
    HasSLP q ℓ' :=
  let ⟨P, hP, hc⟩ := h
  ⟨P, hP.trans hle, hc⟩

/-! #### Fractions -/

/-- A fraction `P/D` of polynomials. -/
abbrev Frac (ι : Type) := MvPolynomial ι ℝ × MvPolynomial ι ℝ

/-- The fraction representing an operand. -/
def argF (fr : List (Frac ι)) : TArg ι → Frac ι
  | .input i => (X i, 1)
  | .const c => (C c, 1)
  | .val j => fr.getD j (0, 1)

/-- The fraction of the result of an operation. -/
def compF : TOp → Frac ι → Frac ι → Frac ι
  | .add, a, b => (a.1 * b.2 + a.2 * b.1, a.2 * b.2)
  | .sub, a, b => (a.1 * b.2 - a.2 * b.1, a.2 * b.2)
  | .mul, a, b => (a.1 * b.1, a.2 * b.2)
  | .div, a, b => (a.1 * b.2, a.2 * b.1)

/-- The tested numerators on all paths of a verifier tree, from the fractions `fr`. -/
def tnums : VTree ι → List (Frac ι) → List (MvPolynomial ι ℝ)
  | .leaf _, _ => []
  | .comp op a b next, fr =>
      (argF fr b).1 :: tnums next (fr ++ [compF op (argF fr a) (argF fr b)])
  | .test _ v yes no, fr => (argF fr v).1 :: (tnums yes fr ++ tnums no fr)
  | .coin c₀ c₁, fr => tnums c₀ fr ++ tnums c₁ fr
  | .send _ next, fr => tnums next fr
  | .recv r₀ r₁, fr => tnums r₀ fr ++ tnums r₁ fr

/-- The values represented by the fractions at `w`. -/
def valF (w : ι → ℝ) (fr : List (Frac ι)) : List ℝ := fr.map fun p => eval w p.1 / eval w p.2

theorem getD_mem_or {α : Type*} (l : List α) (j : ℕ) (d : α) : l.getD j d ∈ l ∨ l.getD j d = d := by
  by_cases hj : j < l.length
  · left; rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
  · right; exact List.getD_eq_default _ _ (not_lt.1 hj)

theorem argF_eval (w : ι → ℝ) (fr : List (Frac ι)) (a : TArg ι) :
    a.eval w (valF w fr) = eval w (argF fr a).1 / eval w (argF fr a).2 := by
  cases a with
  | input i => simp [TArg.eval, argF]
  | const c => simp [TArg.eval, argF]
  | val j =>
    have h0 : (0 : ℝ) = (fun p : Frac ι => eval w p.1 / eval w p.2) (0, 1) := by simp
    simp only [TArg.eval, argF, valF]
    rw [h0, List.getD_map]

theorem argF_den {w : ι → ℝ} {fr : List (Frac ι)} (h : ∀ p ∈ fr, eval w p.2 ≠ 0) (a : TArg ι) :
    eval w (argF fr a).2 ≠ 0 := by
  cases a with
  | input i => simp [argF]
  | const c => simp [argF]
  | val j =>
    rcases getD_mem_or fr j (0, 1) with hj | hj
    · exact h _ hj
    · simp only [argF]; rw [hj]; simp

theorem argF_computes {P : SLP ι ℝ} {fr : List (Frac ι)}
    (h : ∀ p ∈ fr, P.Computes p.1 ∧ P.Computes p.2) (a : TArg ι) :
    P.Computes (argF fr a).1 ∧ P.Computes (argF fr a).2 := by
  cases a with
  | input i => exact ⟨computes_X P i, computes_one P⟩
  | const c => exact ⟨computes_C P c, computes_one P⟩
  | val j =>
    rcases getD_mem_or fr j (0, 1) with hj | hj
    · exact h _ hj
    · simp only [argF, hj]; exact ⟨computes_zero P, computes_one P⟩

/-- The fractions of a computation node take at most four instructions. -/
theorem comp_step {P : SLP ι ℝ} {A B : Frac ι} (hA : P.Computes A.1 ∧ P.Computes A.2)
    (hB : P.Computes B.1 ∧ P.Computes B.2) (op : TOp) :
    ∃ P' : SLP ι ℝ, P'.length ≤ P.length + 4 ∧ (∀ q, P.Computes q → P'.Computes q) ∧
      P'.Computes (compF op A B).1 ∧ P'.Computes (compF op A B).2 := by
  cases op with
  | add =>
    obtain ⟨P1, l1, i1, c1⟩ := step hA.1 hB.2 .mul
    obtain ⟨P2, l2, i2, c2⟩ := step (i1 _ hA.2) (i1 _ hB.1) .mul
    obtain ⟨P3, l3, i3, c3⟩ := step (i2 _ c1) c2 .add
    obtain ⟨P4, l4, i4, c4⟩ := step (i3 _ (i2 _ (i1 _ hA.2))) (i3 _ (i2 _ (i1 _ hB.2))) .mul
    exact ⟨P4, by omega, fun q hq => i4 _ (i3 _ (i2 _ (i1 _ hq))), i4 _ c3, c4⟩
  | sub =>
    obtain ⟨P1, l1, i1, c1⟩ := step hA.1 hB.2 .mul
    obtain ⟨P2, l2, i2, c2⟩ := step (i1 _ hA.2) (i1 _ hB.1) .mul
    obtain ⟨P3, l3, i3, c3⟩ := step (i2 _ c1) c2 .sub
    obtain ⟨P4, l4, i4, c4⟩ := step (i3 _ (i2 _ (i1 _ hA.2))) (i3 _ (i2 _ (i1 _ hB.2))) .mul
    exact ⟨P4, by omega, fun q hq => i4 _ (i3 _ (i2 _ (i1 _ hq))), i4 _ c3, c4⟩
  | mul =>
    obtain ⟨P1, l1, i1, c1⟩ := step hA.1 hB.1 .mul
    obtain ⟨P2, l2, i2, c2⟩ := step (i1 _ hA.2) (i1 _ hB.2) .mul
    exact ⟨P2, by omega, fun q hq => i2 _ (i1 _ hq), i2 _ c1, c2⟩
  | div =>
    obtain ⟨P1, l1, i1, c1⟩ := step hA.1 hB.2 .mul
    obtain ⟨P2, l2, i2, c2⟩ := step (i1 _ hA.2) (i1 _ hB.1) .mul
    exact ⟨P2, by omega, fun q hq => i2 _ (i1 _ hq), i2 _ c1, c2⟩

/-- **Tested numerators have short programs.** -/
theorem tnums_slp (T : VTree ι) : ∀ (fr : List (Frac ι)) (P : SLP ι ℝ),
    (∀ p ∈ fr, P.Computes p.1 ∧ P.Computes p.2) →
    ∀ q ∈ tnums T fr, HasSLP q (P.length + 4 * T.depth) := by
  induction T with
  | leaf b => intro fr P _ q hq; simp [tnums] at hq
  | comp op a b next ih =>
    intro fr P hP q hq
    simp only [tnums, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact ⟨P, by omega, (argF_computes hP b).1⟩
    · obtain ⟨P', hl, hi, h1, h2⟩ :=
        comp_step (argF_computes hP a) (argF_computes hP b) op
      have hP' : ∀ p ∈ fr ++ [compF op (argF fr a) (argF fr b)],
          P'.Computes p.1 ∧ P'.Computes p.2 := by
        intro p hp
        rcases List.mem_append.1 hp with hp | hp
        · exact ⟨hi _ (hP p hp).1, hi _ (hP p hp).2⟩
        · rw [List.mem_singleton] at hp; subst hp; exact ⟨h1, h2⟩
      refine hasSLP_mono (ih _ P' hP' q hq) ?_
      simp only [VTree.depth]
      omega
  | test k v yes no ihy ihn =>
    intro fr P hP q hq
    simp only [tnums, List.mem_cons, List.mem_append] at hq
    rcases hq with rfl | hq | hq
    · exact ⟨P, by omega, (argF_computes hP v).1⟩
    · refine hasSLP_mono (ihy fr P hP q hq) ?_
      simp only [VTree.depth]; omega
    · refine hasSLP_mono (ihn fr P hP q hq) ?_
      simp only [VTree.depth]; omega
  | coin c₀ c₁ ih₀ ih₁ =>
    intro fr P hP q hq
    simp only [tnums, List.mem_append] at hq
    rcases hq with hq | hq
    · refine hasSLP_mono (ih₀ fr P hP q hq) ?_
      simp only [VTree.depth]; omega
    · refine hasSLP_mono (ih₁ fr P hP q hq) ?_
      simp only [VTree.depth]; omega
  | send b next ih =>
    intro fr P hP q hq
    refine hasSLP_mono (ih fr P hP q hq) ?_
    simp only [VTree.depth]; omega
  | recv r₀ r₁ ih₀ ih₁ =>
    intro fr P hP q hq
    simp only [tnums, List.mem_append] at hq
    rcases hq with hq | hq
    · refine hasSLP_mono (ih₀ fr P hP q hq) ?_
      simp only [VTree.depth]; omega
    · refine hasSLP_mono (ih₁ fr P hP q hq) ?_
      simp only [VTree.depth]; omega

/-! #### Runs -/

/-- The run only queries the prover at the input itself. -/
theorem runFrom_congr (w : ι → ℝ) (P P' : VTree.Prover ι) (hP : ∀ s, P w s = P' w s)
    (r : ℕ → Bool) (T : VTree ι) :
    ∀ vals s j, T.runFrom w P r vals s j = T.runFrom w P' r vals s j := by
  induction T with
  | leaf b => intro vals s j; rfl
  | comp op a b next ih => intro vals s j; cases op <;> simp [VTree.runFrom, ih]
  | test k v yes no ihy ihn => intro vals s j; simp [VTree.runFrom, ihy, ihn]
  | coin c₀ c₁ ih₀ ih₁ => intro vals s j; simp [VTree.runFrom, ih₀, ih₁]
  | send b next ih => intro vals s j; simp [VTree.runFrom, ih]
  | recv r₀ r₁ ih₀ ih₁ => intro vals s j; simp [VTree.runFrom, ih₀, ih₁, hP]

theorem valF_snoc (w : ι → ℝ) (fr : List (Frac ι)) (p : Frac ι) :
    valF w (fr ++ [p]) = valF w fr ++ [eval w p.1 / eval w p.2] := by
  simp [valF]

/-- The result of a test is constant near `w₀` if the tested numerator is either the zero
polynomial or nonzero at `w₀`. -/
theorem test_loc (w₀ : ι → ℝ) (k : TestKind) (F : Frac ι) (h2 : eval w₀ F.2 ≠ 0)
    (h1 : F.1 ≠ 0 → eval w₀ F.1 ≠ 0) :
    ∀ᶠ w in 𝓝 w₀, (k.holds (eval w F.1 / eval w F.2) ↔ k.holds (eval w₀ F.1 / eval w₀ F.2)) := by
  by_cases hz : F.1 = 0
  · exact Eventually.of_forall fun w => by simp [hz]
  have hne : eval w₀ F.1 / eval w₀ F.2 ≠ 0 := div_ne_zero (h1 hz) h2
  have hc : ContinuousAt (fun w => eval w F.1 / eval w F.2) w₀ :=
    (continuous_eval _).continuousAt.div (continuous_eval _).continuousAt h2
  cases k with
  | eq =>
    filter_upwards [hc.eventually_ne hne] with w hw
    simp only [TestKind.holds]
    exact ⟨fun h => absurd h hw, fun h => absurd h hne⟩
  | ge =>
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · filter_upwards [hc.eventually (gt_mem_nhds hneg)] with w hw
      simp only [TestKind.holds]
      exact ⟨fun h => absurd h (not_le.2 hw), fun h => absurd h (not_le.2 hneg)⟩
    · filter_upwards [hc.eventually (lt_mem_nhds hpos)] with w hw
      simp only [TestKind.holds]
      exact ⟨fun _ => hpos.le, fun _ => hw.le⟩

/-- **Local constancy.**  If no tested numerator is a nonzero polynomial vanishing at `w₀`,
then for a prover whose replies depend only on the transcript, the outcome is constant near
`w₀`. -/
theorem loc (w₀ : ι → ℝ) (Q : VTree.Transcript → Bool) (r : ℕ → Bool) (T : VTree ι) :
    ∀ (fr : List (Frac ι)) (s : VTree.Transcript) (j : ℕ), (∀ p ∈ fr, eval w₀ p.2 ≠ 0) →
    (∀ q ∈ tnums T fr, q ≠ 0 → eval w₀ q ≠ 0) →
    ∀ᶠ w in 𝓝 w₀, T.runFrom w (fun _ => Q) r (valF w fr) s j =
      T.runFrom w₀ (fun _ => Q) r (valF w₀ fr) s j := by
  induction T with
  | leaf b => intro fr s j _ _; exact Eventually.of_forall fun w => rfl
  | comp op a b next ih =>
    intro fr s j hden htn
    set A := argF fr a with hAdef
    set B := argF fr b with hBdef
    have hA : eval w₀ A.2 ≠ 0 := argF_den hden a
    have hB : eval w₀ B.2 ≠ 0 := argF_den hden b
    have hB1 : B.1 ≠ 0 → eval w₀ B.1 ≠ 0 := htn _ (List.mem_cons_self ..)
    have htn' : ∀ q ∈ tnums next (fr ++ [compF op A B]), q ≠ 0 → eval w₀ q ≠ 0 :=
      fun q hq => htn q (List.mem_cons_of_mem _ hq)
    have hA' : ∀ᶠ w in 𝓝 w₀, eval w A.2 ≠ 0 := (continuous_eval _).continuousAt.eventually_ne hA
    have hB' : ∀ᶠ w in 𝓝 w₀, eval w B.2 ≠ 0 := (continuous_eval _).continuousAt.eventually_ne hB
    have ha : ∀ w, a.eval w (valF w fr) = eval w A.1 / eval w A.2 := fun w => argF_eval w fr a
    have hb : ∀ w, b.eval w (valF w fr) = eval w B.1 / eval w B.2 := fun w => argF_eval w fr b
    have key : eval w₀ (compF op A B).2 ≠ 0 → ∀ v : (ι → ℝ) → ℝ,
        (∀ᶠ w in 𝓝 w₀, v w = eval w (compF op A B).1 / eval w (compF op A B).2) →
        ∀ᶠ w in 𝓝 w₀, next.runFrom w (fun _ => Q) r (valF w fr ++ [v w]) s j =
          next.runFrom w₀ (fun _ => Q) r (valF w₀ fr ++ [v w₀]) s j := by
      intro hN v hv
      have hden' : ∀ p ∈ fr ++ [compF op A B], eval w₀ p.2 ≠ 0 := by
        intro p hp
        rcases List.mem_append.1 hp with hp | hp
        · exact hden p hp
        · rw [List.mem_singleton] at hp; subst hp; exact hN
      have h1 := ih (fr ++ [compF op A B]) s j hden' htn'
      have h0 := hv.self_of_nhds
      filter_upwards [h1, hv] with w hw hvw
      rw [hvw, h0, ← valF_snoc, ← valF_snoc]
      exact hw
    cases op with
    | add =>
      simp only [VTree.runFrom]
      refine key (by simp [compF, hA, hB]) _ ?_
      filter_upwards [hA', hB'] with w hwA hwB
      rw [ha, hb, div_add_div _ _ hwA hwB]
      simp [compF]
    | sub =>
      simp only [VTree.runFrom]
      refine key (by simp [compF, hA, hB]) _ ?_
      filter_upwards [hA', hB'] with w hwA hwB
      rw [ha, hb, div_sub_div _ _ hwA hwB]
      simp [compF]
    | mul =>
      simp only [VTree.runFrom]
      refine key (by simp [compF, hA, hB]) _ (Eventually.of_forall fun w => ?_)
      rw [ha, hb, div_mul_div_comm]
      simp [compF]
    | div =>
      simp only [VTree.runFrom]
      by_cases hz : B.1 = 0
      · refine Eventually.of_forall fun w => ?_
        rw [hb, hb, hz]
        simp
      have hB1w : eval w₀ B.1 ≠ 0 := hB1 hz
      have hy0 : eval w₀ B.1 / eval w₀ B.2 ≠ 0 := div_ne_zero hB1w hB
      have hy : ∀ᶠ w in 𝓝 w₀, eval w B.1 / eval w B.2 ≠ 0 := by
        filter_upwards [(continuous_eval B.1).continuousAt.eventually_ne hB1w, hB'] with w h1 h2
        exact div_ne_zero h1 h2
      have hk := key (by simp [compF, hA, hB1w]) (fun w => a.eval w (valF w fr) /
        b.eval w (valF w fr)) (Eventually.of_forall fun w => by
          simp only [ha, hb, div_div_div_eq]; simp [compF])
      filter_upwards [hk, hy] with w hw hyw
      rw [hb, hb, ite_eq_right hyw, ite_eq_right hy0]
      rw [hb, hb] at hw
      exact hw
  | test k v yes no ihy ihn =>
    intro fr s j hden htn
    have hV2 : eval w₀ (argF fr v).2 ≠ 0 := argF_den hden v
    have hV1 : (argF fr v).1 ≠ 0 → eval w₀ (argF fr v).1 ≠ 0 := htn _ (List.mem_cons_self ..)
    have hT := test_loc w₀ k (argF fr v) hV2 hV1
    simp only [VTree.runFrom, argF_eval]
    by_cases hk : k.holds (eval w₀ (argF fr v).1 / eval w₀ (argF fr v).2)
    · have := ihy fr s j hden fun q hq => htn q (by simp [tnums, hq])
      filter_upwards [hT, this] with w hw hw'
      rw [ite_eq_left (hw.2 hk), ite_eq_left hk]
      exact hw'
    · have := ihn fr s j hden fun q hq => htn q (by simp [tnums, hq])
      filter_upwards [hT, this] with w hw hw'
      rw [ite_eq_right (fun h => hk (hw.1 h)), ite_eq_right hk]
      exact hw'
  | coin c₀ c₁ ih₀ ih₁ =>
    intro fr s j hden htn
    simp only [VTree.runFrom]
    by_cases hr : r j
    · simp only [hr, ite_true]
      exact ih₁ fr s (j + 1) hden fun q hq => htn q (by simp [tnums, hq])
    · simp only [hr]
      exact ih₀ fr s (j + 1) hden fun q hq => htn q (by simp [tnums, hq])
  | send b next ih =>
    intro fr s j hden htn
    exact ih fr _ j hden htn
  | recv r₀ r₁ ih₀ ih₁ =>
    intro fr s j hden htn
    simp only [VTree.runFrom]
    by_cases hQ : Q s
    · simp only [hQ, ite_true]
      exact ih₁ fr _ j hden fun q hq => htn q (by simp [tnums, hq])
    · simp only [hQ]
      exact ih₀ fr _ j hden fun q hq => htn q (by simp [tnums, hq])

/-! #### The generic point and the division -/

/-- A nonzero polynomial does not vanish on a nonempty open set. -/
theorem exists_eval_ne_zero {σ : Type} [Fintype σ] (p : MvPolynomial σ ℝ) (hp : p ≠ 0)
    {U : Set (σ → ℝ)} (hU : IsOpen U) (hne : U.Nonempty) : ∃ x ∈ U, eval x p ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨z, hz⟩ := hne
  have h1 : (fun x => eval x p) =ᶠ[𝓝 z] 0 :=
    Filter.eventually_of_mem (hU.mem_nhds hz) fun x hx => h x hx
  have h2 := (AnalyticOnNhd.eval_mvPolynomial p).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (mem_univ z) h1
  exact hp (MvPolynomial.funext fun x => by simpa using h2 (mem_univ x))

variable {σ : Type}

/-- The substitution `Y = f(X)`. -/
def substY (f : MvPolynomial σ ℝ) (q : MvPolynomial (Option σ) ℝ) : MvPolynomial σ ℝ :=
  Polynomial.eval f (optionEquivLeft ℝ σ q)

theorem eval_substY (f : MvPolynomial σ ℝ) (q : MvPolynomial (Option σ) ℝ) (x : σ → ℝ) :
    eval x (substY f q) = eval (inpXY x (eval x f)) q := by
  rw [show inpXY x (eval x f) = fun o => Option.elim o (eval x f) x from rfl,
    optionEquivLeft_elim_eval, Polynomial.eval_map, Polynomial.eval₂_hom, substY]

theorem optionEquivLeft_rename_some (f : MvPolynomial σ ℝ) :
    optionEquivLeft ℝ σ (rename some f) = Polynomial.C f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [optionEquivLeft_C]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p n hp => simp [map_mul, hp, optionEquivLeft_X_some]

/-- **Division by the graph equation.** -/
theorem dvd_of_substY (f : MvPolynomial σ ℝ) (q : MvPolynomial (Option σ) ℝ)
    (h : substY f q = 0) : ∃ G, q = (X none - rename some f) * G := by
  have hroot : Polynomial.IsRoot (optionEquivLeft ℝ σ q) f := h
  have h1 := Polynomial.mul_divByMonic_eq_iff_isRoot.2 hroot
  refine ⟨(optionEquivLeft ℝ σ).symm
    (optionEquivLeft ℝ σ q /ₘ (Polynomial.X - Polynomial.C f)), ?_⟩
  apply (optionEquivLeft ℝ σ).injective
  rw [map_mul, map_sub, optionEquivLeft_X_none, optionEquivLeft_rename_some,
    AlgEquiv.apply_symm_apply, h1]

end BIP

/-- **Lemma 7.2 (boundary test).** -/
theorem boundary_test {σ : Type} [Fintype σ] [DecidableEq σ] (f : MvPolynomial σ ℝ)
    (U : Set (σ → ℝ)) (hU : IsOpen U) (hUne : U.Nonempty) (W : Set (Option σ → ℝ))
    (hW : IsOpen W) (hUW : ∀ x ∈ U, inpXY x (eval x f) ∈ W) (V : VTree (Option σ)) (t : ℕ)
    (hV : V.depth ≤ t)
    (hdec : V.DecidesOn {w | w none = eval (w ∘ some) f} W ∨
      V.DecidesOn {w | w none ≤ eval (w ∘ some) f} W) :
    ∃ G : MvPolynomial (Option σ) ℝ, G ≠ 0 ∧ HasSLP ((X none - rename some f) * G) (4 * t) := by
  classical
  -- the tested numerators on all paths
  set L := BIP.tnums V [] with hLdef
  -- *A generic point*: `x ∈ U` at which `q(X, f(X))` does not vanish unless it is zero
  obtain ⟨x, hxU, hx⟩ : ∃ x ∈ U, ∀ q ∈ L, BIP.substY f q ≠ 0 → eval x (BIP.substY f q) ≠ 0 := by
    set F := ((L.filter fun q => BIP.substY f q ≠ 0).map (BIP.substY f)).prod with hFdef
    have hF : F ≠ 0 := by
      refine List.prod_ne_zero fun h0 => ?_
      obtain ⟨q, hq, hq0⟩ := List.mem_map.1 h0
      exact (by simpa using (List.mem_filter.1 hq).2 : BIP.substY f q ≠ 0) hq0
    obtain ⟨x, hxU, hFx⟩ := BIP.exists_eval_ne_zero F hF hU hUne
    refine ⟨x, hxU, fun q hq hgq h0 => hFx ?_⟩
    rw [hFdef, map_list_prod]
    refine List.prod_eq_zero (List.mem_map.2 ⟨BIP.substY f q, List.mem_map.2 ⟨q,
      List.mem_filter.2 ⟨hq, by simpa using hgq⟩, rfl⟩, h0⟩)
  set w₀ := inpXY x (eval x f) with hw₀def
  have hw₀W : w₀ ∈ W := hUW x hxU
  by_cases hbad : ∃ q ∈ L, q ≠ 0 ∧ eval w₀ q = 0
  · -- *Division by the graph equation*
    obtain ⟨q, hqL, hq0, hqw⟩ := hbad
    have hgq : BIP.substY f q = 0 := by
      by_contra h
      exact hx q hqL h (by rw [BIP.eval_substY]; exact hqw)
    obtain ⟨G, hG⟩ := BIP.dvd_of_substY f q hgq
    refine ⟨G, ?_, ?_⟩
    · rintro rfl
      rw [mul_zero] at hG
      exact hq0 hG
    · rw [← hG]
      have := BIP.tnums_slp V [] [] (by simp) q hqL
      exact BIP.hasSLP_mono this (by simp; omega)
  · -- *Local constancy* gives a contradiction
    exfalso
    push Not at hbad
    -- a good prover at `w₀`
    have hw₀L1 : w₀ ∈ {w : Option σ → ℝ | w none = eval (w ∘ some) f} := rfl
    have hw₀L2 : w₀ ∈ {w : Option σ → ℝ | w none ≤ eval (w ∘ some) f} :=
      show eval x f ≤ eval x f from le_refl _
    obtain ⟨P, hP⟩ : ∃ P, 2 / 3 ≤ V.accProb w₀ P := by
      rcases hdec with h | h
      · exact (h w₀ hw₀W).1 hw₀L1
      · exact (h w₀ hw₀W).1 hw₀L2
    set Q := P w₀ with hQdef
    -- the prover `P'(w, s) = P(w₀, s)` has the same acceptance probability near `w₀`
    have hloc : ∀ᶠ w in 𝓝 w₀, V.accProb w (fun _ => Q) = V.accProb w₀ P := by
      have hr : ∀ rr : Fin V.depth → Bool, ∀ᶠ w in 𝓝 w₀,
          (V.AcceptsWith w (fun _ => Q) (fun j => if h : j < V.depth then rr ⟨j, h⟩ else false)
            ↔ V.AcceptsWith w₀ P (fun j => if h : j < V.depth then rr ⟨j, h⟩ else false)) := by
        intro rr
        have := BIP.loc w₀ Q (fun j => if h : j < V.depth then rr ⟨j, h⟩ else false) V [] [] 0
          (by simp) hbad
        filter_upwards [this] with w hw
        unfold VTree.AcceptsWith
        rw [BIP.runFrom_congr w₀ P (fun _ => Q) (fun s => rfl)]
        exact iff_of_eq (congrArg (· = some true) hw)
      filter_upwards [Filter.eventually_all.2 hr] with w hw
      unfold VTree.accProb
      rw [Finset.filter_congr fun rr _ => hw rr]
    -- move up from `w₀` along `Y`
    have hcont : Continuous fun ε : ℝ => inpXY x (eval x f + ε) := by
      refine continuous_pi fun o => ?_
      cases o with
      | none => exact continuous_const.add continuous_id
      | some i => exact continuous_const
    have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), inpXY x (eval x f + ε) ∈ W ∧
        V.accProb (inpXY x (eval x f + ε)) (fun _ => Q) = V.accProb w₀ P := by
      have ht := hcont.tendsto 0
      rw [add_zero] at ht
      have hWev : ∀ᶠ w in 𝓝 w₀, w ∈ W := hW.mem_nhds hw₀W
      exact ht.eventually (hWev.and hloc)
    obtain ⟨ε, hε, hεW, hεacc⟩ := hev.exists_gt
    have hn1 : inpXY x (eval x f + ε) ∉ {w : Option σ → ℝ | w none = eval (w ∘ some) f} := by
      change ¬ (eval x f + ε = eval x f)
      intro h; linarith
    have hn2 : inpXY x (eval x f + ε) ∉ {w : Option σ → ℝ | w none ≤ eval (w ∘ some) f} := by
      change ¬ (eval x f + ε ≤ eval x f)
      intro h; linarith
    have hle : V.accProb (inpXY x (eval x f + ε)) (fun _ => Q) ≤ 1 / 3 := by
      rcases hdec with h | h
      · exact (h _ hεW).2 hn1 _
      · exact (h _ hεW).2 hn2 _
    linarith

/-- **Theorem 7.3** (tree part). -/
theorem bip_lower (hLB : PermLowerBound) (hB : BurgisserThm) (t : ℕ → ℕ)
    (V : ∀ m, VTree (Option (Fin m × Fin m))) (hV : ∀ m, (V m).depth ≤ t m)
    (hdec : ∀ m, (V m).DecidesOn {w | w none = eval (w ∘ some) (per m)} univ) :
    SuperPolyLB fun m => t m := by
  obtain ⟨C, hC⟩ := hB
  -- the bound `C m³ (4 t_m + m²)` is at most `5 C (m+1)⁵ (t_m+1)`
  refine superPoly_of_borderLE hLB t (5 * C) 5 1 ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  obtain ⟨G, hG0, hG⟩ := boundary_test (per m) univ isOpen_univ univ_nonempty univ isOpen_univ
    (fun _ _ => mem_univ _) (V m) (t m) (hV m) (Or.inl (hdec m))
  refine (hC m (4 * t m) (per m) hm (totalDegree_per m) ⟨G, hG0, hG⟩).mono ?_
  rw [Fintype.card_prod, Fintype.card_fin]
  have h1 : m ^ 3 ≤ (m + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have h2 : 4 * t m + m * m ≤ 5 * ((m + 1) ^ 2 * (t m + 1)) := by
    have : m * m ≤ (m + 1) ^ 2 := by nlinarith
    have : 1 ≤ (m + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    nlinarith
  calc C * m ^ 3 * (4 * t m + m * m) ≤ C * (m + 1) ^ 3 * (5 * ((m + 1) ^ 2 * (t m + 1))) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2
    _ = 5 * C * (m + 1) ^ 5 * (t m + 1) ^ 1 := by ring

end ClassSep
