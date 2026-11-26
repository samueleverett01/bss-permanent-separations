import ClassSeparations.Basic.Tree

/-!
# The polynomials on a path, and cells (§2.4, Lemma 2.5)

For a tree of depth `t` and a set of marked outcomes, the set of inputs with a marked outcome
is a finite union of *cells* `{p₁ = ⋯ = p_r = 0, q₁ > 0, …, q_m > 0}` with `r, m ≤ 2t`, where
all `pᵢ, qⱼ` are computed by one straight-line program with at most `8t` operations from the
input coordinates and the constants of the tree, and involve at most `2t` input coordinates.
-/

noncomputable section

open MvPolynomial

namespace ClassSep

universe u

variable {ι : Type u}

/-- A cell: the common zeros of the `eqs` at which all the `poss` are positive, together with
one straight-line program that computes all these polynomials. -/
structure Cell (ι : Type u) where
  prog : SLP ι ℝ
  eqs : List (MvPolynomial ι ℝ)
  poss : List (MvPolynomial ι ℝ)

/-- The set of points of a cell. -/
def Cell.carrier (B : Cell ι) : Set (ι → ℝ) :=
  {w | (∀ p ∈ B.eqs, eval w p = 0) ∧ ∀ q ∈ B.poss, 0 < eval w q}

/-- The constants used by an operand. -/
def Operand.constSet {σ K : Type*} : Operand σ K → Set K
  | .const a => {a}
  | _ => ∅

/-- The input coordinates used by an operand. -/
def Operand.inputSet {σ K : Type*} : Operand σ K → Set σ
  | .input i => {i}
  | _ => ∅

/-- The bounds of Lemma 2.5 for a cell, for a tree of depth `t` with constants in `K`. -/
structure Cell.Bounded (B : Cell ι) (t : ℕ) (K : Set ℝ) : Prop where
  eqs_len : B.eqs.length ≤ 2 * t
  poss_len : B.poss.length ≤ 2 * t
  prog_len : B.prog.length ≤ 8 * t
  computes_eqs : ∀ p ∈ B.eqs, B.prog.Computes p
  computes_poss : ∀ q ∈ B.poss, B.prog.Computes q
  consts : ∀ ins ∈ B.prog, ins.a.constSet ∪ ins.b.constSet ⊆ K ∪ {0, 1, -1}
  vars : ∃ I : Finset ι, I.card ≤ 2 * t ∧
    (∀ ins ∈ B.prog, ins.a.inputSet ∪ ins.b.inputSet ⊆ ↑I) ∧
    (∀ p ∈ B.eqs ++ B.poss, p.vars ⊆ I)

/-! ### Auxiliary constructions for the proof of Lemma 2.5

We follow one path of the tree symbolically.  The state of a path records a straight-line
program, the fractions `P/D` representing the values computed so far, the conditions
(equations `p = 0` and positivity conditions `q > 0`) collected so far, and the input
coordinates seen so far.  Every polynomial of the state is stored together with an operand of
the program that computes it (a *symbolic polynomial*). -/

namespace CellsAux

/-! #### Running a program from given values -/

/-- The values obtained by running the instructions `Q` after the values `vs`. -/
def vfrom (vs : List (MvPolynomial ι ℝ)) (Q : SLP ι ℝ) : List (MvPolynomial ι ℝ) :=
  Q.foldl (fun vals ins => vals ++ [ins.eval vals]) vs

theorem values_eq_vfrom (P : SLP ι ℝ) : SLP.values P = vfrom [] P := rfl

theorem values_append (P Q : SLP ι ℝ) : SLP.values (P ++ Q) = vfrom (SLP.values P) Q := by
  simp only [SLP.values, vfrom, List.foldl_append]

theorem vfrom_cons (vs : List (MvPolynomial ι ℝ)) (ins : Instr ι ℝ) (Q : SLP ι ℝ) :
    vfrom vs (ins :: Q) = vfrom (vs ++ [ins.eval vs]) Q := rfl

theorem vfrom_eq_append (Q : SLP ι ℝ) :
    ∀ vs : List (MvPolynomial ι ℝ), ∃ r, vfrom vs Q = vs ++ r := by
  induction Q with
  | nil => intro vs; exact ⟨[], by simp [vfrom]⟩
  | cons ins Q ih =>
    intro vs
    obtain ⟨r, hr⟩ := ih (vs ++ [ins.eval vs])
    exact ⟨ins.eval vs :: r, by rw [vfrom_cons, hr]; simp⟩

theorem length_vfrom (Q : SLP ι ℝ) :
    ∀ vs : List (MvPolynomial ι ℝ), (vfrom vs Q).length = vs.length + Q.length := by
  induction Q with
  | nil => intro vs; simp [vfrom]
  | cons ins Q ih => intro vs; rw [vfrom_cons, ih]; simp; omega

theorem length_values (P : SLP ι ℝ) : (SLP.values P).length = P.length := by
  rw [values_eq_vfrom, length_vfrom]; simp

/-! #### Operands -/

/-- The operand `o` is valid for `n` earlier values, its constant is in `K` and its input
coordinate in `I`. -/
def good (n : ℕ) (K : Set ℝ) (I : Set ι) : Operand ι ℝ → Prop
  | .input i => i ∈ I
  | .const c => c ∈ K
  | .prev j => j < n

theorem good_mono {n n' : ℕ} {K : Set ℝ} {I I' : Set ι} (hn : n ≤ n') (hI : I ⊆ I') :
    ∀ {o : Operand ι ℝ}, good n K I o → good n' K I' o
  | .input _, h => hI h
  | .const _, h => h
  | .prev _, h => lt_of_lt_of_le h hn

/-- The constants and the input coordinates of an operand lie in `K` and `I`. -/
def cin (K : Set ℝ) (I : Set ι) (o : Operand ι ℝ) : Prop :=
  o.constSet ⊆ K ∧ o.inputSet ⊆ I

theorem cin_of_good {n : ℕ} {K : Set ℝ} {I : Set ι} :
    ∀ {o : Operand ι ℝ}, good n K I o → cin K I o
  | .input _, h => ⟨by simp [Operand.constSet], by simpa [Operand.inputSet, good] using h⟩
  | .const _, h => ⟨by simpa [Operand.constSet, good] using h, by simp [Operand.inputSet]⟩
  | .prev _, _ => ⟨by simp [Operand.constSet], by simp [Operand.inputSet]⟩

theorem cin_prev (K : Set ℝ) (I : Set ι) (j : ℕ) : cin K I (.prev j : Operand ι ℝ) :=
  ⟨by simp [Operand.constSet], by simp [Operand.inputSet]⟩

theorem cin_mono {K : Set ℝ} {I I' : Set ι} {o : Operand ι ℝ} (h : cin K I o) (hI : I ⊆ I') :
    cin K I' o :=
  ⟨h.1, h.2.trans hI⟩

theorem eval_append_of_good {vs : List (MvPolynomial ι ℝ)} {K : Set ℝ} {I : Set ι}
    {o : Operand ι ℝ} (h : good vs.length K I o) (r : List (MvPolynomial ι ℝ)) :
    o.eval (vs ++ r) = o.eval vs := by
  cases o with
  | input i => rfl
  | const c => rfl
  | prev j => exact List.getD_append _ _ _ _ h

/-- A symbolic polynomial: an operand together with the polynomial it should compute. -/
abbrev SP (ι : Type u) := Operand ι ℝ × MvPolynomial ι ℝ

/-- The operand of `e` is good for the values `vs` and computes the polynomial of `e`. -/
structure okv (K : Set ℝ) (I : Set ι) (vs : List (MvPolynomial ι ℝ)) (e : SP ι) : Prop where
  isGood : good vs.length K I e.1
  evalEq : e.1.eval vs = e.2

/-- `okv` for the values of a program. -/
abbrev okvP (K : Set ℝ) (I : Set ι) (P : SLP ι ℝ) (e : SP ι) : Prop :=
  okv K I (SLP.values P) e

/-- The instruction `x ∘ y`. -/
def mkIns (op : ArithOp) (x y : SP ι) : Instr ι ℝ := ⟨op, x.1, y.1⟩

/-- The result of the instruction `x ∘ y` placed at position `j`. -/
def mkRes (op : ArithOp) (x y : SP ι) (j : ℕ) : SP ι := (.prev j, op.apply x.2 y.2)

theorem okv_mono {K : Set ℝ} {I : Set ι} {vs : List (MvPolynomial ι ℝ)} {e : SP ι}
    (h : okv K I vs e) (r : List (MvPolynomial ι ℝ)) : okv K I (vs ++ r) e :=
  ⟨good_mono (by simp) subset_rfl h.isGood, by rw [eval_append_of_good h.isGood]; exact h.evalEq⟩

theorem okvP_mono {K : Set ℝ} {I : Set ι} {P : SLP ι ℝ} {e : SP ι} (h : okvP K I P e)
    (l : SLP ι ℝ) : okvP K I (P ++ l) e := by
  obtain ⟨r, hr⟩ := vfrom_eq_append l (SLP.values P)
  show okv K I (SLP.values (P ++ l)) e
  rw [values_append, hr]
  exact okv_mono h r

theorem okvP_prefix {K : Set ℝ} {I : Set ι} {P Q : SLP ι ℝ} {e : SP ι} (h : okvP K I P e)
    (hPQ : P <+: Q) : okvP K I Q e := by
  obtain ⟨t, rfl⟩ := hPQ
  exact okvP_mono h t

theorem okvP_widen {K : Set ℝ} {I I' : Set ι} {P : SLP ι ℝ} {e : SP ι} (h : okvP K I P e)
    (hI : I ⊆ I') : okvP K I' P e :=
  ⟨good_mono le_rfl hI h.isGood, h.evalEq⟩

theorem okv_step {K : Set ℝ} {I : Set ι} {vs : List (MvPolynomial ι ℝ)} {x y : SP ι}
    (hx : okv K I vs x) (hy : okv K I vs y) (op : ArithOp) {j : ℕ} (hj : j = vs.length) :
    okv K I (vs ++ [Instr.eval vs (mkIns op x y)]) (mkRes op x y j) := by
  constructor
  · show j < (vs ++ _).length
    simp [hj]
  · show (vs ++ [_]).getD j 0 = op.apply x.2 y.2
    rw [List.getD_append_right _ _ _ _ (by omega), hj, Nat.sub_self]
    show Instr.eval vs (mkIns op x y) = op.apply x.2 y.2
    simp only [Instr.eval, mkIns, hx.evalEq, hy.evalEq]

theorem okvP_step {K : Set ℝ} {I : Set ι} {P : SLP ι ℝ} {x y : SP ι}
    (hx : okvP K I P x) (hy : okvP K I P y) (op : ArithOp) {j : ℕ} (hj : j = P.length) :
    okvP K I (P ++ [mkIns op x y]) (mkRes op x y j) := by
  show okv K I (SLP.values (P ++ [mkIns op x y])) (mkRes op x y j)
  rw [values_append]
  exact okv_step hx hy op (by rw [hj, length_values])

/-! #### Variables -/

theorem vars_apply {I : Finset ι} (op : ArithOp) {p q : MvPolynomial ι ℝ} (hp : p.vars ⊆ I)
    (hq : q.vars ⊆ I) : (op.apply p q).vars ⊆ I := by
  classical
  cases op
  · exact (vars_add_subset p q).trans (Finset.union_subset hp hq)
  · exact Finset.Subset.trans (vars_sub_subset p) (Finset.union_subset hp hq)
  · exact (vars_mul p q).trans (Finset.union_subset hp hq)

theorem vars_eval {I : Finset ι} {vs : List (MvPolynomial ι ℝ)} (hvs : ∀ p ∈ vs, p.vars ⊆ I)
    {o : Operand ι ℝ} (ho : o.inputSet ⊆ (I : Set ι)) : (o.eval vs).vars ⊆ I := by
  cases o with
  | input i =>
    show (X i : MvPolynomial ι ℝ).vars ⊆ I
    rw [vars_X]
    simpa [Operand.inputSet] using ho
  | const c =>
    show (C c : MvPolynomial ι ℝ).vars ⊆ I
    rw [vars_C]
    exact Finset.empty_subset _
  | prev j =>
    show (vs.getD j 0).vars ⊆ I
    by_cases hj : j < vs.length
    · rw [List.getD_eq_getElem _ _ hj]
      exact hvs _ (List.getElem_mem hj)
    · rw [List.getD_eq_default _ _ (not_lt.1 hj), vars_0]
      exact Finset.empty_subset _

theorem vars_vfrom {I : Finset ι} (Q : SLP ι ℝ)
    (hQ : ∀ ins ∈ Q, ins.a.inputSet ⊆ (I : Set ι) ∧ ins.b.inputSet ⊆ (I : Set ι)) :
    ∀ vs : List (MvPolynomial ι ℝ), (∀ p ∈ vs, p.vars ⊆ I) → ∀ p ∈ vfrom vs Q, p.vars ⊆ I := by
  induction Q with
  | nil => intro vs hvs; simpa [vfrom] using hvs
  | cons ins Q ih =>
    intro vs hvs
    rw [vfrom_cons]
    apply ih (fun i hi => hQ i (List.mem_cons_of_mem _ hi))
    intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact hvs p hp
    · rw [List.mem_singleton] at hp
      subst hp
      obtain ⟨ha, hb⟩ := hQ ins (by simp)
      exact vars_apply ins.op (vars_eval hvs ha) (vars_eval hvs hb)

/-! #### The symbolic state of a path -/

/-- The symbolic state of a path. -/
structure PState (ι : Type u) where
  /-- The program computing all the polynomials. -/
  prog : SLP ι ℝ
  /-- The fractions `P/D` representing the values computed so far. -/
  vals : List (SP ι × SP ι)
  /-- The equations `p = 0`. -/
  eqs : List (SP ι)
  /-- The positivity conditions `q > 0`. -/
  poss : List (SP ι)
  /-- The input coordinates used so far. -/
  ins : List ι

/-- The initial state. -/
def PState.init : PState ι := ⟨[], [], [], [], []⟩

/-- The fraction `0/1`. -/
def defaultVal : SP ι × SP ι := ((.const 0, C 0), (.const 1, C 1))

/-- The input coordinates of a tree operand. -/
def argInputs : TArg ι → List ι
  | .input i => [i]
  | _ => []

theorem argInputs_length (a : TArg ι) : (argInputs a).length ≤ 1 := by
  cases a <;> simp [argInputs]

/-- The fraction representing a tree operand. -/
def PState.arg (st : PState ι) : TArg ι → SP ι × SP ι
  | .input i => ((.input i, X i), (.const 1, C 1))
  | .const c => ((.const c, C c), (.const 1, C 1))
  | .val j => st.vals.getD j defaultVal

/-- Append instructions, values, conditions and input coordinates to a state. -/
def PState.push (st : PState ι) (l : SLP ι ℝ) (nv : List (SP ι × SP ι)) (ne np : List (SP ι))
    (ni : List ι) : PState ι :=
  ⟨st.prog ++ l, st.vals ++ nv, st.eqs ++ ne, st.poss ++ np, st.ins ++ ni⟩

/-- The cell of a state. -/
def PState.cell (st : PState ι) : Cell ι :=
  ⟨st.prog, st.eqs.map Prod.snd, st.poss.map Prod.snd⟩

/-- `x ± y` for fractions: `(P₁D₂ ± P₂D₁) / (D₁D₂)`. -/
def asPush (st : PState ι) (op : ArithOp) (x y : SP ι × SP ι) (ni : List ι) : PState ι :=
  st.push
    [mkIns .mul x.1 y.2, mkIns .mul y.1 x.2,
      mkIns op (mkRes .mul x.1 y.2 st.prog.length) (mkRes .mul y.1 x.2 (st.prog.length + 1)),
      mkIns .mul x.2 y.2]
    [(mkRes op (mkRes .mul x.1 y.2 st.prog.length) (mkRes .mul y.1 x.2 (st.prog.length + 1))
        (st.prog.length + 2), mkRes .mul x.2 y.2 (st.prog.length + 3))] [] [] ni

/-- `x · y` for fractions: `(P₁P₂) / (D₁D₂)`. -/
def mulPush (st : PState ι) (x y : SP ι × SP ι) (ni : List ι) : PState ι :=
  st.push [mkIns .mul x.1 y.1, mkIns .mul x.2 y.2]
    [(mkRes .mul x.1 y.1 st.prog.length, mkRes .mul x.2 y.2 (st.prog.length + 1))] [] [] ni

/-- `x / y` for fractions: `(P₁D₂) / (D₁P₂)`, with the condition `P₂² > 0`. -/
def divPush (st : PState ι) (x y : SP ι × SP ι) (ni : List ι) : PState ι :=
  st.push [mkIns .mul x.1 y.2, mkIns .mul x.2 y.1, mkIns .mul y.1 y.1]
    [(mkRes .mul x.1 y.2 st.prog.length, mkRes .mul x.2 y.1 (st.prog.length + 1))] []
    [mkRes .mul y.1 y.1 (st.prog.length + 2)] ni

/-- The state after a computation node. -/
def PState.comp (st : PState ι) (op : TOp) (a b : TArg ι) : PState ι :=
  match op with
  | .add => asPush st .add (st.arg a) (st.arg b) (argInputs a ++ argInputs b)
  | .sub => asPush st .sub (st.arg a) (st.arg b) (argInputs a ++ argInputs b)
  | .mul => mulPush st (st.arg a) (st.arg b) (argInputs a ++ argInputs b)
  | .div => divPush st (st.arg a) (st.arg b) (argInputs a ++ argInputs b)

/-- The state after a division by zero: the condition `P₂ = 0`. -/
def PState.divZero (st : PState ι) (a b : TArg ι) : PState ι :=
  st.push [] [] [(st.arg b).1] [] (argInputs a ++ argInputs b)

/-- `S = P·D` for a tested value `P/D`. -/
def PState.sgnSP (st : PState ι) (v : TArg ι) : SP ι :=
  mkRes .mul (st.arg v).1 (st.arg v).2 st.prog.length

/-- `-S = 0 - S` for a tested value. -/
def PState.negSP (st : PState ι) (v : TArg ι) : SP ι :=
  mkRes .sub (.const 0, C 0) (st.sgnSP v) (st.prog.length + 1)

/-- The program computing `S` and `-S`. -/
def PState.geProg (st : PState ι) (v : TArg ι) : SLP ι ℝ :=
  [mkIns .mul (st.arg v).1 (st.arg v).2, mkIns .sub (.const 0, C 0) (st.sgnSP v)]

/-- Test `v ≥ 0` answered "yes" with `S = 0`. -/
def PState.geZero (st : PState ι) (v : TArg ι) : PState ι :=
  st.push (st.geProg v) [] [st.sgnSP v] [] (argInputs v)

/-- Test `v ≥ 0` answered "yes" with `S > 0`. -/
def PState.gePos (st : PState ι) (v : TArg ι) : PState ι :=
  st.push (st.geProg v) [] [] [st.sgnSP v] (argInputs v)

/-- Test `v ≥ 0` answered "no": `-S > 0`. -/
def PState.geNeg (st : PState ι) (v : TArg ι) : PState ι :=
  st.push (st.geProg v) [] [] [st.negSP v] (argInputs v)

/-- Test `v = 0` answered "yes": `P = 0`. -/
def PState.eqYes (st : PState ι) (v : TArg ι) : PState ι :=
  st.push [] [] [(st.arg v).1] [] (argInputs v)

/-- Test `v = 0` answered "no": `P² > 0`. -/
def PState.eqNo (st : PState ι) (v : TArg ι) : PState ι :=
  st.push [mkIns .mul (st.arg v).1 (st.arg v).1] [] []
    [mkRes .mul (st.arg v).1 (st.arg v).1 st.prog.length] (argInputs v)

open Classical in
/-- The cells of the paths of a tree from a given state, for the marked outcomes `S`. -/
def gen (S : Set (Option Bool)) : Tree ι → PState ι → List (Cell ι)
  | .leaf b, st => if some b ∈ S then [st.cell] else []
  | .comp op a b next, st =>
      gen S next (st.comp op a b) ++
        (if op = .div ∧ none ∈ S then [(st.divZero a b).cell] else [])
  | .test .ge v yes no, st =>
      gen S yes (st.geZero v) ++ gen S yes (st.gePos v) ++ gen S no (st.geNeg v)
  | .test .eq v yes no, st => gen S yes (st.eqYes v) ++ gen S no (st.eqNo v)

/-! #### Correctness -/

/-- The conditions of a state hold at `w`. -/
def PState.Sat (st : PState ι) (w : ι → ℝ) : Prop :=
  (∀ e ∈ st.eqs, eval w e.2 = 0) ∧ ∀ e ∈ st.poss, 0 < eval w e.2

/-- The number `x` is represented at `w` by the fraction `v`. -/
def valRel (w : ι → ℝ) (x : ℝ) (v : SP ι × SP ι) : Prop :=
  eval w v.2.2 ≠ 0 ∧ x = eval w v.1.2 / eval w v.2.2

/-- The values `vals` are represented at `w` by the fractions of the state. -/
def PState.Inv (st : PState ι) (vals : List ℝ) (w : ι → ℝ) : Prop :=
  List.Forall₂ (valRel w) vals st.vals

theorem mem_carrier_cell {st : PState ι} {w : ι → ℝ} : w ∈ st.cell.carrier ↔ st.Sat w := by
  show ((∀ p ∈ st.eqs.map Prod.snd, eval w p = 0) ∧
    ∀ q ∈ st.poss.map Prod.snd, 0 < eval w q) ↔ _
  simp only [List.forall_mem_map, PState.Sat]

theorem sat_push {st : PState ι} {l : SLP ι ℝ} {nv : List (SP ι × SP ι)} {ne np : List (SP ι)}
    {ni : List ι} {w : ι → ℝ} :
    (st.push l nv ne np ni).Sat w ↔
      st.Sat w ∧ (∀ e ∈ ne, eval w e.2 = 0) ∧ ∀ e ∈ np, 0 < eval w e.2 := by
  simp only [PState.Sat, PState.push, List.mem_append, or_imp, forall_and]
  tauto

theorem inv_push {st : PState ι} {l : SLP ι ℝ} {nv : List (SP ι × SP ι)} {ne np : List (SP ι)}
    {ni : List ι} {vals xs : List ℝ} {w : ι → ℝ} (h : st.Inv vals w)
    (h' : List.Forall₂ (valRel w) xs nv) : (st.push l nv ne np ni).Inv (vals ++ xs) w :=
  List.rel_append h h'

theorem inv_push_nil {st : PState ι} {l : SLP ι ℝ} {ne np : List (SP ι)} {ni : List ι}
    {vals : List ℝ} {w : ι → ℝ} (h : st.Inv vals w) : (st.push l [] ne np ni).Inv vals w := by
  have := inv_push (l := l) (ne := ne) (np := np) (ni := ni) h List.Forall₂.nil
  rwa [List.append_nil] at this

theorem forall₂_getD {α β : Type*} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) {d₁ : α} {d₂ : β} (hd : R d₁ d₂) (j : ℕ) :
    R (l₁.getD j d₁) (l₂.getD j d₂) := by
  induction h generalizing j with
  | nil => simpa using hd
  | cons hab _ ih =>
    cases j with
    | zero => simpa using hab
    | succ j => simpa using ih j

theorem arg_inv {st : PState ι} {vals : List ℝ} {w : ι → ℝ} (h : st.Inv vals w) (a : TArg ι) :
    valRel w (a.eval w vals) (st.arg a) := by
  cases a with
  | input i => simp [valRel, PState.arg, TArg.eval]
  | const c => simp [valRel, PState.arg, TArg.eval]
  | val j =>
    show valRel w (vals.getD j 0) (st.vals.getD j defaultVal)
    exact forall₂_getD h (by simp [valRel, defaultVal]) j

theorem not_exists_of_sub {L : List (Cell ι)} {p : (ι → ℝ) → Prop}
    (hL : ∀ B ∈ L, ∀ w ∈ B.carrier, p w) {w : ι → ℝ} (hw : ¬ p w) :
    ¬ ∃ B ∈ L, w ∈ B.carrier := by
  rintro ⟨B, hB, hwB⟩
  exact hw (hL B hB w hwB)

theorem exists_mem_append {L₁ L₂ : List (Cell ι)} {w : ι → ℝ} :
    (∃ B ∈ L₁ ++ L₂, w ∈ B.carrier) ↔ (∃ B ∈ L₁, w ∈ B.carrier) ∨ ∃ B ∈ L₂, w ∈ B.carrier := by
  simp only [List.mem_append, or_and_right, exists_or]

theorem sat_push0 {st : PState ι} {l : SLP ι ℝ} {nv : List (SP ι × SP ι)} {ni : List ι}
    {w : ι → ℝ} : (st.push l nv [] [] ni).Sat w ↔ st.Sat w := by
  rw [sat_push]; simp

theorem sat_push1e {st : PState ι} {l : SLP ι ℝ} {nv : List (SP ι × SP ι)} {e : SP ι}
    {ni : List ι} {w : ι → ℝ} : (st.push l nv [e] [] ni).Sat w ↔ st.Sat w ∧ eval w e.2 = 0 := by
  rw [sat_push]; simp

theorem sat_push1p {st : PState ι} {l : SLP ι ℝ} {nv : List (SP ι × SP ι)} {e : SP ι}
    {ni : List ι} {w : ι → ℝ} : (st.push l nv [] [e] ni).Sat w ↔ st.Sat w ∧ 0 < eval w e.2 := by
  rw [sat_push]; simp

theorem inv_asPush {st : PState ι} {vals : List ℝ} {w : ι → ℝ} (h : st.Inv vals w)
    {op : ArithOp} (hop : op = .add ∨ op = .sub) {x y : SP ι × SP ι} {ni : List ι} {u v : ℝ}
    (hu : valRel w u x) (hv : valRel w v y) :
    (asPush st op x y ni).Inv (vals ++ [op.apply u v]) w := by
  unfold asPush
  refine inv_push h (List.Forall₂.cons ?_ List.Forall₂.nil)
  obtain ⟨hd1, rfl⟩ := hu
  obtain ⟨hd2, rfl⟩ := hv
  rcases hop with rfl | rfl
  · simp only [valRel, mkRes, ArithOp.apply, map_add, map_mul]
    refine ⟨mul_ne_zero hd1 hd2, ?_⟩
    field_simp
  · simp only [valRel, mkRes, ArithOp.apply, map_sub, map_mul]
    refine ⟨mul_ne_zero hd1 hd2, ?_⟩
    field_simp

theorem inv_mulPush {st : PState ι} {vals : List ℝ} {w : ι → ℝ} (h : st.Inv vals w)
    {x y : SP ι × SP ι} {ni : List ι} {u v : ℝ} (hu : valRel w u x) (hv : valRel w v y) :
    (mulPush st x y ni).Inv (vals ++ [u * v]) w := by
  unfold mulPush
  refine inv_push h (List.Forall₂.cons ?_ List.Forall₂.nil)
  obtain ⟨hd1, rfl⟩ := hu
  obtain ⟨hd2, rfl⟩ := hv
  simp only [valRel, mkRes, ArithOp.apply, map_mul]
  refine ⟨mul_ne_zero hd1 hd2, ?_⟩
  field_simp

theorem inv_divPush {st : PState ι} {vals : List ℝ} {w : ι → ℝ} (h : st.Inv vals w)
    {x y : SP ι × SP ι} {ni : List ι} {u v : ℝ} (hu : valRel w u x) (hv : valRel w v y)
    (hz : eval w y.1.2 ≠ 0) :
    (divPush st x y ni).Inv (vals ++ [u / v]) w := by
  unfold divPush
  refine inv_push h (List.Forall₂.cons ?_ List.Forall₂.nil)
  obtain ⟨hd1, rfl⟩ := hu
  obtain ⟨hd2, rfl⟩ := hv
  simp only [valRel, mkRes, ArithOp.apply, map_mul]
  refine ⟨mul_ne_zero hd1 hz, ?_⟩
  field_simp

open Classical in
theorem gen_correct (S : Set (Option Bool)) (T : Tree ι) : ∀ st : PState ι,
    (∀ B ∈ gen S T st, ∀ w ∈ B.carrier, st.Sat w) ∧
    ∀ vals w, st.Inv vals w → st.Sat w →
      (T.runFrom w vals ∈ S ↔ ∃ B ∈ gen S T st, w ∈ B.carrier) := by
  induction T with
  | leaf b =>
    intro st
    refine ⟨fun B hB w hw => ?_, fun vals w _ hs => ?_⟩
    · simp only [gen] at hB
      split_ifs at hB
      · rw [List.mem_singleton] at hB
        subst hB
        exact mem_carrier_cell.1 hw
      · simp at hB
    · simp only [gen, Tree.runFrom]
      split_ifs with h
      · simp [h, mem_carrier_cell, hs]
      · simp [h]
  | comp op a b next ih =>
    intro st
    have hsub := (ih (st.comp op a b)).1
    have hcor := (ih (st.comp op a b)).2
    cases op with
    | add =>
      have hg : gen S (.comp .add a b next) st = gen S next (st.comp .add a b) := by simp [gen]
      rw [hg]
      refine ⟨fun B hB w hw => sat_push0.1 (hsub B hB w hw), fun vals w hinv hs => ?_⟩
      exact hcor _ w (inv_asPush hinv (Or.inl rfl) (arg_inv hinv a) (arg_inv hinv b))
        (sat_push0.2 hs)
    | sub =>
      have hg : gen S (.comp .sub a b next) st = gen S next (st.comp .sub a b) := by simp [gen]
      rw [hg]
      refine ⟨fun B hB w hw => sat_push0.1 (hsub B hB w hw), fun vals w hinv hs => ?_⟩
      exact hcor _ w (inv_asPush hinv (Or.inr rfl) (arg_inv hinv a) (arg_inv hinv b))
        (sat_push0.2 hs)
    | mul =>
      have hg : gen S (.comp .mul a b next) st = gen S next (st.comp .mul a b) := by simp [gen]
      rw [hg]
      refine ⟨fun B hB w hw => sat_push0.1 (hsub B hB w hw), fun vals w hinv hs => ?_⟩
      exact hcor _ w (inv_mulPush hinv (arg_inv hinv a) (arg_inv hinv b)) (sat_push0.2 hs)
    | div =>
      have hdiv : ∀ w, (st.comp .div a b).Sat w ↔
          st.Sat w ∧ 0 < eval w (st.arg b).1.2 * eval w (st.arg b).1.2 := by
        intro w
        refine sat_push1p.trans ?_
        simp only [mkRes, ArithOp.apply, map_mul]
      have hzero : ∀ w, (st.divZero a b).Sat w ↔ st.Sat w ∧ eval w (st.arg b).1.2 = 0 :=
        fun w => sat_push1e
      have hg : gen S (.comp .div a b next) st = gen S next (st.comp .div a b) ++
          (if none ∈ S then [(st.divZero a b).cell] else []) := by simp [gen]
      rw [hg]
      refine ⟨fun B hB w hw => ?_, fun vals w hinv hs => ?_⟩
      · rcases List.mem_append.1 hB with hB | hB
        · exact ((hdiv w).1 (hsub B hB w hw)).1
        · by_cases hN : none ∈ S
          · rw [ite_eq_left hN, List.mem_singleton] at hB
            subst hB
            exact ((hzero w).1 (mem_carrier_cell.1 hw)).1
          · rw [ite_eq_right hN] at hB
            simp at hB
      · obtain ⟨hd2, hy⟩ := arg_inv hinv b
        have hx := arg_inv hinv a
        simp only [Tree.runFrom]
        rw [exists_mem_append]
        by_cases hz : eval w (st.arg b).1.2 = 0
        · have hy0 : b.eval w vals = 0 := by rw [hy, hz, zero_div]
          rw [ite_eq_left hy0]
          have hno := not_exists_of_sub hsub (w := w) (fun h => by
            have := ((hdiv w).1 h).2
            rw [hz, mul_zero] at this
            exact lt_irrefl _ this)
          by_cases hN : none ∈ S
          · rw [ite_eq_left hN]
            simp only [List.mem_singleton, exists_eq_left, mem_carrier_cell, hzero]
            simp [hN, hs, hz, hno]
          · rw [ite_eq_right hN]
            simp [hN, hno]
        · have hy0 : b.eval w vals ≠ 0 := by rw [hy]; exact div_ne_zero hz hd2
          rw [ite_eq_right hy0]
          rw [hcor _ w (inv_divPush hinv hx ⟨hd2, hy⟩ hz) ((hdiv w).2 ⟨hs, mul_self_pos.2 hz⟩)]
          by_cases hN : none ∈ S
          · rw [ite_eq_left hN]
            simp only [List.mem_singleton, exists_eq_left, mem_carrier_cell, hzero]
            simp [hz]
          · rw [ite_eq_right hN]
            simp
  | test k v yes no ihy ihn =>
    intro st
    cases k with
    | ge =>
      have hs_eq : ∀ w, eval w (st.sgnSP v).2 = eval w (st.arg v).1.2 * eval w (st.arg v).2.2 :=
        fun w => map_mul _ _ _
      have hn_eq : ∀ w, eval w (st.negSP v).2 = 0 - eval w (st.sgnSP v).2 := by
        intro w
        show eval w (C 0 - (st.sgnSP v).2) = _
        rw [map_sub, eval_C]
      have hZ : ∀ w, (st.geZero v).Sat w ↔
          st.Sat w ∧ eval w (st.arg v).1.2 * eval w (st.arg v).2.2 = 0 := by
        intro w; rw [← hs_eq]; exact sat_push1e
      have hP : ∀ w, (st.gePos v).Sat w ↔
          st.Sat w ∧ 0 < eval w (st.arg v).1.2 * eval w (st.arg v).2.2 := by
        intro w; rw [← hs_eq]; exact sat_push1p
      have hN : ∀ w, (st.geNeg v).Sat w ↔
          st.Sat w ∧ eval w (st.arg v).1.2 * eval w (st.arg v).2.2 < 0 := by
        intro w
        refine sat_push1p.trans ?_
        rw [hn_eq, hs_eq, zero_sub, neg_pos]
      have hg : gen S (.test .ge v yes no) st =
          gen S yes (st.geZero v) ++ gen S yes (st.gePos v) ++ gen S no (st.geNeg v) := by
        simp [gen]
      rw [hg]
      refine ⟨fun B hB w hw => ?_, fun vals w hinv hs => ?_⟩
      · simp only [List.mem_append] at hB
        rcases hB with (hB | hB) | hB
        · exact ((hZ w).1 ((ihy _).1 B hB w hw)).1
        · exact ((hP w).1 ((ihy _).1 B hB w hw)).1
        · exact ((hN w).1 ((ihn _).1 B hB w hw)).1
      · obtain ⟨hd, hv⟩ := arg_inv hinv v
        simp only [Tree.runFrom]
        rw [exists_mem_append, exists_mem_append]
        have key : TestKind.ge.holds (v.eval w vals) ↔
            0 ≤ eval w (st.arg v).1.2 * eval w (st.arg v).2.2 := by
          show 0 ≤ v.eval w vals ↔ _
          rw [hv, div_nonneg_iff, mul_nonneg_iff]
        have n1 := not_exists_of_sub (ihy (st.geZero v)).1 (w := w)
        have n2 := not_exists_of_sub (ihy (st.gePos v)).1 (w := w)
        have n3 := not_exists_of_sub (ihn (st.geNeg v)).1 (w := w)
        rcases lt_trichotomy (eval w (st.arg v).1.2 * eval w (st.arg v).2.2) 0 with
          hlt | heq | hgt
        · rw [ite_eq_right (by rw [key]; exact not_le.2 hlt)]
          rw [(ihn (st.geNeg v)).2 vals w (inv_push_nil hinv) ((hN w).2 ⟨hs, hlt⟩)]
          have h1 := n1 (fun h => by have := ((hZ w).1 h).2; linarith)
          have h2 := n2 (fun h => by have := ((hP w).1 h).2; linarith)
          rw [or_iff_right (not_or.2 ⟨h1, h2⟩)]
        · rw [ite_eq_left (by rw [key]; exact heq.ge)]
          rw [(ihy (st.geZero v)).2 vals w (inv_push_nil hinv) ((hZ w).2 ⟨hs, heq⟩)]
          have h2 := n2 (fun h => by have := ((hP w).1 h).2; linarith)
          have h3 := n3 (fun h => by have := ((hN w).1 h).2; linarith)
          rw [or_iff_left h3, or_iff_left h2]
        · rw [ite_eq_left (by rw [key]; exact hgt.le)]
          rw [(ihy (st.gePos v)).2 vals w (inv_push_nil hinv) ((hP w).2 ⟨hs, hgt⟩)]
          have h1 := n1 (fun h => by have := ((hZ w).1 h).2; linarith)
          have h3 := n3 (fun h => by have := ((hN w).1 h).2; linarith)
          rw [or_iff_left h3, or_iff_right h1]
    | eq =>
      have hY : ∀ w, (st.eqYes v).Sat w ↔ st.Sat w ∧ eval w (st.arg v).1.2 = 0 :=
        fun w => sat_push1e
      have hN : ∀ w, (st.eqNo v).Sat w ↔
          st.Sat w ∧ 0 < eval w (st.arg v).1.2 * eval w (st.arg v).1.2 := by
        intro w
        refine sat_push1p.trans ?_
        simp only [mkRes, ArithOp.apply, map_mul]
      have hg : gen S (.test .eq v yes no) st =
          gen S yes (st.eqYes v) ++ gen S no (st.eqNo v) := by
        simp [gen]
      rw [hg]
      refine ⟨fun B hB w hw => ?_, fun vals w hinv hs => ?_⟩
      · rcases List.mem_append.1 hB with hB | hB
        · exact ((hY w).1 ((ihy _).1 B hB w hw)).1
        · exact ((hN w).1 ((ihn _).1 B hB w hw)).1
      · obtain ⟨hd, hv⟩ := arg_inv hinv v
        simp only [Tree.runFrom]
        rw [exists_mem_append]
        have key : TestKind.eq.holds (v.eval w vals) ↔ eval w (st.arg v).1.2 = 0 := by
          show v.eval w vals = 0 ↔ _
          rw [hv, div_eq_zero_iff]
          simp [hd]
        by_cases hp : eval w (st.arg v).1.2 = 0
        · rw [ite_eq_left (key.2 hp)]
          rw [(ihy (st.eqYes v)).2 vals w (inv_push_nil hinv) ((hY w).2 ⟨hs, hp⟩)]
          have h2 := not_exists_of_sub (ihn (st.eqNo v)).1 (w := w) (fun h => by
            have := ((hN w).1 h).2
            rw [hp, mul_zero] at this
            exact lt_irrefl _ this)
          rw [or_iff_left h2]
        · rw [ite_eq_right (fun h => hp (key.1 h))]
          rw [(ihn (st.eqNo v)).2 vals w (inv_push_nil hinv) ((hN w).2 ⟨hs, mul_self_pos.2 hp⟩)]
          have h1 := not_exists_of_sub (ihy (st.eqYes v)).1 (w := w) (fun h => hp ((hY w).1 h).2)
          rw [or_iff_right h1]

/-! #### Bounds -/

/-- The invariant of the symbolic state used for the bounds. -/
structure PState.WF (st : PState ι) (K : Set ℝ) : Prop where
  prog : ∀ i ∈ st.prog, cin K {x | x ∈ st.ins} i.a ∧ cin K {x | x ∈ st.ins} i.b
  vals : ∀ v ∈ st.vals, okvP K {x | x ∈ st.ins} st.prog v.1 ∧ okvP K {x | x ∈ st.ins} st.prog v.2
  eqs : ∀ e ∈ st.eqs, okvP K {x | x ∈ st.ins} st.prog e
  poss : ∀ e ∈ st.poss, okvP K {x | x ∈ st.ins} st.prog e

theorem wf_init (K : Set ℝ) : (PState.init : PState ι).WF K :=
  ⟨by simp [PState.init], by simp [PState.init], by simp [PState.init], by simp [PState.init]⟩

theorem wf_push {K : Set ℝ} {st : PState ι} (hwf : st.WF K) {l : SLP ι ℝ}
    {nv : List (SP ι × SP ι)} {ne np : List (SP ι)} {ni : List ι}
    (hl : ∀ i ∈ l, cin K {x | x ∈ st.ins ++ ni} i.a ∧ cin K {x | x ∈ st.ins ++ ni} i.b)
    (hnv : ∀ v ∈ nv, okvP K {x | x ∈ st.ins ++ ni} (st.prog ++ l) v.1 ∧
      okvP K {x | x ∈ st.ins ++ ni} (st.prog ++ l) v.2)
    (hne : ∀ e ∈ ne, okvP K {x | x ∈ st.ins ++ ni} (st.prog ++ l) e)
    (hnp : ∀ e ∈ np, okvP K {x | x ∈ st.ins ++ ni} (st.prog ++ l) e) :
    (st.push l nv ne np ni).WF K := by
  have hI : {x | x ∈ st.ins} ⊆ {x | x ∈ st.ins ++ ni} := fun x hx => List.mem_append_left _ hx
  have hold : ∀ e, okvP K {x | x ∈ st.ins} st.prog e →
      okvP K {x | x ∈ st.ins ++ ni} (st.prog ++ l) e :=
    fun e h => okvP_widen (okvP_mono h l) hI
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    rcases List.mem_append.1 hi with hi | hi
    · exact ⟨cin_mono (hwf.prog i hi).1 hI, cin_mono (hwf.prog i hi).2 hI⟩
    · exact hl i hi
  · intro v hv
    rcases List.mem_append.1 hv with hv | hv
    · exact ⟨hold _ (hwf.vals v hv).1, hold _ (hwf.vals v hv).2⟩
    · exact hnv v hv
  · intro e he
    rcases List.mem_append.1 he with he | he
    · exact hold _ (hwf.eqs e he)
    · exact hne e he
  · intro e he
    rcases List.mem_append.1 he with he | he
    · exact hold _ (hwf.poss e he)
    · exact hnp e he

theorem arg_ok {K : Set ℝ} {st : PState ι} (hwf : st.WF K) (h0 : (0 : ℝ) ∈ K)
    (h1 : (1 : ℝ) ∈ K) {a : TArg ι} (ha : a.consts ⊆ K) {I : Set ι}
    (hI : {x | x ∈ st.ins} ⊆ I) (hIa : ∀ x ∈ argInputs a, x ∈ I) :
    okvP K I st.prog (st.arg a).1 ∧ okvP K I st.prog (st.arg a).2 := by
  cases a with
  | input i => exact ⟨⟨hIa i (by simp [argInputs]), rfl⟩, ⟨h1, rfl⟩⟩
  | const c => exact ⟨⟨ha (by simp [TArg.consts]), rfl⟩, ⟨h1, rfl⟩⟩
  | val j =>
    show okvP K I st.prog (st.vals.getD j defaultVal).1 ∧
      okvP K I st.prog (st.vals.getD j defaultVal).2
    by_cases hj : j < st.vals.length
    · rw [List.getD_eq_getElem _ _ hj]
      have := hwf.vals _ (List.getElem_mem hj)
      exact ⟨okvP_widen this.1 hI, okvP_widen this.2 hI⟩
    · rw [List.getD_eq_default _ _ (not_lt.1 hj)]
      exact ⟨⟨h0, rfl⟩, ⟨h1, rfl⟩⟩

theorem forall_mem_singleton' {α : Type*} {p : α → Prop} {a : α} (h : p a) : ∀ x ∈ [a], p x := by
  intro x hx
  rw [List.mem_singleton] at hx
  subst hx
  exact h

theorem forall_mem_nil' {α : Type*} {p : α → Prop} : ∀ x ∈ ([] : List α), p x := by
  intro x hx
  simp at hx

theorem wf_asPush {K : Set ℝ} {st : PState ι} (hwf : st.WF K) (op : ArithOp)
    {x y : SP ι × SP ι} {ni : List ι}
    (hx1 : okvP K {z | z ∈ st.ins ++ ni} st.prog x.1)
    (hx2 : okvP K {z | z ∈ st.ins ++ ni} st.prog x.2)
    (hy1 : okvP K {z | z ∈ st.ins ++ ni} st.prog y.1)
    (hy2 : okvP K {z | z ∈ st.ins ++ ni} st.prog y.2) :
    (asPush st op x y ni).WF K := by
  set I : Set ι := {z | z ∈ st.ins ++ ni}
  set n := st.prog.length
  have e1 : okvP K I (st.prog ++ [mkIns .mul x.1 y.2]) (mkRes .mul x.1 y.2 n) :=
    okvP_step hx1 hy2 .mul rfl
  have e2 : okvP K I (st.prog ++ [mkIns .mul x.1 y.2] ++ [mkIns .mul y.1 x.2])
      (mkRes .mul y.1 x.2 (n + 1)) :=
    okvP_step (okvP_mono hy1 _) (okvP_mono hx2 _) .mul (by simp [n])
  have e3 : okvP K I (st.prog ++ [mkIns .mul x.1 y.2] ++ [mkIns .mul y.1 x.2] ++
      [mkIns op (mkRes .mul x.1 y.2 n) (mkRes .mul y.1 x.2 (n + 1))])
      (mkRes op (mkRes .mul x.1 y.2 n) (mkRes .mul y.1 x.2 (n + 1)) (n + 2)) :=
    okvP_step (okvP_mono e1 _) e2 op (by simp [n])
  have e4 : okvP K I (st.prog ++ [mkIns .mul x.1 y.2] ++ [mkIns .mul y.1 x.2] ++
      [mkIns op (mkRes .mul x.1 y.2 n) (mkRes .mul y.1 x.2 (n + 1))] ++ [mkIns .mul x.2 y.2])
      (mkRes .mul x.2 y.2 (n + 3)) :=
    okvP_step (okvP_prefix hx2 (by simp)) (okvP_prefix hy2 (by simp)) .mul (by simp [n])
  unfold asPush
  refine wf_push hwf ?_
    (forall_mem_singleton' ⟨okvP_prefix e3 (by simp [n]), okvP_prefix e4 (by simp [n])⟩)
    forall_mem_nil' forall_mem_nil'
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact ⟨cin_of_good hx1.isGood, cin_of_good hy2.isGood⟩
  · exact ⟨cin_of_good hy1.isGood, cin_of_good hx2.isGood⟩
  · exact ⟨cin_prev _ _ _, cin_prev _ _ _⟩
  · exact ⟨cin_of_good hx2.isGood, cin_of_good hy2.isGood⟩

theorem wf_mulPush {K : Set ℝ} {st : PState ι} (hwf : st.WF K)
    {x y : SP ι × SP ι} {ni : List ι}
    (hx1 : okvP K {z | z ∈ st.ins ++ ni} st.prog x.1)
    (hx2 : okvP K {z | z ∈ st.ins ++ ni} st.prog x.2)
    (hy1 : okvP K {z | z ∈ st.ins ++ ni} st.prog y.1)
    (hy2 : okvP K {z | z ∈ st.ins ++ ni} st.prog y.2) :
    (mulPush st x y ni).WF K := by
  set I : Set ι := {z | z ∈ st.ins ++ ni}
  set n := st.prog.length
  have e1 : okvP K I (st.prog ++ [mkIns .mul x.1 y.1]) (mkRes .mul x.1 y.1 n) :=
    okvP_step hx1 hy1 .mul rfl
  have e2 : okvP K I (st.prog ++ [mkIns .mul x.1 y.1] ++ [mkIns .mul x.2 y.2])
      (mkRes .mul x.2 y.2 (n + 1)) :=
    okvP_step (okvP_mono hx2 _) (okvP_mono hy2 _) .mul (by simp [n])
  unfold mulPush
  refine wf_push hwf ?_ (forall_mem_singleton' ⟨okvP_prefix e1 (by simp), okvP_prefix e2 (by simp)⟩)
    forall_mem_nil' forall_mem_nil'
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact ⟨cin_of_good hx1.isGood, cin_of_good hy1.isGood⟩
  · exact ⟨cin_of_good hx2.isGood, cin_of_good hy2.isGood⟩

theorem wf_divPush {K : Set ℝ} {st : PState ι} (hwf : st.WF K)
    {x y : SP ι × SP ι} {ni : List ι}
    (hx1 : okvP K {z | z ∈ st.ins ++ ni} st.prog x.1)
    (hx2 : okvP K {z | z ∈ st.ins ++ ni} st.prog x.2)
    (hy1 : okvP K {z | z ∈ st.ins ++ ni} st.prog y.1)
    (hy2 : okvP K {z | z ∈ st.ins ++ ni} st.prog y.2) :
    (divPush st x y ni).WF K := by
  set I : Set ι := {z | z ∈ st.ins ++ ni}
  set n := st.prog.length
  have e1 : okvP K I (st.prog ++ [mkIns .mul x.1 y.2]) (mkRes .mul x.1 y.2 n) :=
    okvP_step hx1 hy2 .mul rfl
  have e2 : okvP K I (st.prog ++ [mkIns .mul x.1 y.2] ++ [mkIns .mul x.2 y.1])
      (mkRes .mul x.2 y.1 (n + 1)) :=
    okvP_step (okvP_mono hx2 _) (okvP_mono hy1 _) .mul (by simp [n])
  have e3 : okvP K I (st.prog ++ [mkIns .mul x.1 y.2] ++ [mkIns .mul x.2 y.1] ++
      [mkIns .mul y.1 y.1]) (mkRes .mul y.1 y.1 (n + 2)) :=
    okvP_step (okvP_prefix hy1 (by simp)) (okvP_prefix hy1 (by simp)) .mul (by simp [n])
  unfold divPush
  refine wf_push hwf ?_ (forall_mem_singleton' ⟨okvP_prefix e1 (by simp), okvP_prefix e2 (by simp)⟩)
    forall_mem_nil' (forall_mem_singleton' (okvP_prefix e3 (by simp)))
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact ⟨cin_of_good hx1.isGood, cin_of_good hy2.isGood⟩
  · exact ⟨cin_of_good hx2.isGood, cin_of_good hy1.isGood⟩
  · exact ⟨cin_of_good hy1.isGood, cin_of_good hy1.isGood⟩

theorem subset_ins_append (l l' : List ι) : {x | x ∈ l} ⊆ {x | x ∈ l ++ l'} :=
  fun _ hx => List.mem_append_left _ hx

theorem wf_comp {K : Set ℝ} {st : PState ι} (hwf : st.WF K) (h0 : (0 : ℝ) ∈ K)
    (h1 : (1 : ℝ) ∈ K) (op : TOp) {a b : TArg ι} (ha : a.consts ⊆ K) (hb : b.consts ⊆ K) :
    (st.comp op a b).WF K := by
  obtain ⟨hx1, hx2⟩ := arg_ok hwf h0 h1 ha (subset_ins_append st.ins (argInputs a ++ argInputs b))
    (fun x hx => by simp [hx])
  obtain ⟨hy1, hy2⟩ := arg_ok hwf h0 h1 hb (subset_ins_append st.ins (argInputs a ++ argInputs b))
    (fun x hx => by simp [hx])
  cases op with
  | add => exact wf_asPush hwf .add hx1 hx2 hy1 hy2
  | sub => exact wf_asPush hwf .sub hx1 hx2 hy1 hy2
  | mul => exact wf_mulPush hwf hx1 hx2 hy1 hy2
  | div => exact wf_divPush hwf hx1 hx2 hy1 hy2

theorem wf_divZero {K : Set ℝ} {st : PState ι} (hwf : st.WF K) (h0 : (0 : ℝ) ∈ K)
    (h1 : (1 : ℝ) ∈ K) {a b : TArg ι} (hb : b.consts ⊆ K) : (st.divZero a b).WF K := by
  obtain ⟨hy1, -⟩ := arg_ok hwf h0 h1 hb (subset_ins_append st.ins (argInputs a ++ argInputs b))
    (fun x hx => by simp [hx])
  unfold PState.divZero
  exact wf_push hwf forall_mem_nil' forall_mem_nil' (forall_mem_singleton' (okvP_mono hy1 _))
    forall_mem_nil'

theorem wf_ge {K : Set ℝ} {st : PState ι} (hwf : st.WF K) (h0 : (0 : ℝ) ∈ K)
    (h1 : (1 : ℝ) ∈ K) {v : TArg ι} (hv : v.consts ⊆ K) :
    (st.geZero v).WF K ∧ (st.gePos v).WF K ∧ (st.geNeg v).WF K := by
  obtain ⟨hx1, hx2⟩ := arg_ok hwf h0 h1 hv (subset_ins_append st.ins (argInputs v))
    (fun x hx => by simp [hx])
  set I : Set ι := {z | z ∈ st.ins ++ argInputs v}
  have e1 : okvP K I (st.prog ++ [mkIns .mul (st.arg v).1 (st.arg v).2]) (st.sgnSP v) :=
    okvP_step hx1 hx2 .mul rfl
  have hc0 : okvP K I (st.prog ++ [mkIns .mul (st.arg v).1 (st.arg v).2]) (.const 0, C 0) :=
    ⟨h0, rfl⟩
  have e2 : okvP K I (st.prog ++ [mkIns .mul (st.arg v).1 (st.arg v).2] ++
      [mkIns .sub (.const 0, C 0) (st.sgnSP v)]) (st.negSP v) :=
    okvP_step hc0 e1 .sub (by simp)
  have hgp : st.prog ++ st.geProg v = st.prog ++ [mkIns .mul (st.arg v).1 (st.arg v).2] ++
      [mkIns .sub (.const 0, C 0) (st.sgnSP v)] := by
    simp [PState.geProg]
  have e1' : okvP K I (st.prog ++ st.geProg v) (st.sgnSP v) := by
    rw [hgp]; exact okvP_mono e1 _
  have e2' : okvP K I (st.prog ++ st.geProg v) (st.negSP v) := by
    rw [hgp]; exact e2
  have hl : ∀ i ∈ st.geProg v, cin K I i.a ∧ cin K I i.b := by
    intro i hi
    simp only [PState.geProg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ⟨cin_of_good hx1.isGood, cin_of_good hx2.isGood⟩
    · exact ⟨cin_of_good hc0.isGood, cin_prev _ _ _⟩
  refine ⟨?_, ?_, ?_⟩
  · exact wf_push hwf hl forall_mem_nil' (forall_mem_singleton' e1') forall_mem_nil'
  · exact wf_push hwf hl forall_mem_nil' forall_mem_nil' (forall_mem_singleton' e1')
  · exact wf_push hwf hl forall_mem_nil' forall_mem_nil' (forall_mem_singleton' e2')

theorem wf_eq {K : Set ℝ} {st : PState ι} (hwf : st.WF K) (h0 : (0 : ℝ) ∈ K)
    (h1 : (1 : ℝ) ∈ K) {v : TArg ι} (hv : v.consts ⊆ K) :
    (st.eqYes v).WF K ∧ (st.eqNo v).WF K := by
  obtain ⟨hx1, -⟩ := arg_ok hwf h0 h1 hv (subset_ins_append st.ins (argInputs v))
    (fun x hx => by simp [hx])
  refine ⟨?_, ?_⟩
  · unfold PState.eqYes
    exact wf_push hwf forall_mem_nil' forall_mem_nil' (forall_mem_singleton' (okvP_mono hx1 _))
      forall_mem_nil'
  · unfold PState.eqNo
    refine wf_push hwf ?_ forall_mem_nil' forall_mem_nil'
      (forall_mem_singleton' (okvP_step hx1 hx1 .mul rfl))
    intro i hi
    rw [List.mem_singleton] at hi
    subst hi
    exact ⟨cin_of_good hx1.isGood, cin_of_good hx1.isGood⟩

theorem cell_bounded {K0 : Set ℝ} {t n : ℕ} {st : PState ι} (hwf : st.WF (K0 ∪ {0, 1, -1}))
    (hp : st.prog.length ≤ 4 * n) (he : st.eqs.length + st.poss.length ≤ n)
    (hi : st.ins.length ≤ 2 * n) (hn : n ≤ t) : st.cell.Bounded t K0 := by
  classical
  have hvs : ∀ q ∈ SLP.values st.prog, q.vars ⊆ st.ins.toFinset := by
    rw [values_eq_vfrom]
    refine vars_vfrom st.prog (fun i hi => ?_) [] (by simp)
    rw [List.coe_toFinset]
    exact ⟨(hwf.prog i hi).1.2, (hwf.prog i hi).2.2⟩
  have hok : ∀ e, okvP (K0 ∪ {0, 1, -1}) {x | x ∈ st.ins} st.prog e →
      e.2.vars ⊆ st.ins.toFinset := by
    intro e h
    rw [← h.evalEq]
    refine vars_eval hvs ?_
    rw [List.coe_toFinset]
    exact (cin_of_good h.isGood).2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [PState.cell, List.length_map]; omega
  · simp only [PState.cell, List.length_map]; omega
  · simp only [PState.cell]; omega
  · intro p hp
    simp only [PState.cell, List.mem_map] at hp
    obtain ⟨e, he, rfl⟩ := hp
    exact ⟨e.1, (hwf.eqs e he).evalEq.symm⟩
  · intro p hp
    simp only [PState.cell, List.mem_map] at hp
    obtain ⟨e, he, rfl⟩ := hp
    exact ⟨e.1, (hwf.poss e he).evalEq.symm⟩
  · intro i hi
    exact Set.union_subset (hwf.prog i hi).1.1 (hwf.prog i hi).2.1
  · refine ⟨st.ins.toFinset, (List.toFinset_card_le _).trans (by omega), ?_, ?_⟩
    · intro i hi
      rw [List.coe_toFinset]
      exact Set.union_subset (hwf.prog i hi).1.2 (hwf.prog i hi).2.2
    · intro p hp
      simp only [PState.cell, List.mem_append, List.mem_map] at hp
      rcases hp with ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
      · exact hok e (hwf.eqs e he)
      · exact hok e (hwf.poss e he)

theorem depth_pos (T : Tree ι) : 1 ≤ T.depth := by
  cases T <;> simp [Tree.depth]

theorem gen_bounded (S : Set (Option Bool)) (K0 : Set ℝ) (t : ℕ) (T : Tree ι) :
    ∀ (st : PState ι) (n : ℕ), st.WF (K0 ∪ {0, 1, -1}) → T.consts ⊆ K0 →
      st.prog.length ≤ 4 * n → st.eqs.length + st.poss.length ≤ n → st.ins.length ≤ 2 * n →
      n + T.depth ≤ t → ∀ B ∈ gen S T st, B.Bounded t K0 := by
  classical
  have h0 : (0 : ℝ) ∈ K0 ∪ {0, 1, -1} := by simp
  have h1 : (1 : ℝ) ∈ K0 ∪ {0, 1, -1} := by simp
  have hK : ∀ s ⊆ K0, s ⊆ K0 ∪ {0, 1, -1} := fun s hs => hs.trans Set.subset_union_left
  induction T with
  | leaf b =>
    intro st n hwf _ hp he hi hd B hB
    simp only [gen] at hB
    split_ifs at hB
    · rw [List.mem_singleton] at hB
      subst hB
      exact cell_bounded hwf hp he hi (by simp only [Tree.depth] at hd; omega)
    · simp at hB
  | comp op a b next ih =>
    intro st n hwf hc hp he hi hd B hB
    simp only [Tree.consts, Set.union_subset_iff] at hc
    obtain ⟨⟨ha, hb⟩, hnc⟩ := hc
    have hdn := depth_pos next
    simp only [Tree.depth] at hd
    have hia := argInputs_length a
    have hib := argInputs_length b
    simp only [gen, List.mem_append] at hB
    rcases hB with hB | hB
    · have hc : (st.comp op a b).prog.length ≤ st.prog.length + 4 ∧
          (st.comp op a b).eqs.length + (st.comp op a b).poss.length ≤
            st.eqs.length + st.poss.length + 1 ∧
          (st.comp op a b).ins.length ≤ st.ins.length + 2 := by
        cases op <;>
          simp only [PState.comp, asPush, mulPush, divPush, PState.push, List.length_append,
            List.length_cons, List.length_nil] <;> omega
      exact ih (st.comp op a b) (n + 1) (wf_comp hwf h0 h1 op (hK _ ha) (hK _ hb)) hnc
        (by omega) (by omega) (by omega) (by omega) B hB
    · split_ifs at hB
      · rw [List.mem_singleton] at hB
        subst hB
        refine cell_bounded (n := n + 1) (wf_divZero hwf h0 h1 (hK _ hb)) ?_ ?_ ?_ (by omega)
        · simp only [PState.divZero, PState.push, List.length_append, List.length_nil]; omega
        · simp only [PState.divZero, PState.push, List.length_append, List.length_cons,
            List.length_nil]; omega
        · simp only [PState.divZero, PState.push, List.length_append]; omega
      · simp at hB
  | test k v yes no ihy ihn =>
    intro st n hwf hc hp he hi hd B hB
    simp only [Tree.consts, Set.union_subset_iff] at hc
    obtain ⟨⟨hv, hyc⟩, hnc⟩ := hc
    simp only [Tree.depth] at hd
    have hmy := le_max_left yes.depth no.depth
    have hmn := le_max_right yes.depth no.depth
    have hiv := argInputs_length v
    cases k with
    | ge =>
      obtain ⟨w1, w2, w3⟩ := wf_ge hwf h0 h1 (hK _ hv)
      simp only [gen, List.mem_append] at hB
      rcases hB with (hB | hB) | hB
      · refine ihy (st.geZero v) (n + 1) w1 hyc ?_ ?_ ?_ (by omega) B hB <;>
          simp only [PState.geZero, PState.geProg, PState.push, List.length_append,
            List.length_cons, List.length_nil] <;> omega
      · refine ihy (st.gePos v) (n + 1) w2 hyc ?_ ?_ ?_ (by omega) B hB <;>
          simp only [PState.gePos, PState.geProg, PState.push, List.length_append,
            List.length_cons, List.length_nil] <;> omega
      · refine ihn (st.geNeg v) (n + 1) w3 hnc ?_ ?_ ?_ (by omega) B hB <;>
          simp only [PState.geNeg, PState.geProg, PState.push, List.length_append,
            List.length_cons, List.length_nil] <;> omega
    | eq =>
      obtain ⟨w1, w2⟩ := wf_eq hwf h0 h1 (hK _ hv)
      simp only [gen, List.mem_append] at hB
      rcases hB with hB | hB
      · refine ihy (st.eqYes v) (n + 1) w1 hyc ?_ ?_ ?_ (by omega) B hB <;>
          simp only [PState.eqYes, PState.push, List.length_append,
            List.length_cons, List.length_nil] <;> omega
      · refine ihn (st.eqNo v) (n + 1) w2 hnc ?_ ?_ ?_ (by omega) B hB <;>
          simp only [PState.eqNo, PState.push, List.length_append,
            List.length_cons, List.length_nil] <;> omega

/-! #### The number of cells -/

theorem gen_length (S : Set (Option Bool)) (T : Tree ι) :
    ∀ st : PState ι, (gen S T st).length ≤ 3 ^ T.depth := by
  induction T with
  | leaf b =>
    intro st
    simp only [gen, Tree.depth]
    split_ifs <;> simp
  | comp op a b next ih =>
    intro st
    have h1 := ih (st.comp op a b)
    have hpos : 1 ≤ 3 ^ next.depth := Nat.one_le_pow _ _ (by norm_num)
    simp only [gen, Tree.depth, List.length_append, pow_succ]
    generalize 3 ^ next.depth = y at *
    split_ifs <;> simp only [List.length_cons, List.length_nil] <;> omega
  | test k v yes no ihy ihn =>
    intro st
    have hy : 3 ^ yes.depth ≤ 3 ^ max yes.depth no.depth :=
      Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
    have hn : 3 ^ no.depth ≤ 3 ^ max yes.depth no.depth :=
      Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
    cases k with
    | ge =>
      have h1 := ihy (st.geZero v)
      have h2 := ihy (st.gePos v)
      have h3 := ihn (st.geNeg v)
      simp only [gen, Tree.depth, List.length_append, pow_succ]
      generalize 3 ^ max yes.depth no.depth = y at *
      generalize 3 ^ yes.depth = a at *
      generalize 3 ^ no.depth = c at *
      omega
    | eq =>
      have h1 := ihy (st.eqYes v)
      have h2 := ihn (st.eqNo v)
      simp only [gen, Tree.depth, List.length_append, pow_succ]
      generalize 3 ^ max yes.depth no.depth = y at *
      generalize 3 ^ yes.depth = a at *
      generalize 3 ^ no.depth = c at *
      omega

/-! #### Degrees of the polynomials computed by a program -/

theorem totalDegree_eval_le {vs : List (MvPolynomial ι ℝ)} {m : ℕ}
    (hvs : ∀ p ∈ vs, p.totalDegree ≤ 2 ^ m) (o : Operand ι ℝ) :
    (o.eval vs).totalDegree ≤ 2 ^ m := by
  cases o with
  | input i =>
    show (X i : MvPolynomial ι ℝ).totalDegree ≤ 2 ^ m
    rw [totalDegree_X]
    exact Nat.one_le_two_pow
  | const c =>
    show (C c : MvPolynomial ι ℝ).totalDegree ≤ 2 ^ m
    rw [totalDegree_C]
    exact Nat.zero_le _
  | prev j =>
    show (vs.getD j 0).totalDegree ≤ 2 ^ m
    by_cases hj : j < vs.length
    · rw [List.getD_eq_getElem _ _ hj]
      exact hvs _ (List.getElem_mem hj)
    · rw [List.getD_eq_default _ _ (not_lt.1 hj), totalDegree_zero]
      exact Nat.zero_le _

theorem totalDegree_apply_le (op : ArithOp) {p q : MvPolynomial ι ℝ} {m : ℕ}
    (hp : p.totalDegree ≤ 2 ^ m) (hq : q.totalDegree ≤ 2 ^ m) :
    (op.apply p q).totalDegree ≤ 2 ^ (m + 1) := by
  rw [pow_succ]
  generalize 2 ^ m = y at *
  cases op
  · exact (totalDegree_add p q).trans (max_le (by omega) (by omega))
  · exact (totalDegree_sub p q).trans (max_le (by omega) (by omega))
  · exact (totalDegree_mul p q).trans (by omega)

theorem totalDegree_vfrom (Q : SLP ι ℝ) :
    ∀ vs : List (MvPolynomial ι ℝ), (∀ p ∈ vs, p.totalDegree ≤ 2 ^ vs.length) →
      ∀ p ∈ vfrom vs Q, p.totalDegree ≤ 2 ^ (vfrom vs Q).length := by
  induction Q with
  | nil => intro vs h; simpa [vfrom] using h
  | cons ins Q ih =>
    intro vs hvs
    rw [vfrom_cons]
    apply ih
    intro p hp
    rw [List.length_append, List.length_singleton]
    rcases List.mem_append.1 hp with hp | hp
    · exact (hvs p hp).trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _))
    · rw [List.mem_singleton] at hp
      subst hp
      exact totalDegree_apply_le ins.op (totalDegree_eval_le hvs _) (totalDegree_eval_le hvs _)

end CellsAux

/-- A polynomial computed by a straight-line program with `ℓ` operations has total degree at
most `2 ^ ℓ`. -/
theorem SLP.totalDegree_le {σ : Type*} {P : SLP σ ℝ} {q : MvPolynomial σ ℝ}
    (h : P.Computes q) : q.totalDegree ≤ 2 ^ P.length := by
  obtain ⟨o, rfl⟩ := h
  have hv : ∀ p ∈ SLP.values P, p.totalDegree ≤ 2 ^ (SLP.values P).length := by
    rw [CellsAux.values_eq_vfrom]
    exact CellsAux.totalDegree_vfrom P [] (by simp)
  rw [CellsAux.length_values] at hv
  exact CellsAux.totalDegree_eval_le hv o

/-- **Lemma 2.5 (cells).**  For a tree of depth at most `t` and any set `S` of marked outcomes,
the set of inputs whose outcome is marked is a finite union of cells satisfying the bounds of
the lemma. -/
theorem cells (T : Tree ι) (t : ℕ) (hT : T.depth ≤ t) (S : Set (Option Bool)) :
    ∃ L : List (Cell ι), (∀ B ∈ L, B.Bounded t T.consts) ∧
      {w | T.run w ∈ S} = ⋃ B ∈ L, B.carrier := by
  refine ⟨CellsAux.gen S T CellsAux.PState.init, ?_, ?_⟩
  · exact CellsAux.gen_bounded S T.consts t T _ 0 (CellsAux.wf_init _) subset_rfl
      (by simp [CellsAux.PState.init]) (by simp [CellsAux.PState.init])
      (by simp [CellsAux.PState.init]) (by simpa using hT)
  · ext w
    simp only [Set.mem_iUnion, exists_prop]
    exact (CellsAux.gen_correct S T _).2 [] w List.Forall₂.nil
      ⟨by simp [CellsAux.PState.init], by simp [CellsAux.PState.init]⟩

/-- **Lemma 2.5 (cells)** with a bound on the number of cells: at most `4 ^ t` cells suffice
(the construction gives at most `3 ^ depth`). -/
theorem cells_length (T : Tree ι) (t : ℕ) (hT : T.depth ≤ t) (S : Set (Option Bool)) :
    ∃ L : List (Cell ι), (∀ B ∈ L, B.Bounded t T.consts) ∧
      ({w | T.run w ∈ S} = ⋃ B ∈ L, B.carrier) ∧ L.length ≤ 4 ^ t := by
  refine ⟨CellsAux.gen S T CellsAux.PState.init, ?_, ?_, ?_⟩
  · exact CellsAux.gen_bounded S T.consts t T _ 0 (CellsAux.wf_init _) subset_rfl
      (by simp [CellsAux.PState.init]) (by simp [CellsAux.PState.init])
      (by simp [CellsAux.PState.init]) (by simpa using hT)
  · ext w
    simp only [Set.mem_iUnion, exists_prop]
    exact (CellsAux.gen_correct S T _).2 [] w List.Forall₂.nil
      ⟨by simp [CellsAux.PState.init], by simp [CellsAux.PState.init]⟩
  · exact (CellsAux.gen_length S T _).trans
      ((Nat.pow_le_pow_right (by norm_num) hT).trans (Nat.pow_le_pow_left (by norm_num) t))

end ClassSep
