import ClassSeparations.Basic.Tree

/-!
# Operations on algebraic computation trees

Combinators on the trees of `ClassSeparations.Basic.Tree`, with their effect on runs and on
the depth.

* `Tree.subst g p`: replace each input operand `input i` by the operand `g i` and shift every
  value reference `val j` by `p`.  Run after `p` precomputed values `pre`, it behaves like the
  original tree on the input `i ↦ (g i).eval w pre` (`Tree.runFrom_subst`), provided the
  operands `g i` refer only to the values in `pre`.
* `Tree.rename f`: rename the inputs; the run on `w` is the run of the original tree on
  `w ∘ f`.
* `Tree.shift p`: shift the value references by `p`.
* `Tree.negPrefix L T`: compute `-w i` for the inputs `i ∈ L` (one node `0 - w i` each), then
  run `T`.  `Tree.negSubst L g T` combines it with `subst`.
* `Tree.compl`: swap accepting and rejecting leaves (a division by zero still rejects).
* `Tree.andThen T₂ T₁ q`: run `T₁`; at each accepting leaf continue with `T₂`, whose value
  references are shifted by the (path-dependent) number of values computed so far.  The result
  accepts exactly when both trees accept, and its depth is at most `depth T₁ + depth T₂`.
* For inputs `(x, y, z)`: `Tree.renameCert` (rename the certificate coordinates), `Tree.negY`
  (replace `y` by `-y`, one more node) and `Tree.negRowY` (replace the first argument
  `X ∈ ℝ^{m × n}` by `X'`, which has row `i₀` negated, and `y` by `-y`; `n + 1` more nodes).
-/

noncomputable section

namespace ClassSep

universe u v

variable {ι : Type u} {ι' : Type v}

/-! ## Substitution of operands for inputs -/

/-- Replace the input operand `input i` by `g i` and shift `val j` to `val (j + p)`. -/
def TArg.subst (g : ι → TArg ι') (p : ℕ) : TArg ι → TArg ι'
  | .input i => g i
  | .const c => .const c
  | .val j => .val (j + p)

/-- Replace every input operand `input i` by `g i` and shift every value reference by `p`. -/
def Tree.subst (g : ι → TArg ι') (p : ℕ) : Tree ι → Tree ι'
  | .leaf b => .leaf b
  | .comp op a b next => .comp op (a.subst g p) (b.subst g p) (next.subst g p)
  | .test k v yes no => .test k (v.subst g p) (yes.subst g p) (no.subst g p)

@[simp] theorem Tree.depth_subst (g : ι → TArg ι') (p : ℕ) (T : Tree ι) :
    (T.subst g p).depth = T.depth := by
  induction T with
  | leaf b => rfl
  | comp op a b next ih => simp [Tree.subst, Tree.depth, ih]
  | test k v yes no ih₁ ih₂ => simp [Tree.subst, Tree.depth, ih₁, ih₂]

/-- The operand refers only to the first `p` computed values. -/
def TArg.RefsBelow (p : ℕ) : TArg ι → Prop
  | .input _ => True
  | .const _ => True
  | .val j => j < p

theorem TArg.eval_append_of_refsBelow (w : ι → ℝ) (pre vals : List ℝ) (a : TArg ι)
    (ha : a.RefsBelow pre.length) : a.eval w (pre ++ vals) = a.eval w pre := by
  cases a with
  | input i => rfl
  | const c => rfl
  | val j => exact List.getD_append _ _ _ _ ha

theorem TArg.eval_subst (g : ι → TArg ι') (w : ι' → ℝ) (pre vals : List ℝ)
    (hg : ∀ i, (g i).RefsBelow pre.length) (a : TArg ι) :
    (a.subst g pre.length).eval w (pre ++ vals) = a.eval (fun i => (g i).eval w pre) vals := by
  cases a with
  | input i => exact TArg.eval_append_of_refsBelow _ _ _ _ (hg i)
  | const c => rfl
  | val j =>
    simp only [TArg.subst, TArg.eval]
    rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel]

/-- **Substitution.**  Run after the values `pre`, the substituted tree behaves like the
original tree on the input `i ↦ (g i).eval w pre`. -/
theorem Tree.runFrom_subst (g : ι → TArg ι') (w : ι' → ℝ) (pre : List ℝ)
    (hg : ∀ i, (g i).RefsBelow pre.length) (T : Tree ι) (vals : List ℝ) :
    (T.subst g pre.length).runFrom w (pre ++ vals) =
      T.runFrom (fun i => (g i).eval w pre) vals := by
  induction T generalizing vals with
  | leaf b => rfl
  | comp op a b next ih =>
    cases op <;>
      simp only [Tree.subst, Tree.runFrom, TArg.eval_subst g w pre _ hg, List.append_assoc, ih]
  | test k v yes no ih₁ ih₂ =>
    simp only [Tree.subst, Tree.runFrom, ih₁, ih₂]
    rw [TArg.eval_subst g w pre _ hg]

/-! ## Renaming and shifting -/

/-- Rename the inputs of a tree along `f : ι → ι'`. -/
def Tree.rename (f : ι → ι') (T : Tree ι) : Tree ι' := T.subst (fun i => .input (f i)) 0

@[simp] theorem Tree.depth_rename (f : ι → ι') (T : Tree ι) : (T.rename f).depth = T.depth :=
  Tree.depth_subst _ _ _

theorem Tree.runFrom_rename (f : ι → ι') (T : Tree ι) (w : ι' → ℝ) (vals : List ℝ) :
    (T.rename f).runFrom w vals = T.runFrom (w ∘ f) vals :=
  Tree.runFrom_subst (fun i => .input (f i)) w [] (fun _ => trivial) T vals

theorem Tree.run_rename (f : ι → ι') (T : Tree ι) (w : ι' → ℝ) :
    (T.rename f).run w = T.run (w ∘ f) :=
  Tree.runFrom_rename f T w []

/-- Shift all value references of a tree by `p`. -/
def Tree.shift (p : ℕ) (T : Tree ι) : Tree ι := T.subst TArg.input p

@[simp] theorem Tree.depth_shift (p : ℕ) (T : Tree ι) : (T.shift p).depth = T.depth :=
  Tree.depth_subst _ _ _

theorem Tree.runFrom_shift (T : Tree ι) (w : ι → ℝ) (pre vals : List ℝ) :
    (T.shift pre.length).runFrom w (pre ++ vals) = T.runFrom w vals :=
  Tree.runFrom_subst TArg.input w pre (fun _ => trivial) T vals

/-! ## Precomputing negated inputs -/

/-- Compute `0 - w i` for the inputs `i` of the list `L` (one node each), then run `T`. -/
def Tree.negPrefix : List ι → Tree ι → Tree ι
  | [], T => T
  | i :: L, T => .comp .sub (.const 0) (.input i) (Tree.negPrefix L T)

@[simp] theorem Tree.depth_negPrefix (L : List ι) (T : Tree ι) :
    (Tree.negPrefix L T).depth = T.depth + L.length := by
  induction L with
  | nil => rfl
  | cons i L ih => simp [Tree.negPrefix, Tree.depth, ih]; omega

theorem Tree.runFrom_negPrefix (L : List ι) (T : Tree ι) (w : ι → ℝ) (vals : List ℝ) :
    (Tree.negPrefix L T).runFrom w vals = T.runFrom w (vals ++ L.map fun i => -w i) := by
  induction L generalizing vals with
  | nil => simp [Tree.negPrefix]
  | cons i L ih => simp [Tree.negPrefix, Tree.runFrom, TArg.eval, ih]

/-- Compute `-w j` for the inputs `j ∈ L`, then run `T` with the input `i` replaced by the
operand `g i` (which may refer to the negated inputs as `val 0, …, val (|L| - 1)`). -/
def Tree.negSubst (L : List ι') (g : ι → TArg ι') (T : Tree ι) : Tree ι' :=
  Tree.negPrefix L (T.subst g L.length)

@[simp] theorem Tree.depth_negSubst (L : List ι') (g : ι → TArg ι') (T : Tree ι) :
    (T.negSubst L g).depth = T.depth + L.length := by
  simp [Tree.negSubst]

theorem Tree.run_negSubst (L : List ι') (g : ι → TArg ι') (hg : ∀ i, (g i).RefsBelow L.length)
    (T : Tree ι) (w : ι' → ℝ) :
    (T.negSubst L g).run w = T.run (fun i => (g i).eval w (L.map fun j => -w j)) := by
  have h := Tree.runFrom_subst g w (L.map fun j => -w j) (by simpa using hg) T []
  rw [List.length_map, List.append_nil] at h
  rw [Tree.negSubst, Tree.run, Tree.runFrom_negPrefix, List.nil_append, h, Tree.run]

/-! ## Complement -/

/-- Swap the accepting and the rejecting leaves. -/
def Tree.compl : Tree ι → Tree ι
  | .leaf b => .leaf (!b)
  | .comp op a b next => .comp op a b next.compl
  | .test k v yes no => .test k v yes.compl no.compl

@[simp] theorem Tree.depth_compl (T : Tree ι) : T.compl.depth = T.depth := by
  induction T with
  | leaf b => rfl
  | comp op a b next ih => simp [Tree.compl, Tree.depth, ih]
  | test k v yes no ih₁ ih₂ => simp [Tree.compl, Tree.depth, ih₁, ih₂]

/-- The complement negates the label of the leaf reached; a division by zero is unchanged. -/
theorem Tree.runFrom_compl (T : Tree ι) (w : ι → ℝ) (vals : List ℝ) :
    T.compl.runFrom w vals = (T.runFrom w vals).map (!·) := by
  induction T generalizing vals with
  | leaf b => rfl
  | comp op a b next ih =>
    cases op <;> simp only [Tree.compl, Tree.runFrom, ih]
    split_ifs <;> rfl
  | test k v yes no ih₁ ih₂ =>
    simp only [Tree.compl, Tree.runFrom, ih₁, ih₂]
    split_ifs <;> rfl

theorem Tree.run_compl (T : Tree ι) (w : ι → ℝ) : T.compl.run w = (T.run w).map (!·) :=
  Tree.runFrom_compl T w []

/-- The complement accepts exactly the inputs that reach a rejecting leaf. -/
theorem Tree.accepts_compl (T : Tree ι) (w : ι → ℝ) :
    T.compl.Accepts w ↔ T.run w = some false := by
  rw [Tree.Accepts, Tree.run_compl]
  rcases T.run w with _ | _ | _ <;> simp

/-! ## Conjunction -/

/-- Run `T₁`; at each accepting leaf continue with `T₂`.  The argument `q` is the number of
values computed before the current node; the value references of `T₂` are shifted by it. -/
def Tree.andThen : Tree ι → Tree ι → ℕ → Tree ι
  | .leaf true, T₂, q => T₂.shift q
  | .leaf false, _, _ => .leaf false
  | .comp op a b next, T₂, q => .comp op a b (next.andThen T₂ (q + 1))
  | .test k v yes no, T₂, q => .test k v (yes.andThen T₂ q) (no.andThen T₂ q)

/-- The outcome of a conjunction: the outcome of the first tree unless it accepts, in which
case the outcome of the second. -/
def andOutcome (o₁ o₂ : Option Bool) : Option Bool :=
  o₁.bind fun b => if b then o₂ else some false

theorem Tree.runFrom_andThen (T₁ T₂ : Tree ι) (w : ι → ℝ) (q : ℕ) (vals : List ℝ)
    (hq : vals.length = q) :
    (T₁.andThen T₂ q).runFrom w vals = andOutcome (T₁.runFrom w vals) (T₂.run w) := by
  induction T₁ generalizing q vals with
  | leaf b =>
    cases b
    · simp [Tree.andThen, Tree.runFrom, andOutcome]
    · subst hq
      have h := Tree.runFrom_shift T₂ w vals []
      rw [List.append_nil] at h
      simp only [Tree.andThen, Tree.runFrom, andOutcome, Option.bind_some, ite_true, Tree.run]
      exact h
  | comp op a b next ih =>
    have hq' : ∀ x : ℝ, (vals ++ [x]).length = q + 1 := by simp [hq]
    cases op <;> simp only [Tree.andThen, Tree.runFrom]
    · exact ih _ _ (hq' _)
    · exact ih _ _ (hq' _)
    · exact ih _ _ (hq' _)
    · split_ifs
      · simp [andOutcome]
      · exact ih _ _ (hq' _)
  | test k v yes no ih₁ ih₂ =>
    simp only [Tree.andThen, Tree.runFrom]
    split_ifs
    · exact ih₁ _ _ hq
    · exact ih₂ _ _ hq

theorem Tree.run_andThen (T₁ T₂ : Tree ι) (w : ι → ℝ) :
    (T₁.andThen T₂ 0).run w = andOutcome (T₁.run w) (T₂.run w) :=
  Tree.runFrom_andThen T₁ T₂ w 0 [] rfl

/-- The conjunction accepts exactly when both trees accept. -/
theorem Tree.accepts_andThen (T₁ T₂ : Tree ι) (w : ι → ℝ) :
    (T₁.andThen T₂ 0).Accepts w ↔ T₁.Accepts w ∧ T₂.Accepts w := by
  rw [Tree.Accepts, Tree.run_andThen, Tree.Accepts, Tree.Accepts]
  rcases T₁.run w with _ | _ | _ <;> simp [andOutcome]

theorem Tree.depth_andThen_le (T₁ T₂ : Tree ι) (q : ℕ) :
    (T₁.andThen T₂ q).depth ≤ T₁.depth + T₂.depth := by
  induction T₁ generalizing q with
  | leaf b => cases b <;> simp [Tree.andThen, Tree.depth]
  | comp op a b next ih =>
    simp only [Tree.andThen, Tree.depth]
    have := ih (q + 1)
    omega
  | test k v yes no ih₁ ih₂ =>
    simp only [Tree.andThen, Tree.depth]
    have h₁ := ih₁ q
    have h₂ := ih₂ q
    omega

/-! ## Inputs `(x, y, z)` -/

section Inp3

variable {α γ γ' : Type}

/-- Rename the certificate coordinates of a tree on inputs `(x, y, z)`. -/
def Tree.renameCert (e : γ → γ') (T : Tree (α ⊕ Unit ⊕ γ)) : Tree (α ⊕ Unit ⊕ γ') :=
  T.rename (Sum.map id (Sum.map id e))

@[simp] theorem Tree.depth_renameCert (e : γ → γ') (T : Tree (α ⊕ Unit ⊕ γ)) :
    (T.renameCert e).depth = T.depth :=
  Tree.depth_rename _ _

theorem Tree.run_renameCert (e : γ → γ') (T : Tree (α ⊕ Unit ⊕ γ)) (x : α → ℝ) (y : ℝ)
    (z : γ' → ℝ) : (T.renameCert e).run (inp3 x y z) = T.run (inp3 x y (z ∘ e)) := by
  rw [Tree.renameCert, Tree.run_rename]
  congr 1
  funext i
  rcases i with i | i | i <;> rfl

/-- Replace `y` by `-y` (one more node). -/
def Tree.negY (T : Tree (α ⊕ Unit ⊕ γ)) : Tree (α ⊕ Unit ⊕ γ) :=
  T.negSubst [Sum.inr (Sum.inl ())]
    (Sum.elim (fun i => .input (.inl i)) (Sum.elim (fun _ => .val 0) fun j => .input (.inr (.inr j))))

@[simp] theorem Tree.depth_negY (T : Tree (α ⊕ Unit ⊕ γ)) : T.negY.depth = T.depth + 1 := by
  simp [Tree.negY]

theorem Tree.run_negY (T : Tree (α ⊕ Unit ⊕ γ)) (x : α → ℝ) (y : ℝ) (z : γ → ℝ) :
    T.negY.run (inp3 x y z) = T.run (inp3 x (-y) z) := by
  rw [Tree.negY, Tree.run_negSubst]
  · congr 1
    funext i
    rcases i with i | i | i <;> rfl
  · rintro (i | i | i) <;> simp [TArg.RefsBelow]

/-- Negate row `i₀` of a matrix `X ∈ ℝ^{m × n}`. -/
def negRow {m n : ℕ} (i₀ : Fin m) (X : Fin m × Fin n → ℝ) : Fin m × Fin n → ℝ :=
  fun p => if p.1 = i₀ then -X p else X p

/-- The operands replacing the inputs in `Tree.negRowY`. -/
def negRowYArg {m n : ℕ} (i₀ : Fin m) (e : γ → γ') :
    (Fin m × Fin n) ⊕ Unit ⊕ γ → TArg ((Fin m × Fin n) ⊕ Unit ⊕ γ') :=
  Sum.elim (fun p => if p.1 = i₀ then .val (p.2.val + 1) else .input (.inl p))
    (Sum.elim (fun _ => .val 0) fun c => .input (.inr (.inr (e c))))

/-- The inputs negated by `Tree.negRowY`: `y` and the entries of row `i₀`. -/
def negRowYList {m n : ℕ} (i₀ : Fin m) : List ((Fin m × Fin n) ⊕ Unit ⊕ γ') :=
  Sum.inr (Sum.inl ()) :: (List.finRange n).map fun j => Sum.inl (i₀, j)

/-- Replace `(X, y, z)` by `(X', -y, z ∘ e)`, where `X'` is `X` with row `i₀` negated
(`n + 1` more nodes). -/
def Tree.negRowY {m n : ℕ} (i₀ : Fin m) (e : γ → γ') (T : Tree ((Fin m × Fin n) ⊕ Unit ⊕ γ)) :
    Tree ((Fin m × Fin n) ⊕ Unit ⊕ γ') :=
  T.negSubst (negRowYList i₀) (negRowYArg i₀ e)

@[simp] theorem Tree.depth_negRowY {m n : ℕ} (i₀ : Fin m) (e : γ → γ')
    (T : Tree ((Fin m × Fin n) ⊕ Unit ⊕ γ)) : (T.negRowY i₀ e).depth = T.depth + (n + 1) := by
  simp [Tree.negRowY, negRowYList]

theorem Tree.run_negRowY {m n : ℕ} (i₀ : Fin m) (e : γ → γ')
    (T : Tree ((Fin m × Fin n) ⊕ Unit ⊕ γ)) (X : Fin m × Fin n → ℝ) (y : ℝ) (z : γ' → ℝ) :
    (T.negRowY i₀ e).run (inp3 X y z) = T.run (inp3 (negRow i₀ X) (-y) (z ∘ e)) := by
  rw [Tree.negRowY, Tree.run_negSubst]
  · congr 1
    funext i
    rcases i with ⟨i, j⟩ | i | c
    · by_cases h : i = i₀
      · subst h
        simp only [negRowYArg, negRowYList, Sum.elim_inl, ite_true, TArg.eval, List.map_cons,
          List.map_map, List.getD_cons_succ, inp3, negRow]
        rw [List.getD_eq_getElem _ _ (by simp)]
        simp
      · simp [negRowYArg, h, TArg.eval, inp3, negRow]
    · rfl
    · rfl
  · rintro (⟨i, j⟩ | i | c)
    · by_cases h : i = i₀ <;> simp [negRowYArg, negRowYList, h, TArg.RefsBelow]
    · simp [negRowYArg, negRowYList, TArg.RefsBelow]
    · simp [negRowYArg, TArg.RefsBelow]

end Inp3

/-! ## Splitting certificates -/

/-- `∃ z ∀ u` over the concatenation of two pairs of blocks, for a conjunction of conditions on
the two halves, splits into two independent `∃ ∀` statements. -/
theorem exists_forall_append_iff {k l : ℕ} (P Q : (Fin k → ℝ) → (Fin l → ℝ) → Prop) :
    (∃ z : Fin (k + k) → ℝ, ∀ u : Fin (l + l) → ℝ,
      P (z ∘ Fin.castAdd k) (u ∘ Fin.castAdd l) ∧ Q (z ∘ Fin.natAdd k) (u ∘ Fin.natAdd l)) ↔
      (∃ z, ∀ u, P z u) ∧ (∃ z, ∀ u, Q z u) := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨⟨z ∘ Fin.castAdd k, fun u => ?_⟩, ⟨z ∘ Fin.natAdd k, fun u => ?_⟩⟩
    · have h := (hz (Fin.append u 0)).1
      have hu : (Fin.append u 0 : Fin (l + l) → ℝ) ∘ Fin.castAdd l = u := by
        funext i; exact Fin.append_left _ _ i
      rwa [hu] at h
    · have h := (hz (Fin.append 0 u)).2
      have hu : (Fin.append 0 u : Fin (l + l) → ℝ) ∘ Fin.natAdd l = u := by
        funext i; exact Fin.append_right _ _ i
      rwa [hu] at h
  · rintro ⟨⟨z₁, h₁⟩, ⟨z₂, h₂⟩⟩
    refine ⟨Fin.append z₁ z₂, fun u => ⟨?_, ?_⟩⟩
    · have hz : (Fin.append z₁ z₂ : Fin (k + k) → ℝ) ∘ Fin.castAdd k = z₁ := by
        funext i; exact Fin.append_left _ _ i
      rw [hz]; exact h₁ _
    · have hz : (Fin.append z₁ z₂ : Fin (k + k) → ℝ) ∘ Fin.natAdd k = z₂ := by
        funext i; exact Fin.append_right _ _ i
      rw [hz]; exact h₂ _

end ClassSep
