import ClassSeparations.Universal.Onesided

/-!
# The complex field (§5.6, Theorem 5.3, Remark 5.4)

A *complex tree* is defined as in Definition 2.1, with complex inputs and constants and with
tests `v = 0` only.  An input that reaches a division by zero is rejected.

**Theorem 5.3.**  Let `f ∈ ℝ[X₁, …, Xₙ]` have degree at most `d ≥ 1`.  Suppose that a complex
tree of depth `t` on inputs `(x, y, z) ∈ ℂⁿ × ℂ × ℂᵏ` satisfies, for all `(x, y)`, either
(a) it accepts `(x, y, z)` for some `z` exactly when `y = f(x)`, or
(b) it accepts `(x, y, z)` for every `z` exactly when `y = f(x)`.
Then the border complexity of `f` is at most `C(d+1)⁶((t+1)² + n)`.
-/

noncomputable section

open MvPolynomial Set

namespace ClassSep

/-- An operand of a complex tree. -/
inductive CArg (ι : Type) where
  | input (i : ι)
  | const (c : ℂ)
  | val (j : ℕ)

/-- A complex computation tree: tests are `v = 0` only. -/
inductive CTree (ι : Type) where
  | leaf (accept : Bool)
  | comp (op : TOp) (a b : CArg ι) (next : CTree ι)
  | test (v : CArg ι) (yes no : CTree ι)

namespace CTree

variable {ι : Type}

/-- Depth of a complex tree. -/
def depth : CTree ι → ℕ
  | .leaf _ => 1
  | .comp _ _ _ next => next.depth + 1
  | .test _ yes no => max yes.depth no.depth + 1

/-- Value of an operand. -/
def argEval (w : ι → ℂ) (vals : List ℂ) : CArg ι → ℂ
  | .input i => w i
  | .const c => c
  | .val j => vals.getD j 0

open Classical in
/-- Run a complex tree; `none` signals a division by zero. -/
def runFrom (w : ι → ℂ) : CTree ι → List ℂ → Option Bool
  | .leaf b, _ => some b
  | .comp op a b next, vals =>
      let x := argEval w vals a
      let y := argEval w vals b
      match op with
      | .add => next.runFrom w (vals ++ [x + y])
      | .sub => next.runFrom w (vals ++ [x - y])
      | .mul => next.runFrom w (vals ++ [x * y])
      | .div => if y = 0 then none else next.runFrom w (vals ++ [x / y])
  | .test v yes no, vals =>
      if argEval w vals v = 0 then yes.runFrom w vals else no.runFrom w vals

/-- The complex tree accepts `w`. -/
def Accepts (T : CTree ι) (w : ι → ℂ) : Prop := T.runFrom w [] = some true

end CTree

/-- The complex input `(x, y, z)`. -/
def cinp3 {α γ : Type} (x : α → ℂ) (y : ℂ) (z : γ → ℂ) : α ⊕ Unit ⊕ γ → ℂ :=
  Sum.elim x (Sum.elim (fun _ => y) z)

/-! ## From complex trees to real trees

Every complex value is stored as a block of `11` real values; the real and imaginary parts of
the `j`-th complex value are the real values `11 j + 9` and `11 j + 10`.  The other entries of a
block are intermediate results (or the dummy value `0 + 0`).  A complex input or constant is
given by a pair of real operands `g i`. -/

namespace CTree

variable {ι ι' : Type}

/-- The operand holding the real part of a complex operand. -/
def reArg (g : ι → TArg ι' × TArg ι') : CArg ι → TArg ι'
  | .input i => (g i).1
  | .const c => .const c.re
  | .val j => .val (11 * j + 9)

/-- The operand holding the imaginary part of a complex operand. -/
def imArg (g : ι → TArg ι' × TArg ι') : CArg ι → TArg ι'
  | .input i => (g i).2
  | .const c => .const c.im
  | .val j => .val (11 * j + 10)

/-- `n` dummy nodes `0 + 0`, followed by `T`. -/
def pad : ℕ → Tree ι' → Tree ι'
  | 0, T => T
  | n + 1, T => .comp .add (.const 0) (.const 0) (pad n T)

theorem runFrom_pad (n : ℕ) (T : Tree ι') (w : ι' → ℝ) (vals : List ℝ) :
    (pad n T).runFrom w vals = T.runFrom w (vals ++ List.replicate n 0) := by
  induction n generalizing vals with
  | zero => simp [pad]
  | succ n ih =>
    simp only [pad, Tree.runFrom, TArg.eval, add_zero, ih, List.append_assoc]
    rfl

theorem depth_pad (n : ℕ) (T : Tree ι') : (pad n T).depth = T.depth + n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [pad, Tree.depth, ih]; omega

/-- The block of `11` real nodes simulating one complex operation, whose operands have real
parts `ar, br` and imaginary parts `ai, bi`; `p` is the number of real values computed before
the block. -/
def block (p : ℕ) (ar ai br bi : TArg ι') (N : Tree ι') : TOp → Tree ι'
  | .add => pad 9 (.comp .add ar br (.comp .add ai bi N))
  | .sub => pad 9 (.comp .sub ar br (.comp .sub ai bi N))
  | .mul => pad 5 (.comp .mul ar br (.comp .mul ai bi (.comp .mul ar bi (.comp .mul ai br
      (.comp .sub (.val (p + 5)) (.val (p + 6)) (.comp .add (.val (p + 7)) (.val (p + 8)) N))))))
  | .div => .comp .mul br br (.comp .mul bi bi (.comp .add (.val p) (.val (p + 1))
      (.comp .mul ar br (.comp .mul ai bi (.comp .mul ai br (.comp .mul ar bi
      (.comp .add (.val (p + 3)) (.val (p + 4)) (.comp .sub (.val (p + 5)) (.val (p + 6))
      (.comp .div (.val (p + 7)) (.val (p + 2)) (.comp .div (.val (p + 8)) (.val (p + 2))
        N))))))))))

theorem depth_block (p : ℕ) (ar ai br bi : TArg ι') (N : Tree ι') (op : TOp) :
    (block p ar ai br bi N op).depth = N.depth + 11 := by
  cases op <;> simp [block, Tree.depth, depth_pad]

/-- The real tree simulating a complex tree; `p` is the number of real values computed so
far. -/
def toReal (g : ι → TArg ι' × TArg ι') : CTree ι → ℕ → Tree ι'
  | .leaf b, _ => .leaf b
  | .comp op a b next, p =>
      block p (reArg g a) (imArg g a) (reArg g b) (imArg g b) (toReal g next (p + 11)) op
  | .test v yes no, p =>
      .test .eq (reArg g v) (.test .eq (imArg g v) (toReal g yes p) (toReal g no p))
        (toReal g no p)

theorem depth_toReal (g : ι → TArg ι' × TArg ι') (T : CTree ι) (p : ℕ) :
    (toReal g T p).depth ≤ 11 * T.depth := by
  induction T generalizing p with
  | leaf b => simp [toReal, Tree.depth, CTree.depth]
  | comp op a b next ih =>
    simp only [toReal, depth_block, CTree.depth]
    have := ih (p + 11)
    omega
  | test v yes no ih₁ ih₂ =>
    simp only [toReal, Tree.depth, CTree.depth]
    have h₁ := ih₁ p
    have h₂ := ih₂ p
    have : max yes.depth no.depth ≥ yes.depth := le_max_left _ _
    have : max yes.depth no.depth ≥ no.depth := le_max_right _ _
    omega

/-- The complex operation `op`. -/
def cop : TOp → ℂ → ℂ → ℂ
  | .add => (· + ·)
  | .sub => (· - ·)
  | .mul => (· * ·)
  | .div => (· / ·)

/-- The real values `rv` encode the complex values `cv`. -/
def Enc (rv : List ℝ) (cv : List ℂ) : Prop :=
  rv.length = 11 * cv.length ∧
    ∀ j < cv.length, rv.getD (11 * j + 9) 0 = (cv.getD j 0).re ∧
      rv.getD (11 * j + 10) 0 = (cv.getD j 0).im

theorem enc_nil : Enc [] [] := ⟨rfl, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩

theorem enc_append {rv : List ℝ} {cv : List ℂ} (h : Enc rv cv) (blk : List ℝ) (v : ℂ)
    (hl : blk.length = 11) (h9 : blk.getD 9 0 = v.re) (h10 : blk.getD 10 0 = v.im) :
    Enc (rv ++ blk) (cv ++ [v]) := by
  obtain ⟨hlen, hv⟩ := h
  refine ⟨by simp [hlen, hl]; ring, fun j hj => ?_⟩
  simp only [List.length_append, List.length_singleton] at hj
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
  · rw [List.getD_append rv blk 0 (11 * j + 9) (by omega),
      List.getD_append rv blk 0 (11 * j + 10) (by omega), List.getD_append cv [v] 0 j hj]
    exact hv j hj
  · rw [List.getD_append_right rv blk 0 (11 * cv.length + 9) (by omega),
      List.getD_append_right rv blk 0 (11 * cv.length + 10) (by omega),
      List.getD_append_right cv [v] 0 cv.length le_rfl]
    simp only [hlen, Nat.sub_self, List.getD_cons_zero]
    rw [show 11 * cv.length + 9 - 11 * cv.length = 9 by omega,
      show 11 * cv.length + 10 - 11 * cv.length = 10 by omega]
    exact ⟨h9, h10⟩

/-- The pair of operands `g i` holds the real and imaginary parts of the complex input. -/
def InpOK (g : ι → TArg ι' × TArg ι') (w : ι' → ℝ) (cw : ι → ℂ) : Prop :=
  ∀ i vs, (g i).1.eval w vs = (cw i).re ∧ (g i).2.eval w vs = (cw i).im

theorem eval_reArg {g : ι → TArg ι' × TArg ι'} {w : ι' → ℝ} {cw : ι → ℂ} (hg : InpOK g w cw)
    {rv : List ℝ} {cv : List ℂ} (h : Enc rv cv) (a : CArg ι) (ext : List ℝ)
    (hext : ext.length ≤ 9) : (reArg g a).eval w (rv ++ ext) = (argEval cw cv a).re := by
  cases a with
  | input i => exact (hg i _).1
  | const c => rfl
  | val j =>
    simp only [reArg, TArg.eval, argEval]
    have := h.1
    by_cases hj : j < cv.length
    · rw [List.getD_append _ _ _ _ (by omega)]
      exact (h.2 j hj).1
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
      simp

theorem eval_imArg {g : ι → TArg ι' × TArg ι'} {w : ι' → ℝ} {cw : ι → ℂ} (hg : InpOK g w cw)
    {rv : List ℝ} {cv : List ℂ} (h : Enc rv cv) (a : CArg ι) (ext : List ℝ)
    (hext : ext.length ≤ 10) : (imArg g a).eval w (rv ++ ext) = (argEval cw cv a).im := by
  cases a with
  | input i => exact (hg i _).2
  | const c => rfl
  | val j =>
    simp only [imArg, TArg.eval, argEval]
    have := h.1
    by_cases hj : j < cv.length
    · rw [List.getD_append _ _ _ _ (by omega)]
      exact (h.2 j hj).2
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
      simp

theorem eval_val_append (w : ι' → ℝ) (rv ext : List ℝ) (k : ℕ) :
    (TArg.val (rv.length + k) : TArg ι').eval w (rv ++ ext) = ext.getD k 0 := by
  simp only [TArg.eval]
  rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]

/-- **One complex operation.**  The block simulating it either divides by zero (exactly when
the complex operation does) or appends a block of `11` values encoding the result. -/
theorem runFrom_block (op : TOp) (ar ai br bi : TArg ι') (N : Tree ι') (w : ι' → ℝ)
    (rv : List ℝ) (x y : ℂ)
    (har : ∀ ext : List ℝ, ext.length ≤ 9 → ar.eval w (rv ++ ext) = x.re)
    (hbr : ∀ ext : List ℝ, ext.length ≤ 9 → br.eval w (rv ++ ext) = y.re)
    (hai : ∀ ext : List ℝ, ext.length ≤ 10 → ai.eval w (rv ++ ext) = x.im)
    (hbi : ∀ ext : List ℝ, ext.length ≤ 10 → bi.eval w (rv ++ ext) = y.im)
    (Q : Option Bool) (hQ0 : op = .div → y = 0 → Q = none)
    (hQ : (op = .div → y ≠ 0) → ∀ blk : List ℝ, blk.length = 11 →
      blk.getD 9 0 = (cop op x y).re → blk.getD 10 0 = (cop op x y).im →
      N.runFrom w (rv ++ blk) = Q) :
    (block rv.length ar ai br bi N op).runFrom w rv = Q := by
  cases op with
  | add =>
    simp only [block, runFrom_pad, Tree.runFrom, List.append_assoc, List.cons_append]
    rw [har _ (by simp), hbr _ (by simp), hai _ (by simp), hbi _ (by simp)]
    exact hQ (by simp) _ (by simp) (by simp [cop]) (by simp [cop])
  | sub =>
    simp only [block, runFrom_pad, Tree.runFrom, List.append_assoc, List.cons_append]
    rw [har _ (by simp), hbr _ (by simp), hai _ (by simp), hbi _ (by simp)]
    exact hQ (by simp) _ (by simp) (by simp [cop]) (by simp [cop])
  | mul =>
    simp only [block, runFrom_pad, Tree.runFrom, List.append_assoc, List.cons_append,
      eval_val_append]
    rw [har _ (by simp), hbr _ (by simp), hai _ (by simp), hbi _ (by simp), har _ (by simp),
      hbr _ (by simp), hai _ (by simp), hbi _ (by simp)]
    exact hQ (by simp) _ (by simp) (by simp [cop]) (by simp [cop])
  | div =>
    have hbr0 : br.eval w rv = y.re := by simpa using hbr [] (by simp)
    have hv0 : ∀ ext : List ℝ, (TArg.val rv.length : TArg ι').eval w (rv ++ ext) =
        ext.getD 0 0 := fun ext => by simpa using eval_val_append w rv ext 0
    simp (disch := simp) only [block, Tree.runFrom, List.append_assoc, List.cons_append,
      List.nil_append, eval_val_append, hv0, hbr0, har, hbr, hai, hbi,
      List.getD_cons_zero, List.getD_cons_succ]
    rw [← Complex.normSq_apply]
    by_cases hy : y = 0
    · rw [ite_eq_left (by simp [hy]), hQ0 rfl hy]
    · rw [ite_eq_right (by simpa using hy), ite_eq_right (by simpa using hy)]
      refine hQ (fun _ => hy) _ (by simp) ?_ ?_
      · simp [cop, Complex.div_re, add_div]
      · simp [cop, Complex.div_im, sub_div]

/-- **Simulation.**  The real tree `toReal g T` has the same outcome as the complex tree `T`,
when the real values encode the complex ones and the operands `g i` hold the real and
imaginary parts of the complex inputs. -/
theorem runFrom_toReal {g : ι → TArg ι' × TArg ι'} {w : ι' → ℝ} {cw : ι → ℂ}
    (hg : InpOK g w cw) (T : CTree ι) :
    ∀ (rv : List ℝ) (cv : List ℂ), Enc rv cv →
      (toReal g T rv.length).runFrom w rv = T.runFrom cw cv := by
  induction T with
  | leaf b => intro rv cv _; rfl
  | comp op a b next ih =>
    intro rv cv h
    simp only [toReal]
    apply runFrom_block op _ _ _ _ _ w rv (argEval cw cv a) (argEval cw cv b)
      (fun ext he => eval_reArg hg h a ext he) (fun ext he => eval_reArg hg h b ext he)
      (fun ext he => eval_imArg hg h a ext he) (fun ext he => eval_imArg hg h b ext he)
    · intro hop hy
      subst hop
      simp [CTree.runFrom, hy]
    · intro hne blk hl h9 h10
      have := ih (rv ++ blk) (cv ++ [cop op (argEval cw cv a) (argEval cw cv b)])
        (enc_append h blk _ hl h9 h10)
      rw [List.length_append, hl] at this
      rw [this]
      cases op with
      | add => rfl
      | sub => rfl
      | mul => rfl
      | div =>
        simp only [CTree.runFrom]
        rw [ite_eq_right (hne rfl)]
        rfl
  | test v yes no ih₁ ih₂ =>
    intro rv cv h
    have hre : (reArg g v).eval w rv = (argEval cw cv v).re := by
      simpa using eval_reArg hg h v [] (by simp)
    have him : (imArg g v).eval w rv = (argEval cw cv v).im := by
      simpa using eval_imArg hg h v [] (by simp)
    simp only [toReal, Tree.runFrom, TestKind.holds, hre, him, CTree.runFrom, ih₁ rv cv h,
      ih₂ rv cv h]
    by_cases h0 : argEval cw cv v = 0
    · simp [h0]
    · rw [ite_eq_right h0]
      by_cases h1 : (argEval cw cv v).re = 0
      · rw [ite_eq_left h1, ite_eq_right]
        intro h2
        exact h0 (Complex.ext h1 h2)
      · rw [ite_eq_right h1]

theorem run_toReal {g : ι → TArg ι' × TArg ι'} {w : ι' → ℝ} {cw : ι → ℂ}
    (hg : InpOK g w cw) (T : CTree ι) : (toReal g T 0).run w = T.runFrom cw [] :=
  runFrom_toReal hg T [] [] enc_nil

end CTree

theorem eval_map_ofReal {σ : Type} (f : MvPolynomial σ ℝ) (x : σ → ℝ) :
    eval (fun i => (x i : ℂ)) (map (algebraMap ℝ ℂ) f) = (eval x f : ℂ) := by
  have := eval₂_comp (algebraMap ℝ ℂ) x f
  rw [eval_map]
  simpa [Function.comp_def] using this.symm

/-- The complex certificate with real parts `z' (inl j)` and imaginary parts `z' (inr j)`. -/
def zOf {k : ℕ} (z' : Fin (k + k) → ℝ) (j : Fin k) : ℂ :=
  ⟨z' (finSumFinEquiv (Sum.inl j)), z' (finSumFinEquiv (Sum.inr j))⟩

/-- The real certificate of a complex certificate. -/
def zRe {k : ℕ} (z : Fin k → ℂ) (m : Fin (k + k)) : ℝ :=
  Sum.elim (fun j => (z j).re) (fun j => (z j).im) (finSumFinEquiv.symm m)

theorem zOf_zRe {k : ℕ} (z : Fin k → ℂ) : zOf (zRe z) = z := by
  funext j
  simp only [zOf, zRe, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]

/-- The operands of the real tree on `(x, y, z') ∈ ℝⁿ × ℝ × ℝ^{2k}` holding the real and
imaginary parts of the complex input `(x, y, z)`: the imaginary parts of `x` and `y` are `0`. -/
def gOne (σ : Type) (k : ℕ) :
    σ ⊕ Unit ⊕ Fin k → TArg (σ ⊕ Unit ⊕ Fin (k + k)) × TArg (σ ⊕ Unit ⊕ Fin (k + k))
  | .inl i => (.input (.inl i), .const 0)
  | .inr (.inl u) => (.input (.inr (.inl u)), .const 0)
  | .inr (.inr j) => (.input (.inr (.inr (finSumFinEquiv (.inl j)))),
      .input (.inr (.inr (finSumFinEquiv (.inr j)))))

theorem inpOK_gOne {σ : Type} {k : ℕ} (x : σ → ℝ) (y : ℝ) (z' : Fin (k + k) → ℝ) :
    CTree.InpOK (gOne σ k) (inp3 x y z') (cinp3 (fun i => (x i : ℂ)) (y : ℂ) (zOf z')) := by
  intro i vs
  rcases i with i | u | j
  · simp [gOne, TArg.eval, inp3, cinp3]
  · simp [gOne, TArg.eval, inp3, cinp3]
  · simp [gOne, TArg.eval, inp3, cinp3, zOf]

/-- The operands of the real tree on `(x, y, z') ∈ ℝⁿ × ℝ² × ℝ^{2k}`: both parts of `y` are
inputs. -/
def gTwo (σ : Type) (k : ℕ) :
    σ ⊕ Unit ⊕ Fin k → TArg (σ ⊕ Fin 2 ⊕ Fin (k + k)) × TArg (σ ⊕ Fin 2 ⊕ Fin (k + k))
  | .inl i => (.input (.inl i), .const 0)
  | .inr (.inl _) => (.input (.inr (.inl 0)), .input (.inr (.inl 1)))
  | .inr (.inr j) => (.input (.inr (.inr (finSumFinEquiv (.inl j)))),
      .input (.inr (.inr (finSumFinEquiv (.inr j)))))

theorem inpOK_gTwo {σ : Type} {k : ℕ} (x : σ → ℝ) (y : Fin 2 → ℝ) (z' : Fin (k + k) → ℝ) :
    CTree.InpOK (gTwo σ k) (Sum.elim x (Sum.elim y z'))
      (cinp3 (fun i => (x i : ℂ)) ⟨y 0, y 1⟩ (zOf z')) := by
  intro i vs
  rcases i with i | u | j
  · simp [gTwo, TArg.eval, cinp3]
  · simp [gTwo, TArg.eval, cinp3]
  · simp [gTwo, TArg.eval, cinp3, zOf]

section RealTrees

variable {σ : Type} {k : ℕ}

theorem accepts_toReal_gOne (T : CTree (σ ⊕ Unit ⊕ Fin k)) (x : σ → ℝ) (y : ℝ)
    (z' : Fin (k + k) → ℝ) :
    (CTree.toReal (gOne σ k) T 0).Accepts (inp3 x y z') ↔
      T.Accepts (cinp3 (fun i => (x i : ℂ)) (y : ℂ) (zOf z')) := by
  rw [Tree.Accepts, CTree.run_toReal (inpOK_gOne x y z')]
  rfl

theorem exists_toReal_gOne (T : CTree (σ ⊕ Unit ⊕ Fin k)) (x : σ → ℝ) (y : ℝ) :
    (∃ z', (CTree.toReal (gOne σ k) T 0).Accepts (inp3 x y z')) ↔
      ∃ z, T.Accepts (cinp3 (fun i => (x i : ℂ)) (y : ℂ) z) := by
  constructor
  · rintro ⟨z', h⟩
    exact ⟨zOf z', (accepts_toReal_gOne T x y z').1 h⟩
  · rintro ⟨z, h⟩
    refine ⟨zRe z, (accepts_toReal_gOne T x y _).2 ?_⟩
    rwa [zOf_zRe]

theorem forall_toReal_gOne (T : CTree (σ ⊕ Unit ⊕ Fin k)) (x : σ → ℝ) (y : ℝ) :
    (∀ z', (CTree.toReal (gOne σ k) T 0).Accepts (inp3 x y z')) ↔
      ∀ z, T.Accepts (cinp3 (fun i => (x i : ℂ)) (y : ℂ) z) := by
  constructor
  · intro h z
    have := (accepts_toReal_gOne T x y (zRe z)).1 (h _)
    rwa [zOf_zRe] at this
  · intro h z'
    exact (accepts_toReal_gOne T x y z').2 (h _)

theorem exists_toReal_gTwo (T : CTree (σ ⊕ Unit ⊕ Fin k)) (x : σ → ℝ) (y : Fin 2 → ℝ) :
    (∃ z', (CTree.toReal (gTwo σ k) T 0).Accepts (Sum.elim x (Sum.elim y z'))) ↔
      ∃ z, T.Accepts (cinp3 (fun i => (x i : ℂ)) ⟨y 0, y 1⟩ z) := by
  have key : ∀ z', (CTree.toReal (gTwo σ k) T 0).Accepts (Sum.elim x (Sum.elim y z')) ↔
      T.Accepts (cinp3 (fun i => (x i : ℂ)) ⟨y 0, y 1⟩ (zOf z')) := fun z' => by
    rw [Tree.Accepts, CTree.run_toReal (inpOK_gTwo x y z')]
    rfl
  constructor
  · rintro ⟨z', h⟩
    exact ⟨zOf z', (key z').1 h⟩
  · rintro ⟨z, h⟩
    refine ⟨zRe z, (key _).2 ?_⟩
    rwa [zOf_zRe]

end RealTrees

theorem complex_borderLE_mono {σ : Type} {f : MvPolynomial σ ℝ} {s s' : ℕ} (h : BorderLE f s)
    (hss : s ≤ s') : BorderLE f s' := by
  obtain ⟨Γ, c, hΓ, P, hP, hPf⟩ := h
  exact ⟨Γ, c, hΓ.trans hss, P, hP, hPf⟩

theorem complex_bound_a (D t n m : ℕ) (hD : 1 ≤ D) (hm : m ≤ 22 * t) :
    D ^ 3 * (11 * t) + D ^ 2 * (m + 2) ^ 2 + n ≤ 500 * (D ^ 6 * ((t + 1) ^ 2 + n)) := by
  have h3 : D ^ 3 ≤ D ^ 6 := pow_le_pow_right₀ hD (by norm_num)
  have h2 : D ^ 2 ≤ D ^ 6 := pow_le_pow_right₀ hD (by norm_num)
  have h1 : 1 ≤ D ^ 6 := one_le_pow₀ hD
  have hm2 : (m + 2) ^ 2 ≤ 484 * (t + 1) ^ 2 := by
    calc (m + 2) ^ 2 ≤ (22 * (t + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ = 484 * (t + 1) ^ 2 := by ring
  have e1 : D ^ 3 * (11 * t) ≤ 11 * (D ^ 6 * (t + 1) ^ 2) := by
    calc D ^ 3 * (11 * t) ≤ D ^ 6 * (11 * (t + 1) ^ 2) :=
          Nat.mul_le_mul h3 (by nlinarith)
      _ = 11 * (D ^ 6 * (t + 1) ^ 2) := by ring
  have e2 : D ^ 2 * (m + 2) ^ 2 ≤ 484 * (D ^ 6 * (t + 1) ^ 2) := by
    calc D ^ 2 * (m + 2) ^ 2 ≤ D ^ 6 * (484 * (t + 1) ^ 2) := Nat.mul_le_mul h2 hm2
      _ = 484 * (D ^ 6 * (t + 1) ^ 2) := by ring
  have e3 : n ≤ D ^ 6 * n := Nat.le_mul_of_pos_left n (by omega)
  have : 500 * (D ^ 6 * ((t + 1) ^ 2 + n)) = 500 * (D ^ 6 * (t + 1) ^ 2) + 500 * (D ^ 6 * n) := by
    ring
  omega

theorem complex_bound_b (D t n : ℕ) :
    D ^ 6 * ((11 * t + 1) ^ 2 + n) ≤ 121 * (D ^ 6 * ((t + 1) ^ 2 + n)) := by
  have h : (11 * t + 1) ^ 2 ≤ 121 * (t + 1) ^ 2 := by
    calc (11 * t + 1) ^ 2 ≤ (11 * (t + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ = 121 * (t + 1) ^ 2 := by ring
  have : (11 * t + 1) ^ 2 + n ≤ 121 * ((t + 1) ^ 2 + n) := by omega
  calc D ^ 6 * ((11 * t + 1) ^ 2 + n) ≤ D ^ 6 * (121 * ((t + 1) ^ 2 + n)) :=
        Nat.mul_le_mul_left _ this
    _ = 121 * (D ^ 6 * ((t + 1) ^ 2 + n)) := by ring

theorem complex_bound_coeff (D t n m : ℕ) (hm : m ≤ 22 * t) :
    D ^ 3 * (11 * t) + D ^ 2 * (m + 2 + 1) ^ 2 + n ≤
      625 * (D ^ 3 * (t + 1) + D ^ 2 * (t + 1) ^ 2 + n) := by
  have hm2 : (m + 2 + 1) ^ 2 ≤ 625 * (t + 1) ^ 2 := by
    calc (m + 2 + 1) ^ 2 ≤ (25 * (t + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ = 625 * (t + 1) ^ 2 := by ring
  have e1 : D ^ 3 * (11 * t) ≤ 11 * (D ^ 3 * (t + 1)) := by
    calc D ^ 3 * (11 * t) ≤ D ^ 3 * (11 * (t + 1)) := Nat.mul_le_mul_left _ (by omega)
      _ = 11 * (D ^ 3 * (t + 1)) := by ring
  have e2 : D ^ 2 * (m + 2 + 1) ^ 2 ≤ 625 * (D ^ 2 * (t + 1) ^ 2) := by
    calc D ^ 2 * (m + 2 + 1) ^ 2 ≤ D ^ 2 * (625 * (t + 1) ^ 2) := Nat.mul_le_mul_left _ hm2
      _ = 625 * (D ^ 2 * (t + 1) ^ 2) := by ring
  omega

/-- **Theorem 5.3 (complex field).** -/
theorem complex_field (hS : SAFacts) :
    ∃ C : ℕ, ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (d t k : ℕ) (f : MvPolynomial σ ℝ),
      1 ≤ d → f.totalDegree ≤ d →
      ∀ T : CTree (σ ⊕ Unit ⊕ Fin k), T.depth ≤ t →
      ((∀ (x : σ → ℂ) (y : ℂ), (∃ z, T.Accepts (cinp3 x y z)) ↔
          y = eval x (map (algebraMap ℝ ℂ) f)) ∨
        (∀ (x : σ → ℂ) (y : ℂ), (∀ z, T.Accepts (cinp3 x y z)) ↔
          y = eval x (map (algebraMap ℝ ℂ) f))) →
      BorderLE f (C * (d + 1) ^ 6 * ((t + 1) ^ 2 + Fintype.card σ)) := by
  obtain ⟨Cg, hCg⟩ := graph_theorem hS
  obtain ⟨Co, hCo⟩ := onesided hS
  refine ⟨500 * Cg + 121 * Co, ?_⟩
  intro σ _ _ d t k f hd hf T hT hcase
  set T' := CTree.toReal (gOne σ k) T 0 with hT'def
  have hT' : T'.depth ≤ 11 * t := (CTree.depth_toReal _ T 0).trans (by omega)
  have hval : ∀ (x : σ → ℝ) (y : ℝ),
      (y : ℂ) = eval (fun i => (x i : ℂ)) (map (algebraMap ℝ ℂ) f) ↔ y = eval x f := by
    intro x y
    rw [eval_map_ofReal]
    exact Complex.ofReal_inj
  rcases hcase with ha | hb
  · have h := hCg d (11 * t) (k + k) f hd hf univ isOpen_univ univ_nonempty T' hT'
      (fun x _ y => by rw [hT'def, exists_toReal_gOne, ha, hval])
    refine complex_borderLE_mono h ?_
    have hb := complex_bound_a (d + 1) t (Fintype.card σ) (min (k + k) (2 * (11 * t)))
      (by omega) (min_le_right _ _ |>.trans (by omega))
    calc Cg * ((d + 1) ^ 3 * (11 * t) + (d + 1) ^ 2 * (min (k + k) (2 * (11 * t)) + 2) ^ 2 +
          Fintype.card σ)
        ≤ Cg * (500 * ((d + 1) ^ 6 * ((t + 1) ^ 2 + Fintype.card σ))) :=
          Nat.mul_le_mul_left _ hb
      _ ≤ (500 * Cg + 121 * Co) * (d + 1) ^ 6 * ((t + 1) ^ 2 + Fintype.card σ) := by
          nlinarith [Nat.zero_le (Co * (d + 1) ^ 6 * ((t + 1) ^ 2 + Fintype.card σ))]
  · have h := hCo d (11 * t) (k + k) f hd hf univ isOpen_univ univ_nonempty T' rejecting hT'
      ?_ ?_
    · refine complex_borderLE_mono h ?_
      have hb := complex_bound_b (d + 1) t (Fintype.card σ)
      calc Co * (d + 1) ^ 6 * ((11 * t + 1) ^ 2 + Fintype.card σ)
          = Co * ((d + 1) ^ 6 * ((11 * t + 1) ^ 2 + Fintype.card σ)) := by ring
        _ ≤ Co * (121 * ((d + 1) ^ 6 * ((t + 1) ^ 2 + Fintype.card σ))) :=
          Nat.mul_le_mul_left _ hb
        _ ≤ (500 * Cg + 121 * Co) * (d + 1) ^ 6 * ((t + 1) ^ 2 + Fintype.card σ) := by
          nlinarith [Nat.zero_le (Cg * (d + 1) ^ 6 * ((t + 1) ^ 2 + Fintype.card σ))]
    · intro x _ z'
      have hacc : T'.Accepts (inp3 x (eval x f) z') :=
        (forall_toReal_gOne T x (eval x f)).2 ((hb _ _).2 ((hval x _).2 rfl)) z'
      rw [Tree.Accepts] at hacc
      rw [hacc]
      simp [rejecting]
    · intro x _
      refine ⟨1, one_pos, fun y hy _ => ?_⟩
      have hne : ¬ ∀ z', T'.Accepts (inp3 x y z') := by
        rw [hT'def, forall_toReal_gOne, hb, hval]
        exact hy.ne'
      obtain ⟨z', hz'⟩ := not_forall.mp hne
      refine ⟨z', ?_⟩
      rw [Tree.Accepts] at hz'
      revert hz'
      rcases T'.run (inp3 x y z') with _ | _ | _ <;> simp [rejecting]

/-- **Remark 5.4 (complex coefficients)**, case (a): for `f = f₁ + i f₂` with complex
coefficients, a complex tree deciding the graph of `f` in the existential sense bounds the
border complexity of `f₁` and of `f₂` (via Remark 4.3 with `μ = 2`). -/
theorem complex_coeff (hS : SAFacts) :
    ∃ C : ℕ, ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (d t k : ℕ) (f₁ f₂ : MvPolynomial σ ℝ),
      1 ≤ d → f₁.totalDegree ≤ d → f₂.totalDegree ≤ d →
      ∀ T : CTree (σ ⊕ Unit ⊕ Fin k), T.depth ≤ t →
      (∀ (x : σ → ℂ) (y : ℂ), (∃ z, T.Accepts (cinp3 x y z)) ↔
          y = eval x (map (algebraMap ℝ ℂ) f₁) + Complex.I * eval x (map (algebraMap ℝ ℂ) f₂)) →
      BorderLE f₁ (C * ((d + 1) ^ 3 * (t + 1) + (d + 1) ^ 2 * (t + 1) ^ 2 + Fintype.card σ)) ∧
      BorderLE f₂ (C * ((d + 1) ^ 3 * (t + 1) + (d + 1) ^ 2 * (t + 1) ^ 2 + Fintype.card σ)) := by
  obtain ⟨Cv, hCv⟩ := graph_theorem_vec hS
  refine ⟨625 * Cv, ?_⟩
  intro σ _ _ d t k f₁ f₂ hd hf₁ hf₂ T hT hcase
  set T' := CTree.toReal (gTwo σ k) T 0 with hT'def
  have hT' : T'.depth ≤ 11 * t := (CTree.depth_toReal _ T 0).trans (by omega)
  have hdeg : ∀ i, (![f₁, f₂] i).totalDegree ≤ d := by
    intro i
    fin_cases i
    · exact hf₁
    · exact hf₂
  have hgraph : ∀ x ∈ (univ : Set (σ → ℝ)), ∀ y : Fin 2 → ℝ,
      (∃ z, T'.Accepts (Sum.elim x (Sum.elim y z))) ↔ y = fun i => eval x (![f₁, f₂] i) := by
    intro x _ y
    rw [hT'def, exists_toReal_gTwo, hcase, eval_map_ofReal, eval_map_ofReal, Complex.ext_iff]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, zero_mul,
      Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, add_zero, Complex.add_im,
      Complex.mul_im, one_mul, zero_add]
    constructor
    · rintro ⟨h0, h1⟩
      funext i
      fin_cases i
      · exact h0
      · exact h1
    · intro h
      exact ⟨congrFun h 0, congrFun h 1⟩
  have h := hCv 2 d (11 * t) (k + k) ![f₁, f₂] hd hdeg univ isOpen_univ univ_nonempty T' hT'
    hgraph
  have hb := complex_bound_coeff (d + 1) t (Fintype.card σ) (min (k + k) (2 * (11 * t)))
    (min_le_right _ _ |>.trans (by omega))
  have hle : Cv * ((d + 1) ^ 3 * (11 * t) + (d + 1) ^ 2 * (min (k + k) (2 * (11 * t)) + 2 + 1) ^ 2 +
      Fintype.card σ) ≤
      625 * Cv * ((d + 1) ^ 3 * (t + 1) + (d + 1) ^ 2 * (t + 1) ^ 2 + Fintype.card σ) := by
    calc _ ≤ Cv * (625 * ((d + 1) ^ 3 * (t + 1) + (d + 1) ^ 2 * (t + 1) ^ 2 +
          Fintype.card σ)) := Nat.mul_le_mul_left _ hb
      _ = _ := by ring
  exact ⟨complex_borderLE_mono (h 0) hle, complex_borderLE_mono (h 1) hle⟩

end ClassSep
