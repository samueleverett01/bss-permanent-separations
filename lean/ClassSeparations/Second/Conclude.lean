import ClassSeparations.Second.Continuity
import ClassSeparations.Second.Tilt
import ClassSeparations.Second.EnvValue
import ClassSeparations.Core.Derivatives
import ClassSeparations.Core.Newton
import ClassSeparations.Core.Closure
import ClassSeparations.Core.BaurStrassen

/-!
# Part 2 of the proof of Theorem 6.1 (§6.5–6.6): the assembly

Fix `â, V, ϑ₁` as in Lemma 6.7.  For `x ∈ V` and `ϑ > 0` the minimizers of
`e(x; c) - ϑ⟨â, c⟩` over `B̄` converge to `φ(x)` uniformly as `ϑ → 0` (Lemma 6.5), lie in the
interior of `B̄` for small `ϑ` and satisfy `∇_c e = ϑ â`.  A semialgebraic choice `Θ` of
minimizers (S2) is `C^d` on a smaller ball with `x`-derivatives converging to those of `φ`
(Corollary 3.2).  At `ξ₁ = (x₁, Θ(x₁, ϑ))` the envelope is analytic with invertible Hessian in
`c` (Lemma 6.7); with `P` the Taylor polynomial of order `d + 1` of `e` at `ξ₁`, Newton
iteration (Lemma 3.4) for `E = ∇_c P - ϑ â` reproduces the Taylor polynomial of order `d` of
`Θ(·, ϑ)` at `x₁`.  Replacing `P` by outputs of the graphs of Lemma 6.6 (via Baur–Strassen)
and using continuity of Newton iteration in the coefficients, and finally Lemma 3.3, gives the
bound.
-/

noncomputable section

set_option linter.unusedSectionVars false

open MvPolynomial Set Filter Topology

namespace ClassSep

namespace SecondAux

/-! ### Newton iteration for an approximate solution -/

section NewtonVariant

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- **Lemma 3.4 (b)**, in the form used in §6.6: if a polynomial map `τ` of degree `≤ D` with
`τ(ξ₁) = w₁` solves `E(ξ, τ(ξ)) = 0` up to `o(|ξ - ξ₁|^D)`, and `A` inverts `∂_w E(ξ₁, w₁)`,
then Newton iteration returns `τ`. -/
theorem newtonPoly_eq_of_isLittleO (E : κ → MvPolynomial (ι ⊕ κ) ℝ) (ξ₁ : ι → ℝ)
    (w₁ : κ → ℝ) (A : Matrix κ κ ℝ) (D : ℕ) (hA : A * jacW E (Sum.elim ξ₁ w₁) = 1)
    (τ : κ → MvPolynomial ι ℝ) (hτ : ∀ k, (τ k).totalDegree ≤ D)
    (hτ0 : ∀ k, eval ξ₁ (τ k) = w₁ k)
    (hF : ∀ l, (fun ξ => eval (Sum.elim ξ (fun k => eval ξ (τ k))) (E l)) =o[𝓝 ξ₁]
      (fun ξ => ‖ξ - ξ₁‖ ^ D)) (k : κ) :
    newtonPoly E ξ₁ w₁ A D k = τ k := by
  set T : κ → MvPolynomial ι ℝ :=
    fun k => bind₁ (fun i => X i + MvPolynomial.C (ξ₁ i)) (τ k) with hTdef
  have hT : ∀ k, (T k).totalDegree ≤ D := fun k =>
    (totalDegree_bind₁_le _ (fun i => totalDegree_X_add_C_le i _) _).trans (hτ k)
  have hevalT : ∀ k χ, eval χ (T k) = eval (fun i => χ i + ξ₁ i) (τ k) := by
    intro k χ
    simp only [T]
    rw [eval_bind₁_nt]
    simp
  have hT0 : ∀ k, (T k).coeff 0 = w₁ k := fun k => by
    rw [coeff_zero_eq_eval_zero', hevalT]
    simpa using hτ0 k
  have hET : ∀ l, HighOrd (D + 1)
      (bind₁ (Sum.elim (fun i => MvPolynomial.C (ξ₁ i) + X i) T) (E l)) := by
    intro l
    apply highOrd_of_isLittleO
    have hT' : Tendsto (fun χ : ι → ℝ => ξ₁ + χ) (𝓝 0) (𝓝 ξ₁) := by
      simpa using (tendsto_const_nhds (x := ξ₁)).add (tendsto_id (x := 𝓝 (0 : ι → ℝ)))
    refine ((hF l).comp_tendsto hT').congr (fun χ => ?_) (fun χ => by simp)
    simp only [Function.comp_apply, eval_bind₁_nt]
    have hpt : (fun v => eval χ (Sum.elim (fun i => MvPolynomial.C (ξ₁ i) + X i) T v)) =
        Sum.elim (ξ₁ + χ) (fun k => eval (ξ₁ + χ) (τ k)) := by
      funext v
      cases v with
      | inl i => simp
      | inr k =>
        simp only [Sum.elim_inr, hevalT]
        rw [show (fun i => χ i + ξ₁ i) = ξ₁ + χ from funext fun i => by simp [add_comm]]
    rw [hpt]
  have hiter : ∀ n ≤ D, ∀ k, HighOrd (n + 1)
      ((newtonStep E ξ₁ A D)^[n] (fun l => MvPolynomial.C (w₁ l)) k - T k) := by
    intro n
    induction n with
    | zero =>
      intro _ k
      refine HighOrd.one_of_coeff_zero ?_
      simp [hT0]
    | succ n ih =>
      intro hn k
      rw [Function.iterate_succ_apply']
      exact newtonStep_highOrd E ξ₁ w₁ A D hA T hT hT0 hET (by omega) _ (ih (by omega)) k
  have hfin : (newtonStep E ξ₁ A D)^[D] (fun l => MvPolynomial.C (w₁ l)) k = T k := by
    have := (hiter D le_rfl k).eq_zero ((totalDegree_sub _ _).trans
      (max_le (totalDegree_iterate_newtonStep_le E ξ₁ w₁ A D D k) (hT k)))
    exact sub_eq_zero.1 this
  unfold newtonPoly
  rw [hfin]
  simp only [T, bind₁_bind₁]
  have : (fun i => bind₁ (fun i => X i - MvPolynomial.C (ξ₁ i))
      (X i + MvPolynomial.C (ξ₁ i) : MvPolynomial ι ℝ)) = X := funext fun i => by simp
  rw [this, bind₁_X_left]
  rfl

end NewtonVariant

/-! ### Taylor polynomials and partial derivatives -/

section TaylorDeriv

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The derivative of a polynomial function. -/
def polyDeriv (p : MvPolynomial ι ℝ) (x : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ j, eval x (pderiv j p) • ContinuousLinearMap.proj j

theorem polyDeriv_apply (p : MvPolynomial ι ℝ) (x v : ι → ℝ) :
    polyDeriv p x v = ∑ j, eval x (pderiv j p) * v j := by
  simp [polyDeriv]

theorem hasFDerivAt_eval (p : MvPolynomial ι ℝ) (x : ι → ℝ) :
    HasFDerivAt (fun y => eval y p) (polyDeriv p x) x := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have : polyDeriv (MvPolynomial.C a : MvPolynomial ι ℝ) x = 0 := by
      ext v; simp [polyDeriv_apply]
    rw [this, show (fun y => eval y (MvPolynomial.C a : MvPolynomial ι ℝ)) = fun _ => a from
      funext fun y => eval_C a]
    exact hasFDerivAt_const a x
  | add p q hp hq =>
    have : polyDeriv (p + q) x = polyDeriv p x + polyDeriv q x := by
      ext v; simp [polyDeriv_apply, add_mul, Finset.sum_add_distrib]
    rw [this, show (fun y => eval y (p + q)) = fun y => eval y p + eval y q from
      funext fun y => map_add _ _ _]
    exact hp.add hq
  | mul_X p j hp =>
    have h := hp.mul (hasFDerivAt_apply j x)
    have hδ : ∀ v : ι → ℝ,
        ∑ k, eval x (Pi.single (M := fun _ => MvPolynomial ι ℝ) k 1 j) * v k = v j := by
      intro v
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hk; simp [Ne.symm hk]
      · simp
    have : polyDeriv (p * X j) x =
        eval x p • ContinuousLinearMap.proj j + x j • polyDeriv p x := by
      ext v
      simp only [polyDeriv_apply, Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, map_mul,
        eval_X, add_mul, Finset.sum_add_distrib, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply]
      congr 1
      · rw [← hδ v, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
    rw [this, show (fun y => eval y (p * X j)) = fun y => eval y p * y j from
      funext fun y => by simp]
    exact h

theorem eval_pderiv (p : MvPolynomial ι ℝ) (x : ι → ℝ) (i : ι) :
    eval x (pderiv i p) = fderiv ℝ (fun y => eval y p) x (Pi.single i 1) := by
  rw [(hasFDerivAt_eval p x).fderiv, polyDeriv_apply]
  simp [Pi.single_apply]

/-- The derivative of `y ↦ L(y - ξ₁, …, y - ξ₁)`. -/
theorem hasFDerivAt_jet {j : ℕ} (L : ContinuousMultilinearMap ℝ (fun _ : Fin j => ι → ℝ) ℝ)
    (ξ₁ x : ι → ℝ) :
    HasFDerivAt (fun y => L (fun _ => y - ξ₁))
      ((L.linearDeriv (fun _ => x - ξ₁)).comp
        (ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℝ (ι → ℝ))) x := by
  set A : (ι → ℝ) →L[ℝ] (Fin j → ι → ℝ) :=
    ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℝ (ι → ℝ) with hA
  have hA' : HasFDerivAt (fun y : ι → ℝ => (fun _ : Fin j => y - ξ₁)) A x := by
    have := (A.hasFDerivAt (x := x)).sub_const (fun _ : Fin j => ξ₁)
    convert this using 1
    funext y k
    simp [hA]
  exact (L.hasFDerivAt (fun _ => x - ξ₁)).comp x hA'

/-- Symmetry of the iterated derivative of an analytic function, in the form needed to
differentiate a Taylor term. -/
theorem sum_update_iteratedFDeriv {g : (ι → ℝ) → ℝ} {ξ₁ : ι → ℝ} (hg : AnalyticAt ℝ g ξ₁)
    (j : ℕ) (h v : ι → ℝ) :
    ∑ m : Fin (j + 1), iteratedFDeriv ℝ (j + 1) g ξ₁ (Function.update (fun _ => h) m v) =
      (j + 1) * iteratedFDeriv ℝ j (fun y => fderiv ℝ g y v) ξ₁ (fun _ => h) := by
  have hsym : ∀ m : Fin (j + 1), iteratedFDeriv ℝ (j + 1) g ξ₁
      (Function.update (fun _ => h) m v) =
      iteratedFDeriv ℝ (j + 1) g ξ₁ (Function.update (fun _ => h) (Fin.last j) v) := by
    intro m
    have := (hg.contDiffAt (n := ⊤)).iteratedFDeriv_comp_perm
      (Function.update (fun _ => h) (Fin.last j) v) (Equiv.swap m (Fin.last j))
    rw [← this]
    congr 1
    funext k
    simp only [Function.comp_apply, Function.update_apply, Equiv.swap_apply_def]
    by_cases hk : k = m
    · subst hk; simp
    · by_cases hkl : k = Fin.last j
      · subst hkl; simp [hk, Ne.symm hk]
      · simp [hk, hkl]
  have hsnoc : Function.update (fun _ : Fin (j + 1) => h) (Fin.last j) v =
      Fin.snoc (fun _ : Fin j => h) v := by
    funext k
    refine Fin.lastCases ?_ (fun k => ?_) k
    · simp
    · rw [Function.update_of_ne (Fin.castSucc_ne_last k), Fin.snoc_castSucc]
  simp_rw [hsym]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsnoc,
    iteratedFDeriv_succ_apply_right, Fin.init_snoc, Fin.snoc_last]
  push_cast
  congr 1
  have hc : ContDiffAt ℝ (⊤ : WithTop ℕ∞) (fderiv ℝ g) ξ₁ := hg.fderiv.contDiffAt
  have := (ContinuousLinearMap.apply ℝ ℝ v).iteratedFDeriv_comp_left hc (i := j) le_top
  have e : (fun y => fderiv ℝ g y v) = (ContinuousLinearMap.apply ℝ ℝ v) ∘ fderiv ℝ g := rfl
  rw [e, this]
  rfl

/-- The partial derivative of the Taylor polynomial of order `D + 1` of an analytic function is
the Taylor polynomial of order `D` of its partial derivative. -/
theorem pderiv_taylorPoly {g : (ι → ℝ) → ℝ} {ξ₁ : ι → ℝ} (hg : AnalyticAt ℝ g ξ₁) (D : ℕ)
    (i : ι) : pderiv i (taylorPoly (D + 1) g ξ₁) = taylorPoly D (pd g i) ξ₁ := by
  apply MvPolynomial.funext
  intro x
  rw [eval_pderiv, eval_taylorPoly]
  have hfun : (fun y => eval y (taylorPoly (D + 1) g ξ₁)) = fun y =>
      ∑ j ∈ Finset.range (D + 2), (j.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ j g ξ₁ (fun _ => y - ξ₁) := by
    funext y; rw [eval_taylorPoly]; simp [taylorSum, smul_eq_mul]
  rw [hfun]
  have hd : HasFDerivAt (fun y => ∑ j ∈ Finset.range (D + 2), (j.factorial : ℝ)⁻¹ *
      iteratedFDeriv ℝ j g ξ₁ (fun _ => y - ξ₁))
      (∑ j ∈ Finset.range (D + 2), (j.factorial : ℝ)⁻¹ •
        ((iteratedFDeriv ℝ j g ξ₁).linearDeriv (fun _ => x - ξ₁)).comp
          (ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℝ (ι → ℝ))) x :=
    HasFDerivAt.fun_sum fun j _ => (hasFDerivAt_jet (iteratedFDeriv ℝ j g ξ₁) ξ₁ x).const_mul _
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousMultilinearMap.linearDeriv_apply,
    ContinuousLinearMap.pi_apply, ContinuousLinearMap.coe_id', id_eq, smul_eq_mul]
  rw [Finset.sum_range_succ']
  simp only [Finset.univ_eq_empty, Finset.sum_empty, mul_zero, add_zero]
  unfold taylorSum
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sum_update_iteratedFDeriv hg j, smul_eq_mul, Nat.factorial_succ]
  have hj : ((j : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  rfl

/-- The coefficients of the Taylor polynomials of an analytic function depend continuously on
the base point. -/
theorem tendsto_coeff_taylorPoly_base {g : (ι → ℝ) → ℝ} {ξ₁ : ι → ℝ} (hg : AnalyticAt ℝ g ξ₁)
    (D : ℕ) (m : ι →₀ ℕ) :
    Tendsto (fun ξ => (taylorPoly D g ξ).coeff m) (𝓝 ξ₁) (𝓝 ((taylorPoly D g ξ₁).coeff m)) := by
  have key : ∀ ξ, (taylorPoly D g ξ).coeff m =
      ∑ j ∈ Finset.range (D + 1), (j.factorial : ℝ)⁻¹ *
        ∑ i : Fin j → ι, iteratedFDeriv ℝ j g ξ (fun k => Pi.single (i k) 1) *
          (∏ k : Fin j, (X (i k) - MvPolynomial.C (ξ (i k))) : MvPolynomial ι ℝ).coeff m := by
    intro ξ
    simp only [taylorPoly, jetTerm, coeff_sum, coeff_C_mul, Finset.mul_sum]
  simp_rw [key]
  refine tendsto_finsetSum _ fun j _ => ?_
  refine Tendsto.const_mul _ (tendsto_finsetSum _ fun i _ => ?_)
  refine Tendsto.mul ?_ ?_
  · have hc : ContinuousAt (fun ξ => iteratedFDeriv ℝ j g ξ) ξ₁ :=
      (hg.contDiffAt (n := ⊤)).continuousAt_iteratedFDeriv le_top
    exact hc.tendsto.eval_const _
  · have : CTo (𝓝 ξ₁) (fun ξ => ∏ k : Fin j, (X (i k) - MvPolynomial.C (ξ (i k)) :
        MvPolynomial ι ℝ)) (∏ k : Fin j, (X (i k) - MvPolynomial.C (ξ₁ (i k)))) :=
      CTo.prod _ fun k _ => (CTo.const _).sub (CTo.const_C ((continuous_apply (i k)).tendsto ξ₁))
    exact this m

end TaylorDeriv

/-! ### Coefficients of polynomials of bounded degree -/

section Coeff

variable {ι : Type} [Fintype ι]

theorem coeff_eq_zero_of_notMem_degSet {p : MvPolynomial ι ℝ} {B : ℕ} (h : p.totalDegree ≤ B)
    {m : ι →₀ ℕ} (hm : m ∉ degSet ι B) : p.coeff m = 0 :=
  notMem_support_iff.1 fun h' => hm (support_subset_degSet h h')

theorem totalDegree_pderiv_le [DecidableEq ι] (p : MvPolynomial ι ℝ) (i : ι) :
    (pderiv i p).totalDegree ≤ p.totalDegree := by
  refine Finset.sup_le fun m hm => ?_
  have hm' : (pderiv i p).coeff m ≠ 0 := mem_support_iff.1 hm
  rw [coeff_pderiv] at hm'
  have h1 : p.coeff (m + Finsupp.single i 1) ≠ 0 := left_ne_zero_of_mul hm'
  refine le_trans ?_ (le_totalDegree (mem_support_iff.2 h1))
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
  exact Nat.le_add_right _ _

end Coeff

/-! ### Programs from circuit graphs, and the program for `E = ∇_c Ψ - ϑ â` -/

section Programs

variable {ι : Type}

/-- A gate as an instruction; slot `0` holds `0`, slot `k + 1` holds the constant `k`. -/
def gateInstr : Gate ι → Instr ι ℕ
  | .var i => ⟨.add, .input i, .const 0⟩
  | .const k => ⟨.add, .const (k + 1), .const 0⟩
  | .add j k => ⟨.add, .prev j, .prev k⟩
  | .mul j k => ⟨.mul, .prev j, .prev k⟩

/-- A circuit graph as a program graph. -/
def shapeProg (Γ : Shape ι) : SLP ι ℕ := Γ.map gateInstr

/-- The constants of `shapeProg`. -/
def shapeConst (a : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => a k

theorem length_shapeProg (Γ : Shape ι) : (shapeProg Γ).length = Γ.length := by
  simp [shapeProg]

theorem shape_values_append (Γ : Shape ι) (g : Gate ι) (a : ℕ → ℝ) :
    (Γ ++ [g]).values a = Γ.values a ++ [g.eval a (Γ.values a)] := by
  simp [Shape.values, List.foldl_append]

theorem values_shapeProg (Γ : Shape ι) (a : ℕ → ℝ) :
    ((shapeProg Γ).instantiate (shapeConst a)).values = Γ.values a := by
  induction Γ using List.reverseRecOn with
  | nil => rfl
  | append_singleton Γ g ih =>
    have h1 : (shapeProg (Γ ++ [g])).instantiate (shapeConst a) =
        (shapeProg Γ).instantiate (shapeConst a) ++
          [⟨(gateInstr g).op, (gateInstr g).a.instantiate (shapeConst a),
            (gateInstr g).b.instantiate (shapeConst a)⟩] := by
      simp [shapeProg, SLP.instantiate]
    rw [h1, BaurStrassen.values_append_single, ih, shape_values_append]
    congr 2
    cases g with
    | var i => simp [gateInstr, Instr.eval, ArithOp.apply, Operand.instantiate, Operand.eval,
        shapeConst, Gate.eval]
    | const k => simp [gateInstr, Instr.eval, ArithOp.apply, Operand.instantiate, Operand.eval,
        shapeConst, Gate.eval]
    | add j k => simp [gateInstr, Instr.eval, ArithOp.apply, Operand.instantiate, Operand.eval,
        Gate.eval]
    | mul j k => simp [gateInstr, Instr.eval, ArithOp.apply, Operand.instantiate, Operand.eval,
        Gate.eval]

theorem progOutput_shapeProg (Γ : Shape ι) (a : ℕ → ℝ) (o : ℕ) :
    progOutput (shapeProg Γ) (shapeConst a) (.prev o) = (Γ.values a).getD o 0 := by
  rw [progOutput, values_shapeProg]
  rfl

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-- Shift the constant slots of an operand by `K`. -/
def shOp (K : ℕ) : Operand ι ℕ → Operand ι ℕ
  | .input i => .input i
  | .const m => .const (m + K)
  | .prev j => .prev j

/-- An operand of a program of length `n`, with constants shifted by `K + 1` and forward
references replaced by the slot `K` (which holds `0`). -/
def nOp (K n : ℕ) : Operand ι ℕ → Operand ι ℕ
  | .input i => .input i
  | .const m => .const (m + K + 1)
  | .prev j => if j < n then .prev j else .const K

/-- The program for `E_k = ∂_{c_k} Ψ - b_k`: the program `P` computing `Ψ` and its
derivatives `od` (constants shifted by `κ + 1`), followed by one subtraction for each `k`. -/
def eProg (P : SLP (ι ⊕ κ) ℕ) (od : ι ⊕ κ → Operand (ι ⊕ κ) ℕ) : SLP (ι ⊕ κ) ℕ :=
  P.map (fun ins => ⟨ins.op, shOp (Fintype.card κ + 1) ins.a, shOp (Fintype.card κ + 1) ins.b⟩)
    ++ List.ofFn (fun j : Fin (Fintype.card κ) =>
      (⟨.sub, nOp (Fintype.card κ) P.length (od (Sum.inr ((Fintype.equivFin κ).symm j))),
        .const j⟩ : Instr (ι ⊕ κ) ℕ))

/-- The output operands of `eProg`. -/
def eOut (P : SLP (ι ⊕ κ) ℕ) (k : κ) : Operand (ι ⊕ κ) ℕ :=
  .prev (P.length + (Fintype.equivFin κ k : ℕ))

/-- The constants of `eProg`. -/
def eConst (c : ℕ → ℝ) (b : κ → ℝ) (m : ℕ) : ℝ :=
  if h : m < Fintype.card κ then b ((Fintype.equivFin κ).symm ⟨m, h⟩)
  else if m = Fintype.card κ then 0 else c (m - (Fintype.card κ + 1))

theorem length_eProg (P : SLP (ι ⊕ κ) ℕ) (od : ι ⊕ κ → Operand (ι ⊕ κ) ℕ) :
    (eProg P od).length = P.length + Fintype.card κ := by
  simp [eProg]

open BaurStrassen in
/-- Values of instructions appended after `P` that only read positions of `P`. -/
theorem getD_vals_append {σ' : Type} (c : ℕ → ℝ) (P : SLP σ' ℕ) :
    ∀ (T : SLP σ' ℕ), (∀ ins ∈ T, Valid P.length ins.a ∧ Valid P.length ins.b) →
      ∀ (j : ℕ) (hj : j < T.length), (vals c (P ++ T)).getD (P.length + j) 0 =
        (T[j]).op.apply (ev c (vals c P) (T[j]).a) (ev c (vals c P) (T[j]).b) := by
  intro T
  induction T using List.reverseRecOn with
  | nil => intro _ j hj; simp at hj
  | append_singleton T ins ih =>
    intro hT j hj
    have hT' : ∀ i ∈ T, Valid P.length i.a ∧ Valid P.length i.b :=
      fun i hi => hT i (List.mem_append_left _ hi)
    have hins := hT ins (List.mem_append_right _ (List.mem_singleton_self _))
    rw [← List.append_assoc, vals_append_single]
    have hlen : (vals c (P ++ T)).length = P.length + T.length := by
      rw [length_vals, List.length_append]
    rw [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | hj'
    · rw [List.getD_append _ _ _ _ (by rw [hlen]; omega), ih hT' j hj',
        List.getElem_append_left hj']
    · subst hj'
      rw [List.getD_append_right _ _ _ _ (by rw [hlen]), hlen, Nat.sub_self,
        List.getElem_append_right (le_refl _)]
      simp only [Nat.sub_self, List.getD_cons_zero, List.getElem_singleton]
      have hpre : P <+: P ++ T := List.prefix_append _ _
      rw [ev_mono c hpre hins.1, ev_mono c hpre hins.2]

open BaurStrassen in
theorem progOutputs_eProg (P : SLP (ι ⊕ κ) ℕ) (od : ι ⊕ κ → Operand (ι ⊕ κ) ℕ)
    (c : ℕ → ℝ) (b : κ → ℝ) (k : κ) :
    progOutputs (eProg P od) (eConst c b) (eOut P) k =
      progOutput P c (od (Sum.inr k)) - MvPolynomial.C (b k) := by
  set K := Fintype.card κ with hK
  set c' := eConst c b with hc'
  set P' : SLP (ι ⊕ κ) ℕ :=
    P.map (fun ins => ⟨ins.op, shOp (K + 1) ins.a, shOp (K + 1) ins.b⟩) with hP'
  set T : SLP (ι ⊕ κ) ℕ := List.ofFn (fun j : Fin K =>
    (⟨.sub, nOp K P.length (od (Sum.inr ((Fintype.equivFin κ).symm j))), .const j⟩ :
      Instr (ι ⊕ κ) ℕ)) with hT
  have hshift : ∀ m, c' (m + K + 1) = c m := by
    intro m
    simp only [hc', eConst]
    rw [dif_neg (by omega), if_neg (by omega)]
    congr 1; omega
  have hzero : c' K = 0 := by
    simp only [hc', eConst]
    rw [dif_neg (lt_irrefl _), if_pos rfl]
  have hb : ∀ j : Fin K, c' j = b ((Fintype.equivFin κ).symm j) := by
    intro j
    simp only [hc', eConst]
    rw [dif_pos j.2]
  have hvals : vals c' P' = vals c P := by
    have h : ∀ x : Operand (ι ⊕ κ) ℕ, (shOp (K + 1) x).instantiate c' = x.instantiate c := by
      intro x
      cases x with
      | const m => simp only [shOp, Operand.instantiate, ← add_assoc, hshift]
      | _ => rfl
    simp only [vals, hP', SLP.instantiate, List.map_map]
    congr 2
    funext ins
    simp [h]
  have hlen : P'.length = P.length := by simp [hP']
  have hev : ∀ o : Operand (ι ⊕ κ) ℕ, ev c' (vals c' P') (nOp K P.length o) =
      ev c (vals c P) o := by
    intro o
    cases o with
    | input i => rfl
    | const m => simp [nOp, hshift]
    | prev j =>
      simp only [nOp]
      split_ifs with hj
      · rw [ev_prev, ev_prev, hvals]
      · rw [ev_const, hzero, map_zero, ev_prev,
          List.getD_eq_default _ _ (by rw [length_vals]; omega)]
  have hvalid : ∀ ins ∈ T, Valid P'.length ins.a ∧ Valid P'.length ins.b := by
    intro ins hins
    rw [hT, List.mem_ofFn] at hins
    obtain ⟨j, rfl⟩ := hins
    refine ⟨?_, trivial⟩
    rw [hlen]
    cases h : od (Sum.inr ((Fintype.equivFin κ).symm j)) with
    | prev i =>
      simp only [nOp]
      split_ifs with hi
      · exact hi
      · trivial
    | _ => trivial
  have hk : (Fintype.equivFin κ k : ℕ) < T.length := by
    rw [hT, List.length_ofFn]; exact (Fintype.equivFin κ k).2
  have := getD_vals_append c' P' T hvalid _ hk
  rw [hlen] at this
  show ev c' (vals c' (P' ++ T)) (.prev (P.length + (Fintype.equivFin κ k : ℕ))) = _
  rw [ev_prev, this]
  simp only [hT, List.getElem_ofFn, ArithOp.apply, ev_const]
  rw [hev, Equiv.symm_apply_apply, hb, Equiv.symm_apply_apply]
  rfl

/-- Appending `add j L` (with `L` the length, which reads `0`) puts the value of gate `j` at
the last gate. -/
theorem computes_append_add (Γ : Shape ι) (c : ℕ → ℝ) (j : ℕ) :
    (Γ ++ [Gate.add j Γ.length]).Computes c ((Γ.values c).getD j 0) := by
  rw [Shape.Computes, shape_values_append]
  refine List.mem_append_right _ (List.mem_singleton.2 ?_)
  have h0 : (Γ.values c).getD Γ.length 0 = 0 :=
    List.getD_eq_default _ _ (by rw [length_values])
  simp only [Gate.eval, h0, add_zero]

end Programs

/-! ### The size bound -/

theorem sl_size_arith (CN CB C₆ d k n S g p₂ p₃ γ : ℕ) (hd : d + 1 ≤ S) (hk : k ≤ S) (hn : n ≤ S)
    (hg : g ≤ C₆ * (S + 1) ^ 6) (hp₂ : p₂ ≤ CB * (g + 1)) (hp₃ : p₃ = p₂ + k)
    (hγ : γ ≤ CN * ((d + 1) ^ 3 * (p₃ + 1) + (d + 1) ^ 2 * k ^ 2 + n)) :
    γ + 1 ≤ (CN * (64 * CB * C₆ + CB + 4) + 1) * S ^ 9 := by
  have hS1 : 1 ≤ S := by omega
  have hpow : ∀ a b, a ≤ b → S ^ a ≤ S ^ b := fun a b h => Nat.pow_le_pow_right hS1 h
  have hS6 : (S + 1) ^ 6 ≤ 64 * S ^ 6 := by
    calc (S + 1) ^ 6 ≤ (2 * S) ^ 6 := Nat.pow_le_pow_left (by omega) 6
      _ = 64 * S ^ 6 := by ring
  have h61 : 1 ≤ S ^ 6 := Nat.one_le_pow _ _ hS1
  have hS61 : S ≤ S ^ 6 := by simpa using hpow 1 6 (by norm_num)
  have hg' : g ≤ 64 * C₆ * S ^ 6 := by
    calc g ≤ C₆ * (S + 1) ^ 6 := hg
      _ ≤ C₆ * (64 * S ^ 6) := Nat.mul_le_mul_left _ hS6
      _ = 64 * C₆ * S ^ 6 := by ring
  have hp₂' : p₂ ≤ (64 * CB * C₆ + CB) * S ^ 6 := by
    calc p₂ ≤ CB * (g + 1) := hp₂
      _ ≤ CB * (64 * C₆ * S ^ 6 + S ^ 6) := Nat.mul_le_mul_left _ (by omega)
      _ = (64 * CB * C₆ + CB) * S ^ 6 := by ring
  have hp₃' : p₃ + 1 ≤ (64 * CB * C₆ + CB + 2) * S ^ 6 := by
    have e : (64 * CB * C₆ + CB + 2) * S ^ 6 = (64 * CB * C₆ + CB) * S ^ 6 + S ^ 6 + S ^ 6 := by
      ring
    rw [e]; omega
  have h1 : (d + 1) ^ 3 * (p₃ + 1) ≤ (64 * CB * C₆ + CB + 2) * S ^ 9 := by
    calc (d + 1) ^ 3 * (p₃ + 1) ≤ S ^ 3 * ((64 * CB * C₆ + CB + 2) * S ^ 6) :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hd 3) hp₃'
      _ = (64 * CB * C₆ + CB + 2) * S ^ 9 := by ring
  have h2 : (d + 1) ^ 2 * k ^ 2 ≤ S ^ 9 := by
    calc (d + 1) ^ 2 * k ^ 2 ≤ S ^ 2 * S ^ 2 :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hd 2) (Nat.pow_le_pow_left hk 2)
      _ = S ^ 4 := by ring
      _ ≤ S ^ 9 := hpow 4 9 (by norm_num)
  have h3 : n ≤ S ^ 9 := hn.trans (by simpa using hpow 1 9 (by norm_num))
  have h4 : (d + 1) ^ 3 * (p₃ + 1) + (d + 1) ^ 2 * k ^ 2 + n ≤
      (64 * CB * C₆ + CB + 4) * S ^ 9 := by
    have e : (64 * CB * C₆ + CB + 4) * S ^ 9 =
        (64 * CB * C₆ + CB + 2) * S ^ 9 + S ^ 9 + S ^ 9 := by ring
    rw [e]; omega
  have h5 := Nat.mul_le_mul_left CN h4
  have h6 : 1 ≤ S ^ 9 := Nat.one_le_pow _ _ hS1
  have e : (CN * (64 * CB * C₆ + CB + 4) + 1) * S ^ 9 =
      CN * ((64 * CB * C₆ + CB + 4) * S ^ 9) + S ^ 9 := by ring
  rw [e]; omega

end SecondAux

open SecondAux

namespace SLData

variable {σ κ : Type} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ] {M : ℕ}
  {D : SLData σ κ M} {f : MvPolynomial σ ℝ} {yc : κ}

variable (D) in
/-- The tilted objective `e(x; c) - ϑ⟨â, c⟩`. -/
def tiltObj (â : κ → ℝ) (x : σ → ℝ) (ϑ : ℝ) (c : κ → ℝ) : ℝ :=
  D.env x c - ϑ * ∑ k, â k * c k

theorem isSA_boxDomain (V : Set (σ → ℝ)) (hV : IsSA V) (ε₀ : ℝ) :
    IsSA (boxDomain V ε₀) :=
  FO.isSA_and (hV.preimage_comp some)
    (FO.isSA_and (FO.isSA_lt (FO.IsPolyFn.const 0) (FO.IsPolyFn.coord none))
      (FO.isSA_lt (FO.IsPolyFn.coord none) (FO.IsPolyFn.const ε₀)))

/-- The minimizers of `e(x; c) - ϑ⟨â, c⟩` over `B̄` (§6.5): a semialgebraic choice `W` on
`V × (0, ϑ₂)`, with values in `int B̄`, satisfying `∇_c e = ϑ â`, and converging to `φ`. -/
theorem Good.minimizer_family (hS : SAFacts) (hG : D.Good f yc) {x' : σ → ℝ} {ρ' : ℝ}
    (hK' : Metric.closedBall x' ρ' ⊆ Metric.ball D.x₀ D.ρ)
    (hμ : ∀ η > 0, ∃ μ > 0, ∀ x ∈ Metric.closedBall x' ρ', ∀ c ∈ D.Bbar,
      η ≤ sqDist c (D.φ x) → μ ≤ D.env x c)
    (â : κ → ℝ) {xV : σ → ℝ} {rV : ℝ} (_hrV : 0 < rV)
    (hV : Metric.ball xV rV ⊆ Metric.ball x' ρ') {ϑ₁ : ℝ} (hϑ₁ : 0 < ϑ₁) :
    ∃ (W : (σ → ℝ) → ℝ → (κ → ℝ)) (ϑ₂ : ℝ), 0 < ϑ₂ ∧ ϑ₂ ≤ ϑ₁ ∧
      IsSAFunOn (boxDomain (Metric.ball xV rV) ϑ₂) (uncurryOpt W) ∧
      (∀ x ∈ Metric.ball xV rV, ∀ ϑ ∈ Ioo 0 ϑ₂,
        W x ϑ ∈ D.Bo ∧ ∀ k, D.grad x (W x ϑ) k = ϑ * â k) ∧
      (∀ x ∈ Metric.ball xV rV, Tendsto (W x) (𝓝[>] 0) (𝓝 (D.φ x))) := by
  have hr₀ := hG.r₀_pos
  have hVK : ∀ x ∈ Metric.ball xV rV, x ∈ D.K := fun x hx =>
    Metric.ball_subset_closedBall (hK' (Metric.ball_subset_closedBall (hV hx)))
  have hV' : ∀ x ∈ Metric.ball xV rV, x ∈ Metric.closedBall x' ρ' := fun x hx =>
    Metric.ball_subset_closedBall (hV hx)
  set La : ℝ := 2 * D.r₀ * ∑ k, |â k| + 1 with hLa
  have hLa_pos : 0 < La := by
    have : 0 ≤ ∑ k, |â k| := Finset.sum_nonneg fun k _ => abs_nonneg _
    positivity
  -- minimizers exist
  have hw₀ : D.w₀ ∈ D.Bbar := by
    show sqDist D.w₀ D.w₀ ≤ D.r₀ ^ 2
    rw [sd_self]; positivity
  have hexists : ∀ x ∈ D.K, ∀ ϑ, ∃ c ∈ D.Bbar, ∀ c' ∈ D.Bbar,
      tiltObj D â x ϑ c ≤ tiltObj D â x ϑ c' := by
    intro x hx ϑ
    have hcont : ContinuousOn (tiltObj D â x ϑ) D.Bbar := by
      refine ((hG.contDiff_env hx).continuous.sub (continuous_const.mul
        (continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_apply k)))).continuousOn
    obtain ⟨c, hc, hmin⟩ := isCompact_Bbar.exists_isMinOn ⟨D.w₀, hw₀⟩ hcont
    exact ⟨c, hc, fun c' hc' => hmin hc'⟩
  -- the estimate `e(x; c̄) ≤ ϑ (La - 1)`
  have hest : ∀ x ∈ D.K, ∀ ϑ, 0 ≤ ϑ → ∀ c ∈ D.Bbar,
      (∀ c' ∈ D.Bbar, tiltObj D â x ϑ c ≤ tiltObj D â x ϑ c') → D.env x c ≤ ϑ * (La - 1) := by
    intro x hx ϑ hϑ c hc hmin
    have h1 := hmin (D.φ x) (hG.phi_mem hx)
    simp only [tiltObj, hG.env_phi hx] at h1
    have h2 : ∑ k, â k * c k - ∑ k, â k * D.φ x k ≤ 2 * D.r₀ * ∑ k, |â k| := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_le_sum fun k _ => ?_
      have hck := sd_abs_sub_le hr₀.le hc k
      have hφk := sd_abs_sub_le hr₀.le (hG.phi_mem hx) k
      have : |c k - D.φ x k| ≤ 2 * D.r₀ := by
        calc |c k - D.φ x k| = |(c k - D.w₀ k) - (D.φ x k - D.w₀ k)| := by ring_nf
          _ ≤ |c k - D.w₀ k| + |D.φ x k - D.w₀ k| := abs_sub _ _
          _ ≤ 2 * D.r₀ := by linarith
      calc â k * c k - â k * D.φ x k = â k * (c k - D.φ x k) := by ring
        _ ≤ |â k * (c k - D.φ x k)| := le_abs_self _
        _ = |â k| * |c k - D.φ x k| := abs_mul _ _
        _ ≤ |â k| * (2 * D.r₀) := mul_le_mul_of_nonneg_left this (abs_nonneg _)
        _ = 2 * D.r₀ * |â k| := by ring
    have h3 : D.env x c ≤ ϑ * (∑ k, â k * c k - ∑ k, â k * D.φ x k) := by linarith
    calc D.env x c ≤ ϑ * (∑ k, â k * c k - ∑ k, â k * D.φ x k) := h3
      _ ≤ ϑ * (2 * D.r₀ * ∑ k, |â k|) := mul_le_mul_of_nonneg_left h2 hϑ
      _ = ϑ * (La - 1) := by rw [hLa]; ring
  -- minimizers are close to `φ(x)`
  have hclose : ∀ η > 0, ∀ μ > 0, (∀ x ∈ Metric.closedBall x' ρ', ∀ c ∈ D.Bbar,
      η ≤ sqDist c (D.φ x) → μ ≤ D.env x c) →
      ∀ x ∈ Metric.ball xV rV, ∀ ϑ, 0 < ϑ → ϑ * La ≤ μ → ∀ c ∈ D.Bbar,
      (∀ c' ∈ D.Bbar, tiltObj D â x ϑ c ≤ tiltObj D â x ϑ c') → sqDist c (D.φ x) < η := by
    intro η _ μ _ hμp x hx ϑ hϑ hϑμ c hc hmin
    by_contra hcon
    push Not at hcon
    have h1 := hμp x (hV' x hx) c hc hcon
    have h2 := hest x (hVK x hx) ϑ hϑ.le c hc hmin
    nlinarith
  obtain ⟨μ₀, hμ₀, hμ₀p⟩ := hμ ((D.r₀ / 2) ^ 2) (by positivity)
  set ϑ₂ := min ϑ₁ (μ₀ / La) with hϑ₂def
  have hϑ₂ : 0 < ϑ₂ := lt_min hϑ₁ (div_pos hμ₀ hLa_pos)
  -- interior minimizers satisfy `∇_c e = ϑ â`
  have hint : ∀ x ∈ Metric.ball xV rV, ∀ ϑ ∈ Ioo 0 ϑ₂, ∀ c ∈ D.Bbar,
      (∀ c' ∈ D.Bbar, tiltObj D â x ϑ c ≤ tiltObj D â x ϑ c') →
      c ∈ D.Bo ∧ ∀ k, D.grad x c k = ϑ * â k := by
    intro x hx ϑ hϑ c hc hmin
    have hxK := hVK x hx
    have hϑμ : ϑ * La ≤ μ₀ := by
      have : ϑ < μ₀ / La := hϑ.2.trans_le (min_le_right _ _)
      rw [lt_div_iff₀ hLa_pos] at this; linarith
    have hcl := hclose _ (by positivity) μ₀ hμ₀ hμ₀p x hx ϑ hϑ.1 hϑμ c hc hmin
    have hBo : c ∈ D.Bo := mem_Bo_of_near hr₀ (hG.φ_near x hxK) hcl
    refine ⟨hBo, fun k => ?_⟩
    have hl : HasDerivAt (fun t : ℝ => c + t • (Pi.single k 1 : κ → ℝ)) (Pi.single k 1) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single k 1 : κ → ℝ)).const_add c
    have hloc : IsLocalMin (fun t : ℝ => tiltObj D â x ϑ (c + t • Pi.single k 1)) 0 := by
      have := hl.continuousAt.preimage_mem_nhds (by simpa using D.isOpen_Bo.mem_nhds hBo)
      filter_upwards [this] with t ht
      simpa using hmin _ (Bo_subset_Bbar ht)
    have hd1 : HasDerivAt (fun t : ℝ => D.env x (c + t • Pi.single k 1)) (D.grad x c k) 0 :=
      ((hG.differentiable_env hxK) c).hasFDerivAt.comp_hasDerivAt_of_eq 0 hl (by simp)
    have hd2 : HasDerivAt (fun t : ℝ => ϑ * ∑ j, â j * (c + t • (Pi.single k 1 : κ → ℝ)) j)
        (ϑ * â k) 0 := by
      have e : (fun t : ℝ => ϑ * ∑ j, â j * (c + t • (Pi.single k 1 : κ → ℝ)) j) =
          fun t => ϑ * ∑ j, â j * c j + (ϑ * â k) * t := by
        funext t
        have : ∑ j, â j * (c + t • (Pi.single k 1 : κ → ℝ)) j = ∑ j, â j * c j + t * â k := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
          congr 1
          rw [Finset.sum_eq_single k]
          · simp; ring
          · intro j _ hj; simp [hj]
          · simp
        rw [this]; ring
      rw [e]
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (ϑ * â k)).const_add
        (ϑ * ∑ j, â j * c j)
    have := hloc.hasDerivAt_eq_zero (hd1.sub hd2)
    linarith
  -- a semialgebraic choice of minimizers (S2)
  set Emin : Set (Option σ ⊕ κ → ℝ) := {u | (u ∘ Sum.inl) ∘ some ∈ Metric.ball xV rV ∧
    u (Sum.inl none) ∈ Ioo 0 ϑ₂ ∧ u ∘ Sum.inr ∈ D.Bbar ∧ ∀ c' ∈ D.Bbar,
      tiltObj D â ((u ∘ Sum.inl) ∘ some) (u (Sum.inl none)) (u ∘ Sum.inr) ≤
        tiltObj D â ((u ∘ Sum.inl) ∘ some) (u (Sum.inl none)) c'} with hEmin
  have hEsa : IsSA Emin := by
    have key : IsSA {u : Option σ ⊕ κ → ℝ |
        (u ∘ Sum.inl) ∘ some ∈ Metric.ball xV rV ∧
        (0 < u (Sum.inl none) ∧ u (Sum.inl none) < ϑ₂) ∧
        sqDist (u ∘ Sum.inr) D.w₀ ≤ D.r₀ ^ 2 ∧
        ∃ t : ℝ, ((u ∘ Sum.inl) ∘ some ∈ D.K ∧
            D.env ((u ∘ Sum.inl) ∘ some) (u ∘ Sum.inr) = t) ∧
          ∀ c' : κ → ℝ, ∀ t' : ℝ, (sqDist c' D.w₀ ≤ D.r₀ ^ 2 ∧
            ((u ∘ Sum.inl) ∘ some ∈ D.K ∧ D.env ((u ∘ Sum.inl) ∘ some) c' = t')) →
            t - u (Sum.inl none) * ∑ k, â k * (u ∘ Sum.inr) k ≤
              t' - u (Sum.inl none) * ∑ k, â k * c' k} := by
      refine FO.isSA_and ((isSA_ball xV rV).preimage_comp _) (FO.isSA_and
        (FO.isSA_and (FO.isSA_lt (FO.IsPolyFn.const 0) (FO.IsPolyFn.coord _))
          (FO.isSA_lt (FO.IsPolyFn.coord _) (FO.IsPolyFn.const _))) (FO.isSA_and ?_ ?_))
      · exact FO.isSA_le (isPolyFn_sqDist (fun k => FO.IsPolyFn.coord _)
          (fun k => FO.IsPolyFn.const _)) (FO.IsPolyFn.const _)
      · refine FO.isSA_exists_real (FO.isSA_and ?_ ?_)
        · exact hG.isSA_env_eq (Sum.inl ∘ Sum.inl ∘ some) (Sum.inl ∘ Sum.inr) (Sum.inr ())
        · refine FO.isSA_forall_fun (FO.isSA_forall_real (FO.isSA_imp (FO.isSA_and ?_ ?_) ?_))
          · exact FO.isSA_le (isPolyFn_sqDist (fun k => FO.IsPolyFn.coord _)
              (fun k => FO.IsPolyFn.const _)) (FO.IsPolyFn.const _)
          · exact hG.isSA_env_eq (Sum.inl ∘ Sum.inl ∘ Sum.inl ∘ Sum.inl ∘ some)
              (Sum.inl ∘ Sum.inr) (Sum.inr ())
          · exact FO.isSA_le ((FO.IsPolyFn.coord _).sub ((FO.IsPolyFn.coord _).mul
              (isPolyFn_sum _ fun k => (FO.IsPolyFn.const _).mul (FO.IsPolyFn.coord _))))
              ((FO.IsPolyFn.coord _).sub ((FO.IsPolyFn.coord _).mul
              (isPolyFn_sum _ fun k => (FO.IsPolyFn.const _).mul (FO.IsPolyFn.coord _))))
    convert key using 1
    ext u
    simp only [hEmin, mem_ofPred_eq, mem_Ioo, tiltObj]
    constructor
    · rintro ⟨hx, hϑ, hc, hmin⟩
      refine ⟨hx, hϑ, hc, _, ⟨hVK _ hx, rfl⟩, fun c' t' ⟨hc', _, ht'⟩ => ?_⟩
      rw [← ht']
      exact hmin c' hc'
    · rintro ⟨hx, hϑ, hc, t, ⟨_, ht⟩, hmin⟩
      refine ⟨hx, hϑ, hc, fun c' hc' => ?_⟩
      rw [ht]
      exact hmin c' _ ⟨hc', hVK _ hx, rfl⟩
  obtain ⟨s, hs, hsec⟩ := hS.choice Emin hEsa
  set W : (σ → ℝ) → ℝ → (κ → ℝ) := fun x ϑ => s (extendVal ϑ x) with hWdef
  have hWs : uncurryOpt W = s := by
    funext v
    simp only [uncurryOpt, hWdef]
    congr 1
    funext o
    cases o <;> rfl
  have hWmin : ∀ x ∈ Metric.ball xV rV, ∀ ϑ ∈ Ioo 0 ϑ₂, W x ϑ ∈ D.Bbar ∧
      ∀ c' ∈ D.Bbar, tiltObj D â x ϑ (W x ϑ) ≤ tiltObj D â x ϑ c' := by
    intro x hx ϑ hϑ
    obtain ⟨c, hc, hcmin⟩ := hexists x (hVK x hx) ϑ
    have hmem : Sum.elim (extendVal ϑ x) c ∈ Emin := ⟨hx, hϑ, hc, hcmin⟩
    have := hsec (extendVal ϑ x) ⟨c, hmem⟩
    exact ⟨this.2.2.1, this.2.2.2⟩
  refine ⟨W, ϑ₂, hϑ₂, min_le_left _ _, ?_, fun x hx ϑ hϑ => ?_, fun x hx => ?_⟩
  · rw [hWs]
    exact hs.mono (isSA_boxDomain _ (isSA_ball xV rV) ϑ₂) (subset_univ _)
  · obtain ⟨h1, h2⟩ := hWmin x hx ϑ hϑ
    exact hint x hx ϑ hϑ _ h1 h2
  · rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨μ, hμpos, hμp⟩ := hμ ((ε / 2) ^ 2) (by positivity)
    have hpos : 0 < min ϑ₂ (μ / La) := lt_min hϑ₂ (div_pos hμpos hLa_pos)
    filter_upwards [Ioo_mem_nhdsGT hpos] with ϑ hϑ
    have hϑ₂' : ϑ ∈ Ioo 0 ϑ₂ := ⟨hϑ.1, hϑ.2.trans_le (min_le_left _ _)⟩
    have hϑμ : ϑ * La ≤ μ := by
      have : ϑ < μ / La := hϑ.2.trans_le (min_le_right _ _)
      rw [lt_div_iff₀ hLa_pos] at this; linarith
    obtain ⟨h1, h2⟩ := hWmin x hx ϑ hϑ₂'
    have hcl := hclose _ (by positivity) μ hμpos hμp x hx ϑ hϑ.1 hϑμ _ h1 h2
    rw [dist_pi_lt_iff hε]
    intro k
    rw [Real.dist_eq]
    have := sd_abs_sub_le (by positivity) hcl.le k
    linarith

/-- The `x`-Taylor coefficients of `Θ(·, ϑ)_y` converge to those of `f` (from Corollary 3.2). -/
theorem tendsto_taylor_W {U : Set (σ → ℝ)} (hU : IsOpen U) {x₁ : σ → ℝ} (hx₁ : x₁ ∈ U)
    {W : (σ → ℝ) → ℝ → (κ → ℝ)} {φ : (σ → ℝ) → (κ → ℝ)} {d : ℕ} {ε' : ℝ} (hε' : 0 < ε')
    (hWD : ∀ ε ∈ Ioo 0 ε', ContDiffOn ℝ d (fun ξ => W ξ ε) U) (hφD : ContDiffOn ℝ d φ U)
    (hconv : ∀ j ≤ d, TendstoUniformlyOn (fun ε ξ => iteratedFDeriv ℝ j (fun ξ => W ξ ε) ξ)
      (fun ξ => iteratedFDeriv ℝ j φ ξ) (𝓝[>] 0) U)
    {f : MvPolynomial σ ℝ} (hf : f.totalDegree ≤ d) (yc : κ) (hφf : ∀ x ∈ U, φ x yc = eval x f)
    (m : σ →₀ ℕ) :
    Tendsto (fun ε => (taylorPoly d (fun x => W x ε yc) x₁).coeff m) (𝓝[>] 0)
      (𝓝 (f.coeff m)) := by
  have hφ1 : ContDiffAt ℝ d φ x₁ := hφD.contDiffAt (hU.mem_nhds hx₁)
  have hfeq : (fun x => eval x f) =ᶠ[𝓝 x₁] (fun x => φ x yc) := by
    filter_upwards [hU.mem_nhds hx₁] with x hx using (hφf x hx).symm
  rw [← taylorPoly_eval_poly hf x₁]
  refine tendsto_coeff_taylorPoly (fun j hj => ?_) m
  rw [(hfeq.iteratedFDeriv ℝ j).eq_of_nhds]
  have hproj : iteratedFDeriv ℝ j (fun x => φ x yc) x₁ =
      (ContinuousLinearMap.proj yc).compContinuousMultilinearMap (iteratedFDeriv ℝ j φ x₁) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => ℝ) yc).iteratedFDeriv_comp_left hφ1
      (by exact_mod_cast hj)
  rw [hproj]
  have hev : (fun ε => (ContinuousLinearMap.proj yc).compContinuousMultilinearMap
      (iteratedFDeriv ℝ j (fun x => W x ε) x₁)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun ε => iteratedFDeriv ℝ j (fun x => W x ε yc) x₁) := by
    filter_upwards [Ioo_mem_nhdsGT hε'] with ε hε
    exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => ℝ) yc).iteratedFDeriv_comp_left
      ((hWD ε hε).contDiffAt (hU.mem_nhds hx₁)) (by exact_mod_cast hj)).symm
  refine Tendsto.congr' hev ?_
  have hcont : Continuous (fun L : ContinuousMultilinearMap ℝ (fun _ : Fin j => σ → ℝ) (κ → ℝ) =>
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => ℝ) yc).compContinuousMultilinearMap
        L) :=
    (ContinuousLinearMap.compContinuousMultilinearMapL ℝ _ _ _
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => ℝ) yc)).continuous
  exact (hcont.tendsto _).comp ((hconv j hj).tendsto_at hx₁)

/-- The equation `∇_c P = ϑ â` holds along `x ↦ (x, τ(x))` up to `o(|x - x₁|^d)`, where `τ` is
the Taylor polynomial of order `d` of a `C^d` solution `W` of `∇_c e = b` near `x₁`, and
`∇_c P` the Taylor polynomial of order `d` of `∇_c e` at `(x₁, W(x₁))`. -/
theorem taylor_residual {e : (σ ⊕ κ → ℝ) → ℝ} {x₁ : σ → ℝ} {W : (σ → ℝ) → (κ → ℝ)} {d : ℕ}
    (he : AnalyticAt ℝ e (Sum.elim x₁ (W x₁))) (hW : ContDiffAt ℝ d W x₁) (hd : 1 ≤ d)
    (b : κ → ℝ) (hcrit : ∀ᶠ x in 𝓝 x₁, ∀ l, pd e (Sum.inr l) (Sum.elim x (W x)) = b l) (l : κ) :
    (fun x => eval (Sum.elim x (fun k => eval x (taylorPoly d (fun x => W x k) x₁)))
      (taylorPoly d (pd e (Sum.inr l)) (Sum.elim x₁ (W x₁)) - MvPolynomial.C (b l)))
      =o[𝓝 x₁] (fun x => ‖x - x₁‖ ^ d) := by
  set ξ₁ : σ ⊕ κ → ℝ := Sum.elim x₁ (W x₁) with hξ₁
  set g := pd e (Sum.inr l) with hg_def
  set Tg := taylorPoly d g ξ₁ with hTg
  set τ : κ → MvPolynomial σ ℝ := fun k => taylorPoly d (fun x => W x k) x₁ with hτ
  have hg : AnalyticAt ℝ g ξ₁ := analyticAt_pd he _
  have hWk : ∀ k, ContDiffAt ℝ d (fun x => W x k) x₁ := contDiffAt_pi.1 hW
  have hγc : ContinuousAt (fun x => Sum.elim x (W x)) x₁ := by
    refine continuousAt_pi.2 fun i => ?_
    rcases i with i | k
    · exact (continuous_apply i).continuousAt
    · exact (continuousAt_pi.1 hW.continuousAt) k
  have hγ : Tendsto (fun x => Sum.elim x (W x)) (𝓝 x₁) (𝓝 ξ₁) := hγc.tendsto
  -- the Taylor remainder of `g` along `x ↦ (x, W x)`
  have h2 : (fun x => g (Sum.elim x (W x)) - eval (Sum.elim x (W x)) Tg) =o[𝓝 x₁]
      (fun x => ‖x - x₁‖ ^ d) := by
    have h := (taylorPoly_isLittleO (hg.contDiffAt (n := d))).comp_tendsto hγ
    refine h.trans_isBigO ?_
    have hdiff : DifferentiableAt ℝ (fun x => Sum.elim x (W x)) x₁ := by
      refine differentiableAt_pi.2 fun i => ?_
      rcases i with i | k
      · exact differentiableAt_apply i x₁
      · exact (hWk k).differentiableAt (by exact_mod_cast (show d ≠ 0 by omega))
    have := hdiff.hasFDerivAt.isBigO_sub
    exact this.norm_norm.pow d
  -- Taylor polynomials of `W`
  have hτW : (fun x => (fun k => eval x (τ k)) - W x) =o[𝓝 x₁] (fun x => ‖x - x₁‖ ^ d) := by
    rw [Asymptotics.isLittleO_pi]
    intro k
    refine (taylorPoly_isLittleO (hWk k)).neg_left.congr_left fun x => ?_
    simp [τ]
  have hγτ : Tendsto (fun x => Sum.elim x (fun k => eval x (τ k))) (𝓝 x₁) (𝓝 ξ₁) := by
    have hc : Continuous (fun x : σ → ℝ => Sum.elim x (fun k => eval x (τ k))) :=
      continuous_pi fun v => by
        cases v with
        | inl i => exact continuous_apply i
        | inr k => exact MvPolynomial.continuous_eval _
    have := hc.tendsto x₁
    have e : Sum.elim x₁ (fun k => eval x₁ (τ k)) = ξ₁ := by
      rw [hξ₁]; congr 1; funext k; exact eval_taylorPoly_self _ _ _
    rwa [e] at this
  obtain ⟨L, t, ht, hL⟩ := (contDiff_eval_poly Tg).contDiffAt.exists_lipschitzOnWith (x := ξ₁)
  have h1 : (fun x => eval (Sum.elim x (fun k => eval x (τ k))) Tg - eval (Sum.elim x (W x)) Tg)
      =O[𝓝 x₁] (fun x => (fun k => eval x (τ k)) - W x) := by
    refine Asymptotics.IsBigO.of_bound L ?_
    filter_upwards [hγτ.eventually_mem ht, hγ.eventually_mem ht] with x hx1 hx2
    have hLx := hL.dist_le_mul _ hx1 _ hx2
    rw [dist_eq_norm, dist_eq_norm] at hLx
    refine hLx.trans ?_
    gcongr
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun v => ?_
    cases v with
    | inl i => simp
    | inr k => simpa using norm_le_pi_norm ((fun k => eval x (τ k)) - W x) k
  have hsum := (h1.trans_isLittleO hτW).add h2.neg_left
  refine hsum.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [hcrit] with x hx
  simp only [map_sub, eval_C]
  rw [← hx l]
  ring

end SLData

open SLData

/-- **Part 2** of the proof of Theorem 6.1 (§6.3–6.6), the statement of `sl_conclude`. -/
theorem sl_conclude_proof (hS : SAFacts) :
    ∃ C e : ℕ, ∀ {σ κ : Type} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ] {M : ℕ}
      (D : SLData σ κ M) (f : MvPolynomial σ ℝ) (yc : κ) (d : ℕ), D.Good f yc → 1 ≤ d →
      f.totalDegree ≤ d →
      BorderLE f (C * (d + Fintype.card κ + M + D.ℓmax + Nat.log 2 D.N + Fintype.card σ + 2) ^ e)
    := by
  obtain ⟨C₆, h₆⟩ := SLData.env_value hS
  obtain ⟨CB, hB⟩ := baur_strassen
  obtain ⟨CN, hN⟩ := newton_circuit
  refine ⟨CN * (64 * CB * C₆ + CB + 4) + 1, 9, ?_⟩
  intro σ κ _ _ _ _ M D f yc d hG hd hf
  -- Lemma 6.5
  obtain ⟨x', ρ', hρ', hK', -, hμ⟩ := hG.env_continuity hS
  have hK'K : Metric.ball x' ρ' ⊆ D.K := fun x hx =>
    Metric.ball_subset_closedBall (hK' (Metric.ball_subset_closedBall hx))
  -- Lemma 6.7
  obtain ⟨â, xV, rV, ϑ₁, hrV, hVsub, hϑ₁, htilt⟩ := hG.tilt hS hρ' hK'K
  -- the minimizers
  obtain ⟨W, ϑ₂, hϑ₂, hϑ₂₁, hWsa, hWprop, hWlim⟩ :=
    hG.minimizer_family hS hK' hμ â hrV hVsub hϑ₁
  -- Corollary 3.2
  have hφc : ContinuousOn D.φ (Metric.ball xV rV) := hG.φ_cont.mono (hVsub.trans hK'K)
  obtain ⟨x₁, r', ε', hr', hball', hε', hε'le, -, hWD, -, hφD, hconv⟩ :=
    derivatives_cor hS (Metric.ball xV rV) Metric.isOpen_ball ⟨xV, Metric.mem_ball_self hrV⟩
      ϑ₂ hϑ₂ W hWsa D.φ hφc hWlim d hd
  have hx₁B : x₁ ∈ Metric.ball x₁ r' := Metric.mem_ball_self hr'
  have hx₁V : x₁ ∈ Metric.ball xV rV := hball' hx₁B
  have hx₁K : x₁ ∈ D.K := hK'K (hVsub hx₁V)
  have hx₁OK : ∀ c : κ → ℝ, Sum.elim x₁ c ∈ D.OK := fun c =>
    show x₁ ∈ Metric.ball D.x₀ D.ρ from hK' (Metric.ball_subset_closedBall (hVsub hx₁V))
  -- Lemma 6.6, for `D = d + 1`
  obtain ⟨graphs, hgsize, O₀, -, hO₀dense, hO₀⟩ := h₆ D f yc hG (d + 1) (by omega)
  -- the composite graphs: Lemma 6.6, program, Baur–Strassen, `E`, Newton
  have hB' := fun (prog : SLP (σ ⊕ κ) ℕ) (o : Operand (σ ⊕ κ) ℕ) => hB prog o
  choose P₂ o₀ od cmap hP₂len hP₂ using hB'
  have hN' := fun (prog : SLP (σ ⊕ κ) ℕ) (oE : κ → Operand (σ ⊕ κ) ℕ) =>
    hN (ι := σ) (κ := κ) prog oE d
  choose Γ' out enc hΓ'len hΓ' using hN'
  let prog₁ : Shape (σ ⊕ κ) × ℕ → SLP (σ ⊕ κ) ℕ := fun Γo => shapeProg Γo.1
  let prog₂ : Shape (σ ⊕ κ) × ℕ → SLP (σ ⊕ κ) ℕ := fun Γo => P₂ (prog₁ Γo) (.prev Γo.2)
  let prog₃ : Shape (σ ⊕ κ) × ℕ → SLP (σ ⊕ κ) ℕ := fun Γo =>
    eProg (prog₂ Γo) (od (prog₁ Γo) (.prev Γo.2))
  let oE : Shape (σ ⊕ κ) × ℕ → κ → Operand (σ ⊕ κ) ℕ := fun Γo => eOut (prog₂ Γo)
  let comp : Shape (σ ⊕ κ) × ℕ → Shape σ := fun Γo =>
    Γ' (prog₃ Γo) (oE Γo) ++ [Gate.add (out (prog₃ Γo) (oE Γo) yc) (Γ' (prog₃ Γo) (oE Γo)).length]
  refine borderLE_of_approx hS (graphs.map comp) _ ?_ f ?_
  · -- the size bound
    intro Γ hΓ
    obtain ⟨Γo, hΓo, rfl⟩ := List.mem_map.1 hΓ
    have hlen : (comp Γo).length = (Γ' (prog₃ Γo) (oE Γo)).length + 1 := by
      simp [comp]
    rw [hlen]
    refine sl_size_arith CN CB C₆ d (Fintype.card κ) (Fintype.card σ) _ Γo.1.length
      (prog₂ Γo).length (prog₃ Γo).length _ (by omega) (by omega) (by omega) ?_ ?_ ?_
      (hΓ'len _ _)
    · have := hgsize Γo hΓo
      have e : d + 1 + Fintype.card κ + M + D.ℓmax + Nat.log 2 D.N + Fintype.card σ + 2 =
          d + Fintype.card κ + M + D.ℓmax + Nat.log 2 D.N + Fintype.card σ + 2 + 1 := by omega
      rwa [e] at this
    · have := hP₂len (prog₁ Γo) (.prev Γo.2)
      simpa [prog₂, prog₁, length_shapeProg] using this
    · exact length_eProg _ _
  · intro η hη
    have hη2 : 0 < η / 2 := half_pos hη
    -- the Taylor coefficients of `Θ(·, ϑ)_y` at `x₁` converge to those of `f`
    have hA : ∀ m, Tendsto (fun ϑ => (taylorPoly d (fun x => W x ϑ yc) x₁).coeff m) (𝓝[>] 0)
        (𝓝 (f.coeff m)) :=
      tendsto_taylor_W Metric.isOpen_ball hx₁B hε' hWD hφD hconv hf yc
        (fun x hx => hG.φ_f x (hK'K (hVsub (hball' hx))))
    have hev : ∀ᶠ ϑ in 𝓝[>] (0 : ℝ), ∀ m ∈ degSet σ d,
        |(taylorPoly d (fun x => W x ϑ yc) x₁).coeff m - f.coeff m| < η / 2 := by
      rw [eventually_all_finset]
      intro m _
      have := (hA m).eventually (Metric.ball_mem_nhds _ hη2)
      filter_upwards [this] with ϑ hϑ
      rwa [Real.dist_eq] at hϑ
    obtain ⟨ϑ, hϑ1, hϑ2⟩ := (hev.and (Ioo_mem_nhdsGT hε')).exists
    have hϑ₂' : ϑ ∈ Ioo 0 ϑ₂ := ⟨hϑ2.1, hϑ2.2.trans_le hε'le⟩
    have hϑ₁' : ϑ ∈ Ioo 0 ϑ₁ := ⟨hϑ2.1, hϑ₂'.2.trans_le hϑ₂₁⟩
    obtain ⟨hc₁Bo, hc₁grad⟩ := hWprop x₁ hx₁V ϑ hϑ₂'
    obtain ⟨han, hHess⟩ := htilt x₁ hx₁V ϑ hϑ₁' (W x₁ ϑ) hc₁Bo hc₁grad
    -- the Taylor polynomial `P` of order `d + 1` of `e` at `ξ₁`, and `E = ∇_c P - ϑ â`
    set ξ₁ : σ ⊕ κ → ℝ := Sum.elim x₁ (W x₁ ϑ) with hξ₁
    set P := taylorPoly (d + 1) D.envξ ξ₁ with hP
    set E : κ → MvPolynomial (σ ⊕ κ) ℝ :=
      fun k => pderiv (Sum.inr k) P - MvPolynomial.C (ϑ * â k) with hE
    set H : Matrix κ κ ℝ :=
      Matrix.of fun k l => pd (pd D.envξ (Sum.inr k)) (Sum.inr l) ξ₁ with hH
    have hdP : ∀ k, pderiv (Sum.inr k) P = taylorPoly d (pd D.envξ (Sum.inr k)) ξ₁ :=
      fun k => pderiv_taylorPoly han d (Sum.inr k)
    have hjac : jacW E ξ₁ = H := by
      ext k l
      have hd' : d = (d - 1) + 1 := by omega
      simp only [jacW, hE, hH, Matrix.of_apply, map_sub, pderiv_C, sub_zero, hdP k]
      rw [hd', pderiv_taylorPoly (analyticAt_pd han _) (d - 1) (Sum.inr l), eval_taylorPoly_self]
    have hAH : H⁻¹ * jacW E (Sum.elim x₁ (W x₁ ϑ)) = 1 := by
      rw [← hξ₁, hjac]; exact Matrix.nonsing_inv_mul H hHess
    -- Newton iteration reproduces the Taylor polynomial of `Θ(·, ϑ)`
    have hWϑ : ContDiffAt ℝ d (fun x => W x ϑ) x₁ :=
      (hWD ϑ hϑ2).contDiffAt (Metric.isOpen_ball.mem_nhds hx₁B)
    have hcrit : ∀ᶠ x in 𝓝 x₁, ∀ l, pd D.envξ (Sum.inr l) (Sum.elim x (W x ϑ)) = ϑ * â l := by
      have h1 : ∀ᶠ ξ in 𝓝 ξ₁, AnalyticAt ℝ D.envξ ξ := han.eventually_analyticAt
      have hcont : ContinuousAt (fun x => Sum.elim x (W x ϑ)) x₁ := by
        refine continuousAt_pi.2 fun i => ?_
        rcases i with i | k
        · exact (continuous_apply i).continuousAt
        · exact (continuousAt_pi.1 hWϑ.continuousAt) k
      filter_upwards [hcont.tendsto.eventually h1, Metric.isOpen_ball.mem_nhds hx₁B] with x hx hxB
      intro l
      have hxV : x ∈ Metric.ball xV rV := hball' hxB
      have hxK : x ∈ D.K := hK'K (hVsub hxV)
      rw [← hG.grad_eq_pd hxK hx.differentiableAt l]
      exact (hWprop x hxV ϑ hϑ₂').2 l
    have hnewton : newtonPoly E x₁ (W x₁ ϑ) H⁻¹ d yc = taylorPoly d (fun x => W x ϑ yc) x₁ := by
      refine newtonPoly_eq_of_isLittleO E x₁ (W x₁ ϑ) H⁻¹ d hAH
        (fun k => taylorPoly d (fun x => W x ϑ k) x₁) (fun k => totalDegree_taylorPoly_le _ _ _)
        (fun k => eval_taylorPoly_self _ _ _) (fun l => ?_) yc
      have := taylor_residual (e := D.envξ) (W := fun x => W x ϑ) han hWϑ hd
        (fun l => ϑ * â l) hcrit l
      simp only [hE, hdP l]
      exact this
    -- approximation of `P` by outputs of one of the graphs of Lemma 6.6
    have happrox : ∃ Γo ∈ graphs, ∀ η' > 0, ∃ a : ℕ → ℝ,
        ((Γo.1.values a).getD Γo.2 0).totalDegree ≤ d + 1 ∧
        ∀ m, |((Γo.1.values a).getD Γo.2 0).coeff m - P.coeff m| < η' := by
      refine exists_forall_of_list graphs _ (fun Γo η' η'' hle ⟨a, ha1, ha2⟩ =>
        ⟨a, ha1, fun m => (ha2 m).trans_le hle⟩) ?_
      intro η' hη'
      have hev' : ∀ᶠ ξ in 𝓝 ξ₁, ∀ m ∈ degSet (σ ⊕ κ) (d + 1),
          |(taylorPoly (d + 1) D.envξ ξ).coeff m - P.coeff m| < η' / 2 := by
        rw [eventually_all_finset]
        intro m _
        have := (tendsto_coeff_taylorPoly_base han (d + 1) m).eventually
          (Metric.ball_mem_nhds _ (half_pos hη'))
        filter_upwards [this] with ξ hξ
        rwa [Real.dist_eq] at hξ
      obtain ⟨ξ, hξ, hξO⟩ := mem_closure_iff_nhds.1 (hO₀dense (hx₁OK (W x₁ ϑ))) _ hev'
      obtain ⟨-, Γo, hΓo, hΓoA⟩ := hO₀ ξ hξO
      obtain ⟨a, ha1, ha2⟩ := hΓoA (η' / 2) (half_pos hη')
      refine ⟨Γo, hΓo, a, ha1, fun m => ?_⟩
      by_cases hm : m ∈ degSet (σ ⊕ κ) (d + 1)
      · have h1 := ha2 m
        have h2 := hξ m hm
        calc _ ≤ |((Γo.1.values a).getD Γo.2 0).coeff m -
              (taylorPoly (d + 1) D.envξ ξ).coeff m| +
              |(taylorPoly (d + 1) D.envξ ξ).coeff m - P.coeff m| := abs_sub_le _ _ _
          _ < η' / 2 + η' / 2 := add_lt_add h1 h2
          _ = η' := add_halves η'
      · rw [coeff_eq_zero_of_notMem_degSet ha1 hm,
          coeff_eq_zero_of_notMem_degSet (totalDegree_taylorPoly_le _ _ _) hm]
        simpa using hη'
    obtain ⟨Γo, hΓo, hΓoA⟩ := happrox
    choose a ha1 ha2 using fun j : ℕ => hΓoA (1 / ((j : ℝ) + 1)) (by positivity)
    set Ψ : ℕ → MvPolynomial (σ ⊕ κ) ℝ := fun j => (Γo.1.values (a j)).getD Γo.2 0 with hΨ
    have hΨt : ∀ m, Tendsto (fun j => (Ψ j).coeff m) atTop (𝓝 (P.coeff m)) := by
      intro m
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun j => norm_nonneg _) (fun j => ?_)
        tendsto_one_div_add_atTop_nhds_zero_nat
      rw [Real.norm_eq_abs]
      exact (ha2 j m).le
    set Ej : ℕ → κ → MvPolynomial (σ ⊕ κ) ℝ :=
      fun j k => pderiv (Sum.inr k) (Ψ j) - MvPolynomial.C (ϑ * â k) with hEj
    have hEjt : ∀ k m, Tendsto (fun j => (Ej j k).coeff m) atTop (𝓝 ((E k).coeff m)) := by
      intro k m
      simp only [hEj, hE, MvPolynomial.coeff_sub, coeff_pderiv]
      exact ((hΨt _).mul_const _).sub tendsto_const_nhds
    have hEjdeg : ∀ j k, (Ej j k).totalDegree ≤ d + 1 := fun j k =>
      (totalDegree_sub _ _).trans (max_le ((totalDegree_pderiv_le _ _).trans (ha1 j))
        (by rw [totalDegree_C]; exact Nat.zero_le _))
    have hEdeg : ∀ k, (E k).totalDegree ≤ d + 1 := fun k =>
      (totalDegree_sub _ _).trans (max_le ((totalDegree_pderiv_le _ _).trans
        (totalDegree_taylorPoly_le _ _ _)) (by rw [totalDegree_C]; exact Nat.zero_le _))
    have hNt : ∀ m, Tendsto (fun j => (newtonPoly (Ej j) x₁ (W x₁ ϑ) H⁻¹ d yc).coeff m) atTop
        (𝓝 ((newtonPoly E x₁ (W x₁ ϑ) H⁻¹ d yc).coeff m)) := fun m =>
      tendsto_coeff_newtonPoly (Eb := Ej) (ξb := fun _ => x₁) (wb := fun _ => W x₁ ϑ)
        (Ab := fun _ => H⁻¹) (d + 1) hEjdeg hEdeg hEjt tendsto_const_nhds tendsto_const_nhds
        tendsto_const_nhds d yc m
    have hev3 : ∀ᶠ j in atTop, ∀ m ∈ degSet σ d,
        |(newtonPoly (Ej j) x₁ (W x₁ ϑ) H⁻¹ d yc).coeff m -
          (newtonPoly E x₁ (W x₁ ϑ) H⁻¹ d yc).coeff m| < η / 2 := by
      rw [eventually_all_finset]
      intro m _
      have := (hNt m).eventually (Metric.ball_mem_nhds _ hη2)
      filter_upwards [this] with j hj
      rwa [Real.dist_eq] at hj
    obtain ⟨j, hj⟩ := hev3.exists
    -- the composite graph computes `newtonPoly (Ej j) ...`
    set c₃ : ℕ → ℝ :=
      eConst (cmap (prog₁ Γo) (.prev Γo.2) (shapeConst (a j))) (fun k => ϑ * â k) with hc₃
    refine ⟨comp Γo, List.mem_map_of_mem hΓo, enc (prog₃ Γo) (oE Γo) c₃ x₁ (W x₁ ϑ) H⁻¹,
      newtonPoly (Ej j) x₁ (W x₁ ϑ) H⁻¹ d yc, ?_, ?_⟩
    · have hc := computes_append_add (Γ' (prog₃ Γo) (oE Γo))
        (enc (prog₃ Γo) (oE Γo) c₃ x₁ (W x₁ ϑ) H⁻¹) (out (prog₃ Γo) (oE Γo) yc)
      rw [hΓ' (prog₃ Γo) (oE Γo) c₃ x₁ (W x₁ ϑ) H⁻¹ yc] at hc
      have hprog : progOutputs (prog₃ Γo) c₃ (oE Γo) = Ej j := by
        funext k
        rw [progOutputs_eProg, (hP₂ (prog₁ Γo) (.prev Γo.2) (shapeConst (a j))).2 (Sum.inr k),
          progOutput_shapeProg]
      rw [hprog] at hc
      exact hc
    · intro m
      by_cases hm : m ∈ degSet σ d
      · have h1 := hj m hm
        have h2 := hϑ1 m hm
        rw [hnewton] at h1
        calc |(newtonPoly (Ej j) x₁ (W x₁ ϑ) H⁻¹ d yc).coeff m - f.coeff m|
            ≤ |(newtonPoly (Ej j) x₁ (W x₁ ϑ) H⁻¹ d yc).coeff m -
                (taylorPoly d (fun x => W x ϑ yc) x₁).coeff m| +
              |(taylorPoly d (fun x => W x ϑ yc) x₁).coeff m - f.coeff m| := abs_sub_le _ _ _
          _ < η / 2 + η / 2 := add_lt_add h1 h2
          _ = η := add_halves η
      · rw [coeff_eq_zero_of_notMem_degSet (totalDegree_newtonPoly_le _ _ _ _ _ _) hm,
          coeff_eq_zero_of_notMem_degSet hf hm]
        simpa using hη

end ClassSep
