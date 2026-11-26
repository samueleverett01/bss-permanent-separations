import ClassSeparations.Analysis.Taylor
import ClassSeparations.Basic.Circuits

/-!
# Newton iteration as a circuit (§3.3, Lemma 3.4)

Let `ℛ = ℝ[χ][τ]/(τ^{D+1})`.  For polynomials `E = (E₁, …, E_κ)` in `(ξ, w) ∈ ℝᴺ × ℝ^κ`, a
point `(ξ₁, w₁)` and a matrix `A`, put `Ω⁽⁰⁾ = w₁` and
`Ω⁽ʲ⁺¹⁾ = Ω⁽ʲ⁾ - A E(ξ₁ + τχ, Ω⁽ʲ⁾)` in `ℛ^κ`, and let `gᵢ ∈ ℝ[ξ]` be the sum of the `D + 1`
coefficients of `Ωᵢ⁽ᴰ⁾` with `χ = ξ - ξ₁` substituted.

Every element formed in this iteration has its coefficient of `τʲ` homogeneous of degree `j`
in `χ`; summing the coefficients identifies such elements with polynomials in `χ` of degree
`≤ D`, multiplied with truncation of the total degree at `D`.  We define `newtonPoly` in this
second form, and the circuit of part (a) computes it in the first form.

**Lemma 3.4.**
(a) The `gᵢ` are computed by a circuit with at most `C((D+1)³ℓ + (D+1)²κ² + N)` gates plus the
constants of the program, whose graph depends only on the graph of the program and on `N`,
`κ`, `D`; each `gᵢ` has degree at most `D`; the coefficients of the `gᵢ` are polynomial
functions of the coefficients of `E` and of `ξ₁, w₁, A`.
(b) If `E(ξ₁, w₁) = 0` and `A` is the inverse of `∂_w E(ξ₁, w₁)`, and `ω` is a map with
`ω(ξ₁) = w₁` and `E(ξ, ω(ξ)) = 0` near `ξ₁` that is of class `C^D` at `ξ₁` (for instance the
analytic implicit function), then `gᵢ` is the Taylor polynomial of order `D` of `ωᵢ` at `ξ₁`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open MvPolynomial Filter Topology

namespace ClassSep

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Truncation of a polynomial to its monomials of total degree at most `D`. -/
def truncDeg (D : ℕ) (p : MvPolynomial ι ℝ) : MvPolynomial ι ℝ :=
  ∑ m ∈ p.support.filter (fun m => m.degree ≤ D), monomial m (p.coeff m)

/-- One Newton step in `ℝ[χ]` with truncation at total degree `D`:
`Ω ↦ trunc_D (Ω - A · E(ξ₁ + χ, Ω))`. -/
def newtonStep (E : κ → MvPolynomial (ι ⊕ κ) ℝ) (ξ₁ : ι → ℝ) (A : Matrix κ κ ℝ) (D : ℕ)
    (Ω : κ → MvPolynomial ι ℝ) : κ → MvPolynomial ι ℝ :=
  fun k => truncDeg D (Ω k - ∑ l, MvPolynomial.C (A k l) *
    bind₁ (Sum.elim (fun i => MvPolynomial.C (ξ₁ i) + X i) Ω) (E l))

/-- The output `(g₁, …, g_κ)` of Lemma 3.4, as polynomials in `ξ`. -/
def newtonPoly (E : κ → MvPolynomial (ι ⊕ κ) ℝ) (ξ₁ : ι → ℝ) (w₁ : κ → ℝ) (A : Matrix κ κ ℝ)
    (D : ℕ) : κ → MvPolynomial ι ℝ :=
  fun k => bind₁ (fun i => X i - MvPolynomial.C (ξ₁ i))
    ((newtonStep E ξ₁ A D)^[D] (fun l => MvPolynomial.C (w₁ l)) k)

/-- The Jacobian matrix `∂_w E` at a point. -/
def jacW (E : κ → MvPolynomial (ι ⊕ κ) ℝ) (p : ι ⊕ κ → ℝ) : Matrix κ κ ℝ :=
  fun k l => eval p (pderiv (Sum.inr l) (E k))

/-- The polynomials computed by a program graph `prog` at output operands `o`, with constants
`c`. -/
def progOutputs {σ : Type} (prog : SLP σ ℕ) (c : ℕ → ℝ) {β : Type} (o : β → Operand σ ℕ) :
    β → MvPolynomial σ ℝ :=
  fun b => (o b).instantiate c |>.eval (prog.instantiate c).values

/-! ### Truncation and degrees -/

theorem coeff_add' {σ : Type*} (m : σ →₀ ℕ) (p q : MvPolynomial σ ℝ) :
    (p + q).coeff m = p.coeff m + q.coeff m := by simp

theorem coeff_zero' {σ : Type*} (m : σ →₀ ℕ) : (0 : MvPolynomial σ ℝ).coeff m = 0 := by simp

theorem coeff_truncDeg (D : ℕ) (p : MvPolynomial ι ℝ) (m : ι →₀ ℕ) :
    (truncDeg D p).coeff m = if m.degree ≤ D then p.coeff m else 0 := by
  classical
  unfold truncDeg
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  by_cases hm : m ∈ p.support
  · simp [Finset.mem_filter, hm]
  · have h0 : p.coeff m = 0 := by simpa using hm
    simp [Finset.mem_filter, hm, h0]

theorem totalDegree_truncDeg_le (D : ℕ) (p : MvPolynomial ι ℝ) :
    (truncDeg D p).totalDegree ≤ D := by
  unfold truncDeg
  refine totalDegree_finsetSum_le fun m hm => ?_
  refine (totalDegree_monomial_le _ _).trans ?_
  rw [Finset.mem_filter] at hm
  exact hm.2

theorem totalDegree_bind₁_le {σ τ : Type*} (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ i, (f i).totalDegree ≤ 1) (p : MvPolynomial σ ℝ) :
    (bind₁ f p).totalDegree ≤ p.totalDegree := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine totalDegree_finsetSum_le fun d hd => ?_
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine le_trans ?_ (le_totalDegree hd)
  refine Finset.sum_le_sum fun i _ => ?_
  refine (totalDegree_pow _ _).trans ?_
  calc d i * (f i).totalDegree ≤ d i * 1 := Nat.mul_le_mul_left _ (hf i)
    _ = d i := mul_one _

theorem totalDegree_X_sub_C_le (i : ι) (a : ℝ) :
    (X i - MvPolynomial.C a : MvPolynomial ι ℝ).totalDegree ≤ 1 :=
  (totalDegree_sub_C_le _ _).trans (by rw [totalDegree_X])

theorem totalDegree_X_add_C_le (i : ι) (a : ℝ) :
    (X i + MvPolynomial.C a : MvPolynomial ι ℝ).totalDegree ≤ 1 := by
  refine (totalDegree_add _ _).trans ?_
  rw [totalDegree_X, totalDegree_C]; simp

theorem totalDegree_iterate_newtonStep_le (E : κ → MvPolynomial (ι ⊕ κ) ℝ) (ξ₁ : ι → ℝ)
    (w₁ : κ → ℝ) (A : Matrix κ κ ℝ) (D n : ℕ) (k : κ) :
    ((newtonStep E ξ₁ A D)^[n] (fun l => MvPolynomial.C (w₁ l)) k).totalDegree ≤ D := by
  cases n with
  | zero => simp [totalDegree_C]
  | succ n =>
    rw [Function.iterate_succ_apply']
    exact totalDegree_truncDeg_le _ _

/-- **Lemma 3.4 (a)**: degree bound. -/
theorem totalDegree_newtonPoly_le (E : κ → MvPolynomial (ι ⊕ κ) ℝ) (ξ₁ : ι → ℝ) (w₁ : κ → ℝ)
    (A : Matrix κ κ ℝ) (D : ℕ) (k : κ) : (newtonPoly E ξ₁ w₁ A D k).totalDegree ≤ D :=
  (totalDegree_bind₁_le _ (fun i => totalDegree_X_sub_C_le i _) _).trans
    (totalDegree_iterate_newtonStep_le E ξ₁ w₁ A D D k)

/-! ### Circuit building blocks -/

section CircuitBasics

variable {σ : Type}

/-- The gate refers only to gates with index `< L`. -/
def Gate.RefsLt (L : ℕ) : Gate σ → Prop
  | .var _ => True
  | .const _ => True
  | .add j k => j < L ∧ k < L
  | .mul j k => j < L ∧ k < L

/-- The step function of `Shape.values`. -/
def valStep (c : ℕ → ℝ) (vals : List (MvPolynomial σ ℝ)) (g : Gate σ) :
    List (MvPolynomial σ ℝ) :=
  vals ++ [g.eval c vals]

theorem values_eq_foldl (Γ : Shape σ) (c : ℕ → ℝ) : Γ.values c = Γ.foldl (valStep c) [] := rfl

theorem foldl_valStep_prefix (c : ℕ → ℝ) (G : List (Gate σ)) :
    ∀ V, V <+: G.foldl (valStep c) V := by
  induction G with
  | nil => intro V; exact List.prefix_refl V
  | cons g G ih => intro V; exact (List.prefix_append V _).trans (ih _)

theorem length_foldl_valStep (c : ℕ → ℝ) (G : List (Gate σ)) :
    ∀ V, (G.foldl (valStep c) V).length = V.length + G.length := by
  induction G with
  | nil => intro V; simp
  | cons g G ih => intro V; simp [ih, valStep]; omega

theorem length_values (Γ : Shape σ) (c : ℕ → ℝ) : (Γ.values c).length = Γ.length := by
  simp [values_eq_foldl, length_foldl_valStep]

theorem Gate.eval_append (c : ℕ → ℝ) (V W : List (MvPolynomial σ ℝ)) (g : Gate σ)
    (hg : g.RefsLt V.length) : g.eval c (V ++ W) = g.eval c V := by
  cases g with
  | var i => rfl
  | const k => rfl
  | add j k =>
    simp only [Gate.eval, List.getD_append _ _ _ _ hg.1, List.getD_append _ _ _ _ hg.2]
  | mul j k =>
    simp only [Gate.eval, List.getD_append _ _ _ _ hg.1, List.getD_append _ _ _ _ hg.2]

theorem foldl_valStep_layer (c : ℕ → ℝ) (V : List (MvPolynomial σ ℝ)) (G : List (Gate σ))
    (hG : ∀ g ∈ G, g.RefsLt V.length) :
    ∀ W, G.foldl (valStep c) (V ++ W) = V ++ W ++ G.map (Gate.eval c V) := by
  induction G with
  | nil => intro W; simp
  | cons g G ih =>
    intro W
    simp only [List.foldl_cons, valStep]
    rw [Gate.eval_append c V W g (hG g (by simp)), List.append_assoc,
      ih (fun g hg => hG g (by simp [hg])) (W ++ [g.eval c V])]
    simp

theorem values_append_layer (Γ G : Shape σ) (c : ℕ → ℝ) (hG : ∀ g ∈ G, g.RefsLt Γ.length) :
    (Γ ++ G).values c = Γ.values c ++ G.map (Gate.eval c (Γ.values c)) := by
  rw [values_eq_foldl, List.foldl_append, ← values_eq_foldl]
  have := foldl_valStep_layer c (Γ.values c) G (by rwa [length_values]) []
  simpa using this

/-- Gate `n` of `Γ` computes `p` (for the constants `c`). -/
def Holds (Γ : Shape σ) (c : ℕ → ℝ) (n : ℕ) (p : MvPolynomial σ ℝ) : Prop :=
  n < Γ.length ∧ (Γ.values c).getD n 0 = p

theorem Holds.mono {Γ Γ' : Shape σ} {c : ℕ → ℝ} {n : ℕ} {p : MvPolynomial σ ℝ}
    (h : Holds Γ c n p) (hΓ : Γ <+: Γ') : Holds Γ' c n p := by
  obtain ⟨G, rfl⟩ := hΓ
  refine ⟨by have := h.1; simp; omega, ?_⟩
  rw [values_eq_foldl, List.foldl_append, ← values_eq_foldl]
  obtain ⟨W, hW⟩ := foldl_valStep_prefix c G (Γ.values c)
  rw [← hW, List.getD_append _ _ _ _ (by rw [length_values]; exact h.1)]
  exact h.2

theorem Holds.eval_add {Γ : Shape σ} {c : ℕ → ℝ} {i j : ℕ} {p q : MvPolynomial σ ℝ}
    (hi : Holds Γ c i p) (hj : Holds Γ c j q) :
    (Gate.add i j : Gate σ).eval c (Γ.values c) = p + q := by
  simp only [Gate.eval]; rw [hi.2, hj.2]

theorem Holds.eval_mul {Γ : Shape σ} {c : ℕ → ℝ} {i j : ℕ} {p q : MvPolynomial σ ℝ}
    (hi : Holds Γ c i p) (hj : Holds Γ c j q) :
    (Gate.mul i j : Gate σ).eval c (Γ.values c) = p * q := by
  simp only [Gate.eval]; rw [hi.2, hj.2]

/-- Append a layer of gates which only refer to earlier gates. -/
def layerF (Γ : Shape σ) {m : ℕ} (f : Fin m → Gate σ) : Shape σ := Γ ++ List.ofFn f

theorem length_layerF (Γ : Shape σ) {m : ℕ} (f : Fin m → Gate σ) :
    (layerF Γ f).length = Γ.length + m := by simp [layerF]

theorem prefix_layerF (Γ : Shape σ) {m : ℕ} (f : Fin m → Gate σ) : Γ <+: layerF Γ f :=
  List.prefix_append _ _

theorem holds_layerF (Γ : Shape σ) {m : ℕ} (f : Fin m → Gate σ) (c : ℕ → ℝ)
    (hf : ∀ t, (f t).RefsLt Γ.length) (t : Fin m) :
    Holds (layerF Γ f) c (Γ.length + t) ((f t).eval c (Γ.values c)) := by
  refine ⟨by simp [layerF], ?_⟩
  have hG : ∀ g ∈ List.ofFn f, g.RefsLt Γ.length := by
    intro g hg
    obtain ⟨t, rfl⟩ := List.mem_ofFn.1 hg
    exact hf t
  rw [layerF, values_append_layer Γ _ c hG,
    List.getD_append_right _ _ _ _ (by rw [length_values]; omega), length_values,
    Nat.add_sub_cancel_left, List.getD_eq_getElem _ _ (by simp)]
  simp

/-- Append a layer of gates indexed by a finite type. -/
def layer {α : Type*} [Fintype α] (Γ : Shape σ) (f : α → Gate σ) : Shape σ :=
  layerF Γ (fun t => f ((Fintype.equivFin α).symm t))

/-- Position of the gate of index `a` in a layer starting at `L`. -/
def lidx {α : Type*} [Fintype α] (L : ℕ) (a : α) : ℕ := L + (Fintype.equivFin α a : ℕ)

theorem length_layer {α : Type*} [Fintype α] (Γ : Shape σ) (f : α → Gate σ) :
    (layer Γ f).length = Γ.length + Fintype.card α := length_layerF _ _

theorem prefix_layer {α : Type*} [Fintype α] (Γ : Shape σ) (f : α → Gate σ) :
    Γ <+: layer Γ f := prefix_layerF _ _

theorem holds_layer {α : Type*} [Fintype α] (Γ : Shape σ) (f : α → Gate σ) (c : ℕ → ℝ)
    (hf : ∀ a, (f a).RefsLt Γ.length) (a : α) :
    Holds (layer Γ f) c (lidx Γ.length a) ((f a).eval c (Γ.values c)) := by
  have := holds_layerF Γ (fun t => f ((Fintype.equivFin α).symm t)) c
    (fun t => hf _) (Fintype.equivFin α a)
  simpa [layer, lidx] using this

/-- A block of gates holds the components `v 0, …, v D`. -/
def HoldsB (D : ℕ) (Γ : Shape σ) (c : ℕ → ℝ) (b : ℕ → ℕ) (v : ℕ → MvPolynomial σ ℝ) : Prop :=
  ∀ j ≤ D, Holds Γ c (b j) (v j)

theorem HoldsB.mono {D : ℕ} {Γ Γ' : Shape σ} {c : ℕ → ℝ} {b : ℕ → ℕ}
    {v : ℕ → MvPolynomial σ ℝ} (h : HoldsB D Γ c b v) (hΓ : Γ <+: Γ') : HoldsB D Γ' c b v :=
  fun j hj => (h j hj).mono hΓ

theorem HoldsB.congr {D : ℕ} {Γ : Shape σ} {c : ℕ → ℝ} {b : ℕ → ℕ}
    {v v' : ℕ → MvPolynomial σ ℝ} (h : HoldsB D Γ c b v) (hv : ∀ j ≤ D, v j = v' j) :
    HoldsB D Γ c b v' :=
  fun j hj => hv j hj ▸ h j hj

/-- Componentwise sum of two blocks. -/
def addB (D : ℕ) (Γ : Shape σ) (x y : ℕ → ℕ) : Shape σ × (ℕ → ℕ) :=
  (layerF Γ (fun t : Fin (D + 1) => .add (x t) (y t)), fun j => Γ.length + j)

theorem addB_spec {D : ℕ} {Γ : Shape σ} {c : ℕ → ℝ} {x y : ℕ → ℕ}
    {u v : ℕ → MvPolynomial σ ℝ} (hx : HoldsB D Γ c x u) (hy : HoldsB D Γ c y v) :
    Γ <+: (addB D Γ x y).1 ∧ (addB D Γ x y).1.length = Γ.length + (D + 1) ∧
      HoldsB D (addB D Γ x y).1 c (addB D Γ x y).2 (fun j => u j + v j) := by
  refine ⟨prefix_layerF _ _, length_layerF _ _, fun j hj => ?_⟩
  have := holds_layerF Γ (fun t : Fin (D + 1) => .add (x t) (y t)) c
    (fun t => ⟨(hx t (by omega)).1, (hy t (by omega)).1⟩) ⟨j, by omega⟩
  rw [(hx j hj).eval_add (hy j hj)] at this
  exact this

/-- Multiplication of a block by the value of a gate. -/
def scaleB (D : ℕ) (Γ : Shape σ) (s : ℕ) (x : ℕ → ℕ) : Shape σ × (ℕ → ℕ) :=
  (layerF Γ (fun t : Fin (D + 1) => .mul s (x t)), fun j => Γ.length + j)

theorem scaleB_spec {D : ℕ} {Γ : Shape σ} {c : ℕ → ℝ} {s : ℕ} {a : MvPolynomial σ ℝ}
    {x : ℕ → ℕ} {u : ℕ → MvPolynomial σ ℝ} (hs : Holds Γ c s a) (hx : HoldsB D Γ c x u) :
    Γ <+: (scaleB D Γ s x).1 ∧ (scaleB D Γ s x).1.length = Γ.length + (D + 1) ∧
      HoldsB D (scaleB D Γ s x).1 c (scaleB D Γ s x).2 (fun j => a * u j) := by
  refine ⟨prefix_layerF _ _, length_layerF _ _, fun j hj => ?_⟩
  have := holds_layerF Γ (fun t : Fin (D + 1) => .mul s (x t)) c
    (fun t => ⟨hs.1, (hx t (by omega)).1⟩) ⟨j, by omega⟩
  rw [hs.eval_mul (hx j hj)] at this
  exact this

/-- One step of the truncated product of two blocks: add the products `x a * y (j - a)`. -/
def mulStep (D : ℕ) (x y : ℕ → ℕ) (z : ℕ) (a : ℕ) (st : Shape σ × (ℕ → ℕ)) :
    Shape σ × (ℕ → ℕ) :=
  let Γ1 := layerF st.1 (fun t : Fin (D + 1) => .mul (x a) (y t))
  (layerF Γ1 (fun t : Fin (D + 1) =>
      .add (st.2 t) (if a ≤ (t : ℕ) then st.1.length + ((t : ℕ) - a) else z)),
    fun j => Γ1.length + j)

/-- The first `a` steps of the truncated product. -/
def mulAux (D : ℕ) (Γ : Shape σ) (x y : ℕ → ℕ) (z : ℕ) : ℕ → Shape σ × (ℕ → ℕ)
  | 0 => (Γ, fun _ => z)
  | a + 1 => mulStep D x y z a (mulAux D Γ x y z a)

theorem mulAux_spec {D : ℕ} {Γ : Shape σ} {c : ℕ → ℝ} {x y : ℕ → ℕ} {z : ℕ}
    {u v : ℕ → MvPolynomial σ ℝ} (hx : HoldsB D Γ c x u) (hy : HoldsB D Γ c y v)
    (hz : Holds Γ c z 0) (a : ℕ) (ha : a ≤ D + 1) :
    Γ <+: (mulAux D Γ x y z a).1 ∧
      (mulAux D Γ x y z a).1.length = Γ.length + a * (2 * (D + 1)) ∧
      HoldsB D (mulAux D Γ x y z a).1 c (mulAux D Γ x y z a).2
        (fun j => ∑ a' ∈ Finset.range a, if a' ≤ j then u a' * v (j - a') else 0) := by
  induction a with
  | zero =>
    refine ⟨List.prefix_refl _, by simp [mulAux], fun j hj => ?_⟩
    simpa [mulAux] using hz
  | succ a ih =>
    obtain ⟨h1, h2, h3⟩ := ih (by omega)
    set Γa := (mulAux D Γ x y z a).1
    set Sa := (mulAux D Γ x y z a).2
    have hxa : Holds Γa c (x a) (u a) := (hx a (by omega)).mono h1
    have hyb : HoldsB D Γa c y v := hy.mono h1
    have hzb : Holds Γa c z 0 := hz.mono h1
    set Γ1 := layerF Γa (fun t : Fin (D + 1) => .mul (x a) (y t)) with hΓ1
    have hP : ∀ b ≤ D, Holds Γ1 c (Γa.length + b) (u a * v b) := by
      intro b hb
      have := holds_layerF Γa (fun t : Fin (D + 1) => .mul (x a) (y t)) c
        (fun t => ⟨hxa.1, (hyb t (by omega)).1⟩) ⟨b, by omega⟩
      rw [hxa.eval_mul (hyb b hb)] at this
      exact this
    have hS : HoldsB D Γ1 c Sa
        (fun j => ∑ a' ∈ Finset.range a, if a' ≤ j then u a' * v (j - a') else 0) :=
      h3.mono (prefix_layerF _ _)
    have hz1 : Holds Γ1 c z 0 := hzb.mono (prefix_layerF _ _)
    have hT : ∀ j ≤ D, Holds Γ1 c (if a ≤ j then Γa.length + (j - a) else z)
        (if a ≤ j then u a * v (j - a) else 0) := by
      intro j hj
      split_ifs with haj
      · exact hP _ (by omega)
      · exact hz1
    have hpre : Γa <+: Γ1 := prefix_layerF _ _
    have hlen1 : Γ1.length = Γa.length + (D + 1) := length_layerF _ _
    refine ⟨h1.trans (hpre.trans (prefix_layerF _ _)), ?_, fun j hj => ?_⟩
    · show (layerF Γ1 _).length = _
      rw [length_layerF, hlen1, h2]
      ring
    · have := holds_layerF Γ1 (fun t : Fin (D + 1) =>
        .add (Sa t) (if a ≤ (t : ℕ) then Γa.length + ((t : ℕ) - a) else z)) c
        (fun t => ⟨(hS t (by omega)).1, (hT t (by omega)).1⟩) ⟨j, by omega⟩
      rw [(hS j hj).eval_add (hT j hj)] at this
      have e : (∑ a' ∈ Finset.range (a + 1), if a' ≤ j then u a' * v (j - a') else 0) =
          (∑ a' ∈ Finset.range a, if a' ≤ j then u a' * v (j - a') else 0) +
            (if a ≤ j then u a * v (j - a) else 0) := Finset.sum_range_succ _ _
      show Holds (layerF Γ1 _) c (Γ1.length + j)
        (∑ a' ∈ Finset.range (a + 1), if a' ≤ j then u a' * v (j - a') else 0)
      rw [e]
      exact this

/-- Truncated product of two blocks. -/
def mulB (D : ℕ) (Γ : Shape σ) (x y : ℕ → ℕ) (z : ℕ) : Shape σ × (ℕ → ℕ) :=
  mulAux D Γ x y z (D + 1)

theorem mulB_spec {D : ℕ} {Γ : Shape σ} {c : ℕ → ℝ} {x y : ℕ → ℕ} {z : ℕ}
    {u v : ℕ → MvPolynomial σ ℝ} (hx : HoldsB D Γ c x u) (hy : HoldsB D Γ c y v)
    (hz : Holds Γ c z 0) :
    Γ <+: (mulB D Γ x y z).1 ∧
      (mulB D Γ x y z).1.length = Γ.length + (D + 1) * (2 * (D + 1)) ∧
      HoldsB D (mulB D Γ x y z).1 c (mulB D Γ x y z).2
        (fun j => ∑ a ∈ Finset.range (j + 1), u a * v (j - a)) := by
  obtain ⟨h1, h2, h3⟩ := mulAux_spec hx hy hz (D + 1) le_rfl
  refine ⟨h1, h2, h3.congr fun j hj => ?_⟩
  rw [← Finset.sum_subset (Finset.range_subset_range.2 (by omega : j + 1 ≤ D + 1))]
  · refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.mem_range] at ha
    rw [ite_eq_left (by omega)]
  · intro a _ ha
    rw [Finset.mem_range] at ha
    rw [ite_eq_right (by omega)]

end CircuitBasics

/-! ### The graded representation of `ℝ[χ][τ]/(τ^{D+1})` -/

theorem homogeneousComponent_mul' {σ : Type*} (s t : MvPolynomial σ ℝ) (j : ℕ) :
    homogeneousComponent j (s * t) =
      ∑ a ∈ Finset.range (j + 1), homogeneousComponent a s * homogeneousComponent (j - a) t := by
  classical
  ext m
  rw [coeff_homogeneousComponent, coeff_sum]
  simp only [coeff_mul, coeff_homogeneousComponent]
  rw [Finset.sum_comm]
  split_ifs with hm
  · refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    have hdeg : x.1.degree + x.2.degree = j := by rw [← map_add, hx, hm]
    rw [Finset.sum_eq_single x.1.degree]
    · rw [ite_eq_left rfl, ite_eq_left (by omega)]
    · intro a _ ha
      rw [ite_eq_right (Ne.symm ha), zero_mul]
    · intro h
      exact absurd (Finset.mem_range.2 (by omega)) h
  · symm
    refine Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun a ha => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [Finset.mem_range] at ha
    by_cases h1 : x.1.degree = a
    · by_cases h2 : x.2.degree = j - a
      · exfalso
        apply hm
        rw [← hx, map_add, h1, h2]
        omega
      · rw [ite_eq_right h2, mul_zero]
    · rw [ite_eq_right h1, zero_mul]

/-- The coefficient of `τʲ` of the element `s(τχ)` of `ℝ[χ][τ]/(τ^{D+1})`, i.e. the
homogeneous component of degree `j` of `s ∈ ℝ[χ]`, written in `ξ = ξ₁ + χ`. -/
def rep (ξ₁ : ι → ℝ) (s : MvPolynomial ι ℝ) (j : ℕ) : MvPolynomial ι ℝ :=
  bind₁ (fun i => X i - MvPolynomial.C (ξ₁ i)) (homogeneousComponent j s)

theorem rep_add (ξ₁ : ι → ℝ) (s t : MvPolynomial ι ℝ) (j : ℕ) :
    rep ξ₁ (s + t) j = rep ξ₁ s j + rep ξ₁ t j := by
  simp [rep]

theorem rep_sub (ξ₁ : ι → ℝ) (s t : MvPolynomial ι ℝ) (j : ℕ) :
    rep ξ₁ (s - t) j = rep ξ₁ s j - rep ξ₁ t j := by
  simp [rep]

theorem rep_zero (ξ₁ : ι → ℝ) (j : ℕ) : rep ξ₁ 0 j = 0 := by
  simp [rep]

theorem rep_C_mul (ξ₁ : ι → ℝ) (a : ℝ) (s : MvPolynomial ι ℝ) (j : ℕ) :
    rep ξ₁ (MvPolynomial.C a * s) j = MvPolynomial.C a * rep ξ₁ s j := by
  simp [rep]

theorem rep_mul (ξ₁ : ι → ℝ) (s t : MvPolynomial ι ℝ) (j : ℕ) :
    rep ξ₁ (s * t) j = ∑ a ∈ Finset.range (j + 1), rep ξ₁ s a * rep ξ₁ t (j - a) := by
  simp only [rep, homogeneousComponent_mul', map_sum, map_mul]

theorem rep_C (ξ₁ : ι → ℝ) (a : ℝ) (j : ℕ) :
    rep ξ₁ (MvPolynomial.C a) j = if j = 0 then MvPolynomial.C a else 0 := by
  rw [rep, homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 (isHomogeneous_C ι a))]
  split_ifs <;> simp

theorem rep_X (ξ₁ : ι → ℝ) (i : ι) (j : ℕ) :
    rep ξ₁ (X i) j = if j = 1 then X i - MvPolynomial.C (ξ₁ i) else 0 := by
  rw [rep, homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 (isHomogeneous_X ℝ i))]
  split_ifs <;> simp

theorem rep_xi (ξ₁ : ι → ℝ) (i : ι) (j : ℕ) :
    rep ξ₁ (MvPolynomial.C (ξ₁ i) + X i) j =
      if j = 0 then MvPolynomial.C (ξ₁ i) else if j = 1 then X i - MvPolynomial.C (ξ₁ i)
        else 0 := by
  rw [rep_add, rep_C, rep_X]
  split_ifs <;> simp_all

theorem rep_truncDeg (ξ₁ : ι → ℝ) {D j : ℕ} (hj : j ≤ D) (s : MvPolynomial ι ℝ) :
    rep ξ₁ (truncDeg D s) j = rep ξ₁ s j := by
  unfold rep
  congr 1
  ext m
  rw [coeff_homogeneousComponent, coeff_homogeneousComponent, coeff_truncDeg]
  split_ifs <;> first | rfl | omega

theorem sum_rep (ξ₁ : ι → ℝ) {D : ℕ} {s : MvPolynomial ι ℝ} (hs : s.totalDegree ≤ D) :
    ∑ j ∈ Finset.range (D + 1), rep ξ₁ s j = bind₁ (fun i => X i - MvPolynomial.C (ξ₁ i)) s := by
  unfold rep
  rw [← map_sum]
  congr 1
  conv_rhs => rw [← sum_homogeneousComponent s]
  symm
  refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun j _ hj => ?_
  rw [Finset.mem_range] at hj
  exact homogeneousComponent_eq_zero _ _ (by omega)

/-! ### The constants of the circuit -/

section Slots

/-- The kinds of constants used by the circuit: `0`, `-1`, the program constants, `ξ₁ᵢ`,
`-ξ₁ᵢ`, `w₁ₖ`, `-Aₖₗ`. -/
abbrev SlotT (ι κ : Type) := Unit ⊕ Unit ⊕ ℕ ⊕ ι ⊕ ι ⊕ κ ⊕ (κ × κ)

/-- The value of a constant. -/
def slotVal (c : ℕ → ℝ) (ξ₁ : ι → ℝ) (w₁ : κ → ℝ) (A : Matrix κ κ ℝ) : SlotT ι κ → ℝ :=
  Sum.elim (fun _ => 0) (Sum.elim (fun _ => -1) (Sum.elim c (Sum.elim ξ₁
    (Sum.elim (fun i => -ξ₁ i) (Sum.elim w₁ (fun p => -A p.1 p.2))))))

variable [Encodable ι] [Encodable κ]

/-- The arrangement of the constants in the slots. -/
def encC (c : ℕ → ℝ) (ξ₁ : ι → ℝ) (w₁ : κ → ℝ) (A : Matrix κ κ ℝ) (n : ℕ) : ℝ :=
  ((Encodable.decode n : Option (SlotT ι κ)).map (slotVal c ξ₁ w₁ A)).getD 0

variable (ι κ) in
/-- The slot of a constant. -/
def sIdx (s : SlotT ι κ) : ℕ := Encodable.encode s

theorem encC_sIdx (c : ℕ → ℝ) (ξ₁ : ι → ℝ) (w₁ : κ → ℝ) (A : Matrix κ κ ℝ) (s : SlotT ι κ) :
    encC c ξ₁ w₁ A (sIdx ι κ s) = slotVal c ξ₁ w₁ A s := by
  simp [encC, sIdx, Encodable.encodek]

variable (ι κ) in
def sZero : ℕ := sIdx ι κ (Sum.inl ())

variable (ι κ) in
def sNeg : ℕ := sIdx ι κ (Sum.inr (Sum.inl ()))

variable (ι κ) in
def sProg (a : ℕ) : ℕ := sIdx ι κ (Sum.inr (Sum.inr (Sum.inl a)))

variable (κ) in
def sXi (i : ι) : ℕ := sIdx ι κ (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))

variable (κ) in
def sNegXi (i : ι) : ℕ := sIdx ι κ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))))

variable (ι) in
def sW (k : κ) : ℕ := sIdx ι κ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl k))))))

variable (ι) in
def sNegA (k l : κ) : ℕ :=
  sIdx ι κ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (k, l)))))))

variable (c : ℕ → ℝ) (ξ₁ : ι → ℝ) (w₁ : κ → ℝ) (A : Matrix κ κ ℝ)

theorem encC_sZero : encC c ξ₁ w₁ A (sZero ι κ) = 0 := by
  rw [sZero, encC_sIdx]; rfl

theorem encC_sNeg : encC c ξ₁ w₁ A (sNeg ι κ) = -1 := by
  rw [sNeg, encC_sIdx]; rfl

theorem encC_sProg (a : ℕ) : encC c ξ₁ w₁ A (sProg ι κ a) = c a := by
  rw [sProg, encC_sIdx]; rfl

theorem encC_sXi (i : ι) : encC c ξ₁ w₁ A (sXi κ i) = ξ₁ i := by
  rw [sXi, encC_sIdx]; rfl

theorem encC_sNegXi (i : ι) : encC c ξ₁ w₁ A (sNegXi κ i) = -ξ₁ i := by
  rw [sNegXi, encC_sIdx]; rfl

theorem encC_sW (k : κ) : encC c ξ₁ w₁ A (sW ι k) = w₁ k := by
  rw [sW, encC_sIdx]; rfl

theorem encC_sNegA (k l : κ) : encC c ξ₁ w₁ A (sNegA ι k l) = -A k l := by
  rw [sNegA, encC_sIdx]; rfl

end Slots

/-! ### Evaluating the program in `ℝ[χ][τ]/(τ^{D+1})` -/

section ProgEval

variable [Encodable ι] [Encodable κ]

/-- The gates available during one Newton step: a gate holding `0`, a gate holding `-1`, the
blocks of the inputs `ξ₁ + τχ` and of the current iterate `Ω`. -/
structure Env (ι κ : Type) where
  z : ℕ
  n1 : ℕ
  xiB : ι → ℕ → ℕ
  omB : κ → ℕ → ℕ

variable (ι κ) in
/-- The slot of the constant gate created for an operand. -/
def opSlot : Operand (ι ⊕ κ) ℕ → ℕ
  | .const a => sProg ι κ a
  | _ => sZero ι κ

/-- The block of an operand (`g` is the constant gate created for it). -/
def opBlock (ev : Env ι κ) (bs : List (ℕ → ℕ)) (g : ℕ) : Operand (ι ⊕ κ) ℕ → ℕ → ℕ
  | .input (.inl i) => ev.xiB i
  | .input (.inr k) => ev.omB k
  | .const _ => fun j => if j = 0 then g else ev.z
  | .prev t => bs.getD t (fun _ => ev.z)

/-- The gates for an arithmetic operation on blocks. -/
def opB (D : ℕ) (ev : Env ι κ) : ArithOp → Shape ι → (ℕ → ℕ) → (ℕ → ℕ) → Shape ι × (ℕ → ℕ)
  | .add, Γ, x, y => addB D Γ x y
  | .sub, Γ, x, y => addB D (scaleB D Γ ev.n1 y).1 x (scaleB D Γ ev.n1 y).2
  | .mul, Γ, x, y => mulB D Γ x y ev.z

/-- The gates for one instruction of the program. -/
def instrStep (D : ℕ) (ev : Env ι κ) (st : Shape ι × List (ℕ → ℕ))
    (ins : Instr (ι ⊕ κ) ℕ) : Shape ι × List (ℕ → ℕ) :=
  let Γ1 := layerF st.1 ![Gate.const (opSlot ι κ ins.a), Gate.const (opSlot ι κ ins.b)]
  let r := opB D ev ins.op Γ1 (opBlock ev st.2 st.1.length ins.a)
    (opBlock ev st.2 (st.1.length + 1) ins.b)
  (r.1, st.2 ++ [r.2])

/-- The substitution `(ξ, w) ↦ (ξ₁ + χ, Ω)`. -/
def subst (ξ₁ : ι → ℝ) (Ω : κ → MvPolynomial ι ℝ) : ι ⊕ κ → MvPolynomial ι ℝ :=
  Sum.elim (fun i => MvPolynomial.C (ξ₁ i) + X i) Ω

/-- The environment is correct for `Ω`. -/
def EnvOK (D : ℕ) (Γ : Shape ι) (c' : ℕ → ℝ) (ξ₁ : ι → ℝ) (Ω : κ → MvPolynomial ι ℝ)
    (ev : Env ι κ) : Prop :=
  Holds Γ c' ev.z 0 ∧ Holds Γ c' ev.n1 (MvPolynomial.C (-1)) ∧
    (∀ i, HoldsB D Γ c' (ev.xiB i) (rep ξ₁ (MvPolynomial.C (ξ₁ i) + X i))) ∧
    ∀ k, HoldsB D Γ c' (ev.omB k) (rep ξ₁ (Ω k))

theorem EnvOK.mono {D : ℕ} {Γ Γ' : Shape ι} {c' : ℕ → ℝ} {ξ₁ : ι → ℝ}
    {Ω : κ → MvPolynomial ι ℝ} {ev : Env ι κ} (h : EnvOK D Γ c' ξ₁ Ω ev) (hΓ : Γ <+: Γ') :
    EnvOK D Γ' c' ξ₁ Ω ev :=
  ⟨h.1.mono hΓ, h.2.1.mono hΓ, fun i => (h.2.2.1 i).mono hΓ, fun k => (h.2.2.2 k).mono hΓ⟩

theorem holdsB_zero {D : ℕ} {Γ : Shape ι} {c' : ℕ → ℝ} {z : ℕ} (hz : Holds Γ c' z 0)
    (ξ₁ : ι → ℝ) : HoldsB D Γ c' (fun _ => z) (rep ξ₁ 0) := fun j _ => by
  rw [rep_zero]; exact hz

theorem opBlock_spec {D : ℕ} {Γ : Shape ι} {c : ℕ → ℝ} {c' : ℕ → ℝ} {ξ₁ : ι → ℝ}
    {Ω : κ → MvPolynomial ι ℝ} {ev : Env ι κ} (hev : EnvOK D Γ c' ξ₁ Ω ev)
    (hc' : ∀ a, c' (sProg ι κ a) = c a)
    {bs : List (ℕ → ℕ)} {V : List (MvPolynomial (ι ⊕ κ) ℝ)} (hlen : bs.length = V.length)
    (hbs : ∀ t < bs.length, HoldsB D Γ c' (bs.getD t (fun _ => ev.z))
      (rep ξ₁ (bind₁ (subst ξ₁ Ω) (V.getD t 0))))
    (o : Operand (ι ⊕ κ) ℕ) {g : ℕ} (hg : Holds Γ c' g (MvPolynomial.C (c' (opSlot ι κ o)))) :
    HoldsB D Γ c' (opBlock ev bs g o)
      (rep ξ₁ (bind₁ (subst ξ₁ Ω) ((o.instantiate c).eval V))) := by
  cases o with
  | input v =>
    cases v with
    | inl i => simpa [opBlock, Operand.instantiate, Operand.eval, subst] using hev.2.2.1 i
    | inr k => simpa [opBlock, Operand.instantiate, Operand.eval, subst] using hev.2.2.2 k
  | const a =>
    intro j hj
    simp only [opBlock, Operand.instantiate, Operand.eval, bind₁_C_right, rep_C]
    split_ifs with h0
    · simpa [opSlot, hc'] using hg
    · exact hev.1
  | prev t =>
    simp only [opBlock, Operand.instantiate, Operand.eval]
    by_cases ht : t < bs.length
    · exact hbs t ht
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega), map_zero]
      exact holdsB_zero hev.1 ξ₁

theorem apply_bind₁ {τ : Type*} (op : ArithOp) (f : ι ⊕ κ → MvPolynomial τ ℝ)
    (p q : MvPolynomial (ι ⊕ κ) ℝ) :
    bind₁ f (op.apply p q) = op.apply (bind₁ f p) (bind₁ f q) := by
  cases op <;> simp [ArithOp.apply]

theorem opB_spec {D : ℕ} {Γ : Shape ι} {c' : ℕ → ℝ} {ξ₁ : ι → ℝ} {ev : Env ι κ}
    (hz : Holds Γ c' ev.z 0) (hn1 : Holds Γ c' ev.n1 (MvPolynomial.C (-1)))
    {x y : ℕ → ℕ} {s t : MvPolynomial ι ℝ} (hx : HoldsB D Γ c' x (rep ξ₁ s))
    (hy : HoldsB D Γ c' y (rep ξ₁ t)) (op : ArithOp) :
    Γ <+: (opB D ev op Γ x y).1 ∧ (opB D ev op Γ x y).1.length ≤ Γ.length + 2 * (D + 1) ^ 2 ∧
      HoldsB D (opB D ev op Γ x y).1 c' (opB D ev op Γ x y).2 (rep ξ₁ (op.apply s t)) := by
  cases op with
  | add =>
    obtain ⟨h1, h2, h3⟩ := addB_spec hx hy
    refine ⟨h1, ?_, h3.congr fun j _ => (rep_add ξ₁ s t j).symm⟩
    simp only [opB, h2]
    nlinarith
  | sub =>
    obtain ⟨h1, h2, h3⟩ := scaleB_spec hn1 hy
    obtain ⟨h1', h2', h3'⟩ := addB_spec (hx.mono h1) h3
    refine ⟨h1.trans h1', ?_, h3'.congr fun j _ => ?_⟩
    · simp only [opB, h2', h2]
      nlinarith
    · show _ = rep ξ₁ (s - t) j
      rw [rep_sub, map_neg, map_one]
      ring
  | mul =>
    obtain ⟨h1, h2, h3⟩ := mulB_spec hx hy hz
    refine ⟨h1, ?_, h3.congr fun j _ => (rep_mul ξ₁ s t j).symm⟩
    simp only [opB, h2]
    nlinarith

/-- `Instr.eval` of an instantiated instruction. -/
theorem instr_eval_instantiate (c : ℕ → ℝ) (V : List (MvPolynomial (ι ⊕ κ) ℝ))
    (ins : Instr (ι ⊕ κ) ℕ) :
    Instr.eval V (⟨ins.op, ins.a.instantiate c, ins.b.instantiate c⟩ : Instr (ι ⊕ κ) ℝ) =
      ins.op.apply ((ins.a.instantiate c).eval V) ((ins.b.instantiate c).eval V) := rfl

/-- Invariant of the evaluation of the program. -/
def ProgInv (D : ℕ) (Γ₀ : Shape ι) (c' : ℕ → ℝ) (ξ₁ : ι → ℝ) (Ω : κ → MvPolynomial ι ℝ)
    (ev : Env ι κ) (V : List (MvPolynomial (ι ⊕ κ) ℝ)) (st : Shape ι × List (ℕ → ℕ)) : Prop :=
  Γ₀ <+: st.1 ∧ st.1.length ≤ Γ₀.length + V.length * (2 + 2 * (D + 1) ^ 2) ∧
    st.2.length = V.length ∧
    ∀ t < st.2.length, HoldsB D st.1 c' (st.2.getD t (fun _ => ev.z))
      (rep ξ₁ (bind₁ (subst ξ₁ Ω) (V.getD t 0)))

theorem instrStep_spec {D : ℕ} {Γ₀ : Shape ι} {c : ℕ → ℝ} {c' : ℕ → ℝ} {ξ₁ : ι → ℝ}
    {Ω : κ → MvPolynomial ι ℝ} {ev : Env ι κ} (hev : EnvOK D Γ₀ c' ξ₁ Ω ev)
    (hc' : ∀ a, c' (sProg ι κ a) = c a)
    {V : List (MvPolynomial (ι ⊕ κ) ℝ)} {st : Shape ι × List (ℕ → ℕ)}
    (hst : ProgInv D Γ₀ c' ξ₁ Ω ev V st) (ins : Instr (ι ⊕ κ) ℕ) :
    ProgInv D Γ₀ c' ξ₁ Ω ev
      (V ++ [Instr.eval V (⟨ins.op, ins.a.instantiate c, ins.b.instantiate c⟩ : Instr _ ℝ)])
      (instrStep D ev st ins) := by
  obtain ⟨hpre, hlen, hbl, hbs⟩ := hst
  set Γ1 := layerF st.1 ![Gate.const (opSlot ι κ ins.a), Gate.const (opSlot ι κ ins.b)]
    with hΓ1
  have hpre1 : st.1 <+: Γ1 := prefix_layerF _ _
  have hev1 : EnvOK D Γ1 c' ξ₁ Ω ev := hev.mono (hpre.trans hpre1)
  have hga : Holds Γ1 c' st.1.length (MvPolynomial.C (c' (opSlot ι κ ins.a))) := by
    have := holds_layerF st.1 ![Gate.const (opSlot ι κ ins.a), Gate.const (opSlot ι κ ins.b)]
      c' (fun t => by fin_cases t <;> exact trivial) 0
    simpa [Gate.eval] using this
  have hgb : Holds Γ1 c' (st.1.length + 1) (MvPolynomial.C (c' (opSlot ι κ ins.b))) := by
    have := holds_layerF st.1 ![Gate.const (opSlot ι κ ins.a), Gate.const (opSlot ι κ ins.b)]
      c' (fun t => by fin_cases t <;> exact trivial) 1
    simpa [Gate.eval] using this
  have hbs1 : ∀ t < st.2.length, HoldsB D Γ1 c' (st.2.getD t (fun _ => ev.z))
      (rep ξ₁ (bind₁ (subst ξ₁ Ω) (V.getD t 0))) := fun t ht => (hbs t ht).mono hpre1
  have ha := opBlock_spec hev1 hc' hbl hbs1 ins.a hga
  have hb := opBlock_spec hev1 hc' hbl hbs1 ins.b hgb
  obtain ⟨h1, h2, h3⟩ := opB_spec hev1.1 hev1.2.1 ha hb ins.op
  refine ⟨hpre.trans (hpre1.trans h1), ?_, ?_, ?_⟩
  · show (opB D ev ins.op Γ1 _ _).1.length ≤ _
    have : Γ1.length = st.1.length + 2 := length_layerF _ _
    simp only [List.length_append, List.length_singleton]
    rw [this] at h2
    nlinarith
  · simp [instrStep, hbl]
  · intro t ht
    simp only [instrStep, List.length_append, List.length_singleton] at ht
    simp only [instrStep]
    by_cases hlt : t < st.2.length
    · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (by omega)]
      exact (hbs t hlt).mono (hpre1.trans h1)
    · have htt : t = st.2.length := by omega
      subst htt
      rw [List.getD_append_right _ _ _ _ le_rfl, List.getD_append_right _ _ _ _ (by omega),
        hbl, Nat.sub_self]
      simp only [List.getD_cons_zero]
      rw [instr_eval_instantiate, apply_bind₁]
      exact h3

/-- The gates evaluating the whole program. -/
def progGates (D : ℕ) (ev : Env ι κ) (prog : SLP (ι ⊕ κ) ℕ) (Γ : Shape ι) :
    Shape ι × List (ℕ → ℕ) :=
  prog.foldl (instrStep D ev) (Γ, [])

theorem slp_values_append_singleton {A : Type} [CommRing A] (P : SLP (ι ⊕ κ) A)
    (ins : Instr (ι ⊕ κ) A) :
    SLP.values (P ++ [ins]) = P.values ++ [ins.eval P.values] := by
  simp [SLP.values, List.foldl_append]

theorem progGates_spec {D : ℕ} {Γ₀ : Shape ι} {c : ℕ → ℝ} {c' : ℕ → ℝ} {ξ₁ : ι → ℝ}
    {Ω : κ → MvPolynomial ι ℝ} {ev : Env ι κ} (hev : EnvOK D Γ₀ c' ξ₁ Ω ev)
    (hc' : ∀ a, c' (sProg ι κ a) = c a)
    (prog : SLP (ι ⊕ κ) ℕ) :
    ProgInv D Γ₀ c' ξ₁ Ω ev (prog.instantiate c).values (progGates D ev prog Γ₀) := by
  unfold progGates
  induction prog using List.reverseRecOn with
  | nil =>
    refine ⟨List.prefix_refl _, by simp [SLP.instantiate, SLP.values], by
      simp [SLP.instantiate, SLP.values], fun t ht => by simp at ht⟩
  | append_singleton P ins ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have e : (SLP.instantiate c (P ++ [ins])).values =
        (SLP.instantiate c P).values ++ [Instr.eval (SLP.instantiate c P).values
          (⟨ins.op, ins.a.instantiate c, ins.b.instantiate c⟩ : Instr _ ℝ)] := by
      rw [show SLP.instantiate c (P ++ [ins]) = SLP.instantiate c P ++
        [(⟨ins.op, ins.a.instantiate c, ins.b.instantiate c⟩ : Instr _ ℝ)] by
          simp [SLP.instantiate]]
      exact slp_values_append_singleton _ _
    rw [e]
    exact instrStep_spec hev hc' ih ins

theorem length_slp_values {A : Type} [CommRing A] (P : SLP (ι ⊕ κ) A) :
    P.values.length = P.length := by
  induction P using List.reverseRecOn with
  | nil => rfl
  | append_singleton P ins ih => simp [slp_values_append_singleton, ih]

end ProgEval

/-! ### The Newton steps -/

section NewtonGates

variable [Encodable ι] [Encodable κ]

/-- Constant gates for the output operands, and the blocks of the outputs. -/
def outLayer (ev : Env ι κ) (oE : κ → Operand (ι ⊕ κ) ℕ) (st : Shape ι × List (ℕ → ℕ)) :
    Shape ι × (κ → ℕ → ℕ) :=
  (layer st.1 (fun l : κ => Gate.const (opSlot ι κ (oE l))),
    fun l => opBlock ev st.2 (lidx st.1.length l) (oE l))

theorem outLayer_spec {D : ℕ} {Γ₀ : Shape ι} {c : ℕ → ℝ} {c' : ℕ → ℝ} {ξ₁ : ι → ℝ}
    {Ω : κ → MvPolynomial ι ℝ} {ev : Env ι κ} (hev : EnvOK D Γ₀ c' ξ₁ Ω ev)
    (hc' : ∀ a, c' (sProg ι κ a) = c a) (prog : SLP (ι ⊕ κ) ℕ)
    (oE : κ → Operand (ι ⊕ κ) ℕ) :
    Γ₀ <+: (outLayer ev oE (progGates D ev prog Γ₀)).1 ∧
      (outLayer ev oE (progGates D ev prog Γ₀)).1.length ≤
        Γ₀.length + prog.length * (2 + 2 * (D + 1) ^ 2) + Fintype.card κ ∧
      ∀ l, HoldsB D (outLayer ev oE (progGates D ev prog Γ₀)).1 c'
        ((outLayer ev oE (progGates D ev prog Γ₀)).2 l)
        (rep ξ₁ (bind₁ (subst ξ₁ Ω) (progOutputs prog c oE l))) := by
  obtain ⟨hpre, hlen, hbl, hbs⟩ := progGates_spec hev hc' prog (c := c)
  set st := progGates D ev prog Γ₀
  have hVl : (SLP.instantiate c prog).values.length = prog.length := by
    rw [length_slp_values]; simp [SLP.instantiate]
  have hpre1 : st.1 <+: layer st.1 (fun l : κ => Gate.const (opSlot ι κ (oE l))) :=
    prefix_layer _ _
  refine ⟨hpre.trans hpre1, ?_, fun l => ?_⟩
  · show (layer st.1 (fun l : κ => Gate.const (opSlot ι κ (oE l)))).length ≤ _
    rw [length_layer, ← hVl]
    omega
  · have hg := holds_layer st.1 (fun l : κ => Gate.const (opSlot ι κ (oE l))) c'
      (fun _ => trivial) l
    exact opBlock_spec (hev.mono (hpre.trans hpre1)) hc' hbl
      (fun t ht => (hbs t ht).mono hpre1) (oE l) hg

/-- One column update `Ωₖ ← Ωₖ - Aₖₗ Eₗ` for all `k`. -/
def updStep (D : ℕ) (z : ℕ) (nA : κ → κ → ℕ) (eB : κ → ℕ → ℕ)
    (st : Shape ι × (κ → ℕ → ℕ)) (l : κ) : Shape ι × (κ → ℕ → ℕ) :=
  let Γ1 := layer st.1 (fun p : κ × Fin (D + 1) => Gate.mul (nA p.1 l) (eB l p.2))
  (layer Γ1 (fun p : κ × Fin (D + 1) => Gate.add (st.2 p.1 p.2) (lidx st.1.length p)),
    fun k j => if h : j < D + 1 then lidx Γ1.length (k, (⟨j, h⟩ : Fin (D + 1))) else z)

theorem updStep_spec {D : ℕ} {Γb : Shape ι} {c' : ℕ → ℝ} {ξ₁ : ι → ℝ} {A : Matrix κ κ ℝ}
    {z : ℕ} {nA : κ → κ → ℕ} {eB : κ → ℕ → ℕ} {Y : κ → MvPolynomial ι ℝ}
    (hnA : ∀ k l, Holds Γb c' (nA k l) (MvPolynomial.C (-A k l)))
    (heB : ∀ l, HoldsB D Γb c' (eB l) (rep ξ₁ (Y l)))
    {st : Shape ι × (κ → ℕ → ℕ)} {W : κ → MvPolynomial ι ℝ} (hpre : Γb <+: st.1)
    (hW : ∀ k, HoldsB D st.1 c' (st.2 k) (rep ξ₁ (W k))) (l : κ) :
    st.1 <+: (updStep D z nA eB st l).1 ∧
      (updStep D z nA eB st l).1.length =
        st.1.length + 2 * (Fintype.card κ * (D + 1)) ∧
      ∀ k, HoldsB D (updStep D z nA eB st l).1 c' ((updStep D z nA eB st l).2 k)
        (rep ξ₁ (W k + MvPolynomial.C (-A k l) * Y l)) := by
  set Γ1 := layer st.1 (fun p : κ × Fin (D + 1) => Gate.mul (nA p.1 l) (eB l p.2)) with hΓ1
  have hpre1 : st.1 <+: Γ1 := prefix_layer _ _
  have hP : ∀ p : κ × Fin (D + 1), Holds Γ1 c' (lidx st.1.length p)
      (MvPolynomial.C (-A p.1 l) * rep ξ₁ (Y l) p.2) := by
    intro p
    have hn := (hnA p.1 l).mono hpre
    have he := (heB l p.2 (by omega)).mono hpre
    have := holds_layer st.1 (fun p : κ × Fin (D + 1) => Gate.mul (nA p.1 l) (eB l p.2)) c'
      (fun p => ⟨((hnA p.1 l).mono hpre).1, ((heB l p.2 (by omega)).mono hpre).1⟩) p
    rwa [hn.eval_mul he] at this
  have hW1 : ∀ p : κ × Fin (D + 1), Holds Γ1 c' (st.2 p.1 p.2) (rep ξ₁ (W p.1) p.2) :=
    fun p => (hW p.1 p.2 (by omega)).mono hpre1
  refine ⟨hpre1.trans (prefix_layer Γ1 (fun p : κ × Fin (D + 1) =>
    Gate.add (st.2 p.1 p.2) (lidx st.1.length p))), ?_, fun k j hj => ?_⟩
  · show (layer Γ1 (fun p : κ × Fin (D + 1) =>
      Gate.add (st.2 p.1 p.2) (lidx st.1.length p))).length = _
    rw [length_layer, length_layer]
    simp only [Fintype.card_prod, Fintype.card_fin]
    ring
  · have := holds_layer Γ1 (fun p : κ × Fin (D + 1) =>
      Gate.add (st.2 p.1 p.2) (lidx st.1.length p)) c'
      (fun p => ⟨(hW1 p).1, (hP p).1⟩) (k, ⟨j, by omega⟩)
    rw [(hW1 _).eval_add (hP _)] at this
    show Holds (layer Γ1 (fun p : κ × Fin (D + 1) =>
      Gate.add (st.2 p.1 p.2) (lidx st.1.length p))) c'
      (if h : j < D + 1 then lidx Γ1.length (k, (⟨j, h⟩ : Fin (D + 1))) else z) _
    rw [dite_eq_left (by omega), rep_add, rep_C_mul]
    exact this

theorem foldl_induction {α S : Type*} (f : S → α → S) (I : List α → S → Prop) (s : S)
    (h0 : I [] s) (hs : ∀ L a s, I L s → I (L ++ [a]) (f s a)) (L : List α) :
    I L (L.foldl f s) := by
  induction L using List.reverseRecOn with
  | nil => exact h0
  | append_singleton L a ih => rw [List.foldl_append]; exact hs L a _ ih

/-- One Newton step `Ω ← Ω - A E(ξ₁ + τχ, Ω)`. -/
def newtonOne (D : ℕ) (ev : Env ι κ) (nA : κ → κ → ℕ) (prog : SLP (ι ⊕ κ) ℕ)
    (oE : κ → Operand (ι ⊕ κ) ℕ) (Γ : Shape ι) : Shape ι × (κ → ℕ → ℕ) :=
  (Finset.univ : Finset κ).toList.foldl
    (updStep D ev.z nA (outLayer ev oE (progGates D ev prog Γ)).2)
    ((outLayer ev oE (progGates D ev prog Γ)).1, ev.omB)

/-- The number of gates of one Newton step. -/
def stepCost (D ℓ K : ℕ) : ℕ := ℓ * (2 + 2 * (D + 1) ^ 2) + K + K * (2 * (K * (D + 1)))

theorem newtonOne_spec {D : ℕ} {Γ : Shape ι} {c : ℕ → ℝ} {c' : ℕ → ℝ} {ξ₁ : ι → ℝ}
    {A : Matrix κ κ ℝ} {Ω : κ → MvPolynomial ι ℝ} {ev : Env ι κ} {nA : κ → κ → ℕ}
    (hev : EnvOK D Γ c' ξ₁ Ω ev) (hc' : ∀ a, c' (sProg ι κ a) = c a)
    (hnA : ∀ k l, Holds Γ c' (nA k l) (MvPolynomial.C (-A k l)))
    (prog : SLP (ι ⊕ κ) ℕ) (oE : κ → Operand (ι ⊕ κ) ℕ) :
    Γ <+: (newtonOne D ev nA prog oE Γ).1 ∧
      (newtonOne D ev nA prog oE Γ).1.length ≤
        Γ.length + stepCost D prog.length (Fintype.card κ) ∧
      ∀ k, HoldsB D (newtonOne D ev nA prog oE Γ).1 c' ((newtonOne D ev nA prog oE Γ).2 k)
        (rep ξ₁ (newtonStep (progOutputs prog c oE) ξ₁ A D Ω k)) := by
  obtain ⟨h1, h2, h3⟩ := outLayer_spec hev hc' prog oE
  set o := outLayer ev oE (progGates D ev prog Γ)
  set Y : κ → MvPolynomial ι ℝ := fun l => bind₁ (subst ξ₁ Ω) (progOutputs prog c oE l)
  have hnA' : ∀ k l, Holds o.1 c' (nA k l) (MvPolynomial.C (-A k l)) :=
    fun k l => (hnA k l).mono h1
  have hom : ∀ k, HoldsB D o.1 c' (ev.omB k) (rep ξ₁ (Ω k)) :=
    fun k => (hev.2.2.2 k).mono h1
  have key := foldl_induction (updStep D ev.z nA o.2)
    (fun L st => o.1 <+: st.1 ∧
      st.1.length = o.1.length + L.length * (2 * (Fintype.card κ * (D + 1))) ∧
      ∀ k, HoldsB D st.1 c' (st.2 k)
        (rep ξ₁ (Ω k + (L.map fun l => MvPolynomial.C (-A k l) * Y l).sum)))
    (o.1, ev.omB) ⟨List.prefix_refl _, by simp, fun k => by simpa using hom k⟩
    (fun L a st hst => by
      obtain ⟨g1, g2, g3⟩ := updStep_spec (z := ev.z) (eB := o.2) (Y := Y) hnA' h3 hst.1 hst.2.2 a
      refine ⟨hst.1.trans g1, ?_, fun k => ?_⟩
      · rw [g2, hst.2.1]
        simp only [List.length_append, List.length_singleton]
        ring
      · refine (g3 k).congr fun j _ => ?_
        simp [add_assoc])
    (Finset.univ : Finset κ).toList
  obtain ⟨k1, k2, k3⟩ := key
  refine ⟨h1.trans k1, ?_, fun k => (k3 k).congr fun j hj => ?_⟩
  · have e : (newtonOne D ev nA prog oE Γ).1.length = o.1.length +
        (Finset.univ : Finset κ).toList.length * (2 * (Fintype.card κ * (D + 1))) := k2
    rw [e, Finset.length_toList, Finset.card_univ]
    unfold stepCost
    nlinarith
  · rw [Finset.sum_map_toList]
    unfold newtonStep
    rw [rep_truncDeg ξ₁ hj]
    congr 1
    simp only [Y, subst, map_neg, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]

/-- `n` Newton steps. -/
def newtonIter (D : ℕ) (z n1 : ℕ) (xiB : ι → ℕ → ℕ) (nA : κ → κ → ℕ)
    (prog : SLP (ι ⊕ κ) ℕ) (oE : κ → Operand (ι ⊕ κ) ℕ) (Γ₀ : Shape ι)
    (om₀ : κ → ℕ → ℕ) : ℕ → Shape ι × (κ → ℕ → ℕ)
  | 0 => (Γ₀, om₀)
  | n + 1 => newtonOne D ⟨z, n1, xiB, (newtonIter D z n1 xiB nA prog oE Γ₀ om₀ n).2⟩ nA prog oE
      (newtonIter D z n1 xiB nA prog oE Γ₀ om₀ n).1

theorem newtonIter_spec {D : ℕ} {Γ₀ : Shape ι} {c : ℕ → ℝ} {c' : ℕ → ℝ} {ξ₁ : ι → ℝ}
    {w₁ : κ → ℝ} {A : Matrix κ κ ℝ} {z n1 : ℕ} {xiB : ι → ℕ → ℕ} {nA : κ → κ → ℕ}
    {om₀ : κ → ℕ → ℕ} (hc' : ∀ a, c' (sProg ι κ a) = c a)
    (hz : Holds Γ₀ c' z 0) (hn1 : Holds Γ₀ c' n1 (MvPolynomial.C (-1)))
    (hxi : ∀ i, HoldsB D Γ₀ c' (xiB i) (rep ξ₁ (MvPolynomial.C (ξ₁ i) + X i)))
    (hnA : ∀ k l, Holds Γ₀ c' (nA k l) (MvPolynomial.C (-A k l)))
    (hom : ∀ k, HoldsB D Γ₀ c' (om₀ k) (rep ξ₁ (MvPolynomial.C (w₁ k))))
    (prog : SLP (ι ⊕ κ) ℕ) (oE : κ → Operand (ι ⊕ κ) ℕ) (n : ℕ) :
    Γ₀ <+: (newtonIter D z n1 xiB nA prog oE Γ₀ om₀ n).1 ∧
      (newtonIter D z n1 xiB nA prog oE Γ₀ om₀ n).1.length ≤
        Γ₀.length + n * stepCost D prog.length (Fintype.card κ) ∧
      ∀ k, HoldsB D (newtonIter D z n1 xiB nA prog oE Γ₀ om₀ n).1 c'
        ((newtonIter D z n1 xiB nA prog oE Γ₀ om₀ n).2 k)
        (rep ξ₁ ((newtonStep (progOutputs prog c oE) ξ₁ A D)^[n]
          (fun l => MvPolynomial.C (w₁ l)) k)) := by
  induction n with
  | zero => exact ⟨List.prefix_refl _, by simp [newtonIter], fun k => by simpa [newtonIter] using hom k⟩
  | succ n ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    set st := newtonIter D z n1 xiB nA prog oE Γ₀ om₀ n
    have hev : EnvOK D st.1 c' ξ₁ ((newtonStep (progOutputs prog c oE) ξ₁ A D)^[n]
        (fun l => MvPolynomial.C (w₁ l))) ⟨z, n1, xiB, st.2⟩ :=
      ⟨hz.mono h1, hn1.mono h1, fun i => (hxi i).mono h1, h3⟩
    obtain ⟨g1, g2, g3⟩ := newtonOne_spec hev hc' (fun k l => (hnA k l).mono h1) prog oE
    refine ⟨h1.trans g1, ?_, fun k => ?_⟩
    · show (newtonOne D _ nA prog oE st.1).1.length ≤ _
      refine g2.trans ?_
      rw [Nat.succ_mul]
      omega
    · show HoldsB D (newtonOne D _ nA prog oE st.1).1 c' ((newtonOne D _ nA prog oE st.1).2 k) _
      rw [Function.iterate_succ_apply']
      exact g3 k

/-- Summing the components of the blocks. -/
def sumAux (z : ℕ) (om : κ → ℕ → ℕ) (Γ : Shape ι) : ℕ → Shape ι × (κ → ℕ)
  | 0 => (Γ, fun _ => z)
  | a + 1 => (layer (sumAux z om Γ a).1 (fun k : κ => Gate.add ((sumAux z om Γ a).2 k) (om k a)),
      fun k => lidx (sumAux z om Γ a).1.length k)

theorem sumAux_spec {D : ℕ} {Γ : Shape ι} {c' : ℕ → ℝ} {z : ℕ} {om : κ → ℕ → ℕ}
    {F : κ → ℕ → MvPolynomial ι ℝ} (hz : Holds Γ c' z 0) (hom : ∀ k, HoldsB D Γ c' (om k) (F k))
    (a : ℕ) (ha : a ≤ D + 1) :
    Γ <+: (sumAux z om Γ a).1 ∧ (sumAux z om Γ a).1.length = Γ.length + a * Fintype.card κ ∧
      ∀ k, Holds (sumAux z om Γ a).1 c' ((sumAux z om Γ a).2 k)
        (∑ a' ∈ Finset.range a, F k a') := by
  induction a with
  | zero => exact ⟨List.prefix_refl _, by simp [sumAux], fun k => by simpa [sumAux] using hz⟩
  | succ a ih =>
    obtain ⟨h1, h2, h3⟩ := ih (by omega)
    set st := sumAux z om Γ a
    have hom' : ∀ k, Holds st.1 c' (om k a) (F k a) := fun k => (hom k a (by omega)).mono h1
    refine ⟨h1.trans (prefix_layer st.1 (fun k : κ => Gate.add (st.2 k) (om k a))), ?_,
      fun k => ?_⟩
    · show (layer st.1 (fun k : κ => Gate.add (st.2 k) (om k a))).length = _
      rw [length_layer, h2, Nat.succ_mul]
      ring
    · have := holds_layer st.1 (fun k : κ => Gate.add (st.2 k) (om k a)) c'
        (fun k => ⟨(h3 k).1, (hom' k).1⟩) k
      rw [(h3 k).eval_add (hom' k), ← Finset.sum_range_succ] at this
      exact this

/-! ### The initial gates -/

variable (ι κ)

def initG0 : Shape ι := layerF [] ![Gate.const (sZero ι κ), Gate.const (sNeg ι κ)]
def initG1 : Shape ι := layer (initG0 ι κ) (fun i : ι => Gate.const (sXi κ i))
def initG2 : Shape ι := layer (initG1 ι κ) (fun i : ι => Gate.const (sNegXi κ i))
def initG3 : Shape ι := layer (initG2 ι κ) (fun i : ι => Gate.var i)
def initG4 : Shape ι := layer (initG3 ι κ)
  (fun i : ι => Gate.add (lidx (initG2 ι κ).length i) (lidx (initG1 ι κ).length i))
def initG5 : Shape ι := layer (initG4 ι κ) (fun k : κ => Gate.const (sW ι k))
def initG6 : Shape ι := layer (initG5 ι κ) (fun p : κ × κ => Gate.const (sNegA ι p.1 p.2))

def xiB0 (i : ι) (j : ℕ) : ℕ :=
  if j = 0 then lidx (initG0 ι κ).length i else if j = 1 then lidx (initG3 ι κ).length i else 0
def omB0 (k : κ) (j : ℕ) : ℕ := if j = 0 then lidx (initG4 ι κ).length k else 0
def nA0 (k l : κ) : ℕ := lidx (initG5 ι κ).length (k, l)

variable {ι κ}

theorem init_spec (D : ℕ) (c : ℕ → ℝ) (ξ₁ : ι → ℝ) (w₁ : κ → ℝ) (A : Matrix κ κ ℝ) :
    (initG6 ι κ).length = 2 + 4 * Fintype.card ι + Fintype.card κ + Fintype.card κ ^ 2 ∧
    Holds (initG6 ι κ) (encC c ξ₁ w₁ A) 0 0 ∧
    Holds (initG6 ι κ) (encC c ξ₁ w₁ A) 1 (MvPolynomial.C (-1)) ∧
    (∀ i, HoldsB D (initG6 ι κ) (encC c ξ₁ w₁ A) (xiB0 ι κ i)
      (rep ξ₁ (MvPolynomial.C (ξ₁ i) + X i))) ∧
    (∀ k l, Holds (initG6 ι κ) (encC c ξ₁ w₁ A) (nA0 ι κ k l) (MvPolynomial.C (-A k l))) ∧
    ∀ k, HoldsB D (initG6 ι κ) (encC c ξ₁ w₁ A) (omB0 ι κ k)
      (rep ξ₁ (MvPolynomial.C (w₁ k))) := by
  set c' := encC c ξ₁ w₁ A
  have p01 : initG0 ι κ <+: initG1 ι κ := prefix_layer _ _
  have p12 : initG1 ι κ <+: initG2 ι κ := prefix_layer _ _
  have p23 : initG2 ι κ <+: initG3 ι κ := prefix_layer _ _
  have p34 : initG3 ι κ <+: initG4 ι κ := prefix_layer _ _
  have p45 : initG4 ι κ <+: initG5 ι κ := prefix_layer _ _
  have p56 : initG5 ι κ <+: initG6 ι κ := prefix_layer _ _
  have p46 := p45.trans p56
  have p36 := p34.trans p46
  have p16 := p12.trans (p23.trans p36)
  have p06 := p01.trans p16
  have hl0 : (initG0 ι κ).length = 2 := by simp [initG0, length_layerF]
  have h0 : Holds (initG0 ι κ) c' 0 0 := by
    have := holds_layerF ([] : Shape ι) ![Gate.const (sZero ι κ), Gate.const (sNeg ι κ)] c'
      (fun t => by fin_cases t <;> simp [Gate.RefsLt]) 0
    simp only [Gate.eval, Matrix.cons_val_zero, c', encC_sZero, map_zero, Fin.val_zero,
      List.length_nil, add_zero] at this
    exact this
  have h1 : Holds (initG0 ι κ) c' 1 (MvPolynomial.C (-1)) := by
    have := holds_layerF ([] : Shape ι) ![Gate.const (sZero ι κ), Gate.const (sNeg ι κ)] c'
      (fun t => by fin_cases t <;> simp [Gate.RefsLt]) 1
    simp only [Gate.eval, Matrix.cons_val_one, Matrix.cons_val_zero, c', encC_sNeg,
      Fin.val_one, List.length_nil, zero_add] at this
    exact this
  have hxi : ∀ i, Holds (initG1 ι κ) c' (lidx (initG0 ι κ).length i)
      (MvPolynomial.C (ξ₁ i)) := fun i => by
    have := holds_layer (initG0 ι κ) (fun i : ι => Gate.const (sXi κ i)) c' (fun _ => trivial) i
    simp only [Gate.eval, c', encC_sXi] at this
    exact this
  have hnxi : ∀ i, Holds (initG2 ι κ) c' (lidx (initG1 ι κ).length i)
      (MvPolynomial.C (-ξ₁ i)) := fun i => by
    have := holds_layer (initG1 ι κ) (fun i : ι => Gate.const (sNegXi κ i)) c'
      (fun _ => trivial) i
    simp only [Gate.eval, c', encC_sNegXi] at this
    exact this
  have hX : ∀ i, Holds (initG3 ι κ) c' (lidx (initG2 ι κ).length i) (X i) := fun i => by
    have := holds_layer (initG2 ι κ) (fun i : ι => Gate.var i) c' (fun _ => trivial) i
    simp only [Gate.eval] at this
    exact this
  have hXm : ∀ i, Holds (initG4 ι κ) c' (lidx (initG3 ι κ).length i)
      (X i - MvPolynomial.C (ξ₁ i)) := fun i => by
    have hx := hX i
    have hn := (hnxi i).mono p23
    have := holds_layer (initG3 ι κ)
      (fun i : ι => Gate.add (lidx (initG2 ι κ).length i) (lidx (initG1 ι κ).length i)) c'
      (fun i => ⟨(hX i).1, ((hnxi i).mono p23).1⟩) i
    rw [hx.eval_add hn, map_neg, ← sub_eq_add_neg] at this
    exact this
  have hw : ∀ k, Holds (initG5 ι κ) c' (lidx (initG4 ι κ).length k)
      (MvPolynomial.C (w₁ k)) := fun k => by
    have := holds_layer (initG4 ι κ) (fun k : κ => Gate.const (sW ι k)) c' (fun _ => trivial) k
    simp only [Gate.eval, c', encC_sW] at this
    exact this
  have hA : ∀ k l, Holds (initG6 ι κ) c' (lidx (initG5 ι κ).length (k, l))
      (MvPolynomial.C (-A k l)) := fun k l => by
    have := holds_layer (initG5 ι κ) (fun p : κ × κ => Gate.const (sNegA ι p.1 p.2)) c'
      (fun _ => trivial) (k, l)
    simp only [Gate.eval, c', encC_sNegA] at this
    exact this
  have hz6 : Holds (initG6 ι κ) c' 0 0 := h0.mono p06
  refine ⟨?_, hz6, h1.mono p06, fun i j hj => ?_, hA, fun k j hj => ?_⟩
  · simp only [initG6, initG5, initG4, initG3, initG2, initG1, length_layer, hl0,
      Fintype.card_prod]
    ring
  · rw [rep_xi]
    simp only [xiB0]
    split_ifs
    · exact (hxi i).mono p16
    · exact (hXm i).mono p46
    · exact hz6
  · rw [rep_C]
    simp only [omB0]
    split_ifs
    · exact (hw k).mono p56
    · exact hz6

end NewtonGates

theorem size_arith (N K ℓ D : ℕ) :
    2 + 4 * N + K + K ^ 2 + D * (ℓ * (2 + 2 * (D + 1) ^ 2) + K + K * (2 * (K * (D + 1)))) +
        (D + 1) * K ≤
      10 * ((D + 1) ^ 3 * (ℓ + 1) + (D + 1) ^ 2 * K ^ 2 + N) := by
  have hK : K ≤ K ^ 2 := Nat.le_self_pow two_ne_zero K
  have hd : 1 ≤ D + 1 := Nat.le_add_left 1 D
  have hd2 : 1 ≤ (D + 1) ^ 2 := Nat.one_le_pow _ _ hd
  have hd3 : 1 ≤ (D + 1) ^ 3 := Nat.one_le_pow _ _ hd
  have e1 : D * (ℓ * (2 + 2 * (D + 1) ^ 2)) ≤ 4 * ((D + 1) ^ 3 * ℓ) := by
    have : 2 + 2 * (D + 1) ^ 2 ≤ 4 * (D + 1) ^ 2 := by omega
    calc D * (ℓ * (2 + 2 * (D + 1) ^ 2)) ≤ (D + 1) * (ℓ * (4 * (D + 1) ^ 2)) := by gcongr; omega
      _ = 4 * ((D + 1) ^ 3 * ℓ) := by ring
  have hD2 : D + 1 ≤ (D + 1) ^ 2 := Nat.le_self_pow two_ne_zero _
  have e4 : (D + 1) * K ≤ (D + 1) ^ 2 * K ^ 2 := Nat.mul_le_mul hD2 hK
  have e2 : D * K ≤ (D + 1) ^ 2 * K ^ 2 :=
    le_trans (Nat.mul_le_mul_right K (Nat.le_succ D)) e4
  have e3 : D * (K * (2 * (K * (D + 1)))) ≤ 2 * ((D + 1) ^ 2 * K ^ 2) := by
    calc D * (K * (2 * (K * (D + 1)))) ≤ (D + 1) * (K * (2 * (K * (D + 1)))) :=
          Nat.mul_le_mul_right _ (Nat.le_succ D)
      _ = 2 * ((D + 1) ^ 2 * K ^ 2) := by ring
  have e5 : K ^ 2 ≤ (D + 1) ^ 2 * K ^ 2 := Nat.le_mul_of_pos_left _ hd2
  have e5' : K ≤ (D + 1) ^ 2 * K ^ 2 := hK.trans e5
  have e6 : 1 ≤ (D + 1) ^ 3 * (ℓ + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
  have e7 : (D + 1) ^ 3 * ℓ ≤ (D + 1) ^ 3 * (ℓ + 1) := Nat.mul_le_mul_left _ (Nat.le_succ ℓ)
  have e8 : D * (ℓ * (2 + 2 * (D + 1) ^ 2) + K + K * (2 * (K * (D + 1)))) =
      D * (ℓ * (2 + 2 * (D + 1) ^ 2)) + D * K + D * (K * (2 * (K * (D + 1)))) := by ring
  rw [e8]
  linarith

/-- **Lemma 3.4 (a)**: the circuit.  The graph `Γ`, the output gates and the arrangement
`enc` of the constants depend only on the program graph `prog`, its outputs, and `ι`, `κ`, `D`. -/
theorem newton_circuit :
    ∃ C : ℕ, ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
      (prog : SLP (ι ⊕ κ) ℕ) (oE : κ → Operand (ι ⊕ κ) ℕ) (D : ℕ),
      ∃ (Γ : Shape ι) (out : κ → ℕ)
        (enc : (ℕ → ℝ) → (ι → ℝ) → (κ → ℝ) → Matrix κ κ ℝ → (ℕ → ℝ)),
        Γ.length ≤ C * ((D + 1) ^ 3 * (prog.length + 1) + (D + 1) ^ 2 * Fintype.card κ ^ 2 +
          Fintype.card ι) ∧
        ∀ (c : ℕ → ℝ) (ξ₁ : ι → ℝ) (w₁ : κ → ℝ) (A : Matrix κ κ ℝ) (k : κ),
          (Γ.values (enc c ξ₁ w₁ A)).getD (out k) 0 =
            newtonPoly (progOutputs prog c oE) ξ₁ w₁ A D k := by
  refine ⟨10, ?_⟩
  intro ι κ _ _ _ _ prog oE D
  let : Encodable ι := Fintype.toEncodable ι
  let : Encodable κ := Fintype.toEncodable κ
  set it := newtonIter D 0 1 (xiB0 ι κ) (nA0 ι κ) prog oE (initG6 ι κ) (omB0 ι κ) D with hit
  set fin := sumAux 0 it.2 it.1 (D + 1) with hfin
  have main : ∀ (c : ℕ → ℝ) (ξ₁ : ι → ℝ) (w₁ : κ → ℝ) (A : Matrix κ κ ℝ),
      fin.1.length ≤ 10 * ((D + 1) ^ 3 * (prog.length + 1) +
        (D + 1) ^ 2 * Fintype.card κ ^ 2 + Fintype.card ι) ∧
      ∀ k, (fin.1.values (encC c ξ₁ w₁ A)).getD (fin.2 k) 0 =
        newtonPoly (progOutputs prog c oE) ξ₁ w₁ A D k := by
    intro c ξ₁ w₁ A
    obtain ⟨hl6, hz, hn1, hxi, hnA, hom⟩ := init_spec D c ξ₁ w₁ A
    have hc' : ∀ a, encC c ξ₁ w₁ A (sProg ι κ a) = c a := encC_sProg c ξ₁ w₁ A
    obtain ⟨g1, g2, g3⟩ := newtonIter_spec (c := c) (A := A) hc' hz hn1 hxi hnA hom prog oE D
    obtain ⟨f1, f2, f3⟩ := sumAux_spec (hz.mono g1) g3 (D + 1) le_rfl
    refine ⟨?_, fun k => ?_⟩
    · rw [hl6] at g2
      have e : fin.1.length = it.1.length + (D + 1) * Fintype.card κ := f2
      rw [e]
      exact (Nat.add_le_add_right g2 _).trans
        (size_arith (Fintype.card ι) (Fintype.card κ) prog.length D)
    · rw [(f3 k).2, sum_rep ξ₁ (totalDegree_iterate_newtonStep_le _ _ _ _ _ _ _)]
      rfl
  exact ⟨fin.1, fin.2, encC, (main 0 0 0 0).1, fun c ξ₁ w₁ A k => (main c ξ₁ w₁ A).2 k⟩

/-! ### Continuity of the coefficients -/

section CoeffTendsto

variable {β : Type*} {l : Filter β} {σ : Type*}

/-- Coefficientwise convergence of a family of polynomials. -/
def CTo (l : Filter β) (P : β → MvPolynomial σ ℝ) (p : MvPolynomial σ ℝ) : Prop :=
  ∀ m, Tendsto (fun b => (P b).coeff m) l (𝓝 (p.coeff m))

theorem CTo.const (p : MvPolynomial σ ℝ) : CTo l (fun _ => p) p :=
  fun _ => tendsto_const_nhds

theorem CTo.const_C {a : β → ℝ} {a₀ : ℝ} (h : Tendsto a l (𝓝 a₀)) :
    CTo l (fun b => MvPolynomial.C (a b)) (MvPolynomial.C a₀ : MvPolynomial σ ℝ) := by
  classical
  intro m
  simp only [coeff_C]
  split_ifs
  · exact h
  · exact tendsto_const_nhds

theorem CTo.add {P Q : β → MvPolynomial σ ℝ} {p q : MvPolynomial σ ℝ} (hP : CTo l P p)
    (hQ : CTo l Q q) : CTo l (fun b => P b + Q b) (p + q) := fun m => by
  simpa only [coeff_add'] using (hP m).add (hQ m)

theorem CTo.sub {P Q : β → MvPolynomial σ ℝ} {p q : MvPolynomial σ ℝ} (hP : CTo l P p)
    (hQ : CTo l Q q) : CTo l (fun b => P b - Q b) (p - q) := fun m => by
  simpa only [MvPolynomial.coeff_sub] using (hP m).sub (hQ m)

theorem CTo.mul {P Q : β → MvPolynomial σ ℝ} {p q : MvPolynomial σ ℝ} (hP : CTo l P p)
    (hQ : CTo l Q q) : CTo l (fun b => P b * Q b) (p * q) := fun m => by
  classical
  simp only [coeff_mul]
  exact tendsto_finsetSum _ fun x _ => (hP x.1).mul (hQ x.2)

theorem CTo.sum {α : Type*} (s : Finset α) {P : α → β → MvPolynomial σ ℝ}
    {p : α → MvPolynomial σ ℝ} (h : ∀ a ∈ s, CTo l (P a) (p a)) :
    CTo l (fun b => ∑ a ∈ s, P a b) (∑ a ∈ s, p a) := fun m => by
  simp only [coeff_sum]
  exact tendsto_finsetSum _ fun a ha => h a ha m

theorem CTo.prod {α : Type*} (s : Finset α) {P : α → β → MvPolynomial σ ℝ}
    {p : α → MvPolynomial σ ℝ} (h : ∀ a ∈ s, CTo l (P a) (p a)) :
    CTo l (fun b => ∏ a ∈ s, P a b) (∏ a ∈ s, p a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using CTo.const (l := l) (1 : MvPolynomial σ ℝ)
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul
      (ih fun x hx => h x (Finset.mem_insert_of_mem hx))

theorem CTo.pow {P : β → MvPolynomial σ ℝ} {p : MvPolynomial σ ℝ} (h : CTo l P p) (n : ℕ) :
    CTo l (fun b => P b ^ n) (p ^ n) := by
  induction n with
  | zero => simpa using CTo.const (l := l) (1 : MvPolynomial σ ℝ)
  | succ n ih => simpa only [pow_succ] using ih.mul h

theorem CTo.truncDeg {P : β → MvPolynomial ι ℝ} {p : MvPolynomial ι ℝ} (h : CTo l P p)
    (D : ℕ) : CTo l (fun b => truncDeg D (P b)) (truncDeg D p) := fun m => by
  simp only [coeff_truncDeg]
  split_ifs
  · exact h m
  · exact tendsto_const_nhds

theorem bind₁_eq_sum_of_support_subset {τ : Type*} (f : σ → MvPolynomial τ ℝ)
    (p : MvPolynomial σ ℝ) (S : Finset (σ →₀ ℕ)) (hS : p.support ⊆ S) :
    bind₁ f p = ∑ d ∈ S, MvPolynomial.C (p.coeff d) * ∏ i ∈ d.support, f i ^ d i := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  simp only [bind₁_monomial]
  refine Finset.sum_subset hS fun d _ hd => ?_
  rw [notMem_support_iff.mp hd]
  simp

theorem CTo.bind {τ : Type*} {F : β → σ → MvPolynomial τ ℝ} {f : σ → MvPolynomial τ ℝ}
    {P : β → MvPolynomial σ ℝ} {p : MvPolynomial σ ℝ} (S : Finset (σ →₀ ℕ))
    (hPS : ∀ b, (P b).support ⊆ S) (hpS : p.support ⊆ S) (hP : CTo l P p)
    (hF : ∀ i, CTo l (fun b => F b i) (f i)) :
    CTo l (fun b => bind₁ (F b) (P b)) (bind₁ f p) := by
  have e1 : (fun b => MvPolynomial.bind₁ (F b) (P b)) = fun b =>
      ∑ d ∈ S, MvPolynomial.C ((P b).coeff d) * ∏ i ∈ d.support, F b i ^ d i :=
    funext fun b => bind₁_eq_sum_of_support_subset (F b) (P b) S (hPS b)
  rw [e1, bind₁_eq_sum_of_support_subset f p S hpS]
  exact CTo.sum S fun d _ => (CTo.const_C (hP d)).mul (CTo.prod _ fun i _ => (hF i).pow _)

/-- The finite set of monomials of degree at most `B`. -/
def degSet (σ : Type*) [Finite σ] (B : ℕ) : Finset (σ →₀ ℕ) :=
  (Finsupp.finite_of_degree_le (σ := σ) B).toFinset

theorem support_subset_degSet [Finite σ] {p : MvPolynomial σ ℝ} {B : ℕ}
    (h : p.totalDegree ≤ B) : p.support ⊆ degSet σ B := fun m hm => by
  simp only [degSet, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  exact (le_totalDegree hm).trans h

end CoeffTendsto

/-- **Lemma 3.4 (a)**: the coefficients of the `gᵢ` depend continuously (indeed polynomially)
on the coefficients of `E` (of bounded degree) and on `ξ₁, w₁, A`. -/
theorem tendsto_coeff_newtonPoly {β : Type*} {l : Filter β}
    {Eb : β → κ → MvPolynomial (ι ⊕ κ) ℝ} {E : κ → MvPolynomial (ι ⊕ κ) ℝ}
    {ξb : β → ι → ℝ} {ξ₁ : ι → ℝ} {wb : β → κ → ℝ} {w₁ : κ → ℝ}
    {Ab : β → Matrix κ κ ℝ} {A : Matrix κ κ ℝ} (B : ℕ)
    (hdeg : ∀ b k, (Eb b k).totalDegree ≤ B) (hdegE : ∀ k, (E k).totalDegree ≤ B)
    (hE : ∀ k m, Tendsto (fun b => (Eb b k).coeff m) l (𝓝 ((E k).coeff m)))
    (hξ : Tendsto ξb l (𝓝 ξ₁)) (hw : Tendsto wb l (𝓝 w₁)) (hA : Tendsto Ab l (𝓝 A))
    (D : ℕ) (k : κ) (m : ι →₀ ℕ) :
    Tendsto (fun b => (newtonPoly (Eb b) (ξb b) (wb b) (Ab b) D k).coeff m) l
      (𝓝 ((newtonPoly E ξ₁ w₁ A D k).coeff m)) := by
  have hξi : ∀ i, Tendsto (fun b => ξb b i) l (𝓝 (ξ₁ i)) := fun i => tendsto_pi_nhds.1 hξ i
  have hAkl : ∀ k j, Tendsto (fun b => Ab b k j) l (𝓝 (A k j)) := fun k j =>
    tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hA k) j
  have hit : ∀ n k, CTo l
      (fun b => (newtonStep (Eb b) (ξb b) (Ab b) D)^[n] (fun j => MvPolynomial.C (wb b j)) k)
      ((newtonStep E ξ₁ A D)^[n] (fun j => MvPolynomial.C (w₁ j)) k) := by
    intro n
    induction n with
    | zero => intro k; exact CTo.const_C (tendsto_pi_nhds.1 hw k)
    | succ n ih =>
      intro k
      simp only [Function.iterate_succ_apply']
      refine CTo.truncDeg ((ih k).sub (CTo.sum _ fun j _ => (CTo.const_C (hAkl k j)).mul ?_)) D
      refine CTo.bind (degSet _ B) (fun b => support_subset_degSet (hdeg b j))
        (support_subset_degSet (hdegE j)) (hE j) fun v => ?_
      cases v with
      | inl i => exact (CTo.const_C (hξi i)).add (CTo.const _)
      | inr j' => exact ih j'
  refine CTo.bind (degSet _ D)
    (fun b => support_subset_degSet (totalDegree_iterate_newtonStep_le _ _ _ _ _ _ _))
    (support_subset_degSet (totalDegree_iterate_newtonStep_le _ _ _ _ _ _ _)) (hit D k)
    (fun i => (CTo.const _).sub (CTo.const_C (hξi i))) m

/-! ### Part (b): Newton iteration converges to the Taylor polynomial -/

theorem truncDeg_add (D : ℕ) (p q : MvPolynomial ι ℝ) :
    truncDeg D (p + q) = truncDeg D p + truncDeg D q := by
  ext m
  simp only [coeff_truncDeg, coeff_add']
  split_ifs <;> simp

theorem truncDeg_neg (D : ℕ) (p : MvPolynomial ι ℝ) :
    truncDeg D (-p) = -truncDeg D p := by
  ext m
  simp only [coeff_truncDeg, coeff_neg]
  split_ifs <;> simp

theorem truncDeg_sub (D : ℕ) (p q : MvPolynomial ι ℝ) :
    truncDeg D (p - q) = truncDeg D p - truncDeg D q := by
  rw [sub_eq_add_neg, truncDeg_add, truncDeg_neg, ← sub_eq_add_neg]

theorem truncDeg_of_totalDegree_le {D : ℕ} {p : MvPolynomial ι ℝ} (hp : p.totalDegree ≤ D) :
    truncDeg D p = p := by
  ext m
  rw [coeff_truncDeg]
  split_ifs with h
  · rfl
  · refine (coeff_eq_zero_of_totalDegree_lt ?_).symm
    rw [← Finsupp.degree_apply]
    omega

/-- `p` has no monomials of degree `< j`. -/
def HighOrd (j : ℕ) (p : MvPolynomial ι ℝ) : Prop :=
  ∀ m : ι →₀ ℕ, m.degree < j → p.coeff m = 0

namespace HighOrd

theorem zero (j : ℕ) : HighOrd j (0 : MvPolynomial ι ℝ) := fun m _ => coeff_zero' m

theorem of_zero (p : MvPolynomial ι ℝ) : HighOrd 0 p := fun _ h => absurd h (Nat.not_lt_zero _)

theorem add {j : ℕ} {p q : MvPolynomial ι ℝ} (hp : HighOrd j p) (hq : HighOrd j q) :
    HighOrd j (p + q) := fun m hm => by rw [coeff_add', hp m hm, hq m hm, add_zero]

theorem neg {j : ℕ} {p : MvPolynomial ι ℝ} (hp : HighOrd j p) : HighOrd j (-p) :=
  fun m hm => by rw [coeff_neg, hp m hm, neg_zero]

theorem sub {j : ℕ} {p q : MvPolynomial ι ℝ} (hp : HighOrd j p) (hq : HighOrd j q) :
    HighOrd j (p - q) := fun m hm => by rw [coeff_sub, hp m hm, hq m hm, sub_zero]

theorem mono {i j : ℕ} (hij : i ≤ j) {p : MvPolynomial ι ℝ} (hp : HighOrd j p) : HighOrd i p :=
  fun m hm => hp m (lt_of_lt_of_le hm hij)

theorem mul {i j : ℕ} {p q : MvPolynomial ι ℝ} (hp : HighOrd i p) (hq : HighOrd j q) :
    HighOrd (i + j) (p * q) := by
  classical
  intro m hm
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  have : x.1.degree + x.2.degree = m.degree := by rw [← map_add, hx]
  by_cases h1 : x.1.degree < i
  · rw [hp _ h1, zero_mul]
  · rw [hq _ (by omega), mul_zero]

theorem mul_left (p : MvPolynomial ι ℝ) {j : ℕ} {q : MvPolynomial ι ℝ} (hq : HighOrd j q) :
    HighOrd j (p * q) := by
  simpa using (of_zero p).mul hq

theorem mul_right {j : ℕ} {p : MvPolynomial ι ℝ} (hp : HighOrd j p) (q : MvPolynomial ι ℝ) :
    HighOrd j (p * q) := by
  simpa using hp.mul (of_zero q)

theorem sum {α : Type*} (s : Finset α) {f : α → MvPolynomial ι ℝ} {j : ℕ}
    (h : ∀ a ∈ s, HighOrd j (f a)) : HighOrd j (∑ a ∈ s, f a) := fun m hm => by
  rw [coeff_sum]
  exact Finset.sum_eq_zero fun a ha => h a ha m hm

theorem truncDeg {j : ℕ} {p : MvPolynomial ι ℝ} (hp : HighOrd j p) (D : ℕ) :
    HighOrd j (truncDeg D p) := fun m hm => by
  rw [coeff_truncDeg, hp m hm, ite_self]

theorem one_of_coeff_zero {p : MvPolynomial ι ℝ} (h : p.coeff 0 = 0) : HighOrd 1 p :=
  fun m hm => by
    have : m = 0 := (Finsupp.degree_eq_zero_iff m).1 (by omega)
    rw [this, h]

theorem eq_zero {D : ℕ} {p : MvPolynomial ι ℝ} (hp : HighOrd (D + 1) p)
    (hdeg : p.totalDegree ≤ D) : p = 0 := by
  ext m
  rw [coeff_zero']
  by_cases h : m.degree ≤ D
  · exact hp m (by omega)
  · refine coeff_eq_zero_of_totalDegree_lt ?_
    rw [← Finsupp.degree_apply]
    omega

end HighOrd

theorem coeff_zero_eq_eval_zero' {σ : Type*} (p : MvPolynomial σ ℝ) : p.coeff 0 = eval 0 p := by
  rw [eval_zero]
  rfl

theorem eval_bind₁_nt {σ τ : Type*} (x : τ → ℝ) (f : σ → MvPolynomial τ ℝ)
    (p : MvPolynomial σ ℝ) : eval x (bind₁ f p) = eval (fun i => eval x (f i)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp => simp [hp]

/-- First-order expansion of a polynomial substitution:
`p(a, T + δ) = p(a, T) + ∑ₖ ∂ₖp(a, T) δₖ + O(δ²)`. -/
theorem bind₁_expansion (a : ι → MvPolynomial ι ℝ) {T δ : κ → MvPolynomial ι ℝ} {j : ℕ}
    (hδ : ∀ k, HighOrd j (δ k)) (p : MvPolynomial (ι ⊕ κ) ℝ) :
    HighOrd j (bind₁ (Sum.elim a (fun k => T k + δ k)) p - bind₁ (Sum.elim a T) p) ∧
    HighOrd (j + j) (bind₁ (Sum.elim a (fun k => T k + δ k)) p - bind₁ (Sum.elim a T) p -
      ∑ k, bind₁ (Sum.elim a T) (pderiv (Sum.inr k) p) * δ k) := by
  set φ := bind₁ (Sum.elim a (fun k => T k + δ k))
  set ψ := bind₁ (Sum.elim a T)
  induction p using MvPolynomial.induction_on with
  | C r => simp [φ, ψ, HighOrd.zero]
  | add p q hp hq =>
    refine ⟨?_, ?_⟩
    · convert hp.1.add hq.1 using 1
      simp only [map_add]; ring
    · convert hp.2.add hq.2 using 1
      simp only [map_add, add_mul, Finset.sum_add_distrib]; ring
  | mul_X p v hp =>
    have hx : HighOrd j (φ (X v) - ψ (X v)) := by
      cases v with
      | inl i => simp [φ, ψ, HighOrd.zero]
      | inr k => simpa [φ, ψ] using hδ k
    have hs : ∑ k, ψ (pderiv (Sum.inr k) (X v)) * δ k = φ (X v) - ψ (X v) := by
      cases v with
      | inl i => simp [φ, ψ, pderiv_X]
      | inr k' => simp [φ, ψ, pderiv_X, Pi.single_apply]
    have e : ∑ k, ψ (pderiv (Sum.inr k) (p * X v)) * δ k =
        (∑ k, ψ (pderiv (Sum.inr k) p) * δ k) * ψ (X v) +
          ψ p * ∑ k, ψ (pderiv (Sum.inr k) (X v)) * δ k := by
      rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [pderiv_mul, map_add, map_mul, map_mul]
      ring
    rw [hs] at e
    constructor
    · convert (hp.1.mul_right (φ (X v))).add (hx.mul_left (ψ p)) using 1
      simp only [map_mul]; ring
    · convert (hp.2.mul_right (ψ (X v))).add (hp.1.mul hx) using 1
      rw [e]
      simp only [map_mul]; ring

/-- One Newton step gains one order of accuracy. -/
theorem newtonStep_highOrd (E : κ → MvPolynomial (ι ⊕ κ) ℝ) (ξ₁ : ι → ℝ) (w₁ : κ → ℝ)
    (A : Matrix κ κ ℝ) (D : ℕ) (hA : A * jacW E (Sum.elim ξ₁ w₁) = 1)
    (T : κ → MvPolynomial ι ℝ) (hT : ∀ k, (T k).totalDegree ≤ D)
    (hT0 : ∀ k, (T k).coeff 0 = w₁ k)
    (hET : ∀ l, HighOrd (D + 1)
      (bind₁ (Sum.elim (fun i => MvPolynomial.C (ξ₁ i) + X i) T) (E l)))
    {j : ℕ} (hj : j + 1 ≤ D) (Ω : κ → MvPolynomial ι ℝ)
    (hΩ : ∀ k, HighOrd (j + 1) (Ω k - T k)) (k : κ) :
    HighOrd (j + 2) (newtonStep E ξ₁ A D Ω k - T k) := by
  set a : ι → MvPolynomial ι ℝ := fun i => MvPolynomial.C (ξ₁ i) + X i with ha
  set δ : κ → MvPolynomial ι ℝ := fun k => Ω k - T k with hδ
  have hΩeq : Ω = fun k => T k + δ k := funext fun k => by simp [δ]
  set ψ := bind₁ (Sum.elim a T) with hψ
  set J := jacW E (Sum.elim ξ₁ w₁) with hJ
  have hψ0 : ∀ q, (ψ q - MvPolynomial.C (eval (Sum.elim ξ₁ w₁) q)).coeff 0 = 0 := by
    intro q
    have hpt : (fun v => eval 0 (Sum.elim a T v)) = Sum.elim ξ₁ w₁ := by
      funext v
      cases v with
      | inl i => simp [a]
      | inr k =>
        show eval 0 (T k) = w₁ k
        rw [← coeff_zero_eq_eval_zero', hT0]
    rw [coeff_sub, coeff_C, coeff_zero_eq_eval_zero', hψ, eval_bind₁_nt, hpt]
    simp
  have hs : ∀ l, HighOrd (j + 2)
      (bind₁ (Sum.elim a Ω) (E l) - ∑ k', MvPolynomial.C (J l k') * δ k') := by
    intro l
    have h1 := (bind₁_expansion a (T := T) hΩ (E l)).2
    rw [← hΩeq] at h1
    have h2 : HighOrd (j + 2) (ψ (E l)) := (hET l).mono (by omega)
    have h3 : ∀ k', HighOrd (j + 2)
        ((ψ (pderiv (Sum.inr k') (E l)) - MvPolynomial.C (J l k')) * δ k') := fun k' => by
      have := (HighOrd.one_of_coeff_zero (hψ0 (pderiv (Sum.inr k') (E l)))).mul (hΩ k')
      rw [show 1 + (j + 1) = j + 2 by omega] at this
      simpa [J, jacW] using this
    convert ((h1.mono (by omega)).add h2).add (HighOrd.sum Finset.univ fun k' _ => h3 k')
      using 1
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  have hAJ : ∑ l, MvPolynomial.C (A k l) * ∑ k', MvPolynomial.C (J l k') * δ k' = δ k := by
    calc ∑ l, MvPolynomial.C (A k l) * ∑ k', MvPolynomial.C (J l k') * δ k'
        = ∑ k', MvPolynomial.C ((A * J) k k') * δ k' := by
          simp only [Finset.mul_sum, Matrix.mul_apply, map_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k' _ => Finset.sum_congr rfl fun l _ => ?_
          rw [MvPolynomial.C_mul]
          ring
      _ = δ k := by
          rw [hA]
          simp [Matrix.one_apply]
  have hTT : truncDeg D (T k) = T k := truncDeg_of_totalDegree_le (hT k)
  have key : newtonStep E ξ₁ A D Ω k - T k = truncDeg D (-∑ l, MvPolynomial.C (A k l) *
      (bind₁ (Sum.elim a Ω) (E l) - ∑ k', MvPolynomial.C (J l k') * δ k')) := by
    show truncDeg D (Ω k - ∑ l, MvPolynomial.C (A k l) * bind₁ (Sum.elim a Ω) (E l)) - T k = _
    conv_lhs => rw [← hTT]
    rw [← truncDeg_sub]
    congr 1
    simp only [mul_sub, Finset.sum_sub_distrib, hAJ]
    simp only [δ]
    ring
  rw [key]
  exact ((HighOrd.sum _ fun l _ => (hs l).mul_left _).neg).truncDeg D

/-- A polynomial map which is `O(‖χ‖ⁿ)` when all monomials have degree `≥ n`. -/
theorem isBigO_of_highOrd {n : ℕ} {Q : MvPolynomial ι ℝ} (hQ : HighOrd n Q) :
    (fun χ : ι → ℝ => eval χ Q) =O[𝓝 0] fun χ => ‖χ‖ ^ n := by
  have hev : (fun χ : ι → ℝ => eval χ Q) =
      fun χ => ∑ d ∈ Q.support, Q.coeff d * ∏ i, χ i ^ d i :=
    funext fun χ => eval_eq' χ Q
  rw [hev]
  refine Asymptotics.IsBigO.fun_sum fun d hd => ?_
  have hdeg : n ≤ d.degree := by
    by_contra h
    exact (mem_support_iff.1 hd) (hQ d (by omega))
  refine Asymptotics.IsBigO.const_mul_left ?_ _
  refine Asymptotics.IsBigO.of_bound 1 ?_
  have hball : ∀ᶠ χ in 𝓝 (0 : ι → ℝ), ‖χ‖ ≤ 1 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ι → ℝ) one_pos] with χ hχ
    rw [Metric.mem_ball, dist_zero_right] at hχ
    exact hχ.le
  filter_upwards [hball] with χ hχ
  rw [one_mul, norm_prod, norm_pow, norm_norm]
  calc ∏ i, ‖χ i ^ d i‖ ≤ ∏ i, ‖χ‖ ^ d i :=
        Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => by
          rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm χ i) _
    _ = ‖χ‖ ^ d.degree := by rw [Finset.prod_pow_eq_pow_sum, Finsupp.degree_eq_sum]
    _ ≤ ‖χ‖ ^ n := pow_le_pow_of_le_one (norm_nonneg _) hχ hdeg

/-- If a polynomial map is `o(‖χ‖ᴰ)` at `0`, it has no monomials of degree `≤ D`. -/
theorem highOrd_of_isLittleO {D : ℕ} {P : MvPolynomial ι ℝ}
    (h : (fun χ => eval χ P) =o[𝓝 0] fun χ => ‖χ‖ ^ D) : HighOrd (D + 1) P := by
  have hQ : HighOrd (D + 1) (P - truncDeg D P) := fun m hm => by
    rw [coeff_sub, coeff_truncDeg, ite_eq_left (by omega), sub_self]
  have hpow : (fun χ : ι → ℝ => ‖χ‖ ^ (D + 1)) =o[𝓝 0] fun χ => ‖χ‖ ^ D :=
    (Asymptotics.isLittleO_pow_pow (𝕜 := ℝ) (Nat.lt_succ_self D)).comp_tendsto tendsto_norm_zero
  have hQo := (isBigO_of_highOrd hQ).trans_isLittleO hpow
  have h0 : truncDeg D P = 0 := by
    refine eq_of_isLittleO (ξ₁ := 0) (totalDegree_truncDeg_le D P) (by simp) ?_
    refine (h.sub hQo).congr (fun χ => by simp [map_sub]) (fun χ => by simp)
  intro m hm
  have := congrArg (fun p => p.coeff m) h0
  rwa [coeff_truncDeg, ite_eq_left (by omega), coeff_zero'] at this

theorem contDiff_eval_poly {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℝ) :
    ContDiff ℝ 1 (fun x : σ → ℝ => eval x p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp => simpa using hp.mul (contDiff_apply ℝ (fun _ : σ => ℝ) i)

theorem eval_taylorPoly_self (D : ℕ) (g : (ι → ℝ) → ℝ) (ξ₁ : ι → ℝ) :
    eval ξ₁ (taylorPoly D g ξ₁) = g ξ₁ := by
  unfold taylorPoly
  rw [map_sum, Finset.sum_range_succ']
  simp only [map_mul, eval_C, eval_jetTerm, sub_self]
  have : ∀ j : ℕ, (iteratedFDeriv ℝ (j + 1) g ξ₁) (fun _ => (0 : ι → ℝ)) = 0 :=
    fun j => ContinuousMultilinearMap.map_zero _
  simp [this]

/-- **Lemma 3.4 (b).** -/
theorem newtonPoly_eq_taylorPoly (E : κ → MvPolynomial (ι ⊕ κ) ℝ) (ξ₁ : ι → ℝ) (w₁ : κ → ℝ)
    (A : Matrix κ κ ℝ) (D : ℕ)
    (hE : ∀ k, eval (Sum.elim ξ₁ w₁) (E k) = 0) (hA : A * jacW E (Sum.elim ξ₁ w₁) = 1)
    (ω : (ι → ℝ) → (κ → ℝ)) (hω₁ : ω ξ₁ = w₁) (hωD : ContDiffAt ℝ D ω ξ₁)
    (hωE : ∀ᶠ ξ in 𝓝 ξ₁, ∀ k, eval (Sum.elim ξ (ω ξ)) (E k) = 0) (k : κ) :
    newtonPoly E ξ₁ w₁ A D k = taylorPoly D (fun ξ => ω ξ k) ξ₁ := by
  set τk : κ → MvPolynomial ι ℝ := fun k => taylorPoly D (fun ξ => ω ξ k) ξ₁ with hτk
  set T : κ → MvPolynomial ι ℝ :=
    fun k => bind₁ (fun i => X i + MvPolynomial.C (ξ₁ i)) (τk k) with hTdef
  have hωk : ∀ k, ContDiffAt ℝ D (fun ξ => ω ξ k) ξ₁ := contDiffAt_pi.1 hωD
  have hτ0 : ∀ k, eval ξ₁ (τk k) = w₁ k := fun k => by
    simp only [τk]; rw [eval_taylorPoly_self, hω₁]
  have hT : ∀ k, (T k).totalDegree ≤ D := fun k =>
    (totalDegree_bind₁_le _ (fun i => totalDegree_X_add_C_le i _) _).trans
      (totalDegree_taylorPoly_le _ _ _)
  have hevalT : ∀ k χ, eval χ (T k) = eval (fun i => χ i + ξ₁ i) (τk k) := by
    intro k χ
    simp only [T]
    rw [eval_bind₁_nt]
    simp
  have hT0 : ∀ k, (T k).coeff 0 = w₁ k := fun k => by
    rw [coeff_zero_eq_eval_zero', hevalT]
    simpa using hτ0 k
  -- the analytic input: `E(ξ, T(ξ - ξ₁)) = o(‖ξ - ξ₁‖ᴰ)`
  have hF : ∀ l, (fun ξ => eval (Sum.elim ξ (fun k => eval ξ (τk k))) (E l)) =o[𝓝 ξ₁]
      (fun ξ => ‖ξ - ξ₁‖ ^ D) := by
    intro l
    obtain ⟨K, t, ht, hK⟩ :=
      (contDiff_eval_poly (E l)).contDiffAt.exists_lipschitzOnWith (x := Sum.elim ξ₁ w₁)
    have hτv : Tendsto (fun ξ => Sum.elim ξ (fun k => eval ξ (τk k))) (𝓝 ξ₁)
        (𝓝 (Sum.elim ξ₁ w₁)) := by
      have hc : Continuous (fun ξ : ι → ℝ => Sum.elim ξ (fun k => eval ξ (τk k))) :=
        continuous_pi fun v => by
          cases v with
          | inl i => exact continuous_apply i
          | inr k => exact MvPolynomial.continuous_eval _
      have := hc.tendsto ξ₁
      have e : Sum.elim ξ₁ (fun k => eval ξ₁ (τk k)) = Sum.elim ξ₁ w₁ := by
        congr 1; funext k; exact hτ0 k
      rwa [e] at this
    have hωv : Tendsto (fun ξ => Sum.elim ξ (ω ξ)) (𝓝 ξ₁) (𝓝 (Sum.elim ξ₁ w₁)) := by
      rw [tendsto_pi_nhds]
      intro v
      cases v with
      | inl i => simpa using (continuous_apply i).tendsto ξ₁
      | inr k =>
        have := (hωk k).continuousAt.tendsto
        simp only [hω₁] at this
        simpa using this
    have hdiff : (fun ξ => (fun k => eval ξ (τk k)) - ω ξ) =o[𝓝 ξ₁]
        fun ξ => ‖ξ - ξ₁‖ ^ D := by
      rw [Asymptotics.isLittleO_pi]
      intro k
      refine (taylorPoly_isLittleO (hωk k)).neg_left.congr_left fun ξ => ?_
      simp [τk]
    refine Asymptotics.IsBigO.trans_isLittleO ?_ hdiff
    refine Asymptotics.IsBigO.of_bound K ?_
    filter_upwards [hτv.eventually_mem ht, hωv.eventually_mem ht, hωE] with ξ h1 h2 h3
    have hL := hK.dist_le_mul _ h1 _ h2
    rw [dist_eq_norm, dist_eq_norm, h3 l, sub_zero] at hL
    refine hL.trans ?_
    gcongr
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun v => ?_
    cases v with
    | inl i => simp
    | inr k =>
      simpa using norm_le_pi_norm ((fun k => eval ξ (τk k)) - ω ξ) k
  have hET : ∀ l, HighOrd (D + 1)
      (bind₁ (Sum.elim (fun i => MvPolynomial.C (ξ₁ i) + X i) T) (E l)) := by
    intro l
    apply highOrd_of_isLittleO
    have hT' : Tendsto (fun χ : ι → ℝ => ξ₁ + χ) (𝓝 0) (𝓝 ξ₁) := by
      simpa using (tendsto_const_nhds (x := ξ₁)).add (tendsto_id (x := 𝓝 (0 : ι → ℝ)))
    refine ((hF l).comp_tendsto hT').congr (fun χ => ?_) (fun χ => by simp)
    simp only [Function.comp_apply, eval_bind₁_nt]
    have hpt : (fun v => eval χ (Sum.elim (fun i => MvPolynomial.C (ξ₁ i) + X i) T v)) =
        Sum.elim (ξ₁ + χ) (fun k => eval (ξ₁ + χ) (τk k)) := by
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

end ClassSep
