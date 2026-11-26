import ClassSeparations.Second.Data
import ClassSeparations.Cert.Isolate
import ClassSeparations.Basic.Cells

/-!
# Isolating a certificate (§6.1, Lemma 6.2)

Let a tree `T` on inputs `(x, y, z, u)` verify `y = f(x)` with `∃ z ∀ u` over an open set `U`,
and let `ball xc rc ⊆ U`.  The set
`F = {(x, z) : x ∈ ball xc rc, T accepts (x, f(x), z, u) for all u}` is semialgebraic
(`isSA_Fset`) and projects onto the ball, so Lemma 4.1 applies.  With the coordinates `I` of
`z` fixed to `z₀`, we write `w = (y, z')` with `z' ∈ ℝ^{k ∖ I}` (`κI I = Unit ⊕ (k ∖ I)`),
`z = zOf w`, and `φ(x) = (f(x), ζ'(x))` (`phiOf`).

**Lemma 6.2** (`lemma_6_2`).  There are `ρ, r₀ > 0` with `closedBall x₀ ρ ⊆ ball x₀ r₃`,
`|φ(x) - φ(x₀)| ≤ r₀/2` on `K = closedBall x₀ ρ`, and for `x ∈ K` and `|w - φ(x₀)| ≤ r₀`:
some `u` is rejected at `(x, y, zOf w, u)` iff `w ≠ φ(x)`.
-/

noncomputable section

open MvPolynomial Set Filter Topology

namespace ClassSep

namespace SetupAux

/-! ### Semialgebraicity of the accepted inputs -/

section SA

variable {ι : Type}

theorem isSA_allZero' (l : List (MvPolynomial ι ℝ)) :
    IsSA {w : ι → ℝ | ∀ p ∈ l, eval w p = 0} := by
  induction l with
  | nil => simpa using (isSA_univ : IsSA (Set.univ : Set (ι → ℝ)))
  | cons p l ih =>
    have := (isSA_zero p).inter ih
    convert this using 1
    ext w
    simp

theorem isSA_allPos' (l : List (MvPolynomial ι ℝ)) :
    IsSA {w : ι → ℝ | ∀ p ∈ l, 0 < eval w p} := by
  induction l with
  | nil => simpa using (isSA_univ : IsSA (Set.univ : Set (ι → ℝ)))
  | cons p l ih =>
    have := (isSA_pos p).inter ih
    convert this using 1
    ext w
    simp

theorem isSA_carrier' (B : Cell ι) : IsSA B.carrier :=
  (isSA_allZero' B.eqs).inter (isSA_allPos' B.poss)

theorem isSA_cells (L : List (Cell ι)) : IsSA {w : ι → ℝ | ∃ B ∈ L, w ∈ B.carrier} := by
  induction L with
  | nil => simpa using (isSA_empty : IsSA (∅ : Set (ι → ℝ)))
  | cons B L ih =>
    have := (isSA_carrier' B).union ih
    convert this using 1
    ext w
    simp

/-- The inputs accepted by a tree form a semialgebraic set. -/
theorem isSA_accepts (T : Tree ι) : IsSA {w : ι → ℝ | T.Accepts w} := by
  obtain ⟨L, -, hL⟩ := cells T T.depth le_rfl {some true}
  convert isSA_cells L using 1
  ext w
  have := Set.ext_iff.1 hL w
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.mem_iUnion, exists_prop] at this
  simp only [Set.mem_ofPred_eq, Tree.Accepts]
  exact this

end SA

/-! ### The set `F` -/

section Fset

variable {σ : Type} [Fintype σ] {k l : ℕ}

/-- `F = {(x, z) : x ∈ ball xc rc, T accepts (x, f(x), z, u) for all u}`. -/
def Fset (T : Tree (σ ⊕ Unit ⊕ Fin k ⊕ Fin l)) (f : MvPolynomial σ ℝ) (xc : σ → ℝ) (rc : ℝ) :
    Set (σ ⊕ Fin k → ℝ) :=
  {v | v ∘ Sum.inl ∈ Metric.ball xc rc ∧
    ∀ u, T.Accepts (inp4 (v ∘ Sum.inl) (eval (v ∘ Sum.inl) f) (v ∘ Sum.inr) u)}

theorem mem_Fset {T : Tree (σ ⊕ Unit ⊕ Fin k ⊕ Fin l)} {f : MvPolynomial σ ℝ} {xc : σ → ℝ}
    {rc : ℝ} (x : σ → ℝ) (z : Fin k → ℝ) :
    Sum.elim x z ∈ Fset T f xc rc ↔
      x ∈ Metric.ball xc rc ∧ ∀ u, T.Accepts (inp4 x (eval x f) z u) := Iff.rfl

theorem isSA_Fset (T : Tree (σ ⊕ Unit ⊕ Fin k ⊕ Fin l)) (f : MvPolynomial σ ℝ) (xc : σ → ℝ)
    (rc : ℝ) : IsSA (Fset T f xc rc) := by
  -- the accepted inputs `(x, f(x), z, u)`, as a set of `((x, z), u)`
  let π : σ ⊕ Unit ⊕ Fin k ⊕ Fin l → MvPolynomial ((σ ⊕ Fin k) ⊕ Fin l) ℝ :=
    Sum.elim (fun i => X (.inl (.inl i)))
      (Sum.elim (fun _ => rename (fun i => .inl (.inl i)) f)
        (Sum.elim (fun j => X (.inl (.inr j))) (fun j => X (.inr j))))
  have hA := (isSA_accepts T).preimage_poly π
  have hB := hA.forall_sum (γ := Fin l)
  have hC := ((isSA_ball xc rc).preimage_comp (Sum.inl : σ → σ ⊕ Fin k)).inter hB
  convert hC using 1
  ext v
  simp only [Fset, Set.mem_ofPred_eq, Set.mem_inter_iff]
  refine and_congr Iff.rfl (forall_congr' fun u => ?_)
  apply iff_of_eq
  congr 1
  funext a
  rcases a with i | _ | j | j
  · simp [π, inp4]
  · simp [π, inp4, eval_rename]; rfl
  · simp [π, inp4]
  · simp [π, inp4]

end Fset

/-! ### The coordinates `w = (y, z')` -/

section Coords

variable {σ : Type} [Fintype σ] {k : ℕ}

/-- `κ = Unit ⊕ (k ∖ I)`: the coordinates `w = (y, z')`. -/
abbrev κI {k : ℕ} (I : Finset (Fin k)) : Type := Unit ⊕ {i : Fin k // i ∉ I}

/-- The certificate `z = (z♭, z')` determined by `w = (y, z')`. -/
def zOf {I : Finset (Fin k)} (z₀ : Fin k → ℝ) (w : κI I → ℝ) : Fin k → ℝ :=
  fun i => if h : i ∈ I then z₀ i else w (.inr ⟨i, h⟩)

/-- `φ(x) = (f(x), ζ'(x))`. -/
def phiOf (I : Finset (Fin k)) (f : MvPolynomial σ ℝ) (ζ : (σ → ℝ) → (Fin k → ℝ)) (x : σ → ℝ) :
    κI I → ℝ :=
  Sum.elim (fun _ => eval x f) (fun i => ζ x i.1)

theorem continuous_zOf {I : Finset (Fin k)} (z₀ : Fin k → ℝ) :
    Continuous (zOf (I := I) z₀) := by
  refine continuous_pi fun i => ?_
  by_cases h : i ∈ I
  · simp only [zOf, h, ↓reduceDIte]; exact continuous_const
  · simp only [zOf, h, ↓reduceDIte]; exact continuous_apply _

omit [Fintype σ] in
theorem continuousOn_phiOf (I : Finset (Fin k)) (f : MvPolynomial σ ℝ)
    {ζ : (σ → ℝ) → (Fin k → ℝ)} {S : Set (σ → ℝ)} (hζ : ContinuousOn ζ S) :
    ContinuousOn (phiOf I f ζ) S := by
  refine continuousOn_pi.2 fun a => ?_
  rcases a with _ | i
  · exact (MvPolynomial.continuous_eval f).continuousOn
  · exact continuousOn_pi.1 hζ i.1

end Coords

/-! ### Lemma 6.2 -/

section Goodz

theorem sqd_self' {κ : Type} [Fintype κ] (u : κ → ℝ) : sqDist u u = 0 := by simp [sqDist]

theorem sqd_abs_le' {κ : Type} [Fintype κ] {u w : κ → ℝ} {r : ℝ} (hr : 0 ≤ r)
    (h : sqDist u w ≤ r ^ 2) (c : κ) : |u c - w c| ≤ r := by
  have h1 : (u c - w c) ^ 2 ≤ sqDist u w :=
    Finset.single_le_sum (f := fun j => (u j - w j) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ c)
  have h2 : (u c - w c) ^ 2 ≤ r ^ 2 := h1.trans h
  exact abs_le.2 ⟨by nlinarith, by nlinarith⟩

variable {σ : Type} [Fintype σ] {k l : ℕ}

/-- **Lemma 6.2.** -/
theorem lemma_6_2 (T : Tree (σ ⊕ Unit ⊕ Fin k ⊕ Fin l)) (f : MvPolynomial σ ℝ)
    (U : Set (σ → ℝ))
    (hdec : ∀ x ∈ U, ∀ y : ℝ, (∃ z, ∀ u, T.Accepts (inp4 x y z u)) ↔ y = eval x f)
    (xc : σ → ℝ) (rc : ℝ) (hball : Metric.ball xc rc ⊆ U)
    (x₀ : σ → ℝ) (z₀ : Fin k → ℝ) (N : Set (σ ⊕ Fin k → ℝ)) (I : Finset (Fin k)) (r₃ : ℝ)
    (ζ : (σ → ℝ) → (Fin k → ℝ)) (hN : IsOpen N) (hx₀N : Sum.elim x₀ z₀ ∈ N) (hr₃ : 0 < r₃)
    (hsub : Metric.ball x₀ r₃ ⊆ Metric.ball xc rc) (hζ₀ : ζ x₀ = z₀)
    (hζ : ContinuousOn ζ (Metric.ball x₀ r₃))
    (hiso : ∀ x ∈ Metric.ball x₀ r₃, ∀ z : Fin k → ℝ,
      (Sum.elim x z ∈ Fset T f xc rc ∩ N ∧ ∀ i ∈ I, z i = z₀ i) ↔ z = ζ x) :
    ∃ ρ r₀ : ℝ, 0 < ρ ∧ 0 < r₀ ∧ Metric.closedBall x₀ ρ ⊆ Metric.ball x₀ r₃ ∧
      (∀ x ∈ Metric.closedBall x₀ ρ,
        sqDist (phiOf I f ζ x) (phiOf I f ζ x₀) ≤ (r₀ / 2) ^ 2) ∧
      ∀ x ∈ Metric.closedBall x₀ ρ, ∀ w : κI I → ℝ, sqDist w (phiOf I f ζ x₀) ≤ r₀ ^ 2 →
        ((∃ u, ¬ T.Accepts (inp4 x (w (.inl ())) (zOf z₀ w) u)) ↔ w ≠ phiOf I f ζ x) := by
  set φ := phiOf I f ζ with hφdef
  have hx₀ : x₀ ∈ Metric.ball x₀ r₃ := Metric.mem_ball_self hr₃
  have hφc : ContinuousOn φ (Metric.ball x₀ r₃) := continuousOn_phiOf I f hζ
  -- `ζ x` has the fixed coordinates `z₀` on `I`
  have hζI : ∀ x ∈ Metric.ball x₀ r₃, ∀ i ∈ I, ζ x i = z₀ i := fun x hx =>
    ((hiso x hx (ζ x)).2 rfl).2
  have hzφ : ∀ x ∈ Metric.ball x₀ r₃, zOf z₀ (φ x) = ζ x := by
    intro x hx
    funext i
    by_cases hi : i ∈ I
    · simp [zOf, hi, hζI x hx i hi]
    · simp [zOf, hi, φ, phiOf]
  -- the neighbourhood `N`
  have hG : Continuous fun p : (σ → ℝ) × (κI I → ℝ) => (Sum.elim p.1 (zOf z₀ p.2) : σ ⊕ Fin k → ℝ) := by
    refine continuous_pi fun a => ?_
    rcases a with i | i
    · exact (continuous_apply i).comp continuous_fst
    · exact (continuous_apply i).comp ((continuous_zOf z₀).comp continuous_snd)
  have hG₀ : Sum.elim x₀ (zOf z₀ (φ x₀)) ∈ N := by rw [hzφ x₀ hx₀, hζ₀]; exact hx₀N
  obtain ⟨ε, hε, hεN⟩ := Metric.isOpen_iff.1 (hN.preimage hG) (x₀, φ x₀) hG₀
  set r₀ := ε / 2 with hr₀
  have hr₀pos : 0 < r₀ := by positivity
  -- continuity of `φ` at `x₀`
  have hφt : Tendsto (fun x => sqDist (φ x) (φ x₀)) (𝓝 x₀) (𝓝 0) := by
    have h1 : Tendsto φ (𝓝 x₀) (𝓝 (φ x₀)) :=
      hφc.continuousAt (Metric.isOpen_ball.mem_nhds hx₀)
    have h2 : Continuous fun w : κI I → ℝ => sqDist w (φ x₀) := by
      unfold sqDist; fun_prop
    have := (h2.tendsto (φ x₀)).comp h1
    rwa [Function.comp_def, sqd_self'] at this
  obtain ⟨δ, hδ, hδφ⟩ := Metric.eventually_nhds_iff.1
    (hφt.eventually (gt_mem_nhds (show (0 : ℝ) < (r₀ / 2) ^ 2 by positivity)))
  set ρ := min (min δ ε) r₃ / 2 with hρ
  have hρpos : 0 < ρ := by positivity
  have hK : ∀ x ∈ Metric.closedBall x₀ ρ, dist x x₀ < δ ∧ dist x x₀ < ε ∧ x ∈ Metric.ball x₀ r₃ := by
    intro x hx
    rw [Metric.mem_closedBall] at hx
    have h1 : min (min δ ε) r₃ ≤ min δ ε := min_le_left _ _
    have h2 : min (min δ ε) r₃ ≤ r₃ := min_le_right _ _
    have h3 : min δ ε ≤ δ := min_le_left _ _
    have h4 : min δ ε ≤ ε := min_le_right _ _
    have h5 : 0 < min (min δ ε) r₃ := by positivity
    refine ⟨by linarith, by linarith, Metric.mem_ball.2 (by linarith)⟩
  refine ⟨ρ, r₀, hρpos, hr₀pos, fun x hx => (hK x hx).2.2, fun x hx => (hδφ (hK x hx).1).le, ?_⟩
  intro x hx w hw
  obtain ⟨-, hxε, hx₃⟩ := hK x hx
  have hxU : x ∈ U := hball (hsub hx₃)
  -- `(x, zOf w) ∈ N`
  have hwN : Sum.elim x (zOf z₀ w) ∈ N := by
    have : (x, w) ∈ Metric.ball (x₀, φ x₀) ε := by
      rw [Metric.mem_ball, Prod.dist_eq]
      refine max_lt hxε (lt_of_le_of_lt ?_ (half_lt_self hε))
      rw [dist_pi_le_iff hr₀pos.le]
      intro c
      rw [Real.dist_eq]
      exact sqd_abs_le' hr₀pos.le hw c
    exact hεN this
  constructor
  · rintro ⟨u, hu⟩ rfl
    apply hu
    rw [hzφ x hx₃]
    have := ((hiso x hx₃ (ζ x)).2 rfl).1.1
    exact this.2 u
  · intro hne
    by_contra hcon
    push Not at hcon
    have hy : w (.inl ()) = eval x f := (hdec x hxU _).1 ⟨_, hcon⟩
    have hF : Sum.elim x (zOf z₀ w) ∈ Fset T f xc rc := by
      refine (mem_Fset x _).2 ⟨hsub hx₃, fun u => ?_⟩
      rw [← hy]; exact hcon u
    have hz := (hiso x hx₃ (zOf z₀ w)).1 ⟨⟨hF, hwN⟩, fun i hi => by simp [zOf, hi]⟩
    apply hne
    funext a
    rcases a with _ | ⟨i, hi⟩
    · exact hy
    · have := congrFun hz i
      simp only [zOf, hi, ↓reduceDIte] at this
      exact this

end Goodz

end SetupAux

end ClassSep
