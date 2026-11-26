import ClassSeparations.Core.Local
import ClassSeparations.Cert.Isolate

/-!
# Value functions (§4.4, Proposition 4.5)

**Proposition 4.5.**  Let `Q ∈ ℝ[ξ, s, ν]` (`ξ ∈ ℝᴺ`, `s ∈ ℝ`, `ν ∈ ℝ^κ`) be nonnegative and
computed by a straight-line program with `ℓ` operations.  Let `A ⊆ ℝᴺ` be a nonempty open
semialgebraic set, and suppose that for every `ξ ∈ A` the coordinate `s` attains a maximum
`v(ξ)` on `{(s, ν) : Q(ξ, s, ν) = 0}`.  Let `D ≥ 1`.  Then there are a dense semialgebraic
`A° ⊆ A` and finitely many circuit graphs, each with at most
`C((D+1)³ℓ + (D+1)²(κ+1)² + N)` gates, such that for every `ξ₁ ∈ A°` the function `v` is of
class `C^D` near `ξ₁` and its Taylor polynomial of order `D` at `ξ₁` is a coefficientwise limit
of polynomials of degree `≤ D` computed by one of these graphs with real constants.

The variables of `Q` are `ι ⊕ Option κ`, with `s = none`.  The finitely many graphs depend only
on the program graph, `ι`, `κ` and `D`; each comes with an output gate.

## Proof

There is one graph for each set `I ⊆ κ` of coordinates fixed by Lemma 4.1: the circuit graph
of Theorem 3.5 for the program graph `substProg I prog` of `Q̃(ξ, s, u) = Q(ξ, s, (a, u))`
(the values `a` become constant slots), with the output gate of the coordinate `s`.

Instead of the open dense set `A₁` of continuity of `v` we use the open dense semialgebraic set
`A' = A \ closure Z` on which `v` is analytic (S8), so that `C^D` near points of `A'` is
automatic.  We take `A°` to be the set of `ξ₁ ∈ A'` at which the Taylor polynomial is a limit of
outputs of one of the graphs.  It is semialgebraic because
* the Taylor coefficients of `v` at `ξ₁ ∈ A'` are the unique `t` with
  `v(ξ) - ∑ t_m ξ^m = o(|ξ - ξ₁|^D)` (`isLO_iff`), a first-order formula in `(ξ₁, t)` given
  the (semialgebraic) graph of `v`;
* the coefficients of the outputs of a circuit graph are polynomials in its constants
  (`out_eq`), so being a limit of such outputs is a first-order formula in `t` (`good_iff`).
Density follows by applying Lemma 4.1 and Theorem 3.5 in an arbitrary ball of `A'`
(`exists_good_point`).
-/

noncomputable section

open MvPolynomial Set Filter Topology

namespace ClassSep

/-- The valuation `(ξ, s, ν)` of the variables `ι ⊕ Option κ`. -/
def valξsν {ι κ : Type} (ξ : ι → ℝ) (s : ℝ) (ν : κ → ℝ) : ι ⊕ Option κ → ℝ :=
  Sum.elim ξ (extendVal s ν)

/-! ## A toolkit for instances of (S1)

We verify that concrete sets are semialgebraic by exhibiting them as built from polynomial
sign conditions with `∧`, `∨`, `¬`, `→` and quantifiers over finitely many real variables. -/

section Toolkit

variable {β γ : Type}

/-- `f : ℝ^β → ℝ` is a polynomial function. -/
def IsPolyFun (f : (β → ℝ) → ℝ) : Prop := ∃ p : MvPolynomial β ℝ, ∀ x, f x = eval x p

namespace IsPolyFun

theorem const (c : ℝ) : IsPolyFun (fun _ : β → ℝ => c) := ⟨C c, fun _ => by simp⟩

theorem coord (b : β) : IsPolyFun (fun x : β → ℝ => x b) := ⟨X b, fun _ => by simp⟩

theorem add {f g : (β → ℝ) → ℝ} (hf : IsPolyFun f) (hg : IsPolyFun g) :
    IsPolyFun (fun x => f x + g x) := by
  obtain ⟨p, hp⟩ := hf; obtain ⟨q, hq⟩ := hg
  exact ⟨p + q, fun x => by simp [hp, hq]⟩

theorem sub {f g : (β → ℝ) → ℝ} (hf : IsPolyFun f) (hg : IsPolyFun g) :
    IsPolyFun (fun x => f x - g x) := by
  obtain ⟨p, hp⟩ := hf; obtain ⟨q, hq⟩ := hg
  exact ⟨p - q, fun x => by simp [hp, hq]⟩

theorem mul {f g : (β → ℝ) → ℝ} (hf : IsPolyFun f) (hg : IsPolyFun g) :
    IsPolyFun (fun x => f x * g x) := by
  obtain ⟨p, hp⟩ := hf; obtain ⟨q, hq⟩ := hg
  exact ⟨p * q, fun x => by simp [hp, hq]⟩

theorem neg {f : (β → ℝ) → ℝ} (hf : IsPolyFun f) : IsPolyFun (fun x => -f x) := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨-p, fun x => by simp [hp]⟩

theorem pow {f : (β → ℝ) → ℝ} (hf : IsPolyFun f) (n : ℕ) : IsPolyFun (fun x => f x ^ n) := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨p ^ n, fun x => by simp [hp]⟩

theorem sum {s : Finset γ} {f : γ → (β → ℝ) → ℝ} (h : ∀ c, IsPolyFun (f c)) :
    IsPolyFun (fun x => ∑ c ∈ s, f c x) := by
  choose p hp using h
  exact ⟨∑ c ∈ s, p c, fun x => by simp [hp]⟩

theorem prod {s : Finset γ} {f : γ → (β → ℝ) → ℝ} (h : ∀ c, IsPolyFun (f c)) :
    IsPolyFun (fun x => ∏ c ∈ s, f c x) := by
  choose p hp using h
  exact ⟨∏ c ∈ s, p c, fun x => by simp [hp]⟩

theorem comp {f : (γ → ℝ) → ℝ} (hf : IsPolyFun f) {G : (β → ℝ) → γ → ℝ}
    (hG : ∀ c, IsPolyFun (fun x => G x c)) : IsPolyFun (fun x => f (G x)) := by
  obtain ⟨p, hp⟩ := hf
  choose q hq using hG
  refine ⟨bind₁ q p, fun x => ?_⟩
  show f (G x) = _
  rw [eval_bind₁', hp]
  have : G x = fun c => eval x (q c) := funext fun c => hq c x
  rw [this]

theorem evalPoly (p : MvPolynomial γ ℝ) {G : (β → ℝ) → γ → ℝ}
    (hG : ∀ c, IsPolyFun (fun x => G x c)) : IsPolyFun (fun x => eval (G x) p) :=
  comp (f := fun y => eval y p) ⟨p, fun _ => rfl⟩ hG

end IsPolyFun

theorem isSA_setOf_mem {S : Set (γ → ℝ)} (hS : IsSA S) {G : (β → ℝ) → γ → ℝ}
    (hG : ∀ c, IsPolyFun (fun x => G x c)) : IsSA {x | G x ∈ S} := by
  choose q hq using hG
  have e : ∀ x, G x = fun c => eval x (q c) := fun x => funext fun c => hq c x
  simp only [e]
  exact hS.preimage_poly q

theorem isSA_lt {f g : (β → ℝ) → ℝ} (hf : IsPolyFun f) (hg : IsPolyFun g) :
    IsSA {x | f x < g x} := by
  obtain ⟨p, hp⟩ := hf; obtain ⟨q, hq⟩ := hg
  convert isSA_pos (q - p) using 1
  ext x
  simp [hp, hq, sub_pos]

theorem isSA_le {f g : (β → ℝ) → ℝ} (hf : IsPolyFun f) (hg : IsPolyFun g) :
    IsSA {x | f x ≤ g x} := by
  convert (isSA_lt hg hf).compl using 1
  ext x
  simp

theorem isSA_eq {f g : (β → ℝ) → ℝ} (hf : IsPolyFun f) (hg : IsPolyFun g) :
    IsSA {x | f x = g x} := by
  obtain ⟨p, hp⟩ := hf; obtain ⟨q, hq⟩ := hg
  convert isSA_zero (p - q) using 1
  ext x
  simp [hp, hq, sub_eq_zero]

theorem isSA_abs_lt {f g : (β → ℝ) → ℝ} (hf : IsPolyFun f) (hg : IsPolyFun g) :
    IsSA {x | |f x| < g x} := by
  convert (isSA_lt hg.neg hf).inter (isSA_lt hf hg) using 1
  ext x
  simp [abs_lt]

theorem isSA_abs_le {f g : (β → ℝ) → ℝ} (hf : IsPolyFun f) (hg : IsPolyFun g) :
    IsSA {x | |f x| ≤ g x} := by
  convert (isSA_le hg.neg hf).inter (isSA_le hf hg) using 1
  ext x
  simp [abs_le]

theorem isSA_and {P R : (β → ℝ) → Prop} (h₁ : IsSA {x | P x}) (h₂ : IsSA {x | R x}) :
    IsSA {x | P x ∧ R x} :=
  h₁.inter h₂

theorem isSA_or {P R : (β → ℝ) → Prop} (h₁ : IsSA {x | P x}) (h₂ : IsSA {x | R x}) :
    IsSA {x | P x ∨ R x} :=
  h₁.union h₂

theorem isSA_imp {P R : (β → ℝ) → Prop} (h₁ : IsSA {x | P x}) (h₂ : IsSA {x | R x}) :
    IsSA {x | P x → R x} := by
  convert h₁.compl.union h₂ using 1
  ext x
  simp [imp_iff_not_or]

theorem isSA_exists_real {P : (β → ℝ) → ℝ → Prop}
    (h : IsSA {w : Option β → ℝ | P (fun b => w (some b)) (w none)}) :
    IsSA {x | ∃ a, P x a} :=
  h.exists_option

theorem isSA_forall_real {P : (β → ℝ) → ℝ → Prop}
    (h : IsSA {w : Option β → ℝ | P (fun b => w (some b)) (w none)}) :
    IsSA {x | ∀ a, P x a} := by
  have : IsSA {w : Option β → ℝ | ¬ P (fun b => w (some b)) (w none)} := h.compl
  convert (isSA_exists_real (P := fun x a => ¬ P x a) this).compl using 1
  ext x
  simp

theorem isSA_exists_fun [Finite γ] {P : (β → ℝ) → (γ → ℝ) → Prop}
    (h : IsSA {w : β ⊕ γ → ℝ | P (fun b => w (Sum.inl b)) (fun c => w (Sum.inr c))}) :
    IsSA {x | ∃ z, P x z} :=
  h.exists_sum

theorem isSA_forall_fun [Finite γ] {P : (β → ℝ) → (γ → ℝ) → Prop}
    (h : IsSA {w : β ⊕ γ → ℝ | P (fun b => w (Sum.inl b)) (fun c => w (Sum.inr c))}) :
    IsSA {x | ∀ z, P x z} :=
  h.forall_sum

theorem isSA_forall_finset {s : Finset γ} {P : γ → (β → ℝ) → Prop}
    (h : ∀ c, IsSA {x | P c x}) : IsSA {x | ∀ c ∈ s, P c x} := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isSA_univ : IsSA (Set.univ : Set (β → ℝ)))
  | insert a s _ ih =>
    convert (h a).inter ih using 1
    ext x
    simp

theorem isSA_forall_fintype [Fintype γ] {P : γ → (β → ℝ) → Prop}
    (h : ∀ c, IsSA {x | P c x}) : IsSA {x | ∀ c, P c x} := by
  convert isSA_forall_finset (s := Finset.univ) h using 1
  ext x
  simp

theorem isSA_exists_mem_list {L : List γ} {P : γ → (β → ℝ) → Prop}
    (h : ∀ c ∈ L, IsSA {x | P c x}) : IsSA {x | ∃ c ∈ L, P c x} := by
  induction L with
  | nil => simpa using (isSA_empty : IsSA (∅ : Set (β → ℝ)))
  | cons a L ih =>
    convert (h a List.mem_cons_self).union (ih fun c hc => h c (List.mem_cons_of_mem a hc))
      using 1
    ext x
    simp

end Toolkit

/-! ## The value function is semialgebraic -/

section ValueSA

variable {ι κ : Type} [Fintype ι] [Fintype κ]

omit [Fintype ι] [Fintype κ] in
theorem isPolyFun_valξsν {β : Type} {Ξ : (β → ℝ) → ι → ℝ} {S : (β → ℝ) → ℝ}
    {N : (β → ℝ) → κ → ℝ} (hΞ : ∀ i, IsPolyFun fun w => Ξ w i) (hS : IsPolyFun S)
    (hN : ∀ k, IsPolyFun fun w => N w k) :
    ∀ c, IsPolyFun fun w => valξsν (Ξ w) (S w) (N w) c := by
  rintro (i | _ | k)
  · exact hΞ i
  · exact hS
  · exact hN k

omit [Fintype ι] in
/-- The graph of the value function over `A` is semialgebraic (S1). -/
theorem isSA_graph_value {Q : MvPolynomial (ι ⊕ Option κ) ℝ} {A : Set (ι → ℝ)} (hA : IsSA A)
    {v : (ι → ℝ) → ℝ}
    (hv : ∀ ξ ∈ A, IsGreatest {s | ∃ ν, eval (valξsν ξ s ν) Q = 0} (v ξ)) :
    IsSA {w : ι ⊕ Unit → ℝ |
      (fun i => w (Sum.inl i)) ∈ A ∧ v (fun i => w (Sum.inl i)) = w (Sum.inr ())} := by
  have key : IsSA {w : ι ⊕ Unit → ℝ | (fun i => w (Sum.inl i)) ∈ A ∧
      ((∃ ν : κ → ℝ, eval (valξsν (fun i => w (Sum.inl i)) (w (Sum.inr ())) ν) Q = 0) ∧
      ∀ s : ℝ, (∃ ν : κ → ℝ, eval (valξsν (fun i => w (Sum.inl i)) s ν) Q = 0) →
        s ≤ w (Sum.inr ()))} := by
    refine isSA_and (isSA_setOf_mem hA fun i => IsPolyFun.coord _) (isSA_and ?_ ?_)
    · refine isSA_exists_fun ?_
      exact isSA_eq (IsPolyFun.evalPoly Q (isPolyFun_valξsν (fun i => IsPolyFun.coord _)
        (IsPolyFun.coord _) fun k => IsPolyFun.coord _)) (IsPolyFun.const 0)
    · refine isSA_forall_real (isSA_imp ?_ (isSA_le (IsPolyFun.coord _) (IsPolyFun.coord _)))
      refine isSA_exists_fun ?_
      exact isSA_eq (IsPolyFun.evalPoly Q (isPolyFun_valξsν (fun i => IsPolyFun.coord _)
        (IsPolyFun.coord _) fun k => IsPolyFun.coord _)) (IsPolyFun.const 0)
  convert key using 1
  ext w
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hw, h⟩
    rw [← h]
    exact ⟨hw, (hv _ hw).1, fun s hs => (hv _ hw).2 hs⟩
  · rintro ⟨hw, h1, h2⟩
    exact ⟨hw, (hv _ hw).unique ⟨h1, fun s hs => h2 s hs⟩⟩

omit [Fintype ι] in
/-- Membership in the graph of `v`, at polynomial points. -/
theorem isSA_graph_mem {A : Set (ι → ℝ)} {v : (ι → ℝ) → ℝ}
    (hG : IsSA {w : ι ⊕ Unit → ℝ |
      (fun i => w (Sum.inl i)) ∈ A ∧ v (fun i => w (Sum.inl i)) = w (Sum.inr ())})
    {β : Type} {Ξ : (β → ℝ) → ι → ℝ} {S : (β → ℝ) → ℝ}
    (hΞ : ∀ i, IsPolyFun fun w => Ξ w i) (hS : IsPolyFun S) :
    IsSA {x | Ξ x ∈ A ∧ v (Ξ x) = S x} :=
  isSA_setOf_mem hG (G := fun x => Sum.elim (Ξ x) (fun _ => S x)) (by
    rintro (i | _)
    · exact hΞ i
    · exact hS)

end ValueSA

/-! ## Polynomials of degree `≤ D` with given coefficients -/

section Coeffs

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The degree of a monomial. -/
abbrev mdeg (m : ι →₀ ℕ) : ℕ := m.sum fun _ e => e

omit [DecidableEq ι] in
theorem mdeg_eq (m : ι →₀ ℕ) : mdeg m = ∑ i, m i :=
  Finsupp.sum_fintype _ _ fun _ => rfl

/-- The monomials of degree `≤ D`. -/
def Sfin (ι : Type) [Fintype ι] [DecidableEq ι] (D : ℕ) : Finset (ι →₀ ℕ) :=
  ((Fintype.piFinset fun _ : ι => Finset.range (D + 1)).image
    (Finsupp.equivFunOnFinite.symm)).filter (fun m => mdeg m ≤ D)

theorem mem_Sfin {D : ℕ} {m : ι →₀ ℕ} : m ∈ Sfin ι D ↔ mdeg m ≤ D := by
  unfold Sfin
  rw [Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨Finset.mem_image.2 ⟨⇑m, ?_, ?_⟩, h⟩⟩
  · rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range, Nat.lt_succ_iff]
    refine le_trans ?_ h
    rw [mdeg_eq]
    exact Finset.single_le_sum (fun j _ => Nat.zero_le (m j)) (Finset.mem_univ i)
  · exact Finsupp.equivFunOnFinite.symm_apply_apply m

/-- The polynomial `∑_{|m| ≤ D} t_m X^m`. -/
def Pt {D : ℕ} (t : Sfin ι D → ℝ) : MvPolynomial ι ℝ :=
  ∑ f : Sfin ι D, monomial f.1 (t f)

theorem coeff_Pt {D : ℕ} (t : Sfin ι D → ℝ) (m : ι →₀ ℕ) :
    (Pt t).coeff m = if h : m ∈ Sfin ι D then t ⟨m, h⟩ else 0 := by
  unfold Pt
  rw [coeff_sum]
  simp only [coeff_monomial]
  split_ifs with h
  · rw [Fintype.sum_eq_single ⟨m, h⟩]
    · simp
    · intro f hf
      exact ite_eq_right fun e => hf (Subtype.ext e)
  · exact Finset.sum_eq_zero fun f _ => ite_eq_right fun (e : f.1 = m) => h (e ▸ f.2)

theorem totalDegree_Pt {D : ℕ} (t : Sfin ι D → ℝ) : (Pt t).totalDegree ≤ D := by
  unfold Pt
  refine totalDegree_finsetSum_le fun f _ => ?_
  exact le_trans (totalDegree_monomial_le _ _) (mem_Sfin.1 f.2)

theorem eval_Pt {D : ℕ} (t : Sfin ι D → ℝ) (ξ : ι → ℝ) :
    eval ξ (Pt t) = ∑ f : Sfin ι D, t f * ∏ i, ξ i ^ (f.1 i) := by
  unfold Pt
  simp only [map_sum, eval_monomial]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finsupp.prod_fintype _ _ fun i => pow_zero _]

theorem Pt_coeff {D : ℕ} {p : MvPolynomial ι ℝ} (hp : p.totalDegree ≤ D) :
    Pt (fun f : Sfin ι D => p.coeff f.1) = p := by
  ext m
  rw [coeff_Pt]
  split_ifs with h
  · rfl
  · refine (coeff_eq_zero_of_totalDegree_lt ?_).symm
    rw [mem_Sfin, not_le] at h
    exact lt_of_le_of_lt hp h

theorem isPolyFun_eval_Pt {D : ℕ} {β : Type} {Ξ : (β → ℝ) → ι → ℝ}
    {T : (β → ℝ) → Sfin ι D → ℝ} (hΞ : ∀ i, IsPolyFun fun w => Ξ w i)
    (hT : ∀ f, IsPolyFun fun w => T w f) : IsPolyFun fun w => eval (Ξ w) (Pt (T w)) := by
  simp only [eval_Pt]
  exact IsPolyFun.sum fun f => (hT f).mul (IsPolyFun.prod fun i => (hΞ i).pow _)

end Coeffs

/-! ## The graph of the Taylor coefficients -/

section TaylorGraph

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A first-order formula saying that `v - Pt t = o(|ξ - ξ₁|^D)` at `ξ₁`, i.e. (for `v` of class
`C^D` near `ξ₁`) that `t` are the Taylor coefficients of `v` at `ξ₁`. -/
def IsLO (A : Set (ι → ℝ)) (v : (ι → ℝ) → ℝ) (D : ℕ) (ξ₁ : ι → ℝ) (t : Sfin ι D → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ ξ : ι → ℝ, (∀ i, |ξ i - ξ₁ i| < δ) →
    ∀ r : ℝ, 0 ≤ r → (∀ i, |ξ i - ξ₁ i| ≤ r) → ∀ s : ℝ, (ξ ∈ A ∧ v ξ = s) →
      |s - eval ξ (Pt t)| ≤ ε * r ^ D

theorem isLO_iff {A : Set (ι → ℝ)} (hA : IsOpen A) {v : (ι → ℝ) → ℝ} {D : ℕ} {ξ₁ : ι → ℝ}
    (hξ₁ : ξ₁ ∈ A) (hcd : ContDiffAt ℝ D v ξ₁) (t : Sfin ι D → ℝ) :
    IsLO A v D ξ₁ t ↔ t = fun f => (taylorPoly D v ξ₁).coeff f.1 := by
  constructor
  · intro h
    have hlo : (fun ξ => v ξ - eval ξ (Pt t)) =o[𝓝 ξ₁] fun ξ => ‖ξ - ξ₁‖ ^ D := by
      rw [Asymptotics.isLittleO_iff]
      intro c hc
      obtain ⟨δ, hδ, hδ'⟩ := h c hc
      obtain ⟨δ', hδ'pos, hball⟩ := Metric.isOpen_iff.1 hA ξ₁ hξ₁
      rw [Metric.eventually_nhds_iff]
      refine ⟨min δ δ', lt_min hδ hδ'pos, fun ξ hξ => ?_⟩
      have hξA : ξ ∈ A := hball (lt_of_lt_of_le hξ (min_le_right _ _))
      have hcoord : ∀ i, |ξ i - ξ₁ i| ≤ ‖ξ - ξ₁‖ := fun i => by
        have := norm_le_pi_norm (ξ - ξ₁) i
        simpa [Real.norm_eq_abs] using this
      have hlt : ∀ i, |ξ i - ξ₁ i| < δ := fun i => by
        have := dist_le_pi_dist ξ ξ₁ i
        rw [Real.dist_eq] at this
        exact lt_of_le_of_lt this (lt_of_lt_of_le hξ (min_le_left _ _))
      have := hδ' ξ hlt ‖ξ - ξ₁‖ (norm_nonneg _) hcoord (v ξ) ⟨hξA, rfl⟩
      rw [Real.norm_eq_abs, norm_pow, norm_norm]
      exact this
    have hT := taylorPoly_eq_of_isLittleO hcd (totalDegree_Pt t) hlo
    funext f
    rw [hT, coeff_Pt, dite_eq_left f.2]
  · rintro rfl
    intro ε hε
    have hlo := taylorPoly_isLittleO hcd
    rw [Asymptotics.isLittleO_iff] at hlo
    obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 (hlo hε)
    refine ⟨δ, hδ, fun ξ hξ r hr hrξ s ⟨_, hs⟩ => ?_⟩
    have hd : dist ξ ξ₁ < δ := (dist_pi_lt_iff hδ).2 fun i => by
      rw [Real.dist_eq]; exact hξ i
    have h1 := hδ' hd
    have hnorm : ‖ξ - ξ₁‖ ≤ r := (pi_norm_le_iff_of_nonneg hr).2 fun i => by
      rw [Pi.sub_apply, Real.norm_eq_abs]; exact hrξ i
    rw [Pt_coeff (totalDegree_taylorPoly_le D v ξ₁), ← hs]
    rw [Real.norm_eq_abs, norm_pow, norm_norm] at h1
    refine h1.trans ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm D) hε.le

/-- The graph of the Taylor coefficients over `A'` is semialgebraic. -/
theorem isSA_taylorGraph {A A' : Set (ι → ℝ)} (hA' : IsSA A') {v : (ι → ℝ) → ℝ}
    (hG : IsSA {w : ι ⊕ Unit → ℝ |
      (fun i => w (Sum.inl i)) ∈ A ∧ v (fun i => w (Sum.inl i)) = w (Sum.inr ())}) (D : ℕ) :
    IsSA {w : ι ⊕ Sfin ι D → ℝ | (fun i => w (Sum.inl i)) ∈ A' ∧
      IsLO A v D (fun i => w (Sum.inl i)) (fun f => w (Sum.inr f))} := by
  refine isSA_and (isSA_setOf_mem hA' fun i => IsPolyFun.coord _) ?_
  unfold IsLO
  refine isSA_forall_real (isSA_imp (isSA_lt (IsPolyFun.const 0) (IsPolyFun.coord _)) ?_)
  refine isSA_exists_real (isSA_and (isSA_lt (IsPolyFun.const 0) (IsPolyFun.coord _)) ?_)
  refine isSA_forall_fun (isSA_imp (isSA_forall_fintype fun i => isSA_abs_lt
    (IsPolyFun.sub (IsPolyFun.coord _) (IsPolyFun.coord _)) (IsPolyFun.coord _)) ?_)
  refine isSA_forall_real (isSA_imp (isSA_le (IsPolyFun.const 0) (IsPolyFun.coord _)) ?_)
  refine isSA_imp (isSA_forall_fintype fun i => isSA_abs_le
    (IsPolyFun.sub (IsPolyFun.coord _) (IsPolyFun.coord _)) (IsPolyFun.coord _)) ?_
  refine isSA_forall_real (isSA_imp
    (isSA_graph_mem hG (fun i => IsPolyFun.coord _) (IsPolyFun.coord _)) ?_)
  exact isSA_abs_le (IsPolyFun.sub (IsPolyFun.coord _)
    (isPolyFun_eval_Pt (fun i => IsPolyFun.coord _) (fun f => IsPolyFun.coord _)))
    ((IsPolyFun.coord _).mul ((IsPolyFun.coord _).pow _))

end TaylorGraph

/-! ## Outputs of a circuit graph as polynomials in its constants -/

section Circuits

variable {σ : Type}

theorem Shape.values_append_single {A : Type} [CommRing A] (Γ : Shape σ) (g : Gate σ)
    (c : ℕ → A) : Shape.values (Γ ++ [g]) c = Γ.values c ++ [g.eval c (Γ.values c)] := by
  simp [Shape.values, List.foldl_append]

/-- Circuits commute with ring homomorphisms applied to the constants. -/
theorem Shape.values_map_val {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (Γ : Shape σ)
    (c : ℕ → A) : Γ.values (fun k => f (c k)) = (Γ.values c).map (MvPolynomial.map f) := by
  induction Γ using List.reverseRecOn with
  | nil => rfl
  | append_singleton Γ g ih =>
    rw [Shape.values_append_single, Shape.values_append_single, ih, List.map_append]
    congr 1
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
    have hgetD : ∀ j, ((Shape.values Γ c).map (MvPolynomial.map f)).getD j 0 =
        MvPolynomial.map f ((Shape.values Γ c).getD j 0) := by
      intro j
      simpa using List.getD_map (Shape.values Γ c) 0 (n := j) (MvPolynomial.map f)
    cases g with
    | var i => simp [Gate.eval]
    | const k => simp [Gate.eval]
    | add j k => simp only [Gate.eval, hgetD, map_add]
    | mul j k => simp only [Gate.eval, hgetD, map_mul]

/-- A bound for the constant slots used by a gate. -/
def Gate.slotBound : Gate σ → ℕ
  | .const k => k + 1
  | _ => 0

/-- A bound for the constant slots used by a circuit graph. -/
def Shape.slotBound (Γ : Shape σ) : ℕ := (Γ.map Gate.slotBound).sum

/-- A circuit only depends on the constants in its slots. -/
theorem Shape.values_congr {A : Type} [CommRing A] (Γ : Shape σ) {a b : ℕ → A}
    (h : ∀ k < Γ.slotBound, a k = b k) : Γ.values a = Γ.values b := by
  unfold Shape.values
  apply List.foldl_ext
  intro vals g hg
  cases g with
  | const k =>
    have : k + 1 ≤ Γ.slotBound := List.le_sum_of_mem (List.mem_map.2 ⟨_, hg, rfl⟩)
    simp [Gate.eval, h k (by omega)]
  | var i => rfl
  | add j k => rfl
  | mul j k => rfl

/-- The generic constants: slot `k < M` holds the variable `k`. -/
def cgen (M : ℕ) : ℕ → MvPolynomial (Fin M) ℝ := fun k => if h : k < M then X ⟨k, h⟩ else 0

/-- Extension of constants by zero. -/
def extA {M : ℕ} (a' : Fin M → ℝ) : ℕ → ℝ := fun k => if h : k < M then a' ⟨k, h⟩ else 0

/-- The generic output of a circuit graph with output gate. -/
def Pgen (Γo : Shape σ × ℕ) : MvPolynomial σ (MvPolynomial (Fin Γo.1.slotBound) ℝ) :=
  (Γo.1.values (cgen Γo.1.slotBound)).getD Γo.2 0

/-- The output of a circuit graph is a specialization of its generic output. -/
theorem out_eq (Γo : Shape σ × ℕ) (a : ℕ → ℝ) :
    (Γo.1.values a).getD Γo.2 0 =
      MvPolynomial.map (eval (fun i : Fin Γo.1.slotBound => a i)) (Pgen Γo) := by
  have h1 : Γo.1.values a = Γo.1.values
      (fun k => (eval (fun i : Fin Γo.1.slotBound => a i)) (cgen Γo.1.slotBound k)) := by
    apply Shape.values_congr
    intro k hk
    simp [cgen, hk]
  rw [h1, Shape.values_map_val]
  simpa [Pgen] using List.getD_map (Γo.1.values (cgen Γo.1.slotBound)) 0 (n := Γo.2)
    (MvPolynomial.map (eval (fun i : Fin Γo.1.slotBound => a i)))

theorem out_extA (Γo : Shape σ × ℕ) (a' : Fin Γo.1.slotBound → ℝ) :
    (Γo.1.values (extA a')).getD Γo.2 0 = MvPolynomial.map (eval a') (Pgen Γo) := by
  rw [out_eq]
  congr 3
  funext i
  simp [extA, i.2]

variable [Fintype σ] [DecidableEq σ]

/-- The monomials of the generic output of degree `> D`. -/
def hiSupp (Γo : Shape σ × ℕ) (D : ℕ) : Finset (σ →₀ ℕ) :=
  (Pgen Γo).support.filter (fun m => D < mdeg m)

omit [Fintype σ] [DecidableEq σ] in
theorem totalDegree_map_le_iff (Γo : Shape σ × ℕ) (D : ℕ)
    (φ : MvPolynomial (Fin Γo.1.slotBound) ℝ →+* ℝ) :
    (MvPolynomial.map φ (Pgen Γo)).totalDegree ≤ D ↔
      ∑ m ∈ hiSupp Γo D, (φ ((Pgen Γo).coeff m)) ^ 2 = 0 := by
  rw [Finset.sum_eq_zero_iff_of_nonneg fun m _ => sq_nonneg _]
  simp only [pow_eq_zero_iff two_ne_zero, hiSupp, Finset.mem_filter]
  constructor
  · rintro h m ⟨-, hm⟩
    by_contra hne
    have hmem : m ∈ (MvPolynomial.map φ (Pgen Γo)).support := by
      rw [mem_support_iff, coeff_map]; exact hne
    have : mdeg m ≤ _ := le_totalDegree hmem
    omega
  · intro h
    rw [totalDegree, Finset.sup_le_iff]
    intro m hm
    rw [mem_support_iff, coeff_map] at hm
    by_contra hlt
    rw [not_le] at hlt
    have hm' : m ∈ (Pgen Γo).support := by
      rw [mem_support_iff]
      intro h0
      rw [h0, map_zero] at hm
      exact hm rfl
    exact hm (h m ⟨hm', hlt⟩)

/-- A first-order formula saying that the coefficient vector `t` is a limit of outputs of
degree `≤ D` of the circuit graph `Γo`. -/
def ClosOK (Γo : Shape σ × ℕ) (D : ℕ) (t : Sfin σ D → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ a' : Fin Γo.1.slotBound → ℝ,
    ∑ m ∈ hiSupp Γo D, (eval a' ((Pgen Γo).coeff m)) ^ 2 = 0 ∧
    ∀ f : Sfin σ D, |eval a' ((Pgen Γo).coeff f.1) - t f| < η

/-- The polynomial `P` is a coefficientwise limit of outputs of degree `≤ D` of `Γo`. -/
def Good (Γo : Shape σ × ℕ) (D : ℕ) (P : MvPolynomial σ ℝ) : Prop :=
  ∀ η > 0, ∃ a : ℕ → ℝ, ((Γo.1.values a).getD Γo.2 0).totalDegree ≤ D ∧
    ∀ m, |((Γo.1.values a).getD Γo.2 0).coeff m - P.coeff m| < η

theorem good_iff (Γo : Shape σ × ℕ) {D : ℕ} {P : MvPolynomial σ ℝ} (hP : P.totalDegree ≤ D) :
    Good Γo D P ↔ ClosOK Γo D (fun f => P.coeff f.1) := by
  constructor
  · intro h η hη
    obtain ⟨a, hdeg, hco⟩ := h η hη
    refine ⟨fun i => a i, ?_, fun f => ?_⟩
    · rw [out_eq] at hdeg
      exact (totalDegree_map_le_iff Γo D _).1 hdeg
    · have := hco f.1
      rw [out_eq, coeff_map] at this
      exact this
  · intro h η hη
    obtain ⟨a', hsum, hco⟩ := h η hη
    have hdeg := (totalDegree_map_le_iff Γo D (eval a')).2 hsum
    refine ⟨extA a', ?_, fun m => ?_⟩
    · rw [out_extA]; exact hdeg
    · rw [out_extA]
      by_cases hm : m ∈ Sfin σ D
      · have := hco ⟨m, hm⟩
        rw [coeff_map]
        exact this
      · rw [mem_Sfin, not_le] at hm
        rw [coeff_eq_zero_of_totalDegree_lt (lt_of_le_of_lt hdeg hm),
          coeff_eq_zero_of_totalDegree_lt (lt_of_le_of_lt hP hm), sub_zero, abs_zero]
        exact hη

theorem isSA_closOK (Γo : Shape σ × ℕ) (D : ℕ) : IsSA {t : Sfin σ D → ℝ | ClosOK Γo D t} := by
  unfold ClosOK
  refine isSA_forall_real (isSA_imp (isSA_lt (IsPolyFun.const 0) (IsPolyFun.coord _)) ?_)
  refine isSA_exists_fun (isSA_and ?_ ?_)
  · exact isSA_eq (IsPolyFun.sum fun m => (IsPolyFun.evalPoly _ fun i => IsPolyFun.coord _).pow _)
      (IsPolyFun.const 0)
  · exact isSA_forall_fintype fun f => isSA_abs_lt
      (IsPolyFun.sub (IsPolyFun.evalPoly _ fun i => IsPolyFun.coord _) (IsPolyFun.coord _))
      (IsPolyFun.coord _)

end Circuits

/-! ## Fixing coordinates of `ν` in a program graph -/

section Subst

variable {ι κ : Type} [Fintype κ] [DecidableEq κ]

/-- Substitution of constant slots for the fixed coordinates `I` of `ν`: the coordinate `k ∈ I`
becomes the slot `e k` (`e : κ ≃ Fin |κ|`), and the old slot `j` becomes `j + |κ|`. -/
def substOp (I : Finset κ) : Operand (ι ⊕ Option κ) ℕ → Operand (ι ⊕ Option {k // k ∉ I}) ℕ
  | .input (.inl i) => .input (.inl i)
  | .input (.inr none) => .input (.inr none)
  | .input (.inr (some k)) =>
      if h : k ∈ I then .const (Fintype.equivFin κ k) else .input (.inr (some ⟨k, h⟩))
  | .const j => .const (j + Fintype.card κ)
  | .prev j => .prev j

/-- The program graph of `Q̃(ξ, s, u) = Q(ξ, s, (a, u))`. -/
def substProg (I : Finset κ) (prog : SLP (ι ⊕ Option κ) ℕ) :
    SLP (ι ⊕ Option {k // k ∉ I}) ℕ :=
  prog.map fun ins => ⟨ins.op, substOp I ins.a, substOp I ins.b⟩

/-- The constants of `Q̃`: the values `a = z₀` of the fixed coordinates, then those of `Q`. -/
def substConst (cQ : ℕ → ℝ) (z₀ : κ → ℝ) : ℕ → ℝ := fun n =>
  if h : n < Fintype.card κ then z₀ ((Fintype.equivFin κ).symm ⟨n, h⟩)
  else cQ (n - Fintype.card κ)

/-- The substitution `Q ↦ Q̃` on polynomials. -/
def substVar (I : Finset κ) (z₀ : κ → ℝ) :
    ι ⊕ Option κ → MvPolynomial (ι ⊕ Option {k // k ∉ I}) ℝ
  | .inl i => X (.inl i)
  | .inr none => X (.inr none)
  | .inr (some k) => if h : k ∈ I then C (z₀ k) else X (.inr (some ⟨k, h⟩))

theorem length_substProg (I : Finset κ) (prog : SLP (ι ⊕ Option κ) ℕ) :
    (substProg I prog).length = prog.length :=
  List.length_map _

theorem eval_substOp (I : Finset κ) (cQ : ℕ → ℝ) (z₀ : κ → ℝ)
    (vals : List (MvPolynomial (ι ⊕ Option κ) ℝ)) (x : Operand (ι ⊕ Option κ) ℕ) :
    ((substOp I x).instantiate (substConst cQ z₀)).eval (vals.map (bind₁ (substVar I z₀))) =
      bind₁ (substVar I z₀) ((x.instantiate cQ).eval vals) := by
  rcases x with ((i | _ | k) | j | j)
  · simp [substOp, Operand.instantiate, Operand.eval, substVar]
  · simp [substOp, Operand.instantiate, Operand.eval, substVar]
  · by_cases h : k ∈ I
    · simp [substOp, h, Operand.instantiate, Operand.eval, substVar, substConst]
    · simp [substOp, h, Operand.instantiate, Operand.eval, substVar]
  · simp [substOp, Operand.instantiate, Operand.eval, substConst]
  · simp only [substOp, Operand.instantiate, Operand.eval]
    simpa using List.getD_map vals 0 (n := j) (bind₁ (substVar I z₀))

theorem values_substProg (I : Finset κ) (cQ : ℕ → ℝ) (z₀ : κ → ℝ)
    (prog : SLP (ι ⊕ Option κ) ℕ) :
    ((substProg I prog).instantiate (substConst cQ z₀)).values =
      (prog.instantiate cQ).values.map (bind₁ (substVar I z₀)) := by
  induction prog using List.reverseRecOn with
  | nil => rfl
  | append_singleton P ins ih =>
    simp only [substProg, SLP.instantiate, List.map_append, List.map_cons,
      List.map_nil] at ih ⊢
    rw [BaurStrassen.values_append_single, BaurStrassen.values_append_single, ih,
      List.map_append]
    congr 1
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
    simp only [Instr.eval]
    rw [eval_substOp, eval_substOp]
    cases ins.op <;> simp [ArithOp.apply]

theorem progOutput_subst (I : Finset κ) (prog : SLP (ι ⊕ Option κ) ℕ) (cQ : ℕ → ℝ)
    (z₀ : κ → ℝ) (oQ : Operand (ι ⊕ Option κ) ℕ) :
    progOutput (substProg I prog) (substConst cQ z₀) (substOp I oQ) =
      bind₁ (substVar I z₀) (progOutput prog cQ oQ) := by
  unfold progOutput
  rw [values_substProg, eval_substOp]

omit [Fintype κ] in
theorem eval_substVar (I : Finset κ) (z₀ : κ → ℝ) (ξ : ι → ℝ)
    (w : Option {k // k ∉ I} → ℝ) :
    (fun b => eval (Sum.elim ξ w) (substVar I z₀ b)) =
      valξsν ξ (w none) (fun k => if h : k ∈ I then z₀ k else w (some ⟨k, h⟩)) := by
  funext b
  rcases b with i | _ | k
  · simp [substVar, valξsν]
  · simp [substVar, valξsν, extendVal]
  · by_cases h : k ∈ I <;> simp [substVar, valξsν, extendVal, h]

end Subst

/-! ## Applying the local theorem on a ball -/

section Main

/-- The conclusion of Theorem 3.5 for a fixed program graph and circuit graph. -/
def LocalConcl {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (prog : SLP (ι ⊕ κ) ℕ) (oQ : Operand (ι ⊕ κ) ℕ) (D : ℕ) (Γ : Shape ι) (out : κ → ℕ) :
    Prop :=
  ∀ (cQ : ℕ → ℝ) (ξ₀ : ι → ℝ) (ρ : ℝ) (w₀ : κ → ℝ) (r₀ : ℝ) (lam : κ → ℝ)
    (φ : (ι → ℝ) → (κ → ℝ)),
    LocalHyp (progOutput prog cQ oQ) ξ₀ ρ w₀ r₀ lam φ →
    ∃ (ξs : ι → ℝ) (rs : ℝ) (Es : Set (ι → ℝ)),
      0 < rs ∧ Metric.ball ξs rs ⊆ Metric.closedBall ξ₀ ρ ∧ Es ⊆ Metric.ball ξs rs ∧
      IsSA Es ∧ DimLT Es (Fintype.card ι) ∧
      ContDiffOn ℝ D φ (Metric.ball ξs rs) ∧
      ∀ ξ₁ ∈ Metric.ball ξs rs \ Es, ∀ η > 0, ∃ a : ℕ → ℝ, ∀ k : κ,
        ((Γ.values a).getD (out k) 0).totalDegree ≤ D ∧
        ∀ m, |((Γ.values a).getD (out k) 0).coeff m -
          (taylorPoly D (fun ξ => φ ξ k) ξ₁).coeff m| < η

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The core of the proof of Proposition 4.5: in every ball `U₁` in which `v` is continuous
there is a point at which the Taylor polynomial of `v` is a limit of outputs of one of the
graphs. -/
theorem exists_good_point (hS : SAFacts) (prog : SLP (ι ⊕ Option κ) ℕ)
    (oQ : Operand (ι ⊕ Option κ) ℕ) (D : ℕ) (Γ : Finset κ → Shape ι)
    (out : (I : Finset κ) → Option {k // k ∉ I} → ℕ)
    (hloc : ∀ I, LocalConcl (substProg I prog) (substOp I oQ) D (Γ I) (out I))
    (cQ : ℕ → ℝ) {A A' : Set (ι → ℝ)} {v : (ι → ℝ) → ℝ} (hA'A : A' ⊆ A)
    (hG : IsSA {w : ι ⊕ Unit → ℝ |
      (fun i => w (Sum.inl i)) ∈ A ∧ v (fun i => w (Sum.inl i)) = w (Sum.inr ())})
    (hcont : ContinuousOn v A')
    (hQnn : ∀ p, 0 ≤ eval p (progOutput prog cQ oQ))
    (hmax : ∀ ξ ∈ A, IsGreatest {s | ∃ ν, eval (valξsν ξ s ν) (progOutput prog cQ oQ) = 0}
      (v ξ))
    {xc : ι → ℝ} {rc : ℝ} (hrc : 0 < rc) (hball : Metric.ball xc rc ⊆ A') :
    ∃ ξ₁ ∈ Metric.ball xc rc, ∃ I : Finset κ, Good (Γ I, out I none) D (taylorPoly D v ξ₁) := by
  set Q := progOutput prog cQ oQ with hQ
  -- the set `F = {(ξ, ν) : ξ ∈ U₁, Q(ξ, v ξ, ν) = 0}`
  set F : Set (ι ⊕ κ → ℝ) := {w | (fun i => w (Sum.inl i)) ∈ Metric.ball xc rc ∧
    eval (valξsν (fun i => w (Sum.inl i)) (v (fun i => w (Sum.inl i)))
      (fun k => w (Sum.inr k))) Q = 0} with hF_def
  have hFsa : IsSA F := by
    have key : IsSA {w : ι ⊕ κ → ℝ | (fun i => w (Sum.inl i)) ∈ Metric.ball xc rc ∧
        ∃ s, ((fun i => w (Sum.inl i)) ∈ A ∧ v (fun i => w (Sum.inl i)) = s) ∧
          eval (valξsν (fun i => w (Sum.inl i)) s (fun k => w (Sum.inr k))) Q = 0} := by
      refine isSA_and (isSA_setOf_mem (isSA_ball xc rc) fun i => IsPolyFun.coord _) ?_
      refine isSA_exists_real (isSA_and
        (isSA_graph_mem hG (fun i => IsPolyFun.coord _) (IsPolyFun.coord _)) ?_)
      exact isSA_eq (IsPolyFun.evalPoly Q (isPolyFun_valξsν (fun i => IsPolyFun.coord _)
        (IsPolyFun.coord _) fun k => IsPolyFun.coord _)) (IsPolyFun.const 0)
    convert key using 1
    ext w
    simp only [F, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, _, ⟨hA'A (hball h1), rfl⟩, h2⟩
    · rintro ⟨h1, s, ⟨_, rfl⟩, h2⟩
      exact ⟨h1, h2⟩
  have hFsub : ∀ w ∈ F, w ∘ Sum.inl ∈ Metric.ball xc rc := fun w hw => hw.1
  have hproj : ∀ x ∈ Metric.ball xc rc, ∃ z, Sum.elim x z ∈ F := by
    intro x hx
    obtain ⟨ν, hν⟩ := (hmax x (hA'A (hball hx))).1
    exact ⟨ν, hx, hν⟩
  -- Lemma 4.1
  obtain ⟨x₀, z₀, N, I, r₃, ζ, -, hN, hN0, hr₃, hsub3, hζ0, hζan, hiff⟩ :=
    isolate hS xc rc hrc F hFsa hFsub hproj
  -- the reduced problem in `w = (s, u)`
  set νf : (Option {k // k ∉ I} → ℝ) → κ → ℝ :=
    fun w k => if h : k ∈ I then z₀ k else w (some ⟨k, h⟩) with hνf
  set φ : (ι → ℝ) → Option {k // k ∉ I} → ℝ := fun ξ o => o.elim (v ξ) (fun k => ζ ξ k.1)
    with hφ
  set Q' := progOutput (substProg I prog) (substConst cQ z₀) (substOp I oQ) with hQ'
  have hevalQ' : ∀ ξ w, evalξw ξ w Q' = eval (valξsν ξ (w none) (νf w)) Q := by
    intro ξ w
    rw [show evalξw ξ w Q' = eval (Sum.elim ξ w) Q' from rfl, hQ', progOutput_subst,
      eval_bind₁', eval_substVar]
  have hball3 : Metric.ball x₀ r₃ ⊆ A' := hsub3.trans hball
  have hφcont : ContinuousOn φ (Metric.ball x₀ r₃) := by
    rw [continuousOn_pi]
    rintro (_ | k)
    · exact hcont.mono hball3
    · exact (continuous_apply k.1).comp_continuousOn hζan.continuousOn
  have hφat : ContinuousAt φ x₀ :=
    hφcont.continuousAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr₃))
  obtain ⟨ε₁, hε₁, hNball⟩ := Metric.isOpen_iff.1 hN _ hN0
  set r₀ := ε₁ / 2 with hr₀
  have hr₀pos : 0 < r₀ := by positivity
  obtain ⟨δ, hδ, hδφ⟩ := Metric.continuousAt_iff.1 hφat (r₀ / 2) (by positivity)
  set ρ := min (min (δ / 2) (r₃ / 2)) (ε₁ / 2) with hρ_def
  have hρ : 0 < ρ := by positivity
  have hρδ : ρ < δ := by
    have := min_le_left (min (δ / 2) (r₃ / 2)) (ε₁ / 2)
    have := min_le_left (δ / 2) (r₃ / 2)
    linarith
  have hρr₃ : ρ < r₃ := by
    have := min_le_left (min (δ / 2) (r₃ / 2)) (ε₁ / 2)
    have := min_le_right (δ / 2) (r₃ / 2)
    linarith
  have hρε₁ : ρ < ε₁ := by
    have := min_le_right (min (δ / 2) (r₃ / 2)) (ε₁ / 2)
    linarith
  have hKsub : Metric.closedBall x₀ ρ ⊆ Metric.ball x₀ r₃ := Metric.closedBall_subset_ball hρr₃
  set w₀ := φ x₀ with hw₀_def
  have hw0 : ∀ k (h : k ∉ I), w₀ (some ⟨k, h⟩) = z₀ k := by
    intro k h
    simp [hw₀_def, hφ, hζ0]
  have hNmem : ∀ ξ ∈ Metric.closedBall x₀ ρ, ∀ w ∈ Metric.closedBall w₀ r₀,
      Sum.elim ξ (νf w) ∈ N := by
    intro ξ hξ w hw
    apply hNball
    rw [Metric.mem_ball, dist_pi_lt_iff hε₁]
    rintro (i | k)
    · exact lt_of_le_of_lt (dist_le_pi_dist ξ x₀ i)
        (lt_of_le_of_lt (Metric.mem_closedBall.1 hξ) hρε₁)
    · simp only [Sum.elim_inr, hνf]
      split_ifs with h
      · simpa [hζ0] using hε₁
      · rw [← hw0 k h]
        refine lt_of_le_of_lt (dist_le_pi_dist w w₀ _)
          (lt_of_le_of_lt (Metric.mem_closedBall.1 hw) ?_)
        rw [hr₀]
        linarith
  have hyp : LocalHyp Q' x₀ ρ w₀ r₀ (Pi.single none 1) φ := by
    refine ⟨hρ, hr₀pos, ?_, hφcont.mono hKsub, ?_, ?_, ?_⟩
    · intro ξ _ w _
      rw [hevalQ']
      exact hQnn _
    · intro ξ hξ
      exact (hδφ (lt_of_le_of_lt (Metric.mem_closedBall.1 hξ) hρδ)).le
    · intro ξ hξ
      have hξ3 := hKsub hξ
      have h := (hiff ξ hξ3 (ζ ξ)).2 rfl
      rw [hevalQ']
      have hν : νf (φ ξ) = ζ ξ := by
        funext k
        simp only [hνf, hφ]
        split_ifs with hk
        · exact (h.2 k hk).symm
        · rfl
      rw [hν]
      exact h.1.1.2
    · intro ξ hξ w hw hzero hne
      rw [single_dotProduct, single_dotProduct, one_mul, one_mul]
      have hξ3 := hKsub hξ
      have hξA : ξ ∈ A := hA'A (hball (hsub3 hξ3))
      rw [hevalQ'] at hzero
      have hle : w none ≤ v ξ := (hmax ξ hξA).2 ⟨νf w, hzero⟩
      refine lt_of_le_of_ne hle fun heq' => hne ?_
      have heq : w none = v ξ := heq'
      have hmem : Sum.elim ξ (νf w) ∈ F ∩ N ∧ ∀ i ∈ I, νf w i = z₀ i := by
        refine ⟨⟨⟨hsub3 hξ3, ?_⟩, hNmem ξ hξ w hw⟩, fun i hi => by simp [hνf, hi]⟩
        show eval (valξsν ξ (v ξ) (νf w)) Q = 0
        rw [← heq]
        exact hzero
      have hνeq := (hiff ξ hξ3 (νf w)).1 hmem
      funext o
      rcases o with _ | ⟨k, hk⟩
      · exact heq
      · have := congrFun hνeq k
        simp only [hνf, hk, dite_false] at this
        exact this
  -- Theorem 3.5
  obtain ⟨ξs, rs, Es, hrs, hsubs, -, -, hEdim, -, hprop⟩ :=
    hloc I (substConst cQ z₀) x₀ ρ w₀ r₀ (Pi.single none 1) φ hyp
  have hnsub : ¬ Metric.ball ξs rs ⊆ Es := by
    intro hsub
    have hint : ξs ∈ interior Es :=
      (Metric.isOpen_ball.subset_interior_iff.2 hsub) (Metric.mem_ball_self hrs)
    rw [(dimLT_card_iff Es).1 hEdim] at hint
    exact hint
  obtain ⟨ξ₁, hξ₁b, hξ₁E⟩ := Set.not_subset.1 hnsub
  refine ⟨ξ₁, hsub3 (hKsub (hsubs hξ₁b)), I, fun η hη => ?_⟩
  obtain ⟨a, ha⟩ := hprop ξ₁ ⟨hξ₁b, hξ₁E⟩ η hη
  exact ⟨a, (ha none).1, (ha none).2⟩

end Main

/-- **Proposition 4.5 (value functions).** -/
theorem value_functions (hS : SAFacts) :
    ∃ C : ℕ, ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
      (prog : SLP (ι ⊕ Option κ) ℕ) (oQ : Operand (ι ⊕ Option κ) ℕ) (D : ℕ), 1 ≤ D →
      ∃ graphs : List (Shape ι × ℕ),
        (∀ Γo ∈ graphs, Γo.1.length ≤ C * ((D + 1) ^ 3 * (prog.length + 1) +
          (D + 1) ^ 2 * (Fintype.card κ + 1) ^ 2 + Fintype.card ι)) ∧
        ∀ (cQ : ℕ → ℝ) (A : Set (ι → ℝ)) (v : (ι → ℝ) → ℝ),
          IsOpen A → A.Nonempty → IsSA A →
          (∀ p, 0 ≤ eval p (progOutput prog cQ oQ)) →
          (∀ ξ ∈ A, IsGreatest {s | ∃ ν, eval (valξsν ξ s ν) (progOutput prog cQ oQ) = 0}
            (v ξ)) →
          ∃ A₀ ⊆ A, IsSA A₀ ∧ A ⊆ closure A₀ ∧
            ∀ ξ₁ ∈ A₀, ContDiffAt ℝ D v ξ₁ ∧ ∃ Γo ∈ graphs, ∀ η > 0, ∃ a : ℕ → ℝ,
              ((Γo.1.values a).getD Γo.2 0).totalDegree ≤ D ∧
              ∀ m, |((Γo.1.values a).getD Γo.2 0).coeff m - (taylorPoly D v ξ₁).coeff m| < η := by
  obtain ⟨CL, hCL⟩ := local_theorem hS
  refine ⟨CL, fun {ι κ} _ _ _ _ prog oQ D hD => ?_⟩
  -- one circuit graph for each set `I` of fixed coordinates
  have key : ∀ I : Finset κ, ∃ (Γ : Shape ι) (out : Option {k // k ∉ I} → ℕ),
      Γ.length ≤ CL * ((D + 1) ^ 3 * ((substProg I prog).length + 1) +
        (D + 1) ^ 2 * Fintype.card (Option {k // k ∉ I}) ^ 2 + Fintype.card ι) ∧
      LocalConcl (substProg I prog) (substOp I oQ) D Γ out :=
    fun I => hCL (substProg I prog) (substOp I oQ) D hD
  choose Γ out hlen hloc using key
  refine ⟨(Finset.univ : Finset (Finset κ)).toList.map (fun I => (Γ I, out I none)), ?_, ?_⟩
  · intro Γo hΓo
    obtain ⟨I, -, rfl⟩ := List.mem_map.1 hΓo
    refine (hlen I).trans (Nat.mul_le_mul_left _ ?_)
    rw [length_substProg, Fintype.card_option]
    have : Fintype.card {k // k ∉ I} ≤ Fintype.card κ := Fintype.card_subtype_le _
    gcongr
  intro cQ A v hAo _ hAsa hQnn hmax
  have hG := isSA_graph_value hAsa hmax
  have hvSA : IsSAFunOn₁ A v := by
    refine ⟨hAsa, ?_⟩
    convert hG using 1
    ext w
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, congrFun h2 ()⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, funext fun u => h2⟩
  -- `v` is analytic on an open dense semialgebraic `A' ⊆ A` (S8)
  obtain ⟨Z, hZsa, -, hZdim, hZan⟩ := hS.nash A v hAo hvSA
  set A' := A \ closure Z with hA'_def
  have hA'A : A' ⊆ A := sdiff_subset
  have hA'o : IsOpen A' := hAo.sdiff isClosed_closure
  have hA'sa : IsSA A' := hAsa.diff hZsa.closure
  have hdense : A ⊆ closure A' :=
    (dense_compl_of_dimLT hS hZsa hZdim).open_subset_closure_inter hAo
  have han : ∀ ξ ∈ A', AnalyticAt ℝ v ξ :=
    fun ξ hξ => hZan ξ ⟨hξ.1, fun h => hξ.2 (subset_closure h)⟩
  have hcont : ContinuousOn v A' := fun ξ hξ => (han ξ hξ).continuousAt.continuousWithinAt
  set graphs := (Finset.univ : Finset (Finset κ)).toList.map (fun I => (Γ I, out I none))
    with hgraphs
  refine ⟨{ξ₁ | ξ₁ ∈ A' ∧ ∃ Γo ∈ graphs, Good Γo D (taylorPoly D v ξ₁)},
    fun ξ hξ => hA'A hξ.1, ?_, ?_, ?_⟩
  · -- semialgebraicity
    have e : {ξ₁ | ξ₁ ∈ A' ∧ ∃ Γo ∈ graphs, Good Γo D (taylorPoly D v ξ₁)} =
        {ξ₁ | ∃ Γo ∈ graphs, ∃ t : Sfin ι D → ℝ,
          (ξ₁ ∈ A' ∧ IsLO A v D ξ₁ t) ∧ ClosOK Γo D t} := by
      ext ξ₁
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hξ₁, Γo, hΓo, hgood⟩
        refine ⟨Γo, hΓo, _, ⟨hξ₁, (isLO_iff hAo (hA'A hξ₁) (han ξ₁ hξ₁).contDiffAt _).2 rfl⟩,
          (good_iff Γo (totalDegree_taylorPoly_le D v ξ₁)).1 hgood⟩
      · rintro ⟨Γo, hΓo, t, ⟨hξ₁, hlo⟩, hclos⟩
        obtain rfl := (isLO_iff hAo (hA'A hξ₁) (han ξ₁ hξ₁).contDiffAt _).1 hlo
        exact ⟨hξ₁, Γo, hΓo, (good_iff Γo (totalDegree_taylorPoly_le D v ξ₁)).2 hclos⟩
    rw [e]
    exact isSA_exists_mem_list fun Γo _ => isSA_exists_fun (isSA_and
      (isSA_taylorGraph hA'sa hG D) (isSA_setOf_mem (isSA_closOK Γo D) fun f => IsPolyFun.coord _))
  · -- density
    refine hdense.trans (closure_minimal (fun y hy => ?_) isClosed_closure)
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨r, hr, hrA'⟩ := Metric.isOpen_iff.1 hA'o y hy
    have hball : Metric.ball y (min r ε) ⊆ A' :=
      (Metric.ball_subset_ball (min_le_left _ _)).trans hrA'
    obtain ⟨ξ₁, hξ₁, I, hgood⟩ := exists_good_point hS prog oQ D Γ out hloc cQ hA'A hG hcont
      hQnn hmax (lt_min hr hε) hball
    refine ⟨ξ₁, ⟨hball hξ₁, _, List.mem_map.2 ⟨I, Finset.mem_toList.2 (Finset.mem_univ I), rfl⟩,
      hgood⟩, ?_⟩
    rw [dist_comm]
    exact lt_of_lt_of_le (Metric.mem_ball.1 hξ₁) (min_le_right _ _)
  · -- the property at every point
    rintro ξ₁ ⟨hξ₁, h⟩
    exact ⟨(han ξ₁ hξ₁).contDiffAt, h⟩

end ClassSep
