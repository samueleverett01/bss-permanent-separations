import ClassSeparations.Basic.Cells
import ClassSeparations.Core.BaurStrassen
import ClassSeparations.SA.Formula

/-!
# The margin of a certificate (§5.3, Lemma 5.2 (a))

We work with a cell `B` whose variables are *parameters* `ξ ∈ ℝ^π` and *certificate
coordinates* `z ∈ ℝ^ζ` (`π`, `ζ` arbitrary finite types).  In §5 the parameters are `(x, y)`;
in §6 they are `(x, w)`.

1. **Homogenization** (`homogenization`).  Substituting `z = ũ/u₀` in a straight-line program
   with `L` operations and keeping numerators gives a program with at most `4L` operations over
   the variables `π ⊕ Option ζ` (`u₀ = inr none`, `ũᵢ = inr (some i)`) that computes, for every
   polynomial `p` computed by the original program, a polynomial `p♯` with
   `p♯(ξ, u₀, ũ) = u₀^a · p(ξ, ũ/u₀)` whenever `u₀ ≠ 0`.
2. **The margin system** (6) and the sum of squares `Q = marginPoly p♯ q♯` of its equations, in
   the variables `π ⊕ Option (MVar ζ m)`: the coordinate `none` is the unknown `s`, and
   `ν = (u₀, ũ, σ₀, σ₁, …, σ_m) : MVar ζ m → ℝ` with `MVar ζ m = Option ζ ⊕ Option (Fin m)`
   (`u₀ = inl none`, `ũᵢ = inl (some i)`, `σ₀ = inr none`, `σⱼ = inr (some j)`).  `Q ≥ 0`, its
   zero set is the set of solutions of (6) (`marginPoly_eq_zero_iff`), and it has a straight-line
   program with at most `4L + 2|ζ| + 2r + 5m + 11` operations (`exists_margin`,
   `exists_margin_graph`).
3. **Lemma 5.2 (a)** (`margin_cert_iff`, alias `lemma_5_2_a`): `ξ` has a certificate in the cell
   iff (6) has a solution
   with `s > 0`; and the boundedness facts used in Lemma 5.2 (b), (c): every solution has
   `s ≤ 1` (`margin_s_le_one`), the solutions with `s ≥ s₀ ≥ 0` over a compact set of parameters
   form a compact set (`margin_isCompact`), and `s` attains its maximum on the solutions at every
   `ξ` that has a certificate (`margin_attains`).

We also provide the substitution of input coordinates in programs and cells
(`SLP.substIn`, `Cell.substIn`), used to fix the irrelevant certificate coordinates to `0`.
-/

noncomputable section

open MvPolynomial Set Filter Topology

namespace ClassSep

namespace Margin

/-! ### Generic facts about programs -/

section Generic

variable {V : Type}

/-- The operand only refers to the first `n` values. -/
def OValid (n : ℕ) : Operand V ℝ → Prop
  | .prev j => j < n
  | _ => True

@[simp] theorem eval_input (vals : List (MvPolynomial V ℝ)) (i : V) :
    (Operand.input i : Operand V ℝ).eval vals = X i := rfl

@[simp] theorem eval_const (vals : List (MvPolynomial V ℝ)) (c : ℝ) :
    (Operand.const c : Operand V ℝ).eval vals = C c := rfl

theorem OValid.mono {n n' : ℕ} {o : Operand V ℝ} (h : OValid n o) (hn : n ≤ n') : OValid n' o := by
  cases o with
  | prev j => exact lt_of_lt_of_le h hn
  | _ => trivial

theorem values_append_exists (P : SLP V ℝ) :
    ∀ R : SLP V ℝ, ∃ r, (P ++ R).values = P.values ++ r := by
  intro R
  induction R using List.reverseRecOn with
  | nil => exact ⟨[], by simp⟩
  | append_singleton R ins ih =>
    obtain ⟨r, hr⟩ := ih
    refine ⟨r ++ [ins.eval (P ++ R).values], ?_⟩
    rw [← List.append_assoc, BaurStrassen.values_append_single, hr, List.append_assoc]

theorem eval_append_of_valid {P : SLP V ℝ} {o : Operand V ℝ} (ho : OValid P.length o)
    (R : SLP V ℝ) : o.eval (P ++ R).values = o.eval P.values := by
  obtain ⟨r, hr⟩ := values_append_exists P R
  rw [hr]
  cases o with
  | prev j =>
    simp only [Operand.eval]
    exact List.getD_append _ _ _ _ (by rw [BaurStrassen.length_values]; exact ho)
  | _ => rfl

theorem eval_last (P : SLP V ℝ) (ins : Instr V ℝ) :
    (Operand.prev P.length : Operand V ℝ).eval (P ++ [ins]).values = ins.eval P.values := by
  rw [BaurStrassen.values_append_single]
  simp only [Operand.eval]
  rw [List.getD_append_right _ _ _ _ (by rw [BaurStrassen.length_values]),
    BaurStrassen.length_values]
  simp

/-! ### Expressions and their compilation into programs -/

/-- Expressions over operands, compiled into straight-line programs. -/
inductive SExpr (V : Type) where
  | leaf (o : Operand V ℝ)
  | bin (op : ArithOp) (e₁ e₂ : SExpr V)
  | sq (e : SExpr V)

namespace SExpr

/-- Number of operations. -/
def nodes : SExpr V → ℕ
  | leaf _ => 0
  | bin _ e₁ e₂ => e₁.nodes + e₂.nodes + 1
  | sq e => e.nodes + 1

/-- All leaves refer to the first `n` values. -/
def Valid (n : ℕ) : SExpr V → Prop
  | leaf o => OValid n o
  | bin _ e₁ e₂ => e₁.Valid n ∧ e₂.Valid n
  | sq e => e.Valid n

theorem Valid.mono {n n' : ℕ} (hn : n ≤ n') : ∀ {e : SExpr V}, e.Valid n → e.Valid n'
  | leaf _, h => OValid.mono h hn
  | bin _ _ _, h => ⟨Valid.mono hn h.1, Valid.mono hn h.2⟩
  | sq e, h => @Valid.mono n n' hn e h

/-- The polynomial denoted by an expression, given the values of the program. -/
def den (vals : List (MvPolynomial V ℝ)) : SExpr V → MvPolynomial V ℝ
  | leaf o => o.eval vals
  | bin op e₁ e₂ => op.apply (e₁.den vals) (e₂.den vals)
  | sq e => e.den vals ^ 2

/-- Compile an expression into instructions appended after `n` earlier instructions; returns
the instructions and the output operand. -/
def compile : SExpr V → ℕ → SLP V ℝ × Operand V ℝ
  | leaf o, _ => ([], o)
  | bin op e₁ e₂, n =>
    let c₁ := e₁.compile n
    let c₂ := e₂.compile (n + c₁.1.length)
    (c₁.1 ++ c₂.1 ++ [⟨op, c₁.2, c₂.2⟩], .prev (n + c₁.1.length + c₂.1.length))
  | sq e, n =>
    let c := e.compile n
    (c.1 ++ [⟨.mul, c.2, c.2⟩], .prev (n + c.1.length))

theorem den_append {P : SLP V ℝ} (R : SLP V ℝ) :
    ∀ {e : SExpr V}, e.Valid P.length → e.den (P ++ R).values = e.den P.values
  | leaf _, h => eval_append_of_valid h R
  | bin op _ _, h => by
    simp only [den]; rw [den_append R h.1, den_append R h.2]
  | sq e, h => by
    simp only [den]; rw [@den_append P R e h]

theorem compile_spec : ∀ (e : SExpr V) (P : SLP V ℝ), e.Valid P.length →
    (e.compile P.length).1.length = e.nodes ∧
    OValid (P ++ (e.compile P.length).1).length (e.compile P.length).2 ∧
    (e.compile P.length).2.eval (P ++ (e.compile P.length).1).values = e.den P.values
  | leaf o, P, h => by
    refine ⟨rfl, ?_, ?_⟩
    · simpa [compile, Valid] using h
    · simp [compile, den]
  | bin op e₁ e₂, P, h => by
    obtain ⟨h₁l, h₁v, h₁e⟩ := compile_spec e₁ P h.1
    set c₁ := e₁.compile P.length with hc₁
    set P₁ := P ++ c₁.1 with hP₁
    have hlen₁ : P₁.length = P.length + c₁.1.length := List.length_append
    have hv₂ : e₂.Valid P₁.length := Valid.mono (by omega) h.2
    obtain ⟨h₂l, h₂v, h₂e⟩ := compile_spec e₂ P₁ hv₂
    rw [hlen₁] at h₂l h₂v h₂e
    set c₂ := e₂.compile (P.length + c₁.1.length) with hc₂
    have hprog : P ++ ((e₁.bin op e₂).compile P.length).1 =
        (P₁ ++ c₂.1) ++ [⟨op, c₁.2, c₂.2⟩] := by
      simp only [compile, hP₁, List.append_assoc]
      rfl
    have hout : ((e₁.bin op e₂).compile P.length).2 = .prev (P₁ ++ c₂.1).length := by
      simp only [compile, List.length_append, hP₁]
      rw [← hc₁, ← hc₂]
    refine ⟨?_, ?_, ?_⟩
    · simp only [compile, List.length_append, List.length_singleton, nodes]
      rw [← hc₁, ← hc₂, h₁l, h₂l]
    · rw [hprog, hout]
      simp [OValid]
    · rw [hprog, hout, eval_last]
      simp only [Instr.eval, den]
      have hv₁ : OValid P₁.length c₁.2 := h₁v
      rw [eval_append_of_valid hv₁, h₁e, h₂e, den_append c₁.1 h.2]
  | sq e, P, h => by
    obtain ⟨hl, hv, he⟩ := compile_spec e P h
    set c := e.compile P.length with hc
    have hprog : P ++ (e.sq.compile P.length).1 = (P ++ c.1) ++ [⟨.mul, c.2, c.2⟩] := by
      simp only [compile, List.append_assoc]
      rfl
    have hout : (e.sq.compile P.length).2 = .prev (P ++ c.1).length := by
      simp only [compile, List.length_append]
      rw [← hc]
    refine ⟨?_, ?_, ?_⟩
    · simp only [compile, List.length_append, List.length_singleton, nodes]
      rw [← hc, hl]
    · rw [hprog, hout]
      simp [OValid]
    · rw [hprog, hout, eval_last]
      simp only [Instr.eval, den, ArithOp.apply]
      rw [he, pow_two]

/-- Sum of a list of expressions. -/
def sumE (l : List (SExpr V)) : SExpr V :=
  l.foldr (fun e acc => .bin .add e acc) (.leaf (.const 0))

theorem den_sumE (vals : List (MvPolynomial V ℝ)) (l : List (SExpr V)) :
    (sumE l).den vals = (l.map (den vals)).sum := by
  induction l with
  | nil => simp [sumE, den, Operand.eval]
  | cons e l ih =>
    simp only [sumE, List.foldr_cons, den, ArithOp.apply, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]

theorem nodes_sumE (l : List (SExpr V)) :
    (sumE l).nodes = (l.map nodes).sum + l.length := by
  induction l with
  | nil => simp [sumE, nodes]
  | cons e l ih =>
    simp only [sumE, List.foldr_cons, nodes, List.map_cons, List.sum_cons,
      List.length_cons] at ih ⊢
    rw [ih]; ring

theorem valid_sumE {n : ℕ} (l : List (SExpr V)) (h : ∀ e ∈ l, e.Valid n) :
    (sumE l).Valid n := by
  induction l with
  | nil => simp [sumE, Valid, OValid]
  | cons e l ih =>
    simp only [sumE, List.foldr_cons, Valid] at ih ⊢
    exact ⟨h e (by simp), ih fun e' he' => h e' (by simp [he'])⟩

end SExpr

/-- Append the compiled expression to a program. -/
theorem exists_append_expr (P : SLP V ℝ) (e : SExpr V) (he : e.Valid P.length) :
    ∃ (P' : SLP V ℝ) (o : Operand V ℝ), P'.length = P.length + e.nodes ∧
      o.eval P'.values = e.den P.values := by
  obtain ⟨hl, -, he'⟩ := SExpr.compile_spec e P he
  exact ⟨P ++ (e.compile P.length).1, _, by rw [List.length_append, hl], he'⟩

end Generic

/-! ### Substituting input coordinates -/

section Subst

variable {ι ι' : Type}

/-- Replace input coordinates by operands (input coordinates or constants). -/
def Operand.substIn (ρ : ι → Operand ι' ℝ) : Operand ι ℝ → Operand ι' ℝ
  | .input i => ρ i
  | .const c => .const c
  | .prev j => .prev j

/-- Replace the input coordinates of a program by operands (input coordinates or constants). -/
def SLP.substIn (ρ : ι → Operand ι' ℝ) (P : SLP ι ℝ) : SLP ι' ℝ :=
  P.map fun ins => ⟨ins.op, Operand.substIn ρ ins.a, Operand.substIn ρ ins.b⟩

/-- The polynomial of a substituted coordinate. -/
def ρpoly (ρ : ι → Operand ι' ℝ) (i : ι) : MvPolynomial ι' ℝ := (ρ i).eval []

/-- The substitution only uses input coordinates and constants. -/
def NoPrev (ρ : ι → Operand ι' ℝ) : Prop := ∀ i j, ρ i ≠ .prev j

theorem eval_bind₁_ (v : ι' → ℝ) (g : ι → MvPolynomial ι' ℝ) (p : MvPolynomial ι ℝ) :
    eval v (bind₁ g p) = eval (fun i => eval v (g i)) p :=
  eval₂Hom_bind₁ _ _ _ _

theorem eval_substIn {ρ : ι → Operand ι' ℝ} (hρ : NoPrev ρ) (vals : List (MvPolynomial ι ℝ)) :
    ∀ o : Operand ι ℝ, (Operand.substIn ρ o).eval (vals.map (bind₁ (ρpoly ρ))) =
      bind₁ (ρpoly ρ) (o.eval vals)
  | .input i => by
    simp only [Operand.substIn, Operand.eval, bind₁_X_right, ρpoly]
    cases h : ρ i with
    | input k => rfl
    | const c => rfl
    | prev j => exact absurd h (hρ i j)
  | .const c => by simp [Operand.substIn, Operand.eval]
  | .prev j => by
    simp only [Operand.substIn, Operand.eval]
    rw [show (0 : MvPolynomial ι' ℝ) = bind₁ (ρpoly ρ) 0 from (map_zero _).symm, List.getD_map]

theorem ArithOp.apply_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (op : ArithOp)
    (a b : R) : φ (op.apply a b) = op.apply (φ a) (φ b) := by
  cases op <;> simp [ArithOp.apply]

theorem SLP.values_substIn {ρ : ι → Operand ι' ℝ} (hρ : NoPrev ρ) (P : SLP ι ℝ) :
    (SLP.substIn ρ P).values = P.values.map (bind₁ (ρpoly ρ)) := by
  induction P using List.reverseRecOn with
  | nil => rfl
  | append_singleton P ins ih =>
    simp only [SLP.substIn, List.map_append, List.map_cons, List.map_nil] at ih ⊢
    rw [BaurStrassen.values_append_single, BaurStrassen.values_append_single, ih,
      List.map_append, List.map_cons, List.map_nil]
    congr 2
    simp only [Instr.eval]
    rw [eval_substIn hρ, eval_substIn hρ]
    exact (ArithOp.apply_map (bind₁ (ρpoly ρ)).toRingHom ins.op _ _).symm

theorem SLP.length_substIn (ρ : ι → Operand ι' ℝ) (P : SLP ι ℝ) :
    (SLP.substIn ρ P).length = P.length := by simp [SLP.substIn]

theorem SLP.computes_substIn {ρ : ι → Operand ι' ℝ} (hρ : NoPrev ρ) {P : SLP ι ℝ}
    {p : MvPolynomial ι ℝ} (h : P.Computes p) :
    (SLP.substIn ρ P).Computes (bind₁ (ρpoly ρ) p) := by
  obtain ⟨o, rfl⟩ := h
  exact ⟨Operand.substIn ρ o, by rw [SLP.values_substIn hρ, eval_substIn hρ]⟩

/-- Substitution of input coordinates in a cell. -/
def Cell.substIn (ρ : ι → Operand ι' ℝ) (B : Cell ι) : Cell ι' :=
  ⟨SLP.substIn ρ B.prog, B.eqs.map (bind₁ (ρpoly ρ)), B.poss.map (bind₁ (ρpoly ρ))⟩

theorem Cell.mem_carrier_substIn (ρ : ι → Operand ι' ℝ) (B : Cell ι) (w : ι' → ℝ) :
    w ∈ (Cell.substIn ρ B).carrier ↔ (fun i => eval w (ρpoly ρ i)) ∈ B.carrier := by
  simp only [Cell.carrier, Cell.substIn, Set.mem_ofPred_eq, List.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, eval_bind₁_]

theorem Cell.computes_substIn {ρ : ι → Operand ι' ℝ} (hρ : NoPrev ρ) (B : Cell ι)
    (h : ∀ p ∈ B.eqs ++ B.poss, B.prog.Computes p) :
    ∀ p ∈ (Cell.substIn ρ B).eqs ++ (Cell.substIn ρ B).poss,
      (Cell.substIn ρ B).prog.Computes p := by
  intro p hp
  simp only [Cell.substIn, List.mem_append, List.mem_map] at hp
  rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
  · exact SLP.computes_substIn hρ (h q (List.mem_append_left _ hq))
  · exact SLP.computes_substIn hρ (h q (List.mem_append_right _ hq))

theorem OValid.substIn {ρ : ι → Operand ι' ℝ} (hρ : NoPrev ρ) {n : ℕ} :
    ∀ {o : Operand ι ℝ}, OValid n o → OValid n (Operand.substIn ρ o)
  | .input i, _ => by
    simp only [Operand.substIn]
    cases h : ρ i with
    | prev j => exact absurd h (hρ i j)
    | _ => trivial
  | .const _, _ => trivial
  | .prev _, h => h

theorem bind₁_X_comp (f : ι → ι') (p : MvPolynomial ι ℝ) :
    bind₁ (fun i => (X (f i) : MvPolynomial ι' ℝ)) p = rename f p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

end Subst

/-! ### Homogenization -/

section Homog

variable {π ζ : Type}

/-- The point `(ξ, ũ/u₀)` for a point `(ξ, u₀, ũ)` of `ℝ^(π ⊕ Option ζ)` (`u₀ = inr none`). -/
def dehom (w : π ⊕ Option ζ → ℝ) : π ⊕ ζ → ℝ :=
  Sum.elim (fun p => w (.inl p)) (fun i => w (.inr (some i)) / w (.inr none))

/-- The pair `(P, R)` represents `p`: `R = u₀^a` and `P = u₀^a · p(ξ, ũ/u₀)` where `u₀ ≠ 0`. -/
def Rep (P R : MvPolynomial (π ⊕ Option ζ) ℝ) (p : MvPolynomial (π ⊕ ζ) ℝ) : Prop :=
  ∃ a : ℕ, R = X (.inr none) ^ a ∧ ∀ w : π ⊕ Option ζ → ℝ, w (.inr none) ≠ 0 →
    eval w P = w (.inr none) ^ a * eval (dehom w) p

theorem Rep.add {P₁ R₁ P₂ R₂ : MvPolynomial (π ⊕ Option ζ) ℝ} {p₁ p₂ : MvPolynomial (π ⊕ ζ) ℝ}
    (h₁ : Rep P₁ R₁ p₁) (h₂ : Rep P₂ R₂ p₂) :
    Rep (P₁ * R₂ + P₂ * R₁) (R₁ * R₂) (p₁ + p₂) := by
  obtain ⟨a₁, rfl, e₁⟩ := h₁
  obtain ⟨a₂, rfl, e₂⟩ := h₂
  refine ⟨a₁ + a₂, by rw [pow_add], fun w hw => ?_⟩
  simp only [map_add, map_mul, map_pow, eval_X, e₁ w hw, e₂ w hw]
  ring

theorem Rep.sub {P₁ R₁ P₂ R₂ : MvPolynomial (π ⊕ Option ζ) ℝ} {p₁ p₂ : MvPolynomial (π ⊕ ζ) ℝ}
    (h₁ : Rep P₁ R₁ p₁) (h₂ : Rep P₂ R₂ p₂) :
    Rep (P₁ * R₂ - P₂ * R₁) (R₁ * R₂) (p₁ - p₂) := by
  obtain ⟨a₁, rfl, e₁⟩ := h₁
  obtain ⟨a₂, rfl, e₂⟩ := h₂
  refine ⟨a₁ + a₂, by rw [pow_add], fun w hw => ?_⟩
  simp only [map_sub, map_mul, map_pow, eval_X, e₁ w hw, e₂ w hw]
  ring

theorem Rep.mul {P₁ R₁ P₂ R₂ : MvPolynomial (π ⊕ Option ζ) ℝ} {p₁ p₂ : MvPolynomial (π ⊕ ζ) ℝ}
    (h₁ : Rep P₁ R₁ p₁) (h₂ : Rep P₂ R₂ p₂) :
    Rep (P₁ * P₂) (R₁ * R₂) (p₁ * p₂) := by
  obtain ⟨a₁, rfl, e₁⟩ := h₁
  obtain ⟨a₂, rfl, e₂⟩ := h₂
  refine ⟨a₁ + a₂, by rw [pow_add], fun w hw => ?_⟩
  simp only [map_mul, e₁ w hw, e₂ w hw]
  ring

/-- A pair of operands (numerator, power of `u₀`). -/
abbrev HPair (π ζ : Type) := Operand (π ⊕ Option ζ) ℝ × Operand (π ⊕ Option ζ) ℝ

/-- The pair representing `0`. -/
def hDefault : HPair π ζ := (.const 0, .const 1)

/-- The pair of an operand of the original program, given the pairs of its instructions. -/
def hOp (prs : List (HPair π ζ)) : Operand (π ⊕ ζ) ℝ → HPair π ζ
  | .input (.inl p) => (.input (.inl p), .const 1)
  | .input (.inr i) => (.input (.inr (some i)), .input (.inr none))
  | .const c => (.const c, .const 1)
  | .prev j => prs.getD j hDefault

/-- The expressions for the pair of `x ∘ y`: `(P₁R₂ ± P₂R₁, R₁R₂)` and `(P₁P₂, R₁R₂)`. -/
def hExpr (op : ArithOp) (x y : HPair π ζ) : SExpr (π ⊕ Option ζ) × SExpr (π ⊕ Option ζ) :=
  match op with
  | .add => (.bin .add (.bin .mul (.leaf x.1) (.leaf y.2)) (.bin .mul (.leaf y.1) (.leaf x.2)),
      .bin .mul (.leaf x.2) (.leaf y.2))
  | .sub => (.bin .sub (.bin .mul (.leaf x.1) (.leaf y.2)) (.bin .mul (.leaf y.1) (.leaf x.2)),
      .bin .mul (.leaf x.2) (.leaf y.2))
  | .mul => (.bin .mul (.leaf x.1) (.leaf y.1), .bin .mul (.leaf x.2) (.leaf y.2))

/-- One step of the homogenization. -/
def hStep (st : SLP (π ⊕ Option ζ) ℝ × List (HPair π ζ)) (ins : Instr (π ⊕ ζ) ℝ) :
    SLP (π ⊕ Option ζ) ℝ × List (HPair π ζ) :=
  let e := hExpr ins.op (hOp st.2 ins.a) (hOp st.2 ins.b)
  let c₁ := e.1.compile st.1.length
  let c₂ := e.2.compile (st.1 ++ c₁.1).length
  (st.1 ++ c₁.1 ++ c₂.1, st.2 ++ [(c₁.2, c₂.2)])

/-- The homogenized program and the pairs of the instructions of the original program. -/
def homog (P : SLP (π ⊕ ζ) ℝ) : SLP (π ⊕ Option ζ) ℝ × List (HPair π ζ) :=
  P.foldl hStep ([], [])

/-- The pair is valid for the program `Q` and represents `p`. -/
def PairOK (Q : SLP (π ⊕ Option ζ) ℝ) (pr : HPair π ζ) (p : MvPolynomial (π ⊕ ζ) ℝ) : Prop :=
  OValid Q.length pr.1 ∧ OValid Q.length pr.2 ∧ Rep (pr.1.eval Q.values) (pr.2.eval Q.values) p

theorem PairOK.append {Q : SLP (π ⊕ Option ζ) ℝ} {pr : HPair π ζ} {p : MvPolynomial (π ⊕ ζ) ℝ}
    (h : PairOK Q pr p) (R : SLP (π ⊕ Option ζ) ℝ) : PairOK (Q ++ R) pr p := by
  refine ⟨h.1.mono (by simp), h.2.1.mono (by simp), ?_⟩
  rw [eval_append_of_valid h.1, eval_append_of_valid h.2.1]
  exact h.2.2

theorem pairOK_default (Q : SLP (π ⊕ Option ζ) ℝ) : PairOK Q hDefault 0 :=
  ⟨trivial, trivial, ⟨0, by simp [hDefault, Operand.eval], fun w _ => by
    simp [hDefault, Operand.eval]⟩⟩

/-- The invariant of the homogenization. -/
def HInv (P : SLP (π ⊕ ζ) ℝ) (st : SLP (π ⊕ Option ζ) ℝ × List (HPair π ζ)) : Prop :=
  st.2.length = P.length ∧ st.1.length ≤ 4 * P.length ∧
    ∀ j, PairOK st.1 (st.2.getD j hDefault) (P.values.getD j 0)

theorem hOp_ok {P : SLP (π ⊕ ζ) ℝ} {st : SLP (π ⊕ Option ζ) ℝ × List (HPair π ζ)}
    (h : HInv P st) : ∀ o, PairOK st.1 (hOp st.2 o) (o.eval P.values)
  | .input (.inl p) => ⟨trivial, trivial, ⟨0, by simp [hOp, Operand.eval], fun w _ => by
      simp [hOp, Operand.eval, dehom]⟩⟩
  | .input (.inr i) => ⟨trivial, trivial, ⟨1, by simp [hOp, Operand.eval], fun w hw => by
      simp only [hOp, Operand.eval, eval_X, dehom, Sum.elim_inr, pow_one]
      field_simp⟩⟩
  | .const c => ⟨trivial, trivial, ⟨0, by simp [hOp, Operand.eval], fun w _ => by
      simp [hOp, Operand.eval]⟩⟩
  | .prev j => h.2.2 j

theorem hExpr_spec (op : ArithOp) {Q : SLP (π ⊕ Option ζ) ℝ} {x y : HPair π ζ}
    {a b : MvPolynomial (π ⊕ ζ) ℝ} (hx : PairOK Q x a) (hy : PairOK Q y b) :
    (hExpr op x y).1.Valid Q.length ∧ (hExpr op x y).2.Valid Q.length ∧
    (hExpr op x y).1.nodes + (hExpr op x y).2.nodes ≤ 4 ∧
    Rep ((hExpr op x y).1.den Q.values) ((hExpr op x y).2.den Q.values) (op.apply a b) := by
  obtain ⟨hx1, hx2, hxr⟩ := hx
  obtain ⟨hy1, hy2, hyr⟩ := hy
  cases op
  · exact ⟨⟨⟨hx1, hy2⟩, ⟨hy1, hx2⟩⟩, ⟨hx2, hy2⟩, by simp [hExpr, SExpr.nodes],
      by simpa [hExpr, SExpr.den, ArithOp.apply] using hxr.add hyr⟩
  · exact ⟨⟨⟨hx1, hy2⟩, ⟨hy1, hx2⟩⟩, ⟨hx2, hy2⟩, by simp [hExpr, SExpr.nodes],
      by simpa [hExpr, SExpr.den, ArithOp.apply] using hxr.sub hyr⟩
  · exact ⟨⟨hx1, hy1⟩, ⟨hx2, hy2⟩, by simp [hExpr, SExpr.nodes],
      by simpa [hExpr, SExpr.den, ArithOp.apply] using hxr.mul hyr⟩

theorem hStep_inv {P : SLP (π ⊕ ζ) ℝ} {st : SLP (π ⊕ Option ζ) ℝ × List (HPair π ζ)}
    (h : HInv P st) (ins : Instr (π ⊕ ζ) ℝ) : HInv (P ++ [ins]) (hStep st ins) := by
  have hx := hOp_ok h ins.a
  have hy := hOp_ok h ins.b
  obtain ⟨hlen, hsz, hok⟩ := h
  obtain ⟨hv₁, hv₂, hnodes, hrep⟩ := hExpr_spec ins.op hx hy
  set e := hExpr ins.op (hOp st.2 ins.a) (hOp st.2 ins.b) with he
  obtain ⟨hl₁, hov₁, hev₁⟩ := SExpr.compile_spec e.1 st.1 hv₁
  set c₁ := e.1.compile st.1.length with hc₁
  have hv₂' : e.2.Valid (st.1 ++ c₁.1).length := hv₂.mono (by simp)
  obtain ⟨hl₂, hov₂, hev₂⟩ := SExpr.compile_spec e.2 (st.1 ++ c₁.1) hv₂'
  set c₂ := e.2.compile (st.1 ++ c₁.1).length with hc₂
  have hst : hStep st ins = (st.1 ++ c₁.1 ++ c₂.1, st.2 ++ [(c₁.2, c₂.2)]) := rfl
  rw [hst]
  have hPv : (P ++ [ins]).values = P.values ++ [ins.eval P.values] :=
    BaurStrassen.values_append_single P ins
  have hPl : P.values.length = P.length := BaurStrassen.length_values P
  refine ⟨by simp [hlen], ?_, fun j => ?_⟩
  · simp only [List.length_append, List.length_singleton]
    omega
  · rw [hPv]
    rcases lt_trichotomy j P.length with hj | rfl | hj
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      exact ((hok j).append c₁.1).append c₂.1
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
      simp only [hlen, hPl, Nat.sub_self, List.getD_cons_zero]
      refine ⟨hov₁.mono (by simp), hov₂, ?_⟩
      rw [eval_append_of_valid hov₁, hev₁, hev₂, SExpr.den_append c₁.1 hv₂]
      exact hrep
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      exact pairOK_default _

theorem homog_inv (P : SLP (π ⊕ ζ) ℝ) : HInv P (homog P) := by
  induction P using List.reverseRecOn with
  | nil =>
    refine ⟨rfl, by simp [homog], fun j => ?_⟩
    have h0 := pairOK_default (π := π) (ζ := ζ) []
    simpa [homog, SLP.values] using h0
  | append_singleton P ins ih =>
    have : homog (P ++ [ins]) = hStep (homog P) ins := by simp [homog, List.foldl_append]
    rw [this]
    exact hStep_inv ih ins

/-- **Homogenization** (§5.3).  Substituting `z = ũ/u₀` in a program with `L` operations and
keeping numerators gives a program with at most `4L` operations that computes, for every
polynomial `p` computed by the original program, a polynomial `p♯` (at a valid operand) with
`p♯(ξ, u₀, ũ) = u₀^a · p(ξ, ũ/u₀)` whenever `u₀ ≠ 0`. -/
theorem homogenization (P : SLP (π ⊕ ζ) ℝ) :
    ∃ P' : SLP (π ⊕ Option ζ) ℝ, P'.length ≤ 4 * P.length ∧
      ∀ p, P.Computes p → ∃ (o : Operand (π ⊕ Option ζ) ℝ) (a : ℕ), OValid P'.length o ∧
        ∀ w : π ⊕ Option ζ → ℝ, w (.inr none) ≠ 0 →
          eval w (o.eval P'.values) = w (.inr none) ^ a * eval (dehom w) p := by
  refine ⟨(homog P).1, (homog_inv P).2.1, fun p ⟨o, ho⟩ => ?_⟩
  obtain ⟨hv, -, a, -, he⟩ := hOp_ok (homog_inv P) o
  exact ⟨_, a, hv, fun w hw => by rw [ho]; exact he w hw⟩

end Homog

/-! ### The margin system and its sum of squares -/

/-- The unknowns `ν = (u₀, ũ, σ₀, σ₁, …, σ_m)` of the margin system: `u₀ = inl none`,
`ũᵢ = inl (some i)`, `σ₀ = inr none`, `σⱼ = inr (some j)`. -/
abbrev MVar (ζ : Type) (m : ℕ) := Option ζ ⊕ Option (Fin m)

section MarginPoly

variable {π ζ : Type} [Fintype ζ]

/-- The embedding of the variables `(ξ, u₀, ũ)` of the homogenized polynomials into the variables
`π ⊕ Option (MVar ζ m)` of `Q` (whose coordinate `inr none` is `s`). -/
def hEmb (m : ℕ) : π ⊕ Option ζ → π ⊕ Option (MVar ζ m) :=
  Sum.elim Sum.inl (fun o => Sum.inr (some (Sum.inl o)))

/-- The sum of squares `Q` of the equations of the margin system (6):
`(u₀² + |ũ|² - 1)² + ∑ (p♯ᵢ)² + (u₀ - s - σ₀²)² + ∑ (q♯ⱼ - s - σⱼ²)²`. -/
def marginPoly {r m : ℕ} (pS : Fin r → MvPolynomial (π ⊕ Option ζ) ℝ)
    (qS : Fin m → MvPolynomial (π ⊕ Option ζ) ℝ) : MvPolynomial (π ⊕ Option (MVar ζ m)) ℝ :=
  (X (.inr (some (.inl none))) ^ 2 + ∑ i : ζ, X (.inr (some (.inl (some i)))) ^ 2 - 1) ^ 2 +
  ∑ i, rename (hEmb m) (pS i) ^ 2 +
  (X (.inr (some (.inl none))) - X (.inr none) - X (.inr (some (.inr none))) ^ 2) ^ 2 +
  ∑ j, (rename (hEmb m) (qS j) - X (.inr none) - X (.inr (some (.inr (some j)))) ^ 2) ^ 2

variable {r m : ℕ} (pS : Fin r → MvPolynomial (π ⊕ Option ζ) ℝ)
  (qS : Fin m → MvPolynomial (π ⊕ Option ζ) ℝ)

theorem marginPoly_nonneg (w : π ⊕ Option (MVar ζ m) → ℝ) : 0 ≤ eval w (marginPoly pS qS) := by
  simp only [marginPoly, map_add, map_pow, map_sum]
  positivity

theorem eval_marginPoly (ξ : π → ℝ) (s : ℝ) (ν : MVar ζ m → ℝ) :
    eval (Sum.elim ξ (extendVal s ν)) (marginPoly pS qS) =
      (ν (.inl none) ^ 2 + ∑ i, ν (.inl (some i)) ^ 2 - 1) ^ 2 +
      ∑ i, eval (Sum.elim ξ (fun o => ν (.inl o))) (pS i) ^ 2 +
      (ν (.inl none) - s - ν (.inr none) ^ 2) ^ 2 +
      ∑ j, (eval (Sum.elim ξ (fun o => ν (.inl o))) (qS j) - s - ν (.inr (some j)) ^ 2) ^ 2 := by
  have hc : Sum.elim ξ (extendVal s ν) ∘ hEmb m = Sum.elim ξ (fun o => ν (.inl o)) := by
    funext v; cases v <;> rfl
  simp [marginPoly, eval_rename, hc, extendVal]

/-- The zero set of `Q(ξ, ·)` is the set of solutions of the margin system (6). -/
theorem marginPoly_eq_zero_iff (ξ : π → ℝ) (s : ℝ) (ν : MVar ζ m → ℝ) :
    eval (Sum.elim ξ (extendVal s ν)) (marginPoly pS qS) = 0 ↔
      ν (.inl none) ^ 2 + ∑ i, ν (.inl (some i)) ^ 2 = 1 ∧
      (∀ i, eval (Sum.elim ξ (fun o => ν (.inl o))) (pS i) = 0) ∧
      ν (.inl none) - s = ν (.inr none) ^ 2 ∧
      ∀ j, eval (Sum.elim ξ (fun o => ν (.inl o))) (qS j) - s = ν (.inr (some j)) ^ 2 := by
  rw [eval_marginPoly]
  rw [add_eq_zero_iff_of_nonneg (by positivity) (by positivity),
    add_eq_zero_iff_of_nonneg (by positivity) (by positivity),
    add_eq_zero_iff_of_nonneg (by positivity) (by positivity),
    Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity),
    Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)]
  simp only [Finset.mem_univ, true_implies, pow_eq_zero_iff two_ne_zero, sub_eq_zero]
  tauto

/-- Every solution of (6) has `s ≤ 1`. -/
theorem margin_s_le_one {ξ : π → ℝ} {s : ℝ} {ν : MVar ζ m → ℝ}
    (h : eval (Sum.elim ξ (extendVal s ν)) (marginPoly pS qS) = 0) : s ≤ 1 := by
  rw [marginPoly_eq_zero_iff] at h
  obtain ⟨h1, -, h0, -⟩ := h
  have hs : 0 ≤ ∑ i, ν (.inl (some i)) ^ 2 := by positivity
  nlinarith [sq_nonneg (ν (.inr none)), sq_nonneg (ν (.inl none) - 1)]

/-- On a compact set of parameters, the unknowns `ν` of the solutions with `s ≥ 0` are bounded. -/
theorem margin_bounded {K : Set (π → ℝ)} (hK : IsCompact K) :
    ∃ R, 1 ≤ R ∧ ∀ ξ ∈ K, ∀ s ν, 0 ≤ s → eval (Sum.elim ξ (extendVal s ν)) (marginPoly pS qS) = 0 →
      ∀ k, |ν k| ≤ R := by
  set F : (π → ℝ) × (Option ζ → ℝ) → ℝ := fun p => ∑ j, |eval (Sum.elim p.1 p.2) (qS j)| with hF
  have hFc : Continuous F := by
    refine continuous_finsetSum _ fun j _ => ?_
    refine continuous_abs.comp ((MvPolynomial.continuous_eval (qS j)).comp ?_)
    refine continuous_pi fun v => ?_
    cases v with
    | inl p => exact (continuous_apply p).comp continuous_fst
    | inr o => exact (continuous_apply o).comp continuous_snd
  obtain ⟨M, hM⟩ := (hK.prod (isCompact_closedBall (0 : Option ζ → ℝ) 1)).exists_bound_of_continuousOn
    hFc.continuousOn
  refine ⟨max 1 M, le_max_left _ _, fun ξ hξ s ν hs h k => ?_⟩
  rw [marginPoly_eq_zero_iff] at h
  obtain ⟨h1, -, h0, hq⟩ := h
  have hsum : 0 ≤ ∑ i, ν (.inl (some i)) ^ 2 := by positivity
  have hu : ∀ o, |ν (.inl o)| ≤ 1 := by
    intro o
    refine abs_le_of_sq_le_sq ?_ zero_le_one
    cases o with
    | none => nlinarith
    | some i =>
      have := Finset.single_le_sum (f := fun i => ν (.inl (some i)) ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ i)
      nlinarith [sq_nonneg (ν (.inl none))]
  have hR : (1 : ℝ) ≤ max 1 M := le_max_left _ _
  cases k with
  | inl o => exact (hu o).trans hR
  | inr o =>
    cases o with
    | none =>
      have hu0 := abs_le.1 (hu none)
      refine (abs_le_of_sq_le_sq ?_ zero_le_one).trans hR
      nlinarith
    | some j =>
      have hmem : (ξ, fun o => ν (.inl o)) ∈ K ×ˢ Metric.closedBall (0 : Option ζ → ℝ) 1 := by
        refine ⟨hξ, ?_⟩
        rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
        intro o
        rw [Real.norm_eq_abs]
        exact hu o
      have hFb := hM _ hmem
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hFb
      have hqj : eval (Sum.elim ξ (fun o => ν (.inl o))) (qS j) ≤ M := by
        refine (le_abs_self _).trans (le_trans ?_ hFb)
        exact Finset.single_le_sum (f := fun j => |eval (Sum.elim ξ (fun o => ν (.inl o))) (qS j)|)
          (fun j _ => abs_nonneg _) (Finset.mem_univ j)
      have hsq : ν (.inr (some j)) ^ 2 ≤ max 1 M ^ 2 := by
        have := hq j
        have hM' : M ≤ max 1 M := le_max_right _ _
        nlinarith
      exact abs_le_of_sq_le_sq hsq (by linarith)

omit [Fintype ζ] in
theorem continuous_mpt :
    Continuous fun p : (π → ℝ) × ℝ × (MVar ζ m → ℝ) => Sum.elim p.1 (extendVal p.2.1 p.2.2) := by
  refine continuous_pi fun v => ?_
  cases v with
  | inl i => exact (continuous_apply i).comp continuous_fst
  | inr o =>
    cases o with
    | none => exact continuous_fst.comp continuous_snd
    | some k => exact (continuous_apply k).comp (continuous_snd.comp continuous_snd)

/-- Over a compact set of parameters, the solutions of (6) with `s ≥ s₀ ≥ 0` form a compact set. -/
theorem margin_isCompact {K : Set (π → ℝ)} (hK : IsCompact K) {s₀ : ℝ} (hs₀ : 0 ≤ s₀) :
    IsCompact {p : (π → ℝ) × ℝ × (MVar ζ m → ℝ) | p.1 ∈ K ∧ s₀ ≤ p.2.1 ∧
      eval (Sum.elim p.1 (extendVal p.2.1 p.2.2)) (marginPoly pS qS) = 0} := by
  obtain ⟨R, hR1, hR⟩ := margin_bounded pS qS hK
  refine (hK.prod ((isCompact_Icc (a := s₀) (b := 1)).prod
    (isCompact_closedBall (0 : MVar ζ m → ℝ) R))).of_isClosed_subset ?_ ?_
  · have h1 : Continuous fun p : (π → ℝ) × ℝ × (MVar ζ m → ℝ) => p.1 := continuous_fst
    have h2 : Continuous fun p : (π → ℝ) × ℝ × (MVar ζ m → ℝ) => p.2.1 :=
      continuous_fst.comp continuous_snd
    have h3 : IsClosed {p : (π → ℝ) × ℝ × (MVar ζ m → ℝ) |
        eval (Sum.elim p.1 (extendVal p.2.1 p.2.2)) (marginPoly pS qS) = 0} :=
      isClosed_eq ((MvPolynomial.continuous_eval _).comp continuous_mpt) continuous_const
    have h4 : IsClosed {p : (π → ℝ) × ℝ × (MVar ζ m → ℝ) | s₀ ≤ p.2.1} :=
      isClosed_le continuous_const h2
    exact (hK.isClosed.preimage h1).inter (h4.inter h3)
  · rintro ⟨ξ, s, ν⟩ ⟨hξ, hs, h⟩
    refine ⟨hξ, ⟨hs, margin_s_le_one pS qS h⟩, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by linarith)]
    intro k
    rw [Real.norm_eq_abs]
    exact hR ξ hξ s ν (hs₀.trans hs) h k

/-- The parameters in a compact set at which (6) has a solution with `s ≥ s₀ ≥ 0` form a closed
set. -/
theorem margin_isClosed_proj {K : Set (π → ℝ)} (hK : IsCompact K) {s₀ : ℝ} (hs₀ : 0 ≤ s₀) :
    IsClosed {ξ | ξ ∈ K ∧ ∃ s, s₀ ≤ s ∧ ∃ ν : MVar ζ m → ℝ,
      eval (Sum.elim ξ (extendVal s ν)) (marginPoly pS qS) = 0} := by
  have h1 : Continuous fun p : (π → ℝ) × ℝ × (MVar ζ m → ℝ) => p.1 := continuous_fst
  have := ((margin_isCompact pS qS hK hs₀).image h1).isClosed
  convert this using 1
  ext ξ
  simp only [Set.mem_ofPred_eq, Set.mem_image, Prod.exists]
  constructor
  · rintro ⟨hξ, s, hs, ν, h⟩
    exact ⟨ξ, s, ν, ⟨hξ, hs, h⟩, rfl⟩
  · rintro ⟨ξ', s, ν, ⟨hξ, hs, h⟩, rfl⟩
    exact ⟨hξ, s, hs, ν, h⟩

end MarginPoly

/-! ### Lemma 5.2 (a) -/

section Cert

variable {π ζ : Type} [Fintype ζ]

/-- The homogenized polynomials `p♯ᵢ`, `q♯ⱼ` of a cell: `p♯ᵢ(ξ, u₀, ũ) = u₀^{aᵢ} pᵢ(ξ, ũ/u₀)` and
`q♯ⱼ(ξ, u₀, ũ) = u₀^{bⱼ} qⱼ(ξ, ũ/u₀)` whenever `u₀ ≠ 0`. -/
structure IsHomog (B : Cell (π ⊕ ζ)) (pS : Fin B.eqs.length → MvPolynomial (π ⊕ Option ζ) ℝ)
    (qS : Fin B.poss.length → MvPolynomial (π ⊕ Option ζ) ℝ) : Prop where
  eqs : ∀ i, ∃ a : ℕ, ∀ w : π ⊕ Option ζ → ℝ, w (.inr none) ≠ 0 →
    eval w (pS i) = w (.inr none) ^ a * eval (dehom w) (B.eqs.get i)
  poss : ∀ j, ∃ b : ℕ, ∀ w : π ⊕ Option ζ → ℝ, w (.inr none) ≠ 0 →
    eval w (qS j) = w (.inr none) ^ b * eval (dehom w) (B.poss.get j)

variable {B : Cell (π ⊕ ζ)} {pS : Fin B.eqs.length → MvPolynomial (π ⊕ Option ζ) ℝ}
  {qS : Fin B.poss.length → MvPolynomial (π ⊕ Option ζ) ℝ}

/-- **Lemma 5.2 (a)** (general form): `ξ` has a certificate in the cell exactly when the margin
system (6) has a solution with `s > 0`. -/
theorem margin_cert_iff (hH : IsHomog B pS qS) (ξ : π → ℝ) :
    (∃ z : ζ → ℝ, Sum.elim ξ z ∈ B.carrier) ↔
      ∃ s > 0, ∃ ν : MVar ζ B.poss.length → ℝ,
        eval (Sum.elim ξ (extendVal s ν)) (marginPoly pS qS) = 0 := by
  constructor
  · rintro ⟨z, hz⟩
    set N := Real.sqrt (1 + ∑ i, z i ^ 2) with hN
    have hN0 : 0 < N := Real.sqrt_pos.2 (by positivity)
    set u : Option ζ → ℝ := fun o => o.elim (1 / N) (fun i => z i / N) with hu
    have hu0 : 0 < u none := by simp [u]; positivity
    have hdeh : dehom (Sum.elim ξ u) = Sum.elim ξ z := by
      funext v
      cases v with
      | inl p => rfl
      | inr i => simp [dehom, u]; field_simp
    have hp : ∀ i, eval (Sum.elim ξ u) (pS i) = 0 := fun i => by
      obtain ⟨a, ha⟩ := hH.eqs i
      rw [ha _ (by simpa using hu0.ne'), hdeh, hz.1 _ (List.get_mem _ _), mul_zero]
    have hq : ∀ j, 0 < eval (Sum.elim ξ u) (qS j) := fun j => by
      obtain ⟨b, hb⟩ := hH.poss j
      rw [hb _ (by simpa using hu0.ne'), hdeh]
      exact mul_pos (pow_pos (by simpa using hu0) _) (hz.2 _ (List.get_mem _ _))
    set g : Option (Fin B.poss.length) → ℝ :=
      fun o => o.elim (u none) (fun j => eval (Sum.elim ξ u) (qS j)) with hg
    obtain ⟨o₀, -, ho₀⟩ := Finset.exists_min_image Finset.univ g Finset.univ_nonempty
    have hs : 0 < g o₀ := by
      cases o₀ with
      | none => simpa [g] using hu0
      | some j => simpa [g] using hq j
    have hsu : g o₀ ≤ u none := ho₀ none (Finset.mem_univ _)
    have hsq : ∀ j, g o₀ ≤ eval (Sum.elim ξ u) (qS j) := fun j => ho₀ (some j) (Finset.mem_univ _)
    refine ⟨g o₀, hs, Sum.elim u (fun o => o.elim (Real.sqrt (u none - g o₀))
      (fun j => Real.sqrt (eval (Sum.elim ξ u) (qS j) - g o₀))), ?_⟩
    rw [marginPoly_eq_zero_iff]
    refine ⟨?_, fun i => hp i, ?_, fun j => ?_⟩
    · simp only [Sum.elim_inl, u, Option.elim_none, Option.elim_some]
      have hS : 0 ≤ ∑ i, z i ^ 2 := by positivity
      have hN2 : N ^ 2 = 1 + ∑ i, z i ^ 2 := Real.sq_sqrt (by positivity)
      simp_rw [div_pow]
      rw [← Finset.sum_div, ← add_div, one_pow, hN2]
      exact div_self (by positivity)
    · simp only [Sum.elim_inr, Sum.elim_inl, Option.elim_none]
      rw [Real.sq_sqrt (sub_nonneg.2 hsu)]
    · simp only [Sum.elim_inr, Sum.elim_inl, Option.elim_some]
      rw [Real.sq_sqrt (sub_nonneg.2 (hsq j))]
  · rintro ⟨s, hs, ν, hν⟩
    rw [marginPoly_eq_zero_iff] at hν
    obtain ⟨-, hp, h0, hq⟩ := hν
    set u : Option ζ → ℝ := fun o => ν (.inl o) with hu
    have hu0 : 0 < u none := by
      have := sq_nonneg (ν (.inr none)); simp only [u]; linarith
    have hdeh : dehom (Sum.elim ξ u) = Sum.elim ξ (fun i => u (some i) / u none) := by
      funext v; cases v <;> rfl
    refine ⟨fun i => u (some i) / u none, ?_, ?_⟩
    · intro p hpm
      obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hpm
      obtain ⟨a, ha⟩ := hH.eqs i
      have := ha (Sum.elim ξ u) (by simpa using hu0.ne')
      rw [hp i, hdeh] at this
      exact (mul_eq_zero.1 this.symm).resolve_left (pow_ne_zero _ (by simpa using hu0.ne'))
    · intro q hqm
      obtain ⟨j, rfl⟩ := List.mem_iff_get.1 hqm
      obtain ⟨b, hb⟩ := hH.poss j
      have := hb (Sum.elim ξ u) (by simpa using hu0.ne')
      rw [hdeh] at this
      have hpos : 0 < eval (Sum.elim ξ u) (qS j) := by
        have := hq j; nlinarith [sq_nonneg (ν (.inr (some j)))]
      rw [this] at hpos
      exact pos_of_mul_pos_right hpos (pow_nonneg (by simpa using hu0.le) _)

/-- **Lemma 5.2 (a)** (alias of `margin_cert_iff`). -/
theorem lemma_5_2_a (hH : IsHomog B pS qS) (ξ : π → ℝ) :
    (∃ z : ζ → ℝ, Sum.elim ξ z ∈ B.carrier) ↔
      ∃ s > 0, ∃ ν : MVar ζ B.poss.length → ℝ,
        eval (Sum.elim ξ (extendVal s ν)) (marginPoly pS qS) = 0 :=
  margin_cert_iff hH ξ

/-- At a parameter that has a certificate, the coordinate `s` attains a maximum `v ∈ (0, 1]` on
the solutions of (6) (used in Lemma 5.2 (b)). -/
theorem margin_attains (hH : IsHomog B pS qS) {ξ : π → ℝ}
    (hξ : ∃ z : ζ → ℝ, Sum.elim ξ z ∈ B.carrier) :
    ∃ v, IsGreatest {s | ∃ ν : MVar ζ B.poss.length → ℝ,
      eval (Sum.elim ξ (extendVal s ν)) (marginPoly pS qS) = 0} v ∧ 0 < v ∧ v ≤ 1 := by
  obtain ⟨s₁, hs₁, ν₁, h₁⟩ := (margin_cert_iff hH ξ).1 hξ
  set T := (fun p : (π → ℝ) × ℝ × (MVar ζ B.poss.length → ℝ) => p.2.1) ''
    {p | p.1 ∈ ({ξ} : Set (π → ℝ)) ∧ 0 ≤ p.2.1 ∧
      eval (Sum.elim p.1 (extendVal p.2.1 p.2.2)) (marginPoly pS qS) = 0} with hT
  have hTc : IsCompact T :=
    (margin_isCompact pS qS isCompact_singleton le_rfl).image
      (continuous_fst.comp continuous_snd)
  have hTne : T.Nonempty := ⟨s₁, ⟨(ξ, s₁, ν₁), ⟨rfl, hs₁.le, h₁⟩, rfl⟩⟩
  obtain ⟨g, ⟨⟨ξ', s', ν'⟩, ⟨hξ', hs', h'⟩, rfl⟩, hgmax⟩ := hTc.exists_isGreatest hTne
  simp only [Set.mem_singleton_iff] at hξ'
  subst hξ'
  have hg₁ : s₁ ≤ s' := hgmax ⟨(ξ', s₁, ν₁), ⟨rfl, hs₁.le, h₁⟩, rfl⟩
  refine ⟨s', ⟨⟨ν', h'⟩, fun s ⟨ν, hν⟩ => ?_⟩, lt_of_lt_of_le hs₁ hg₁,
    margin_s_le_one pS qS h'⟩
  rcases le_or_gt 0 s with hs | hs
  · exact hgmax ⟨(ξ', s, ν), ⟨rfl, hs, hν⟩, rfl⟩
  · linarith

end Cert

/-! ### A straight-line program for `Q` -/

section Build

variable {π ζ : Type} [Fintype ζ]

/-- The expression of `Q`, with the operands `op`, `oq` holding `p♯ᵢ`, `q♯ⱼ`. -/
def marginExpr {r m : ℕ} (op : Fin r → Operand (π ⊕ Option (MVar ζ m)) ℝ)
    (oq : Fin m → Operand (π ⊕ Option (MVar ζ m)) ℝ) : SExpr (π ⊕ Option (MVar ζ m)) :=
  let u0 : SExpr (π ⊕ Option (MVar ζ m)) := .leaf (.input (.inr (some (.inl none))))
  let s : SExpr (π ⊕ Option (MVar ζ m)) := .leaf (.input (.inr none))
  let E1 := SExpr.sq (.bin .sub (.bin .add (.sq u0) (SExpr.sumE ((Finset.univ : Finset ζ).toList.map
    fun i => .sq (.leaf (.input (.inr (some (.inl (some i))))))))) (.leaf (.const 1)))
  let E2 := SExpr.sumE ((Finset.univ : Finset (Fin r)).toList.map fun i => .sq (.leaf (op i)))
  let E3 := SExpr.sq (.bin .sub (.bin .sub u0 s) (.sq (.leaf (.input (.inr (some (.inr none)))))))
  let E4 := SExpr.sumE ((Finset.univ : Finset (Fin m)).toList.map fun j =>
    .sq (.bin .sub (.bin .sub (.leaf (oq j)) s) (.sq (.leaf (.input (.inr (some (.inr (some j)))))))))
  .bin .add (.bin .add (.bin .add E1 E2) E3) E4

theorem nodes_marginExpr {r m : ℕ} (op : Fin r → Operand (π ⊕ Option (MVar ζ m)) ℝ)
    (oq : Fin m → Operand (π ⊕ Option (MVar ζ m)) ℝ) :
    (marginExpr op oq).nodes = 2 * Fintype.card ζ + 2 * r + 5 * m + 11 := by
  simp only [marginExpr, SExpr.nodes, SExpr.nodes_sumE, List.map_map, Function.comp_def,
    List.length_map, Finset.length_toList, Finset.card_univ, Fintype.card_fin, List.map_const',
    List.sum_replicate, smul_eq_mul]
  ring

theorem valid_marginExpr {r m : ℕ} {op : Fin r → Operand (π ⊕ Option (MVar ζ m)) ℝ}
    {oq : Fin m → Operand (π ⊕ Option (MVar ζ m)) ℝ} {n : ℕ} (hop : ∀ i, OValid n (op i))
    (hoq : ∀ j, OValid n (oq j)) : (marginExpr op oq).Valid n := by
  simp only [marginExpr, SExpr.Valid]
  refine ⟨⟨⟨⟨⟨trivial, SExpr.valid_sumE _ ?_⟩, trivial⟩, SExpr.valid_sumE _ ?_⟩,
    ⟨trivial, trivial⟩, trivial⟩, SExpr.valid_sumE _ ?_⟩
  · simp only [List.mem_map]
    rintro e ⟨i, -, rfl⟩
    exact trivial
  · simp only [List.mem_map]
    rintro e ⟨i, -, rfl⟩
    exact hop i
  · simp only [List.mem_map]
    rintro e ⟨j, -, rfl⟩
    exact ⟨⟨hoq j, trivial⟩, trivial⟩

theorem den_marginExpr {r m : ℕ} {op : Fin r → Operand (π ⊕ Option (MVar ζ m)) ℝ}
    {oq : Fin m → Operand (π ⊕ Option (MVar ζ m)) ℝ}
    {pS : Fin r → MvPolynomial (π ⊕ Option ζ) ℝ} {qS : Fin m → MvPolynomial (π ⊕ Option ζ) ℝ}
    (vals : List (MvPolynomial (π ⊕ Option (MVar ζ m)) ℝ))
    (hop : ∀ i, (op i).eval vals = rename (hEmb m) (pS i))
    (hoq : ∀ j, (oq j).eval vals = rename (hEmb m) (qS j)) :
    (marginExpr op oq).den vals = marginPoly pS qS := by
  simp only [marginExpr, SExpr.den, SExpr.den_sumE, List.map_map, Function.comp_def,
    ArithOp.apply, eval_input, eval_const, hop, hoq, Finset.sum_map_toList, map_one, marginPoly]

/-- **The margin program**: a straight-line program for `Q = marginPoly p♯ q♯` with at most
`4L + 2|ζ| + 2r + 5m + 11` operations, where `L` is the length of the program of the cell. -/
theorem exists_margin (B : Cell (π ⊕ ζ)) (hcomp : ∀ p ∈ B.eqs ++ B.poss, B.prog.Computes p) :
    ∃ (pS : Fin B.eqs.length → MvPolynomial (π ⊕ Option ζ) ℝ)
      (qS : Fin B.poss.length → MvPolynomial (π ⊕ Option ζ) ℝ), IsHomog B pS qS ∧
      ∃ (P : SLP (π ⊕ Option (MVar ζ B.poss.length)) ℝ)
        (o : Operand (π ⊕ Option (MVar ζ B.poss.length)) ℝ),
        P.length ≤ 4 * B.prog.length + 2 * Fintype.card ζ + 2 * B.eqs.length +
          5 * B.poss.length + 11 ∧
        o.eval P.values = marginPoly pS qS := by
  obtain ⟨P', hP'len, hP'⟩ := homogenization B.prog
  have hE : ∀ i : Fin B.eqs.length, ∃ (o : Operand (π ⊕ Option ζ) ℝ) (a : ℕ),
      OValid P'.length o ∧ ∀ w : π ⊕ Option ζ → ℝ, w (.inr none) ≠ 0 →
        eval w (o.eval P'.values) = w (.inr none) ^ a * eval (dehom w) (B.eqs.get i) :=
    fun i => hP' _ (hcomp _ (List.mem_append_left _ (List.get_mem _ _)))
  have hQ : ∀ j : Fin B.poss.length, ∃ (o : Operand (π ⊕ Option ζ) ℝ) (b : ℕ),
      OValid P'.length o ∧ ∀ w : π ⊕ Option ζ → ℝ, w (.inr none) ≠ 0 →
        eval w (o.eval P'.values) = w (.inr none) ^ b * eval (dehom w) (B.poss.get j) :=
    fun j => hP' _ (hcomp _ (List.mem_append_right _ (List.get_mem _ _)))
  choose oE aE hvE heE using hE
  choose oQ aQ hvQ heQ using hQ
  refine ⟨fun i => (oE i).eval P'.values, fun j => (oQ j).eval P'.values,
    ⟨fun i => ⟨aE i, heE i⟩, fun j => ⟨aQ j, heQ j⟩⟩, ?_⟩
  -- rename the homogenized program into the variables of `Q`
  let ρ : π ⊕ Option ζ → Operand (π ⊕ Option (MVar ζ B.poss.length)) ℝ :=
    fun v => .input (hEmb B.poss.length v)
  have hρ : NoPrev ρ := fun _ _ h => by cases h
  have hρp : ∀ p, bind₁ (ρpoly ρ) p = rename (hEmb B.poss.length) p := fun p => bind₁_X_comp _ p
  set P'' := SLP.substIn ρ P' with hP''
  have hlen'' : P''.length = P'.length := SLP.length_substIn _ _
  have hval : ∀ o : Operand (π ⊕ Option ζ) ℝ,
      (Operand.substIn ρ o).eval P''.values = rename (hEmb B.poss.length) (o.eval P'.values) := by
    intro o
    rw [hP'', SLP.values_substIn hρ, eval_substIn hρ, hρp]
  have hv : (marginExpr (fun i => Operand.substIn ρ (oE i)) (fun j => Operand.substIn ρ (oQ j))).Valid
      P''.length :=
    valid_marginExpr (fun i => by rw [hlen'']; exact (hvE i).substIn hρ)
      (fun j => by rw [hlen'']; exact (hvQ j).substIn hρ)
  obtain ⟨P, o, hPlen, ho⟩ := exists_append_expr P'' _ hv
  refine ⟨P, o, ?_, ?_⟩
  · rw [hPlen, nodes_marginExpr, hlen'']
    omega
  · rw [ho]
    exact den_marginExpr _ (fun i => hval _) (fun j => hval _)

/-- **The margin program as a program graph** (for Proposition 4.5): a program graph with
constant slots and at most `4L + 2|ζ| + 2r + 5m + 11` operations computing `Q`. -/
theorem exists_margin_graph (B : Cell (π ⊕ ζ)) (hcomp : ∀ p ∈ B.eqs ++ B.poss, B.prog.Computes p) :
    ∃ (pS : Fin B.eqs.length → MvPolynomial (π ⊕ Option ζ) ℝ)
      (qS : Fin B.poss.length → MvPolynomial (π ⊕ Option ζ) ℝ), IsHomog B pS qS ∧
      ∃ (prog : SLP (π ⊕ Option (MVar ζ B.poss.length)) ℕ) (cQ : ℕ → ℝ)
        (oQ : Operand (π ⊕ Option (MVar ζ B.poss.length)) ℕ),
        prog.length ≤ 4 * B.prog.length + 2 * Fintype.card ζ + 2 * B.eqs.length +
          5 * B.poss.length + 11 ∧
        progOutput prog cQ oQ = marginPoly pS qS := by
  obtain ⟨pS, qS, hH, P, o, hlen, ho⟩ := exists_margin B hcomp
  refine ⟨pS, qS, hH, BaurStrassen.graphOf (BaurStrassen.allConsts P o) P,
    fun m => (BaurStrassen.allConsts P o).getD m 0,
    BaurStrassen.toSlot (BaurStrassen.allConsts P o) o, ?_, ?_⟩
  · rw [BaurStrassen.length_graphOf]; exact hlen
  · rw [progOutput, BaurStrassen.graphOf_instantiate, BaurStrassen.toSlot_out_instantiate, ho]

end Build

end Margin

end ClassSep
