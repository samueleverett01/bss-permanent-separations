import ClassSeparations.Core.BaurStrassen

/-!
# Compiling arithmetic expressions to straight-line programs

A small language of arithmetic expressions whose leaves are input coordinates and constant
slots, with squaring (sharing the squared subexpression), powers by repeated squaring, and
embedded program graphs (with renamed inputs and constants).  `Ex.comp` compiles an expression
to a program graph; `Ex.comp_spec` computes the polynomial obtained, and `Ex.comp_length` the
number of operations.  Used for the program of the system of Lemma 6.6.

Conventions on the constants: slot `0` holds `0` and slot `1` holds `1`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open MvPolynomial

namespace ClassSep

namespace SecondAux

open BaurStrassen

variable {V V₀ : Type}

/-- Arithmetic expressions. -/
inductive Ex (V V₀ : Type) where
  | leaf (o : Operand V ℕ)
  | add (a b : Ex V V₀)
  | sub (a b : Ex V V₀)
  | mul (a b : Ex V V₀)
  | sq (a : Ex V V₀)
  | pow (a : Ex V V₀) (N : ℕ)
  | prog (P : SLP V₀ ℕ) (o : Operand V₀ ℕ) (ρ : V₀ → Operand V ℕ) (cm : ℕ → ℕ)

/-- An operand that does not read earlier instructions. -/
def Closed : Operand V ℕ → Prop
  | .prev _ => False
  | _ => True

/-- All leaves (and renamed inputs) are closed. -/
def Ex.Ok : Ex V V₀ → Prop
  | .leaf o => Closed o
  | .add a b => a.Ok ∧ b.Ok
  | .sub a b => a.Ok ∧ b.Ok
  | .mul a b => a.Ok ∧ b.Ok
  | .sq a => a.Ok
  | .pow a _ => a.Ok
  | .prog _ _ ρ _ => ∀ v, Closed (ρ v)

/-- The polynomial computed by an expression, with constants `c`. -/
def Ex.peval (c : ℕ → ℝ) : Ex V V₀ → MvPolynomial V ℝ
  | .leaf o => ev c [] o
  | .add a b => a.peval c + b.peval c
  | .sub a b => a.peval c - b.peval c
  | .mul a b => a.peval c * b.peval c
  | .sq a => a.peval c ^ 2
  | .pow a N => a.peval c ^ N
  | .prog P o ρ cm => bind₁ (fun v => ev c [] (ρ v)) (progOutput P (c ∘ cm) o)

/-- The number of instructions of repeated squaring. -/
def powLen (N : ℕ) : ℕ :=
  if N ≤ 1 then 0 else powLen (N / 2) + (if N % 2 = 0 then 1 else 2)
termination_by N
decreasing_by omega

/-- Repeated squaring of the operand `u`, at offset `n`. -/
def pw (u : Operand V ℕ) (N : ℕ) (n : ℕ) : SLP V ℕ × Operand V ℕ :=
  if N = 0 then ([], .const 1)
  else if N = 1 then ([], u)
  else
    let r := pw u (N / 2) n
    if N % 2 = 0 then (r.1 ++ [⟨.mul, r.2, r.2⟩], .prev (n + r.1.length))
    else (r.1 ++ [⟨.mul, r.2, r.2⟩, ⟨.mul, .prev (n + r.1.length), u⟩],
      .prev (n + r.1.length + 1))
termination_by N
decreasing_by omega

/-- Renaming an operand of an embedded program at offset `n`. -/
def relocOp (n : ℕ) (ρ : V₀ → Operand V ℕ) (cm : ℕ → ℕ) : Operand V₀ ℕ → Operand V ℕ
  | .input v => ρ v
  | .const m => .const (cm m)
  | .prev j => .prev (n + j)

/-- An embedded program at offset `n`. -/
def reloc (n : ℕ) (ρ : V₀ → Operand V ℕ) (cm : ℕ → ℕ) (P : SLP V₀ ℕ) : SLP V ℕ :=
  P.map fun ins => ⟨ins.op, relocOp n ρ cm ins.a, relocOp n ρ cm ins.b⟩

/-- The output operand of an embedded program of length `L`; out-of-range references read the
slot `0` (which holds `0`). -/
def relocOut (n : ℕ) (ρ : V₀ → Operand V ℕ) (cm : ℕ → ℕ) (L : ℕ) :
    Operand V₀ ℕ → Operand V ℕ
  | .input v => ρ v
  | .const m => .const (cm m)
  | .prev j => if j < L then .prev (n + j) else .const 0

/-- Compile an expression at offset `n`. -/
def Ex.comp : Ex V V₀ → ℕ → SLP V ℕ × Operand V ℕ
  | .leaf o, _ => ([], o)
  | .add a b, n =>
    let ra := a.comp n
    let rb := b.comp (n + ra.1.length)
    (ra.1 ++ rb.1 ++ [⟨.add, ra.2, rb.2⟩], .prev (n + ra.1.length + rb.1.length))
  | .sub a b, n =>
    let ra := a.comp n
    let rb := b.comp (n + ra.1.length)
    (ra.1 ++ rb.1 ++ [⟨.sub, ra.2, rb.2⟩], .prev (n + ra.1.length + rb.1.length))
  | .mul a b, n =>
    let ra := a.comp n
    let rb := b.comp (n + ra.1.length)
    (ra.1 ++ rb.1 ++ [⟨.mul, ra.2, rb.2⟩], .prev (n + ra.1.length + rb.1.length))
  | .sq a, n =>
    let ra := a.comp n
    (ra.1 ++ [⟨.mul, ra.2, ra.2⟩], .prev (n + ra.1.length))
  | .pow a N, n =>
    let ra := a.comp n
    let rp := pw ra.2 N (n + ra.1.length)
    (ra.1 ++ rp.1, rp.2)
  | .prog P o ρ cm, n => (reloc n ρ cm P, relocOut n ρ cm P.length o)

/-- The size of an expression: the number of instructions of its compilation. -/
def Ex.size : Ex V V₀ → ℕ
  | .leaf _ => 0
  | .add a b => a.size + b.size + 1
  | .sub a b => a.size + b.size + 1
  | .mul a b => a.size + b.size + 1
  | .sq a => a.size + 1
  | .pow a N => a.size + powLen N
  | .prog P _ _ _ => P.length

/-! ### Lengths -/

theorem length_pw (u : Operand V ℕ) (N n : ℕ) : (pw u N n).1.length = powLen N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rw [pw, powLen]
    by_cases h0 : N = 0
    · simp [h0]
    by_cases h1 : N = 1
    · simp [h1]
    have hle : ¬ N ≤ 1 := by omega
    simp only [h0, h1, if_false, hle]
    have := ih (N / 2) (by omega)
    split_ifs <;> simp [this]

theorem powLen_le (N : ℕ) : powLen N ≤ 2 * Nat.log 2 N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rw [powLen]
    split_ifs with h1 h2
    · exact Nat.zero_le _
    · have := ih (N / 2) (by omega)
      have hlog : Nat.log 2 N = Nat.log 2 (N / 2) + 1 := by
        rw [Nat.log_of_one_lt_of_le (by norm_num) (by omega)]
      omega
    · have := ih (N / 2) (by omega)
      have hlog : Nat.log 2 N = Nat.log 2 (N / 2) + 1 := by
        rw [Nat.log_of_one_lt_of_le (by norm_num) (by omega)]
      omega

theorem Ex.comp_length : ∀ (e : Ex V V₀) (n : ℕ), (e.comp n).1.length = e.size
  | .leaf o, n => rfl
  | .add a b, n => by
    simp only [Ex.comp, Ex.size, List.length_append, List.length_singleton,
      Ex.comp_length a, Ex.comp_length b]
  | .sub a b, n => by
    simp only [Ex.comp, Ex.size, List.length_append, List.length_singleton,
      Ex.comp_length a, Ex.comp_length b]
  | .mul a b, n => by
    simp only [Ex.comp, Ex.size, List.length_append, List.length_singleton,
      Ex.comp_length a, Ex.comp_length b]
  | .sq a, n => by
    simp only [Ex.comp, Ex.size, List.length_append, List.length_singleton, Ex.comp_length a]
  | .pow a N, n => by
    simp only [Ex.comp, Ex.size, List.length_append, Ex.comp_length a, length_pw]
  | .prog P o ρ cm, n => by simp [Ex.comp, Ex.size, reloc]

/-! ### Semantics -/

theorem ev_closed (c : ℕ → ℝ) (W : List (MvPolynomial V ℝ)) {o : Operand V ℕ}
    (ho : Closed o) : ev c W o = ev c [] o := by
  cases o with
  | prev j => exact absurd ho id
  | _ => rfl

theorem valid_closed {n : ℕ} {o : Operand V ℕ} (ho : Closed o) : Valid n o := by
  cases o with
  | prev j => exact absurd ho id
  | _ => trivial

theorem pw_spec (c : ℕ → ℝ) (hc1 : c 1 = 1) (u : Operand V ℕ) (N : ℕ) :
    ∀ (Pre : SLP V ℕ), Valid Pre.length u →
      ev c (vals c (Pre ++ (pw u N Pre.length).1)) (pw u N Pre.length).2 =
        ev c (vals c Pre) u ^ N ∧
      Valid (Pre.length + (pw u N Pre.length).1.length) (pw u N Pre.length).2 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro Pre hu
    by_cases h0 : N = 0
    · subst h0
      rw [pw, if_pos rfl]
      exact ⟨by simp [hc1], trivial⟩
    by_cases h1 : N = 1
    · subst h1
      rw [pw, if_neg one_ne_zero, if_pos rfl]
      exact ⟨by simp, by simpa using hu⟩
    obtain ⟨ih1, ih2⟩ := ih (N / 2) (by omega) Pre hu
    set r := pw u (N / 2) Pre.length with hr
    have hpre : Pre <+: Pre ++ r.1 := List.prefix_append _ _
    have hlen : (Pre ++ r.1).length = Pre.length + r.1.length := List.length_append
    rw [pw]
    simp only [h0, h1, if_false]
    rw [← hr]
    by_cases hev : N % 2 = 0
    · simp only [hev, if_true]
      have heq : N = 2 * (N / 2) := by omega
      refine ⟨?_, show Pre.length + r.1.length < Pre.length + (r.1 ++ _).length by simp⟩
      -- the value
      rw [← List.append_assoc, ← hlen, ev_last, ih1]
      simp only [ArithOp.apply]
      conv_rhs => rw [heq, pow_mul]
      ring
    · simp only [hev, if_false]
      have heq : N = 2 * (N / 2) + 1 := by omega
      refine ⟨?_, show Pre.length + r.1.length + 1 < Pre.length + (r.1 ++ _).length by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega⟩
      have e : Pre ++ (r.1 ++ [⟨.mul, r.2, r.2⟩, ⟨.mul, .prev (Pre.length + r.1.length), u⟩]) =
          (Pre ++ r.1 ++ [⟨.mul, r.2, r.2⟩]) ++ [⟨.mul, .prev (Pre.length + r.1.length), u⟩] := by
        simp
      have hlen2 : (Pre ++ r.1 ++ [(⟨.mul, r.2, r.2⟩ : Instr V ℕ)]).length =
          Pre.length + r.1.length + 1 := by
        simp only [List.length_append, List.length_singleton]
      rw [e, ← hlen2, ev_last]
      simp only [ArithOp.apply]
      rw [ev_prev, show Pre.length + r.1.length = (Pre ++ r.1).length from hlen.symm]
      have hlast := ev_last c (Pre ++ r.1) (⟨.mul, r.2, r.2⟩ : Instr V ℕ)
      rw [ev_prev] at hlast
      rw [hlast, ih1]
      have hpre2 : Pre <+: Pre ++ r.1 ++ [(⟨.mul, r.2, r.2⟩ : Instr V ℕ)] :=
        List.prefix_append_of_prefix hpre
      rw [ev_mono c hpre2 hu]
      simp only [ArithOp.apply]
      conv_rhs => rw [heq, pow_succ, pow_mul]
      ring

/-- Values of an embedded program. -/
theorem vals_reloc (c : ℕ → ℝ) (ρ : V₀ → Operand V ℕ) (cm : ℕ → ℕ) (hρ : ∀ v, Closed (ρ v))
    (Pre : SLP V ℕ) :
    ∀ P : SLP V₀ ℕ, vals c (Pre ++ reloc Pre.length ρ cm P) =
      vals c Pre ++ (vals (c ∘ cm) P).map (bind₁ fun v => ev c [] (ρ v)) := by
  intro P
  induction P using List.reverseRecOn with
  | nil => simp [reloc, vals, SLP.instantiate, SLP.values]
  | append_singleton P ins ih =>
    have h1 : reloc Pre.length ρ cm (P ++ [ins]) = reloc Pre.length ρ cm P ++
        [⟨ins.op, relocOp Pre.length ρ cm ins.a, relocOp Pre.length ρ cm ins.b⟩] := by
      simp [reloc]
    rw [h1, ← List.append_assoc, vals_append_single, ih, vals_append_single, List.map_append,
      List.append_assoc]
    congr 2
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
    have hop : ∀ x : Operand V₀ ℕ,
        ev c (vals c Pre ++ (vals (c ∘ cm) P).map (bind₁ fun v => ev c [] (ρ v)))
          (relocOp Pre.length ρ cm x) =
        bind₁ (fun v => ev c [] (ρ v)) (ev (c ∘ cm) (vals (c ∘ cm) P) x) := by
      intro x
      cases x with
      | input v => simp only [relocOp, ev_input, bind₁_X_right]; exact ev_closed _ _ (hρ v)
      | const m => simp [relocOp]
      | prev j =>
        simp only [relocOp, ev_prev]
        rw [List.getD_append_right _ _ _ _ (by rw [length_vals]; omega), length_vals,
          Nat.add_sub_cancel_left]
        by_cases hj : j < (vals (c ∘ cm) P).length
        · rw [List.getD_eq_getElem _ _ (by simpa using hj),
            List.getD_eq_getElem _ _ hj, List.getElem_map]
        · rw [List.getD_eq_default _ _ (by simpa using hj),
            List.getD_eq_default _ _ (by omega), map_zero]
    rw [hop, hop]
    cases ins.op <;> simp [ArithOp.apply]

theorem Ex.comp_spec (c : ℕ → ℝ) (hc0 : c 0 = 0) (hc1 : c 1 = 1) :
    ∀ (e : Ex V V₀), e.Ok → ∀ (Pre : SLP V ℕ),
      ev c (vals c (Pre ++ (e.comp Pre.length).1)) (e.comp Pre.length).2 = e.peval c ∧
      Valid (Pre.length + (e.comp Pre.length).1.length) (e.comp Pre.length).2
  | .leaf o, ho, Pre => by
    simp only [Ex.comp, List.append_nil, Ex.peval]
    exact ⟨ev_closed _ _ ho, valid_closed ho⟩
  | .add a b, ⟨ha, hb⟩, Pre => by
    obtain ⟨a1, a2⟩ := Ex.comp_spec c hc0 hc1 a ha Pre
    have hlen : (Pre ++ (a.comp Pre.length).1).length = Pre.length + (a.comp Pre.length).1.length :=
      List.length_append
    obtain ⟨b1, b2⟩ := Ex.comp_spec c hc0 hc1 b hb (Pre ++ (a.comp Pre.length).1)
    rw [hlen] at b1 b2
    have hpre : Pre ++ (a.comp Pre.length).1 <+:
        Pre ++ (a.comp Pre.length).1 ++ (b.comp (Pre.length + (a.comp Pre.length).1.length)).1 :=
      List.prefix_append _ _
    refine ⟨?_, ?_⟩
    · simp only [Ex.comp, Ex.peval]
      have e : Pre ++ ((a.comp Pre.length).1 ++
          (b.comp (Pre.length + (a.comp Pre.length).1.length)).1 ++
          [⟨.add, (a.comp Pre.length).2,
            (b.comp (Pre.length + (a.comp Pre.length).1.length)).2⟩]) =
          (Pre ++ (a.comp Pre.length).1 ++
            (b.comp (Pre.length + (a.comp Pre.length).1.length)).1) ++
          [⟨.add, (a.comp Pre.length).2,
            (b.comp (Pre.length + (a.comp Pre.length).1.length)).2⟩] := by simp
      rw [e]
      have hl : Pre.length + (a.comp Pre.length).1.length +
          (b.comp (Pre.length + (a.comp Pre.length).1.length)).1.length =
          (Pre ++ (a.comp Pre.length).1 ++
            (b.comp (Pre.length + (a.comp Pre.length).1.length)).1).length := by
        simp only [List.length_append]
      rw [hl, ev_last]
      simp only [ArithOp.apply]
      rw [ev_mono c hpre (by rw [hlen]; exact a2), a1, b1]
    · simp only [Ex.comp, List.length_append, List.length_singleton]
      show _ < _
      omega
  | .sub a b, ⟨ha, hb⟩, Pre => by
    obtain ⟨a1, a2⟩ := Ex.comp_spec c hc0 hc1 a ha Pre
    have hlen : (Pre ++ (a.comp Pre.length).1).length = Pre.length + (a.comp Pre.length).1.length :=
      List.length_append
    obtain ⟨b1, b2⟩ := Ex.comp_spec c hc0 hc1 b hb (Pre ++ (a.comp Pre.length).1)
    rw [hlen] at b1 b2
    have hpre : Pre ++ (a.comp Pre.length).1 <+:
        Pre ++ (a.comp Pre.length).1 ++ (b.comp (Pre.length + (a.comp Pre.length).1.length)).1 :=
      List.prefix_append _ _
    refine ⟨?_, ?_⟩
    · simp only [Ex.comp, Ex.peval]
      have e : Pre ++ ((a.comp Pre.length).1 ++
          (b.comp (Pre.length + (a.comp Pre.length).1.length)).1 ++
          [⟨.sub, (a.comp Pre.length).2,
            (b.comp (Pre.length + (a.comp Pre.length).1.length)).2⟩]) =
          (Pre ++ (a.comp Pre.length).1 ++
            (b.comp (Pre.length + (a.comp Pre.length).1.length)).1) ++
          [⟨.sub, (a.comp Pre.length).2,
            (b.comp (Pre.length + (a.comp Pre.length).1.length)).2⟩] := by simp
      rw [e]
      have hl : Pre.length + (a.comp Pre.length).1.length +
          (b.comp (Pre.length + (a.comp Pre.length).1.length)).1.length =
          (Pre ++ (a.comp Pre.length).1 ++
            (b.comp (Pre.length + (a.comp Pre.length).1.length)).1).length := by
        simp only [List.length_append]
      rw [hl, ev_last]
      simp only [ArithOp.apply]
      rw [ev_mono c hpre (by rw [hlen]; exact a2), a1, b1]
    · simp only [Ex.comp, List.length_append, List.length_singleton]
      show _ < _
      omega
  | .mul a b, ⟨ha, hb⟩, Pre => by
    obtain ⟨a1, a2⟩ := Ex.comp_spec c hc0 hc1 a ha Pre
    have hlen : (Pre ++ (a.comp Pre.length).1).length = Pre.length + (a.comp Pre.length).1.length :=
      List.length_append
    obtain ⟨b1, b2⟩ := Ex.comp_spec c hc0 hc1 b hb (Pre ++ (a.comp Pre.length).1)
    rw [hlen] at b1 b2
    have hpre : Pre ++ (a.comp Pre.length).1 <+:
        Pre ++ (a.comp Pre.length).1 ++ (b.comp (Pre.length + (a.comp Pre.length).1.length)).1 :=
      List.prefix_append _ _
    refine ⟨?_, ?_⟩
    · simp only [Ex.comp, Ex.peval]
      have e : Pre ++ ((a.comp Pre.length).1 ++
          (b.comp (Pre.length + (a.comp Pre.length).1.length)).1 ++
          [⟨.mul, (a.comp Pre.length).2,
            (b.comp (Pre.length + (a.comp Pre.length).1.length)).2⟩]) =
          (Pre ++ (a.comp Pre.length).1 ++
            (b.comp (Pre.length + (a.comp Pre.length).1.length)).1) ++
          [⟨.mul, (a.comp Pre.length).2,
            (b.comp (Pre.length + (a.comp Pre.length).1.length)).2⟩] := by simp
      rw [e]
      have hl : Pre.length + (a.comp Pre.length).1.length +
          (b.comp (Pre.length + (a.comp Pre.length).1.length)).1.length =
          (Pre ++ (a.comp Pre.length).1 ++
            (b.comp (Pre.length + (a.comp Pre.length).1.length)).1).length := by
        simp only [List.length_append]
      rw [hl, ev_last]
      simp only [ArithOp.apply]
      rw [ev_mono c hpre (by rw [hlen]; exact a2), a1, b1]
    · simp only [Ex.comp, List.length_append, List.length_singleton]
      show _ < _
      omega
  | .sq a, ha, Pre => by
    obtain ⟨a1, a2⟩ := Ex.comp_spec c hc0 hc1 a ha Pre
    have hlen : (Pre ++ (a.comp Pre.length).1).length =
        Pre.length + (a.comp Pre.length).1.length := List.length_append
    refine ⟨?_, ?_⟩
    · simp only [Ex.comp, Ex.peval]
      rw [← List.append_assoc, ← hlen, ev_last]
      simp only [ArithOp.apply]
      rw [a1, pow_two]
    · simp only [Ex.comp, List.length_append, List.length_singleton]
      show _ < _
      omega
  | .pow a N, ha, Pre => by
    obtain ⟨a1, a2⟩ := Ex.comp_spec c hc0 hc1 a ha Pre
    have hlen : (Pre ++ (a.comp Pre.length).1).length =
        Pre.length + (a.comp Pre.length).1.length := List.length_append
    obtain ⟨p1, p2⟩ := pw_spec c hc1 (a.comp Pre.length).2 N (Pre ++ (a.comp Pre.length).1)
      (by rw [hlen]; exact a2)
    rw [hlen] at p1 p2
    refine ⟨?_, ?_⟩
    · simp only [Ex.comp, Ex.peval]
      rw [← List.append_assoc, p1, a1]
    · simp only [Ex.comp, List.length_append]
      rw [← add_assoc]
      exact p2
  | .prog P o ρ cm, hρ, Pre => by
    refine ⟨?_, ?_⟩
    · simp only [Ex.comp, Ex.peval]
      rw [vals_reloc c ρ cm hρ Pre P]
      cases o with
      | input v =>
        simp only [relocOut, progOutput]
        rw [ev_closed _ _ (hρ v)]
        simp [Operand.instantiate, Operand.eval]
      | const m => simp [relocOut, progOutput, Operand.instantiate, Operand.eval]
      | prev j =>
        simp only [relocOut]
        split_ifs with hj
        · simp only [ev_prev, progOutput]
          rw [List.getD_append_right _ _ _ _ (by rw [length_vals]; omega), length_vals,
            Nat.add_sub_cancel_left]
          have hj' : j < (vals (c ∘ cm) P).length := by rw [length_vals]; exact hj
          rw [List.getD_eq_getElem _ _ (by simpa using hj'), List.getElem_map]
          show _ = bind₁ _ ((vals (c ∘ cm) P).getD j 0)
          rw [List.getD_eq_getElem _ _ hj']
        · simp only [ev_const, hc0, map_zero, progOutput]
          simp only [Operand.instantiate, Operand.eval]
          rw [List.getD_eq_default _ _ (by
            have := length_vals (c ∘ cm) P
            simp only [vals] at this
            omega)]
          simp
    · simp only [Ex.comp]
      cases o with
      | input v => exact valid_closed (hρ v)
      | const m => trivial
      | prev j =>
        simp only [relocOut]
        split_ifs with hj
        · show _ < _
          simp [reloc]; omega
        · trivial

end SecondAux

end ClassSep
