import ClassSeparations.Second.EnvBasic
import ClassSeparations.Second.ExProg
import ClassSeparations.Cert.Value

/-!
# The envelope is a value function (§6.4, Lemma 6.6)

**Lemma 6.6.**  For every `D ≥ 1` there are finitely many circuit graphs, each with at most
`s_e(D)` gates (a polynomial in `D, κ, M, ℓ, log N, n`), and a dense semialgebraic set `𝒪°`
of `𝒪 = int K × ℝ^κ`, such that at every `ξ₁ ∈ 𝒪°` the function `e` is of class `C^D` near
`ξ₁` and its Taylor polynomial of order `D` at `ξ₁` is a coefficientwise limit of polynomials
of degree at most `D` computed by one of these graphs with real constants.

*Proof.*  Assign a rejecting cell to each of the `r = κ + 3` atoms.  For one assignment the
constraints on weights and atoms form one polynomial system with parameters `ξ = (x, c)`: the
margin system of the assigned cell for each atom, `s_i = θ_i²`, `|ω_i - w₀|² + ρ_i² = r₀²`,
`λ_i = β_i²`, `∑ β_i² = 1` and `T = J`.  Its sum of squares `Q` (the margin systems are already
nonnegative) has a straight-line program with `O(κ(ℓ + log N) + κ³)` operations (repeated
squaring for `s^N`), see `exists_prog`.  The sets on which an assignment attains `e` are
semialgebraic and cover `𝒪`, so the union of their interiors is dense (S4)(a); on each interior
Proposition 4.5 applies with the coordinate `T` in the role of `s`.

(We keep `s_i` as an unknown with the equation `s_i = θ_i²`, so that each margin program is
embedded with input coordinates only.)
-/

noncomputable section

set_option linter.unusedSectionVars false

open MvPolynomial Set Filter Topology

namespace ClassSep

open SecondAux

namespace SecondAux

/-- The unknowns of the polynomial system of one assignment: for each of the `r` atoms, the
atom `ω`, the unknowns `ν` of its margin system, and `θ, ρ, β, s` (`s = θ²`, slack `ρ`,
weight `β²`). -/
abbrev Unk (κ : Type) (M r : ℕ) := Fin r × (κ ⊕ Fin M ⊕ Fin 4)

namespace Unk

variable {κ : Type} {M r : ℕ}

def om (ν : Unk κ M r → ℝ) (i : Fin r) (k : κ) : ℝ := ν (i, Sum.inl k)
def nu (ν : Unk κ M r → ℝ) (i : Fin r) (m : Fin M) : ℝ := ν (i, Sum.inr (Sum.inl m))
def th (ν : Unk κ M r → ℝ) (i : Fin r) : ℝ := ν (i, Sum.inr (Sum.inr 0))
def rh (ν : Unk κ M r → ℝ) (i : Fin r) : ℝ := ν (i, Sum.inr (Sum.inr 1))
def be (ν : Unk κ M r → ℝ) (i : Fin r) : ℝ := ν (i, Sum.inr (Sum.inr 2))
def sv (ν : Unk κ M r → ℝ) (i : Fin r) : ℝ := ν (i, Sum.inr (Sum.inr 3))

/-- The configuration encoded by the unknowns. -/
def cfg (ν : Unk κ M r → ℝ) : Cfg κ M r → ℝ :=
  Cfg.mk (fun i => be ν i ^ 2) (om ν) (sv ν) (nu ν)

/-- Assemble the unknowns. -/
def mk (om : Fin r → κ → ℝ) (nu : Fin r → Fin M → ℝ) (th rh be sv : Fin r → ℝ) :
    Unk κ M r → ℝ
  | (i, Sum.inl k) => om i k
  | (i, Sum.inr (Sum.inl m)) => nu i m
  | (i, Sum.inr (Sum.inr j)) => ![th i, rh i, be i, sv i] j

end Unk

/-! ### Sums of expressions -/

variable {V V₀ : Type}

/-- The sum of a list of expressions. -/
def exSum (l : List (Ex V V₀)) : Ex V V₀ := l.foldr Ex.add (.leaf (.const 0))

theorem peval_exSum (c : ℕ → ℝ) (hc0 : c 0 = 0) (l : List (Ex V V₀)) :
    (exSum l).peval c = (l.map (Ex.peval c)).sum := by
  induction l with
  | nil => simp [exSum, Ex.peval, hc0]
  | cons e l ih =>
    simp only [exSum, List.foldr_cons, Ex.peval, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]

theorem ok_exSum (l : List (Ex V V₀)) (h : ∀ e ∈ l, e.Ok) : (exSum l).Ok := by
  induction l with
  | nil => exact trivial
  | cons e l ih =>
    exact ⟨h e (List.mem_cons_self ..), ih fun e' he' => h e' (List.mem_cons_of_mem _ he')⟩

theorem size_exSum_le (l : List (Ex V V₀)) (s : ℕ) (h : ∀ e ∈ l, e.size ≤ s) :
    (exSum l).size ≤ l.length * (s + 1) := by
  induction l with
  | nil => simp [exSum, Ex.size]
  | cons e l ih =>
    have h1 := h e (List.mem_cons_self ..)
    have h2 := ih fun e' he' => h e' (List.mem_cons_of_mem _ he')
    simp only [exSum, List.foldr_cons, Ex.size, List.length_cons] at h2 ⊢
    nlinarith

/-- A sum over `Fin r`. -/
def sumR {r : ℕ} (f : Fin r → Ex V V₀) : Ex V V₀ := exSum (List.ofFn f)

/-- A sum over a finite type. -/
def sumK {κ : Type} [Fintype κ] (f : κ → Ex V V₀) : Ex V V₀ :=
  exSum (List.ofFn fun j => f ((Fintype.equivFin κ).symm j))

theorem peval_sumR (c : ℕ → ℝ) (hc0 : c 0 = 0) {r : ℕ} (f : Fin r → Ex V V₀) :
    (sumR f).peval c = ∑ i, (f i).peval c := by
  rw [sumR, peval_exSum c hc0, List.map_ofFn, List.sum_ofFn]
  rfl

theorem peval_sumK (c : ℕ → ℝ) (hc0 : c 0 = 0) {κ : Type} [Fintype κ] (f : κ → Ex V V₀) :
    (sumK f).peval c = ∑ k, (f k).peval c := by
  rw [sumK, peval_exSum c hc0, List.map_ofFn, List.sum_ofFn]
  exact Equiv.sum_comp (Fintype.equivFin κ).symm (fun k => (f k).peval c)

theorem ok_sumR {r : ℕ} (f : Fin r → Ex V V₀) (h : ∀ i, (f i).Ok) : (sumR f).Ok :=
  ok_exSum _ fun e he => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 he
    exact h i

theorem ok_sumK {κ : Type} [Fintype κ] (f : κ → Ex V V₀) (h : ∀ k, (f k).Ok) : (sumK f).Ok :=
  ok_exSum _ fun e he => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 he
    exact h _

theorem size_sumR_le {r : ℕ} (f : Fin r → Ex V V₀) (s : ℕ) (h : ∀ i, (f i).size ≤ s) :
    (sumR f).size ≤ r * (s + 1) := by
  have := size_exSum_le (List.ofFn f) s fun e he => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 he
    exact h i
  simpa [sumR] using this

theorem size_sumK_le {κ : Type} [Fintype κ] (f : κ → Ex V V₀) (s : ℕ)
    (h : ∀ k, (f k).size ≤ s) : (sumK f).size ≤ Fintype.card κ * (s + 1) := by
  have := size_exSum_le (List.ofFn fun j => f ((Fintype.equivFin κ).symm j)) s fun e he => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 he
    exact h _
  simpa [sumK] using this

/-- `|A - B|²` as an expression. -/
def sqDistE {κ : Type} [Fintype κ] (A B : κ → Ex V V₀) : Ex V V₀ :=
  sumK fun k => .sq (.sub (A k) (B k))

theorem peval_sqDistE (c : ℕ → ℝ) (hc0 : c 0 = 0) {κ : Type} [Fintype κ] (A B : κ → Ex V V₀)
    (p : V → ℝ) :
    eval p ((sqDistE A B).peval c) =
      sqDist (fun k => eval p ((A k).peval c)) (fun k => eval p ((B k).peval c)) := by
  rw [sqDistE, peval_sumK c hc0, map_sum]
  simp [Ex.peval, sqDist]

theorem ok_sqDistE {κ : Type} [Fintype κ] (A B : κ → Ex V V₀) (hA : ∀ k, (A k).Ok)
    (hB : ∀ k, (B k).Ok) : (sqDistE A B).Ok :=
  ok_sumK _ fun k => ⟨hA k, hB k⟩

theorem size_sqDistE_le {κ : Type} [Fintype κ] (A B : κ → Ex V V₀) (sA sB : ℕ)
    (hA : ∀ k, (A k).size ≤ sA) (hB : ∀ k, (B k).size ≤ sB) :
    (sqDistE A B).size ≤ Fintype.card κ * (sA + sB + 3) := by
  refine size_sumK_le _ _ fun k => ?_
  have := hA k
  have := hB k
  simp only [Ex.size]
  omega

end SecondAux

namespace SLData

variable {σ κ : Type} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ] {M : ℕ}

variable (D : SLData σ κ M) in
/-- The value of the sum of squares `Q` of the system of the assignment `β`. -/
def Qval {r : ℕ} (β : Fin r → Fin D.B) (ξ : σ ⊕ κ → ℝ) (T : ℝ) (ν : Unk κ M r → ℝ) : ℝ :=
  ∑ i, eval (pt (ξ ∘ Sum.inl) (Unk.om ν i) (Unk.nu ν i) (Unk.sv ν i)) (D.Q (β i)) +
    ∑ i, (Unk.sv ν i - Unk.th ν i ^ 2) ^ 2 +
    ∑ i, (sqDist (Unk.om ν i) D.w₀ + Unk.rh ν i ^ 2 - D.r₀ ^ 2) ^ 2 +
    (∑ i, Unk.be ν i ^ 2 - 1) ^ 2 + (T - D.cfgJ (Unk.cfg ν) (ξ ∘ Sum.inr)) ^ 2

/-- The bound on the length of the program of one assignment. -/
def progBound (D : SLData σ κ M) (r : ℕ) : ℕ :=
  r * (D.ℓmax + 2 * Nat.log 2 D.N) + 40 * (r + 1) ^ 2 * (Fintype.card κ + 1)

/-! ### The program of one assignment -/

section QProg

variable (D : SLData σ κ M)

/-- The constants: `0, 1, a, 2a, r₀², w₀`, then the constants of the margin programs. -/
def qC (m : ℕ) : ℝ :=
  if h : m < 5 then ![0, 1, D.a, 2 * D.a, D.r₀ ^ 2] ⟨m, h⟩
  else if h' : m - 5 < Fintype.card κ then D.w₀ ((Fintype.equivFin κ).symm ⟨m - 5, h'⟩)
  else if h'' : (Nat.unpair (m - (5 + Fintype.card κ))).1 < D.B then
    D.cst ⟨_, h''⟩ (Nat.unpair (m - (5 + Fintype.card κ))).2
  else 0

/-- The slots of the constants of the margin program of cell `b`. -/
def qcm (b : Fin D.B) (m : ℕ) : ℕ := 5 + Fintype.card κ + Nat.pair b m

theorem qC_qcm (b : Fin D.B) : D.qC ∘ D.qcm b = D.cst b := by
  funext m
  have h1 : ¬ (D.qcm b m < 5) := by unfold qcm; omega
  have h2 : ¬ (D.qcm b m - 5 < Fintype.card κ) := by unfold qcm; omega
  simp only [Function.comp_apply]
  rw [qC, dif_neg h1, dif_neg h2]
  have e : D.qcm b m - (5 + Fintype.card κ) = Nat.pair b m := by unfold qcm; omega
  simp only [e, Nat.unpair_pair]
  rw [dif_pos b.2]

theorem qC_zero : D.qC 0 = 0 := by simp [qC]
theorem qC_one : D.qC 1 = 1 := by simp [qC]
theorem qC_two : D.qC 2 = D.a := by simp [qC]
theorem qC_three : D.qC 3 = 2 * D.a := by simp [qC]
theorem qC_four : D.qC 4 = D.r₀ ^ 2 := by simp [qC]

theorem qC_w₀ (k : κ) : D.qC (5 + (Fintype.equivFin κ k : ℕ)) = D.w₀ k := by
  simp only [qC]
  rw [dif_neg (by omega), dif_pos (by have := (Fintype.equivFin κ k).2; omega)]
  congr 1
  rw [Equiv.symm_apply_eq]
  ext
  simp

variable {r : ℕ}

/-- The input renaming of the margin program of atom `i`. -/
def qρ (i : Fin r) :
    σ ⊕ κ ⊕ Option (Fin M) → Operand ((σ ⊕ κ) ⊕ Option (Unk κ M r)) ℕ
  | .inl x => .input (.inl (.inl x))
  | .inr (.inl k) => .input (.inr (some (i, .inl k)))
  | .inr (.inr none) => .input (.inr (some (i, .inr (.inr 3))))
  | .inr (.inr (some m)) => .input (.inr (some (i, .inr (.inl m))))

/-- Expression types. -/
abbrev QEx (σ κ : Type) (M r : ℕ) := Ex ((σ ⊕ κ) ⊕ Option (Unk κ M r)) (σ ⊕ κ ⊕ Option (Fin M))

/-- An unknown, as an expression. -/
def uE (i : Fin r) (j : κ ⊕ Fin M ⊕ Fin 4) : QEx σ κ M r := .leaf (.input (.inr (some (i, j))))

/-- `λ_i = β_i²`. -/
def lamE (i : Fin r) : QEx σ κ M r := .mul (uE i (.inr (.inr 2))) (uE i (.inr (.inr 2)))

/-- The mean `ω̄_k = ∑ λ_i ω_{i,k}`. -/
def omBarE (k : κ) : QEx σ κ M r := sumR fun i => .mul (lamE i) (uE i (.inl k))

/-- The objective `J`. -/
def JE : QEx σ κ M r :=
  .sub (.sub (sumR fun i => .mul (lamE i) (.pow (uE i (.inr (.inr 3))) D.N))
      (.mul (.leaf (.const 2)) (sumR fun i => .mul (lamE i) (sqDistE (fun k => uE i (.inl k))
        omBarE))))
    (.mul (.leaf (.const 3)) (sqDistE (fun k => .leaf (.input (.inl (.inr k)))) omBarE))

/-- The expression for `Q` of the assignment `β`. -/
def QE (β : Fin r → Fin D.B) : QEx σ κ M r :=
  .add (.add (.add (.add
    (sumR fun i => .prog (D.prog (β i)) (D.out (β i)) (qρ i) (D.qcm (β i)))
    (sumR fun i => .sq (.sub (uE i (.inr (.inr 3)))
      (.mul (uE i (.inr (.inr 0))) (uE i (.inr (.inr 0)))))))
    (sumR fun i => .sq (.sub (.add (sqDistE (fun k => uE i (.inl k))
        (fun k => .leaf (.const (5 + (Fintype.equivFin κ k : ℕ)))))
      (.mul (uE i (.inr (.inr 1))) (uE i (.inr (.inr 1))))) (.leaf (.const 4)))))
    (.sq (.sub (sumR fun i => lamE i) (.leaf (.const 1)))))
    (.sq (.sub (.leaf (.input (.inr none))) (JE D)))

theorem ok_QE (β : Fin r → Fin D.B) : (QE D β).Ok := by
  have hu : ∀ (i : Fin r) (j : κ ⊕ Fin M ⊕ Fin 4), (uE (σ := σ) (κ := κ) (M := M) i j).Ok :=
    fun _ _ => trivial
  have hlam : ∀ i : Fin r, (lamE (σ := σ) (κ := κ) (M := M) i).Ok := fun i => ⟨hu _ _, hu _ _⟩
  have hbar : ∀ k, (omBarE (σ := σ) (κ := κ) (M := M) (r := r) k).Ok :=
    fun k => ok_sumR _ fun i => ⟨hlam i, hu _ _⟩
  refine ⟨⟨⟨⟨ok_sumR _ fun i => ?_, ok_sumR _ fun i => ⟨hu _ _, hu _ _, hu _ _⟩⟩,
    ok_sumR _ fun i => ⟨⟨ok_sqDistE _ _ (fun k => hu _ _) (fun k => trivial),
      hu _ _, hu _ _⟩, trivial⟩⟩, ok_sumR _ hlam, trivial⟩, trivial, ?_⟩
  · intro v
    rcases v with x | k | _ | m <;> trivial
  · exact ⟨⟨ok_sumR _ fun i => ⟨hlam i, hu _ _⟩, trivial,
      ok_sumR _ fun i => ⟨hlam i, ok_sqDistE _ _ (fun k => hu _ _) hbar⟩⟩,
      trivial, ok_sqDistE _ _ (fun k => trivial) hbar⟩

theorem eval_QE (β : Fin r → Fin D.B) (ξ : σ ⊕ κ → ℝ) (T : ℝ) (ν : Unk κ M r → ℝ) :
    eval (valξsν ξ T ν) ((QE D β).peval D.qC) = D.Qval β ξ T ν := by
  set p := valξsν ξ T ν with hp
  have hc0 := qC_zero D
  have hu : ∀ (i : Fin r) (j : κ ⊕ Fin M ⊕ Fin 4),
      eval p ((uE (σ := σ) (κ := κ) (M := M) i j).peval D.qC) = ν (i, j) := by
    intro i j; simp [uE, Ex.peval, hp, valξsν, extendVal]
  have hc : ∀ m, eval p ((Ex.leaf (.const m) : QEx σ κ M r).peval D.qC) = D.qC m := by
    intro m; simp [Ex.peval]
  have hc' : ∀ m, eval p (BaurStrassen.ev D.qC ([] : List (MvPolynomial
      ((σ ⊕ κ) ⊕ Option (Unk κ M r)) ℝ)) (.const m)) = D.qC m := by
    intro m; simp
  have hx : ∀ k, eval p ((Ex.leaf (.input (.inl (.inr k))) : QEx σ κ M r).peval D.qC) =
      ξ (Sum.inr k) := by
    intro k; simp [Ex.peval, hp, valξsν]
  have hT : eval p ((Ex.leaf (.input (.inr none)) : QEx σ κ M r).peval D.qC) = T := by
    simp [Ex.peval, hp, valξsν, extendVal]
  have hlam : ∀ i : Fin r, eval p ((lamE (σ := σ) (κ := κ) (M := M) i).peval D.qC) =
      Unk.be ν i ^ 2 := by
    intro i; simp only [lamE, Ex.peval, map_mul, hu]; rw [sq]; rfl
  have hbar : ∀ k, eval p ((omBarE (σ := σ) (κ := κ) (M := M) (r := r) k).peval D.qC) =
      ∑ i, Unk.be ν i ^ 2 * Unk.om ν i k := by
    intro k
    rw [omBarE, peval_sumR _ hc0, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Ex.peval, map_mul, hlam, hu]
    rfl
  have hJ : eval p ((JE D (r := r)).peval D.qC) = D.cfgJ (Unk.cfg ν) (ξ ∘ Sum.inr) := by
    simp only [JE, Ex.peval, map_sub, map_mul, map_pow, peval_sumR _ hc0, map_sum]
    rw [peval_sqDistE _ hc0]
    simp only [hc', qC_two, qC_three, hx, hbar]
    have e1 : ∀ i : Fin r, eval p (Ex.peval D.qC (sqDistE (fun k => uE i (Sum.inl k))
        omBarE)) = sqDist (Unk.om ν i) (fun k => ∑ i, Unk.be ν i ^ 2 * Unk.om ν i k) := by
      intro i
      rw [peval_sqDistE _ hc0]
      simp only [hu, hbar]
      rfl
    simp only [e1, hlam, hu]
    unfold cfgJ envJ Unk.cfg
    simp only [Cfg.lam_mk, Cfg.om_mk, Cfg.s_mk]
    have e2 : (fun k => ξ (Sum.inr k)) = ξ ∘ Sum.inr := rfl
    rw [e2]
    unfold Unk.sv
    ring
  have hprog : ∀ i : Fin r, eval p (bind₁ (fun v => BaurStrassen.ev D.qC [] (qρ i v))
      (progOutput (D.prog (β i)) (D.qC ∘ D.qcm (β i)) (D.out (β i)))) =
      eval (pt (ξ ∘ Sum.inl) (Unk.om ν i) (Unk.nu ν i) (Unk.sv ν i)) (D.Q (β i)) := by
    intro i
    rw [eval_bind₁', qC_qcm]
    have e : (fun b => eval p (BaurStrassen.ev D.qC [] (qρ i b))) =
        pt (ξ ∘ Sum.inl) (Unk.om ν i) (Unk.nu ν i) (Unk.sv ν i) := by
      funext v
      rcases v with x | k | _ | m <;> simp [qρ, hp, valξsν, extendVal, pt, Unk.om, Unk.nu, Unk.sv]
    rw [e]
    rfl
  have hsd : ∀ i : Fin r, eval p ((sqDistE (fun k => uE i (Sum.inl k))
      (fun k => (Ex.leaf (.const (5 + (Fintype.equivFin κ k : ℕ))) : QEx σ κ M r))).peval
        D.qC) = sqDist (Unk.om ν i) D.w₀ := by
    intro i
    rw [peval_sqDistE _ hc0]
    simp only [hu, hc, qC_w₀]
    rfl
  simp only [QE, Ex.peval, map_add, map_sub, map_mul, map_pow, peval_sumR _ hc0, map_sum, hprog,
    hu, hlam, hJ, hc', qC_one, qC_four, hsd]
  have hT' : eval p (BaurStrassen.ev D.qC ([] : List (MvPolynomial
      ((σ ⊕ κ) ⊕ Option (Unk κ M r)) ℝ)) (.input (.inr none))) = T := hT
  rw [hT']
  unfold Qval
  have s1 : ∑ x : Fin r, (ν (x, Sum.inr (Sum.inr 3)) - ν (x, Sum.inr (Sum.inr 0)) *
      ν (x, Sum.inr (Sum.inr 0))) ^ 2 = ∑ i, (Unk.sv ν i - Unk.th ν i ^ 2) ^ 2 :=
    Finset.sum_congr rfl fun i _ => by unfold Unk.sv Unk.th; ring
  have s2 : ∑ x : Fin r, (sqDist (Unk.om ν x) D.w₀ + ν (x, Sum.inr (Sum.inr 1)) *
      ν (x, Sum.inr (Sum.inr 1)) - D.r₀ ^ 2) ^ 2 =
      ∑ i, (sqDist (Unk.om ν i) D.w₀ + Unk.rh ν i ^ 2 - D.r₀ ^ 2) ^ 2 :=
    Finset.sum_congr rfl fun i _ => by unfold Unk.rh; ring
  rw [s1, s2]

theorem size_QE_le (β : Fin r → Fin D.B) : (QE D β).size ≤ progBound D r := by
  set K := Fintype.card κ with hK
  set L := D.ℓmax with hL
  set P := powLen D.N with hP
  have hPl : P ≤ 2 * Nat.log 2 D.N := powLen_le _
  have hu : ∀ (i : Fin r) (j : κ ⊕ Fin M ⊕ Fin 4), (uE (σ := σ) (κ := κ) (M := M) i j).size = 0 :=
    fun _ _ => rfl
  have hlam : ∀ i : Fin r, (lamE (σ := σ) (κ := κ) (M := M) i).size = 1 := fun _ => rfl
  have hbar : ∀ k, (omBarE (σ := σ) (κ := κ) (M := M) (r := r) k).size ≤ r * (2 + 1) :=
    fun k => size_sumR_le _ 2 fun i => by simp [Ex.size, hlam, hu]
  have hsd1 : ∀ i : Fin r, (sqDistE (fun k => uE (σ := σ) (κ := κ) (M := M) i (Sum.inl k))
      omBarE).size ≤ K * (0 + r * (2 + 1) + 3) :=
    fun i => size_sqDistE_le _ _ 0 _ (fun k => (hu _ _).le) hbar
  have hP1 : (sumR fun i : Fin r => (Ex.mul (lamE i) (.pow (uE i (.inr (.inr 3))) D.N) :
      QEx σ κ M r)).size ≤ r * (P + 2 + 1) :=
    size_sumR_le _ _ fun i => by simp only [Ex.size, hlam, hu]; omega
  have hP2 : (sumR fun i : Fin r => (Ex.mul (lamE i) (sqDistE (fun k => uE i (Sum.inl k))
      omBarE) : QEx σ κ M r)).size ≤ r * (K * (0 + r * (2 + 1) + 3) + 2 + 1) :=
    size_sumR_le _ _ fun i => by
      have := hsd1 i
      simp only [Ex.size, hlam]
      omega
  have hP3 : (sqDistE (fun k => (Ex.leaf (.input (.inl (.inr k))) : QEx σ κ M r))
      omBarE).size ≤ K * (0 + r * (2 + 1) + 3) :=
    size_sqDistE_le _ _ 0 _ (fun k => le_refl _) hbar
  have hJ : (JE D (r := r)).size ≤ r * (P + 2 + 1) + r * (K * (0 + r * (2 + 1) + 3) + 2 + 1) +
      K * (0 + r * (2 + 1) + 3) + 4 := by
    simp only [JE, Ex.size]
    omega
  have hS1 : (sumR fun i : Fin r => (Ex.prog (D.prog (β i)) (D.out (β i)) (qρ i)
      (D.qcm (β i)) : QEx σ κ M r)).size ≤ r * (L + 1) :=
    size_sumR_le _ _ fun i => by
      simp only [Ex.size, hL, ℓmax]
      exact Finset.le_sup (f := fun b : Fin D.B => (D.prog b).length) (Finset.mem_univ _)
  have hS2 : (sumR fun i : Fin r => (Ex.sq (.sub (uE i (.inr (.inr 3)))
      (.mul (uE i (.inr (.inr 0))) (uE i (.inr (.inr 0))))) : QEx σ κ M r)).size ≤ r * (3 + 1) :=
    size_sumR_le _ _ fun i => by simp [Ex.size, hu]
  have hS3 : (sumR fun i : Fin r => (Ex.sq (.sub (.add (sqDistE (fun k => uE i (Sum.inl k))
        (fun k => .leaf (.const (5 + (Fintype.equivFin κ k : ℕ)))))
      (.mul (uE i (.inr (.inr 1))) (uE i (.inr (.inr 1))))) (.leaf (.const 4))) :
        QEx σ κ M r)).size ≤ r * (K * (0 + 0 + 3) + 4 + 1) :=
    size_sumR_le _ _ fun i => by
      have := size_sqDistE_le (fun k => uE (σ := σ) (κ := κ) (M := M) i (Sum.inl k))
        (fun k => (Ex.leaf (.const (5 + (Fintype.equivFin κ k : ℕ))) : QEx σ κ M r)) 0 0
        (fun k => (hu _ _).le) (fun k => le_refl _)
      simp only [Ex.size, hu]
      omega
  have hS4 : (Ex.sq (.sub (sumR fun i : Fin r => lamE i) (.leaf (.const 1))) :
      QEx σ κ M r).size ≤ r * (1 + 1) + 2 := by
    have := size_sumR_le (fun i : Fin r => (lamE i : QEx σ κ M r)) 1 fun i => (hlam i).le
    simp only [Ex.size]
    omega
  have htot : (QE D β).size ≤ r * (L + 1) + r * (3 + 1) + r * (K * (0 + 0 + 3) + 4 + 1) +
      (r * (1 + 1) + 2) + (r * (P + 2 + 1) + r * (K * (0 + r * (2 + 1) + 3) + 2 + 1) +
      K * (0 + r * (2 + 1) + 3) + 4) + 2 + 4 := by
    simp only [QE, Ex.size] at hS4 ⊢
    omega
  have hrP : r * P ≤ r * (2 * Nat.log 2 D.N) := Nat.mul_le_mul_left _ hPl
  unfold progBound
  rw [← hK, ← hL]
  have e1 : r * (L + 2 * Nat.log 2 D.N) = r * L + r * (2 * Nat.log 2 D.N) := by ring
  have e2 : r * (L + 1) + r * (3 + 1) + r * (K * (0 + 0 + 3) + 4 + 1) + (r * (1 + 1) + 2) +
      (r * (P + 2 + 1) + r * (K * (0 + r * (2 + 1) + 3) + 2 + 1) + K * (0 + r * (2 + 1) + 3) + 4)
      + 2 + 4 = r * L + r * P + (3 * (r * r * K) + 9 * (r * K) + 3 * K + 18 * r + 12) := by ring
  have e3 : 40 * (r + 1) ^ 2 * (K + 1) = 40 * (r * r * K) + 40 * (r * r) + 80 * (r * K) +
      80 * r + 40 * K + 40 := by ring
  rw [e1, e3]
  rw [e2] at htot
  have h4 : 0 ≤ r * r := Nat.zero_le _
  omega

end QProg

variable (D : SLData σ κ M) in
/-- **The program of one assignment**: a straight-line program for `Q`. -/
theorem exists_prog (r : ℕ) (β : Fin r → Fin D.B) :
    ∃ (prog : SLP ((σ ⊕ κ) ⊕ Option (Unk κ M r)) ℕ)
      (oQ : Operand ((σ ⊕ κ) ⊕ Option (Unk κ M r)) ℕ) (cQ : ℕ → ℝ),
      prog.length ≤ progBound D r ∧
      ∀ ξ T ν, eval (valξsν ξ T ν) (progOutput prog cQ oQ) = D.Qval β ξ T ν := by
  refine ⟨((QE D β).comp 0).1, ((QE D β).comp 0).2, D.qC, ?_, fun ξ T ν => ?_⟩
  · rw [Ex.comp_length]; exact size_QE_le D β
  · have := ((QE D β).comp_spec D.qC (qC_zero D) (qC_one D) (ok_QE D β) []).1
    simp only [List.length_nil, List.nil_append] at this
    rw [progOutput]
    change eval _ (BaurStrassen.ev D.qC (BaurStrassen.vals D.qC ((QE D β).comp 0).1)
      ((QE D β).comp 0).2) = _
    rw [this, eval_QE]

variable {D : SLData σ κ M} {f : MvPolynomial σ ℝ} {yc : κ}

theorem Good.Qval_nonneg (hG : D.Good f yc) {r : ℕ} (β : Fin r → Fin D.B) (ξ : σ ⊕ κ → ℝ)
    (T : ℝ) (ν : Unk κ M r → ℝ) : 0 ≤ D.Qval β ξ T ν := by
  unfold Qval
  have h1 : 0 ≤ ∑ i, eval (pt (ξ ∘ Sum.inl) (Unk.om ν i) (Unk.nu ν i) (Unk.sv ν i))
      (D.Q (β i)) := Finset.sum_nonneg fun i _ => hG.nonneg _ _
  have h2 : 0 ≤ ∑ i, (Unk.sv ν i - Unk.th ν i ^ 2) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have h3 : 0 ≤ ∑ i, (sqDist (Unk.om ν i) D.w₀ + Unk.rh ν i ^ 2 - D.r₀ ^ 2) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  positivity

theorem Good.Qval_eq_zero_iff (hG : D.Good f yc) {r : ℕ} (β : Fin r → Fin D.B)
    (ξ : σ ⊕ κ → ℝ) (T : ℝ) (ν : Unk κ M r → ℝ) :
    D.Qval β ξ T ν = 0 ↔
      (∀ i, eval (pt (ξ ∘ Sum.inl) (Unk.om ν i) (Unk.nu ν i) (Unk.sv ν i)) (D.Q (β i)) = 0)
      ∧ (∀ i, Unk.sv ν i = Unk.th ν i ^ 2)
      ∧ (∀ i, sqDist (Unk.om ν i) D.w₀ + Unk.rh ν i ^ 2 = D.r₀ ^ 2) ∧
      ∑ i, Unk.be ν i ^ 2 = 1 ∧ T = D.cfgJ (Unk.cfg ν) (ξ ∘ Sum.inr) := by
  unfold Qval
  set A := ∑ i, eval (pt (ξ ∘ Sum.inl) (Unk.om ν i) (Unk.nu ν i) (Unk.sv ν i)) (D.Q (β i))
  set A' := ∑ i, (Unk.sv ν i - Unk.th ν i ^ 2) ^ 2
  set B := ∑ i, (sqDist (Unk.om ν i) D.w₀ + Unk.rh ν i ^ 2 - D.r₀ ^ 2) ^ 2
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => hG.nonneg _ _
  have hA' : 0 ≤ A' := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hB : 0 ≤ B := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hC := sq_nonneg (∑ i, Unk.be ν i ^ 2 - 1)
  have hD := sq_nonneg (T - D.cfgJ (Unk.cfg ν) (ξ ∘ Sum.inr))
  constructor
  · intro h
    have hA0 : A = 0 := by linarith
    have hA'0 : A' = 0 := by linarith
    have hB0 : B = 0 := by linarith
    have hC0 : (∑ i, Unk.be ν i ^ 2 - 1) ^ 2 = 0 := by linarith
    have hD0 : (T - D.cfgJ (Unk.cfg ν) (ξ ∘ Sum.inr)) ^ 2 = 0 := by linarith
    have hC1 : ∑ i, Unk.be ν i ^ 2 - 1 = 0 := (pow_eq_zero_iff two_ne_zero).1 hC0
    have hD1 : T - D.cfgJ (Unk.cfg ν) (ξ ∘ Sum.inr) = 0 := (pow_eq_zero_iff two_ne_zero).1 hD0
    refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, by linarith, by linarith⟩
    · exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hG.nonneg _ _)).1 hA0 i
        (Finset.mem_univ _)
    · have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).1 hA'0 i
        (Finset.mem_univ _)
      have := pow_eq_zero_iff (n := 2) two_ne_zero |>.1 this
      linarith
    · have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).1 hB0 i
        (Finset.mem_univ _)
      have := pow_eq_zero_iff (n := 2) two_ne_zero |>.1 this
      linarith
  · rintro ⟨h1, h1', h2, h3, h4⟩
    have hA0 : A = 0 := Finset.sum_eq_zero fun i _ => h1 i
    have hA'0 : A' = 0 := Finset.sum_eq_zero fun i _ => by rw [h1' i]; ring
    have hB0 : B = 0 := Finset.sum_eq_zero fun i _ => by rw [h2 i]; ring
    rw [hA0, hA'0, hB0, h3, h4]
    ring

/-- A zero of the system of `β` gives an admissible configuration. -/
theorem Good.cfgOK_of_Qval (hG : D.Good f yc) {r : ℕ} (β : Fin r → Fin D.B)
    {ξ : σ ⊕ κ → ℝ} (hξ : ξ ∈ D.Kξ) {T : ℝ} {ν : Unk κ M r → ℝ} (h : D.Qval β ξ T ν = 0) :
    D.CfgOK (ξ ∘ Sum.inl) (Unk.cfg ν) ∧ T = D.cfgJ (Unk.cfg ν) (ξ ∘ Sum.inr) := by
  obtain ⟨h1, h1', h2, h3, h4⟩ := (hG.Qval_eq_zero_iff β ξ T ν).1 h
  refine ⟨⟨fun i => sq_nonneg _, h3, fun i => ⟨hξ, ?_, ?_, β i, h1 i⟩⟩, h4⟩
  · show sqDist (Unk.om ν i) D.w₀ ≤ D.r₀ ^ 2
    nlinarith [h2 i, sq_nonneg (Unk.rh ν i)]
  · show 0 ≤ Unk.sv ν i
    rw [h1' i]; exact sq_nonneg _

/-- An admissible configuration whose atoms lie in the cells `β` is encoded by unknowns. -/
theorem Good.exists_unk (hG : D.Good f yc) {r : ℕ} (β : Fin r → Fin D.B) {x : σ → ℝ}
    {z : Cfg κ M r → ℝ} (hz : D.CfgOK x z)
    (hβ : ∀ i, eval (pt x (Cfg.om z i) (Cfg.nu z i) (Cfg.s z i)) (D.Q (β i)) = 0)
    (ξ : σ ⊕ κ → ℝ) (hξx : ξ ∘ Sum.inl = x) :
    ∃ ν : Unk κ M r → ℝ, D.Qval β ξ (D.cfgJ z (ξ ∘ Sum.inr)) ν = 0 := by
  obtain ⟨hl, hsum, hat⟩ := hz
  set ν : Unk κ M r → ℝ := Unk.mk (Cfg.om z) (Cfg.nu z) (fun i => Real.sqrt (Cfg.s z i))
    (fun i => Real.sqrt (D.r₀ ^ 2 - sqDist (Cfg.om z i) D.w₀))
    (fun i => Real.sqrt (Cfg.lam z i)) (Cfg.s z) with hν
  have hom : Unk.om ν = Cfg.om z := rfl
  have hnu : Unk.nu ν = Cfg.nu z := rfl
  have hsv : Unk.sv ν = Cfg.s z := rfl
  have hth : ∀ i, Unk.th ν i ^ 2 = Cfg.s z i := fun i =>
    Real.sq_sqrt (hat i).2.2.1
  have hrh : ∀ i, Unk.rh ν i ^ 2 = D.r₀ ^ 2 - sqDist (Cfg.om z i) D.w₀ := fun i =>
    Real.sq_sqrt (by
      have : sqDist (Cfg.om z i) D.w₀ ≤ D.r₀ ^ 2 := (hat i).2.1
      linarith)
  have hbe : ∀ i, Unk.be ν i ^ 2 = Cfg.lam z i := fun i => Real.sq_sqrt (hl i)
  have hcfg : Unk.cfg ν = z := by
    funext u
    rcases u with i | ⟨i, k⟩ | i | ⟨i, m⟩
    · exact hbe i
    · rfl
    · rfl
    · rfl
  refine ⟨ν, (hG.Qval_eq_zero_iff β ξ _ ν).2 ⟨fun i => ?_, fun i => ?_, fun i => ?_, ?_, ?_⟩⟩
  · rw [hξx, hom, hnu, hsv]; exact hβ i
  · rw [hth, hsv]
  · rw [hrh, hom]; ring
  · simp only [hbe]; exact hsum
  · rw [hcfg]

/-- The size bound of Lemma 6.6. -/
theorem ev_size_arith (Cv Dg k M L lN n Lp U S : ℕ) (hS : S = Dg + k + M + L + lN + n + 2)
    (hLp : Lp ≤ (k + 3) * (L + 2 * lN) + 40 * (k + 3 + 1) ^ 2 * (k + 1))
    (hU : U = (k + 3) * (k + (M + 4))) :
    Cv * ((Dg + 1) ^ 3 * (Lp + 1) + (Dg + 1) ^ 2 * (U + 1) ^ 2 + (n + k)) ≤
      Cv * 1000 * S ^ 6 := by
  have hS1 : 1 ≤ S := by omega
  have hpow : ∀ a b, a ≤ b → S ^ a ≤ S ^ b := fun a b h => Nat.pow_le_pow_right hS1 h
  have h1 : k + 3 ≤ 2 * S := by omega
  have h2 : k + 3 + 1 ≤ 2 * S := by omega
  have h3 : k + 1 ≤ S := by omega
  have h4 : L + 2 * lN ≤ 2 * S := by omega
  have h5 : k + (M + 4) ≤ 2 * S := by omega
  have hLp' : Lp + 1 ≤ 165 * S ^ 3 := by
    have a1 : (k + 3) * (L + 2 * lN) ≤ (2 * S) * (2 * S) := Nat.mul_le_mul h1 h4
    have a2 : 40 * (k + 3 + 1) ^ 2 * (k + 1) ≤ 40 * (2 * S) ^ 2 * S :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2 2)) h3
    have a3 : S ^ 2 ≤ S ^ 3 := hpow 2 3 (by norm_num)
    have a4 : 1 ≤ S ^ 3 := Nat.one_le_pow _ _ hS1
    have e1 : (2 * S) * (2 * S) = 4 * S ^ 2 := by ring
    have e2 : 40 * (2 * S) ^ 2 * S = 160 * S ^ 3 := by ring
    omega
  have hU' : U + 1 ≤ 5 * S ^ 2 := by
    rw [hU]
    have a1 : (k + 3) * (k + (M + 4)) ≤ (2 * S) * (2 * S) := Nat.mul_le_mul h1 h5
    have a2 : 1 ≤ S ^ 2 := Nat.one_le_pow _ _ hS1
    have e1 : (2 * S) * (2 * S) = 4 * S ^ 2 := by ring
    omega
  have hD : Dg + 1 ≤ S := by omega
  have t1 : (Dg + 1) ^ 3 * (Lp + 1) ≤ 165 * S ^ 6 := by
    calc (Dg + 1) ^ 3 * (Lp + 1) ≤ S ^ 3 * (165 * S ^ 3) :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hD 3) hLp'
      _ = 165 * S ^ 6 := by ring
  have t2 : (Dg + 1) ^ 2 * (U + 1) ^ 2 ≤ 25 * S ^ 6 := by
    calc (Dg + 1) ^ 2 * (U + 1) ^ 2 ≤ S ^ 2 * (5 * S ^ 2) ^ 2 :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hD 2) (Nat.pow_le_pow_left hU' 2)
      _ = 25 * S ^ 6 := by ring
  have t3 : n + k ≤ S ^ 6 := (show n + k ≤ S by omega).trans (by simpa using hpow 1 6 (by norm_num))
  have t4 : (Dg + 1) ^ 3 * (Lp + 1) + (Dg + 1) ^ 2 * (U + 1) ^ 2 + (n + k) ≤ 1000 * S ^ 6 := by
    omega
  calc Cv * ((Dg + 1) ^ 3 * (Lp + 1) + (Dg + 1) ^ 2 * (U + 1) ^ 2 + (n + k))
      ≤ Cv * (1000 * S ^ 6) := Nat.mul_le_mul_left _ t4
    _ = Cv * 1000 * S ^ 6 := by ring

end SLData

/-- **Lemma 6.6.** -/
theorem SLData.env_value (hS : SAFacts) :
    ∃ C : ℕ, ∀ {σ κ : Type} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ] {M : ℕ}
      (D : SLData σ κ M) (f : MvPolynomial σ ℝ) (yc : κ), D.Good f yc → ∀ Dg : ℕ, 1 ≤ Dg →
      ∃ graphs : List (Shape (σ ⊕ κ) × ℕ),
        (∀ Γo ∈ graphs, Γo.1.length ≤ C * (Dg + Fintype.card κ + M + D.ℓmax +
          Nat.log 2 D.N + Fintype.card σ + 2) ^ 6) ∧
        ∃ O₀ ⊆ D.OK, D.OK ⊆ closure O₀ ∧ ∀ ξ₁ ∈ O₀, ContDiffAt ℝ Dg D.envξ ξ₁ ∧
          ∃ Γo ∈ graphs, ∀ η > 0, ∃ a : ℕ → ℝ,
            ((Γo.1.values a).getD Γo.2 0).totalDegree ≤ Dg ∧
            ∀ m, |((Γo.1.values a).getD Γo.2 0).coeff m - (taylorPoly Dg D.envξ ξ₁).coeff m| < η
  := by
  obtain ⟨Cv, hVF⟩ := value_functions hS
  refine ⟨Cv * 1000, ?_⟩
  intro σ κ _ _ _ _ M D f yc hG Dg hDg
  set r := Fintype.card κ + 3 with hr
  -- the programs of all assignments
  have hp := fun β : Fin r → Fin D.B => D.exists_prog r β
  choose prog oQ cQ hlen heval using hp
  have hg := fun β : Fin r → Fin D.B =>
    hVF (ι := σ ⊕ κ) (κ := Unk κ M r) (prog β) (oQ β) Dg hDg
  choose graphsβ hsize hprop using hg
  set graphs : List (Shape (σ ⊕ κ) × ℕ) :=
    (Finset.univ : Finset (Fin r → Fin D.B)).toList.flatMap graphsβ with hgraphs
  have hmemg : ∀ β, ∀ Γo ∈ graphsβ β, Γo ∈ graphs := fun β Γo h =>
    List.mem_flatMap.2 ⟨β, Finset.mem_toList.2 (Finset.mem_univ _), h⟩
  refine ⟨graphs, ?_, ?_⟩
  · -- the size bound
    intro Γo hΓo
    obtain ⟨β, -, hβ⟩ := List.mem_flatMap.1 hΓo
    refine (hsize β Γo hβ).trans ?_
    have hcard : Fintype.card (Unk κ M r) = (Fintype.card κ + 3) * (Fintype.card κ + (M + 4)) := by
      simp [Unk, Fintype.card_prod, Fintype.card_sum, hr]
    have hcard' : Fintype.card (σ ⊕ κ) = Fintype.card σ + Fintype.card κ := Fintype.card_sum
    rw [hcard']
    exact ev_size_arith Cv Dg (Fintype.card κ) M D.ℓmax (Nat.log 2 D.N) (Fintype.card σ)
      (prog β).length (Fintype.card (Unk κ M r)) _ rfl (hlen β) hcard
  -- the sets where an assignment attains `e`
  set S : (Fin r → Fin D.B) → Set (σ ⊕ κ → ℝ) :=
    fun β => {ξ | ξ ∈ D.OK ∧ ∃ ν, D.Qval β ξ (D.envξ ξ) ν = 0} with hSdef
  have hnonneg : ∀ β p, 0 ≤ eval p (progOutput (prog β) (cQ β) (oQ β)) := by
    intro β p
    have hp : p = valξsν (p ∘ Sum.inl) (p (Sum.inr none)) (p ∘ Sum.inr ∘ some) := by
      funext v
      rcases v with i | o
      · rfl
      · cases o <;> rfl
    rw [hp, heval]
    exact hG.Qval_nonneg β _ _ _
  have hgreat : ∀ β, ∀ ξ ∈ S β, IsGreatest {s | ∃ ν, eval (valξsν ξ s ν)
      (progOutput (prog β) (cQ β) (oQ β)) = 0} (D.envξ ξ) := by
    intro β ξ hξ
    obtain ⟨hξO, ν, hν⟩ := hξ
    refine ⟨⟨ν, by rw [heval]; exact hν⟩, ?_⟩
    rintro T ⟨ν', hν'⟩
    rw [heval] at hν'
    obtain ⟨hok, hT⟩ := hG.cfgOK_of_Qval β (OK_subset_Kξ hξO) hν'
    rw [hT]
    exact hG.cfgJ_le_env (OK_subset_Kξ hξO) _ hok
  have hcover : D.OK ⊆ ⋃ β ∈ (Finset.univ : Finset (Fin r → Fin D.B)), S β := by
    intro ξ hξ
    have hxK : ξ ∘ Sum.inl ∈ D.K := OK_subset_Kξ hξ
    obtain ⟨z, hz, hzJ⟩ := hG.exists_cfg hxK (ξ ∘ Sum.inr)
    have hb : ∀ i, ∃ b : Fin D.B,
        eval (pt (ξ ∘ Sum.inl) (Cfg.om z i) (Cfg.nu z i) (Cfg.s z i)) (D.Q b) = 0 :=
      fun i => (hz.2.2 i).2.2.2
    choose β hβ using hb
    obtain ⟨ν, hν⟩ := hG.exists_unk β hz hβ ξ rfl
    refine mem_iUnion₂.2 ⟨β, Finset.mem_univ _, hξ, ν, ?_⟩
    have : D.envξ ξ = D.cfgJ z (ξ ∘ Sum.inr) := hzJ.symm
    rw [this]; exact hν
  have hSsa : ∀ β, IsSA (S β) := by
    intro β
    set Qp := progOutput (prog β) (cQ β) (oQ β) with hQp
    have key : IsSA {ξ : σ ⊕ κ → ℝ | ξ ∈ D.OK ∧ ∃ t : ℝ, (ξ ∘ Sum.inl ∈ D.K ∧
        D.env (ξ ∘ Sum.inl) (ξ ∘ Sum.inr) = t) ∧ ∃ ν : Unk κ M r → ℝ,
          eval (valξsν ξ t ν) Qp = 0} := by
      refine FO.isSA_and D.isSA_OK (FO.isSA_exists_real (FO.isSA_and ?_ ?_))
      · exact hG.isSA_env_eq (Sum.inl ∘ Sum.inl) (Sum.inl ∘ Sum.inr) (Sum.inr ())
      · refine FO.isSA_exists_fun (FO.isSA_eq (FO.IsPolyFn.eval_comp (fun v => ?_) Qp)
          (FO.IsPolyFn.const 0))
        rcases v with i | o
        · exact FO.IsPolyFn.coord _
        · cases o with
          | none => exact FO.IsPolyFn.coord _
          | some u => exact FO.IsPolyFn.coord _
    convert key using 1
    ext ξ
    simp only [hSdef, mem_ofPred_eq]
    constructor
    · rintro ⟨hξ, ν, hν⟩
      exact ⟨hξ, _, ⟨OK_subset_Kξ hξ, rfl⟩, ν, by rw [heval]; exact hν⟩
    · rintro ⟨hξ, t, ⟨_, ht⟩, ν, hν⟩
      refine ⟨hξ, ν, ?_⟩
      rw [heval] at hν
      have : D.envξ ξ = t := ht
      rw [this]; exact hν
  -- Proposition 4.5 on the interiors
  have hA₀ : ∀ β, ∃ A₀ ⊆ interior (S β), A₀ ⊆ D.OK ∧ interior (S β) ⊆ closure A₀ ∧
      ∀ ξ₁ ∈ A₀, ContDiffAt ℝ Dg D.envξ ξ₁ ∧ ∃ Γo ∈ graphsβ β, ∀ η > 0, ∃ a : ℕ → ℝ,
        ((Γo.1.values a).getD Γo.2 0).totalDegree ≤ Dg ∧
        ∀ m, |((Γo.1.values a).getD Γo.2 0).coeff m - (taylorPoly Dg D.envξ ξ₁).coeff m| < η := by
    intro β
    rcases (interior (S β)).eq_empty_or_nonempty with he | hne
    · refine ⟨∅, empty_subset _, empty_subset _, ?_, fun ξ h => absurd h (notMem_empty _)⟩
      rw [he]; exact empty_subset _
    · obtain ⟨A₀, hA₀sub, -, hdense, hA₀⟩ := hprop β (cQ β) (interior (S β)) D.envξ
        isOpen_interior hne (hSsa β).interior (hnonneg β)
        (fun ξ hξ => hgreat β ξ (interior_subset hξ))
      exact ⟨A₀, hA₀sub, fun ξ hξ => (interior_subset (hA₀sub hξ)).1, hdense, hA₀⟩
  choose A₀ hA₀sub hA₀OK hA₀dense hA₀prop using hA₀
  refine ⟨⋃ β, A₀ β, iUnion_subset fun β => hA₀OK β, ?_, ?_⟩
  · intro ξ hξ
    rw [mem_closure_iff_nhds]
    intro t ht
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (inter_mem ht (isOpen_OK.mem_nhds hξ))
    obtain ⟨β, -, hβ⟩ := exists_interior_of_finite_cover hS Finset.univ S (fun β _ => hSsa β)
      Metric.isOpen_ball ⟨ξ, Metric.mem_ball_self hε⟩ (fun y hy => hcover (hball hy).2)
    obtain ⟨y, hy⟩ := hβ
    have hyA : y ∈ closure (A₀ β) := hA₀dense β (interior_mono inter_subset_left hy)
    obtain ⟨w, hw1, hw2⟩ := mem_closure_iff_nhds.1 hyA _ (isOpen_interior.mem_nhds hy)
    exact ⟨w, (hball (interior_subset hw1).2).1, mem_iUnion.2 ⟨β, hw2⟩⟩
  · intro ξ₁ hξ₁
    obtain ⟨β, hβ⟩ := mem_iUnion.1 hξ₁
    obtain ⟨hcd, Γo, hΓo, hΓoA⟩ := hA₀prop β ξ₁ hβ
    exact ⟨hcd, Γo, hmemg β Γo hΓo, hΓoA⟩

end ClassSep
