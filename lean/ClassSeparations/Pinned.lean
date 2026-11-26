import ClassSeparations.Main

/-!
# Pinned statements

This file restates, verbatim and independently of the files where they are proved, the
statements of the main results, and checks that the proved theorems have exactly these types.
It guards against accidental changes of statements during the formalization.
-/

noncomputable section

open MvPolynomial Set Filter Topology

namespace ClassSep.Pinned

open ClassSep

/-- Lemma 2.6. -/
example : ∀ {ι : Type} (T : Tree ι) (t : ℕ) (_ : T.depth ≤ t) (S : Set (Option Bool)),
    ∃ L : List (Cell ι), (∀ B ∈ L, B.Bounded t T.consts) ∧
      {w | T.run w ∈ S} = ⋃ B ∈ L, B.carrier :=
  fun T t hT S => cells T t hT S

/-- Theorem 4.2. -/
example (hS : SAFacts) :
    ∃ C : ℕ, ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (d t k : ℕ) (f : MvPolynomial σ ℝ),
      1 ≤ d → f.totalDegree ≤ d →
      ∀ U : Set (σ → ℝ), IsOpen U → U.Nonempty →
      ∀ T : Tree (σ ⊕ Unit ⊕ Fin k), T.depth ≤ t →
      (∀ x ∈ U, ∀ y : ℝ, (∃ z, T.Accepts (inp3 x y z)) ↔ y = eval x f) →
      BorderLE f
        (C * ((d + 1) ^ 3 * t + (d + 1) ^ 2 * (min k (2 * t) + 2) ^ 2 + Fintype.card σ)) :=
  graph_theorem hS

/-- Theorem 5.1. -/
example (hS : SAFacts) :
    ∃ C : ℕ, ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (d t k : ℕ) (f : MvPolynomial σ ℝ),
      1 ≤ d → f.totalDegree ≤ d →
      ∀ U : Set (σ → ℝ), IsOpen U → U.Nonempty →
      ∀ (T : Tree (σ ⊕ Unit ⊕ Fin k)) (M : Set (Option Bool)), T.depth ≤ t →
      (∀ x ∈ U, ∀ z, T.run (inp3 x (eval x f) z) ∉ M) →
      (∀ x ∈ U, ∃ ρ > 0, ∀ y, eval x f < y → y < eval x f + ρ →
        ∃ z, T.run (inp3 x y z) ∈ M) →
      BorderLE f (C * (d + 1) ^ 6 * ((t + 1) ^ 2 + Fintype.card σ)) :=
  onesided hS

/-- Theorem 6.1. -/
example (hS : SAFacts) (hQE : EffectiveQE) :
    ∃ C e : ℕ, ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (d t k l : ℕ) (f : MvPolynomial σ ℝ),
      1 ≤ d → f.totalDegree ≤ d →
      ∀ U : Set (σ → ℝ), IsOpen U → U.Nonempty →
      ∀ T : Tree (σ ⊕ Unit ⊕ Fin k ⊕ Fin l), T.depth ≤ t →
      (∀ x ∈ U, ∀ y : ℝ, (∃ z, ∀ u, T.Accepts (inp4 x y z u)) ↔ y = eval x f) →
      BorderLE f (C * (t + k + l + d + Fintype.card σ + 1) ^ e) :=
  second_level hS hQE

/-- Corollary 4.7. -/
example (hS : SAFacts) (hLB : PermLowerBound) (r : PerRel)
    (hr : r = .eq ∨ r = .le ∨ r = .ge) (t k : ℕ → ℕ)
    (T : ∀ m, Tree ((Fin m × Fin m) ⊕ Unit ⊕ Fin (k m)))
    (hT : ∀ m, (T m).depth ≤ t m) (hdec : ∀ m, ExDecides (T m) (perLang r m)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ m : ℕ in atTop, (2 : ℝ) ^ (c * Real.logb 2 m ^ (4 / 3 : ℝ)) ≤ t m :=
  cor_np hS hLB r hr t k T hT hdec

/-- Theorem 7.3 (tree part). -/
example (hLB : PermLowerBound) (hB : BurgisserThm) (t : ℕ → ℕ)
    (V : ∀ m, VTree (Option (Fin m × Fin m))) (hV : ∀ m, (V m).depth ≤ t m)
    (hdec : ∀ m, (V m).DecidesOn {w | w none = eval (w ∘ some) (per m)} univ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ m : ℕ in atTop, (2 : ℝ) ^ (c * Real.logb 2 m ^ (4 / 3 : ℝ)) ≤ t m :=
  bip_lower hLB hB t V hV hdec

/-- Theorem 7.8. -/
example (hS : SAFacts) (hLB : PermLowerBound) (hC : CountingBound)
    (Pr : ∀ m, AMProtocol (Option (Fin m × Fin m))) (t : ℕ → ℕ) (B e : ℕ)
    (hpoly : ∀ m, (Pr m).ρ + (Pr m).μ + t m ≤ B * (m + 1) ^ e) (ht : ∀ m, (Pr m).V.depth ≤ t m)
    (hdec : ∀ m, (Pr m).Decides (perGraph m)) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ᶠ m : ℕ in atTop, c' * Real.log (Real.log m) ≤ (Pr m).c :=
  am_rounds hS hLB hC Pr t B e hpoly ht hdec

/-- Theorem A. -/
example (hS : SAFacts) (hLB : PermLowerBound) (hF : ClassFacts) :
    (∀ r : PerRel, (r = .eq ∨ r = .le ∨ r = .ge) → permLang r ∈ PAR_R ∧ permLang r ∉ NP_R) ∧
      NP_R ⊂ PAR_R :=
  theorem_A hS hLB hF

/-- Theorem B. -/
example (hS : SAFacts) (hLB : PermLowerBound) (hQE : EffectiveQE) (hF : ClassFacts) :
    (∀ r : PerRel, (r = .eq ∨ r = .le ∨ r = .ge) →
      permLang r ∉ coNP_R ∧ permLang r ∉ Sigma2_R) ∧
    coNP_R ⊂ PAR_R ∧ Sigma2_R ⊂ PAR_R :=
  theorem_B hS hLB hQE hF

/-- Theorem C. -/
example (hS : SAFacts) (hLB : PermLowerBound) (hF : ClassFacts) :
    cpermLang ∈ PAR_C ∧ cpermLang ∉ NP_C ∧ cpermLang ∉ coNP_C ∧
      NP_C ⊂ PAR_C ∧ coNP_C ⊂ PAR_C :=
  theorem_C hS hLB hF

/-- Theorem D. -/
example (hLB : PermLowerBound) (hB : BurgisserThm) (hF : ClassFacts) :
    permLang .eq ∉ BIP_R ∧ BIP_R ⊂ PAR_R :=
  theorem_D hLB hB hF

/-- Theorem E. -/
example (hS : SAFacts) (hLB : PermLowerBound) (hC : CountingBound) (hF : ClassFacts) :
    (∀ c, 1 ≤ c → AM_R c = NP_R) ∧ AM_R_const = NP_R ∧ NP_R ⊂ AM_R_poly ∧
      AM_R_poly = IP_R ∧ permLang .eq ∉ AM_R_const :=
  theorem_E hS hLB hC hF

end ClassSep.Pinned
