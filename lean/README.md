# Lean formalization of "NP_ℝ ≠ PAR_ℝ, Σ₂^ℝ ≠ PAR_ℝ, and BIP_ℝ ≠ PAR_ℝ"

Lean 4 (v4.36.0) + Mathlib (v4.36.0).  About 36 000 lines in `ClassSeparations/` (67 files).

## Building

```bash
cd lean
lake exe cache get   # download prebuilt Mathlib
lake build
```

(Inside the Claude Code sandbox the toolchain lives in `lean/.elan`; run `source env.sh` first.)

To see what a theorem depends on, use e.g. `#print axioms ClassSep.theorem_A`: every result
of the paper depends only on `propext`, `Classical.choice` and `Quot.sound`.

## What is proved, and from what

Every numbered result of the paper (Lemma 2.6 through Theorem 7.8, Remarks 4.3, 5.4, 7.4(a)
and Theorems A–F) is stated and proved in Lean.  The results that the paper **cites** from the
literature are not proved; they are explicit hypotheses (arguments of type `Prop`) of the
theorems that use them — nothing is added as an `axiom`:

| Hypothesis | Paper | File |
| --- | --- | --- |
| `SAFacts` | facts (S2)–(S8) on semialgebraic sets (BCR98, vdD98) | `SA/Facts.lean` |
| `PermLowerBound` | Theorem 2.3 [Cla26]: border complexity of `per_m` exceeds `2^{c (log m)^{4/3}}` | `Cited.lean` |
| `BurgisserThm` | Theorem 2.5 [Bur04] | `Cited.lean` |
| `EffectiveQE` | effective quantifier elimination [BPR06, Thm 14.16] (Lemma 6.3(d)) | `Second/Cited.lean` |
| `CountingBound` | the counting bound (C) of Lemma 7.7 [BPR06] | `Interaction/Cited.lean` |
| `ClassFacts` | known inclusions: `NP_ℝ, coNP_ℝ, Σ₂^ℝ ⊆ PAR_ℝ`, `NP_ℂ, coNP_ℂ ⊆ PAR_ℂ`, `BIP_ℝ ⊆ PAR_ℝ` [IdR99], `PAR_ℝ ⊊ IP_ℝ`, `AM_ℝ[poly] = IP_ℝ` [BM16] | `Machines/Cited.lean` |

Fact (S1) is not a hypothesis: semialgebraic sets are *defined* as the sets definable by
first-order formulas over `(ℝ, +, ×, <)` (`SA/Formula.lean`), so (S1) holds by construction.
The theorem of Baur and Strassen (Theorem 2.4), Hoeffding's inequality (from Mathlib), Ryser's
formula, and the unrolling of machines into trees are proved, not assumed.

All the theorems below are conditional on the hypotheses they take; in particular all lower
bounds for the permanent are conditional on `PermLowerBound` (Theorem 2.3 of the paper, cited
there from the manuscript [Cla26]).

## Correspondence with the paper

| Paper | Lean | File |
| --- | --- | --- |
| Def. 2.1 (trees) | `Tree`, `Tree.run`, `Tree.Accepts`, `Tree.depth` | `Basic/Tree.lean` |
| Def. 2.2 (border complexity) | `IsApprox`, `BorderLE`, `borderComplexity` | `Basic/Circuits.lean` |
| Thm. 2.4 (Baur–Strassen) | `baur_strassen` (uniform), `baur_strassen'` | `Core/BaurStrassen.lean` |
| Lemma 2.6 (cells) | `cells`, `cells_length` | `Basic/Cells.lean` |
| (S1)–(S8) consequences | `SA/Lemmas.lean`, `SA/Dim.lean` | |
| Lemma 3.1, Cor. 3.2 | `derivatives`, `derivatives_cor` | `Core/Derivatives.lean` |
| Lemma 3.3 | `closure_lemma`, `borderLE_of_approx` | `Core/Closure.lean` |
| Lemma 3.4 | `newton_circuit`, `newtonPoly_eq_taylorPoly`, `tendsto_coeff_newtonPoly` | `Core/Newton.lean` |
| Thm. 3.5, Lemmas 3.6, 3.7 | `local_theorem`, `minimisers`, `genericCentre` | `Core/Local.lean` |
| Lemma 4.1 | `isolate` | `Cert/Isolate.lean` |
| Thm. 4.2, Rem. 4.3, Thm. 4.4 | `graph_theorem`, `graph_theorem_vec`, `threshold_theorem_le/ge` | `Cert/Graph.lean` |
| Prop. 4.5 | `value_functions` | `Cert/Value.lean` |
| Lemma 4.6 | `ryser`; `permLang_mem_PAR`, `cpermLang_mem_PAR` | `Cert/Permanent.lean`, `Machines/Perm.lean` |
| Cor. 4.7 | `cor_np` (trees); `theorem_A` (classes) | `Cert/Permanent.lean`, `Main.lean` |
| Thm. 5.1, Lemma 5.2 | `onesided`, `Margin.margin_cert_iff`, `OnesidedAux.lemma_5_2_b/c` | `Universal/Onesided.lean`, `Universal/Margin.lean` |
| Thm. 5.3, Rem. 5.4 | `complex_field`, `complex_coeff` | `Universal/Complex.lean` |
| Cor. 5.5 | `cor_conp_universal`, `cor_conp_strict`, `cor_conp_complex`; `theorem_B/C` | `Universal/Separations.lean`, `Main.lean` |
| Thm. 6.1 | `second_level` (= `sl_setup` + `sl_conclude_proof`) | `Second/Main.lean` |
| Lemma 6.2 | `SetupAux.lemma_6_2` | `Second/Goodz.lean` |
| Lemma 6.3 | `SetupAux.lemma_6_3_a/b/c` (`Second/Flatten.lean`), `lemma_6_3_d` (`Second/FlattenD.lean`), `exponent_bound` (`Second/Exponent.lean`) | |
| Lemma 6.4 | `envelope_props` | `Second/Envelope.lean` |
| Lemma 6.5 | `SLData.Good.env_continuity` | `Second/Continuity.lean` |
| Lemma 6.6 | `SLData.env_value` | `Second/EnvValue.lean` |
| Lemma 6.7 | `SLData.Good.tilt` | `Second/Tilt.lean` |
| Cor. 6.8 | `cor_second`; `theorem_B` | `Second/Main.lean`, `Main.lean` |
| Def. 7.1, Lemma 7.2, Thm. 7.3 | `VTree`, `boundary_test`, `bip_lower`; `theorem_D` | `Interaction/Boolean.lean`, `Main.lean` |
| Rem. 7.4 (a) | `boundary_test_countable` | `Interaction/Remark74.lean` |
| Def. 7.5, Lemma 7.7, (12), Thm. 7.8 | `AMProtocol`, `fixing_coins`, `strategy_tree`, `am_rounds` | `Interaction/AM.lean` |
| Thm. 7.6 | `am_eq_np`, `am_const_eq_np` | `Machines/AMNP.lean` |
| Theorems A–F | `theorem_A` … `theorem_F` | `Main.lean` |
| §1–2 classes | `P_R`, `NP_R`, `coNP_R`, `Sigma2_R`, `PAR_R`, `NP_C`, `PAR_C`, `BIP_R`, `IP_R`, `AM_R` | `Machines/*.lean` |

`ClassSeparations/Pinned.lean` restates the main statements verbatim and checks them against
the proved theorems.

## Conventions and deviations

* `ℝⁿ` is `ι → ℝ` for a finite type `ι` (sup norm; balls are sup-norm balls unless stated).
  Squared Euclidean distances entering polynomial programs are sums of squares (`sqDist`).
* A tree's run returns an outcome `Option Bool`: `some b` = leaf `b`, `none` = division by zero
  (rejection).  Marked leaves are a set of marked outcomes.  Tests may be applied to any operand.
* Derivatives are Mathlib's `fderiv`/`iteratedFDeriv`; Taylor polynomials are
  `taylorPoly D g ξ₁` (`Analysis/Taylor.lean`).  Corollary 3.2 is stated with iterated Fréchet
  derivatives (whose components are the partial derivatives `∂^α`).
* Programs and circuits have constant *slots*; a program/circuit *graph* is the object with slots.
* Machines are real random-access machines (index registers address real registers), which
  simulate BSS machines with polynomial overhead.  `PAR_ℝ` is defined by P-uniform families of
  algebraic circuits with sign gates of polynomial depth, uniformity being witnessed by a
  machine that outputs the description of a gate from the binary digits of its index.
* Some proofs differ from the paper's: Lemma 4.1 is proved by induction on the certificate
  coordinates via cell decomposition (no Nash manifolds or tangent spaces); Lemma 3.4(b) and the
  implicit-function steps of §5.5 and §6.6 use little-o estimates instead of the analytic
  implicit function theorem; in Lemma 6.4 the hypothesis `r₀ ≥ 0` is explicit.
* Remark 7.4 (b) ("any purely discrete resource") is informal and is not formalized.
