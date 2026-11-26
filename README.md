# NP_R ≠ PAR_R: the permanent has no short real certificates

LaTeX source of the paper

> **NP_ℝ ≠ PAR_ℝ, Σ₂^ℝ ≠ PAR_ℝ and BIP_ℝ ≠ PAR_ℝ: the permanent has no short real certificates**

> [!IMPORTANT]
> **This paper is mostly AI-written.** The proofs were found, and most of the text was drafted, by AI models in conversation with the human author. The results have not been peer reviewed and should be read with that in mind.

## How these results came about

The results in this repository came out of a conversation between Samuel Everett and Claude Fable 5.2, an AI model developed by Anthropic. Claude Fable 5.2 found the proofs together with Samuel Everett and wrote most of the paper.

That conversation started from initial ideas in a separate, earlier conversation with ChatGPT Astra 6.2, which proved $\mathrm{BIP}_{\mathbb R}^{\times}\subsetneq\mathrm{PAR}_{\mathbb R}^{\times}$ (Boolean-message interactive proofs against parallel polynomial time, in the real model with multiplication). The conversation with Claude Fable 5.2 extended that starting point to the further separations listed below.

A Lean formalization of the results is currently underway.

## Results

In the Blum–Shub–Smale model, the graph `{Y = per_m(X)}` of the real permanent lies in parallel polynomial time PAR_ℝ and outside each of

- NP_ℝ and coNP_ℝ,
- the second existential level Σ₂ of the real polynomial hierarchy,
- constant-round Arthur–Merlin proofs with real messages,
- interactive proofs with Boolean messages (BIP_ℝ),

and over the complex numbers outside NP_ℂ and coNP_ℂ. Each of these classes is therefore strictly contained in PAR_ℝ (respectively PAR_ℂ).

The separations use the superpolynomial lower bound for the border complexity of the permanent (Theorem 2.3 in the paper, cited from the Anthropic manuscript "VP ≠ VNP over every field" and its Lean formalization). Two families of results use no lower bound:

- the graph theorems: a polynomial of polynomial degree whose graph has short existential, universal or ∃∀ real certificates has small border complexity;
- AM_ℝ[O(1)] = NP_ℝ ⊊ AM_ℝ[poly].

## Layout

| File | Content |
| --- | --- |
| `main.tex` | Title, abstract, section includes |
| `macros.tex` | Notation |
| `refs.bib` | Bibliography |
| `sections/intro.tex` | Introduction and statements of the main theorems |
| `sections/prelim.tex` | Model, classes, border complexity, semialgebraic tools, cells |
| `sections/core.tex` | Derivatives of semialgebraic families, Newton iteration as a circuit, the local theorem |
| `sections/certificates.tex` | Existential certificates: graph theorem, thresholds, value functions |
| `sections/universal.tex` | Universal certificates and the complex field |
| `sections/second-level.tex` | An existential and a universal block |
| `sections/interaction.tex` | Boolean messages and constant-round Arthur–Merlin proofs |
| `sections/open.tex` | Open problems |

## Building

```bash
latexmk -pdf main.tex
```

## Status

The proofs have not been peer reviewed. The paper is mostly AI-written (see above). A Lean formalization is in progress.

The bibliographic data in `refs.bib` were checked against publisher and Crossref records. The numbered results cited from the Anthropic manuscript, Bürgisser (2004, 2026), Baartse–Meer, Baur–Strassen and Cucker et al. were confirmed in the sources. Still to be confirmed against the full texts: the attributions to Cucker (1992, 1993), Koiran (1994), Blum–Cucker–Shub–Smale, and the numbering in Basu–Pollack–Roy, which follows the second edition (2006).
