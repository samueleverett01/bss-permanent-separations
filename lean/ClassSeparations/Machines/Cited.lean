import ClassSeparations.Machines.Interactive
import ClassSeparations.Machines.Complex

/-!
# Known inclusions between classes, cited by the paper

* `NP_ℝ ⊆ PAR_ℝ`, `coNP_ℝ ⊆ PAR_ℝ`, `Σ₂^ℝ ⊆ PAR_ℝ`: quantifier elimination in parallel
  polynomial time for a bounded number of quantifier blocks [Ren92, Cuc93, BCSS98] (§2.1).
* `NP_ℂ ⊆ PAR_ℂ`, `coNP_ℂ ⊆ PAR_ℂ` [BCSS98] (proof of Corollary 5.5 (c)).
* `BIP_ℝ ⊆ PAR_ℝ` in the model with multiplication [IdR99] (§7.1).
* `PAR_ℝ ⊊ IP_ℝ` [BM16, Theorem 14] and `AM_ℝ[poly] = IP_ℝ` (public coins suffice)
  [BM16, Proposition 6] (§7.2).

These are hypotheses of the class-level theorems.
-/

namespace ClassSep

/-- The cited relations between complexity classes. -/
structure ClassFacts : Prop where
  np_sub_par : NP_R ⊆ PAR_R
  conp_sub_par : coNP_R ⊆ PAR_R
  sigma2_sub_par : Sigma2_R ⊆ PAR_R
  npc_sub_parc : NP_C ⊆ PAR_C
  conpc_sub_parc : coNP_C ⊆ PAR_C
  bip_sub_par : BIP_R ⊆ PAR_R
  par_ssubset_ip : PAR_R ⊂ IP_R
  am_poly_eq_ip : AM_R_poly = IP_R

end ClassSep
