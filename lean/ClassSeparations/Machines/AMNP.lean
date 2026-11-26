import ClassSeparations.Machines.Cited
import ClassSeparations.Machines.NPtoAM
import ClassSeparations.Machines.AMtoNP

/-!
# Constant-round Arthur–Merlin proofs equal `NP_ℝ` (Theorem 7.6)

**Theorem 7.6.**  For every constant `c ≥ 1`, `AM_ℝ[c] = NP_ℝ`.  Hence
`AM_ℝ[O(1)] = NP_ℝ ⊊ AM_ℝ[poly] = IP_ℝ`.

The inclusion `AM_ℝ[c] ⊆ NP_ℝ` fixes the coins (Lemma 7.7): polynomially many coin strings per
round suffice for all inputs at once; they form Boolean advice of polynomial length, which a
machine stores in one real constant and reads by doubling and comparing [CKKLW95, Koi94]; the
certificate is a strategy tree, checked by the tree `T` of (12).  The converse inclusion lets
Merlin send the certificate in the first round.  The strict inclusion and the last equality are
the cited results of Baartse and Meer (`ClassFacts`).

The two inclusions are `AMNPAux.am_sub_np` (`Machines/AMtoNP.lean`, with the machine
construction `AMNPAux.gather_count` of `Machines/Gather.lean`) and `AMNPAux.np_sub_am`
(`Machines/NPtoAM.lean`); running a machine as a subroutine is `AMNPAux.sim_spec`
(`Machines/Simulate.lean`).
-/

namespace ClassSep

/-- **Theorem 7.6**, first part. -/
theorem am_eq_np (hC : CountingBound) (c : ℕ) (hc : 1 ≤ c) : AM_R c = NP_R :=
  Set.Subset.antisymm (AMNPAux.am_sub_np hC c hc) (AMNPAux.np_sub_am c hc)

/-- **Theorem 7.6**, second part: `AM_ℝ[O(1)] = NP_ℝ ⊊ AM_ℝ[poly] = IP_ℝ`. -/
theorem am_const_eq_np (hC : CountingBound) (hF : ClassFacts) :
    AM_R_const = NP_R ∧ NP_R ⊂ AM_R_poly ∧ AM_R_poly = IP_R := by
  have h1 : AM_R_const = NP_R := by
    apply Set.Subset.antisymm
    · intro L hL
      simp only [AM_R_const, Set.mem_iUnion, Set.mem_ofPred_eq] at hL
      obtain ⟨c, hc, hL⟩ := hL
      rwa [am_eq_np hC c hc] at hL
    · intro L hL
      simp only [AM_R_const, Set.mem_iUnion, Set.mem_ofPred_eq]
      exact ⟨1, le_rfl, by rwa [am_eq_np hC 1 le_rfl]⟩
  refine ⟨h1, ?_, hF.am_poly_eq_ip⟩
  rw [hF.am_poly_eq_ip]
  exact ssubset_of_subset_of_ssubset hF.np_sub_par hF.par_ssubset_ip

end ClassSep
