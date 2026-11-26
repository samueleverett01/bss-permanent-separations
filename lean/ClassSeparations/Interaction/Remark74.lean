import ClassSeparations.Interaction.Boolean

/-!
# Remark 7.4 (a): messages from a countable set

**Remark 7.4 (a).**  The proof of Lemma 7.2 applies when the prover's messages are taken from a
fixed countable set `𝓜 ⊆ ℝ` instead of `{0, 1}`, and the verifier's messages are still bits.
The generic point is chosen with coordinates algebraically independent over the field generated
by the constants of the verifier, the coefficients of `f` and the elements of `𝓜`; the tested
numerators on the paths followed at `w₀` (with the prover fixed) have coefficients in that
field, and their programs use the received messages as constants.

A verifier tree with messages from `𝓜` receives a real number at a receive node and appends it
to the list of computed values, so that later operations and tests can use it.

(Remark 7.4 (b), on "any purely discrete resource", is an informal remark and is not
formalized.)
-/

noncomputable section

open MvPolynomial Set Filter Topology Classical

namespace ClassSep

/-- A verifier tree whose receive nodes receive real numbers (appended to the computed values). -/
inductive MVTree (ι : Type) where
  | leaf (accept : Bool)
  | comp (op : TOp) (a b : TArg ι) (next : MVTree ι)
  | test (kind : TestKind) (v : TArg ι) (yes no : MVTree ι)
  | coin (c₀ c₁ : MVTree ι)
  | send (bit : Bool) (next : MVTree ι)
  | recv (next : MVTree ι)

namespace MVTree

variable {ι : Type}

/-- Depth. -/
def depth : MVTree ι → ℕ
  | .leaf _ => 1
  | .comp _ _ _ next => next.depth + 1
  | .test _ _ yes no => max yes.depth no.depth + 1
  | .coin c₀ c₁ => max c₀.depth c₁.depth + 1
  | .send _ next => next.depth + 1
  | .recv next => next.depth + 1

/-- A transcript: bits sent (`(true, 0/1)`) and real messages received (`(false, m)`). -/
abbrev MTranscript := List (Bool × ℝ)

/-- A prover: a real message for every input and transcript. -/
abbrev MProver (ι : Type) := (ι → ℝ) → MTranscript → ℝ

/-- Run the tree. -/
def runFrom (w : ι → ℝ) (P : MProver ι) (r : ℕ → Bool) :
    MVTree ι → List ℝ → MTranscript → ℕ → Option Bool
  | .leaf b, _, _, _ => some b
  | .comp op a b next, vals, s, j =>
      let x := a.eval w vals
      let y := b.eval w vals
      match op with
      | .add => next.runFrom w P r (vals ++ [x + y]) s j
      | .sub => next.runFrom w P r (vals ++ [x - y]) s j
      | .mul => next.runFrom w P r (vals ++ [x * y]) s j
      | .div => if y = 0 then none else next.runFrom w P r (vals ++ [x / y]) s j
  | .test k v yes no, vals, s, j =>
      if k.holds (v.eval w vals) then yes.runFrom w P r vals s j
      else no.runFrom w P r vals s j
  | .coin c₀ c₁, vals, s, j =>
      if r j then c₁.runFrom w P r vals s (j + 1) else c₀.runFrom w P r vals s (j + 1)
  | .send b next, vals, s, j =>
      next.runFrom w P r vals (s ++ [(true, if b then 1 else 0)]) j
  | .recv next, vals, s, j =>
      next.runFrom w P r (vals ++ [P w s]) (s ++ [(false, P w s)]) j

/-- Acceptance probability. -/
def accProb (V : MVTree ι) (w : ι → ℝ) (P : MProver ι) : ℝ :=
  ((Finset.univ.filter fun r : Fin V.depth → Bool =>
      V.runFrom w P (fun j => if h : j < V.depth then r ⟨j, h⟩ else false) [] [] 0 =
        some true).card : ℝ) / 2 ^ V.depth

/-- The protocol with messages from `𝓜` decides `L` on `W`. -/
def DecidesOn (V : MVTree ι) (𝓜 : Set ℝ) (L W : Set (ι → ℝ)) : Prop :=
  ∀ w ∈ W, (w ∈ L → ∃ P : MProver ι, (∀ s, P w s ∈ 𝓜) ∧ 2 / 3 ≤ V.accProb w P) ∧
    (w ∉ L → ∀ P : MProver ι, (∀ s, P w s ∈ 𝓜) → V.accProb w P ≤ 1 / 3)

end MVTree

/-! ### Auxiliary constructions for Remark 7.4 (a)

As in the proof of Lemma 7.2 (`ClassSep.BIP`), we follow the paths symbolically.  A received
message `m` is represented by the fraction `m/1`, a constant.  The tested numerators over all
paths and all messages from `𝓜` form a countable set (`MBIP.tnums`), each of them has a
straight-line program with at most `4t` operations (whose constants include the received
messages), and the outcome is locally constant near `w₀` if none of them is a nonzero
polynomial vanishing at `w₀`, for a prover whose replies lie in `𝓜` and depend only on the
transcript.
-/

namespace MBIP

open BIP

variable {ι : Type}

/-- The tested numerators on all paths of `T`, for all messages from `𝓜`. -/
def tnums (𝓜 : Set ℝ) : MVTree ι → List (Frac ι) → Set (MvPolynomial ι ℝ)
  | .leaf _, _ => ∅
  | .comp op a b next, fr =>
      insert (argF fr b).1 (tnums 𝓜 next (fr ++ [compF op (argF fr a) (argF fr b)]))
  | .test _ v yes no, fr => insert (argF fr v).1 (tnums 𝓜 yes fr ∪ tnums 𝓜 no fr)
  | .coin c₀ c₁, fr => tnums 𝓜 c₀ fr ∪ tnums 𝓜 c₁ fr
  | .send _ next, fr => tnums 𝓜 next fr
  | .recv next, fr => ⋃ m ∈ 𝓜, tnums 𝓜 next (fr ++ [(C m, 1)])

theorem tnums_countable (𝓜 : Set ℝ) (h𝓜 : 𝓜.Countable) (T : MVTree ι) :
    ∀ fr, (tnums 𝓜 T fr).Countable := by
  induction T with
  | leaf b => intro fr; simp [tnums]
  | comp op a b next ih => intro fr; exact (ih _).insert _
  | test k v yes no ihy ihn => intro fr; exact ((ihy fr).union (ihn fr)).insert _
  | coin c₀ c₁ ih₀ ih₁ => intro fr; exact (ih₀ fr).union (ih₁ fr)
  | send b next ih => intro fr; exact ih fr
  | recv next ih => intro fr; exact h𝓜.biUnion fun m _ => ih _

/-- **Tested numerators have short programs.** -/
theorem tnums_slp (𝓜 : Set ℝ) (T : MVTree ι) : ∀ (fr : List (Frac ι)) (P : SLP ι ℝ),
    (∀ p ∈ fr, P.Computes p.1 ∧ P.Computes p.2) →
    ∀ q ∈ tnums 𝓜 T fr, HasSLP q (P.length + 4 * T.depth) := by
  induction T with
  | leaf b => intro fr P _ q hq; simp [tnums] at hq
  | comp op a b next ih =>
    intro fr P hP q hq
    simp only [tnums, Set.mem_insert_iff] at hq
    rcases hq with rfl | hq
    · exact ⟨P, by omega, (argF_computes hP b).1⟩
    · obtain ⟨P', hl, hi, h1, h2⟩ :=
        comp_step (argF_computes hP a) (argF_computes hP b) op
      have hP' : ∀ p ∈ fr ++ [compF op (argF fr a) (argF fr b)],
          P'.Computes p.1 ∧ P'.Computes p.2 := by
        intro p hp
        rcases List.mem_append.1 hp with hp | hp
        · exact ⟨hi _ (hP p hp).1, hi _ (hP p hp).2⟩
        · rw [List.mem_singleton] at hp; subst hp; exact ⟨h1, h2⟩
      refine hasSLP_mono (ih _ P' hP' q hq) ?_
      simp only [MVTree.depth]
      omega
  | test k v yes no ihy ihn =>
    intro fr P hP q hq
    simp only [tnums, Set.mem_insert_iff, Set.mem_union] at hq
    rcases hq with rfl | hq | hq
    · exact ⟨P, by omega, (argF_computes hP v).1⟩
    · refine hasSLP_mono (ihy fr P hP q hq) ?_
      simp only [MVTree.depth]; omega
    · refine hasSLP_mono (ihn fr P hP q hq) ?_
      simp only [MVTree.depth]; omega
  | coin c₀ c₁ ih₀ ih₁ =>
    intro fr P hP q hq
    simp only [tnums, Set.mem_union] at hq
    rcases hq with hq | hq
    · refine hasSLP_mono (ih₀ fr P hP q hq) ?_
      simp only [MVTree.depth]; omega
    · refine hasSLP_mono (ih₁ fr P hP q hq) ?_
      simp only [MVTree.depth]; omega
  | send b next ih =>
    intro fr P hP q hq
    refine hasSLP_mono (ih fr P hP q hq) ?_
    simp only [MVTree.depth]; omega
  | recv next ih =>
    intro fr P hP q hq
    simp only [tnums, Set.mem_iUnion] at hq
    obtain ⟨m, -, hq⟩ := hq
    -- the received message is a constant of the program: no new instruction
    have hP' : ∀ p ∈ fr ++ [((C m : MvPolynomial ι ℝ), (1 : MvPolynomial ι ℝ))],
        P.Computes p.1 ∧ P.Computes p.2 := by
      intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · exact hP p hp
      · rw [List.mem_singleton] at hp; subst hp; exact ⟨computes_C P m, computes_one P⟩
    refine hasSLP_mono (ih _ P hP' q hq) ?_
    simp only [MVTree.depth]; omega

/-- The run only queries the prover at the input itself. -/
theorem runFrom_congr (w : ι → ℝ) (P P' : MVTree.MProver ι) (hP : ∀ s, P w s = P' w s)
    (r : ℕ → Bool) (T : MVTree ι) :
    ∀ vals s j, T.runFrom w P r vals s j = T.runFrom w P' r vals s j := by
  induction T with
  | leaf b => intro vals s j; rfl
  | comp op a b next ih => intro vals s j; cases op <;> simp [MVTree.runFrom, ih]
  | test k v yes no ihy ihn => intro vals s j; simp [MVTree.runFrom, ihy, ihn]
  | coin c₀ c₁ ih₀ ih₁ => intro vals s j; simp [MVTree.runFrom, ih₀, ih₁]
  | send b next ih => intro vals s j; simp [MVTree.runFrom, ih]
  | recv next ih => intro vals s j; simp [MVTree.runFrom, ih, hP]

/-- **Local constancy.**  If no tested numerator is a nonzero polynomial vanishing at `w₀`,
then for a prover whose replies lie in `𝓜` and depend only on the transcript, the outcome is
constant near `w₀`. -/
theorem loc (𝓜 : Set ℝ) (w₀ : ι → ℝ) (Q : MVTree.MTranscript → ℝ) (hQ : ∀ s, Q s ∈ 𝓜)
    (r : ℕ → Bool) (T : MVTree ι) :
    ∀ (fr : List (Frac ι)) (s : MVTree.MTranscript) (j : ℕ), (∀ p ∈ fr, eval w₀ p.2 ≠ 0) →
    (∀ q ∈ tnums 𝓜 T fr, q ≠ 0 → eval w₀ q ≠ 0) →
    ∀ᶠ w in 𝓝 w₀, T.runFrom w (fun _ => Q) r (valF w fr) s j =
      T.runFrom w₀ (fun _ => Q) r (valF w₀ fr) s j := by
  induction T with
  | leaf b => intro fr s j _ _; exact Eventually.of_forall fun w => rfl
  | comp op a b next ih =>
    intro fr s j hden htn
    set A := argF fr a with hAdef
    set B := argF fr b with hBdef
    have hA : eval w₀ A.2 ≠ 0 := argF_den hden a
    have hB : eval w₀ B.2 ≠ 0 := argF_den hden b
    have hB1 : B.1 ≠ 0 → eval w₀ B.1 ≠ 0 := htn _ (Set.mem_insert _ _)
    have htn' : ∀ q ∈ tnums 𝓜 next (fr ++ [compF op A B]), q ≠ 0 → eval w₀ q ≠ 0 :=
      fun q hq => htn q (Set.mem_insert_of_mem _ hq)
    have hA' : ∀ᶠ w in 𝓝 w₀, eval w A.2 ≠ 0 := (continuous_eval _).continuousAt.eventually_ne hA
    have hB' : ∀ᶠ w in 𝓝 w₀, eval w B.2 ≠ 0 := (continuous_eval _).continuousAt.eventually_ne hB
    have ha : ∀ w, a.eval w (valF w fr) = eval w A.1 / eval w A.2 := fun w => argF_eval w fr a
    have hb : ∀ w, b.eval w (valF w fr) = eval w B.1 / eval w B.2 := fun w => argF_eval w fr b
    have key : eval w₀ (compF op A B).2 ≠ 0 → ∀ v : (ι → ℝ) → ℝ,
        (∀ᶠ w in 𝓝 w₀, v w = eval w (compF op A B).1 / eval w (compF op A B).2) →
        ∀ᶠ w in 𝓝 w₀, next.runFrom w (fun _ => Q) r (valF w fr ++ [v w]) s j =
          next.runFrom w₀ (fun _ => Q) r (valF w₀ fr ++ [v w₀]) s j := by
      intro hN v hv
      have hden' : ∀ p ∈ fr ++ [compF op A B], eval w₀ p.2 ≠ 0 := by
        intro p hp
        rcases List.mem_append.1 hp with hp | hp
        · exact hden p hp
        · rw [List.mem_singleton] at hp; subst hp; exact hN
      have h1 := ih (fr ++ [compF op A B]) s j hden' htn'
      have h0 := hv.self_of_nhds
      filter_upwards [h1, hv] with w hw hvw
      rw [hvw, h0, ← valF_snoc, ← valF_snoc]
      exact hw
    cases op with
    | add =>
      simp only [MVTree.runFrom]
      refine key (by simp [compF, hA, hB]) _ ?_
      filter_upwards [hA', hB'] with w hwA hwB
      rw [ha, hb, div_add_div _ _ hwA hwB]
      simp [compF]
    | sub =>
      simp only [MVTree.runFrom]
      refine key (by simp [compF, hA, hB]) _ ?_
      filter_upwards [hA', hB'] with w hwA hwB
      rw [ha, hb, div_sub_div _ _ hwA hwB]
      simp [compF]
    | mul =>
      simp only [MVTree.runFrom]
      refine key (by simp [compF, hA, hB]) _ (Eventually.of_forall fun w => ?_)
      rw [ha, hb, div_mul_div_comm]
      simp [compF]
    | div =>
      simp only [MVTree.runFrom]
      by_cases hz : B.1 = 0
      · refine Eventually.of_forall fun w => ?_
        rw [hb, hb, hz]
        simp
      have hB1w : eval w₀ B.1 ≠ 0 := hB1 hz
      have hy0 : eval w₀ B.1 / eval w₀ B.2 ≠ 0 := div_ne_zero hB1w hB
      have hy : ∀ᶠ w in 𝓝 w₀, eval w B.1 / eval w B.2 ≠ 0 := by
        filter_upwards [(continuous_eval B.1).continuousAt.eventually_ne hB1w, hB'] with w h1 h2
        exact div_ne_zero h1 h2
      have hk := key (by simp [compF, hA, hB1w]) (fun w => a.eval w (valF w fr) /
        b.eval w (valF w fr)) (Eventually.of_forall fun w => by
          simp only [ha, hb, div_div_div_eq]; simp [compF])
      filter_upwards [hk, hy] with w hw hyw
      rw [hb, hb, ite_eq_right hyw, ite_eq_right hy0]
      rw [hb, hb] at hw
      exact hw
  | test k v yes no ihy ihn =>
    intro fr s j hden htn
    have hV2 : eval w₀ (argF fr v).2 ≠ 0 := argF_den hden v
    have hV1 : (argF fr v).1 ≠ 0 → eval w₀ (argF fr v).1 ≠ 0 := htn _ (Set.mem_insert _ _)
    have hT := test_loc w₀ k (argF fr v) hV2 hV1
    simp only [MVTree.runFrom, argF_eval]
    by_cases hk : k.holds (eval w₀ (argF fr v).1 / eval w₀ (argF fr v).2)
    · have := ihy fr s j hden fun q hq => htn q (by simp [tnums, hq])
      filter_upwards [hT, this] with w hw hw'
      rw [ite_eq_left (hw.2 hk), ite_eq_left hk]
      exact hw'
    · have := ihn fr s j hden fun q hq => htn q (by simp [tnums, hq])
      filter_upwards [hT, this] with w hw hw'
      rw [ite_eq_right (fun h => hk (hw.1 h)), ite_eq_right hk]
      exact hw'
  | coin c₀ c₁ ih₀ ih₁ =>
    intro fr s j hden htn
    simp only [MVTree.runFrom]
    by_cases hr : r j
    · simp only [hr, ite_true]
      exact ih₁ fr s (j + 1) hden fun q hq => htn q (by simp [tnums, hq])
    · simp only [hr]
      exact ih₀ fr s (j + 1) hden fun q hq => htn q (by simp [tnums, hq])
  | send b next ih =>
    intro fr s j hden htn
    exact ih fr _ j hden htn
  | recv next ih =>
    intro fr s j hden htn
    simp only [MVTree.runFrom]
    -- the received message `Q s` is represented by the constant fraction `Q s / 1`
    have hden' : ∀ p ∈ fr ++ [((C (Q s) : MvPolynomial ι ℝ), (1 : MvPolynomial ι ℝ))],
        eval w₀ p.2 ≠ 0 := by
      intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · exact hden p hp
      · rw [List.mem_singleton] at hp; subst hp; simp
    have htn' : ∀ q ∈ tnums 𝓜 next (fr ++ [(C (Q s), 1)]), q ≠ 0 → eval w₀ q ≠ 0 :=
      fun q hq => htn q (Set.mem_biUnion (hQ s) hq)
    have h1 := ih _ (s ++ [(false, Q s)]) j hden' htn'
    have hv : ∀ w : ι → ℝ, valF w (fr ++ [((C (Q s) : MvPolynomial ι ℝ), 1)]) =
        valF w fr ++ [Q s] := fun w => by simp [valF]
    simp only [hv] at h1
    exact h1

end MBIP

/-- **Remark 7.4 (a).** -/
theorem boundary_test_countable {σ : Type} [Fintype σ] [DecidableEq σ] (f : MvPolynomial σ ℝ)
    (𝓜 : Set ℝ) (h𝓜 : 𝓜.Countable) (U : Set (σ → ℝ)) (hU : IsOpen U) (hUne : U.Nonempty)
    (W : Set (Option σ → ℝ)) (hW : IsOpen W) (hUW : ∀ x ∈ U, inpXY x (eval x f) ∈ W)
    (V : MVTree (Option σ)) (t : ℕ) (hV : V.depth ≤ t)
    (hdec : V.DecidesOn 𝓜 {w | w none = eval (w ∘ some) f} W ∨
      V.DecidesOn 𝓜 {w | w none ≤ eval (w ∘ some) f} W) :
    ∃ G : MvPolynomial (Option σ) ℝ, G ≠ 0 ∧ HasSLP ((X none - rename some f) * G) (4 * t) := by
  classical
  -- the tested numerators on all paths, for all messages from `𝓜`: a countable set
  set S := MBIP.tnums 𝓜 V [] with hSdef
  have hS : S.Countable := MBIP.tnums_countable 𝓜 h𝓜 V []
  -- *A generic point* (Baire): `x ∈ U` at which `q(X, f(X))` does not vanish unless it is zero
  obtain ⟨x, hxU, hx⟩ : ∃ x ∈ U, ∀ q ∈ S, BIP.substY f q ≠ 0 → eval x (BIP.substY f q) ≠ 0 := by
    have hD : Dense (⋂ q ∈ S,
        {x : σ → ℝ | BIP.substY f q ≠ 0 → eval x (BIP.substY f q) ≠ 0}) := by
      refine dense_biInter_of_isOpen (fun q _ => ?_) hS (fun q _ => ?_)
      · by_cases h : BIP.substY f q = 0
        · simp [h]
        · simp only [ne_eq, h, not_false_eq_true, forall_const]
          exact isOpen_ne_fun (continuous_eval _) continuous_const
      · by_cases h : BIP.substY f q = 0
        · simp [h]
        · simp only [ne_eq, h, not_false_eq_true, forall_const]
          rw [dense_iff_inter_open]
          intro O hO hOne
          obtain ⟨y, hyO, hy⟩ := BIP.exists_eval_ne_zero _ h hO hOne
          exact ⟨y, hyO, hy⟩
    obtain ⟨x, hxU, hxD⟩ := hD.inter_open_nonempty U hU hUne
    exact ⟨x, hxU, fun q hq => Set.mem_iInter₂.1 hxD q hq⟩
  set w₀ := inpXY x (eval x f) with hw₀def
  have hw₀W : w₀ ∈ W := hUW x hxU
  by_cases hbad : ∃ q ∈ S, q ≠ 0 ∧ eval w₀ q = 0
  · -- *Division by the graph equation*
    obtain ⟨q, hqS, hq0, hqw⟩ := hbad
    have hgq : BIP.substY f q = 0 := by
      by_contra h
      exact hx q hqS h (by rw [BIP.eval_substY]; exact hqw)
    obtain ⟨G, hG⟩ := BIP.dvd_of_substY f q hgq
    refine ⟨G, ?_, ?_⟩
    · rintro rfl
      rw [mul_zero] at hG
      exact hq0 hG
    · rw [← hG]
      have := MBIP.tnums_slp 𝓜 V [] [] (by simp) q hqS
      exact BIP.hasSLP_mono this (by simp; omega)
  · -- *Local constancy* gives a contradiction
    exfalso
    push Not at hbad
    -- a good prover at `w₀`
    have hw₀L1 : w₀ ∈ {w : Option σ → ℝ | w none = eval (w ∘ some) f} := rfl
    have hw₀L2 : w₀ ∈ {w : Option σ → ℝ | w none ≤ eval (w ∘ some) f} :=
      show eval x f ≤ eval x f from le_refl _
    obtain ⟨P, hP𝓜, hP⟩ : ∃ P : MVTree.MProver (Option σ), (∀ s, P w₀ s ∈ 𝓜) ∧
        2 / 3 ≤ V.accProb w₀ P := by
      rcases hdec with h | h
      · exact (h w₀ hw₀W).1 hw₀L1
      · exact (h w₀ hw₀W).1 hw₀L2
    set Q := P w₀ with hQdef
    -- the prover `P'(w, s) = P(w₀, s)` has the same acceptance probability near `w₀`
    have hloc : ∀ᶠ w in 𝓝 w₀, V.accProb w (fun _ => Q) = V.accProb w₀ P := by
      have hr : ∀ rr : Fin V.depth → Bool, ∀ᶠ w in 𝓝 w₀,
          (V.runFrom w (fun _ => Q) (fun j => if h : j < V.depth then rr ⟨j, h⟩ else false)
              [] [] 0 = some true ↔
            V.runFrom w₀ P (fun j => if h : j < V.depth then rr ⟨j, h⟩ else false)
              [] [] 0 = some true) := by
        intro rr
        have := MBIP.loc 𝓜 w₀ Q hP𝓜 (fun j => if h : j < V.depth then rr ⟨j, h⟩ else false)
          V [] [] 0 (by simp) hbad
        filter_upwards [this] with w hw
        rw [MBIP.runFrom_congr w₀ P (fun _ => Q) (fun s => rfl)]
        exact iff_of_eq (congrArg (· = some true) hw)
      filter_upwards [Filter.eventually_all.2 hr] with w hw
      unfold MVTree.accProb
      rw [Finset.filter_congr fun rr _ => hw rr]
    -- move up from `w₀` along `Y`
    have hcont : Continuous fun ε : ℝ => inpXY x (eval x f + ε) := by
      refine continuous_pi fun o => ?_
      cases o with
      | none => exact continuous_const.add continuous_id
      | some i => exact continuous_const
    have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), inpXY x (eval x f + ε) ∈ W ∧
        V.accProb (inpXY x (eval x f + ε)) (fun _ => Q) = V.accProb w₀ P := by
      have ht := hcont.tendsto 0
      rw [add_zero] at ht
      have hWev : ∀ᶠ w in 𝓝 w₀, w ∈ W := hW.mem_nhds hw₀W
      exact ht.eventually (hWev.and hloc)
    obtain ⟨ε, hε, hεW, hεacc⟩ := hev.exists_gt
    have hn1 : inpXY x (eval x f + ε) ∉ {w : Option σ → ℝ | w none = eval (w ∘ some) f} := by
      change ¬ (eval x f + ε = eval x f)
      intro h; linarith
    have hn2 : inpXY x (eval x f + ε) ∉ {w : Option σ → ℝ | w none ≤ eval (w ∘ some) f} := by
      change ¬ (eval x f + ε ≤ eval x f)
      intro h; linarith
    have hle : V.accProb (inpXY x (eval x f + ε)) (fun _ => Q) ≤ 1 / 3 := by
      rcases hdec with h | h
      · exact (h _ hεW).2 hn1 _ fun s => hP𝓜 s
      · exact (h _ hεW).2 hn2 _ fun s => hP𝓜 s
    linarith

end ClassSep
