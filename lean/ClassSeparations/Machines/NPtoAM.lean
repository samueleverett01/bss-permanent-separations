import ClassSeparations.Machines.Simulate
import ClassSeparations.Machines.Interactive

/-!
# `NP_ℝ ⊆ AM_ℝ[c]` (the easy half of Theorem 7.6)

Merlin sends the certificate in the first round; there are no coins (`ρ = 0`) and the messages
of the later rounds are ignored.  The verifier moves the first message into place: it computes
the certificate length `q(n) = I 2 / c`, sets the block sizes to `[n, q(n)]`, clears the
registers of the later messages, and runs the `NP_ℝ` machine (`simStmt`).
-/

set_option autoImplicit false

noncomputable section

open Classical

namespace ClassSep

namespace AMNPAux

open Prog

/-! ## Registers holding a concatenation -/

theorem vecReg_append {a b : ℕ} (u : Fin a → ℝ) (v : Fin b → ℝ) (i : ℕ) :
    vecReg (Fin.append u v) i = if i < a then vecReg u i else vecReg v (i - a) := by
  unfold vecReg
  by_cases h : i < a
  · rw [if_pos h, dif_pos (by omega), dif_pos h]
    exact Fin.append_left u v ⟨i, h⟩
  · rw [if_neg h]
    by_cases h' : i < a + b
    · rw [dif_pos h', dif_pos (by omega)]
      have := Fin.append_right u v ⟨i - a, by omega⟩
      rw [← this]
      congr 1
      ext
      simp only [Fin.coe_natAdd]
      omega
    · rw [dif_neg h', dif_neg (by omega)]

theorem vecReg_of_le {a : ℕ} (u : Fin a → ℝ) {i : ℕ} (h : a ≤ i) : vecReg u i = 0 := by
  simp [vecReg, show ¬ i < a by omega]

theorem vecReg_of_lt {a : ℕ} (u : Fin a → ℝ) {i : ℕ} (h : i < a) : vecReg u i = u ⟨i, h⟩ := by
  simp [vecReg, h]

/-- The registers of the input `(x, r, z)` of a verifier without coins: `x`, then the messages,
round after round. -/
theorem vecReg_amVec_noCoins {n c μ : ℕ} (x : Fin n → ℝ) (r : Fin c → Fin 0 → Bool)
    (z : Fin c → Fin μ → ℝ) (hc : 1 ≤ c) (i : ℕ) (hi : i < n + μ) :
    vecReg (amVec x r z) i = vecReg (Fin.append x (z ⟨0, by omega⟩)) i := by
  unfold amVec
  rw [vecReg_append, vecReg_append, vecReg_append]
  by_cases h : i < n
  · simp [h, show i < n + c * 0 by omega]
  · simp only [h, Nat.mul_zero, Nat.add_zero, if_false]
    have h1 : i - n < c * μ := by
      have : μ ≤ c * μ := Nat.le_mul_of_pos_left μ (by omega)
      omega
    rw [vecReg_of_lt _ h1, vecReg_of_lt _ (show i - n < μ by omega)]
    congr 1
    · ext
      simp [Nat.div_eq_of_lt (show i - n < μ by omega)]
    · ext
      simp [Nat.mod_eq_of_lt (show i - n < μ by omega)]

/-! ## The verifier -/

/-- The verifier of the protocol for an `NP_ℝ` machine `M` with `c` rounds.  Registers:
`b = idxBd M + 3` (zero), `b+1, b+2, b+3` (interpreter), `b+4` (`q(n)`), `b+5, b+7, b+8, b+9`
(scratch), `b+6` (`n + q(n)`). -/
def npAMStmt (M : Machine) (c : ℕ) : Stmt :=
  Stmt.seqs [divIdx (idxBd M + 3 + 4) (idxBd M + 3 + 5) 2 c, loadIdx 1 (idxBd M + 3 + 4),
    loadIdx (idxBd M + 3 + 6) 0,
    addIdx (idxBd M + 3 + 6) (idxBd M + 3 + 4) (idxBd M + 3 + 7) (idxBd M + 3),
    fillRange (idxBd M + 3 + 6) 2 0 (idxBd M + 3 + 8) (idxBd M + 3 + 9) (idxBd M + 3),
    clearIdx 2 (idxBd M + 3),
    simStmt M (idxBd M + 3 + 1) (idxBd M + 3 + 2) (idxBd M + 3 + 3) (idxBd M + 3),
    .ite (.idxEq (idxBd M + 3 + 3) (idxBd M + 3)) (.halt false) (.halt true)]

/-- The running time of the verifier. -/
def npAMTime (M : Machine) (c n μ T : ℕ) : ℕ :=
  (μ * (c + 3) + 1) + ((3 * μ + 1) + ((3 * n + 1) + ((7 * μ + 2) +
    ((6 * (n + μ) + 11 * (c * μ) + 4) + ((3 * (c * μ) + 1) + (simTime M T + (0 + 2)))))))

theorem npAM_spec (M : Machine) {c : ℕ} (hc : 1 ≤ c) {n μ T : ℕ} (x : Fin n → ℝ)
    (r : Fin c → Fin 0 → Bool) (z : Fin c → Fin μ → ℝ) {o : Option Bool}
    (hrun : M.run T (initConfig [n, μ] (vecReg (Fin.append x (z ⟨0, by omega⟩)))) = some o) :
    Halts (npAMStmt M c) (St.init [n, c * 0, c * μ] (vecReg (amVec x r z)))
      (fun _ res => res = some (decide (o = some true))) (npAMTime M c n μ T) := by
  set b := idxBd M + 3 with hbdef
  set R₀ := vecReg (amVec x r z) with hR₀
  set I₀ : ℕ → ℕ := fun k => [n, c * 0, c * μ].getD k 0 with hI₀
  have hI₀b : ∀ k, 3 ≤ k → I₀ k = 0 := by
    intro k hk
    simp only [hI₀]
    rw [List.getD_eq_default _ _ (by simp; omega)]
  have hb3 : 3 ≤ b := by omega
  -- step 1: `I (b+4) := q(n)`
  set I₁ := Function.update (Function.update I₀ (b + 5) (c * μ)) (b + 4) μ with hI₁
  have h1 : Runs (divIdx (b + 4) (b + 5) 2 c) ⟨R₀, I₀⟩ (· = ⟨R₀, I₁⟩) (μ * (c + 3) + 1) :=
    divIdx_spec hc (by omega) (by omega) (by omega) (hI₀b _ (by omega)) (hI₀b _ (by omega))
      (by simp [hI₀])
  -- step 2: `I 1 := q(n)`
  set I₂ := Function.update I₁ 1 μ with hI₂
  have h2 : Runs (loadIdx 1 (b + 4)) ⟨R₀, I₁⟩ (· = ⟨R₀, I₂⟩) (3 * μ + 1) := by
    have := loadIdx_spec (st := ⟨R₀, I₁⟩) (k := 1) (a := b + 4) (by omega)
      (by simp [hI₁, hI₀, Function.update_of_ne (show (1 : ℕ) ≠ b + 4 by omega),
        Function.update_of_ne (show (1 : ℕ) ≠ b + 5 by omega)])
    simpa [hI₂, hI₁] using this
  -- step 3: `I (b+6) := n`
  set I₃ := Function.update I₂ (b + 6) n with hI₃
  have h3 : Runs (loadIdx (b + 6) 0) ⟨R₀, I₂⟩ (· = ⟨R₀, I₃⟩) (3 * n + 1) := by
    have := loadIdx_spec (st := ⟨R₀, I₂⟩) (k := b + 6) (a := 0) (by omega)
      (by simp [hI₂, hI₁, Function.update_of_ne (show b + 6 ≠ 1 by omega),
        Function.update_of_ne (show b + 6 ≠ b + 4 by omega),
        Function.update_of_ne (show b + 6 ≠ b + 5 by omega), hI₀b (b + 6) (by omega)])
    have e : I₂ 0 = n := by
      simp [hI₂, hI₁, Function.update_of_ne (show (0 : ℕ) ≠ 1 by omega),
        Function.update_of_ne (show (0 : ℕ) ≠ b + 4 by omega),
        Function.update_of_ne (show (0 : ℕ) ≠ b + 5 by omega), hI₀]
    simpa [hI₃, e] using this
  -- step 4: `I (b+6) := n + q(n)`
  set I₄ := Function.update I₃ (b + 6) (n + μ) with hI₄
  have h4 : Runs (addIdx (b + 6) (b + 4) (b + 7) b) ⟨R₀, I₃⟩ (· = ⟨R₀, I₄⟩) (7 * μ + 2) := by
    have e7 : I₃ (b + 7) = 0 := by
      simp [hI₃, hI₂, hI₁, Function.update_apply, hI₀b (b + 7) (by omega)]
    have eb : I₃ b = 0 := by
      simp only [hI₃, hI₂, hI₁, Function.update_apply]
      split_ifs <;> first | omega | exact hI₀b b hb3
    have e4 : I₃ (b + 4) = μ := by simp [hI₃, hI₂, hI₁, Function.update_apply]
    have e6 : I₃ (b + 6) = n := by simp [hI₃]
    have := addIdx_spec (st := ⟨R₀, I₃⟩) (k := b + 6) (a := b + 4) (cnt := b + 7) (z := b)
      (by omega) (by omega) (by omega) (by omega) (by omega) e7 eb
    simp only [e4, e6] at this
    simpa [hI₄, hI₃] using this
  -- step 5: clear the registers of the later messages
  set R₅ := fillR R₀ (n + μ) (c * μ) 0 with hR₅
  have h5 : Runs (fillRange (b + 6) 2 0 (b + 8) (b + 9) b) ⟨R₀, I₄⟩ (· = ⟨R₅, I₄⟩)
      (6 * (n + μ) + 11 * (c * μ) + 4) := by
    have z8 : I₄ (b + 8) = 0 := by
      simp [hI₄, hI₃, hI₂, hI₁, Function.update_apply, hI₀b (b + 8) (by omega)]
    have z9 : I₄ (b + 9) = 0 := by
      simp [hI₄, hI₃, hI₂, hI₁, Function.update_apply, hI₀b (b + 9) (by omega)]
    have zb : I₄ b = 0 := by
      simp only [hI₄, hI₃, hI₂, hI₁, Function.update_apply]
      split_ifs <;> first | omega | exact hI₀b b hb3
    have e6 : I₄ (b + 6) = n + μ := by simp [hI₄]
    have e2 : I₄ 2 = c * μ := by
      simp [hI₄, hI₃, hI₂, hI₁, Function.update_apply, hI₀] <;> omega
    have := fillRange_spec (st := ⟨R₀, I₄⟩) (dst := b + 6) (len := 2) (v := 0) (q := b + 8)
      (c := b + 9) (z := b) (by omega) (by omega) (by omega) ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ z8 z9 zb
    simp only [e6, e2] at this
    exact this
  -- step 6: `I 2 := 0`
  set I₆ := Function.update I₄ 2 0 with hI₆
  have h6 : Runs (clearIdx 2 b) ⟨R₅, I₄⟩ (· = ⟨R₅, I₆⟩) (3 * (c * μ) + 1) := by
    have zb : I₄ b = 0 := by
      simp only [hI₄, hI₃, hI₂, hI₁, Function.update_apply]
      split_ifs <;> first | omega | exact hI₀b b hb3
    have e2 : I₄ 2 = c * μ := by
      simp [hI₄, hI₃, hI₂, hI₁, Function.update_apply, hI₀] <;> omega
    have := clearIdx_spec (st := ⟨R₅, I₄⟩) (k := 2) (z := b) (by omega) zb
    simp only [e2] at this
    exact this
  -- the state before the simulation
  have hI₆k : ∀ k, I₆ k = if k < b then [n, μ].getD k 0 else I₀ k + (if k = b + 4 then μ else 0)
      + (if k = b + 5 then c * μ else 0) + (if k = b + 6 then n + μ else 0) := by
    intro k
    simp only [hI₆, hI₄, hI₃, hI₂, hI₁, Function.update_apply]
    by_cases hk : k < b
    · rw [if_pos hk]
      rcases Nat.lt_or_ge k 3 with h | h
      · interval_cases k <;> simp [hI₀] <;> omega
      · rw [List.getD_eq_default _ _ (by simp; omega)]
        simp [show k ≠ 2 by omega, show k ≠ 1 by omega, show k ≠ b + 4 by omega,
          show k ≠ b + 5 by omega, show k ≠ b + 6 by omega, hI₀b k h]
    · rw [if_neg hk]
      simp [show k ≠ 2 by omega, show k ≠ 1 by omega, hI₀b k (by omega)]
      split_ifs <;> omega
  -- step 7: the simulation
  have hok : SimOk b (b + 1) (b + 2) (b + 3) b :=
    ⟨by omega, by omega, by omega, le_rfl, by omega, by omega, by omega, by omega, by omega,
      by omega⟩
  have hag : Agree b (n + μ + T) (initConfig [n, μ] (vecReg (Fin.append x (z ⟨0, by omega⟩))))
      ⟨R₅, I₆⟩ := by
    refine ⟨fun k hk => ?_, fun i _ => ?_⟩
    · simp only [hI₆k, if_pos hk]
      rfl
    · show fillR R₀ (n + μ) (c * μ) 0 i = vecReg (Fin.append x (z ⟨0, by omega⟩)) i
      by_cases hi : i < n + μ
      · rw [fillR_of_not_mem (Or.inl hi), hR₀, vecReg_amVec_noCoins x r z hc i hi]
      · rw [vecReg_of_le _ (show n + μ ≤ i by omega)]
        by_cases hi' : i < n + μ + c * μ
        · rw [fillR_of_mem ⟨by omega, hi'⟩]
        · rw [fillR_of_not_mem (Or.inr (by omega)), hR₀, vecReg_of_le]
          simp only [Nat.mul_zero, Nat.add_zero]
          omega
  have hzero : ∀ k, b ≤ k → k ≤ b + 3 → I₆ k = 0 := by
    intro k hk1 hk2
    rw [hI₆k, if_neg (by omega), hI₀b k (by omega)]
    simp [show k ≠ b + 4 by omega, show k ≠ b + 5 by omega, show k ≠ b + 6 by omega]
  have h7 := sim_spec M hok (by omega) (c₀ := initConfig [n, μ]
    (vecReg (Fin.append x (z ⟨0, by omega⟩)))) (B := n + μ) (H := n + μ + T) rfl hrun
    (fun k hk => by
      simp only [initConfig]
      rcases Nat.lt_or_ge k 2 with h | h
      · interval_cases k <;> simp <;> omega
      · rw [List.getD_eq_default _ _ (by simp; omega)]; omega)
    le_rfl ⟨R₅, I₆⟩ hag (hzero (b + 1) (by omega) (by omega)) (hzero (b + 2) (by omega) (by omega))
    (hzero (b + 3) (by omega) (by omega)) (hzero b le_rfl (by omega))
  -- step 8: halt
  have h8 : ∀ st' : St, ((∀ k, b ≤ k → k ≠ b + 3 → st'.I k = I₆ k) ∧
      st'.I (b + 3) = (if o = some true then 1 else 0) ∧ (∀ k < b, st'.I k ≤ n + μ + T) ∧
      (∀ i, n + μ + T ≤ i → st'.R i = R₅ i)) →
      Halts (.seq (.ite (.idxEq (b + 3) b) (.halt false) (.halt true)) .skip) st'
        (fun _ res => res = some (decide (o = some true))) (2 + 0) := by
    intro st' hst
    refine Spec.seq (Q₁ := fun _ => False) ?_ fun _ h => h.elim
    obtain ⟨hfr, hacc, -, -⟩ := hst
    have hzb : st'.I b = 0 := by
      rw [hfr b le_rfl (by omega), hzero b le_rfl (by omega)]
    by_cases ho : o = some true
    · refine Spec.ite_neg (T := 0) ?_ (Spec.halt ?_)
      · simp [hacc, hzb, ho]
      · simp [ho]
    · refine Spec.ite_pos (T := 0) ?_ (Spec.halt ?_)
      · simp [hacc, hzb, ho]
      · simp [ho]
  have h78 := (Spec.of_runs (H := fun _ res => res = some (decide (o = some true))) h7).seq h8
  have hall := Spec.seq_eq (Spec.of_runs h1) (Spec.seq_eq (Spec.of_runs h2)
    (Spec.seq_eq (Spec.of_runs h3) (Spec.seq_eq (Spec.of_runs h4)
    (Spec.seq_eq (Spec.of_runs h5) (Spec.seq_eq (Spec.of_runs h6) h78)))))
  refine hall.mono_time ?_
  simp only [npAMTime]
  omega

/-! ## The value of the protocol -/

theorem ciSup_indicator {α : Type} [Nonempty α] (A : α → Prop) :
    (⨆ y : α, (if A y then (1 : ℝ) else 0)) = if ∃ y, A y then 1 else 0 := by
  by_cases h : ∃ y, A y
  · rw [if_pos h]
    obtain ⟨y₀, hy₀⟩ := h
    have hb : BddAbove (Set.range fun y => if A y then (1 : ℝ) else 0) :=
      ⟨1, by rintro _ ⟨y, rfl⟩; dsimp only; split_ifs <;> norm_num⟩
    refine le_antisymm (ciSup_le fun y => by split_ifs <;> norm_num) ?_
    have := le_ciSup hb y₀
    simpa [hy₀] using this
  · rw [if_neg h]
    simp only [not_exists] at h
    simp [h]

/-- The value of a protocol whose acceptance only depends on the first message: from round
`i ≥ 1` on, the value is the acceptance indicator. -/
theorem amValFrom_first_later {c ρ μ : ℕ} (hc : 1 ≤ c)
    (acc : (Fin c → Fin ρ → Bool) → (Fin c → Fin μ → ℝ) → Prop) (A : (Fin μ → ℝ) → Prop)
    (hacc : ∀ r z, acc r z ↔ A (z ⟨0, by omega⟩)) :
    ∀ m i, c - i = m → 1 ≤ i → ∀ r z,
      amValFrom c ρ μ acc i r z = if A (z ⟨0, by omega⟩) then 1 else 0 := by
  intro m
  induction m with
  | zero =>
    intro i hm hi r z
    rw [amValFrom, dif_neg (by omega)]
    simp only [hacc]
  | succ m ih =>
    intro i hm hi r z
    rw [amValFrom, dif_pos (show i < c by omega)]
    have hin : ∀ (b : Fin ρ → Bool) (y : Fin μ → ℝ),
        amValFrom c ρ μ acc (i + 1) (Function.update r ⟨i, by omega⟩ b)
          (Function.update z ⟨i, by omega⟩ y) = if A (z ⟨0, by omega⟩) then 1 else 0 := by
      intro b y
      rw [ih (i + 1) (by omega) (by omega)]
      rw [Function.update_of_ne (show (⟨0, by omega⟩ : Fin c) ≠ ⟨i, by omega⟩ by
        intro h; simp [Fin.ext_iff] at h; omega)]
    simp only [hin, ciSup_const, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp

/-- The value (10) of a protocol whose acceptance only depends on the first message. -/
theorem amValFrom_first {c ρ μ : ℕ} (hc : 1 ≤ c)
    (acc : (Fin c → Fin ρ → Bool) → (Fin c → Fin μ → ℝ) → Prop) (A : (Fin μ → ℝ) → Prop)
    (hacc : ∀ r z, acc r z ↔ A (z ⟨0, by omega⟩)) (r : Fin c → Fin ρ → Bool)
    (z : Fin c → Fin μ → ℝ) :
    amValFrom c ρ μ acc 0 r z = if ∃ y, A y then 1 else 0 := by
  rw [amValFrom, dif_pos (show 0 < c by omega)]
  have hin : ∀ (b : Fin ρ → Bool) (y : Fin μ → ℝ),
      amValFrom c ρ μ acc (0 + 1) (Function.update r ⟨0, by omega⟩ b)
        (Function.update z ⟨0, by omega⟩ y) = if A y then 1 else 0 := by
    intro b y
    rw [amValFrom_first_later hc acc A hacc _ 1 rfl le_rfl]
    simp
  simp only [hin, ciSup_indicator, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp

/-- **`NP_ℝ ⊆ AM_ℝ[c]`** for `c ≥ 1`. -/
theorem np_sub_am (c : ℕ) (hc : 1 ≤ c) : NP_R ⊆ AM_R c := by
  rintro L ⟨M, p, q, hp, hq, hM⟩
  refine ⟨(npAMStmt M c).toMachine, fun _ => 0, q, fun n => npAMTime M c n (q n) (p n) + 1,
    pb_const 0, hq, ?_, ?_⟩
  · simp only [npAMTime, simTime]
    pb_tac
  · intro n x
    have key : ∀ (r : Fin c → Fin 0 → Bool) (z : Fin c → Fin (q n) → ℝ),
        (npAMStmt M c).toMachine.run (npAMTime M c n (q n) (p n) + 1)
          (initConfig [n, c * 0, c * q n] (vecReg (amVec x r z))) =
        some (some (decide (M.HaltsWith (p n) [n, q n] (Fin.append x (z ⟨0, by omega⟩))
          (some true)))) := by
      intro r z
      obtain ⟨o, ho⟩ := (hM n x).1 (z ⟨0, by omega⟩)
      obtain ⟨st', res, hres, hrun⟩ := Halts.run (npAM_spec M hc x r z ho)
      have := hrun 0
      rw [St.init_at] at this
      simp only [Nat.add_zero] at this
      rw [this, hres]
      simp only [Machine.HaltsWith] at ho ⊢
      simp [ho]
    refine ⟨fun r z => ⟨_, key r z⟩, ?_⟩
    have hv := amValFrom_first (ρ := 0) (μ := q n) hc
      (fun r z => (npAMStmt M c).toMachine.HaltsWith (npAMTime M c n (q n) (p n) + 1)
        [n, c * 0, c * q n] (amVec x r z) (some true))
      (fun y => M.HaltsWith (p n) [n, q n] (Fin.append x y) (some true))
      (fun r z => by rw [Machine.HaltsWith, key r z]; simp) (fun _ _ => false) (fun _ _ => 0)
    simp only [hv]
    constructor
    · intro hx
      rw [if_pos ((hM n x).2.1 hx)]
      norm_num
    · intro hx
      rw [if_neg (fun h => hx ((hM n x).2.2 h))]
      norm_num

end AMNPAux

end ClassSep
