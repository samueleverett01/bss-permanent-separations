import ClassSeparations.Machines.Classes

/-!
# The Ryser circuits (Lemma 4.6): gate numbering

For `m ≥ 1`, the circuit evaluating `per_m(X)` by Ryser's formula and comparing it with `Y`.
Gate indices have `3m + 5` bits, split into fields (least significant first):

* `kind` (3 bits), `J`, `I`, `F` (`m` bits each), `tag` (2 bits),

so that the description of a gate is computed from the bits of its index by copying bit fields
(`ClassSeparations.Machines.RyserMachine`).

* `tag = 0`, one block per `F < 2^m` (the subset `S = {q : F_q = 1}`):
  - `kind = 0` (row sums): `A(F, I, J) = A(F, I, J/2) + [F_{hp J} = 1] · In(F, I, J/2)` if `J` is
    odd, `0` otherwise (`hp J` = highest one of `J`); for `J = 2^j - 1` this is
    `∑_{q < j, F_q = 1} X_{i,q}`, `i = pc I`;
  - `kind = 1` (inputs): `In(F, I, J)` = input `pc(I) · m + pc(J)` (`pc` = number of ones);
  - `kind = 2` (products): `P(F, I, J) = P(F, I/2, J) · A(F, I/2, J)` if `I` is odd, the sign
    `∏_q (F_q ? 1 : -1) = (-1)^{m - |S|}` otherwise;
  - other kinds: `0`.
* `tag = 1`, the addition tree, with the level `L` in the field `I` and the position `p` in the
  field `J`: `T(L, p) = T(L/2, 2p+1) + T(L/2, 2p)` if `L` is odd, `P(p, 2^m-1, 2^m-1) + 0`
  otherwise; the root is `T(2^m - 1, 0) = per_m(X)`.
* `tag = 2`: the comparison with `Y = In(0, 2^m - 1, 0)` (input `m²`):
  `kind 0: per - Y`, `kind 1: Y - per`, `kind 2: [per - Y ≥ 0]`, `kind 3: [Y - per ≥ 0]`,
  `kind 4: [per - Y ≥ 0] · [Y - per ≥ 0]`.

The circuit for `Y ≤ per` ends with the gate `(tag 2, kind 2)`, for `Y ≥ per` with `kind 3`, for
`Y = per` with `kind 4`.
-/

noncomputable section

open Classical

namespace ClassSep

namespace Ryser

/-! ## Gate indices -/

/-- The gate index with fields `tag`, `F`, `I`, `J`, `kind`. -/
def idx (m tag F I J kind : ℕ) : ℕ := kind + 8 * (J + 2 ^ m * (I + 2 ^ m * (F + 2 ^ m * tag)))

/-- The field `kind` of a gate index. -/
def kindOf (i : ℕ) : ℕ := i % 8
/-- The field `J` of a gate index. -/
def jOf (m i : ℕ) : ℕ := i / 8 % 2 ^ m
/-- The field `I` of a gate index. -/
def iOf (m i : ℕ) : ℕ := i / 8 / 2 ^ m % 2 ^ m
/-- The field `F` of a gate index. -/
def fOf (m i : ℕ) : ℕ := i / 8 / 2 ^ m / 2 ^ m % 2 ^ m
/-- The field `tag` of a gate index. -/
def tagOf (m i : ℕ) : ℕ := i / 8 / 2 ^ m / 2 ^ m / 2 ^ m

theorem idx_decomp (m i : ℕ) : idx m (tagOf m i) (fOf m i) (iOf m i) (jOf m i) (kindOf i) = i := by
  unfold idx kindOf jOf iOf fOf tagOf
  rw [Nat.mod_add_div (i / 8 / 2 ^ m / 2 ^ m), Nat.mod_add_div (i / 8 / 2 ^ m),
    Nat.mod_add_div (i / 8), Nat.mod_add_div]

section fields

variable {m t F I J k : ℕ}

theorem idx_div_eight (hk : k < 8) :
    idx m t F I J k / 8 = J + 2 ^ m * (I + 2 ^ m * (F + 2 ^ m * t)) := by
  unfold idx
  rw [Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt hk, Nat.zero_add]

theorem kindOf_idx (hk : k < 8) : kindOf (idx m t F I J k) = k := by
  unfold kindOf idx
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]

theorem jOf_idx (hk : k < 8) (hJ : J < 2 ^ m) : jOf m (idx m t F I J k) = J := by
  unfold jOf
  rw [idx_div_eight hk, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hJ]

theorem iOf_idx (hk : k < 8) (hJ : J < 2 ^ m) (hI : I < 2 ^ m) :
    iOf m (idx m t F I J k) = I := by
  unfold iOf
  rw [idx_div_eight hk, Nat.add_mul_div_left _ _ (Nat.two_pow_pos m), Nat.div_eq_of_lt hJ,
    Nat.zero_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hI]

theorem fOf_idx (hk : k < 8) (hJ : J < 2 ^ m) (hI : I < 2 ^ m) (hF : F < 2 ^ m) :
    fOf m (idx m t F I J k) = F := by
  unfold fOf
  rw [idx_div_eight hk, Nat.add_mul_div_left _ _ (Nat.two_pow_pos m), Nat.div_eq_of_lt hJ,
    Nat.zero_add, Nat.add_mul_div_left _ _ (Nat.two_pow_pos m), Nat.div_eq_of_lt hI,
    Nat.zero_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hF]

theorem tagOf_idx (hk : k < 8) (hJ : J < 2 ^ m) (hI : I < 2 ^ m) (hF : F < 2 ^ m) :
    tagOf m (idx m t F I J k) = t := by
  unfold tagOf
  rw [idx_div_eight hk, Nat.add_mul_div_left _ _ (Nat.two_pow_pos m), Nat.div_eq_of_lt hJ,
    Nat.zero_add, Nat.add_mul_div_left _ _ (Nat.two_pow_pos m), Nat.div_eq_of_lt hI,
    Nat.zero_add, Nat.add_mul_div_left _ _ (Nat.two_pow_pos m), Nat.div_eq_of_lt hF,
    Nat.zero_add]

theorem kindOf_lt (i : ℕ) : kindOf i < 8 := Nat.mod_lt _ (by norm_num)
theorem jOf_lt (m i : ℕ) : jOf m i < 2 ^ m := Nat.mod_lt _ (Nat.two_pow_pos m)
theorem iOf_lt (m i : ℕ) : iOf m i < 2 ^ m := Nat.mod_lt _ (Nat.two_pow_pos m)
theorem fOf_lt (m i : ℕ) : fOf m i < 2 ^ m := Nat.mod_lt _ (Nat.two_pow_pos m)

theorem tagOf_lt {i : ℕ} (hi : i < 2 ^ (3 * m + 5)) : tagOf m i < 4 := by
  unfold tagOf
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul,
    Nat.div_lt_iff_lt_mul (by positivity)]
  calc i < 2 ^ (3 * m + 5) := hi
    _ = _ := by ring

/-- The ordering of gate indices is lexicographic in `(tag, F, I, J, kind)`. -/
theorem idx_lt_of_kind {k' : ℕ} (h : k < k') : idx m t F I J k < idx m t F I J k' := by
  unfold idx; omega

theorem idx_lt_of_J {J' k' : ℕ} (hJ : J < J') (hk : k < 8) :
    idx m t F I J k < idx m t F I J' k' := by
  unfold idx
  have : 2 ^ m * (I + 2 ^ m * (F + 2 ^ m * t)) = 2 ^ m * (I + 2 ^ m * (F + 2 ^ m * t)) := rfl
  omega

theorem idx_lt_of_I {I' J' k' : ℕ} (hI : I < I') (hJ : J < 2 ^ m) (hk : k < 8) :
    idx m t F I J k < idx m t F I' J' k' := by
  unfold idx
  have h1 : 2 ^ m * I + 2 ^ m ≤ 2 ^ m * I' := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hI
  have h2 : 2 ^ m * (I + 2 ^ m * (F + 2 ^ m * t)) =
      2 ^ m * I + 2 ^ m * (2 ^ m * (F + 2 ^ m * t)) := Nat.mul_add _ _ _
  have h3 : 2 ^ m * (I' + 2 ^ m * (F + 2 ^ m * t)) =
      2 ^ m * I' + 2 ^ m * (2 ^ m * (F + 2 ^ m * t)) := Nat.mul_add _ _ _
  omega

theorem idx_lt_of_F {F' I' J' k' : ℕ} (hF : F < F') (hI : I < 2 ^ m) (hJ : J < 2 ^ m)
    (hk : k < 8) : idx m t F I J k < idx m t F' I' J' k' := by
  unfold idx
  have h1 : 2 ^ m * F + 2 ^ m ≤ 2 ^ m * F' := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hF
  have h1' : 2 ^ m * (2 ^ m * F + 2 ^ m) ≤ 2 ^ m * (2 ^ m * F') := Nat.mul_le_mul_left _ h1
  have h4 : 2 ^ m * I + 2 ^ m ≤ 2 ^ m * 2 ^ m := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hI
  have e1 : 2 ^ m * (I + 2 ^ m * (F + 2 ^ m * t)) =
      2 ^ m * I + 2 ^ m * (2 ^ m * F) + 2 ^ m * (2 ^ m * (2 ^ m * t)) := by ring
  have e2 : 2 ^ m * (I' + 2 ^ m * (F' + 2 ^ m * t)) =
      2 ^ m * I' + 2 ^ m * (2 ^ m * F') + 2 ^ m * (2 ^ m * (2 ^ m * t)) := by ring
  have e3 : 2 ^ m * (2 ^ m * F + 2 ^ m) = 2 ^ m * (2 ^ m * F) + 2 ^ m * 2 ^ m := by ring
  omega

theorem idx_lt_of_tag {t' F' I' J' k' : ℕ} (ht : t < t') (hF : F < 2 ^ m) (hI : I < 2 ^ m)
    (hJ : J < 2 ^ m) (hk : k < 8) : idx m t F I J k < idx m t' F' I' J' k' := by
  unfold idx
  have h1 : 2 ^ m * t + 2 ^ m ≤ 2 ^ m * t' := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ ht
  have h5 : 2 ^ m * F + 2 ^ m ≤ 2 ^ m * 2 ^ m := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hF
  have h4 : 2 ^ m * I + 2 ^ m ≤ 2 ^ m * 2 ^ m := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hI
  have h1' : 2 ^ m * (2 ^ m * (2 ^ m * t + 2 ^ m)) ≤ 2 ^ m * (2 ^ m * (2 ^ m * t')) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h1)
  have h5' : 2 ^ m * (2 ^ m * F + 2 ^ m) ≤ 2 ^ m * (2 ^ m * 2 ^ m) :=
    Nat.mul_le_mul_left _ h5
  have e1 : 2 ^ m * (I + 2 ^ m * (F + 2 ^ m * t)) =
      2 ^ m * I + 2 ^ m * (2 ^ m * F) + 2 ^ m * (2 ^ m * (2 ^ m * t)) := by ring
  have e2 : 2 ^ m * (I' + 2 ^ m * (F' + 2 ^ m * t')) =
      2 ^ m * I' + 2 ^ m * (2 ^ m * F') + 2 ^ m * (2 ^ m * (2 ^ m * t')) := by ring
  have e3 : 2 ^ m * (2 ^ m * (2 ^ m * t + 2 ^ m)) =
      2 ^ m * (2 ^ m * (2 ^ m * t)) + 2 ^ m * (2 ^ m * 2 ^ m) := by ring
  have e4 : 2 ^ m * (2 ^ m * F + 2 ^ m) = 2 ^ m * (2 ^ m * F) + 2 ^ m * 2 ^ m := by ring
  omega

theorem idx_lt_two_pow (hk : k < 8) (hJ : J < 2 ^ m) (hI : I < 2 ^ m) (hF : F < 2 ^ m)
    (ht : t < 4) : idx m t F I J k < 2 ^ (3 * m + 5) := by
  have := idx_lt_of_tag (m := m) (t' := 4) (F' := 0) (I' := 0) (J' := 0) (k' := 0) ht hF hI hJ hk
  have e : idx m 4 0 0 0 0 = 2 ^ (3 * m + 5) := by unfold idx; ring
  omega

/-- The binary digits of a gate index. -/
theorem idx_testBit (hk : k < 8) (hJ : J < 2 ^ m) (hI : I < 2 ^ m) (hF : F < 2 ^ m) (q : ℕ) :
    (idx m t F I J k).testBit q =
      if q < 3 then k.testBit q
      else if q < 3 + m then J.testBit (q - 3)
      else if q < 3 + 2 * m then I.testBit (q - (3 + m))
      else if q < 3 + 3 * m then F.testBit (q - (3 + 2 * m))
      else t.testBit (q - (3 + 3 * m)) := by
  unfold idx
  rw [show k + 8 * (J + 2 ^ m * (I + 2 ^ m * (F + 2 ^ m * t))) =
      2 ^ 3 * (2 ^ m * (2 ^ m * (2 ^ m * t + F) + I) + J) + k by ring,
    Nat.testBit_two_pow_mul_add _ (by norm_num; omega)]
  by_cases h3 : q < 3
  · simp [h3]
  rw [if_neg h3, if_neg h3, Nat.testBit_two_pow_mul_add _ hJ]
  by_cases h4 : q - 3 < m
  · simp [h4, show q < 3 + m by omega]
  rw [if_neg h4, if_neg (by omega), Nat.testBit_two_pow_mul_add _ hI]
  by_cases h5 : q - 3 - m < m
  · rw [if_pos h5, if_pos (by omega), show q - 3 - m = q - (3 + m) by omega]
  rw [if_neg h5, if_neg (by omega), Nat.testBit_two_pow_mul_add _ hF]
  by_cases h6 : q - 3 - m - m < m
  · rw [if_pos h6, if_pos (by omega), show q - 3 - m - m = q - (3 + 2 * m) by omega]
  rw [if_neg h6, if_neg (by omega), show q - 3 - m - m - m = q - (3 + 3 * m) by omega]

theorem jOf_testBit (m i j : ℕ) : (jOf m i).testBit j = (decide (j < m) && i.testBit (3 + j)) := by
  unfold jOf
  rw [Nat.testBit_mod_two_pow, show (8 : ℕ) = 2 ^ 3 by norm_num, Nat.testBit_div_two_pow,
    Nat.add_comm j 3]

theorem iOf_testBit (m i j : ℕ) :
    (iOf m i).testBit j = (decide (j < m) && i.testBit (3 + m + j)) := by
  unfold iOf
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, show (8 : ℕ) = 2 ^ 3 by norm_num,
    Nat.testBit_div_two_pow]
  congr 2; omega

theorem fOf_testBit (m i j : ℕ) :
    (fOf m i).testBit j = (decide (j < m) && i.testBit (3 + 2 * m + j)) := by
  unfold fOf
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_div_two_pow,
    show (8 : ℕ) = 2 ^ 3 by norm_num, Nat.testBit_div_two_pow]
  congr 2; omega

theorem kindOf_testBit (i j : ℕ) : (kindOf i).testBit j = (decide (j < 3) && i.testBit j) := by
  unfold kindOf
  rw [show (8 : ℕ) = 2 ^ 3 by norm_num, Nat.testBit_mod_two_pow]

theorem tagOf_testBit (m i j : ℕ) : (tagOf m i).testBit j = i.testBit (3 + 3 * m + j) := by
  unfold tagOf
  rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow, Nat.testBit_div_two_pow,
    show (8 : ℕ) = 2 ^ 3 by norm_num, Nat.testBit_div_two_pow]
  congr 1; omega

end fields

/-! ## Auxiliary functions of the fields -/

/-- The number of ones among the binary digits `0, …, q-1` of `x`. -/
def pc : ℕ → ℕ → ℕ
  | 0, _ => 0
  | q + 1, x => pc q x + if x.testBit q then 1 else 0

/-- The digit of `F` at the highest one of `J` below `q` (`false` if there is none). -/
def look : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | q + 1, F, J => if J.testBit q then F.testBit q else look q F J

/-- The sign `∏_{j < q} (F_j ? 1 : -1)`. -/
def sgn : ℕ → ℕ → ℝ
  | 0, _ => 1
  | q + 1, F => if F.testBit q then sgn q F else -sgn q F

theorem pc_le (q x : ℕ) : pc q x ≤ q := by
  induction q with
  | zero => simp [pc]
  | succ q ih => simp only [pc]; split_ifs <;> omega

/-! ## The circuits -/

/-- The root of the addition tree. -/
def root (m : ℕ) : ℕ := idx m 1 0 (2 ^ m - 1) 0 0

/-- The input gate of `Y` (input number `m²`). -/
def yIdx (m : ℕ) : ℕ := idx m 0 0 (2 ^ m - 1) 0 1

/-- The final gates. -/
def fin (m k : ℕ) : ℕ := idx m 2 0 0 0 k

/-- Gate number `i` of the Ryser circuits for `m × m` matrices. -/
def gate (m i : ℕ) : AGate :=
  if tagOf m i = 0 then
    if kindOf i = 0 then
      if (jOf m i).testBit 0 then
        .arith .add (idx m 0 (fOf m i) (iOf m i) (jOf m i / 2) 0)
          (if look m (fOf m i) (jOf m i) then idx m 0 (fOf m i) (iOf m i) (jOf m i / 2) 1 else 0)
      else .const 0
    else if kindOf i = 1 then .input (pc m (iOf m i) * m + pc m (jOf m i))
    else if kindOf i = 2 then
      if (iOf m i).testBit 0 then
        .arith .mul (idx m 0 (fOf m i) (iOf m i / 2) (jOf m i) 2)
          (idx m 0 (fOf m i) (iOf m i / 2) (jOf m i) 0)
      else .const (sgn m (fOf m i))
    else .const 0
  else if tagOf m i = 1 then
    if (iOf m i).testBit 0 then
      .arith .add (idx m 1 0 (iOf m i / 2) (2 * jOf m i % 2 ^ m + 1) 0)
        (idx m 1 0 (iOf m i / 2) (2 * jOf m i % 2 ^ m) 0)
    else .arith .add (idx m 0 (jOf m i) (2 ^ m - 1) (2 ^ m - 1) 2) 0
  else if tagOf m i = 2 then
    if kindOf i = 0 then .arith .sub (root m) (yIdx m)
    else if kindOf i = 1 then .arith .sub (yIdx m) (root m)
    else if kindOf i = 2 then .sign (fin m 0)
    else if kindOf i = 3 then .sign (fin m 1)
    else if kindOf i = 4 then .arith .mul (fin m 2) (fin m 3)
    else .const 0
  else .const 0

/-- The Ryser circuit ending with the final gate of kind `last`. -/
def circ (m last : ℕ) : ACircuit := (List.range (fin m last + 1)).map (gate m)

end Ryser

end ClassSep
