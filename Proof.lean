import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

/-!
  Partial formalization of MathOverflow 323963.

  The sequence is

      a 0 = ... = a 4 = 1,
      a (n+5) * a n = (a (n+4)+1)(a (n+3)+1)(a (n+2)+1)(a (n+1)+1).

  The alternating invariant, the transformed recurrence, the 14-block
  induction, and the final 2-adic pairing argument are proved below.

  The fourteen-step 2-adic return and the odd-prime valuation-atom
  induction are both proved below.
-/

namespace MO323963

/-! ## The sequence and its alternating first integral -/

def a : ℕ → ℚ
  | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 1
  | n + 5 => (a (n + 4) + 1) * (a (n + 3) + 1) *
      (a (n + 2) + 1) * (a (n + 1) + 1) / a n

lemma a_pos : ∀ n, 0 < a n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => norm_num [a]
    | 1 => norm_num [a]
    | 2 => norm_num [a]
    | 3 => norm_num [a]
    | 4 => norm_num [a]
    | n + 5 =>
      have h0 := ih n (by omega)
      have h1 := ih (n + 1) (by omega)
      have h2 := ih (n + 2) (by omega)
      have h3 := ih (n + 3) (by omega)
      have h4 := ih (n + 4) (by omega)
      rw [a]
      positivity

lemma a_ne (n : ℕ) : a n ≠ 0 := (a_pos n).ne'

lemma ap1_ne (n : ℕ) : a n + 1 ≠ 0 := by
  have := a_pos n
  linarith

lemma rec_eq (n : ℕ) :
    a (n + 5) * a n =
      (a (n + 4) + 1) * (a (n + 3) + 1) *
      (a (n + 2) + 1) * (a (n + 1) + 1) := by
  show ((a (n + 4) + 1) * (a (n + 3) + 1) *
      (a (n + 2) + 1) * (a (n + 1) + 1) / a n) * a n = _
  rw [div_mul_cancel₀ _ (a_ne n)]

def R (n : ℕ) : ℚ :=
  a n * a (n + 2) * a (n + 4) /
    (a (n + 1) * a (n + 3) * (a (n + 1) + 1) * (a (n + 3) + 1))

lemma R_mul_succ (n : ℕ) : R n * R (n + 1) = 1 := by
  have h := rec_eq n
  unfold R
  field_simp [a_ne, ap1_ne]
  nlinarith [h]

lemma R_zero : R 0 = 1 / 4 := by norm_num [R, a]

lemma R_even_odd (n : ℕ) :
    (R (2 * n) = 1 / 4) ∧ (R (2 * n + 1) = 4) := by
  induction n with
  | zero =>
      constructor
      · exact R_zero
      · have h := R_mul_succ 0
        rw [R_zero] at h
        norm_num at h ⊢
        linarith
  | succ n ih =>
      rcases ih with ⟨he, ho⟩
      have he' : R (2 * (n + 1)) = 1 / 4 := by
        have h := R_mul_succ (2 * n + 1)
        rw [show 2 * n + 1 + 1 = 2 * (n + 1) by omega, ho] at h
        norm_num at h ⊢
        linarith
      constructor
      · exact he'
      · have h := R_mul_succ (2 * (n + 1))
        rw [he'] at h
        norm_num at h ⊢
        linarith

def T (z : ℚ) : ℚ := z * (z + 1) / 2

lemma T_pos (n : ℕ) : 0 < T (a n) := by
  unfold T
  have := a_pos n
  positivity

lemma T_ne (n : ℕ) : T (a n) ≠ 0 := (T_pos n).ne'

lemma invariant_even (n : ℕ) :
    a (2 * n) * a (2 * n + 2) * a (2 * n + 4) =
      T (a (2 * n + 1)) * T (a (2 * n + 3)) := by
  have h := (R_even_odd n).1
  unfold R at h
  unfold T
  field_simp [a_ne, ap1_ne] at h ⊢
  nlinarith [h]

lemma invariant_odd (n : ℕ) :
    a (2 * n + 1) * a (2 * n + 3) * a (2 * n + 5) =
      16 * (T (a (2 * n + 2)) * T (a (2 * n + 4))) := by
  have h := (R_even_odd n).2
  unfold R at h
  unfold T
  field_simp [a_ne, ap1_ne] at h ⊢
  nlinarith [h]

/-! ## The transformed sequence -/

def x (n : ℕ) : ℚ := a n * a (n + 2) / T (a (n + 1))

lemma x_pos (n : ℕ) : 0 < x n := by
  unfold x
  have h0 := a_pos n
  have h1 := a_pos (n + 2)
  have hT := T_pos (n + 1)
  positivity

lemma x_ne (n : ℕ) : x n ≠ 0 := (x_pos n).ne'

lemma x_mul_even (n : ℕ) :
    x (2 * n) * x (2 * n + 2) = a (2 * n + 2) := by
  have h := invariant_even n
  unfold x
  field_simp [T_ne]
  linear_combination a (2 * n + 2) * h

lemma x_mul_odd (n : ℕ) :
    x (2 * n + 1) * x (2 * n + 3) = 16 * a (2 * n + 3) := by
  have h := invariant_odd n
  unfold x
  field_simp [T_ne]
  linear_combination a (2 * n + 3) * h

lemma x0 : x 0 = 1 := by norm_num [x, T, a]
lemma x1 : x 1 = 1 := by norm_num [x, T, a]
lemma x2 : x 2 = 1 := by norm_num [x, T, a]
lemma x3 : x 3 = 16 := by norm_num [x, T, a]

/-- Odd phase of the transformed recurrence. -/
lemma x_rec_odd (n : ℕ) :
    x (2*n+4) =
      x (2*n+1) * x (2*n+3) *
        (16 + x (2*n+1) * x (2*n+3)) /
        (512 * x (2*n) * x (2*n+2)) := by
  have h02 := x_mul_even n
  have h24 := x_mul_even (n+1)
  rw [show 2*(n+1)=2*n+2 by omega,
      show 2*n+2+2=2*n+4 by omega] at h24
  have h13 := x_mul_odd n
  have hxd : x (2*n+2) * T (a (2*n+3)) =
      a (2*n+2) * a (2*n+4) := by
    rw [x]
    field_simp [T_ne]
  have hcancel : a (2*n+2) * x (2*n+4) = T (a (2*n+3)) := by
    rw [← h24] at hxd
    have hp := x_pos (2*n+2)
    nlinarith
  have hmain : x (2*n) * x (2*n+2) * x (2*n+4) =
      T (a (2*n+3)) := by
    rw [h02]
    exact hcancel
  field_simp [x_ne]
  have hL : x (2*n+4) * 512 * x (2*n) * x (2*n+2) =
      512 * T (a (2*n+3)) := by
    linear_combination 512 * hmain
  have hR : x (2*n+1) * x (2*n+3) *
      (16 + x (2*n+1) * x (2*n+3)) =
      512 * T (a (2*n+3)) := by
    rw [h13, T]
    ring
  exact hL.trans hR.symm

/-- Even positive phase of the transformed recurrence. -/
lemma x_rec_even (n : ℕ) :
    x (2*n+5) =
      128 * x (2*n+2) * x (2*n+4) *
        (1 + x (2*n+2) * x (2*n+4)) /
        (x (2*n+1) * x (2*n+3)) := by
  have h13 := x_mul_odd n
  have h35 := x_mul_odd (n+1)
  rw [show 2*(n+1)+1=2*n+3 by omega,
      show 2*(n+1)+3=2*n+5 by omega] at h35
  have h24 := x_mul_even (n+1)
  rw [show 2*(n+1)=2*n+2 by omega,
      show 2*n+2+2=2*n+4 by omega] at h24
  have hxd : x (2*n+3) * T (a (2*n+4)) =
      a (2*n+3) * a (2*n+5) := by
    rw [x]
    field_simp [T_ne]
  have hmul : x (2*n+3) *
      (a (2*n+3) * x (2*n+5) - 16 * T (a (2*n+4))) = 0 := by
    linear_combination a (2*n+3) * h35 - 16 * hxd
  have hcancel : a (2*n+3) * x (2*n+5) =
      16 * T (a (2*n+4)) := by
    rcases mul_eq_zero.mp hmul with hzero | hzero
    · exact absurd hzero (x_pos _).ne'
    · linarith
  field_simp [x_ne]
  have hL : x (2*n+5) * x (2*n+1) * x (2*n+3) =
      16 * a (2*n+3) * x (2*n+5) := by
    linear_combination x (2*n+5) * h13
  have hL' : x (2*n+5) * x (2*n+1) * x (2*n+3) =
      256 * T (a (2*n+4)) := by
    calc
      _ = 16 * a (2*n+3) * x (2*n+5) := hL
      _ = 16 * (a (2*n+3) * x (2*n+5)) := by ring
      _ = 16 * (16 * T (a (2*n+4))) := by rw [hcancel]
      _ = 256 * T (a (2*n+4)) := by ring
  have hR : 128 * x (2*n+2) * x (2*n+4) *
      (1 + x (2*n+2) * x (2*n+4)) =
      256 * T (a (2*n+4)) := by
    calc
      _ = 128 * (x (2*n+2) * x (2*n+4)) *
          (1 + x (2*n+2) * x (2*n+4)) := by ring
      _ = 128 * a (2*n+4) * (1 + a (2*n+4)) := by rw [h24]
      _ = 256 * T (a (2*n+4)) := by rw [T]; ring
  exact hL'.trans hR.symm

/-! ## The fourteen-step 2-adic return -/

abbrev v2 (q : ℚ) : ℤ := padicValRat 2 q

def Unit2 (q : ℚ) : Prop := q ≠ 0 ∧ v2 q = 0
def Val4 (q : ℚ) : Prop := q ≠ 0 ∧ v2 q = 4
def Close4 (q r : ℚ) : Prop := q = r ∨ 2 ≤ v2 (q-r)

/-- The lower-bound word
`(0,0,0,4,0,4,2,2,-2,2,2,4,0,4)`. -/
def ell (n : ℕ) : ℤ :=
  match n % 14 with
  | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 4
  | 4 => 0 | 5 => 4 | 6 => 2 | 7 => 2
  | 8 => -2 | 9 => 2 | 10 => 2 | 11 => 4
  | 12 => 0 | _ => 4

def kExp (n : ℕ) : ℤ := if n % 2 = 0 then 0 else 4

lemma ell_period (n : ℕ) : ell (n + 14) = ell n := by simp [ell]
lemma kExp_period (n : ℕ) : kExp (n + 14) = kExp n := by
  simp [kExp, Nat.add_mod]

/-- The negative entry in `ell` is harmless after pairing indices two apart. -/
lemma word_pair (n : ℕ) : 0 ≤ ell n + ell (n + 2) - kExp n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < 14
    · interval_cases n <;> norm_num [ell, kExp]
    · have hih := ih (n - 14) (by omega)
      have hnrep : n = (n - 14) + 14 := by omega
      rw [hnrep, ell_period, kExp_period]
      have harg : n - 14 + 14 + 2 = (n - 14 + 2) + 14 := by omega
      rw [harg, ell_period]
      exact hih

lemma v2_two_pow (k : ℕ) : v2 ((2 : ℚ) ^ k) = k := by
  change padicValRat 2 ((2 : ℚ) ^ k) = (k : ℤ)
  rw [padicValRat.pow (by norm_num),
    show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num,
    padicValRat.self (by norm_num)]
  ring

lemma v2_16 : v2 (16 : ℚ) = 4 := by
  have h := v2_two_pow 4
  norm_num at h ⊢
  exact h

/-- A block begins with three units, then a term of valuation four; the first
and third units agree modulo four in the 2-adic sense. -/
def TubeAt (s : ℕ) : Prop :=
  Unit2 (x s) ∧ Unit2 (x (s+1)) ∧ Unit2 (x (s+2)) ∧
    Val4 (x (s+3)) ∧ Close4 (x s) (x (s+2))

def BoundsAt (s : ℕ) : Prop :=
  ∀ r, r < 14 → ell r ≤ v2 (x (s+r))

lemma tube_zero : TubeAt 0 := by
  unfold TubeAt Unit2 Val4 Close4
  rw [x0, x1, x2, x3]
  norm_num [padicValRat.one, v2_16]


/-! ### Exact normalized equations for one fourteen-step block -/

lemma x_rec_odd_block (q j : ℕ) :
    x (14*q+2*j+4) =
      x (14*q+2*j+1) * x (14*q+2*j+3) *
        (16 + x (14*q+2*j+1) * x (14*q+2*j+3)) /
        (512 * x (14*q+2*j) * x (14*q+2*j+2)) := by
  have h0 : 2*(7*q+j)+4 = 14*q+2*j+4 := by omega
  have h1 : 2*(7*q+j)+1 = 14*q+2*j+1 := by omega
  have h2 : 2*(7*q+j)+3 = 14*q+2*j+3 := by omega
  have h3 : 2*(7*q+j) = 14*q+2*j := by omega
  have h4 : 2*(7*q+j)+2 = 14*q+2*j+2 := by omega
  simpa only [h0, h1, h2, h3, h4] using x_rec_odd (7*q+j)

lemma x_rec_even_block (q j : ℕ) :
    x (14*q+2*j+5) =
      128 * x (14*q+2*j+2) * x (14*q+2*j+4) *
        (1 + x (14*q+2*j+2) * x (14*q+2*j+4)) /
        (x (14*q+2*j+1) * x (14*q+2*j+3)) := by
  have h0 : 2*(7*q+j)+5 = 14*q+2*j+5 := by omega
  have h1 : 2*(7*q+j)+2 = 14*q+2*j+2 := by omega
  have h2 : 2*(7*q+j)+4 = 14*q+2*j+4 := by omega
  have h3 : 2*(7*q+j)+1 = 14*q+2*j+1 := by omega
  have h4 : 2*(7*q+j)+3 = 14*q+2*j+3 := by omega
  simpa only [h0, h1, h2, h3, h4] using x_rec_even (7*q+j)

def u0 (q : ℕ) : ℚ := x (14*q)
def u1 (q : ℕ) : ℚ := x (14*q+1)
def u2 (q : ℕ) : ℚ := x (14*q+2)
def u3 (q : ℕ) : ℚ := x (14*q+3) / 16

def z4 (q : ℕ) : ℚ := x (14*q+4)
def z5 (q : ℕ) : ℚ := x (14*q+5) / 16
def z6 (q : ℕ) : ℚ := x (14*q+6) / 4
def z7 (q : ℕ) : ℚ := x (14*q+7) / 4
def z8 (q : ℕ) : ℚ := 4 * x (14*q+8)
def z9 (q : ℕ) : ℚ := x (14*q+9) / 4
def z10 (q : ℕ) : ℚ := x (14*q+10) / 4
def z11 (q : ℕ) : ℚ := x (14*q+11) / 16
def z12 (q : ℕ) : ℚ := x (14*q+12)
def z13 (q : ℕ) : ℚ := x (14*q+13) / 16
def z14 (q : ℕ) : ℚ := x (14*q+14)
def z15 (q : ℕ) : ℚ := x (14*q+15)
def z16 (q : ℕ) : ℚ := x (14*q+16)
def z17 (q : ℕ) : ℚ := x (14*q+17) / 16

lemma u1_ne (q : ℕ) : u1 q ≠ 0 := by unfold u1; exact x_ne _
lemma u2_ne (q : ℕ) : u2 q ≠ 0 := by unfold u2; exact x_ne _
lemma u3_ne (q : ℕ) : u3 q ≠ 0 := by
  unfold u3
  exact div_ne_zero (x_ne _) (by norm_num)
lemma z4_ne (q : ℕ) : z4 q ≠ 0 := by unfold z4; exact x_ne _
lemma z5_ne (q : ℕ) : z5 q ≠ 0 := by
  unfold z5
  exact div_ne_zero (x_ne _) (by norm_num)
lemma z6_ne (q : ℕ) : z6 q ≠ 0 := by
  unfold z6
  exact div_ne_zero (x_ne _) (by norm_num)

lemma z4_formula (q : ℕ) :
    z4 q = u1 q*u3 q*(1+u1 q*u3 q)/(2*u0 q*u2 q) := by
  unfold z4 u0 u1 u2 u3
  rw [x_rec_odd_block q 0]
  field_simp [x_ne]
  ring_nf

lemma z5_formula (q : ℕ) :
    z5 q = u2 q*z4 q*(1+u2 q*z4 q)/(2*u1 q*u3 q) := by
  unfold z5 u1 u2 u3 z4
  rw [x_rec_even_block q 0]
  field_simp [x_ne]
  ring

lemma z6_formula (q : ℕ) :
    z6 q = (1+u2 q*z4 q)*(1+16*u3 q*z5 q)/u1 q := by
  unfold z6
  rw [x_rec_odd_block q 1]
  have hx3 : x (14*q+3) = 16*u3 q := by unfold u3; ring
  have hx5 : x (14*q+5) = 16*z5 q := by unfold z5; ring
  rw [hx3, hx5, z5_formula q]
  unfold u1 u2 u3 z4
  norm_num
  field_simp [x_ne]
  ring

lemma z7_raw_formula (q : ℕ) :
    z7 q = z4 q*z6 q*(1+4*z4 q*z6 q)/(2*u3 q*z5 q) := by
  unfold z7 z4 z5 z6 u3
  rw [x_rec_even_block q 1]
  norm_num
  field_simp [x_ne]
  ring

lemma z7_formula (q : ℕ) :
    z7 q = (1+16*u3 q*z5 q)*(1+4*z4 q*z6 q)/u2 q := by
  have hcore : z4 q*z6 q*u2 q =
      2*u3 q*z5 q*(1+16*u3 q*z5 q) := by
    rw [z6_formula q, z5_formula q]
    field_simp [u1_ne, u3_ne]
  rw [z7_raw_formula q]
  field_simp [u2_ne, u3_ne, z5_ne]
  linear_combination (1+4*z4 q*z6 q) * hcore

lemma z8_raw_formula (q : ℕ) :
    z8 q = 2*z5 q*z7 q*(1+4*z5 q*z7 q)/(z4 q*z6 q) := by
  unfold z8 z4 z5 z6 z7
  rw [x_rec_odd_block q 2]
  norm_num
  field_simp [x_ne]
  ring

lemma z8_formula (q : ℕ) :
    z8 q = (1+4*z4 q*z6 q)*(1+4*z5 q*z7 q)/u3 q := by
  have hcore : 2*u3 q*z5 q*z7 q =
      z4 q*z6 q*(1+4*z4 q*z6 q) := by
    rw [z7_formula q, z6_formula q, z5_formula q]
    field_simp [u1_ne, u2_ne, u3_ne]
  rw [z8_raw_formula q]
  field_simp [u3_ne, z4_ne, z6_ne]
  linear_combination (1+4*z5 q*z7 q) * hcore

lemma z9_formula (q : ℕ) :
    z9 q = z6 q*z8 q*(1+z6 q*z8 q)/(2*z5 q*z7 q) := by
  unfold z9 z5 z6 z7 z8
  rw [x_rec_even_block q 2]
  norm_num
  field_simp [x_ne]
  ring

lemma z10_formula (q : ℕ) :
    z10 q = z7 q*z9 q*(1+z7 q*z9 q)/(8*z6 q*z8 q) := by
  unfold z10 z6 z7 z8 z9
  rw [x_rec_odd_block q 3]
  norm_num
  field_simp [x_ne]
  ring

lemma z11_formula (q : ℕ) :
    z11 q = z8 q*z10 q*(1+z8 q*z10 q)/(2*z7 q*z9 q) := by
  unfold z11 z7 z8 z9 z10
  rw [x_rec_even_block q 3]
  norm_num
  field_simp [x_ne]
  ring

lemma z12_formula (q : ℕ) :
    z12 q = 2*z9 q*z11 q*(1+4*z9 q*z11 q)/(z8 q*z10 q) := by
  unfold z12 z8 z9 z10 z11
  rw [x_rec_odd_block q 4]
  norm_num
  field_simp [x_ne]
  ring

lemma z13_formula (q : ℕ) :
    z13 q = z10 q*z12 q*(1+4*z10 q*z12 q)/(2*z9 q*z11 q) := by
  unfold z13 z9 z10 z11 z12
  rw [x_rec_even_block q 4]
  norm_num
  field_simp [x_ne]
  ring

lemma z14_formula (q : ℕ) :
    z14 q = 2*z11 q*z13 q*(1+16*z11 q*z13 q)/(z10 q*z12 q) := by
  unfold z14 z10 z11 z12 z13
  rw [x_rec_odd_block q 5]
  norm_num
  field_simp [x_ne]
  ring

lemma z15_formula (q : ℕ) :
    z15 q = z12 q*z14 q*(1+z12 q*z14 q)/(2*z11 q*z13 q) := by
  unfold z15 z11 z12 z13 z14
  rw [x_rec_even_block q 5]
  norm_num
  field_simp [x_ne]
  ring

lemma z16_formula (q : ℕ) :
    z16 q = z13 q*z15 q*(1+z13 q*z15 q)/(2*z12 q*z14 q) := by
  unfold z16 z12 z13 z14 z15
  rw [x_rec_odd_block q 6]
  norm_num
  field_simp [x_ne]
  ring

lemma z17_formula (q : ℕ) :
    z17 q = z14 q*z16 q*(1+z14 q*z16 q)/(2*z13 q*z15 q) := by
  unfold z17 z13 z14 z15 z16
  rw [x_rec_even_block q 6]
  norm_num
  field_simp [x_ne]
  ring


/-! ### Elementary 2-adic calculus and the easy half of the block -/

lemma Unit2.mul {q r : ℚ} (hq : Unit2 q) (hr : Unit2 r) : Unit2 (q*r) := by
  refine ⟨mul_ne_zero hq.1 hr.1, ?_⟩
  change padicValRat 2 (q*r) = 0
  rw [padicValRat.mul hq.1 hr.1]
  change v2 q + v2 r = 0
  rw [hq.2, hr.2]
  ring

lemma Unit2.div {q r : ℚ} (hq : Unit2 q) (hr : Unit2 r) : Unit2 (q/r) := by
  refine ⟨div_ne_zero hq.1 hr.1, ?_⟩
  change padicValRat 2 (q/r) = 0
  rw [padicValRat.div hq.1 hr.1]
  change v2 q - v2 r = 0
  rw [hq.2, hr.2]
  ring

lemma unit_den_not_dvd_two {q : ℚ} (hq : Unit2 q) : ¬ 2 ∣ q.den := by
  intro hden
  have hnum : ¬ 2 ∣ q.num.natAbs := by
    intro hn
    have hg : 2 ∣ Nat.gcd q.num.natAbs q.den := Nat.dvd_gcd hn hden
    rw [Nat.Coprime.gcd_eq_one q.reduced] at hg
    norm_num at hg
  have hvnum : padicValInt 2 q.num = 0 := by
    apply padicValInt.eq_zero_of_not_dvd
    intro hd
    exact hnum (Int.ofNat_dvd_left.mp hd)
  have hvden : 1 ≤ padicValNat 2 q.den :=
    one_le_padicValNat_of_dvd q.den_nz hden
  have hv := hq.2
  change (padicValInt 2 q.num : ℤ) - (padicValNat 2 q.den : ℤ) = 0 at hv
  rw [hvnum] at hv
  omega

lemma unit_num_not_dvd_two {q : ℚ} (hq : Unit2 q) : ¬ (2 : ℤ) ∣ q.num := by
  intro hnum
  have hn : 2 ∣ q.num.natAbs := Int.ofNat_dvd_left.mp hnum
  have hden : ¬ 2 ∣ q.den := by
    intro hd
    have hg : 2 ∣ Nat.gcd q.num.natAbs q.den := Nat.dvd_gcd hn hd
    rw [Nat.Coprime.gcd_eq_one q.reduced] at hg
    norm_num at hg
  have hvden : padicValNat 2 q.den = 0 :=
    padicValNat.eq_zero_of_not_dvd hden
  have hnumne : q.num.natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero]
    exact Rat.num_ne_zero.mpr hq.1
  have hvnum : 1 ≤ padicValInt 2 q.num := by
    change 1 ≤ padicValNat 2 q.num.natAbs
    exact one_le_padicValNat_of_dvd hnumne hn
  have hv := hq.2
  change (padicValInt 2 q.num : ℤ) - (padicValNat 2 q.den : ℤ) = 0 at hv
  rw [hvden] at hv
  omega

lemma val_ge_of_dvd {w : ℤ} {e : ℕ} (h : (2 ^ e : ℤ) ∣ w) :
    w = 0 ∨ (e : ℤ) ≤ padicValRat 2 (w : ℚ) := by
  rcases eq_or_ne w 0 with rfl | hne
  · left; rfl
  · right
    obtain ⟨k, hk⟩ := h
    have hkne : k ≠ 0 := by rintro rfl; simp at hk; exact hne hk
    rw [hk]
    push_cast
    rw [padicValRat.mul (by positivity) (by exact_mod_cast hkne)]
    have hp : padicValRat 2 ((2 : ℚ)^e) = e := v2_two_pow e
    rw [hp]
    have hkval : 0 ≤ padicValRat 2 (k : ℚ) := by
      rw [padicValRat.of_int]
      positivity
    omega

lemma unit_one_add_val {q : ℚ} (hq : Unit2 q) (hadd : q + 1 ≠ 0) :
    1 ≤ v2 (q + 1) := by
  let N : ℤ := q.num + q.den
  have hnmod : q.num % 2 = 1 :=
    Int.two_dvd_ne_zero.mp (unit_num_not_dvd_two hq)
  have hdmodN : q.den % 2 = 1 :=
    Nat.two_dvd_ne_zero.mp (unit_den_not_dvd_two hq)
  have hdmodI : (q.den : ℤ) % 2 = 1 := by exact_mod_cast hdmodN
  have hNdiv : (2 : ℤ) ∣ N := by
    apply Int.dvd_iff_emod_eq_zero.mpr
    dsimp [N]
    omega
  have heq : q + 1 = (N : ℚ) / (q.den : ℚ) := by
    calc
      q + 1 = (q.num : ℚ) / (q.den : ℚ) + 1 := by rw [q.num_div_den]
      _ = (N : ℚ) / (q.den : ℚ) := by
        dsimp [N]
        push_cast
        field_simp
  have hNne : N ≠ 0 := by
    intro hzero
    apply hadd
    rw [heq, hzero]
    norm_num
  have hvN : (1 : ℤ) ≤ padicValRat 2 (N : ℚ) :=
    (val_ge_of_dvd hNdiv).resolve_left hNne
  have hdenne : (q.den : ℚ) ≠ 0 := by positivity
  have hvden : padicValRat 2 (q.den : ℚ) = 0 := by
    rw [padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd (unit_den_not_dvd_two hq)]
    rfl
  change 1 ≤ padicValRat 2 (q + 1)
  rw [heq, padicValRat.div (by exact_mod_cast hNne) hdenne, hvden]
  simpa using hvN

lemma one_add_val_eq_zero_of_pos {q : ℚ} (hq : q ≠ 0)
    (hsum : 1+q ≠ 0) (hpos : 0 < v2 q) : v2 (1+q) = 0 := by
  have hsum' : q+1 ≠ 0 := by rwa [add_comm]
  have hone : v2 (1:ℚ) = 0 := by
    change padicValRat 2 (1:ℚ) = 0
    exact padicValRat.one
  have hvne : v2 q ≠ v2 (1:ℚ) := by rw [hone]; omega
  have hv := padicValRat.add_eq_min hsum' hq one_ne_zero hvne
  change v2 (q+1) = min (v2 q) (v2 (1:ℚ)) at hv
  rw [hone, min_eq_right (le_of_lt hpos)] at hv
  rwa [add_comm] at hv

lemma one_add_val_nonneg {q : ℚ} (hsum : 1+q ≠ 0)
    (hq : 0 ≤ v2 q) : 0 ≤ v2 (1+q) := by
  have h := padicValRat.min_le_padicValRat_add
    (p := 2) (q := (1:ℚ)) (r := q) hsum
  have hone : v2 (1:ℚ) = 0 := by
    change padicValRat 2 (1:ℚ) = 0
    exact padicValRat.one
  change min (v2 (1:ℚ)) (v2 q) ≤ v2 (1+q) at h
  rw [hone, min_eq_left hq] at h
  exact h

lemma unit_one_add_of_pos {q : ℚ} (hq : q ≠ 0)
    (hsum : 1+q ≠ 0) (hpos : 0 < v2 q) : Unit2 (1+q) :=
  ⟨hsum, one_add_val_eq_zero_of_pos hq hsum hpos⟩

lemma v2_four : v2 (4 : ℚ) = 2 := by
  have h := v2_two_pow 2
  norm_num at h ⊢
  exact h

lemma z4_nonneg_generic {a0 a1 a2 a3 y4 : ℚ}
    (ha0 : Unit2 a0) (ha1 : Unit2 a1)
    (ha2 : Unit2 a2) (ha3 : Unit2 a3)
    (hsum : 1 + a1*a3 ≠ 0)
    (hy : y4 = a1*a3*(1+a1*a3)/(2*a0*a2)) :
    0 ≤ v2 y4 := by
  have hp : Unit2 (a1*a3) := ha1.mul ha3
  have hadd : 1 ≤ v2 (1+a1*a3) := by
    rw [add_comm]
    exact unit_one_add_val hp (by rwa [add_comm])
  have hnum : a1*a3*(1+a1*a3) ≠ 0 := mul_ne_zero hp.1 hsum
  have hden : 2*a0*a2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) ha0.1) ha2.1
  rw [hy]
  change 0 ≤ padicValRat 2 (a1*a3*(1+a1*a3)/(2*a0*a2))
  rw [padicValRat.div hnum hden,
    padicValRat.mul hp.1 hsum,
    padicValRat.mul (mul_ne_zero (by norm_num) ha0.1) ha2.1,
    padicValRat.mul (by norm_num) ha0.1]
  change 0 ≤ v2 (a1*a3) + v2 (1+a1*a3) -
      (v2 (2:ℚ) + v2 a0 + v2 a2)
  rw [hp.2, ha0.2, ha2.2]
  have htwo : v2 (2 : ℚ) = 1 := by
    change padicValRat 2 (2 : ℚ) = 1
    rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num,
      padicValRat.self (by norm_num)]
  rw [htwo]
  omega

lemma z5_nonneg_generic {a1 a2 a3 y4 y5 : ℚ}
    (ha1 : Unit2 a1) (ha2 : Unit2 a2) (ha3 : Unit2 a3)
    (hy4ne : y4 ≠ 0) (hy4 : 0 ≤ v2 y4)
    (hA : 1+a2*y4 ≠ 0)
    (hy : y5 = a2*y4*(1+a2*y4)/(2*a1*a3)) :
    0 ≤ v2 y5 := by
  have hupne : a2*y4 ≠ 0 := mul_ne_zero ha2.1 hy4ne
  have hnum : a2*y4*(1+a2*y4) ≠ 0 := mul_ne_zero hupne hA
  have hden : 2*a1*a3 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) ha1.1) ha3.1
  have hval : v2 y5 = v2 y4 + v2 (1+a2*y4) - 1 := by
    rw [hy]
    change padicValRat 2 (a2*y4*(1+a2*y4)/(2*a1*a3)) =
      v2 y4 + v2 (1+a2*y4) - 1
    rw [padicValRat.div hnum hden,
      padicValRat.mul hupne hA,
      padicValRat.mul ha2.1 hy4ne,
      padicValRat.mul (mul_ne_zero (by norm_num) ha1.1) ha3.1,
      padicValRat.mul (by norm_num) ha1.1]
    change v2 a2 + v2 y4 + v2 (1+a2*y4) -
      (v2 (2:ℚ) + v2 a1 + v2 a3) =
      v2 y4 + v2 (1+a2*y4) - 1
    rw [ha1.2, ha2.2, ha3.2]
    have htwo : v2 (2 : ℚ) = 1 := by
      change padicValRat 2 (2 : ℚ) = 1
      rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num,
        padicValRat.self (by norm_num)]
    rw [htwo]
    ring
  by_cases hy0 : v2 y4 = 0
  · have hyunit : Unit2 y4 := ⟨hy4ne, hy0⟩
    have hpunit : Unit2 (a2*y4) := ha2.mul hyunit
    have hA1 : 1 ≤ v2 (1+a2*y4) := by
      rw [add_comm]
      exact unit_one_add_val hpunit (by rwa [add_comm])
    rw [hval, hy0]
    omega
  · have hypos : 0 < v2 y4 := lt_of_le_of_ne hy4 (Ne.symm hy0)
    have hprodpos : 0 < v2 (a2*y4) := by
      change 0 < padicValRat 2 (a2*y4)
      rw [padicValRat.mul ha2.1 hy4ne]
      change 0 < v2 a2 + v2 y4
      rw [ha2.2]
      omega
    have hA0 := one_add_val_eq_zero_of_pos hupne hA hprodpos
    rw [hval, hA0]
    omega

lemma initial_cancellation (q : ℕ) (h : TubeAt (14*q)) :
    0 ≤ v2 (z4 q) ∧ 0 ≤ v2 (z5 q) ∧ 0 ≤ v2 (z6 q) ∧
      Unit2 (z7 q) ∧ Unit2 (z8 q) := by
  unfold TubeAt at h
  have hu0 : Unit2 (u0 q) := by simpa [u0] using h.1
  have hu1 : Unit2 (u1 q) := by simpa [u1] using h.2.1
  have hu2 : Unit2 (u2 q) := by simpa [u2] using h.2.2.1
  have hu3 : Unit2 (u3 q) := by
    refine ⟨u3_ne q, ?_⟩
    change padicValRat 2 (x (14*q+3)/16) = 0
    rw [padicValRat.div (x_ne _) (by norm_num)]
    change v2 (x (14*q+3)) - v2 (16:ℚ) = 0
    rw [h.2.2.2.1.2, v2_16]
    ring
  have hsum4 : 1+u1 q*u3 q ≠ 0 := by
    unfold u1 u3
    have h1 := x_pos (14*q+1)
    have h3 := x_pos (14*q+3)
    positivity
  have hz4 : 0 ≤ v2 (z4 q) :=
    z4_nonneg_generic hu0 hu1 hu2 hu3 hsum4 (z4_formula q)
  have hA : 1+u2 q*z4 q ≠ 0 := by
    unfold u2 z4
    have h2 := x_pos (14*q+2)
    have h4 := x_pos (14*q+4)
    positivity
  have hz5 : 0 ≤ v2 (z5 q) :=
    z5_nonneg_generic hu1 hu2 hu3 (z4_ne q) hz4 hA (z5_formula q)
  have hup : 0 ≤ v2 (u2 q*z4 q) := by
    change 0 ≤ padicValRat 2 (u2 q*z4 q)
    rw [padicValRat.mul hu2.1 (z4_ne q)]
    change 0 ≤ v2 (u2 q) + v2 (z4 q)
    rw [hu2.2]
    simpa using hz4
  have hAval : 0 ≤ v2 (1+u2 q*z4 q) :=
    one_add_val_nonneg hA hup
  let yB := 16*u3 q*z5 q
  have hyBne : yB ≠ 0 := by
    dsimp [yB]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hu3.1) (z5_ne q)
  have hyBpos : 0 < v2 yB := by
    change 0 < padicValRat 2 (16*u3 q*z5 q)
    rw [padicValRat.mul (mul_ne_zero (by norm_num) hu3.1) (z5_ne q),
      padicValRat.mul (by norm_num) hu3.1]
    change 0 < v2 (16:ℚ) + v2 (u3 q) + v2 (z5 q)
    rw [v2_16, hu3.2]
    omega
  have hBsum : 1+yB ≠ 0 := by
    dsimp [yB, u3, z5]
    have h3 := x_pos (14*q+3)
    have h5 := x_pos (14*q+5)
    positivity
  have hB : Unit2 (1+yB) :=
    unit_one_add_of_pos hyBne hBsum hyBpos
  have hz6 : 0 ≤ v2 (z6 q) := by
    rw [z6_formula q]
    change 0 ≤ padicValRat 2
      ((1+u2 q*z4 q)*(1+16*u3 q*z5 q)/u1 q)
    rw [padicValRat.div (mul_ne_zero hA hB.1) hu1.1,
      padicValRat.mul hA hB.1]
    change 0 ≤ v2 (1+u2 q*z4 q) + v2 (1+16*u3 q*z5 q) -
      v2 (u1 q)
    change 0 ≤ v2 (1+u2 q*z4 q) + v2 (1+yB) - v2 (u1 q)
    rw [hB.2, hu1.2]
    simpa using hAval
  let yC := 4*z4 q*z6 q
  have hyCne : yC ≠ 0 := by
    dsimp [yC]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (z4_ne q)) (z6_ne q)
  have hyCpos : 0 < v2 yC := by
    change 0 < padicValRat 2 (4*z4 q*z6 q)
    rw [padicValRat.mul (mul_ne_zero (by norm_num) (z4_ne q)) (z6_ne q),
      padicValRat.mul (by norm_num) (z4_ne q)]
    change 0 < v2 (4:ℚ) + v2 (z4 q) + v2 (z6 q)
    rw [v2_four]
    omega
  have hCsum : 1+yC ≠ 0 := by
    dsimp [yC, z4, z6]
    have h4 := x_pos (14*q+4)
    have h6 := x_pos (14*q+6)
    positivity
  have hC : Unit2 (1+yC) :=
    unit_one_add_of_pos hyCne hCsum hyCpos
  have hz7 : Unit2 (z7 q) := by
    rw [z7_formula q]
    change Unit2 ((1+yB)*(1+yC)/u2 q)
    exact (hB.mul hC).div hu2
  let yD := 4*z5 q*z7 q
  have hyDne : yD ≠ 0 := by
    dsimp [yD]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (z5_ne q)) hz7.1
  have hyDpos : 0 < v2 yD := by
    change 0 < padicValRat 2 (4*z5 q*z7 q)
    rw [padicValRat.mul (mul_ne_zero (by norm_num) (z5_ne q)) hz7.1,
      padicValRat.mul (by norm_num) (z5_ne q)]
    change 0 < v2 (4:ℚ) + v2 (z5 q) + v2 (z7 q)
    rw [v2_four, hz7.2]
    omega
  have hDsum : 1+yD ≠ 0 := by
    dsimp [yD, z5, z7]
    have h5 := x_pos (14*q+5)
    have h7 := x_pos (14*q+7)
    positivity
  have hD : Unit2 (1+yD) :=
    unit_one_add_of_pos hyDne hDsum hyDpos
  have hz8 : Unit2 (z8 q) := by
    rw [z8_formula q]
    change Unit2 ((1+yC)*(1+yD)/u3 q)
    exact (hC.mul hD).div hu3
  exact ⟨hz4, hz5, hz6, hz7, hz8⟩


/-! ### The first exceptional cancellation: the term z9 -/

def A4 (q : ℕ) : ℚ := 1+u2 q*z4 q
def B5 (q : ℕ) : ℚ := 1+16*u3 q*z5 q
def C6 (q : ℕ) : ℚ := 1+4*z4 q*z6 q
def D7 (q : ℕ) : ℚ := 1+4*z5 q*z7 q
def E9 (q : ℕ) : ℚ :=
  (u1 q*u3 q + A4 q*B5 q*C6 q*D7 q) / z4 q

lemma z7_ne (q : ℕ) : z7 q ≠ 0 := by
  unfold z7
  exact div_ne_zero (x_ne _) (by norm_num)

lemma A4_ne (q : ℕ) : A4 q ≠ 0 := by
  unfold A4 u2 z4
  have h2 := x_pos (14*q+2)
  have h4 := x_pos (14*q+4)
  positivity

lemma B5_ne (q : ℕ) : B5 q ≠ 0 := by
  unfold B5 u3 z5
  have h3 := x_pos (14*q+3)
  have h5 := x_pos (14*q+5)
  positivity

lemma C6_ne (q : ℕ) : C6 q ≠ 0 := by
  unfold C6 z4 z6
  have h4 := x_pos (14*q+4)
  have h6 := x_pos (14*q+6)
  positivity

lemma z9_eq_D7_mul_E9 (q : ℕ) :
    z9 q = D7 q*E9 q/(u1 q*u3 q) := by
  let A := A4 q
  let B := B5 q
  let C := C6 q
  let D := D7 q
  let p := u1 q*u3 q
  have hp : p ≠ 0 := mul_ne_zero (u1_ne q) (u3_ne q)
  have h68 : z6 q*z8 q = A*B*C*D/p := by
    dsimp [A, B, C, D, p, A4, B5, C6, D7]
    rw [z8_formula q, z6_formula q]
    field_simp [u1_ne, u3_ne]
  have hone : 1+z6 q*z8 q = (p+A*B*C*D)/p := by
    rw [h68]
    field_simp [hp]
  have hden : 2*z5 q*z7 q = z4 q*A*B*C/p := by
    dsimp [A, B, C, p, A4, B5, C6]
    rw [z7_formula q, z5_formula q]
    field_simp [u1_ne, u2_ne, u3_ne]
  rw [z9_formula q, hone, h68]
  apply (div_eq_iff
    (mul_ne_zero (mul_ne_zero (by norm_num) (z5_ne q)) (z7_ne q))).2
  rw [hden]
  dsimp [A, B, C, D, p, E9, A4, B5, C6, D7]
  field_simp [u1_ne, u3_ne, z4_ne]

lemma unit_B5 (q : ℕ) (hu3 : Unit2 (u3 q))
    (hz5 : 0 ≤ v2 (z5 q)) : Unit2 (B5 q) := by
  let y := 16*u3 q*z5 q
  have hyne : y ≠ 0 := by
    dsimp [y]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hu3.1) (z5_ne q)
  have hypos : 0 < v2 y := by
    change 0 < padicValRat 2 (16*u3 q*z5 q)
    rw [padicValRat.mul (mul_ne_zero (by norm_num) hu3.1) (z5_ne q),
      padicValRat.mul (by norm_num) hu3.1]
    change 0 < v2 (16:ℚ) + v2 (u3 q) + v2 (z5 q)
    rw [v2_16, hu3.2]
    omega
  have hsum : 1+y ≠ 0 := by
    dsimp [y, u3, z5]
    have h3 := x_pos (14*q+3)
    have h5 := x_pos (14*q+5)
    positivity
  change Unit2 (1+y)
  exact unit_one_add_of_pos hyne hsum hypos

lemma unit_C6 (q : ℕ) (hz4 : 0 ≤ v2 (z4 q))
    (hz6 : 0 ≤ v2 (z6 q)) : Unit2 (C6 q) := by
  let y := 4*z4 q*z6 q
  have hyne : y ≠ 0 := by
    dsimp [y]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (z4_ne q)) (z6_ne q)
  have hypos : 0 < v2 y := by
    change 0 < padicValRat 2 (4*z4 q*z6 q)
    rw [padicValRat.mul (mul_ne_zero (by norm_num) (z4_ne q)) (z6_ne q),
      padicValRat.mul (by norm_num) (z4_ne q)]
    change 0 < v2 (4:ℚ) + v2 (z4 q) + v2 (z6 q)
    rw [v2_four]
    omega
  have hsum : 1+y ≠ 0 := by
    dsimp [y, z4, z6]
    have h4 := x_pos (14*q+4)
    have h6 := x_pos (14*q+6)
    positivity
  change Unit2 (1+y)
  exact unit_one_add_of_pos hyne hsum hypos

lemma unit_D7 (q : ℕ) (hz5 : 0 ≤ v2 (z5 q))
    (hz7 : Unit2 (z7 q)) : Unit2 (D7 q) := by
  let y := 4*z5 q*z7 q
  have hyne : y ≠ 0 := by
    dsimp [y]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (z5_ne q)) hz7.1
  have hypos : 0 < v2 y := by
    change 0 < padicValRat 2 (4*z5 q*z7 q)
    rw [padicValRat.mul (mul_ne_zero (by norm_num) (z5_ne q)) hz7.1,
      padicValRat.mul (by norm_num) (z5_ne q)]
    change 0 < v2 (4:ℚ) + v2 (z5 q) + v2 (z7 q)
    rw [v2_four, hz7.2]
    omega
  have hsum : 1+y ≠ 0 := by
    dsimp [y, z5, z7]
    have h5 := x_pos (14*q+5)
    have h7 := x_pos (14*q+7)
    positivity
  change Unit2 (1+y)
  exact unit_one_add_of_pos hyne hsum hypos

def VGe (k : ℤ) (q : ℚ) : Prop := q = 0 ∨ k ≤ v2 q

lemma VGe.add {k : ℤ} {q r : ℚ} (hq : VGe k q) (hr : VGe k r) :
    VGe k (q+r) := by
  rcases hq with rfl | hq
  · simpa using hr
  rcases hr with rfl | hr
  · simpa using (Or.inr hq : VGe k q)
  by_cases hs : q+r=0
  · exact Or.inl hs
  · right
    have h := padicValRat.min_le_padicValRat_add
      (p:=2) (q:=q) (r:=r) hs
    change min (v2 q) (v2 r) ≤ v2 (q+r) at h
    omega

lemma VGe.mul_right_unit {k : ℤ} {q r : ℚ}
    (hq : VGe k q) (hr : Unit2 r) : VGe k (q*r) := by
  rcases hq with rfl | hq
  · left; ring
  · by_cases hq0 : q=0
    · left; rw [hq0]; ring
    · right
      change k ≤ padicValRat 2 (q*r)
      rw [padicValRat.mul hq0 hr.1]
      change k ≤ v2 q + v2 r
      rw [hr.2]
      simpa using hq

lemma VGe.mul_left_unit {k : ℤ} {q r : ℚ}
    (hq : VGe k q) (hr : Unit2 r) : VGe k (r*q) := by
  rw [mul_comm]
  exact hq.mul_right_unit hr


lemma one_add_ne_of_val_pos {q : ℚ} (hpos : 0 < v2 q) : 1+q ≠ 0 := by
  intro hs
  have heq : q = -1 := by linarith
  have hv : v2 q = 0 := by
    rw [heq]
    change padicValRat 2 (-(1:ℚ)) = 0
    rw [padicValRat.neg, padicValRat.one]
  omega

lemma add_ne_zero_of_val_ne {q r : ℚ}
    (hv : v2 q ≠ v2 r) : q+r ≠ 0 := by
  intro hs
  have heq : q = -r := by linarith
  apply hv
  rw [heq]
  change padicValRat 2 (-r) = v2 r
  rw [padicValRat.neg]

lemma E9_unit (q : ℕ) (h : TubeAt (14*q)) : Unit2 (E9 q) := by
  unfold TubeAt at h
  have hu0 : Unit2 (u0 q) := by simpa [u0] using h.1
  have hu1 : Unit2 (u1 q) := by simpa [u1] using h.2.1
  have hu2 : Unit2 (u2 q) := by simpa [u2] using h.2.2.1
  have hu3 : Unit2 (u3 q) := by
    refine ⟨u3_ne q, ?_⟩
    change padicValRat 2 (x (14*q+3)/16) = 0
    rw [padicValRat.div (x_ne _) (by norm_num)]
    change v2 (x (14*q+3)) - v2 (16:ℚ) = 0
    rw [h.2.2.2.1.2, v2_16]
    ring
  rcases initial_cancellation q (by simpa [TubeAt] using h) with
    ⟨hz4, hz5, hz6, hz7, hz8⟩
  have hB : Unit2 (B5 q) := unit_B5 q hu3 hz5
  have hC : Unit2 (C6 q) := unit_C6 q hz4 hz6
  have hD : Unit2 (D7 q) := unit_D7 q hz5 hz7
  let A := A4 q
  let B := B5 q
  let C := C6 q
  let D := D7 q
  let p := u1 q*u3 q
  let Q := B*C*D
  let N := p+A*Q
  have hBu : Unit2 B := by simpa [B] using hB
  have hCu : Unit2 C := by simpa [C] using hC
  have hDu : Unit2 D := by simpa [D] using hD
  have hp : Unit2 p := hu1.mul hu3
  have hQ : Unit2 Q := (hBu.mul hCu).mul hDu
  let α := v2 (z4 q)
  by_cases hα0 : α = 0
  · have hz4unit : Unit2 (z4 q) := ⟨z4_ne q, hα0⟩
    have hprod : Unit2 (u2 q*z4 q) := hu2.mul hz4unit
    have hAval : 1 ≤ v2 A := by
      dsimp [A, A4]
      rw [add_comm]
      exact unit_one_add_val hprod (by
        rw [add_comm]
        exact A4_ne q)
    have hAQne : A*Q ≠ 0 := mul_ne_zero (A4_ne q) hQ.1
    have hAQval : v2 (A*Q) = v2 A := by
      change padicValRat 2 (A*Q) = v2 A
      rw [padicValRat.mul (A4_ne q) hQ.1]
      change v2 A + v2 Q = v2 A
      rw [hQ.2]
      ring
    have hvalne : v2 p ≠ v2 (A*Q) := by
      rw [hp.2, hAQval]
      omega
    have hNne : N ≠ 0 := by
      dsimp [N]
      exact add_ne_zero_of_val_ne hvalne
    have hNval : v2 N = 0 := by
      have hv := padicValRat.add_eq_min hNne hp.1 hAQne hvalne
      change v2 N = min (v2 p) (v2 (A*Q)) at hv
      rw [hp.2, hAQval, min_eq_left (by omega)] at hv
      exact hv
    have hNunit : Unit2 N := ⟨hNne, hNval⟩
    unfold E9
    convert hNunit.div hz4unit using 1 ;
      dsimp [N, Q, p, A, B, C, D] ; ring
  · have hαpos : 0 < α := by
      dsimp [α]
      omega
    have hprodne : u2 q*z4 q ≠ 0 :=
      mul_ne_zero hu2.1 (z4_ne q)
    have hprodval : v2 (u2 q*z4 q) = α := by
      change padicValRat 2 (u2 q*z4 q) = α
      rw [padicValRat.mul hu2.1 (z4_ne q)]
      change v2 (u2 q) + v2 (z4 q) = α
      rw [hu2.2]
      dsimp [α]
      ring
    have hAunit : Unit2 A := by
      have hpos : 0 < v2 (u2 q*z4 q) := by rw [hprodval]; exact hαpos
      have hsum : 1+u2 q*z4 q ≠ 0 := one_add_ne_of_val_pos hpos
      dsimp [A, A4]
      exact unit_one_add_of_pos hprodne hsum hpos
    have hz5val : v2 (z5 q) = α-1 := by
      have hnum : u2 q*z4 q*A ≠ 0 :=
        mul_ne_zero hprodne hAunit.1
      have hden : 2*u1 q*u3 q ≠ 0 :=
        mul_ne_zero (mul_ne_zero (by norm_num) hu1.1) hu3.1
      rw [z5_formula q]
      change padicValRat 2 (u2 q*z4 q*A/(2*u1 q*u3 q)) = α-1
      rw [padicValRat.div hnum hden,
        padicValRat.mul hprodne hAunit.1,
        padicValRat.mul hu2.1 (z4_ne q),
        padicValRat.mul (mul_ne_zero (by norm_num) hu1.1) hu3.1,
        padicValRat.mul (by norm_num) hu1.1]
      change v2 (u2 q) + v2 (z4 q) + v2 A -
        (v2 (2:ℚ) + v2 (u1 q) + v2 (u3 q)) = α-1
      rw [hu1.2, hu2.2, hu3.2, hAunit.2]
      have htwo : v2 (2:ℚ) = 1 := by
        change padicValRat 2 (2:ℚ) = 1
        rw [show (2:ℚ) = ((2:ℕ):ℚ) by norm_num,
          padicValRat.self (by norm_num)]
      rw [htwo]
      dsimp [α]
      ring
    have hz6unit : Unit2 (z6 q) := by
      rw [z6_formula q]
      change Unit2 (A*B/u1 q)
      exact (hAunit.mul hBu).div hu1
    have hBdev : VGe (α+1) (B-1) := by
      right
      have heq : B-1 = 16*u3 q*z5 q := by
        dsimp [B, B5]
        ring
      rw [heq]
      change α+1 ≤ padicValRat 2 (16*u3 q*z5 q)
      rw [padicValRat.mul (mul_ne_zero (by norm_num) hu3.1) (z5_ne q),
        padicValRat.mul (by norm_num) hu3.1]
      change α+1 ≤ v2 (16:ℚ) + v2 (u3 q) + v2 (z5 q)
      rw [v2_16, hu3.2, hz5val]
      omega
    have hCdev : VGe (α+1) (C-1) := by
      right
      have heq : C-1 = 4*z4 q*z6 q := by
        dsimp [C, C6]
        ring
      rw [heq]
      change α+1 ≤ padicValRat 2 (4*z4 q*z6 q)
      rw [padicValRat.mul (mul_ne_zero (by norm_num) (z4_ne q)) hz6unit.1,
        padicValRat.mul (by norm_num) (z4_ne q)]
      change α+1 ≤ v2 (4:ℚ) + v2 (z4 q) + v2 (z6 q)
      rw [v2_four, hz6unit.2]
      omega
    have hDdev : VGe (α+1) (D-1) := by
      right
      have heq : D-1 = 4*z5 q*z7 q := by
        dsimp [D, D7]
        ring
      rw [heq]
      change α+1 ≤ padicValRat 2 (4*z5 q*z7 q)
      rw [padicValRat.mul (mul_ne_zero (by norm_num) (z5_ne q)) hz7.1,
        padicValRat.mul (by norm_num) (z5_ne q)]
      change α+1 ≤ v2 (4:ℚ) + v2 (z5 q) + v2 (z7 q)
      rw [v2_four, hz5val, hz7.2]
      omega
    have hQdev : VGe (α+1) (Q-1) := by
      have heq : Q-1 = (B-1)*C*D + (C-1)*D + (D-1) := by
        dsimp [Q]
        ring
      rw [heq]
      simpa only [add_assoc] using
        (((hBdev.mul_right_unit hCu).mul_right_unit hDu).add
          ((hCdev.mul_right_unit hDu).add hDdev))
    let R := A*(Q-1)
    have hRge : VGe (α+1) R := hQdev.mul_left_unit hAunit
    let r := u0 q/p
    have hr : Unit2 r := hu0.div hp
    let t := 2*r
    have htne : t ≠ 0 := by
      dsimp [t]
      exact mul_ne_zero (by norm_num) hr.1
    have htval : v2 t = 1 := by
      change padicValRat 2 (2*r) = 1
      rw [padicValRat.mul (by norm_num) hr.1]
      change v2 (2:ℚ) + v2 r = 1
      rw [hr.2]
      have htwo : v2 (2:ℚ) = 1 := by
        change padicValRat 2 (2:ℚ) = 1
        rw [show (2:ℚ) = ((2:ℕ):ℚ) by norm_num,
          padicValRat.self (by norm_num)]
      rw [htwo]
      ring
    have htpos : 0 < v2 t := by rw [htval]; norm_num
    have htadd : 1+t ≠ 0 := one_add_ne_of_val_pos htpos
    have htunit : Unit2 (1+t) :=
      unit_one_add_of_pos htne htadd htpos
    let K := u2 q*(1+t)
    have hK : Unit2 K := hu2.mul htunit
    let base := z4 q*K
    have hbaseNe : base ≠ 0 := by
      dsimp [base]
      exact mul_ne_zero (z4_ne q) hK.1
    have hbaseVal : v2 base = α := by
      change padicValRat 2 (z4 q*K) = α
      rw [padicValRat.mul (z4_ne q) hK.1]
      change v2 (z4 q) + v2 K = α
      rw [hK.2]
      ring
    have hp1 : 1+u1 q*u3 q =
        2*u0 q*u2 q*z4 q/(u1 q*u3 q) := by
      rw [z4_formula q]
      field_simp [hu0.1, hu1.1, hu2.1, hu3.1]
    have hdecomp : N = base+R := by
      dsimp [N, base, R, K, t, r, Q, p, A, A4, B, C, D]
      field_simp [hu1.1, hu3.1]
      field_simp [hu1.1, hu3.1] at hp1
      linear_combination hp1
    have hNne : N ≠ 0 := by
      rw [hdecomp]
      by_cases hR0 : R=0
      · rw [hR0, add_zero]
        exact hbaseNe
      · have hRv := hRge.resolve_left hR0
        apply add_ne_zero_of_val_ne
        rw [hbaseVal]
        omega
    have hNval : v2 N = α := by
      rw [hdecomp]
      by_cases hR0 : R=0
      · rw [hR0, add_zero]
        exact hbaseVal
      · have hRv := hRge.resolve_left hR0
        have hvne : v2 base ≠ v2 R := by rw [hbaseVal]; omega
        have hv := padicValRat.add_eq_min
          (by rw [← hdecomp]; exact hNne) hbaseNe hR0 hvne
        change v2 (base+R) = min (v2 base) (v2 R) at hv
        rw [hbaseVal, min_eq_left (by omega)] at hv
        exact hv
    have hNne' :
        u1 q*u3 q+A4 q*B5 q*C6 q*D7 q ≠ 0 := by
      convert hNne using 1 ;
        dsimp [N, Q, p, A, B, C, D] ; ring
    have hNval' :
        v2 (u1 q*u3 q+A4 q*B5 q*C6 q*D7 q) = α := by
      convert hNval using 1 ;
        dsimp [N, Q, p, A, B, C, D] ; ring_nf
    refine ⟨?_, ?_⟩
    · unfold E9
      exact div_ne_zero hNne' (z4_ne q)
    · change padicValRat 2
        ((u1 q*u3 q+A4 q*B5 q*C6 q*D7 q)/z4 q) = 0
      rw [padicValRat.div hNne' (z4_ne q)]
      change v2 (u1 q*u3 q+A4 q*B5 q*C6 q*D7 q) -
        v2 (z4 q) = 0
      rw [hNval']
      dsimp [α]
      ring


lemma z9_unit (q : ℕ) (h : TubeAt (14*q)) : Unit2 (z9 q) := by
  unfold TubeAt at h
  have hu1 : Unit2 (u1 q) := by simpa [u1] using h.2.1
  have hu3 : Unit2 (u3 q) := by
    refine ⟨u3_ne q, ?_⟩
    change padicValRat 2 (x (14*q+3)/16) = 0
    rw [padicValRat.div (x_ne _) (by norm_num)]
    change v2 (x (14*q+3)) - v2 (16:ℚ) = 0
    rw [h.2.2.2.1.2, v2_16]
    ring
  rcases initial_cancellation q (by simpa [TubeAt] using h) with
    ⟨hz4, hz5, hz6, hz7, hz8⟩
  have hD : Unit2 (D7 q) := unit_D7 q hz5 hz7
  rw [z9_eq_D7_mul_E9 q]
  exact (hD.mul (E9_unit q (by simpa [TubeAt] using h))).div (hu1.mul hu3)



lemma Unit2.neg {q : ℚ} (hq : Unit2 q) : Unit2 (-q) := by
  refine ⟨neg_ne_zero.mpr hq.1, ?_⟩
  change padicValRat 2 (-q)=0
  rw [padicValRat.neg]
  exact hq.2

lemma close4_symm {q r : ℚ} (h : Close4 q r) : Close4 r q := by
  rcases h with rfl | h
  · left; rfl
  · right
    change 2 ≤ padicValRat 2 (r-q)
    rw [show r-q=-(q-r) by ring, padicValRat.neg]
    exact h

lemma close4_cases {q r : ℚ} (h : Close4 q r) :
    q=r ∨ (q-r ≠ 0 ∧ 2 ≤ v2 (q-r)) := by
  rcases h with h | h
  · exact Or.inl h
  · by_cases heq : q=r
    · exact Or.inl heq
    · exact Or.inr ⟨sub_ne_zero.mpr heq, h⟩

lemma close4_trans {q r s : ℚ} (h1 : Close4 q r) (h2 : Close4 r s) :
    Close4 q s := by
  rcases close4_cases h1 with rfl | ⟨h1ne,h1v⟩
  · exact h2
  rcases close4_cases h2 with rfl | ⟨h2ne,h2v⟩
  · exact Or.inr h1v
  by_cases hqs : q=s
  · exact Or.inl hqs
  · right
    have heq : q-s=(q-r)+(r-s) := by ring
    rw [heq]
    have hv := padicValRat.min_le_padicValRat_add
      (p:=2) (q:=q-r) (r:=r-s)
      (by rw [← heq]; exact sub_ne_zero.mpr hqs)
    change min (v2 (q-r)) (v2 (r-s)) ≤ v2 ((q-r)+(r-s)) at hv
    omega

lemma close4_mul {q r Q R : ℚ}
    (hq : Unit2 q) (hR : Unit2 R)
    (h1 : Close4 q Q) (h2 : Close4 r R) :
    Close4 (q*r) (Q*R) := by
  have hs1 : Close4 (q*r) (q*R) := by
    rcases close4_cases h2 with rfl | ⟨hne,hv⟩
    · left; rfl
    · right
      change 2 ≤ padicValRat 2 (q*r-q*R)
      rw [show q*r-q*R=q*(r-R) by ring,
        padicValRat.mul hq.1 hne]
      change 2 ≤ v2 q+v2 (r-R)
      rw [hq.2]
      simpa using hv
  have hs2 : Close4 (q*R) (Q*R) := by
    rcases close4_cases h1 with rfl | ⟨hne,hv⟩
    · left; rfl
    · right
      change 2 ≤ padicValRat 2 (q*R-Q*R)
      rw [show q*R-Q*R=(q-Q)*R by ring,
        padicValRat.mul hne hR.1]
      change 2 ≤ v2 (q-Q)+v2 R
      rw [hR.2]
      simpa using hv
  exact close4_trans hs1 hs2

lemma eight_dvd_sq_sub_one {m : ℤ} (hm : ¬ (2 : ℤ) ∣ m) :
    (8 : ℤ) ∣ m^2-1 := by
  have hne : ¬ Even m := by rwa [even_iff_two_dvd]
  have ho : Odd m := Int.not_even_iff_odd.mp hne
  rcases ho with ⟨k,hk⟩
  have hp : Even (k*(k+1)) := Int.even_mul_succ_self k
  obtain ⟨j,hj⟩ := even_iff_two_dvd.mp hp
  refine ⟨j, ?_⟩
  rw [hk]
  nlinarith

lemma unit_sq_sub_one_val {q : ℚ} (hq : Unit2 q)
    (hsub : q^2-1 ≠ 0) : 3 ≤ v2 (q^2-1) := by
  let N : ℤ := q.num^2-(q.den:ℤ)^2
  have hn8 := eight_dvd_sq_sub_one (unit_num_not_dvd_two hq)
  have hdnot : ¬(2:ℤ) ∣ (q.den:ℤ) := by
    intro hd
    exact unit_den_not_dvd_two hq (Int.ofNat_dvd.mp hd)
  have hd8 := eight_dvd_sq_sub_one hdnot
  have hNdiv : (2^3:ℤ) ∣ N := by
    obtain ⟨j,hj⟩ := hn8
    obtain ⟨k,hk⟩ := hd8
    refine ⟨j-k, ?_⟩
    dsimp [N]
    nlinarith
  have heq : q^2-1=(N:ℚ)/((q.den:ℚ)^2) := by
    calc
      q^2-1=((q.num:ℚ)/(q.den:ℚ))^2-1 := by rw [q.num_div_den]
      _=(N:ℚ)/((q.den:ℚ)^2) := by
        dsimp [N]
        push_cast
        field_simp
  have hNne : N ≠ 0 := by
    intro hz
    apply hsub
    rw [heq,hz]
    norm_num
  have hvN : (3:ℤ) ≤ padicValRat 2 (N:ℚ) :=
    (val_ge_of_dvd hNdiv).resolve_left hNne
  have hdenne : ((q.den:ℚ)^2) ≠ 0 := by positivity
  have hvden : padicValRat 2 ((q.den:ℚ)^2)=0 := by
    rw [padicValRat.pow (by positivity), padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd (unit_den_not_dvd_two hq)]
    rfl
  change 3 ≤ padicValRat 2 (q^2-1)
  rw [heq,padicValRat.div (by exact_mod_cast hNne) hdenne,hvden]
  simpa using hvN

def q10 (q : ℕ) : ℚ := (1+z7 q*z9 q)/(8*z6 q)
def q15 (q : ℕ) : ℚ := (1+z12 q*z14 q)/z10 q
def q16 (q : ℕ) : ℚ := (1+z13 q*z15 q)/(2*z12 q)

lemma z8_ne (q : ℕ) : z8 q ≠ 0 := by
  unfold z8
  exact mul_ne_zero (by norm_num) (x_ne _)

lemma z10_ne (q : ℕ) : z10 q ≠ 0 := by
  unfold z10
  exact div_ne_zero (x_ne _) (by norm_num)
lemma z11_ne (q : ℕ) : z11 q ≠ 0 := by
  unfold z11
  exact div_ne_zero (x_ne _) (by norm_num)
lemma z12_ne (q : ℕ) : z12 q ≠ 0 := by unfold z12; exact x_ne _
lemma z13_ne (q : ℕ) : z13 q ≠ 0 := by
  unfold z13
  exact div_ne_zero (x_ne _) (by norm_num)
lemma z14_ne (q : ℕ) : z14 q ≠ 0 := by unfold z14; exact x_ne _
lemma z15_ne (q : ℕ) : z15 q ≠ 0 := by unfold z15; exact x_ne _
lemma z16_ne (q : ℕ) : z16 q ≠ 0 := by unfold z16; exact x_ne _
lemma z17_ne (q : ℕ) : z17 q ≠ 0 := by
  unfold z17
  exact div_ne_zero (x_ne _) (by norm_num)

lemma q10_ne (q : ℕ) : q10 q ≠ 0 := by
  unfold q10 z6 z7 z9
  have h6 := x_pos (14*q+6)
  have h7 := x_pos (14*q+7)
  have h9 := x_pos (14*q+9)
  positivity

lemma q15_ne (q : ℕ) : q15 q ≠ 0 := by
  unfold q15 z10 z12 z14
  have h10 := x_pos (14*q+10)
  have h12 := x_pos (14*q+12)
  have h14 := x_pos (14*q+14)
  positivity

lemma q16_ne (q : ℕ) : q16 q ≠ 0 := by
  unfold q16 z12 z13 z15
  have h12 := x_pos (14*q+12)
  have h13 := x_pos (14*q+13)
  have h15 := x_pos (14*q+15)
  positivity

lemma unit_one_add_four_mul {r s : ℚ}
    (hr : r ≠ 0) (hs : s ≠ 0)
    (hvr : 0 ≤ v2 r) (hvs : 0 ≤ v2 s) :
    Unit2 (1+4*r*s) := by
  have hyne : 4*r*s ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hr) hs
  have hypos : 0 < v2 (4*r*s) := by
    change 0 < padicValRat 2 (4*r*s)
    rw [padicValRat.mul (mul_ne_zero (by norm_num) hr) hs,
      padicValRat.mul (by norm_num) hr]
    change 0 < v2 (4:ℚ)+v2 r+v2 s
    rw [v2_four]
    omega
  exact unit_one_add_of_pos hyne (one_add_ne_of_val_pos hypos) hypos

lemma unit_one_add_sixteen_mul {r s : ℚ}
    (hr : r ≠ 0) (hs : s ≠ 0)
    (hvr : 0 ≤ v2 r) (hvs : 0 ≤ v2 s) :
    Unit2 (1+16*r*s) := by
  have hyne : 16*r*s ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hr) hs
  have hypos : 0 < v2 (16*r*s) := by
    change 0 < padicValRat 2 (16*r*s)
    rw [padicValRat.mul (mul_ne_zero (by norm_num) hr) hs,
      padicValRat.mul (by norm_num) hr]
    change 0 < v2 (16:ℚ)+v2 r+v2 s
    rw [v2_16]
    omega
  exact unit_one_add_of_pos hyne (one_add_ne_of_val_pos hypos) hypos

lemma z10_eq_q10 (q : ℕ) :
    z10 q = (z7 q*z9 q/z8 q)*q10 q := by
  unfold q10
  rw [z10_formula q]
  field_simp [z6_ne, z8_ne]

/-- The five genuinely finite congruence checks left after the z9 cancellation. -/

def Nonneg2' (q : ℚ) : Prop := q ≠ 0 ∧ 0 ≤ v2 q

lemma VGe.mul' {k l : ℤ} {q r : ℚ} (hq : VGe k q) (hr : VGe l r) :
    VGe (k+l) (q*r) := by
  rcases hq with rfl | hq
  · left; ring
  rcases hr with rfl | hr
  · left; ring
  by_cases hq0 : q=0
  · left; rw [hq0]; ring
  by_cases hr0 : r=0
  · left; rw [hr0]; ring
  right
  change k+l ≤ padicValRat 2 (q*r)
  rw [padicValRat.mul hq0 hr0]
  change k+l ≤ v2 q+v2 r
  omega

lemma close4_iff_vge' {q r : ℚ} : Close4 q r ↔ VGe 2 (q-r) := by
  constructor
  · rintro (h | h)
    · left; exact sub_eq_zero.mpr h
    · exact Or.inr h
  · rintro (h | h)
    · left; exact sub_eq_zero.mp h
    · exact Or.inr h

lemma close4_add' {q r Q R : ℚ}
    (h1 : Close4 q Q) (h2 : Close4 r R) :
    Close4 (q+r) (Q+R) := by
  rw [close4_iff_vge'] at h1 h2 ⊢
  have h := h1.add h2
  convert h using 1 ; ring

lemma close4_neg'2 {q r : ℚ} (h : Close4 q r) : Close4 (-q) (-r) := by
  rw [close4_iff_vge'] at h ⊢
  rcases h with h | h
  · left; linarith
  · by_cases hz : -q- -r=0
    · exact Or.inl hz
    · right
      change 2 ≤ padicValRat 2 (-q- -r)
      rw [show -q- -r=-(q-r) by ring, padicValRat.neg]
      exact h

lemma close4_mul_nonneg' {q r Q R : ℚ}
    (hq : Nonneg2' q) (hR : Nonneg2' R)
    (h1 : Close4 q Q) (h2 : Close4 r R) :
    Close4 (q*r) (Q*R) := by
  have hs1 : Close4 (q*r) (q*R) := by
    rw [close4_iff_vge'] at h2 ⊢
    have hq0 : VGe 0 q := Or.inr hq.2
    have hm := hq0.mul' h2
    convert hm using 1 ; ring
  have hs2 : Close4 (q*R) (Q*R) := by
    rw [close4_iff_vge'] at h1 ⊢
    have hR0 : VGe 0 R := Or.inr hR.2
    have hm := h1.mul' hR0
    convert hm using 1 ; ring
  exact close4_trans hs1 hs2

lemma unit_sub_one_vge' (q : ℚ) (hq : Unit2 q) : VGe 1 (q-1) := by
  by_cases heq : q=1
  · left; rw [heq]; ring
  · right
    have hne : -q+1 ≠ 0 := by
      intro hz
      apply heq
      calc
        q = q+(-q+1) := by rw [hz]; ring
        _ = 1 := by ring
    have hv := unit_one_add_val hq.neg hne
    change 1 ≤ padicValRat 2 (-q+1) at hv
    rw [show -q+1=-(q-1) by ring, padicValRat.neg] at hv
    exact hv

lemma two_mul_unit_close_two' {q : ℚ} (hq : Unit2 q) :
    Close4 (2*q) 2 := by
  rw [close4_iff_vge']
  have htwo : VGe 1 (2:ℚ) := by
    right
    change 1 ≤ padicValRat 2 (2:ℚ)
    rw [show (2:ℚ)=((2:ℕ):ℚ) by norm_num,
      padicValRat.self (by norm_num)]
  have hm := htwo.mul' (unit_sub_one_vge' q hq)
  convert hm using 1 ; ring

lemma unit_sq_close_one' {q : ℚ} (hq : Unit2 q) : Close4 (q^2) 1 := by
  by_cases heq : q^2=1
  · exact Or.inl heq
  · right
    have hsub : q^2-1 ≠ 0 := sub_ne_zero.mpr heq
    have h := unit_sq_sub_one_val hq hsub
    omega

lemma nonneg_mul' {q r : ℚ} (hq : Nonneg2' q) (hr : Nonneg2' r) :
    Nonneg2' (q*r) := by
  refine ⟨mul_ne_zero hq.1 hr.1, ?_⟩
  change 0 ≤ padicValRat 2 (q*r)
  rw [padicValRat.mul hq.1 hr.1]
  change 0 ≤ v2 q+v2 r
  exact add_nonneg hq.2 hr.2

lemma unit_nonneg' {q : ℚ} (hq : Unit2 q) : Nonneg2' q :=
  ⟨hq.1, by rw [hq.2]⟩

lemma unit_of_close4' {q r : ℚ} (hr : Unit2 r)
    (hqr : Close4 q r) (hqne : q ≠ 0) : Unit2 q := by
  refine ⟨hqne, ?_⟩
  rcases close4_cases hqr with heq | ⟨hdne,hdv⟩
  · rw [heq, hr.2]
  · have hsum : (q-r)+r ≠ 0 := by
      simpa only [sub_add_cancel] using hqne
    have hvne : v2 (q-r) ≠ v2 r := by
      rw [hr.2]
      omega
    have hv := padicValRat.add_eq_min hsum hdne hr.1 hvne
    change v2 ((q-r)+r) = min (v2 (q-r)) (v2 r) at hv
    rw [hr.2, min_eq_right (by omega)] at hv
    simpa only [sub_add_cancel] using hv

lemma VGe.neg' {k : ℤ} {q : ℚ} (hq : VGe k q) : VGe k (-q) := by
  rcases hq with rfl | hq
  · left; ring
  · by_cases hz : -q=0
    · exact Or.inl hz
    · right
      change k ≤ padicValRat 2 (-q)
      rw [padicValRat.neg]
      exact hq

def p10b (q : ℕ) : ℚ := u1 q*u3 q
def s10b (q : ℕ) : ℚ := 2*z4 q*A4 q/p10b q
def L10b (q : ℕ) : ℚ := (B5 q*C6 q*D7 q-1)/s10b q
def F10b (q : ℕ) : ℚ :=
  u0 q*u2 q+(p10b q+2*A4 q)*L10b q+A4 q*s10b q*(L10b q)^2

lemma u0_ne (q : ℕ) : u0 q ≠ 0 := by unfold u0; exact x_ne _

lemma p10b_ne (q : ℕ) : p10b q ≠ 0 := by
  unfold p10b
  exact mul_ne_zero (u1_ne q) (u3_ne q)

lemma s10b_ne (q : ℕ) : s10b q ≠ 0 := by
  unfold s10b
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) (z4_ne q)) (A4_ne q))
    (p10b_ne q)

lemma B5_s10b_formula (q : ℕ) :
    B5 q=1+4*u2 q*u3 q*s10b q := by
  unfold B5 s10b p10b A4
  rw [z5_formula q]
  field_simp [u1_ne,u3_ne] ; ring

lemma C6_s10b_formula (q : ℕ) :
    C6 q=1+2*u3 q*s10b q*B5 q := by
  unfold C6 s10b p10b A4 B5
  rw [z6_formula q]
  field_simp [u1_ne,u3_ne] ; ring

lemma D7_s10b_formula (q : ℕ) :
    D7 q=1+s10b q*B5 q*C6 q := by
  unfold D7 s10b p10b A4 B5 C6
  rw [z7_formula q,z5_formula q]
  field_simp [u1_ne,u2_ne,u3_ne] ; ring

lemma L10b_formula (q : ℕ) :
    L10b q=4*u2 q*u3 q+2*u3 q*(B5 q)^2+(B5 q*C6 q)^2 := by
  have hBm : B5 q-1=4*u2 q*u3 q*s10b q := by
    linarith [B5_s10b_formula q]
  have hBC : B5 q*C6 q-1=
      s10b q*(4*u2 q*u3 q+2*u3 q*(B5 q)^2) := by
    calc
      B5 q*C6 q-1 =
          B5 q*(1+2*u3 q*s10b q*B5 q)-1 := by
            rw [C6_s10b_formula q]
      _ = (B5 q-1)+2*u3 q*s10b q*(B5 q)^2 := by ring
      _ = s10b q*(4*u2 q*u3 q+2*u3 q*(B5 q)^2) := by
            rw [hBm]
            ring
  unfold L10b
  rw [D7_s10b_formula q]
  apply (div_eq_iff (s10b_ne q)).2
  linear_combination hBC

lemma p10b_add_one (q : ℕ) :
    p10b q+1=2*z4 q*(u0 q*u2 q/p10b q) := by
  unfold p10b
  rw [z4_formula q]
  field_simp [u0_ne,u1_ne,u2_ne,u3_ne] ; ring

lemma z4_p10b_identity (q : ℕ) :
    2*u0 q*u2 q*z4 q=p10b q*(1+p10b q) := by
  unfold p10b
  rw [z4_formula q]
  field_simp [u0_ne,u1_ne,u2_ne,u3_ne]

lemma z7_p10b_formula (q : ℕ) :
    z7 q=B5 q*C6 q/u2 q := z7_formula q

lemma z6_p10b_formula (q : ℕ) :
    z6 q=A4 q*B5 q/u1 q := z6_formula q

lemma z9_p10b_formula (q : ℕ) :
    z9 q=D7 q*(p10b q+A4 q*B5 q*C6 q*D7 q)/
      (z4 q*p10b q) := by
  rw [z9_eq_D7_mul_E9 q]
  unfold p10b E9
  field_simp [u1_ne,u3_ne,z4_ne]

lemma q10_F10b_formula5 (q : ℕ) :
    q10 q=F10b q*u1 q/(4*u2 q*(p10b q)^2*B5 q) := by
  let Q : ℚ := B5 q*C6 q*D7 q
  have hsum : 1+z7 q*z9 q=
      (A4 q*(p10b q+Q^2)+p10b q*(Q-1))/
        (u2 q*p10b q*z4 q) := by
    rw [z7_p10b_formula q,z9_p10b_formula q]
    dsimp [Q]
    field_simp [u2_ne,p10b_ne,z4_ne]
    unfold A4
    ring
  have hsL : s10b q*L10b q=Q-1 := by
    unfold L10b
    dsimp [Q]
    field_simp [s10b_ne]
  have hbase : A4 q*(p10b q+1)=s10b q*(u0 q*u2 q) := by
    calc
      A4 q*(p10b q+1) =
          A4 q*(p10b q*(1+p10b q))/p10b q := by
            field_simp [p10b_ne] ; ring
      _ = A4 q*(2*u0 q*u2 q*z4 q)/p10b q := by
            rw [z4_p10b_identity q]
      _ = s10b q*(u0 q*u2 q) := by
            unfold s10b
            ring
  have hfactor :
      A4 q*(p10b q+Q^2)+p10b q*(Q-1)=s10b q*F10b q := by
    have hQ : Q=1+s10b q*L10b q := by linarith [hsL]
    rw [hQ]
    unfold F10b
    nlinarith [hbase]
  unfold q10
  rw [hsum,hfactor,z6_p10b_formula q]
  unfold s10b
  field_simp [u1_ne,u2_ne,p10b_ne,A4_ne,B5_ne,z4_ne] ; ring

lemma tube_normalized_units (q : ℕ) (h : TubeAt (14*q)) :
    Unit2 (u0 q) ∧ Unit2 (u1 q) ∧ Unit2 (u2 q) ∧ Unit2 (u3 q) := by
  unfold TubeAt at h
  have hu0 : Unit2 (u0 q) := by simpa [u0] using h.1
  have hu1 : Unit2 (u1 q) := by simpa [u1] using h.2.1
  have hu2 : Unit2 (u2 q) := by simpa [u2] using h.2.2.1
  have hu3 : Unit2 (u3 q) := by
    refine ⟨u3_ne q, ?_⟩
    change padicValRat 2 (x (14*q+3)/16)=0
    rw [padicValRat.div (x_ne _) (by norm_num)]
    change v2 (x (14*q+3))-v2 (16:ℚ)=0
    rw [h.2.2.2.1.2,v2_16]
    ring
  exact ⟨hu0,hu1,hu2,hu3⟩

lemma A4_nonneg (q : ℕ) (h : TubeAt (14*q)) : Nonneg2' (A4 q) := by
  obtain ⟨hu0,hu1,hu2,hu3⟩ := tube_normalized_units q h
  rcases initial_cancellation q h with ⟨hz4,hz5,hz6,hz7,hz8⟩
  have hpv : 0 ≤ v2 (u2 q*z4 q) := by
    change 0 ≤ padicValRat 2 (u2 q*z4 q)
    rw [padicValRat.mul hu2.1 (z4_ne q)]
    change 0 ≤ v2 (u2 q)+v2 (z4 q)
    rw [hu2.2]
    simpa using hz4
  exact ⟨A4_ne q,one_add_val_nonneg (A4_ne q) hpv⟩

lemma s10b_nonneg2 (q : ℕ) (h : TubeAt (14*q)) : Nonneg2' (s10b q) := by
  obtain ⟨hu0,hu1,hu2,hu3⟩ := tube_normalized_units q h
  rcases initial_cancellation q h with ⟨hz4,hz5,hz6,hz7,hz8⟩
  have hp : Unit2 (p10b q) := by unfold p10b; exact hu1.mul hu3
  have hA := A4_nonneg q h
  refine ⟨s10b_ne q, ?_⟩
  unfold s10b
  change 0 ≤ padicValRat 2 (2*z4 q*A4 q/p10b q)
  rw [padicValRat.div
      (mul_ne_zero (mul_ne_zero (by norm_num) (z4_ne q)) hA.1) hp.1,
    padicValRat.mul (mul_ne_zero (by norm_num) (z4_ne q)) hA.1,
    padicValRat.mul (by norm_num) (z4_ne q)]
  change 0 ≤ v2 (2:ℚ)+v2 (z4 q)+v2 (A4 q)-v2 (p10b q)
  rw [hp.2]
  have htwo : v2 (2:ℚ)=1 := by
    change padicValRat 2 (2:ℚ)=1
    rw [show (2:ℚ)=((2:ℕ):ℚ) by norm_num,
      padicValRat.self (by norm_num)]
  rw [htwo]
  have hAv : 0 ≤ v2 (A4 q) := hA.2
  omega

lemma L10b_close_neg_one2 (q : ℕ) (h : TubeAt (14*q)) :
    Close4 (L10b q) (-1) := by
  obtain ⟨hu0,hu1,hu2,hu3⟩ := tube_normalized_units q h
  rcases initial_cancellation q h with ⟨hz4,hz5,hz6,hz7,hz8⟩
  have hB : Unit2 (B5 q) := unit_B5 q hu3 hz5
  have hC : Unit2 (C6 q) := unit_C6 q hz4 hz6
  have hterm1 : Close4 (4*u2 q*u3 q) 0 := by
    rw [close4_iff_vge']
    have hfour : VGe 2 (4:ℚ) := by
      right
      change 2 ≤ v2 (4:ℚ)
      rw [v2_four]
    have hunit : VGe 0 (u2 q*u3 q) :=
      Or.inr (by rw [(hu2.mul hu3).2])
    have hm := hfour.mul' hunit
    convert hm using 1 ; ring
  have hterm2 : Close4 (2*u3 q*(B5 q)^2) 2 := by
    have hB2 : Unit2 ((B5 q)^2) := by
      simpa [pow_two] using hB.mul hB
    have hUB : Unit2 (u3 q*(B5 q)^2) := hu3.mul hB2
    convert two_mul_unit_close_two' hUB using 1 ; ring
  have hterm3 : Close4 ((B5 q*C6 q)^2) 1 :=
    unit_sq_close_one' (hB.mul hC)
  have hs12 := close4_add' hterm1 hterm2
  have hs123 := close4_add' hs12 hterm3
  have hL3 : Close4 (L10b q) 3 := by
    rw [L10b_formula q]
    convert hs123 using 1 ; norm_num
  have h3neg : Close4 (3:ℚ) (-1) := by
    right
    change 2 ≤ padicValRat 2 ((3:ℚ)-(-1))
    norm_num
    change 2 ≤ v2 (4:ℚ)
    rw [v2_four]
  exact close4_trans hL3 h3neg

lemma p10b_close2 (q : ℕ) (h : TubeAt (14*q)) :
    Close4 (p10b q) (2*z4 q-1) := by
  obtain ⟨hu0,hu1,hu2,hu3⟩ := tube_normalized_units q h
  rcases initial_cancellation q h with ⟨hz4,hz5,hz6,hz7,hz8⟩
  have hp : Unit2 (p10b q) := by unfold p10b; exact hu1.mul hu3
  let W : ℚ := u0 q*u2 q/p10b q
  have hW : Unit2 W := by dsimp [W]; exact (hu0.mul hu2).div hp
  have hw1 := unit_sub_one_vge' W hW
  have htwo : VGe 1 (2:ℚ) := by
    right
    change 1 ≤ padicValRat 2 (2:ℚ)
    rw [show (2:ℚ)=((2:ℕ):ℚ) by norm_num,
      padicValRat.self (by norm_num)]
  have hz0 : VGe 0 (z4 q) := Or.inr hz4
  have hm := (htwo.mul' hz0).mul' hw1
  rw [close4_iff_vge']
  have heq : p10b q-(2*z4 q-1)=2*z4 q*(W-1) := by
    calc
      p10b q-(2*z4 q-1)=p10b q+1-2*z4 q := by ring
      _=2*z4 q*W-2*z4 q := by rw [p10b_add_one q]
      _=2*z4 q*(W-1) := by ring
  rw [heq]
  simpa using hm

lemma s10b_close2 (q : ℕ) (h : TubeAt (14*q)) :
    Close4 (s10b q) (2*z4 q*A4 q) := by
  obtain ⟨hu0,hu1,hu2,hu3⟩ := tube_normalized_units q h
  rcases initial_cancellation q h with ⟨hz4,hz5,hz6,hz7,hz8⟩
  have hp : Unit2 (p10b q) := by unfold p10b; exact hu1.mul hu3
  have hA := A4_nonneg q h
  have hpinv : Unit2 (1/p10b q) := by
    exact (show Unit2 (1:ℚ) from ⟨one_ne_zero,padicValRat.one⟩).div hp
  have hw1 := unit_sub_one_vge' (1/p10b q) hpinv
  have htwo : VGe 1 (2:ℚ) := by
    right
    change 1 ≤ padicValRat 2 (2:ℚ)
    rw [show (2:ℚ)=((2:ℕ):ℚ) by norm_num,
      padicValRat.self (by norm_num)]
  have hz0 : VGe 0 (z4 q) := Or.inr hz4
  have hA0 : VGe 0 (A4 q) := Or.inr hA.2
  have hm := ((htwo.mul' hz0).mul' hA0).mul' hw1
  rw [close4_iff_vge']
  have heq : s10b q-2*z4 q*A4 q=
      2*z4 q*A4 q*(1/p10b q-1) := by
    unfold s10b
    field_simp [p10b_ne]
  rw [heq]
  simpa using hm

lemma parity_target_close_zero_d {u z : ℚ}
    (hu : Unit2 u) (hz : Nonneg2' z) :
    Close4 (2*z*((1+u*z)^2-u-1)) 0 := by
  have htwo1 : VGe 1 (2:ℚ) := by
    right
    change 1 ≤ padicValRat 2 (2:ℚ)
    rw [show (2:ℚ)=((2:ℕ):ℚ) by norm_num,
      padicValRat.self (by norm_num)]
  have htwo0 : VGe 0 (2:ℚ) := by
    right
    change 0 ≤ padicValRat 2 (2:ℚ)
    rw [show (2:ℚ)=((2:ℕ):ℚ) by norm_num,
      padicValRat.self (by norm_num)]
    norm_num
  have hu0 : VGe 0 u := Or.inr (by rw [hu.2])
  have hz0 : VGe 0 z := Or.inr hz.2
  have hW : VGe 1 (z*((1+u*z)^2-u-1)) := by
    have hfac : (1+u*z)^2-u-1=u*(2*z+u*z^2-1) := by ring
    rw [hfac]
    by_cases hzunit : v2 z=0
    · have hzu : Unit2 z := ⟨hz.1,hzunit⟩
      have hz2u : Unit2 (z^2) := by
        simpa [pow_two] using hzu.mul hzu
      have huz2 : Unit2 (u*z^2) := hu.mul hz2u
      have hfirst : VGe 1 (2*z) := by
        have hm := VGe.mul' htwo1
          (Or.inr (by rw [hzu.2]) : VGe 0 z)
        simpa using hm
      have hsecond : VGe 1 (u*z^2-1) :=
        unit_sub_one_vge' _ huz2
      have hinside : VGe 1 (2*z+u*z^2-1) := by
        have hh := hfirst.add hsecond
        convert hh using 1 ; ring
      have hm := VGe.mul' (VGe.mul'
        (Or.inr (by rw [hzu.2]) : VGe 0 z) hu0) hinside
      convert hm using 1 ; ring
    · have hz1 : 1 ≤ v2 z := by
        have hznonneg := hz.2
        omega
      have hz1v : VGe 1 z := Or.inr hz1
      have hz2v : VGe 0 (z^2) := by
        have hm := VGe.mul' hz0 hz0
        simpa [pow_two] using hm
      have hone0 : VGe 0 (-(1:ℚ)) := by
        right
        change 0 ≤ padicValRat 2 (-(1:ℚ))
        rw [padicValRat.neg,padicValRat.one]
      have hinside0 : VGe 0 (2*z+u*z^2-1) := by
        have hfirst := VGe.mul' htwo0 hz0
        have hsecond := VGe.mul' hu0 hz2v
        have hh := (hfirst.add hsecond).add hone0
        convert hh using 1 ; ring
      have hm := VGe.mul' (VGe.mul' hz1v hu0) hinside0
      convert hm using 1 ; ring
  rw [close4_iff_vge']
  have hm := VGe.mul' htwo1 hW
  convert hm using 1 ; ring

lemma F10b_close_zero_d (q : ℕ) (h : TubeAt (14*q)) :
    Close4 (F10b q) 0 := by
  obtain ⟨hu0,hu1,hu2,hu3⟩ := tube_normalized_units q h
  rcases initial_cancellation q h with ⟨hz4,hz5,hz6,hz7,hz8⟩
  have ht := h
  unfold TubeAt at ht
  have hclose02 : Close4 (u0 q) (u2 q) := by
    simpa [u0,u2] using ht.2.2.2.2
  have hp : Unit2 (p10b q) := by unfold p10b; exact hu1.mul hu3
  have hA := A4_nonneg q h
  have hs := s10b_nonneg2 q h
  have hLclose := L10b_close_neg_one2 q h
  have hu2p : 0 < u2 q := by unfold u2; exact x_pos _
  have hu3p : 0 < u3 q := by
    unfold u3
    exact div_pos (x_pos _) (by norm_num)
  have hz5p : 0 < z5 q := by
    unfold z5
    exact div_pos (x_pos _) (by norm_num)
  have hz4p : 0 < z4 q := by unfold z4; exact x_pos _
  have hz6p : 0 < z6 q := by
    unfold z6
    exact div_pos (x_pos _) (by norm_num)
  have hBp : 0 < B5 q := by unfold B5; positivity
  have hCp : 0 < C6 q := by unfold C6; positivity
  have hLpos : 0 < L10b q := by
    rw [L10b_formula q]
    positivity
  have hL : Unit2 (L10b q) := by
    have hm : Unit2 (-1:ℚ) := by
      norm_num [Unit2,padicValRat.neg,padicValRat.one]
    exact unit_of_close4' hm hLclose hLpos.ne'
  have hu02 : Close4 (u0 q*u2 q) 1 := by
    have hprod : Close4 (u0 q*u2 q) (u0 q*u0 q) :=
      close4_mul hu0 hu0 (Or.inl rfl) (close4_symm hclose02)
    have hsq : Close4 (u0 q*u0 q) 1 := by
      convert unit_sq_close_one' hu0 using 1 ; ring
    exact close4_trans hprod hsq
  have hpu : Unit2 (p10b q+2*A4 q) := by
    let y : ℚ := 2*A4 q/p10b q
    have hyne : y ≠ 0 := by
      dsimp [y]
      exact div_ne_zero (mul_ne_zero (by norm_num) hA.1) hp.1
    have hypos : 0 < v2 y := by
      dsimp [y]
      change 0 < padicValRat 2 (2*A4 q/p10b q)
      rw [padicValRat.div (mul_ne_zero (by norm_num) hA.1) hp.1,
        padicValRat.mul (by norm_num) hA.1]
      change 0 < v2 (2:ℚ)+v2 (A4 q)-v2 (p10b q)
      rw [hp.2]
      have htwo : v2 (2:ℚ)=1 := by
        change padicValRat 2 (2:ℚ)=1
        rw [show (2:ℚ)=((2:ℕ):ℚ) by norm_num,
          padicValRat.self (by norm_num)]
      rw [htwo]
      have hAv := hA.2
      omega
    have hyu : Unit2 (1+y) :=
      unit_one_add_of_pos hyne (one_add_ne_of_val_pos hypos) hypos
    have heq : p10b q+2*A4 q=p10b q*(1+y) := by
      dsimp [y]
      field_simp [p10b_ne]
    rw [heq]
    exact hp.mul hyu
  have hcoef : Close4 (p10b q+2*A4 q)
      ((2*z4 q-1)+2*A4 q) :=
    close4_add' (p10b_close2 q h) (Or.inl rfl)
  have hminus : Unit2 (-1:ℚ) := by
    norm_num [Unit2,padicValRat.neg,padicValRat.one]
  have hmulL : Close4 ((p10b q+2*A4 q)*L10b q)
      (((2*z4 q-1)+2*A4 q)*(-1)) :=
    close4_mul hpu hminus hcoef hLclose
  have hLsq : Close4 ((L10b q)^2) 1 := unit_sq_close_one' hL
  have htwoN : Nonneg2' (2:ℚ) := by
    refine ⟨by norm_num, ?_⟩
    change 0 ≤ padicValRat 2 (2:ℚ)
    rw [show (2:ℚ)=((2:ℕ):ℚ) by norm_num,
      padicValRat.self (by norm_num)]
    norm_num
  have hzN : Nonneg2' (z4 q) := ⟨z4_ne q,hz4⟩
  have honeN : Nonneg2' (1:ℚ) :=
    unit_nonneg' ⟨one_ne_zero,padicValRat.one⟩
  have htwozA : Nonneg2' (2*z4 q*A4 q) :=
    nonneg_mul' (nonneg_mul' htwoN hzN) hA
  have htwozA1 : Nonneg2' ((2*z4 q*A4 q)*1) :=
    nonneg_mul' htwozA honeN
  have hsL2 : Close4 (s10b q*(L10b q)^2)
      ((2*z4 q*A4 q)*1) :=
    close4_mul_nonneg' hs honeN (s10b_close2 q h) hLsq
  have hAsL2 : Close4 (A4 q*(s10b q*(L10b q)^2))
      (A4 q*((2*z4 q*A4 q)*1)) :=
    close4_mul_nonneg' hA htwozA1 (Or.inl rfl) hsL2
  have hsum := close4_add' (close4_add' hu02 hmulL) hAsL2
  have hsum' : Close4 (F10b q)
      (1+((2*z4 q-1)+2*A4 q)*(-1)+
        A4 q*((2*z4 q*A4 q)*1)) := by
    simpa only [F10b, mul_assoc] using hsum
  have htarget :
      1+((2*z4 q-1)+2*A4 q)*(-1)+A4 q*((2*z4 q*A4 q)*1) =
        2*z4 q*((1+u2 q*z4 q)^2-u2 q-1) := by
    unfold A4
    ring
  rw [htarget] at hsum'
  exact close4_trans hsum' (parity_target_close_zero_d hu2 hzN)

set_option maxHeartbeats 800000 in
lemma q10_nonneg_proved_e (q : ℕ) (h : TubeAt (14*q)) :
    0 ≤ v2 (q10 q) := by
  obtain ⟨hu0,hu1,hu2,hu3⟩ := tube_normalized_units q h
  rcases initial_cancellation q h with ⟨hz4,hz5,hz6,hz7,hz8⟩
  have hp : Unit2 (p10b q) := by unfold p10b; exact hu1.mul hu3
  have hB : Unit2 (B5 q) := unit_B5 q hu3 hz5
  have hp2 : Unit2 ((p10b q)^2) := by
    simpa [pow_two] using hp.mul hp
  have hdenU : Unit2 (u2 q*(p10b q)^2*B5 q) :=
    (hu2.mul hp2).mul hB
  have hFne : F10b q ≠ 0 := by
    intro hz
    apply q10_ne q
    rw [q10_F10b_formula5 q,hz]
    norm_num
  have hFval : 2 ≤ v2 (F10b q) := by
    rcases F10b_close_zero_d q h with heq | hv
    · exact absurd heq hFne
    · simpa using hv
  rw [q10_F10b_formula5 q]
  rw [show 4*u2 q*(p10b q)^2*B5 q =
      4*(u2 q*(p10b q)^2*B5 q) by ring]
  change 0 ≤ padicValRat 2
    (F10b q*u1 q/(4*(u2 q*(p10b q)^2*B5 q)))
  rw [padicValRat.div (mul_ne_zero hFne hu1.1)
      (mul_ne_zero (by norm_num) hdenU.1),
    padicValRat.mul hFne hu1.1,
    padicValRat.mul (by norm_num) hdenU.1]
  change 0 ≤ v2 (F10b q)+v2 (u1 q)-
    (v2 (4:ℚ)+v2 (u2 q*(p10b q)^2*B5 q))
  rw [hu1.2,hdenU.2,v2_four]
  omega

def P15 (q : ℕ) : ℚ := z7 q*z9 q
def r15 (q : ℕ) : ℚ := q10 q
def H15 (q : ℕ) : ℚ := 1+P15 q*r15 q
def I15 (q : ℕ) : ℚ := 1+2*z9 q*r15 q*H15 q
def J15 (q : ℕ) : ℚ := 1+4*(z9 q/z8 q)*r15 q*H15 q*I15 q
def K15 (q : ℕ) : ℚ := 1+8*(1/z8 q)*r15 q*H15 q*I15 q*J15 q
def L15 (q : ℕ) : ℚ := (H15 q*I15 q*J15 q*K15 q-1)/r15 q

lemma z6_pos15 (q : ℕ) : 0 < z6 q := by
  unfold z6
  exact div_pos (x_pos _) (by norm_num)

lemma z7_pos15 (q : ℕ) : 0 < z7 q := by
  unfold z7
  exact div_pos (x_pos _) (by norm_num)

lemma z8_pos15_c (q : ℕ) : 0 < z8 q := by
  unfold z8
  have hx := x_pos (14*q+8)
  positivity

lemma z9_pos15_c (q : ℕ) : 0 < z9 q := by
  unfold z9
  exact div_pos (x_pos _) (by norm_num)

lemma z9_ne15_c (q : ℕ) : z9 q ≠ 0 := (z9_pos15_c q).ne'

lemma r15_pos_c (q : ℕ) : 0 < r15 q := by
  unfold r15 q10
  positivity [z6_pos15 q,z7_pos15 q,z9_pos15_c q]

lemma H15_pos_c (q : ℕ) : 0 < H15 q := by
  unfold H15 P15
  positivity [z7_pos15 q,z9_pos15_c q,r15_pos_c q]

lemma I15_pos_c (q : ℕ) : 0 < I15 q := by
  unfold I15
  positivity [z9_pos15_c q,r15_pos_c q,H15_pos_c q]

lemma J15_pos_c (q : ℕ) : 0 < J15 q := by
  unfold J15
  positivity [z8_pos15_c q,z9_pos15_c q,r15_pos_c q,H15_pos_c q,I15_pos_c q]

lemma K15_pos_c (q : ℕ) : 0 < K15 q := by
  unfold K15
  positivity [z8_pos15_c q,r15_pos_c q,H15_pos_c q,I15_pos_c q,J15_pos_c q]

lemma P15_ne_c (q : ℕ) : P15 q ≠ 0 := by
  unfold P15
  exact mul_ne_zero (z7_ne q) (z9_ne15_c q)

lemma r15_ne_c (q : ℕ) : r15 q ≠ 0 := (r15_pos_c q).ne'

lemma z10_formula15_c (q : ℕ) :
    z10 q=P15 q*r15 q/z8 q := by
  rw [z10_eq_q10 q]
  unfold P15 r15
  ring

lemma z11_formula15_c (q : ℕ) :
    z11 q=r15 q*H15 q/2 := by
  rw [z11_formula q,z10_formula15_c q]
  unfold H15 P15
  field_simp [z7_ne,z8_ne,z9_ne15_c,r15_ne_c]

lemma z12_formula15_c (q : ℕ) :
    z12 q=H15 q*I15 q/z7 q := by
  rw [z12_formula q,z10_formula15_c q,z11_formula15_c q]
  unfold I15 P15
  field_simp [z7_ne,z8_ne,z9_ne15_c,r15_ne_c,(H15_pos_c q).ne']
  ring

lemma z13_formula15_c (q : ℕ) :
    z13 q=I15 q*J15 q/z8 q := by
  rw [z13_formula q,z10_formula15_c q,z11_formula15_c q,z12_formula15_c q]
  unfold J15 P15
  field_simp [z7_ne,z8_ne,z9_ne15_c,r15_ne_c,
    (H15_pos_c q).ne',(I15_pos_c q).ne']

lemma z14_formula15_c (q : ℕ) :
    z14 q=J15 q*K15 q/z9 q := by
  rw [z14_formula q,z10_formula15_c q,z11_formula15_c q,
    z12_formula15_c q,z13_formula15_c q]
  unfold K15 P15
  field_simp [z7_ne,z8_ne,z9_ne15_c,r15_ne_c,
    (H15_pos_c q).ne',(I15_pos_c q).ne',(J15_pos_c q).ne']
  ring

lemma L15_formula_c (q : ℕ) :
    L15 q=P15 q+2*z9 q*(H15 q)^2+
      4*(z9 q/z8 q)*(H15 q*I15 q)^2+
      8*(1/z8 q)*(H15 q*I15 q*J15 q)^2 := by
  unfold L15 K15 J15 I15 H15
  field_simp [r15_ne_c,z8_ne]
  ring

set_option maxHeartbeats 800000 in
lemma q15_formula15_e (q : ℕ) :
    q15 q=z8 q/(P15 q)^2*(8*z6 q+L15 q) := by
  unfold q15
  rw [z12_formula15_c q,z14_formula15_c q,z10_formula15_c q]
  unfold L15 r15
  have hq10 : 1+P15 q=8*z6 q*q10 q := by
    unfold q10 P15
    field_simp [z6_ne]
  have hscaled := congrArg (fun t : ℚ => P15 q*t) hq10
  field_simp [z7_ne,z8_ne,z9_ne15_c,q10_ne,P15_ne_c]
  unfold P15 at hscaled ⊢
  ring_nf at hscaled ⊢
  linarith

lemma VGe.weaken' {k l : ℤ} {q : ℚ} (hkl : k ≤ l) (hq : VGe l q) :
    VGe k q := by
  rcases hq with rfl | hq
  · exact Or.inl rfl
  · exact Or.inr (le_trans hkl hq)

lemma vge_of_unit' {q : ℚ} (hq : Unit2 q) : VGe 0 q :=
  Or.inr (by rw [hq.2])

lemma vge_of_nonneg' {q : ℚ} (hq : Nonneg2' q) : VGe 0 q :=
  Or.inr hq.2

lemma vge_two' : VGe 1 (2:ℚ) := by
  right
  change 1 ≤ padicValRat 2 (2:ℚ)
  rw [show (2:ℚ)=((2:ℕ):ℚ) by norm_num,
    padicValRat.self (by norm_num)]

lemma vge_four' : VGe 2 (4:ℚ) := Or.inr (by rw [v2_four])

lemma vge_eight_b : VGe 3 (8:ℚ) := by
  right
  have h := v2_two_pow 3
  norm_num at h ⊢
  omega

lemma unit_add_vge_one_b {u y : ℚ} (hu : Unit2 u)
    (hy : VGe 1 y) (hsum : u+y ≠ 0) : Unit2 (u+y) := by
  refine ⟨hsum, ?_⟩
  rcases hy with rfl | hy
  · simpa using hu.2
  · have hyne : y ≠ 0 := by
      intro heq
      rw [heq] at hy
      norm_num [v2,padicValRat.zero] at hy
    have hvne : v2 u ≠ v2 y := by
      rw [hu.2]
      omega
    have hv := padicValRat.add_eq_min hsum hu.1 hyne hvne
    change v2 (u+y)=min (v2 u) (v2 y) at hv
    rw [hu.2,min_eq_left (by omega)] at hv
    exact hv

def E15b (q : ℕ) : ℚ :=
  2*z9 q*(H15 q)^2+
    4*(z9 q/z8 q)*(H15 q*I15 q)^2+
    8*(1/z8 q)*(H15 q*I15 q*J15 q)^2

lemma L15_eq_P_add_E_b (q : ℕ) : L15 q=P15 q+E15b q := by
  rw [L15_formula_c q]
  unfold E15b
  ring

set_option maxHeartbeats 800000 in
lemma q15_unit_proved_b (q : ℕ) (h : TubeAt (14*q)) : Unit2 (q15 q) := by
  rcases initial_cancellation q h with ⟨hz4,hz5,hz6,hz7,hz8⟩
  have hz9 := z9_unit q h
  have hP : Unit2 (P15 q) := by
    unfold P15
    exact hz7.mul hz9
  have hr : Nonneg2' (r15 q) :=
    ⟨r15_ne_c q, q10_nonneg_proved_e q h⟩
  have hPr : Nonneg2' (P15 q*r15 q) :=
    nonneg_mul' (unit_nonneg' hP) hr
  have hH : Nonneg2' (H15 q) := by
    refine ⟨(H15_pos_c q).ne', ?_⟩
    unfold H15
    exact one_add_val_nonneg (H15_pos_c q).ne' hPr.2
  have hIterm : VGe 1 (2*z9 q*r15 q*H15 q) := by
    have hm := VGe.mul'
      (VGe.mul' (VGe.mul' vge_two' (vge_of_unit' hz9))
        (vge_of_nonneg' hr)) (vge_of_nonneg' hH)
    simpa [add_assoc] using hm
  have hI : Unit2 (I15 q) := by
    unfold I15
    exact unit_add_vge_one_b
      (show Unit2 (1:ℚ) from ⟨one_ne_zero,padicValRat.one⟩)
      hIterm (I15_pos_c q).ne'
  have hz9z8 : Unit2 (z9 q/z8 q) := hz9.div hz8
  have hJterm : VGe 1
      (4*(z9 q/z8 q)*r15 q*H15 q*I15 q) := by
    have hm := VGe.mul'
      (VGe.mul'
        (VGe.mul' (VGe.mul' vge_four' (vge_of_unit' hz9z8))
          (vge_of_nonneg' hr)) (vge_of_nonneg' hH))
      (vge_of_unit' hI)
    have hm2 : VGe 2
        (4*(z9 q/z8 q)*r15 q*H15 q*I15 q) := by
      simpa [add_assoc] using hm
    exact VGe.weaken' (k:=1) (l:=2) (by norm_num) hm2
  have hJ : Unit2 (J15 q) := by
    unfold J15
    exact unit_add_vge_one_b
      (show Unit2 (1:ℚ) from ⟨one_ne_zero,padicValRat.one⟩)
      hJterm (J15_pos_c q).ne'
  have honeDiv8 : Unit2 (1/z8 q) :=
    (show Unit2 (1:ℚ) from ⟨one_ne_zero,padicValRat.one⟩).div hz8
  have hKterm : VGe 1
      (8*(1/z8 q)*r15 q*H15 q*I15 q*J15 q) := by
    have hm := VGe.mul'
      (VGe.mul'
        (VGe.mul'
          (VGe.mul' (VGe.mul' vge_eight_b (vge_of_unit' honeDiv8))
            (vge_of_nonneg' hr)) (vge_of_nonneg' hH))
        (vge_of_unit' hI)) (vge_of_unit' hJ)
    have hm3 : VGe 3
        (8*(1/z8 q)*r15 q*H15 q*I15 q*J15 q) := by
      simpa [add_assoc] using hm
    exact VGe.weaken' (k:=1) (l:=3) (by norm_num) hm3
  have hK : Unit2 (K15 q) := by
    unfold K15
    exact unit_add_vge_one_b
      (show Unit2 (1:ℚ) from ⟨one_ne_zero,padicValRat.one⟩)
      hKterm (K15_pos_c q).ne'
  have hH2 : VGe 0 ((H15 q)^2) := by
    have hm := VGe.mul' (vge_of_nonneg' hH) (vge_of_nonneg' hH)
    simpa [pow_two] using hm
  have hHI2 : VGe 0 ((H15 q*I15 q)^2) := by
    have hHI := VGe.mul' (vge_of_nonneg' hH) (vge_of_unit' hI)
    have hm := VGe.mul' hHI hHI
    simpa [pow_two,add_assoc] using hm
  have hHIJ2 : VGe 0 ((H15 q*I15 q*J15 q)^2) := by
    have hHIJ := VGe.mul'
      (VGe.mul' (vge_of_nonneg' hH) (vge_of_unit' hI))
      (vge_of_unit' hJ)
    have hm := VGe.mul' hHIJ hHIJ
    simpa [pow_two,add_assoc] using hm
  have hE1 : VGe 1 (2*z9 q*(H15 q)^2) := by
    have hm := VGe.mul' (VGe.mul' vge_two' (vge_of_unit' hz9)) hH2
    simpa [add_assoc] using hm
  have hE2 : VGe 1 (4*(z9 q/z8 q)*(H15 q*I15 q)^2) := by
    have hm := VGe.mul' (VGe.mul' vge_four' (vge_of_unit' hz9z8)) hHI2
    have hm2 : VGe 2 (4*(z9 q/z8 q)*(H15 q*I15 q)^2) := by
      simpa [add_assoc] using hm
    exact VGe.weaken' (k:=1) (l:=2) (by norm_num) hm2
  have hE3 : VGe 1 (8*(1/z8 q)*(H15 q*I15 q*J15 q)^2) := by
    have hm := VGe.mul' (VGe.mul' vge_eight_b (vge_of_unit' honeDiv8)) hHIJ2
    have hm3 : VGe 3 (8*(1/z8 q)*(H15 q*I15 q*J15 q)^2) := by
      simpa [add_assoc] using hm
    exact VGe.weaken' (k:=1) (l:=3) (by norm_num) hm3
  have hE : VGe 1 (E15b q) := by
    unfold E15b
    exact (hE1.add hE2).add hE3
  have hPEpos : 0 < P15 q+E15b q := by
    unfold P15 E15b
    positivity [z7_pos15 q,z8_pos15_c q,z9_pos15_c q,
      H15_pos_c q,I15_pos_c q,J15_pos_c q]
  have hL : Unit2 (L15 q) := by
    rw [L15_eq_P_add_E_b q]
    exact unit_add_vge_one_b hP hE hPEpos.ne'
  have hz6N : Nonneg2' (z6 q) := ⟨z6_ne q,hz6⟩
  have h8z6 : VGe 1 (8*z6 q) := by
    have hm := VGe.mul' vge_eight_b (vge_of_nonneg' hz6N)
    have hm3 : VGe 3 (8*z6 q) := by simpa using hm
    exact VGe.weaken' (k:=1) (l:=3) (by norm_num) hm3
  have hMpos : 0 < L15 q+8*z6 q := by
    rw [L15_eq_P_add_E_b q]
    have hz6p := z6_pos15 q
    exact add_pos hPEpos (mul_pos (by norm_num) hz6p)
  have hM : Unit2 (8*z6 q+L15 q) := by
    have hh := unit_add_vge_one_b hL h8z6 hMpos.ne'
    simpa [add_comm] using hh
  have hP2 : Unit2 ((P15 q)^2) := by
    simpa [pow_two] using hP.mul hP
  have hcoef : Unit2 (z8 q/(P15 q)^2) := hz8.div hP2
  rw [q15_formula15_e q]
  exact hcoef.mul hM

def Y16 (q : ℕ) : ℚ := I15 q*J15 q*K15 q
def T16 (q : ℕ) : ℚ := (Y16 q-1)/H15 q
def W16 (q : ℕ) : ℚ := P15 q+(Y16 q)^2+P15 q*T16 q

lemma Y16_pos (q : ℕ) : 0 < Y16 q := by
  unfold Y16
  positivity [I15_pos_c q,J15_pos_c q,K15_pos_c q]

lemma T16_pos_b (q : ℕ) : 0 < T16 q := by
  have hI : 1 < I15 q := by
    unfold I15
    have hp : 0 < 2*z9 q*r15 q*H15 q := by
      positivity [z9_pos15_c q,r15_pos_c q,H15_pos_c q]
    linarith
  have hJ : 1 < J15 q := by
    unfold J15
    have hp : 0 < 4*(z9 q/z8 q)*r15 q*H15 q*I15 q := by
      positivity [z8_pos15_c q,z9_pos15_c q,r15_pos_c q,
        H15_pos_c q,I15_pos_c q]
    linarith
  have hK : 1 < K15 q := by
    unfold K15
    have hp : 0 < 8*(1/z8 q)*r15 q*H15 q*I15 q*J15 q := by
      positivity [z8_pos15_c q,r15_pos_c q,H15_pos_c q,
        I15_pos_c q,J15_pos_c q]
    linarith
  have hIJ : 1 < I15 q*J15 q := by
    have hp := mul_pos (sub_pos.mpr hI) (sub_pos.mpr hJ)
    nlinarith
  have hY : 1 < I15 q*J15 q*K15 q := by
    have hp := mul_pos (sub_pos.mpr hIJ) (sub_pos.mpr hK)
    nlinarith
  unfold T16 Y16
  exact div_pos (sub_pos.mpr hY) (H15_pos_c q)

lemma W16_pos_b (q : ℕ) : 0 < W16 q := by
  unfold W16 P15
  positivity [z7_pos15 q,z9_pos15_c q,Y16_pos q,T16_pos_b q]

lemma T16_formula_b (q : ℕ) :
    T16 q=2*z9 q*r15 q+
      4*(z9 q/z8 q)*r15 q*(I15 q)^2+
      8*(1/z8 q)*r15 q*(I15 q*J15 q)^2 := by
  unfold T16 Y16 K15 J15 I15
  field_simp [(H15_pos_c q).ne',z8_ne]
  ring

set_option maxHeartbeats 800000 in
lemma z15_eq_K_mul_q15_d (q : ℕ) : z15 q=K15 q*q15 q := by
  rw [z15_formula q,z11_formula15_c q,
    z12_formula15_c q,z13_formula15_c q,z14_formula15_c q]
  unfold q15
  rw [z10_formula15_c q,z12_formula15_c q,z14_formula15_c q]
  unfold P15
  field_simp [z7_ne,z8_ne,z9_ne15_c,r15_ne_c,
    (H15_pos_c q).ne',(I15_pos_c q).ne',(J15_pos_c q).ne']

set_option maxHeartbeats 1600000 in
lemma q16_formula_W_d (q : ℕ) :
    q16 q=W16 q*z7 q/(2*I15 q*(P15 q)^2*r15 q) := by
  unfold q16
  rw [z13_formula15_c q,z15_eq_K_mul_q15_d q,z12_formula15_c q,
    q15_formula15_e q]
  unfold W16 T16 Y16 L15
  have hq10 : 1+P15 q=8*z6 q*q10 q := by
    unfold q10 P15
    field_simp [z6_ne]
  field_simp [z7_ne,z8_ne,z9_ne15_c,q10_ne,r15_ne_c,P15_ne_c,
    (H15_pos_c q).ne',(I15_pos_c q).ne']
  unfold H15 r15
  have hscaled := congrArg
    (fun t : ℚ => I15 q*J15 q*K15 q*t) hq10
  ring_nf at hscaled ⊢
  linarith

lemma H_I_J_K_data (q : ℕ) (h : TubeAt (14*q)) :
    Nonneg2' (H15 q) ∧ Unit2 (I15 q) ∧
      Unit2 (J15 q) ∧ Unit2 (K15 q) := by
  rcases initial_cancellation q h with ⟨hz4,hz5,hz6,hz7,hz8⟩
  have hz9 := z9_unit q h
  have hP : Unit2 (P15 q) := by
    unfold P15
    exact hz7.mul hz9
  have hr : Nonneg2' (r15 q) :=
    ⟨r15_ne_c q,q10_nonneg_proved_e q h⟩
  have hPr := nonneg_mul' (unit_nonneg' hP) hr
  have hH : Nonneg2' (H15 q) := by
    refine ⟨(H15_pos_c q).ne', ?_⟩
    unfold H15
    exact one_add_val_nonneg (H15_pos_c q).ne' hPr.2
  have hIterm : VGe 1 (2*z9 q*r15 q*H15 q) := by
    have hm := VGe.mul'
      (VGe.mul' (VGe.mul' vge_two' (vge_of_unit' hz9))
        (vge_of_nonneg' hr)) (vge_of_nonneg' hH)
    simpa [add_assoc] using hm
  have hI : Unit2 (I15 q) := by
    unfold I15
    exact unit_add_vge_one_b
      (show Unit2 (1:ℚ) from ⟨one_ne_zero,padicValRat.one⟩)
      hIterm (I15_pos_c q).ne'
  have hz9z8 : Unit2 (z9 q/z8 q) := hz9.div hz8
  have hJterm : VGe 1
      (4*(z9 q/z8 q)*r15 q*H15 q*I15 q) := by
    have hm := VGe.mul'
      (VGe.mul'
        (VGe.mul' (VGe.mul' vge_four' (vge_of_unit' hz9z8))
          (vge_of_nonneg' hr)) (vge_of_nonneg' hH))
      (vge_of_unit' hI)
    have hm2 : VGe 2
        (4*(z9 q/z8 q)*r15 q*H15 q*I15 q) := by
      simpa [add_assoc] using hm
    exact VGe.weaken' (k:=1) (l:=2) (by norm_num) hm2
  have hJ : Unit2 (J15 q) := by
    unfold J15
    exact unit_add_vge_one_b
      (show Unit2 (1:ℚ) from ⟨one_ne_zero,padicValRat.one⟩)
      hJterm (J15_pos_c q).ne'
  have honeDiv8 : Unit2 (1/z8 q) :=
    (show Unit2 (1:ℚ) from ⟨one_ne_zero,padicValRat.one⟩).div hz8
  have hKterm : VGe 1
      (8*(1/z8 q)*r15 q*H15 q*I15 q*J15 q) := by
    have hm := VGe.mul'
      (VGe.mul'
        (VGe.mul'
          (VGe.mul' (VGe.mul' vge_eight_b (vge_of_unit' honeDiv8))
            (vge_of_nonneg' hr)) (vge_of_nonneg' hH))
        (vge_of_unit' hI)) (vge_of_unit' hJ)
    have hm3 : VGe 3
        (8*(1/z8 q)*r15 q*H15 q*I15 q*J15 q) := by
      simpa [add_assoc] using hm
    exact VGe.weaken' (k:=1) (l:=3) (by norm_num) hm3
  have hK : Unit2 (K15 q) := by
    unfold K15
    exact unit_add_vge_one_b
      (show Unit2 (1:ℚ) from ⟨one_ne_zero,padicValRat.one⟩)
      hKterm (K15_pos_c q).ne'
  exact ⟨hH,hI,hJ,hK⟩


lemma val_add_vge_succ_b {k : ℤ} {x y : ℚ}
    (hxne : x ≠ 0) (hx : v2 x=k) (hy : VGe (k+1) y)
    (hsum : x+y ≠ 0) : v2 (x+y)=k := by
  by_cases hy0 : y=0
  · rw [hy0,add_zero]
    exact hx
  · rcases hy with hyEq | hy
    · exact absurd hyEq hy0
    · have hvne : v2 x ≠ v2 y := by omega
      have hv := padicValRat.add_eq_min hsum hxne hy0 hvne
      change v2 (x+y)=min (v2 x) (v2 y) at hv
      rw [hx,min_eq_left (by omega)] at hv
      exact hv

set_option maxHeartbeats 1600000 in
lemma W16_val (q : ℕ) (h : TubeAt (14*q)) :
    v2 (W16 q)=v2 (r15 q)+1 := by
  rcases initial_cancellation q h with ⟨hz4,hz5,hz6,hz7,hz8⟩
  have hz9 := z9_unit q h
  rcases H_I_J_K_data q h with ⟨hH,hI,hJ,hK⟩
  have hP : Unit2 (P15 q) := by
    unfold P15
    exact hz7.mul hz9
  have hrne := r15_ne_c q
  have hrV : VGe (v2 (r15 q)) (r15 q) := Or.inr le_rfl
  have hI2 : Unit2 ((I15 q)^2) := by
    simpa [pow_two] using hI.mul hI
  have hIJ2 : Unit2 ((I15 q*J15 q)^2) := by
    have hIJ := hI.mul hJ
    simpa [pow_two] using hIJ.mul hIJ
  let t1 : ℚ := 2*z9 q*r15 q
  let t2 : ℚ := 4*(z9 q/z8 q)*r15 q*(I15 q)^2
  let t3 : ℚ := 8*(1/z8 q)*r15 q*(I15 q*J15 q)^2
  have ht1ne : t1 ≠ 0 := by
    dsimp [t1]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hz9.1) hrne
  have ht1val : v2 t1=v2 (r15 q)+1 := by
    dsimp [t1]
    change padicValRat 2 (2*z9 q*r15 q)=v2 (r15 q)+1
    rw [padicValRat.mul (mul_ne_zero (by norm_num) hz9.1) hrne,
      padicValRat.mul (by norm_num) hz9.1]
    change v2 (2:ℚ)+v2 (z9 q)+v2 (r15 q)=v2 (r15 q)+1
    rw [hz9.2]
    have htwo : v2 (2:ℚ)=1 := by
      change padicValRat 2 (2:ℚ)=1
      rw [show (2:ℚ)=((2:ℕ):ℚ) by norm_num,
        padicValRat.self (by norm_num)]
    rw [htwo]
    ring
  have hz9z8 : Unit2 (z9 q/z8 q) := hz9.div hz8
  have ht2 : VGe (v2 (r15 q)+2) t2 := by
    dsimp [t2]
    have hm := VGe.mul'
      (VGe.mul' (VGe.mul' vge_four' (vge_of_unit' hz9z8)) hrV)
      (vge_of_unit' hI2)
    simpa [add_assoc,add_comm,add_left_comm] using hm
  have honeDiv8 : Unit2 (1/z8 q) :=
    (show Unit2 (1:ℚ) from ⟨one_ne_zero,padicValRat.one⟩).div hz8
  have ht3 : VGe (v2 (r15 q)+3) t3 := by
    dsimp [t3]
    have hm := VGe.mul'
      (VGe.mul' (VGe.mul' vge_eight_b (vge_of_unit' honeDiv8)) hrV)
      (vge_of_unit' hIJ2)
    simpa [add_assoc,add_comm,add_left_comm] using hm
  have ht3w : VGe (v2 (r15 q)+2) t3 :=
    VGe.weaken' (k:=v2 (r15 q)+2) (l:=v2 (r15 q)+3) (by omega) ht3
  have hcorr : VGe (v2 (r15 q)+2) (t2+t3) := ht2.add ht3w
  have hTeq : T16 q=t1+(t2+t3) := by
    rw [T16_formula_b q]
    dsimp [t1,t2,t3]
    ring
  have hTsum : t1+(t2+t3) ≠ 0 := by
    rw [← hTeq]
    exact (T16_pos_b q).ne'
  have hcorr' : VGe ((v2 (r15 q)+1)+1) (t2+t3) := by
    simpa only [add_assoc,one_add_one_eq_two] using hcorr
  have hTval : v2 (T16 q)=v2 (r15 q)+1 := by
    rw [hTeq]
    exact val_add_vge_succ_b ht1ne ht1val hcorr' hTsum
  have hY : Unit2 (Y16 q) := by
    unfold Y16
    exact (hI.mul hJ).mul hK
  have hYplus : VGe 1 (Y16 q+1) := by
    right
    exact unit_one_add_val hY (by positivity [Y16_pos q])
  have hYT : Y16 q-1=H15 q*T16 q := by
    unfold T16
    field_simp [(H15_pos_c q).ne']
  have hTvg : VGe (v2 (r15 q)+1) (T16 q) := Or.inr (by rw [hTval])
  have hYminus : VGe (v2 (r15 q)+1) (Y16 q-1) := by
    rw [hYT]
    have hm := VGe.mul' (vge_of_nonneg' hH) hTvg
    simpa using hm
  have hYsq : VGe (v2 (r15 q)+2) ((Y16 q)^2-1) := by
    have hm := VGe.mul' hYminus hYplus
    convert hm using 1 <;> ring
  have hPoneEq : P15 q+1=8*z6 q*r15 q := by
    unfold P15 r15 q10
    field_simp [z6_ne]
    ring
  have hz6N : Nonneg2' (z6 q) := ⟨z6_ne q,hz6⟩
  have hPone3 : VGe (v2 (r15 q)+3) (P15 q+1) := by
    rw [hPoneEq]
    have hm := VGe.mul'
      (VGe.mul' vge_eight_b (vge_of_nonneg' hz6N)) hrV
    simpa [add_assoc,add_comm,add_left_comm] using hm
  have hPone2 : VGe (v2 (r15 q)+2) (P15 q+1) :=
    VGe.weaken' (k:=v2 (r15 q)+2) (l:=v2 (r15 q)+3) (by omega) hPone3
  have hPYsq : VGe (v2 (r15 q)+2) (P15 q+(Y16 q)^2) := by
    have hm := hPone2.add hYsq
    convert hm using 1 ; ring
  have hPTne : P15 q*T16 q ≠ 0 :=
    mul_ne_zero hP.1 (T16_pos_b q).ne'
  have hPTval : v2 (P15 q*T16 q)=v2 (r15 q)+1 := by
    change padicValRat 2 (P15 q*T16 q)=v2 (r15 q)+1
    rw [padicValRat.mul hP.1 (T16_pos_b q).ne']
    change v2 (P15 q)+v2 (T16 q)=v2 (r15 q)+1
    rw [hP.2,hTval]
    ring
  have hWeq : W16 q=P15 q*T16 q+(P15 q+(Y16 q)^2) := by
    unfold W16
    ring
  have hWsum : P15 q*T16 q+(P15 q+(Y16 q)^2) ≠ 0 := by
    rw [← hWeq]
    exact (W16_pos_b q).ne'
  have hPYsq' : VGe ((v2 (r15 q)+1)+1)
      (P15 q+(Y16 q)^2) := by
    simpa only [add_assoc,one_add_one_eq_two] using hPYsq
  rw [hWeq]
  exact val_add_vge_succ_b hPTne hPTval hPYsq' hWsum

set_option maxHeartbeats 800000 in
lemma q16_unit_proved_b (q : ℕ) (h : TubeAt (14*q)) : Unit2 (q16 q) := by
  rcases initial_cancellation q h with ⟨hz4,hz5,hz6,hz7,hz8⟩
  have hz9 := z9_unit q h
  rcases H_I_J_K_data q h with ⟨hH,hI,hJ,hK⟩
  have hP : Unit2 (P15 q) := by
    unfold P15
    exact hz7.mul hz9
  have hP2 : Unit2 ((P15 q)^2) := by
    simpa [pow_two] using hP.mul hP
  have hIU : Unit2 (I15 q*(P15 q)^2) := hI.mul hP2
  have hWne := (W16_pos_b q).ne'
  have hnumne : W16 q*z7 q ≠ 0 := mul_ne_zero hWne hz7.1
  have hdenne : 2*I15 q*(P15 q)^2*r15 q ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) hI.1) hP2.1) (r15_ne_c q)
  have hnumval : v2 (W16 q*z7 q)=v2 (r15 q)+1 := by
    change padicValRat 2 (W16 q*z7 q)=v2 (r15 q)+1
    rw [padicValRat.mul hWne hz7.1]
    change v2 (W16 q)+v2 (z7 q)=v2 (r15 q)+1
    rw [W16_val q h,hz7.2]
    ring
  have hdenval : v2 (2*I15 q*(P15 q)^2*r15 q)=v2 (r15 q)+1 := by
    change padicValRat 2 (2*I15 q*(P15 q)^2*r15 q)=v2 (r15 q)+1
    rw [padicValRat.mul
        (mul_ne_zero (mul_ne_zero (by norm_num) hI.1) hP2.1) (r15_ne_c q),
      padicValRat.mul (mul_ne_zero (by norm_num) hI.1) hP2.1,
      padicValRat.mul (by norm_num) hI.1]
    change v2 (2:ℚ)+v2 (I15 q)+v2 ((P15 q)^2)+v2 (r15 q)=
      v2 (r15 q)+1
    rw [hI.2,hP2.2]
    have htwo : v2 (2:ℚ)=1 := by
      change padicValRat 2 (2:ℚ)=1
      rw [show (2:ℚ)=((2:ℕ):ℚ) by norm_num,
        padicValRat.self (by norm_num)]
    rw [htwo]
    ring
  rw [q16_formula_W_d q]
  refine ⟨div_ne_zero hnumne hdenne, ?_⟩
  change padicValRat 2
    (W16 q*z7 q/(2*I15 q*(P15 q)^2*r15 q))=0
  rw [padicValRat.div hnumne hdenne]
  change v2 (W16 q*z7 q)-v2 (2*I15 q*(P15 q)^2*r15 q)=0
  rw [hnumval,hdenval]
  ring

lemma s10b_vge_one_r (q : ℕ) (h : TubeAt (14*q)) :
    VGe 1 (s10b q) := by
  obtain ⟨hu0,hu1,hu2,hu3⟩ := tube_normalized_units q h
  rcases initial_cancellation q h with ⟨hz4,hz5,hz6,hz7,hz8⟩
  have hp : Unit2 (p10b q) := by
    unfold p10b
    exact hu1.mul hu3
  have hA := A4_nonneg q h
  right
  unfold s10b
  change 1 ≤ padicValRat 2 (2*z4 q*A4 q/p10b q)
  rw [padicValRat.div
      (mul_ne_zero (mul_ne_zero (by norm_num) (z4_ne q)) hA.1) hp.1,
    padicValRat.mul (mul_ne_zero (by norm_num) (z4_ne q)) hA.1,
    padicValRat.mul (by norm_num) (z4_ne q)]
  change 1 ≤ v2 (2:ℚ)+v2 (z4 q)+v2 (A4 q)-v2 (p10b q)
  rw [hp.2]
  have htwo : v2 (2:ℚ)=1 := by
    change padicValRat 2 (2:ℚ)=1
    rw [show (2:ℚ)=((2:ℕ):ℚ) by norm_num,
      padicValRat.self (by norm_num)]
  rw [htwo]
  have hAv := hA.2
  omega

lemma z9_times_p10b_sq_r (q : ℕ) :
    z9 q*(p10b q)^2 =
      D7 q*(2*u0 q*u2 q+p10b q*u2 q+
        2*(A4 q)^2*L10b q) := by
  let Q : ℚ := B5 q*C6 q*D7 q
  have hQ : Q=1+s10b q*L10b q := by
    unfold L10b
    dsimp [Q]
    field_simp [s10b_ne]
    ring
  have hs : s10b q*p10b q=2*z4 q*A4 q := by
    unfold s10b
    field_simp [p10b_ne]
  have hp := z4_p10b_identity q
  have hcore :
      p10b q*(p10b q+A4 q*Q) =
        z4 q*(2*u0 q*u2 q+p10b q*u2 q+
          2*(A4 q)^2*L10b q) := by
    rw [hQ]
    calc
      p10b q*(p10b q+A4 q*(1+s10b q*L10b q)) =
          p10b q*(p10b q+A4 q)+
            A4 q*L10b q*(s10b q*p10b q) := by ring
      _ = p10b q*(p10b q+A4 q)+
            A4 q*L10b q*(2*z4 q*A4 q) := by rw [hs]
      _ = z4 q*(2*u0 q*u2 q+p10b q*u2 q+
            2*(A4 q)^2*L10b q) := by
          unfold A4
          linear_combination -hp
  rw [z9_p10b_formula q]
  rw [show A4 q*B5 q*C6 q*D7 q=A4 q*Q by
    dsimp [Q]
    ring]
  change
    D7 q*(p10b q+A4 q*Q)/(z4 q*p10b q)*(p10b q)^2 =
      D7 q*(2*u0 q*u2 q+p10b q*u2 q+
        2*(A4 q)^2*L10b q)
  field_simp [p10b_ne,z4_ne]
  linear_combination D7 q*hcore

lemma z9_close_neg_u0_r (q : ℕ) (h : TubeAt (14*q)) :
    Close4 (z9 q) (-u0 q) := by
  obtain ⟨hu0,hu1,hu2,hu3⟩ := tube_normalized_units q h
  rcases initial_cancellation q h with ⟨hz4,hz5,hz6,hz7,hz8⟩
  have ht := h
  unfold TubeAt at ht
  have hclose02 : Close4 (u0 q) (u2 q) := by
    simpa [u0,u2] using ht.2.2.2.2
  have hp : Unit2 (p10b q) := by
    unfold p10b
    exact hu1.mul hu3
  have hA := A4_nonneg q h
  have hs := s10b_nonneg2 q h
  have hs1 := s10b_vge_one_r q h
  have hB : Unit2 (B5 q) := unit_B5 q hu3 hz5
  have hC : Unit2 (C6 q) := unit_C6 q hz4 hz6
  have hD : Unit2 (D7 q) := unit_D7 q hz5 hz7
  have hz9 := z9_unit q h
  have hone : Unit2 (1:ℚ) := ⟨one_ne_zero,padicValRat.one⟩
  have honeN : Nonneg2' (1:ℚ) := unit_nonneg' hone
  have htwoN : Nonneg2' (2:ℚ) := by
    refine ⟨by norm_num, ?_⟩
    change 0 ≤ padicValRat 2 (2:ℚ)
    rw [show (2:ℚ)=((2:ℕ):ℚ) by norm_num,
      padicValRat.self (by norm_num)]
    norm_num
  have hzN : Nonneg2' (z4 q) := ⟨z4_ne q,hz4⟩
  have hAN : Nonneg2' (A4 q) := hA
  have hBclose : Close4 (B5 q) 1 := by
    rw [close4_iff_vge']
    unfold B5
    have h16 : VGe 4 (16:ℚ) := by
      right
      change 4 ≤ v2 (16:ℚ)
      rw [v2_16]
    have hm := (h16.mul' (vge_of_unit' hu3)).mul'
      (vge_of_nonneg' ⟨z5_ne q,hz5⟩)
    have hw : VGe 2 (16*u3 q*z5 q) :=
      VGe.weaken' (k:=2) (l:=4) (by norm_num) (by simpa [add_assoc] using hm)
    convert hw using 1 ; ring
  have hCclose : Close4 (C6 q) 1 := by
    rw [C6_s10b_formula q,close4_iff_vge']
    have hm := ((vge_two'.mul' (vge_of_unit' hu3)).mul' hs1).mul'
      (vge_of_unit' hB)
    have hw : VGe 2 (2*u3 q*s10b q*B5 q) := by
      simpa [add_assoc] using hm
    convert hw using 1 ; ring
  have hBCclose : Close4 (B5 q*C6 q) 1 := by
    have hm := close4_mul hB hone hBclose hCclose
    simpa using hm
  have hstarget : Close4 (s10b q) (2*z4 q*A4 q) :=
    s10b_close2 q h
  have htargetN : Nonneg2' (1:ℚ) := honeN
  have hsBCclose :
      Close4 (s10b q*(B5 q*C6 q)) ((2*z4 q*A4 q)*1) :=
    close4_mul_nonneg' hs htargetN hstarget hBCclose
  have hDclose :
      Close4 (D7 q) (1+2*z4 q*A4 q) := by
    rw [D7_s10b_formula q]
    have honeclose : Close4 (1:ℚ) 1 := Or.inl rfl
    have hm := close4_add' honeclose hsBCclose
    convert hm using 1 <;> ring
  have hu02 : Close4 (u0 q*u2 q) 1 := by
    have hprod : Close4 (u0 q*u2 q) (u0 q*u0 q) :=
      close4_mul hu0 hu0 (Or.inl rfl) (close4_symm hclose02)
    have hsq : Close4 (u0 q*u0 q) 1 := by
      convert unit_sq_close_one' hu0 using 1 ; ring
    exact close4_trans hprod hsq
  have hterm0 : Close4 (2*u0 q*u2 q) 2 := by
    have htwoClose : Close4 (2:ℚ) 2 := Or.inl rfl
    have hm := close4_mul_nonneg' htwoN honeN htwoClose hu02
    convert hm using 1 <;> ring
  have hpclose := p10b_close2 q h
  have hterm1 :
      Close4 (p10b q*u2 q) ((2*z4 q-1)*u2 q) :=
    close4_mul hp hu2 hpclose (Or.inl rfl)
  have hminus : Unit2 (-1:ℚ) := by
    norm_num [Unit2,padicValRat.neg,padicValRat.one]
  have hA2N : Nonneg2' ((A4 q)^2) := by
    simpa [pow_two] using nonneg_mul' hAN hAN
  have hcoefN : Nonneg2' (2*(A4 q)^2) :=
    nonneg_mul' htwoN hA2N
  have hterm2 :
      Close4 (2*(A4 q)^2*L10b q) (2*(A4 q)^2*(-1)) :=
    close4_mul_nonneg' hcoefN (unit_nonneg' hminus)
      (Or.inl rfl) (L10b_close_neg_one2 q h)
  have hXclose :
      Close4
        (2*u0 q*u2 q+p10b q*u2 q+2*(A4 q)^2*L10b q)
        (2+(2*z4 q-1)*u2 q+2*(A4 q)^2*(-1)) :=
    close4_add' (close4_add' hterm0 hterm1) hterm2
  let Xt : ℚ := 2+(2*z4 q-1)*u2 q+2*(A4 q)^2*(-1)
  have htwopos : VGe 1 (2:ℚ) := vge_two'
  have hz0 : VGe 0 (z4 q) := vge_of_nonneg' hzN
  have hA0 : VGe 0 (A4 q) := vge_of_nonneg' hAN
  have htwoz : VGe 1 (2*z4 q) := by
    simpa using htwopos.mul' hz0
  have hptarget : Unit2 (2*z4 q-1) := by
    have hcorr : VGe 1 (-(2*z4 q)) := (htwoz.neg')
    have hne : 1 + (-(2*z4 q)) ≠ 0 := by
      intro heq
      have hzhalf : z4 q=1/2 := by linarith
      have hv := hz4
      rw [hzhalf] at hv
      change 0 ≤ padicValRat 2 ((1:ℚ)/2) at hv
      rw [padicValRat.div (by norm_num) (by norm_num),
        padicValRat.one] at hv
      change 0 ≤ 0-v2 (2:ℚ) at hv
      have htwoVal : v2 (2:ℚ)=1 := by
        change padicValRat 2 (2:ℚ)=1
        rw [show (2:ℚ)=((2:ℕ):ℚ) by norm_num,
          padicValRat.self (by norm_num)]
      rw [htwoVal] at hv
      omega
    have hu := unit_add_vge_one_b hone hcorr hne
    convert hu.neg using 1 ; ring
  have hmid : Unit2 ((2*z4 q-1)*u2 q) := hptarget.mul hu2
  have hA2v : VGe 0 ((A4 q)^2) := by
    simpa [pow_two] using hA0.mul' hA0
  have hcorr2 : VGe 1 (2+2*(A4 q)^2*(-1)) := by
    have h1 := htwopos
    have h2 := (htwopos.mul' hA2v).mul' (vge_of_unit' hminus)
    have hm := h1.add h2
    convert hm using 1
  have hXtneg : Xt < 0 := by
    have hu2p : 0 < u2 q := by unfold u2; exact x_pos _
    have hz4p : 0 < z4 q := by unfold z4; exact x_pos _
    have heq :
        Xt = -u2 q*(1+2*z4 q+2*u2 q*(z4 q)^2) := by
      dsimp [Xt]
      unfold A4
      ring
    rw [heq]
    have hbr : 0 < 1+2*z4 q+2*u2 q*(z4 q)^2 := by
      positivity
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hu2p) hbr
  have hXt : Unit2 Xt := by
    have hsumne :
        (2*z4 q-1)*u2 q+(2+2*(A4 q)^2*(-1)) ≠ 0 := by
      have heq :
          (2*z4 q-1)*u2 q+(2+2*(A4 q)^2*(-1))=Xt := by
        dsimp [Xt]
        ring
      rw [heq]
      exact hXtneg.ne
    have hm := unit_add_vge_one_b hmid hcorr2 hsumne
    convert hm using 1 ; ring
  have hDXclose :
      Close4
        (D7 q*(2*u0 q*u2 q+p10b q*u2 q+
          2*(A4 q)^2*L10b q))
        ((1+2*z4 q*A4 q)*Xt) := by
    exact close4_mul hD hXt hDclose (by simpa [Xt] using hXclose)
  have hlast : VGe 0 (u2 q*(z4 q)^2+z4 q+1) := by
    have hz2 := hz0.mul' hz0
    have hu2z2 := (vge_of_unit' hu2).mul' hz2
    have hm := (hu2z2.add hz0).add (vge_of_unit' hone)
    convert hm using 1 ; ring
  have htargetClose :
      Close4 ((1+2*z4 q*A4 q)*Xt) (-u2 q) := by
    rw [close4_iff_vge']
    have hfour : VGe 2 (4:ℚ) := vge_four'
    have hm := (((hfour.mul' (vge_of_unit' hu2)).mul' hz0).mul' hA0).mul' hlast
    have hm2 : VGe 2
        (4*u2 q*z4 q*A4 q*(u2 q*(z4 q)^2+z4 q+1)) := by
      simpa [add_assoc] using hm
    have heq :
        (1+2*z4 q*A4 q)*Xt-(-u2 q) =
          -(4*u2 q*z4 q*A4 q*
            (u2 q*(z4 q)^2+z4 q+1)) := by
      dsimp [Xt]
      unfold A4
      ring
    rw [heq]
    exact hm2.neg'
  have hprodClose :
      Close4 (z9 q*(p10b q)^2) (-u2 q) := by
    rw [z9_times_p10b_sq_r q]
    exact close4_trans hDXclose htargetClose
  have hp2close : Close4 ((p10b q)^2) 1 :=
    unit_sq_close_one' hp
  have hstrip : Close4 (z9 q*(p10b q)^2) (z9 q) := by
    have hm := close4_mul hz9 hone (Or.inl rfl) hp2close
    simpa using hm
  have hz9u2 : Close4 (z9 q) (-u2 q) :=
    close4_trans (close4_symm hstrip) hprodClose
  exact close4_trans hz9u2
    (close4_neg'2 (close4_symm hclose02))

lemma inv_close_self_unit_r {a : ℚ} (ha : Unit2 a) :
    Close4 (1/a) a := by
  by_cases heq : 1/a=a
  · exact Or.inl heq
  · right
    have hnumne : 1-a^2 ≠ 0 := by
      intro hn
      apply heq
      apply (div_eq_iff ha.1).2
      nlinarith
    have hs : 3 ≤ v2 (a^2-1) :=
      unit_sq_sub_one_val ha (by
        intro hz
        apply hnumne
        linarith)
    change 2 ≤ padicValRat 2 (1/a-a)
    rw [show 1/a-a=(1-a^2)/a by
      field_simp [ha.1],
      padicValRat.div hnumne ha.1]
    change 2 ≤ v2 (1-a^2)-v2 a
    rw [ha.2]
    have hv : v2 (1-a^2)=v2 (a^2-1) := by
      change padicValRat 2 (1-a^2)=padicValRat 2 (a^2-1)
      rw [show 1-a^2=-(a^2-1) by ring,padicValRat.neg]
    rw [hv]
    omega

lemma z14_close_neg_u0_r (q : ℕ) (h : TubeAt (14*q)) :
    Close4 (z14 q) (-u0 q) := by
  obtain ⟨hu0,hu1,hu2,hu3⟩ := tube_normalized_units q h
  rcases initial_cancellation q h with ⟨hz4,hz5,hz6,hz7,hz8⟩
  have hz9 := z9_unit q h
  rcases H_I_J_K_data q h with ⟨hH,hI,hJ,hK⟩
  have hr : Nonneg2' (r15 q) :=
    ⟨r15_ne_c q,q10_nonneg_proved_e q h⟩
  have hone : Unit2 (1:ℚ) := ⟨one_ne_zero,padicValRat.one⟩
  have hJclose : Close4 (J15 q) 1 := by
    rw [close4_iff_vge']
    unfold J15
    have hzratio : Unit2 (z9 q/z8 q) := hz9.div hz8
    have hm := (((vge_four'.mul' (vge_of_unit' hzratio)).mul'
      (vge_of_nonneg' hr)).mul' (vge_of_nonneg' hH)).mul'
        (vge_of_unit' hI)
    have hm2 : VGe 2
        (4*(z9 q/z8 q)*r15 q*H15 q*I15 q) := by
      simpa [add_assoc] using hm
    convert hm2 using 1 ; ring
  have hKclose : Close4 (K15 q) 1 := by
    rw [close4_iff_vge']
    unfold K15
    have honeDiv : Unit2 (1/z8 q) := hone.div hz8
    have hm := ((((vge_eight_b.mul' (vge_of_unit' honeDiv)).mul'
      (vge_of_nonneg' hr)).mul' (vge_of_nonneg' hH)).mul'
        (vge_of_unit' hI)).mul' (vge_of_unit' hJ)
    have hm3 : VGe 3
        (8*(1/z8 q)*r15 q*H15 q*I15 q*J15 q) := by
      simpa [add_assoc] using hm
    have hm2 := VGe.weaken' (k:=2) (l:=3) (by norm_num) hm3
    convert hm2 using 1 ; ring
  have hJKclose : Close4 (J15 q*K15 q) 1 := by
    have hm := close4_mul hJ hone hJclose hKclose
    simpa using hm
  have hinv : Close4 (1/z9 q) (-u0 q) :=
    close4_trans (inv_close_self_unit_r hz9) (z9_close_neg_u0_r q h)
  have hm := close4_mul (hJ.mul hK) hu0.neg hJKclose hinv
  rw [z14_formula15_c q]
  convert hm using 1 <;> field_simp [hz9.1]

set_option maxHeartbeats 1200000 in
lemma T16_val_r (q : ℕ) (h : TubeAt (14*q)) :
    v2 (T16 q)=v2 (r15 q)+1 := by
  rcases initial_cancellation q h with ⟨hz4,hz5,hz6,hz7,hz8⟩
  have hz9 := z9_unit q h
  rcases H_I_J_K_data q h with ⟨hH,hI,hJ,hK⟩
  have hrne := r15_ne_c q
  have hrV : VGe (v2 (r15 q)) (r15 q) := Or.inr le_rfl
  have hI2 : Unit2 ((I15 q)^2) := by
    simpa [pow_two] using hI.mul hI
  have hIJ2 : Unit2 ((I15 q*J15 q)^2) := by
    have hIJ := hI.mul hJ
    simpa [pow_two] using hIJ.mul hIJ
  let t1 : ℚ := 2*z9 q*r15 q
  let t2 : ℚ := 4*(z9 q/z8 q)*r15 q*(I15 q)^2
  let t3 : ℚ := 8*(1/z8 q)*r15 q*(I15 q*J15 q)^2
  have ht1ne : t1 ≠ 0 := by
    dsimp [t1]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hz9.1) hrne
  have ht1val : v2 t1=v2 (r15 q)+1 := by
    dsimp [t1]
    change padicValRat 2 (2*z9 q*r15 q)=v2 (r15 q)+1
    rw [padicValRat.mul (mul_ne_zero (by norm_num) hz9.1) hrne,
      padicValRat.mul (by norm_num) hz9.1]
    change v2 (2:ℚ)+v2 (z9 q)+v2 (r15 q)=v2 (r15 q)+1
    rw [hz9.2]
    have htwo : v2 (2:ℚ)=1 := by
      change padicValRat 2 (2:ℚ)=1
      rw [show (2:ℚ)=((2:ℕ):ℚ) by norm_num,
        padicValRat.self (by norm_num)]
    rw [htwo]
    ring
  have hz9z8 : Unit2 (z9 q/z8 q) := hz9.div hz8
  have ht2 : VGe (v2 (r15 q)+2) t2 := by
    dsimp [t2]
    have hm := VGe.mul'
      (VGe.mul' (VGe.mul' vge_four' (vge_of_unit' hz9z8)) hrV)
      (vge_of_unit' hI2)
    simpa [add_assoc,add_comm,add_left_comm] using hm
  have honeDiv8 : Unit2 (1/z8 q) :=
    (show Unit2 (1:ℚ) from ⟨one_ne_zero,padicValRat.one⟩).div hz8
  have ht3 : VGe (v2 (r15 q)+3) t3 := by
    dsimp [t3]
    have hm := VGe.mul'
      (VGe.mul' (VGe.mul' vge_eight_b (vge_of_unit' honeDiv8)) hrV)
      (vge_of_unit' hIJ2)
    simpa [add_assoc,add_comm,add_left_comm] using hm
  have ht3w : VGe (v2 (r15 q)+2) t3 :=
    VGe.weaken' (k:=v2 (r15 q)+2) (l:=v2 (r15 q)+3) (by omega) ht3
  have hcorr : VGe (v2 (r15 q)+2) (t2+t3) := ht2.add ht3w
  have hTeq : T16 q=t1+(t2+t3) := by
    rw [T16_formula_b q]
    dsimp [t1,t2,t3]
    ring
  have hTsum : t1+(t2+t3) ≠ 0 := by
    rw [← hTeq]
    exact (T16_pos_b q).ne'
  have hcorr' : VGe ((v2 (r15 q)+1)+1) (t2+t3) := by
    simpa only [add_assoc,one_add_one_eq_two] using hcorr
  rw [hTeq]
  exact val_add_vge_succ_b ht1ne ht1val hcorr' hTsum

def M16 (q : ℕ) : ℚ := z13 q*z15 q

lemma M16_formula_r (q : ℕ) :
    M16 q=Y16 q*(P15 q+H15 q*Y16 q)/
      ((P15 q)^2*r15 q) := by
  have hL : H15 q*Y16 q-1=r15 q*L15 q := by
    unfold L15 Y16
    field_simp [r15_ne_c]
  have hbase : P15 q+1=8*z6 q*r15 q := by
    unfold P15 r15 q10
    field_simp [z6_ne]
    ring
  have hquot :
      P15 q+H15 q*Y16 q =
        r15 q*(8*z6 q+L15 q) := by
    linarith
  unfold M16
  rw [z13_formula15_c q,z15_eq_K_mul_q15_d q,
    q15_formula15_e q]
  change
    (I15 q*J15 q/z8 q)*
        (K15 q*(z8 q/(P15 q)^2*(8*z6 q+L15 q))) =
      Y16 q*(P15 q+H15 q*Y16 q)/((P15 q)^2*r15 q)
  rw [hquot]
  unfold Y16
  field_simp [z8_ne,P15_ne_c,r15_ne_c]

lemma z16_via_M16_r (q : ℕ) :
    z16 q=M16 q*q16 q/z14 q := by
  unfold M16 q16
  rw [z16_formula q]
  field_simp [z12_ne,z14_ne]

lemma VGe.div_unit_r {k : ℤ} {x u : ℚ}
    (hx : VGe k x) (hu : Unit2 u) : VGe k (x/u) := by
  rcases hx with rfl | hx
  · left
    field_simp [hu.1]
    ring
  · by_cases hx0 : x=0
    · left
      rw [hx0]
      field_simp [hu.1]
      ring
    · right
      change k ≤ padicValRat 2 (x/u)
      rw [padicValRat.div hx0 hu.1]
      change k ≤ v2 x-v2 u
      rw [hu.2]
      omega

lemma VGe.div_two_r {k : ℤ} {x : ℚ}
    (hx : VGe (k+1) x) : VGe k (x/2) := by
  rcases hx with rfl | hx
  · left
    norm_num
  · by_cases hx0 : x=0
    · left
      rw [hx0]
      norm_num
    · right
      change k ≤ padicValRat 2 (x/2)
      rw [padicValRat.div hx0 (by norm_num)]
      change k ≤ v2 x-v2 (2:ℚ)
      have htwo : v2 (2:ℚ)=1 := by
        change padicValRat 2 (2:ℚ)=1
        rw [show (2:ℚ)=((2:ℕ):ℚ) by norm_num,
          padicValRat.self (by norm_num)]
      rw [htwo]
      omega

lemma close4_inv_congr_units_r {a b : ℚ}
    (ha : Unit2 a) (hb : Unit2 b) (h : Close4 a b) :
    Close4 (1/a) (1/b) := by
  rcases close4_cases h with rfl | ⟨habne,habv⟩
  · exact Or.inl rfl
  · by_cases hi : 1/a=1/b
    · exact Or.inl hi
    · right
      have hbanne : b-a ≠ 0 := by
        intro hz
        apply habne
        linarith
      change 2 ≤ padicValRat 2 (1/a-1/b)
      rw [show 1/a-1/b=(b-a)/(a*b) by
        field_simp [ha.1,hb.1],
        padicValRat.div hbanne (mul_ne_zero ha.1 hb.1),
        padicValRat.mul ha.1 hb.1]
      change 2 ≤ v2 (b-a)-(v2 a+v2 b)
      rw [ha.2,hb.2]
      have hv : v2 (b-a)=v2 (a-b) := by
        change padicValRat 2 (b-a)=padicValRat 2 (a-b)
        rw [show b-a=-(a-b) by ring,padicValRat.neg]
      rw [hv]
      omega

lemma close4_div_units_r {q r Q R : ℚ}
    (hq : Unit2 q) (hr : Unit2 r) (hR : Unit2 R)
    (h1 : Close4 q Q) (h2 : Close4 r R) :
    Close4 (q/r) (Q/R) := by
  have hone : Unit2 (1:ℚ) := ⟨one_ne_zero,padicValRat.one⟩
  have hiR : Unit2 (1/R) := hone.div hR
  have hi := close4_inv_congr_units_r hr hR h2
  have hm := close4_mul hq hiR h1 hi
  convert hm using 1 <;> field_simp [hr.1,hR.1]

set_option maxHeartbeats 1800000 in
lemma M16_q16_close_one_runit (q : ℕ) (h : TubeAt (14*q))
    (hr0 : v2 (r15 q)=0) :
    Close4 (M16 q*q16 q) 1 := by
  rcases initial_cancellation q h with ⟨hz4,hz5,hz6,hz7,hz8⟩
  have hz9 := z9_unit q h
  rcases H_I_J_K_data q h with ⟨hH,hI,hJ,hK⟩
  have hP : Unit2 (P15 q) := by
    unfold P15
    exact hz7.mul hz9
  have hr : Unit2 (r15 q) := ⟨r15_ne_c q,hr0⟩
  have hP2 : Unit2 ((P15 q)^2) := by
    simpa [pow_two] using hP.mul hP
  have hY : Unit2 (Y16 q) := by
    unfold Y16
    exact (hI.mul hJ).mul hK
  have hone : Unit2 (1:ℚ) := ⟨one_ne_zero,padicValRat.one⟩
  have hHpos : 0 < v2 (H15 q) := by
    have hPr : Unit2 (P15 q*r15 q) := hP.mul hr
    have hv := unit_one_add_val hPr (by
      unfold P15
      positivity [z7_pos15 q,z9_pos15_c q,r15_pos_c q])
    rw [show H15 q=1+P15 q*r15 q by rfl]
    simpa [add_comm] using hv
  have hH1 : VGe 1 (H15 q) := Or.inr (by omega)
  have hTval : v2 (T16 q)=1 := by
    rw [T16_val_r q h,hr0]
    norm_num
  have hT1 : VGe 1 (T16 q) := Or.inr (by rw [hTval])
  have hYT : Y16 q-1=H15 q*T16 q := by
    unfold T16
    field_simp [(H15_pos_c q).ne']
  have hYclose : Close4 (Y16 q) 1 := by
    rw [close4_iff_vge']
    rw [hYT]
    have hm := hH1.mul' hT1
    simpa using hm
  have hPone : P15 q+1=8*z6 q*r15 q := by
    unfold P15 r15 q10
    field_simp [z6_ne]
    ring
  have hz6N : Nonneg2' (z6 q) := ⟨z6_ne q,hz6⟩
  have hPone3 : VGe 3 (P15 q+1) := by
    rw [hPone]
    have hm := (vge_eight_b.mul' (vge_of_nonneg' hz6N)).mul'
      (vge_of_unit' hr)
    simpa [add_assoc] using hm
  have hPclose : Close4 (P15 q) (-1) := by
    rw [close4_iff_vge']
    have hw := VGe.weaken' (k:=2) (l:=3) (by norm_num) hPone3
    convert hw using 1 ; ring
  have hP2close : Close4 ((P15 q)^2) 1 := unit_sq_close_one' hP
  let N : ℚ := (P15 q+H15 q*Y16 q)/r15 q
  have hNclose : Close4 N (P15 q) := by
    rw [close4_iff_vge']
    have hHsqT : VGe 3 (H15 q*(Y16 q-1)) := by
      rw [hYT]
      have hm := (hH1.mul' hH1).mul' hT1
      convert hm using 1 ; ring
    have hnum : VGe 3
        ((P15 q+1)+H15 q*(Y16 q-1)) :=
      hPone3.add hHsqT
    have hdiv3 := VGe.div_unit_r hnum hr
    have hdiv := VGe.weaken' (k:=2) (l:=3) (by norm_num) hdiv3
    convert hdiv using 1
    dsimp [N]
    unfold H15
    field_simp [hr.1]
    ring
  have hN : Unit2 N := by
    have hNp : 0 < N := by
      dsimp [N]
      unfold P15
      positivity [z7_pos15 q,z9_pos15_c q,H15_pos_c q,
        Y16_pos q,r15_pos_c q]
    exact unit_of_close4' hP hNclose hNp.ne'
  have hMformula : M16 q=Y16 q*N/(P15 q)^2 := by
    rw [M16_formula_r q]
    dsimp [N]
    field_simp [P15_ne_c,r15_ne_c]
  have hYNclose : Close4 (Y16 q*N) (P15 q) := by
    have hm := close4_mul hY hP hYclose hNclose
    simpa using hm
  have hMcloseP : Close4 (M16 q) (P15 q) := by
    rw [hMformula]
    have hm := close4_div_units_r (hY.mul hN) hP2 hone
      hYNclose hP2close
    simpa using hm
  have hMclose : Close4 (M16 q) (-1) :=
    close4_trans hMcloseP hPclose
  have hM : Unit2 (M16 q) := by
    rw [hMformula]
    exact (hY.mul hN).div hP2
  have hYplus : VGe 1 (Y16 q+1) := by
    right
    exact unit_one_add_val hY (by positivity [Y16_pos q])
  have hYsq3 : VGe 3 ((Y16 q)^2-1) := by
    have hYm : VGe 2 (Y16 q-1) := by
      rw [hYT]
      simpa using hH1.mul' hT1
    have hm := hYm.mul' hYplus
    convert hm using 1 ; ring
  have hA : Close4 ((P15 q+1)/2) 0 := by
    rw [close4_iff_vge']
    have hv := VGe.div_two_r (k:=2) hPone3
    convert hv using 1 ; ring
  have hB : Close4 (((Y16 q)^2-1)/2) 0 := by
    rw [close4_iff_vge']
    have hv := VGe.div_two_r (k:=2) hYsq3
    convert hv using 1 ; ring
  have hI2 : Unit2 ((I15 q)^2) := by
    simpa [pow_two] using hI.mul hI
  have hIJ2 : Unit2 ((I15 q*J15 q)^2) := by
    have hIJ := hI.mul hJ
    simpa [pow_two] using hIJ.mul hIJ
  have hU2 : Unit2 ((z9 q/z8 q)*r15 q*(I15 q)^2) :=
    ((hz9.div hz8).mul hr).mul hI2
  have hterm2 : Close4
      (2*((z9 q/z8 q)*r15 q*(I15 q)^2)) 2 :=
    two_mul_unit_close_two' hU2
  have hU3 : Nonneg2'
      (4*((1/z8 q)*r15 q*(I15 q*J15 q)^2)) := by
    have honeDiv : Unit2 (1/z8 q) := hone.div hz8
    have hfourN : Nonneg2' (4:ℚ) :=
      ⟨by norm_num,by rw [v2_four]; norm_num⟩
    exact nonneg_mul' hfourN
      (unit_nonneg' ((honeDiv.mul hr).mul hIJ2))
  have hterm3 : Close4
      (4*((1/z8 q)*r15 q*(I15 q*J15 q)^2)) 0 := by
    rw [close4_iff_vge']
    have honeDiv : Unit2 (1/z8 q) := hone.div hz8
    have htail : Unit2 ((1/z8 q)*r15 q*(I15 q*J15 q)^2) :=
      (honeDiv.mul hr).mul hIJ2
    have hm := vge_four'.mul' (vge_of_unit' htail)
    convert hm using 1 ; ring
  have hTdivFormula :
      T16 q/2 =
        z9 q*r15 q+
        2*((z9 q/z8 q)*r15 q*(I15 q)^2)+
        4*((1/z8 q)*r15 q*(I15 q*J15 q)^2) := by
    rw [T16_formula_b q]
    ring
  have hTdivClose :
      Close4 (T16 q/2) (z9 q*r15 q+2) := by
    rw [hTdivFormula]
    have hzr : Close4 (z9 q*r15 q) (z9 q*r15 q) := Or.inl rfl
    have h23 := close4_add' hterm2 hterm3
    have hs := close4_add' hzr h23
    convert hs using 1 <;> ring
  have hTarget : Unit2 (z9 q*r15 q+2) := by
    have hzr := hz9.mul hr
    have hne : z9 q*r15 q+2 ≠ 0 := by
      positivity [z9_pos15_c q,r15_pos_c q]
    exact unit_add_vge_one_b hzr vge_two' hne
  have hPTclose :
      Close4 (P15 q*(T16 q/2))
        (P15 q*(z9 q*r15 q+2)) :=
    close4_mul hP hTarget (Or.inl rfl) hTdivClose
  have hVclose :
      Close4 (W16 q/2)
        (P15 q*(z9 q*r15 q+2)) := by
    have hsum := close4_add' (close4_add' hA hB) hPTclose
    unfold W16
    convert hsum using 1 <;> ring
  have hV : Unit2 (W16 q/2) := by
    refine ⟨div_ne_zero (W16_pos_b q).ne' (by norm_num), ?_⟩
    change padicValRat 2 (W16 q/2)=0
    rw [padicValRat.div (W16_pos_b q).ne' (by norm_num)]
    change v2 (W16 q)-v2 (2:ℚ)=0
    rw [W16_val q h,hr0]
    have htwo : v2 (2:ℚ)=1 := by
      change padicValRat 2 (2:ℚ)=1
      rw [show (2:ℚ)=((2:ℕ):ℚ) by norm_num,
        padicValRat.self (by norm_num)]
    rw [htwo]
    norm_num
  have hNumClose0 :
      Close4 ((W16 q/2)*z7 q)
        (P15 q*(z9 q*r15 q+2)*z7 q) := by
    have hm := close4_mul hV hz7 hVclose (Or.inl rfl)
    simpa [mul_assoc] using hm
  have hFirst : Close4 ((P15 q)^2*r15 q) (r15 q) := by
    have hm := close4_mul hP2 hr hP2close (Or.inl rfl)
    simpa using hm
  have hTwo : Close4 (2*(P15 q*z7 q)) 2 :=
    two_mul_unit_close_two' (hP.mul hz7)
  have hTargetNum :
      Close4 (P15 q*(z9 q*r15 q+2)*z7 q)
        (r15 q+2) := by
    have hs := close4_add' hFirst hTwo
    convert hs using 1 ; unfold P15 ; ring
  have hrplus : Close4 (r15 q+2) (-r15 q) := by
    rw [close4_iff_vge']
    have huadd : VGe 1 (r15 q+1) := by
      by_cases heq : r15 q+1=0
      · exact Or.inl heq
      · right
        exact unit_one_add_val hr heq
    have hm := vge_two'.mul' huadd
    convert hm using 1 ; ring
  have hNumClose : Close4 ((W16 q/2)*z7 q) (-r15 q) :=
    close4_trans hNumClose0 (close4_trans hTargetNum hrplus)
  have hNum : Unit2 ((W16 q/2)*z7 q) := hV.mul hz7
  have hIclose : Close4 (I15 q) 1 := by
    rw [close4_iff_vge']
    unfold I15
    have hm := ((vge_two'.mul' (vge_of_unit' hz9)).mul'
      (vge_of_unit' hr)).mul' hH1
    have hm2 : VGe 2 (2*z9 q*r15 q*H15 q) := by
      simpa [add_assoc] using hm
    convert hm2 using 1 ; ring
  have hIPclose : Close4 (I15 q*(P15 q)^2) 1 := by
    have hm := close4_mul hI hone hIclose hP2close
    simpa using hm
  have hDenClose :
      Close4 (I15 q*(P15 q)^2*r15 q) (r15 q) := by
    have hm := close4_mul (hI.mul hP2) hr hIPclose (Or.inl rfl)
    simpa [mul_assoc] using hm
  have hDen : Unit2 (I15 q*(P15 q)^2*r15 q) :=
    (hI.mul hP2).mul hr
  have hqClose : Close4 (q16 q) (-1) := by
    have hd := close4_div_units_r hNum hDen hr hNumClose hDenClose
    rw [q16_formula_W_d q]
    have heq :
        W16 q*z7 q/(2*I15 q*(P15 q)^2*r15 q) =
          ((W16 q/2)*z7 q)/(I15 q*(P15 q)^2*r15 q) := by
      field_simp [hI.1,hP.1,hr.1]
    rw [heq]
    convert hd using 1 ; field_simp [hr.1]
  have hq := q16_unit_proved_b q h
  have hm := close4_mul hM
    (show Unit2 (-1:ℚ) by
      norm_num [Unit2,padicValRat.neg,padicValRat.one])
    hMclose hqClose
  convert hm using 1 ; ring

def VClose (k : ℤ) (a b : ℚ) : Prop := VGe k (a-b)

lemma VClose.refl {k : ℤ} {a : ℚ} : VClose k a a := by
  left
  ring

lemma VClose.symm {k : ℤ} {a b : ℚ} (h : VClose k a b) :
    VClose k b a := by
  unfold VClose at h ⊢
  have hn := h.neg'
  convert hn using 1 ; ring

lemma VClose.add {k : ℤ} {a b A B : ℚ}
    (h1 : VClose k a A) (h2 : VClose k b B) :
    VClose k (a+b) (A+B) := by
  unfold VClose at h1 h2 ⊢
  have h := h1.add h2
  convert h using 1 ; ring

lemma VClose.trans {k : ℤ} {a b c : ℚ}
    (h1 : VClose k a b) (h2 : VClose k b c) :
    VClose k a c := by
  unfold VClose at h1 h2 ⊢
  have h := h1.add h2
  convert h using 1 ; ring

lemma VClose.mul {k : ℤ} {q r Q R : ℚ}
    (hq : VGe 0 q) (hR : VGe 0 R)
    (h1 : VClose k q Q) (h2 : VClose k r R) :
    VClose k (q*r) (Q*R) := by
  unfold VClose at h1 h2 ⊢
  have hs1 := hq.mul' h2
  have hs2 := h1.mul' hR
  have hs2' : VGe (0+k) ((q-Q)*R) := by
    simpa [add_comm] using hs2
  have hs := hs1.add hs2'
  have hs' : VGe k (q*(r-R)+(q-Q)*R) := by
    simpa using hs
  convert hs' using 1 ; ring

lemma unit_sq_vclose3_r {a : ℚ} (ha : Unit2 a) :
    VClose 3 (a^2) 1 := by
  unfold VClose
  by_cases heq : a^2=1
  · left
    linarith
  · right
    exact unit_sq_sub_one_val ha (sub_ne_zero.mpr heq)

set_option maxHeartbeats 2200000 in
lemma M16_q16_close_one_rpos (q : ℕ) (h : TubeAt (14*q))
    (hrpos : 0 < v2 (r15 q)) :
    Close4 (M16 q*q16 q) 1 := by
  rcases initial_cancellation q h with ⟨hz4,hz5,hz6,hz7,hz8⟩
  have hz9 := z9_unit q h
  rcases H_I_J_K_data q h with ⟨hHn,hI,hJ,hK⟩
  have hP : Unit2 (P15 q) := by
    unfold P15
    exact hz7.mul hz9
  have hP2 : Unit2 ((P15 q)^2) := by
    simpa [pow_two] using hP.mul hP
  have hrN : Nonneg2' (r15 q) :=
    ⟨r15_ne_c q,le_of_lt hrpos⟩
  have hH : Unit2 (H15 q) := by
    have hPrN := nonneg_mul' (unit_nonneg' hP) hrN
    have hprpos : 0 < v2 (P15 q*r15 q) := by
      change 0 < padicValRat 2 (P15 q*r15 q)
      rw [padicValRat.mul hP.1 hrN.1]
      change 0 < v2 (P15 q)+v2 (r15 q)
      rw [hP.2]
      simpa using hrpos
    unfold H15
    exact unit_one_add_of_pos hPrN.1
      (by simpa [H15] using (H15_pos_c q).ne') hprpos
  have hY : Unit2 (Y16 q) := by
    unfold Y16
    exact (hI.mul hJ).mul hK
  have hone : Unit2 (1:ℚ) := ⟨one_ne_zero,padicValRat.one⟩
  have hPone : P15 q+1=8*z6 q*r15 q := by
    unfold P15 r15 q10
    field_simp [z6_ne]
    ring
  have hz6N : Nonneg2' (z6 q) := ⟨z6_ne q,hz6⟩
  have hPone4 : VGe 4 (P15 q+1) := by
    rw [hPone]
    have hr1 : VGe 1 (r15 q) := Or.inr (by omega)
    have hm := (vge_eight_b.mul' (vge_of_nonneg' hz6N)).mul' hr1
    simpa [add_assoc] using hm
  have hPclose3 : VClose 3 (P15 q) (-1) := by
    unfold VClose
    have hw := VGe.weaken' (k:=3) (l:=4) (by norm_num) hPone4
    convert hw using 1 ; ring
  have hPclose : Close4 (P15 q) (-1) := by
    rw [close4_iff_vge']
    unfold VClose at hPclose3
    exact VGe.weaken' (k:=2) (l:=3) (by norm_num) hPclose3
  let d : ℚ := z9 q*r15 q*H15 q
  have hdN : Nonneg2' d := by
    dsimp [d]
    exact nonneg_mul' (nonneg_mul' (unit_nonneg' hz9) hrN)
      (unit_nonneg' hH)
  have hd1 : VGe 1 d := by
    right
    dsimp [d]
    change 1 ≤ padicValRat 2 (z9 q*r15 q*H15 q)
    rw [padicValRat.mul
        (mul_ne_zero hz9.1 hrN.1) hH.1,
      padicValRat.mul hz9.1 hrN.1]
    change 1 ≤ v2 (z9 q)+v2 (r15 q)+v2 (H15 q)
    rw [hz9.2,hH.2]
    omega
  have hJclose3 : VClose 3 (J15 q) 1 := by
    unfold VClose J15
    have hr1 : VGe 1 (r15 q) := Or.inr (by omega)
    have hzratio := hz9.div hz8
    have hm := ((((vge_four'.mul' (vge_of_unit' hzratio)).mul'
      hr1).mul' (vge_of_unit' hH)).mul' (vge_of_unit' hI))
    have hm3 : VGe 3
        (4*(z9 q/z8 q)*r15 q*H15 q*I15 q) := by
      simpa [add_assoc] using hm
    convert hm3 using 1 ; ring
  have hKclose3 : VClose 3 (K15 q) 1 := by
    unfold VClose K15
    have honeDiv := hone.div hz8
    have hr1 : VGe 1 (r15 q) := Or.inr (by omega)
    have hm := (((((vge_eight_b.mul' (vge_of_unit' honeDiv)).mul'
      hr1).mul' (vge_of_unit' hH)).mul' (vge_of_unit' hI)).mul'
        (vge_of_unit' hJ))
    have hm4 : VGe 4
        (8*(1/z8 q)*r15 q*H15 q*I15 q*J15 q) := by
      simpa [add_assoc] using hm
    have hm3 := VGe.weaken' (k:=3) (l:=4) (by norm_num) hm4
    convert hm3 using 1 ; ring
  have hJKclose3 : VClose 3 (J15 q*K15 q) 1 := by
    have hm := VClose.mul (vge_of_unit' hJ) (vge_of_unit' hone)
      hJclose3 hKclose3
    simpa using hm
  have hYIclose3 : VClose 3 (Y16 q) (I15 q) := by
    have hm := VClose.mul (vge_of_unit' hI) (vge_of_unit' hone)
      (VClose.refl) hJKclose3
    unfold Y16
    convert hm using 1 <;> ring
  have hIeq : I15 q=1+2*d := by
    unfold I15
    dsimp [d]
    ring
  have hYclose3 : VClose 3 (Y16 q) (1+2*d) := by
    rw [← hIeq]
    exact hYIclose3
  have hHsq3 := unit_sq_vclose3_r hH
  have hHI : Unit2 (H15 q*I15 q) := hH.mul hI
  have hHIsq3 := unit_sq_vclose3_r hHI
  have hU4 : Unit2 ((z9 q/z8 q)*(H15 q*I15 q)^2) := by
    have hs : Unit2 ((H15 q*I15 q)^2) := by
      simpa [pow_two] using hHI.mul hHI
    exact (hz9.div hz8).mul hs
  have htermH : VGe 3 (2*z9 q*((H15 q)^2-1)) := by
    unfold VClose at hHsq3
    have hm := (vge_two'.mul' (vge_of_unit' hz9)).mul' hHsq3
    have hm4 : VGe 4 (2*z9 q*((H15 q)^2-1)) := by
      simpa [add_assoc] using hm
    exact VGe.weaken' (k:=3) (l:=4) (by norm_num) hm4
  have hterm4 : VGe 3
      (4*((z9 q/z8 q)*(H15 q*I15 q)^2-1)) := by
    have hu1 := unit_sub_one_vge' _ hU4
    have hm := vge_four'.mul' hu1
    simpa using hm
  have hterm8 : VGe 3
      (8*(1/z8 q)*(H15 q*I15 q*J15 q)^2) := by
    have hHIJ := (hH.mul hI).mul hJ
    have hs : Unit2 ((H15 q*I15 q*J15 q)^2) := by
      simpa [pow_two] using hHIJ.mul hHIJ
    have hu := (hone.div hz8).mul hs
    have hm := vge_eight_b.mul' (vge_of_unit' hu)
    convert hm using 1 ; ring
  have hLclose3 :
      VClose 3 (L15 q) (P15 q+2*z9 q+4) := by
    unfold VClose
    rw [L15_formula_c q]
    have hs := (htermH.add hterm4).add hterm8
    convert hs using 1 ; ring
  have hEight : VClose 3 (8*z6 q) 0 := by
    unfold VClose
    have hm := vge_eight_b.mul' (vge_of_nonneg' hz6N)
    convert hm using 1 ; ring
  have hBclose3 :
      VClose 3 (8*z6 q+L15 q) (P15 q+2*z9 q+4) := by
    have hm := VClose.add hEight hLclose3
    convert hm using 1 ; ring
  let Bt : ℚ := P15 q+2*z9 q+4
  have hBt : Unit2 Bt := by
    have hcorr : VGe 1 (2*z9 q+4) := by
      have h2 := vge_two'.mul' (vge_of_unit' hz9)
      have h4 : VGe 2 (4:ℚ) := vge_four'
      have h4w := VGe.weaken' (k:=1) (l:=2) (by norm_num) h4
      exact h2.add h4w
    have hne : P15 q+(2*z9 q+4) ≠ 0 := by
      unfold P15
      positivity [z7_pos15 q,z9_pos15_c q]
    dsimp [Bt]
    have hm := unit_add_vge_one_b hP hcorr hne
    convert hm using 1 ; ring
  have hOne2d : Unit2 (1+2*d) := by
    have h2d : VGe 1 (2*d) := by
      have hm := vge_two'.mul' (vge_of_nonneg' hdN)
      simpa using hm
    exact unit_add_vge_one_b hone h2d (by
      dsimp [d]
      positivity [z9_pos15_c q,r15_pos_c q,H15_pos_c q])
  let E : ℚ := (1+2*d)*Bt
  have hE : Unit2 E := by
    dsimp [E]
    exact hOne2d.mul hBt
  have hNumclose3 :
      VClose 3 (Y16 q*(8*z6 q+L15 q)) E := by
    have hm := VClose.mul (vge_of_unit' hY) (vge_of_unit' hBt)
      hYclose3 (by simpa [Bt] using hBclose3)
    simpa [E] using hm
  have hP2close3 := unit_sq_vclose3_r hP
  have hEPclose3 : VClose 3 (E*(P15 q)^2) E := by
    have hm := VClose.mul (vge_of_unit' hE) (vge_of_unit' hone)
      (VClose.refl) hP2close3
    simpa using hm
  have hNumEPclose3 :
      VClose 3 (Y16 q*(8*z6 q+L15 q)) (E*(P15 q)^2) :=
    VClose.trans hNumclose3 hEPclose3.symm
  have hMcloseE3 : VClose 3 (M16 q) E := by
    unfold VClose at hNumEPclose3 ⊢
    have hdv := VGe.div_unit_r hNumEPclose3 hP2
    rw [M16_formula_r q]
    have hquot :
        (P15 q+H15 q*Y16 q)/r15 q=8*z6 q+L15 q := by
      have hL : H15 q*Y16 q-1=r15 q*L15 q := by
        unfold L15 Y16
        field_simp [r15_ne_c]
      have hbase := hPone
      field_simp [r15_ne_c]
      linarith
    rw [show
      Y16 q*(P15 q+H15 q*Y16 q)/((P15 q)^2*r15 q) =
        Y16 q*((P15 q+H15 q*Y16 q)/r15 q)/(P15 q)^2 by
          field_simp [P15_ne_c,r15_ne_c],
      hquot]
    convert hdv using 1 ; field_simp [P15_ne_c]
  let T : ℚ := z9 q+1+d
  have hEtarget3 : VClose 3 E (1+2*T) := by
    unfold VClose
    have hP3 := VGe.weaken' (k:=3) (l:=4) (by norm_num) hPone4
    have h2dP : VGe 3 (2*d*(P15 q+1)) := by
      have hm := (vge_two'.mul' hd1).mul' hPone4
      have hm6 : VGe 6 (2*d*(P15 q+1)) := by
        simpa [add_assoc] using hm
      exact VGe.weaken' (k:=3) (l:=6) (by norm_num) hm6
    have hzplus : VGe 1 (z9 q+1) := by
      right
      exact unit_one_add_val hz9 (by positivity [z9_pos15_c q])
    have h4dz : VGe 3 (4*d*(z9 q+1)) := by
      have hm := (vge_four'.mul' hd1).mul' hzplus
      have hm4 : VGe 4 (4*d*(z9 q+1)) := by
        simpa [add_assoc] using hm
      exact VGe.weaken' (k:=3) (l:=4) (by norm_num) hm4
    have hs := (hP3.add h2dP).add h4dz
    dsimp [E,Bt,T]
    convert hs using 1 ; ring
  have hMtarget3 : VClose 3 (M16 q) (1+2*T) :=
    VClose.trans hMcloseE3 hEtarget3
  let N : ℚ := (M16 q-1)/2
  have hNclose : Close4 N T := by
    rw [close4_iff_vge']
    unfold VClose at hMtarget3
    have hdv := VGe.div_two_r (k:=2) hMtarget3
    dsimp [N]
    convert hdv using 1 ; dsimp [T] ; ring
  have hMclose1 : Close4 (M16 q) 1 := by
    rw [close4_iff_vge']
    unfold VClose at hMtarget3
    have hT1 : VGe 1 T := by
      dsimp [T]
      have hz1 : VGe 1 (z9 q+1) := by
        right
        exact unit_one_add_val hz9 (by positivity [z9_pos15_c q])
      exact hz1.add hd1
    have h2T : VGe 2 (2*T) := by
      have hm := vge_two'.mul' hT1
      simpa using hm
    have htarget : VGe 2 ((1+2*T)-1) := by
      convert h2T using 1 ; ring
    have hm := (VGe.weaken' (k:=2) (l:=3) (by norm_num) hMtarget3).add htarget
    convert hm using 1 ; ring
  have hM : Unit2 (M16 q) :=
    unit_of_close4' hone hMclose1 (by
      unfold M16
      exact mul_ne_zero (z13_ne q) (z15_ne q))
  have hIclose : Close4 (I15 q) 1 := by
    rw [close4_iff_vge']
    rw [hIeq]
    have h2d : VGe 2 (2*d) := by
      have hm := vge_two'.mul' hd1
      simpa using hm
    convert h2d using 1 ; ring
  have hHIclose : Close4 (H15 q*I15 q) (H15 q) := by
    have hm := close4_mul hH hone (Or.inl rfl) hIclose
    simpa using hm
  have hZ12Hdiv :
      Close4 (z12 q) (H15 q/z7 q) := by
    rw [z12_formula15_c q]
    exact close4_div_units_r (hH.mul hI) hz7 hz7
      hHIclose (Or.inl rfl)
  have hHdiv :
      H15 q/z7 q=1/z7 q+z9 q*r15 q := by
    unfold H15 P15
    field_simp [z7_ne]
  have hInv7 : Close4 (1/z7 q) (z7 q) :=
    inv_close_self_unit_r hz7
  have hHdivClose :
      Close4 (H15 q/z7 q) (z7 q+z9 q*r15 q) := by
    rw [hHdiv]
    exact close4_add' hInv7 (Or.inl rfl)
  have hZ12close :
      Close4 (z12 q) (z7 q+z9 q*r15 q) :=
    close4_trans hZ12Hdiv hHdivClose
  have hdclose : Close4 d (z9 q*r15 q) := by
    rw [close4_iff_vge']
    have hr1 : VGe 1 (r15 q) := Or.inr (by omega)
    have hm := (((vge_of_unit' hz9).mul' hr1).mul'
      (vge_of_unit' hP)).mul' hr1
    have hm2 : VGe 2
        (z9 q*r15 q*P15 q*r15 q) := by
      simpa [add_assoc] using hm
    dsimp [d]
    unfold H15
    convert hm2 using 1 ; ring
  have hZ7neg : Close4 (z7 q) (-z9 q) := by
    have hpdiv := close4_div_units_r hP hz9 hz9
      hPclose (Or.inl rfl)
    have hinvneg := close4_neg'2 (inv_close_self_unit_r hz9)
    unfold P15 at hpdiv
    have hpdiv' : Close4 (z7 q) ((-1)/z9 q) := by
      convert hpdiv using 1 ; field_simp [hz9.1]
    have hinvneg' : Close4 ((-1)/z9 q) (-z9 q) := by
      convert hinvneg using 1 ; field_simp [hz9.1]
    exact close4_trans hpdiv' hinvneg'
  have hNegShift : Close4 (-z9 q) (z9 q+2) := by
    rw [close4_iff_vge']
    have hzplus : VGe 1 (z9 q+1) := by
      right
      exact unit_one_add_val hz9 (by positivity [z9_pos15_c q])
    have hm := vge_two'.mul' hzplus
    convert hm.neg' using 1 ; ring
  have hBase : Close4 (z9 q+2) (z7 q) :=
    close4_symm (close4_trans hZ7neg hNegShift)
  have hRight :
      Close4 (z9 q+2+d) (z7 q+z9 q*r15 q) :=
    close4_add' hBase hdclose
  have hOneN : Close4 (1+N) (z12 q) := by
    have honeClose : Close4 (1:ℚ) 1 := Or.inl rfl
    have ha := close4_add' honeClose hNclose
    have hb : Close4 (1+T) (z9 q+2+d) := by
      dsimp [T]
      exact Or.inl (by ring)
    exact close4_trans ha
      (close4_trans hb (close4_trans hRight (close4_symm hZ12close)))
  have hZ12 : Unit2 (z12 q) := by
    rw [z12_formula15_c q]
    exact (hH.mul hI).div hz7
  have hz13p : 0 < z13 q := by
    unfold z13
    exact div_pos (x_pos _) (by norm_num)
  have hz15p : 0 < z15 q := by
    unfold z15
    exact x_pos _
  have hmpos : 0 < M16 q := by
    unfold M16
    exact mul_pos hz13p hz15p
  have hOneNpos : 0 < 1+N := by
    have heq : 1+N=(1+M16 q)/2 := by
      dsimp [N]
      ring
    rw [heq]
    positivity
  have hOneNU : Unit2 (1+N) :=
    unit_of_close4' hZ12 hOneN hOneNpos.ne'
  have hqFormula : q16 q=(1+N)/z12 q := by
    change q16 q=(1+(M16 q-1)/2)/z12 q
    unfold q16 M16
    field_simp [z12_ne]
    ring
  have hqClose : Close4 (q16 q) 1 := by
    rw [hqFormula]
    have hd := close4_div_units_r hOneNU hZ12 hZ12
      hOneN (Or.inl rfl)
    convert hd using 1
    field_simp [hZ12.1]
  have hq := q16_unit_proved_b q h
  have hm := close4_mul hM hone hMclose1 hqClose
  simpa using hm

lemma M16_q16_close_one_r (q : ℕ) (h : TubeAt (14*q)) :
    Close4 (M16 q*q16 q) 1 := by
  have hrnonneg : 0 ≤ v2 (r15 q) := by
    simpa [r15] using q10_nonneg_proved_e q h
  by_cases hr0 : v2 (r15 q)=0
  · exact M16_q16_close_one_runit q h hr0
  · apply M16_q16_close_one_rpos q h
    omega

lemma z16_close_neg_u0_r (q : ℕ) (h : TubeAt (14*q)) :
    Close4 (z16 q) (-u0 q) := by
  rcases initial_cancellation q h with ⟨hz4,hz5,hz6,hz7,hz8⟩
  have hz9 := z9_unit q h
  rcases H_I_J_K_data q h with ⟨hH,hI,hJ,hK⟩
  have hz13 : Unit2 (z13 q) := by
    rw [z13_formula15_c q]
    exact (hI.mul hJ).div hz8
  have hq15 := q15_unit_proved_b q h
  have hz15 : Unit2 (z15 q) := by
    rw [z15_eq_K_mul_q15_d q]
    exact hK.mul hq15
  have hM : Unit2 (M16 q) := by
    unfold M16
    exact hz13.mul hz15
  have hq16 := q16_unit_proved_b q h
  have hz14 : Unit2 (z14 q) := by
    rw [z14_formula15_c q]
    exact (hJ.mul hK).div hz9
  have hquot :
      Close4 ((M16 q*q16 q)/z14 q) (1/z14 q) :=
    close4_div_units_r (hM.mul hq16) hz14 hz14
      (M16_q16_close_one_r q h) (Or.inl rfl)
  rw [z16_via_M16_r q]
  exact close4_trans
    (close4_trans hquot (inv_close_self_unit_r hz14))
    (z14_close_neg_u0_r q h)

structure CancellationCore (q : ℕ) : Prop where
  q10_nonneg : 0 ≤ v2 (q10 q)
  q15_unit : Unit2 (q15 q)
  q16_unit : Unit2 (q16 q)
  z14_close_neg_u0 : Close4 (z14 q) (-u0 q)
  z16_close_neg_u0 : Close4 (z16 q) (-u0 q)

lemma cancellation_core (q : ℕ) (h : TubeAt (14*q)) :
    CancellationCore q := by
  exact ⟨q10_nonneg_proved_e q h,
    q15_unit_proved_b q h,
    q16_unit_proved_b q h,
    z14_close_neg_u0_r q h,
    z16_close_neg_u0_r q h⟩

/-- Everything after the first exceptional cancellation.  These are exactly
the q10, q15, q16, and returned-mod-four calculations still to formalize. -/
structure LateCertificate (q : ℕ) : Prop where
  z10_nonneg : 0 ≤ v2 (z10 q)
  z11_nonneg : 0 ≤ v2 (z11 q)
  z12_nonneg : 0 ≤ v2 (z12 q)
  z13_nonneg : 0 ≤ v2 (z13 q)
  z14_unit : Unit2 (z14 q)
  z15_unit : Unit2 (z15 q)
  z16_unit : Unit2 (z16 q)
  z17_unit : Unit2 (z17 q)
  returned_close : Close4 (z14 q) (z16 q)

lemma late_cancellation14 (q : ℕ) (h : TubeAt (14*q)) :
    LateCertificate q := by
  have ht := h
  unfold TubeAt at ht
  have hu0 : Unit2 (u0 q) := by simpa [u0] using ht.1
  rcases initial_cancellation q h with ⟨hz4, hz5, hz6, hz7, hz8⟩
  have hz9 := z9_unit q h
  have core := cancellation_core q h
  have hcoef10 : Unit2 (z7 q*z9 q/z8 q) :=
    (hz7.mul hz9).div hz8
  have hz10 : 0 ≤ v2 (z10 q) := by
    rw [z10_eq_q10 q]
    change 0 ≤ padicValRat 2 ((z7 q*z9 q/z8 q)*q10 q)
    rw [padicValRat.mul hcoef10.1 (q10_ne q)]
    change 0 ≤ v2 (z7 q*z9 q/z8 q)+v2 (q10 q)
    rw [hcoef10.2]
    simpa using core.q10_nonneg
  have hHne : 1+z8 q*z10 q ≠ 0 := by
    unfold z8 z10
    have h8 := x_pos (14*q+8)
    have h10 := x_pos (14*q+10)
    positivity
  have hz11 : 0 ≤ v2 (z11 q) :=
    z5_nonneg_generic hz7 hz8 hz9 (z10_ne q) hz10 hHne (z11_formula q)
  have hprodH : 0 ≤ v2 (z8 q*z10 q) := by
    change 0 ≤ padicValRat 2 (z8 q*z10 q)
    rw [padicValRat.mul hz8.1 (z10_ne q)]
    change 0 ≤ v2 (z8 q)+v2 (z10 q)
    rw [hz8.2]
    simpa using hz10
  have hHnonneg : 0 ≤ v2 (1+z8 q*z10 q) :=
    one_add_val_nonneg hHne hprodH
  have hval11 : v2 (z11 q) =
      v2 (z10 q)+v2 (1+z8 q*z10 q)-1 := by
    have hnum : z8 q*z10 q*(1+z8 q*z10 q) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hz8.1 (z10_ne q)) hHne
    have hden : 2*z7 q*z9 q ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hz7.1) hz9.1
    rw [z11_formula q]
    change padicValRat 2
      (z8 q*z10 q*(1+z8 q*z10 q)/(2*z7 q*z9 q)) =
      v2 (z10 q)+v2 (1+z8 q*z10 q)-1
    rw [padicValRat.div hnum hden,
      padicValRat.mul (mul_ne_zero hz8.1 (z10_ne q)) hHne,
      padicValRat.mul hz8.1 (z10_ne q),
      padicValRat.mul (mul_ne_zero (by norm_num) hz7.1) hz9.1,
      padicValRat.mul (by norm_num) hz7.1]
    change v2 (z8 q)+v2 (z10 q)+v2 (1+z8 q*z10 q)-
      (v2 (2:ℚ)+v2 (z7 q)+v2 (z9 q)) =
      v2 (z10 q)+v2 (1+z8 q*z10 q)-1
    rw [hz7.2, hz8.2, hz9.2]
    have htwo : v2 (2:ℚ)=1 := by
      change padicValRat 2 (2:ℚ)=1
      rw [show (2:ℚ)=((2:ℕ):ℚ) by norm_num,
        padicValRat.self (by norm_num)]
    rw [htwo]
    ring
  have hF11 : Unit2 (1+4*z9 q*z11 q) :=
    unit_one_add_four_mul hz9.1 (z11_ne q) (by rw [hz9.2]) hz11
  have hval12 : v2 (z12 q) = 1+v2 (z11 q)-v2 (z10 q) := by
    have hnum : 2*z9 q*z11 q*(1+4*z9 q*z11 q) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hz9.1)
        (z11_ne q)) hF11.1
    have hden : z8 q*z10 q ≠ 0 :=
      mul_ne_zero hz8.1 (z10_ne q)
    rw [z12_formula q]
    change padicValRat 2
      (2*z9 q*z11 q*(1+4*z9 q*z11 q)/(z8 q*z10 q)) =
      1+v2 (z11 q)-v2 (z10 q)
    rw [padicValRat.div hnum hden,
      padicValRat.mul
        (mul_ne_zero (mul_ne_zero (by norm_num) hz9.1) (z11_ne q)) hF11.1,
      padicValRat.mul (mul_ne_zero (by norm_num) hz9.1) (z11_ne q),
      padicValRat.mul (by norm_num) hz9.1,
      padicValRat.mul hz8.1 (z10_ne q)]
    change v2 (2:ℚ)+v2 (z9 q)+v2 (z11 q)+
      v2 (1+4*z9 q*z11 q)-(v2 (z8 q)+v2 (z10 q)) =
      1+v2 (z11 q)-v2 (z10 q)
    rw [hz8.2, hz9.2, hF11.2]
    have htwo : v2 (2:ℚ)=1 := by
      change padicValRat 2 (2:ℚ)=1
      rw [show (2:ℚ)=((2:ℕ):ℚ) by norm_num,
        padicValRat.self (by norm_num)]
    rw [htwo]
    ring
  have hz12 : 0 ≤ v2 (z12 q) := by omega
  have hF12 : Unit2 (1+4*z10 q*z12 q) :=
    unit_one_add_four_mul (z10_ne q) (z12_ne q) hz10 hz12
  have hval13 : v2 (z13 q) =
      v2 (z10 q)+v2 (z12 q)-1-v2 (z11 q) := by
    have hnum : z10 q*z12 q*(1+4*z10 q*z12 q) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (z10_ne q) (z12_ne q)) hF12.1
    have hden : 2*z9 q*z11 q ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hz9.1) (z11_ne q)
    rw [z13_formula q]
    change padicValRat 2
      (z10 q*z12 q*(1+4*z10 q*z12 q)/(2*z9 q*z11 q)) =
      v2 (z10 q)+v2 (z12 q)-1-v2 (z11 q)
    rw [padicValRat.div hnum hden,
      padicValRat.mul (mul_ne_zero (z10_ne q) (z12_ne q)) hF12.1,
      padicValRat.mul (z10_ne q) (z12_ne q),
      padicValRat.mul (mul_ne_zero (by norm_num) hz9.1) (z11_ne q),
      padicValRat.mul (by norm_num) hz9.1]
    change v2 (z10 q)+v2 (z12 q)+v2 (1+4*z10 q*z12 q)-
      (v2 (2:ℚ)+v2 (z9 q)+v2 (z11 q)) =
      v2 (z10 q)+v2 (z12 q)-1-v2 (z11 q)
    rw [hF12.2, hz9.2]
    have htwo : v2 (2:ℚ)=1 := by
      change padicValRat 2 (2:ℚ)=1
      rw [show (2:ℚ)=((2:ℕ):ℚ) by norm_num,
        padicValRat.self (by norm_num)]
    rw [htwo]
    ring
  have hz13val : v2 (z13 q)=0 := by omega
  have hz13 : Unit2 (z13 q) := ⟨z13_ne q, hz13val⟩
  have hF13 : Unit2 (1+16*z11 q*z13 q) :=
    unit_one_add_sixteen_mul (z11_ne q) hz13.1 hz11 (by rw [hz13.2])
  have hval14 : v2 (z14 q) =
      1+v2 (z11 q)-v2 (z10 q)-v2 (z12 q) := by
    have hnum : 2*z11 q*z13 q*(1+16*z11 q*z13 q) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (z11_ne q))
        hz13.1) hF13.1
    have hden : z10 q*z12 q ≠ 0 :=
      mul_ne_zero (z10_ne q) (z12_ne q)
    rw [z14_formula q]
    change padicValRat 2
      (2*z11 q*z13 q*(1+16*z11 q*z13 q)/(z10 q*z12 q)) =
      1+v2 (z11 q)-v2 (z10 q)-v2 (z12 q)
    rw [padicValRat.div hnum hden,
      padicValRat.mul
        (mul_ne_zero (mul_ne_zero (by norm_num) (z11_ne q)) hz13.1) hF13.1,
      padicValRat.mul (mul_ne_zero (by norm_num) (z11_ne q)) hz13.1,
      padicValRat.mul (by norm_num) (z11_ne q),
      padicValRat.mul (z10_ne q) (z12_ne q)]
    change v2 (2:ℚ)+v2 (z11 q)+v2 (z13 q)+
      v2 (1+16*z11 q*z13 q)-(v2 (z10 q)+v2 (z12 q)) =
      1+v2 (z11 q)-v2 (z10 q)-v2 (z12 q)
    rw [hz13.2, hF13.2]
    have htwo : v2 (2:ℚ)=1 := by
      change padicValRat 2 (2:ℚ)=1
      rw [show (2:ℚ)=((2:ℕ):ℚ) by norm_num,
        padicValRat.self (by norm_num)]
    rw [htwo]
    ring
  have hz14val : v2 (z14 q)=0 := by omega
  have hz14 : Unit2 (z14 q) := ⟨z14_ne q, hz14val⟩
  have hsum15 : 1+z12 q*z14 q ≠ 0 := by
    unfold z12 z14
    have h12 := x_pos (14*q+12)
    have h14 := x_pos (14*q+14)
    positivity
  have hnum15val : v2 (1+z12 q*z14 q)=v2 (z10 q) := by
    have hv := core.q15_unit.2
    unfold q15 at hv
    change padicValRat 2 ((1+z12 q*z14 q)/z10 q)=0 at hv
    rw [padicValRat.div hsum15 (z10_ne q)] at hv
    change v2 (1+z12 q*z14 q)-v2 (z10 q)=0 at hv
    omega
  have hval15 : v2 (z15 q)=0 := by
    have hnum : z12 q*z14 q*(1+z12 q*z14 q) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (z12_ne q) hz14.1) hsum15
    have hden : 2*z11 q*z13 q ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) (z11_ne q)) hz13.1
    rw [z15_formula q]
    change padicValRat 2
      (z12 q*z14 q*(1+z12 q*z14 q)/(2*z11 q*z13 q))=0
    rw [padicValRat.div hnum hden,
      padicValRat.mul (mul_ne_zero (z12_ne q) hz14.1) hsum15,
      padicValRat.mul (z12_ne q) hz14.1,
      padicValRat.mul (mul_ne_zero (by norm_num) (z11_ne q)) hz13.1,
      padicValRat.mul (by norm_num) (z11_ne q)]
    change v2 (z12 q)+v2 (z14 q)+v2 (1+z12 q*z14 q)-
      (v2 (2:ℚ)+v2 (z11 q)+v2 (z13 q))=0
    rw [hz13.2, hz14.2, hnum15val]
    have htwo : v2 (2:ℚ)=1 := by
      change padicValRat 2 (2:ℚ)=1
      rw [show (2:ℚ)=((2:ℕ):ℚ) by norm_num,
        padicValRat.self (by norm_num)]
    rw [htwo]
    omega
  have hz15 : Unit2 (z15 q) := ⟨z15_ne q, hval15⟩
  have hsum16 : 1+z13 q*z15 q ≠ 0 := by
    unfold z13 z15
    have h13 := x_pos (14*q+13)
    have h15 := x_pos (14*q+15)
    positivity
  have hnum16val : v2 (1+z13 q*z15 q)=1+v2 (z12 q) := by
    have hv := core.q16_unit.2
    unfold q16 at hv
    change padicValRat 2 ((1+z13 q*z15 q)/(2*z12 q))=0 at hv
    rw [padicValRat.div hsum16
      (mul_ne_zero (by norm_num) (z12_ne q)),
      padicValRat.mul (by norm_num) (z12_ne q)] at hv
    change v2 (1+z13 q*z15 q)-
      (v2 (2:ℚ)+v2 (z12 q))=0 at hv
    have htwo : v2 (2:ℚ)=1 := by
      change padicValRat 2 (2:ℚ)=1
      rw [show (2:ℚ)=((2:ℕ):ℚ) by norm_num,
        padicValRat.self (by norm_num)]
    rw [htwo] at hv
    omega
  have hval16 : v2 (z16 q)=0 := by
    have hnum : z13 q*z15 q*(1+z13 q*z15 q) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hz13.1 hz15.1) hsum16
    have hden : 2*z12 q*z14 q ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) (z12_ne q)) hz14.1
    rw [z16_formula q]
    change padicValRat 2
      (z13 q*z15 q*(1+z13 q*z15 q)/(2*z12 q*z14 q))=0
    rw [padicValRat.div hnum hden,
      padicValRat.mul (mul_ne_zero hz13.1 hz15.1) hsum16,
      padicValRat.mul hz13.1 hz15.1,
      padicValRat.mul
        (mul_ne_zero (by norm_num) (z12_ne q)) hz14.1,
      padicValRat.mul (by norm_num) (z12_ne q)]
    change v2 (z13 q)+v2 (z15 q)+v2 (1+z13 q*z15 q)-
      (v2 (2:ℚ)+v2 (z12 q)+v2 (z14 q))=0
    rw [hz13.2, hz14.2, hz15.2, hnum16val]
    have htwo : v2 (2:ℚ)=1 := by
      change padicValRat 2 (2:ℚ)=1
      rw [show (2:ℚ)=((2:ℕ):ℚ) by norm_num,
        padicValRat.self (by norm_num)]
    rw [htwo]
    ring
  have hz16 : Unit2 (z16 q) := ⟨z16_ne q, hval16⟩
  have hreturned : Close4 (z14 q) (z16 q) :=
    close4_trans core.z14_close_neg_u0
      (close4_symm core.z16_close_neg_u0)
  have hprod_close_sq : Close4 (z14 q*z16 q) (u0 q*u0 q) := by
    have hm := close4_mul hz14 (hu0.neg)
      core.z14_close_neg_u0 core.z16_close_neg_u0
    convert hm using 1 ; ring
  have hsq_close : Close4 (u0 q*u0 q) 1 := by
    by_cases heq : u0 q*u0 q=1
    · exact Or.inl heq
    · right
      have hpow : u0 q^2-1 ≠ 0 := by
        intro hz
        apply heq
        rw [pow_two] at hz
        exact sub_eq_zero.mp hz
      have hv := unit_sq_sub_one_val hu0 hpow
      change 2 ≤ v2 (u0 q*u0 q-1)
      rw [← pow_two]
      omega
  have hprod_close : Close4 (z14 q*z16 q) 1 :=
    close4_trans hprod_close_sq hsq_close
  have hprod : Unit2 (z14 q*z16 q) := hz14.mul hz16
  have hplus_ne : 1+z14 q*z16 q ≠ 0 := by
    unfold z14 z16
    have h14 := x_pos (14*q+14)
    have h16 := x_pos (14*q+16)
    positivity
  have hplus_val : v2 (1+z14 q*z16 q)=1 := by
    rcases hprod_close with heq | hdiff
    · rw [heq]
      have htwo : v2 (2:ℚ)=1 := by
        change padicValRat 2 (2:ℚ)=1
        rw [show (2:ℚ)=((2:ℕ):ℚ) by norm_num,
          padicValRat.self (by norm_num)]
      change padicValRat 2 (1+(1:ℚ))=1
      norm_num
      exact htwo
    · have hdiffne : z14 q*z16 q-1 ≠ 0 := by
        intro hz
        rw [hz] at hdiff
        norm_num [padicValRat.zero] at hdiff
      have htwo : v2 (2:ℚ)=1 := by
        change padicValRat 2 (2:ℚ)=1
        rw [show (2:ℚ)=((2:ℕ):ℚ) by norm_num,
          padicValRat.self (by norm_num)]
      have hvne : v2 (2:ℚ) ≠ v2 (z14 q*z16 q-1) := by
        rw [htwo]
        omega
      have hsum : (2:ℚ)+(z14 q*z16 q-1) ≠ 0 := by
        convert hplus_ne using 1 ; ring
      have hv := padicValRat.add_eq_min
        hsum (by norm_num) hdiffne hvne
      change v2 ((2:ℚ)+(z14 q*z16 q-1)) =
        min (v2 (2:ℚ)) (v2 (z14 q*z16 q-1)) at hv
      rw [htwo,min_eq_left (by omega)] at hv
      convert hv using 1 ; ring_nf
  have hz17val : v2 (z17 q)=0 := by
    have hnum : z14 q*z16 q*(1+z14 q*z16 q) ≠ 0 :=
      mul_ne_zero hprod.1 hplus_ne
    have hden : 2*z13 q*z15 q ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hz13.1) hz15.1
    rw [z17_formula q]
    change padicValRat 2
      (z14 q*z16 q*(1+z14 q*z16 q)/(2*z13 q*z15 q))=0
    rw [padicValRat.div hnum hden,
      padicValRat.mul hprod.1 hplus_ne,
      padicValRat.mul (mul_ne_zero (by norm_num) hz13.1) hz15.1,
      padicValRat.mul (by norm_num) hz13.1]
    change v2 (z14 q*z16 q)+v2 (1+z14 q*z16 q)-
      (v2 (2:ℚ)+v2 (z13 q)+v2 (z15 q))=0
    rw [hprod.2,hplus_val,hz13.2,hz15.2]
    have htwo : v2 (2:ℚ)=1 := by
      change padicValRat 2 (2:ℚ)=1
      rw [show (2:ℚ)=((2:ℕ):ℚ) by norm_num,
        padicValRat.self (by norm_num)]
    rw [htwo]
    ring
  have hz17 : Unit2 (z17 q) := ⟨z17_ne q,hz17val⟩
  exact {
    z10_nonneg := hz10
    z11_nonneg := hz11
    z12_nonneg := hz12
    z13_nonneg := by rw [hz13.2]
    z14_unit := hz14
    z15_unit := hz15
    z16_unit := hz16
    z17_unit := hz17
    returned_close := hreturned
  }


lemma pv2_16 : padicValRat 2 (16:ℚ) = 4 := v2_16
lemma pv2_four : padicValRat 2 (4:ℚ) = 2 := v2_four

lemma val_x5 (q : ℕ) :
    v2 (x (14*q+5)) = v2 (z5 q)+4 := by
  unfold z5
  change padicValRat 2 (x (14*q+5)) =
    padicValRat 2 (x (14*q+5)/16)+4
  rw [padicValRat.div (x_ne _) (by norm_num), pv2_16]
  ring

lemma val_x6 (q : ℕ) :
    v2 (x (14*q+6)) = v2 (z6 q)+2 := by
  unfold z6
  change padicValRat 2 (x (14*q+6)) =
    padicValRat 2 (x (14*q+6)/4)+2
  rw [padicValRat.div (x_ne _) (by norm_num), pv2_four]
  ring

lemma val_x7 (q : ℕ) :
    v2 (x (14*q+7)) = v2 (z7 q)+2 := by
  unfold z7
  change padicValRat 2 (x (14*q+7)) =
    padicValRat 2 (x (14*q+7)/4)+2
  rw [padicValRat.div (x_ne _) (by norm_num), pv2_four]
  ring

lemma val_x8 (q : ℕ) :
    v2 (x (14*q+8)) = v2 (z8 q)-2 := by
  unfold z8
  change padicValRat 2 (x (14*q+8)) =
    padicValRat 2 (4*x (14*q+8))-2
  rw [padicValRat.mul (by norm_num) (x_ne _), pv2_four]
  ring

lemma val_x9 (q : ℕ) :
    v2 (x (14*q+9)) = v2 (z9 q)+2 := by
  unfold z9
  change padicValRat 2 (x (14*q+9)) =
    padicValRat 2 (x (14*q+9)/4)+2
  rw [padicValRat.div (x_ne _) (by norm_num), pv2_four]
  ring

lemma val_x10 (q : ℕ) :
    v2 (x (14*q+10)) = v2 (z10 q)+2 := by
  unfold z10
  change padicValRat 2 (x (14*q+10)) =
    padicValRat 2 (x (14*q+10)/4)+2
  rw [padicValRat.div (x_ne _) (by norm_num), pv2_four]
  ring

lemma val_x11 (q : ℕ) :
    v2 (x (14*q+11)) = v2 (z11 q)+4 := by
  unfold z11
  change padicValRat 2 (x (14*q+11)) =
    padicValRat 2 (x (14*q+11)/16)+4
  rw [padicValRat.div (x_ne _) (by norm_num), pv2_16]
  ring

lemma val_x13 (q : ℕ) :
    v2 (x (14*q+13)) = v2 (z13 q)+4 := by
  unfold z13
  change padicValRat 2 (x (14*q+13)) =
    padicValRat 2 (x (14*q+13)/16)+4
  rw [padicValRat.div (x_ne _) (by norm_num), pv2_16]
  ring

lemma val_x17 (q : ℕ) :
    v2 (x (14*q+17)) = v2 (z17 q)+4 := by
  unfold z17
  change padicValRat 2 (x (14*q+17)) =
    padicValRat 2 (x (14*q+17)/16)+4
  rw [padicValRat.div (x_ne _) (by norm_num), pv2_16]
  ring

/--
Assembly of the fourteen-step return.

After writing the input window as `(u₀,u₁,u₂,16u₃)`, normalize the next
fourteen values as

`z₄, 16z₅, 4z₆, 4z₇, z₈/4, 4z₉, 4z₁₀, 16z₁₁,
 z₁₂, 16z₁₃, z₁₄, z₁₅, z₁₆, 16z₁₇`.

The straight-line identities, the cancellation proving that `z₉` is a
unit, all subsequent valuation bookkeeping, and the return assembly are
formalized above and below.  The only finite input still assumed is
`cancellation_core`: `q₁₀ ∈ ℤ₂`, `q₁₅,q₁₆ ∈ ℤ₂ˣ`, and
`z₁₄ ≡ z₁₆ ≡ -u₀ (mod 4)`.
-/
lemma return14 (q : ℕ) (h : TubeAt (14*q)) :
    BoundsAt (14*q) ∧ TubeAt (14*(q+1)) := by
  have ht := h
  unfold TubeAt at ht
  rcases initial_cancellation q h with ⟨hz4, hz5, hz6, hz7, hz8⟩
  have hz9 := z9_unit q h
  have hc := late_cancellation14 q h
  constructor
  · intro r hr
    interval_cases r
    · have hv : 0 ≤ v2 (x (14*q)) := by rw [ht.1.2]
      simpa [ell] using hv
    · have hv : 0 ≤ v2 (x (14*q+1)) := by rw [ht.2.1.2]
      simpa [ell] using hv
    · have hv : 0 ≤ v2 (x (14*q+2)) := by rw [ht.2.2.1.2]
      simpa [ell] using hv
    · have hv : 4 ≤ v2 (x (14*q+3)) := le_of_eq ht.2.2.2.1.2.symm
      simpa [ell] using hv
    · simpa [ell, z4] using hz4
    · have hv := val_x5 q
      have hb : 4 ≤ v2 (x (14*q+5)) := by omega
      simpa [ell] using hb
    · have hv := val_x6 q
      have hb : 2 ≤ v2 (x (14*q+6)) := by omega
      simpa [ell] using hb
    · have hv := val_x7 q
      have hb : 2 ≤ v2 (x (14*q+7)) := by rw [hv, hz7.2]; omega
      simpa [ell] using hb
    · have hv := val_x8 q
      have hb : (-2:ℤ) ≤ v2 (x (14*q+8)) := by rw [hv, hz8.2]; omega
      simpa [ell] using hb
    · have hv := val_x9 q
      have hb : 2 ≤ v2 (x (14*q+9)) := by rw [hv, hz9.2]; omega
      simpa [ell] using hb
    · have hv := val_x10 q
      have hn := hc.z10_nonneg
      have hb : 2 ≤ v2 (x (14*q+10)) := by omega
      simpa [ell] using hb
    · have hv := val_x11 q
      have hn := hc.z11_nonneg
      have hb : 4 ≤ v2 (x (14*q+11)) := by omega
      simpa [ell] using hb
    · simpa [ell, z12] using hc.z12_nonneg
    · have hv := val_x13 q
      have hn := hc.z13_nonneg
      have hb : 4 ≤ v2 (x (14*q+13)) := by omega
      simpa [ell] using hb
  · unfold TubeAt
    have hs : 14*(q+1) = 14*q+14 := by omega
    have h14 : Unit2 (x (14*(q+1))) := by
      simpa [z14, hs] using hc.z14_unit
    have h15 : Unit2 (x (14*(q+1)+1)) := by
      convert hc.z15_unit using 1
    have h16 : Unit2 (x (14*(q+1)+2)) := by
      convert hc.z16_unit using 1
    have h17 : Val4 (x (14*(q+1)+3)) := by
      refine ⟨x_ne _, ?_⟩
      have hv := val_x17 q
      have hv' : v2 (x (14*q+17)) = 4 := by
        rw [hv, hc.z17_unit.2]
        omega
      convert hv' using 1
    have hclose : Close4 (x (14*(q+1))) (x (14*(q+1)+2)) := by
      convert hc.returned_close using 1
    exact ⟨h14, h15, h16, h17, hclose⟩

lemma tube_blocks : ∀ q, TubeAt (14*q) := by
  intro q
  induction q with
  | zero => simpa using tube_zero
  | succ q ih => exact (return14 q ih).2

lemma bounds_blocks (q : ℕ) : BoundsAt (14*q) :=
  (return14 q (tube_blocks q)).1

lemma x_lower (n : ℕ) : ell n ≤ v2 (x n) := by
  have hr : n % 14 < 14 := Nat.mod_lt _ (by norm_num)
  have hb := bounds_blocks (n / 14) (n % 14) hr
  have hdecomp : 14 * (n / 14) + n % 14 = n := by
    have h := Nat.mod_add_div n 14
    omega
  rw [hdecomp] at hb
  have hell : ell (n % 14) = ell n := by simp [ell]
  rwa [hell] at hb

/-! ## Recovering nonnegative valuations for `a` -/

lemma val_a_even (n : ℕ) :
    v2 (a (2*n+2)) = v2 (x (2*n)) + v2 (x (2*n+2)) := by
  have h := congrArg (padicValRat 2) (x_mul_even n)
  rw [padicValRat.mul (x_ne _) (x_ne _)] at h
  exact h.symm

lemma val_a_odd (n : ℕ) :
    v2 (a (2*n+3)) = v2 (x (2*n+1)) + v2 (x (2*n+3)) - 4 := by
  have h := congrArg (padicValRat 2) (x_mul_odd n)
  rw [padicValRat.mul (x_ne _) (x_ne _),
      padicValRat.mul (by norm_num) (a_ne _)] at h
  change v2 (x (2*n+1)) + v2 (x (2*n+3)) =
      v2 (16 : ℚ) + v2 (a (2*n+3)) at h
  rw [v2_16] at h
  omega

lemma val_even_nonneg (n : ℕ) : 0 ≤ v2 (a (2*n+2)) := by
  rw [val_a_even]
  have h0 := x_lower (2*n)
  have h2 := x_lower (2*n+2)
  have hw := word_pair (2*n)
  simp [kExp] at hw
  omega

lemma val_odd_nonneg (n : ℕ) : 0 ≤ v2 (a (2*n+3)) := by
  rw [val_a_odd]
  have h1 := x_lower (2*n+1)
  have h3 := x_lower (2*n+3)
  have hw := word_pair (2*n+1)
  rw [show 2*n+1+2 = 2*n+3 by omega] at hw
  simp [kExp] at hw
  omega

theorem two_adic_val_nonneg (n : ℕ) : 0 ≤ v2 (a n) := by
  match n with
  | 0 =>
      change 0 ≤ padicValRat 2 (a 0)
      rw [show a 0 = 1 from rfl, padicValRat.one]
  | 1 =>
      change 0 ≤ padicValRat 2 (a 1)
      rw [show a 1 = 1 from rfl, padicValRat.one]
  | m+2 =>
    have hm : m % 2 < 2 := Nat.mod_lt _ (by norm_num)
    interval_cases hmod : m % 2
    · have hdecomp : m = 2 * (m / 2) := by
        have h := Nat.mod_add_div m 2
        omega
      rw [hdecomp]
      exact val_even_nonneg (m/2)
    · have hdecomp : m = 2 * (m / 2) + 1 := by
        have h := Nat.mod_add_div m 2
        omega
      rw [hdecomp]
      exact val_odd_nonneg (m/2)

/-! ## Odd primes and the final integrality bridge -/

def oddB (n : ℕ) : ℚ := a n + 1

lemma oddB_pos (n : ℕ) : 0 < oddB n := by
  unfold oddB
  have := a_pos n
  linarith

lemma oddB_ne (n : ℕ) : oddB n ≠ 0 := (oddB_pos n).ne'

lemma odd_star (n : ℕ) :
    oddB (n+5)*a n =
      a n + oddB (n+4)*oddB (n+3)*oddB (n+2)*oddB (n+1) := by
  have h := rec_eq n
  calc
    oddB (n+5)*a n = a (n+5)*a n+a n := by unfold oddB; ring
    _ = a n+oddB (n+4)*oddB (n+3)*oddB (n+2)*oddB (n+1) := by
      rw [h]
      unfold oddB
      ring

lemma odd_b5 : oddB 5 = 17 := by norm_num [oddB, a]
lemma odd_b6 : oddB 6 = 137 := by norm_num [oddB, a]
lemma odd_b7 : oddB 7 = 9317 := by norm_num [oddB, a]
lemma odd_b8 : oddB 8 = 43398587 := by norm_num [oddB, a]
lemma odd_b9 : oddB 9 = 941718655098992 := by norm_num [oddB, a]

section OddValBasics

variable (p : ℕ)

lemma odd_val_nat_nonneg (m : ℕ) : 0 ≤ padicValRat p (m : ℚ) := by
  rw [padicValRat.of_nat]
  positivity

lemma odd_val_nat_eq_zero {m : ℕ} (h : ¬ p ∣ m) :
    padicValRat p (m : ℚ) = 0 := by
  rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd h]
  rfl

lemma odd_dvd_of_val_pos {m : ℕ}
    (h : 0 < padicValRat p (m : ℚ)) : p ∣ m := by
  by_contra hd
  rw [odd_val_nat_eq_zero p hd] at h
  exact lt_irrefl 0 h

end OddValBasics

def oddAtom (p : ℕ) : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | n+5 => padicValRat p (oddB (n+5))-oddAtom p n

lemma oddAtom_succ (p n : ℕ) :
    oddAtom p (n+5)=padicValRat p (oddB (n+5))-oddAtom p n := rfl

lemma odd_val_b_eq (p n : ℕ) :
    padicValRat p (oddB (n+5))=oddAtom p (n+5)+oddAtom p n := by
  rw [oddAtom_succ]
  ring

lemma oddAtom0 (p : ℕ) : oddAtom p 0=0 := rfl
lemma oddAtom1 (p : ℕ) : oddAtom p 1=0 := rfl
lemma oddAtom2 (p : ℕ) : oddAtom p 2=0 := rfl
lemma oddAtom3 (p : ℕ) : oddAtom p 3=0 := rfl
lemma oddAtom4 (p : ℕ) : oddAtom p 4=0 := rfl

section OddPrimeProof

variable (p : ℕ) [hp : Fact p.Prime]

lemma odd_not_dvd_two_pow (hp2 : p ≠ 2) (k : ℕ) : ¬p ∣ 2^k := fun hd =>
  hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp
    (hp.out.dvd_of_dvd_pow hd))

lemma odd_val_two_pow_zero (hp2 : p ≠ 2) (k : ℕ) :
    padicValRat p ((2^k : ℕ) : ℚ)=0 :=
  odd_val_nat_eq_zero p (odd_not_dvd_two_pow p hp2 k)

lemma odd_val_a (hp2 : p ≠ 2) (n : ℕ) :
    padicValRat p (a (n+5)) =
      oddAtom p (n+4)+oddAtom p (n+3)+
        oddAtom p (n+2)+oddAtom p (n+1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
      have h16 : a 5=((2^4 : ℕ) : ℚ) := by norm_num [a]
      rw [h16, odd_val_two_pow_zero p hp2,
        oddAtom4, oddAtom3, oddAtom2, oddAtom1]
      ring
    | 1 =>
      have h : a 6=((2^3 : ℕ) : ℚ)*oddB 5 := by
        norm_num [oddB, a]
      rw [h, padicValRat.mul (by norm_num) (oddB_ne _),
        odd_val_two_pow_zero p hp2]
      have ht5 : oddAtom p 5=padicValRat p (oddB 5) := by
        rw [oddAtom_succ, oddAtom0]
        ring
      rw [ht5, oddAtom4, oddAtom3, oddAtom2]
      ring
    | 2 =>
      have h : a 7=((2^2 : ℕ) : ℚ)*oddB 5*oddB 6 := by
        norm_num [oddB, a]
      rw [h, padicValRat.mul (mul_ne_zero (by norm_num) (oddB_ne _)) (oddB_ne _),
        padicValRat.mul (by norm_num) (oddB_ne _),
        odd_val_two_pow_zero p hp2]
      have ht5 : oddAtom p 5=padicValRat p (oddB 5) := by
        rw [oddAtom_succ, oddAtom0]
        ring
      have ht6 : oddAtom p 6=padicValRat p (oddB 6) := by
        rw [oddAtom_succ, oddAtom1]
        ring
      rw [ht5, ht6, oddAtom4, oddAtom3]
      ring
    | 3 =>
      have h : a 8=((2^1 : ℕ) : ℚ)*oddB 5*oddB 6*oddB 7 := by
        norm_num [oddB, a]
      rw [h,
        padicValRat.mul
          (mul_ne_zero (mul_ne_zero (by norm_num) (oddB_ne _)) (oddB_ne _))
          (oddB_ne _),
        padicValRat.mul (mul_ne_zero (by norm_num) (oddB_ne _)) (oddB_ne _),
        padicValRat.mul (by norm_num) (oddB_ne _),
        odd_val_two_pow_zero p hp2]
      have ht5 : oddAtom p 5=padicValRat p (oddB 5) := by
        rw [oddAtom_succ, oddAtom0]
        ring
      have ht6 : oddAtom p 6=padicValRat p (oddB 6) := by
        rw [oddAtom_succ, oddAtom1]
        ring
      have ht7 : oddAtom p 7=padicValRat p (oddB 7) := by
        rw [oddAtom_succ, oddAtom2]
        ring
      rw [ht5, ht6, ht7, oddAtom4]
      ring
    | 4 =>
      have h : a 9=oddB 5*oddB 6*oddB 7*oddB 8 := by
        norm_num [oddB, a]
      rw [h,
        padicValRat.mul
          (mul_ne_zero (mul_ne_zero (oddB_ne _) (oddB_ne _)) (oddB_ne _))
          (oddB_ne _),
        padicValRat.mul (mul_ne_zero (oddB_ne _) (oddB_ne _)) (oddB_ne _),
        padicValRat.mul (oddB_ne _) (oddB_ne _)]
      have ht5 : oddAtom p 5=padicValRat p (oddB 5) := by
        rw [oddAtom_succ, oddAtom0]
        ring
      have ht6 : oddAtom p 6=padicValRat p (oddB 6) := by
        rw [oddAtom_succ, oddAtom1]
        ring
      have ht7 : oddAtom p 7=padicValRat p (oddB 7) := by
        rw [oddAtom_succ, oddAtom2]
        ring
      have ht8 : oddAtom p 8=padicValRat p (oddB 8) := by
        rw [oddAtom_succ, oddAtom3]
        ring
      rw [ht5, ht6, ht7, ht8]
      ring
    | m+5 =>
      have hrec := rec_eq (m+5)
      have h1 :
          padicValRat p (a (m+5+5))+padicValRat p (a (m+5)) =
            padicValRat p (oddB (m+5+4))+
              padicValRat p (oddB (m+5+3))+
              padicValRat p (oddB (m+5+2))+
              padicValRat p (oddB (m+5+1)) := by
        rw [← padicValRat.mul (a_ne _) (a_ne _)]
        change a (m+5+5)*a (m+5)=
          oddB (m+5+4)*oddB (m+5+3)*oddB (m+5+2)*oddB (m+5+1) at hrec
        rw [hrec,
          padicValRat.mul
            (mul_ne_zero (mul_ne_zero (oddB_ne _) (oddB_ne _)) (oddB_ne _))
            (oddB_ne _),
          padicValRat.mul (mul_ne_zero (oddB_ne _) (oddB_ne _)) (oddB_ne _),
          padicValRat.mul (oddB_ne _) (oddB_ne _)]
      have hprev := ih m (by omega)
      have hb9 := odd_val_b_eq p (m+4)
      have hb8 := odd_val_b_eq p (m+3)
      have hb7 := odd_val_b_eq p (m+2)
      have hb6 := odd_val_b_eq p (m+1)
      ring_nf at h1 hprev hb9 hb8 hb7 hb6 ⊢
      omega

end OddPrimeProof

section OddPrimeProof

variable (p : ℕ) [hp : Fact p.Prime]

lemma odd_burst_step (hp2 : p ≠ 2) (k : ℕ)
    (h_nonneg : ∀ j, j ≤ k+9 → 0 ≤ oddAtom p j)
    (h : 0 < oddAtom p (k+10)) :
    oddAtom p (k+9)=0 ∧ oddAtom p (k+8)=0 ∧
      oddAtom p (k+7)=0 ∧ oddAtom p (k+6)=0 := by
  have hb := odd_val_b_eq p (k+5)
  rw [show k+5+5=k+10 by omega] at hb
  have hbpos : 0 < padicValRat p (oddB (k+10)) := by
    have ht5 := h_nonneg (k+5) (by omega)
    omega
  have ha := odd_val_a p hp2 (k+5)
  rw [show k+5+5=k+10 by omega,
    show k+5+4=k+9 by omega,
    show k+5+3=k+8 by omega,
    show k+5+2=k+7 by omega,
    show k+5+1=k+6 by omega] at ha
  have h1 : oddB (k+10)+ -a (k+10)=1 := by
    unfold oddB
    ring
  have hmin := padicValRat.min_le_padicValRat_add (p := p)
    (q := oddB (k+10)) (r := -a (k+10)) (by rw [h1]; norm_num)
  rw [h1, padicValRat.one, padicValRat.neg] at hmin
  have hva : padicValRat p (a (k+10)) ≤ 0 := by
    rcases min_le_iff.mp hmin with h' | h' <;> omega
  have h9 := h_nonneg (k+9) (by omega)
  have h8 := h_nonneg (k+8) (by omega)
  have h7 := h_nonneg (k+7) (by omega)
  have h6 := h_nonneg (k+6) (by omega)
  omega

lemma odd_atom_step_nonneg (hp2 : p ≠ 2) (k : ℕ)
    (h_nonneg : ∀ j, j ≤ k+9 → 0 ≤ oddAtom p j)
    (h_burst : 0 < oddAtom p (k+5) →
      oddAtom p (k+4)=0 ∧ oddAtom p (k+3)=0 ∧
        oddAtom p (k+2)=0 ∧ oddAtom p (k+1)=0) :
    0 ≤ oddAtom p (k+10) := by
  have ht5 : 0 ≤ oddAtom p (k+5) := h_nonneg (k+5) (by omega)
  have hb10 := odd_val_b_eq p (k+5)
  rw [show k+5+5=k+10 by omega] at hb10
  have ha10 := odd_val_a p hp2 (k+5)
  rw [show k+5+5=k+10 by omega,
    show k+5+4=k+9 by omega,
    show k+5+3=k+8 by omega,
    show k+5+2=k+7 by omega,
    show k+5+1=k+6 by omega] at ha10
  have hva10 : 0 ≤ padicValRat p (a (k+10)) := by
    have h9 := h_nonneg (k+9) (by omega)
    have h8 := h_nonneg (k+8) (by omega)
    have h7 := h_nonneg (k+7) (by omega)
    have h6 := h_nonneg (k+6) (by omega)
    omega
  rcases eq_or_lt_of_le ht5 with hT0 | hTpos
  · have h1 : (1:ℚ)+a (k+10)=oddB (k+10) := by
      unfold oddB
      ring
    have hmin := padicValRat.min_le_padicValRat_add (p := p)
      (q := (1:ℚ)) (r := a (k+10)) (by rw [h1]; exact oddB_ne _)
    rw [h1, padicValRat.one] at hmin
    have hvb10 : 0 ≤ padicValRat p (oddB (k+10)) :=
      le_trans (by simp [hva10]) hmin
    omega
  · set V := oddAtom p (k+5) with hV
    obtain ⟨hz4,hz3,hz2,hz1⟩ := h_burst hTpos
    have ha5 := odd_val_a p hp2 k
    have hva5 : padicValRat p (a (k+5))=0 := by
      omega
    have ha6 := odd_val_a p hp2 (k+1)
    rw [show k+1+5=k+6 by omega,
      show k+1+4=k+5 by omega,
      show k+1+3=k+4 by omega,
      show k+1+2=k+3 by omega,
      show k+1+1=k+2 by omega] at ha6
    have hva6 : padicValRat p (a (k+6))=V := by
      omega
    have ha7 := odd_val_a p hp2 (k+2)
    rw [show k+2+5=k+7 by omega,
      show k+2+4=k+6 by omega,
      show k+2+3=k+5 by omega,
      show k+2+2=k+4 by omega,
      show k+2+1=k+3 by omega] at ha7
    have hva7 : V ≤ padicValRat p (a (k+7)) := by
      have h6 := h_nonneg (k+6) (by omega)
      omega
    have ha8 := odd_val_a p hp2 (k+3)
    rw [show k+3+5=k+8 by omega,
      show k+3+4=k+7 by omega,
      show k+3+3=k+6 by omega,
      show k+3+2=k+5 by omega,
      show k+3+1=k+4 by omega] at ha8
    have hva8 : V ≤ padicValRat p (a (k+8)) := by
      have h7 := h_nonneg (k+7) (by omega)
      have h6 := h_nonneg (k+6) (by omega)
      omega
    have ha9 := odd_val_a p hp2 (k+4)
    rw [show k+4+5=k+9 by omega,
      show k+4+4=k+8 by omega,
      show k+4+3=k+7 by omega,
      show k+4+2=k+6 by omega,
      show k+4+1=k+5 by omega] at ha9
    have hva9 : V ≤ padicValRat p (a (k+9)) := by
      have h8 := h_nonneg (k+8) (by omega)
      have h7 := h_nonneg (k+7) (by omega)
      have h6 := h_nonneg (k+6) (by omega)
      omega
    have hvb5 : V ≤ padicValRat p (oddB (k+5)) := by
      have hb := odd_val_b_eq p k
      have hk := h_nonneg k (by omega)
      omega
    have hvb6 : 0 ≤ padicValRat p (oddB (k+6)) := by
      have hb := odd_val_b_eq p (k+1)
      rw [show k+1+5=k+6 by omega] at hb
      have h6 := h_nonneg (k+6) (by omega)
      have h1 := h_nonneg (k+1) (by omega)
      omega
    have hvb7 : 0 ≤ padicValRat p (oddB (k+7)) := by
      have hb := odd_val_b_eq p (k+2)
      rw [show k+2+5=k+7 by omega] at hb
      have h7 := h_nonneg (k+7) (by omega)
      have h2 := h_nonneg (k+2) (by omega)
      omega
    have hvb8 : 0 ≤ padicValRat p (oddB (k+8)) := by
      have hb := odd_val_b_eq p (k+3)
      rw [show k+3+5=k+8 by omega] at hb
      have h8 := h_nonneg (k+8) (by omega)
      have h3 := h_nonneg (k+3) (by omega)
      omega
    have hs7 : V ≤ padicValRat p (a (k+7)*oddB (k+6)) := by
      rw [padicValRat.mul (a_ne _) (oddB_ne _)]
      omega
    have hs8 : V ≤ padicValRat p
        (a (k+8)*(oddB (k+6)*oddB (k+7))) := by
      rw [padicValRat.mul (a_ne _) (mul_ne_zero (oddB_ne _) (oddB_ne _)),
        padicValRat.mul (oddB_ne _) (oddB_ne _)]
      omega
    have hs9 : V ≤ padicValRat p
        (a (k+9)*(oddB (k+6)*oddB (k+7)*oddB (k+8))) := by
      rw [padicValRat.mul (a_ne _)
          (mul_ne_zero (mul_ne_zero (oddB_ne _) (oddB_ne _)) (oddB_ne _)),
        padicValRat.mul (mul_ne_zero (oddB_ne _) (oddB_ne _)) (oddB_ne _),
        padicValRat.mul (oddB_ne _) (oddB_ne _)]
      omega
    have hs7pos : 0 < a (k+7)*oddB (k+6) :=
      mul_pos (a_pos _) (oddB_pos _)
    have hs8pos : 0 < a (k+8)*(oddB (k+6)*oddB (k+7)) :=
      mul_pos (a_pos _) (mul_pos (oddB_pos _) (oddB_pos _))
    have hs9pos :
        0 < a (k+9)*(oddB (k+6)*oddB (k+7)*oddB (k+8)) :=
      mul_pos (a_pos _)
        (mul_pos (mul_pos (oddB_pos _) (oddB_pos _)) (oddB_pos _))
    have hsum1pos : 0 < oddB (k+5)+a (k+6) :=
      add_pos (oddB_pos _) (a_pos _)
    have hsum2pos :
        0 < oddB (k+5)+a (k+6)+a (k+7)*oddB (k+6) :=
      add_pos hsum1pos hs7pos
    have hsum3pos :
        0 < oddB (k+5)+a (k+6)+a (k+7)*oddB (k+6)+
          a (k+8)*(oddB (k+6)*oddB (k+7)) :=
      add_pos hsum2pos hs8pos
    have hsum4pos :
        0 < oddB (k+5)+a (k+6)+a (k+7)*oddB (k+6)+
          a (k+8)*(oddB (k+6)*oddB (k+7))+
          a (k+9)*(oddB (k+6)*oddB (k+7)*oddB (k+8)) :=
      add_pos hsum3pos hs9pos
    have hsum1 : V ≤ padicValRat p (oddB (k+5)+a (k+6)) :=
      le_trans (le_min hvb5 (by omega))
        (padicValRat.min_le_padicValRat_add (p := p) hsum1pos.ne')
    have hsum2 : V ≤ padicValRat p
        (oddB (k+5)+a (k+6)+a (k+7)*oddB (k+6)) :=
      le_trans (le_min hsum1 hs7)
        (padicValRat.min_le_padicValRat_add (p := p) hsum2pos.ne')
    have hsum3 : V ≤ padicValRat p
        (oddB (k+5)+a (k+6)+a (k+7)*oddB (k+6)+
          a (k+8)*(oddB (k+6)*oddB (k+7))) :=
      le_trans (le_min hsum2 hs8)
        (padicValRat.min_le_padicValRat_add (p := p) hsum3pos.ne')
    have hsum4 : V ≤ padicValRat p
        (oddB (k+5)+a (k+6)+a (k+7)*oddB (k+6)+
          a (k+8)*(oddB (k+6)*oddB (k+7))+
          a (k+9)*(oddB (k+6)*oddB (k+7)*oddB (k+8))) :=
      le_trans (le_min hsum3 hs9)
        (padicValRat.min_le_padicValRat_add (p := p) hsum4pos.ne')
    have hkey : oddB (k+10)*a (k+5) =
        oddB (k+5)+a (k+6)+a (k+7)*oddB (k+6)+
          a (k+8)*(oddB (k+6)*oddB (k+7))+
          a (k+9)*(oddB (k+6)*oddB (k+7)*oddB (k+8)) := by
      have hs := odd_star (k+5)
      rw [show k+5+5=k+10 by omega,
        show k+5+4=k+9 by omega,
        show k+5+3=k+8 by omega,
        show k+5+2=k+7 by omega,
        show k+5+1=k+6 by omega] at hs
      calc
        oddB (k+10)*a (k+5) =
            a (k+5)+oddB (k+9)*oddB (k+8)*oddB (k+7)*oddB (k+6) := hs
        _ = _ := by
          unfold oddB
          ring
    have hvkey : V ≤ padicValRat p (oddB (k+10)*a (k+5)) := by
      rw [hkey]
      exact hsum4
    have hmul : padicValRat p (oddB (k+10)*a (k+5)) =
        padicValRat p (oddB (k+10))+padicValRat p (a (k+5)) :=
      padicValRat.mul (oddB_ne _) (a_ne _)
    have hvb10 : V ≤ padicValRat p (oddB (k+10)) := by
      omega
    omega

end OddPrimeProof

lemma oddAtom5_eq (p : ℕ) :
    oddAtom p 5=padicValRat p ((17:ℕ):ℚ) := by
  rw [oddAtom_succ, odd_b5, oddAtom0]
  ring_nf

lemma oddAtom6_eq (p : ℕ) :
    oddAtom p 6=padicValRat p ((137:ℕ):ℚ) := by
  rw [oddAtom_succ, odd_b6, oddAtom1]
  ring_nf

lemma oddAtom7_eq (p : ℕ) :
    oddAtom p 7=padicValRat p ((9317:ℕ):ℚ) := by
  rw [oddAtom_succ, odd_b7, oddAtom2]
  ring_nf

lemma oddAtom8_eq (p : ℕ) :
    oddAtom p 8=padicValRat p ((43398587:ℕ):ℚ) := by
  rw [oddAtom_succ, odd_b8, oddAtom3]
  ring_nf

lemma oddAtom9_eq (p : ℕ) :
    oddAtom p 9=padicValRat p ((941718655098992:ℕ):ℚ) := by
  rw [oddAtom_succ, odd_b9, oddAtom4]
  ring_nf

section OddPrimeProof

variable (p : ℕ) [hp : Fact p.Prime]

lemma odd_not_dvd_of_coprime {m n : ℕ}
    (hd : p ∣ m) (hc : Nat.Coprime m n) : ¬p ∣ n := by
  intro hn
  apply hp.out.not_dvd_one
  rw [← hc.gcd_eq_one]
  exact Nat.dvd_gcd hd hn

lemma odd_val_zero_of_coprime {m n : ℕ}
    (hd : p ∣ m) (hc : Nat.Coprime m n) :
    padicValRat p (n:ℚ)=0 :=
  odd_val_nat_eq_zero p (odd_not_dvd_of_coprime p hd hc)

lemma odd_main_induction (hp2 : p ≠ 2) : ∀ n,
    (0 ≤ oddAtom p n) ∧
      (∀ k, n=k+5 → 0 < oddAtom p n →
        oddAtom p (k+4)=0 ∧ oddAtom p (k+3)=0 ∧
          oddAtom p (k+2)=0 ∧ oddAtom p (k+1)=0) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
      exact ⟨by rw [oddAtom0], fun k hk => absurd hk (by omega)⟩
    | 1 =>
      exact ⟨by rw [oddAtom1], fun k hk => absurd hk (by omega)⟩
    | 2 =>
      exact ⟨by rw [oddAtom2], fun k hk => absurd hk (by omega)⟩
    | 3 =>
      exact ⟨by rw [oddAtom3], fun k hk => absurd hk (by omega)⟩
    | 4 =>
      exact ⟨by rw [oddAtom4], fun k hk => absurd hk (by omega)⟩
    | 5 =>
      refine ⟨by rw [oddAtom5_eq]; exact odd_val_nat_nonneg p 17,
        fun k hk _ => ?_⟩
      obtain rfl : k=0 := by omega
      exact ⟨oddAtom4 p,oddAtom3 p,oddAtom2 p,oddAtom1 p⟩
    | 6 =>
      refine ⟨by rw [oddAtom6_eq]; exact odd_val_nat_nonneg p 137,
        fun k hk h6 => ?_⟩
      obtain rfl : k=1 := by omega
      rw [oddAtom6_eq] at h6
      have hd : p ∣ 137 := odd_dvd_of_val_pos p h6
      have hz5 : oddAtom p 5=0 := by
        rw [oddAtom5_eq]
        exact odd_val_zero_of_coprime p hd (by norm_num)
      exact ⟨hz5,oddAtom4 p,oddAtom3 p,oddAtom2 p⟩
    | 7 =>
      refine ⟨by rw [oddAtom7_eq]; exact odd_val_nat_nonneg p 9317,
        fun k hk h7 => ?_⟩
      obtain rfl : k=2 := by omega
      rw [oddAtom7_eq] at h7
      have hd : p ∣ 9317 := odd_dvd_of_val_pos p h7
      have hz6 : oddAtom p 6=0 := by
        rw [oddAtom6_eq]
        exact odd_val_zero_of_coprime p hd (by norm_num)
      have hz5 : oddAtom p 5=0 := by
        rw [oddAtom5_eq]
        exact odd_val_zero_of_coprime p hd (by norm_num)
      exact ⟨hz6,hz5,oddAtom4 p,oddAtom3 p⟩
    | 8 =>
      refine ⟨by rw [oddAtom8_eq]; exact odd_val_nat_nonneg p 43398587,
        fun k hk h8 => ?_⟩
      obtain rfl : k=3 := by omega
      rw [oddAtom8_eq] at h8
      have hd : p ∣ 43398587 := odd_dvd_of_val_pos p h8
      have hz7 : oddAtom p 7=0 := by
        rw [oddAtom7_eq]
        exact odd_val_zero_of_coprime p hd (by norm_num)
      have hz6 : oddAtom p 6=0 := by
        rw [oddAtom6_eq]
        exact odd_val_zero_of_coprime p hd (by norm_num)
      have hz5 : oddAtom p 5=0 := by
        rw [oddAtom5_eq]
        exact odd_val_zero_of_coprime p hd (by norm_num)
      exact ⟨hz7,hz6,hz5,oddAtom4 p⟩
    | 9 =>
      refine ⟨?_, fun k hk h9 => ?_⟩
      · rw [oddAtom9_eq]
        exact odd_val_nat_nonneg p 941718655098992
      obtain rfl : k=4 := by omega
      rw [oddAtom9_eq] at h9
      have hd : p ∣ 941718655098992 := odd_dvd_of_val_pos p h9
      have hz8 : oddAtom p 8=0 := by
        rw [oddAtom8_eq]
        exact odd_val_zero_of_coprime p hd (by norm_num)
      have hz7 : oddAtom p 7=0 := by
        rw [oddAtom7_eq]
        exact odd_val_zero_of_coprime p hd (by norm_num)
      have hz6 : oddAtom p 6=0 := by
        rw [oddAtom6_eq]
        exact odd_val_zero_of_coprime p hd (by norm_num)
      have hz5 : oddAtom p 5=0 := by
        rw [oddAtom5_eq]
        exact odd_val_zero_of_coprime p hd (by norm_num)
      exact ⟨hz8,hz7,hz6,hz5⟩
    | k+10 =>
      have h_nonneg : ∀ j, j ≤ k+9 → 0 ≤ oddAtom p j := fun j hj =>
        (ih j (by omega)).1
      have h_burst : 0 < oddAtom p (k+5) →
          oddAtom p (k+4)=0 ∧ oddAtom p (k+3)=0 ∧
            oddAtom p (k+2)=0 ∧ oddAtom p (k+1)=0 :=
        (ih (k+5) (by omega)).2 k rfl
      refine ⟨odd_atom_step_nonneg p hp2 k h_nonneg h_burst,
        fun k' hk' h => ?_⟩
      obtain rfl : k'=k+5 := by omega
      have hres := odd_burst_step p hp2 k h_nonneg h
      rw [show k+5+4=k+9 by omega,
        show k+5+3=k+8 by omega,
        show k+5+2=k+7 by omega,
        show k+5+1=k+6 by omega]
      exact hres

theorem odd_prime_val_nonneg_proved (hp2 : p ≠ 2) (n : ℕ) :
    0 ≤ padicValRat p (a n) := by
  match n with
  | 0 => rw [show a 0=1 from rfl, padicValRat.one]
  | 1 => rw [show a 1=1 from rfl, padicValRat.one]
  | 2 => rw [show a 2=1 from rfl, padicValRat.one]
  | 3 => rw [show a 3=1 from rfl, padicValRat.one]
  | 4 => rw [show a 4=1 from rfl, padicValRat.one]
  | m+5 =>
    rw [odd_val_a p hp2 m]
    have h4 := (odd_main_induction p hp2 (m+4)).1
    have h3 := (odd_main_induction p hp2 (m+3)).1
    have h2 := (odd_main_induction p hp2 (m+2)).1
    have h1 := (odd_main_induction p hp2 (m+1)).1
    omega

end OddPrimeProof

theorem odd_prime_val_nonneg (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (n : ℕ) :
    0 ≤ padicValRat p (a n) :=
  odd_prime_val_nonneg_proved p hp2 n

lemma exists_int_of_all_val_nonneg (r : ℚ)
    (h : ∀ p : ℕ, p.Prime → 0 ≤ padicValRat p r) : ∃ z : ℤ, r = z := by
  refine ⟨r.num, ?_⟩
  have hden : r.den = 1 := by
    by_contra hd
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hd
    haveI : Fact q.Prime := ⟨hq⟩
    have hnum : padicValInt q r.num = 0 := by
      apply padicValInt.eq_zero_of_not_dvd
      intro hdvd
      have h1 : q ∣ r.num.natAbs := Int.ofNat_dvd_left.mp hdvd
      have h2 : q ∣ Nat.gcd r.num.natAbs r.den := Nat.dvd_gcd h1 hqd
      rw [r.reduced] at h2
      exact hq.one_lt.ne' (Nat.dvd_one.mp h2)
    have hden1 : 1 ≤ padicValNat q r.den :=
      one_le_padicValNat_of_dvd r.den_pos.ne' hqd
    have hval : padicValRat q r < 0 := by
      have hdef : padicValRat q r =
          padicValInt q r.num - padicValNat q r.den := rfl
      rw [hdef]
      omega
    exact absurd (h q hq) (not_le.mpr hval)
  exact ((Rat.den_eq_one_iff r).mp hden).symm

theorem integrality (n : ℕ) : ∃ z : ℤ, a n = z := by
  apply exists_int_of_all_val_nonneg
  intro p hp
  haveI : Fact p.Prime := ⟨hp⟩
  rcases eq_or_ne p 2 with rfl | hp2
  · exact two_adic_val_nonneg n
  · exact odd_prime_val_nonneg p hp2 n

end MO323963

