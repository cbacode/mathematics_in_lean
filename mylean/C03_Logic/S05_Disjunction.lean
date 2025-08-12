import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h

#check le_or_gt

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h]
    calc
      x ≤ 0 := by linarith [h]
      _ ≤ -x := by linarith [h]

-- solution
theorem le_abs_self_ans (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h]
    linarith

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
    calc
      -x ≤ 0 := by linarith [h]
      _ ≤ x := by linarith [h]
  · rw [abs_of_neg h]

-- solution
theorem neg_le_abs_self_ans (x : ℝ) : -x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
    linarith
  · rw [abs_of_neg h]

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x + y) with h | h
  · rw[abs_of_nonneg h]
    apply add_le_add
    · exact le_abs_self x
    · exact le_abs_self y
  · rw[abs_of_neg h]
    rw[neg_add x y]
    apply add_le_add
    · exact neg_le_abs_self x
    · exact neg_le_abs_self y

-- solution
theorem abs_add_ans (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x + y) with h | h
  · rw [abs_of_nonneg h]
    linarith [le_abs_self x, le_abs_self y]
  · rw [abs_of_neg h]
    linarith [neg_le_abs_self x, neg_le_abs_self y]

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  · rcases le_or_gt 0 y with h | h
    · rw[abs_of_nonneg h]
      intro h₁; left; exact h₁
    · rw[abs_of_neg h]
      intro h₁; right; exact h₁
  · intro h
    rcases h with h | h
    · exact lt_of_lt_of_le h (le_abs_self y)
    · exact lt_of_lt_of_le h (neg_le_abs_self y)

-- solution
theorem lt_abs_ans : x < |y| ↔ x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    constructor
    · intro h'
      left
      exact h'
    · intro h'
      rcases h' with h' | h'
      · exact h'
      · linarith
  rw [abs_of_neg h]
  constructor
  · intro h'
    right
    exact h'
  · intro h'
    rcases h' with h' | h'
    · linarith
    · exact h'

#check lt_of_lt_of_le

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  constructor
  · rcases le_or_gt 0 x with h | h
    · rw[abs_of_nonneg h]
      intro h₁
      constructor
      · have h₂ : 0 < y := by linarith [h, h₁]
        linarith [h₂, h₁]
      · exact h₁
    · rw[abs_of_neg h]
      intro h₁
      constructor
      · linarith [h₁]
      · have h₂ : 0 < y := by linarith [h, h₁]
        linarith [h₂, h]
  · intro h
    rcases h with ⟨h₁, h₂⟩
    rcases le_or_gt 0 x with h | h
    · rw[abs_of_nonneg h]; exact h₂
    · rw[abs_of_neg h]; linarith [h₁]

-- solution
theorem abs_lt_ans : |x| < y ↔ -y < x ∧ x < y := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
    constructor
    · intro h'
      constructor
      · linarith
      exact h'
    · intro h'
      rcases h' with ⟨h1, h2⟩
      exact h2
  · rw [abs_of_neg h]
    constructor
    · intro h'
      constructor
      · linarith
      · linarith
    · intro h'
      linarith

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt

#check lt_trichotomy

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  sorry

-- solution
example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x, y, rfl | rfl⟩ <;> linarith [sq_nonneg x, sq_nonneg y]

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h₁ : x ^ 2 - 1 = 0 := by rw[h, sub_self]
  have h₂ : (x + 1) * (x - 1) = x ^ 2 - 1 := by ring
  have h₃ : (x + 1) * (x - 1) = 0 := by
    rw[h₁] at h₂
    exact h₂
  apply eq_zero_or_eq_zero_of_mul_eq_zero at h₃
  rcases h₃ with h₃ | h₃
  · right; exact eq_neg_iff_add_eq_zero.mpr h₃
  · left; exact eq_of_sub_eq_zero h₃

-- solution
example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h' : x ^ 2 - 1 = 0 := by rw [h, sub_self]
  have h'' : (x + 1) * (x - 1) = 0 := by
    rw [← h']
    ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h'' with h1 | h1
  · right
    exact eq_neg_iff_add_eq_zero.mpr h1
  · left
    exact eq_of_sub_eq_zero h1

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h₁ : x ^ 2 - y ^ 2 = 0 := by
    rw[h, sub_self]
  have h₂ : (x - y) * (x + y) = 0 := by
    rw[← h₁]; ring
  apply eq_zero_or_eq_zero_of_mul_eq_zero at h₂
  rcases h₂ with h₂ | h₂
  · left; exact eq_of_sub_eq_zero h₂
  · right; exact eq_neg_iff_add_eq_zero.mpr h₂

-- solution
example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h' : x ^ 2 - y ^ 2 = 0 := by rw [h, sub_self]
  have h'' : (x + y) * (x - y) = 0 := by
    rw [← h']
    ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h'' with h1 | h1
  · right
    exact eq_neg_iff_add_eq_zero.mpr h1
  · left
    exact eq_of_sub_eq_zero h1

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h₁ : x ^ 2 - 1 = 0 := by rw[h, sub_self]
  have h₂ : (x + 1) * (x - 1) = x ^ 2 - 1 := by ring
  have h₃ : (x + 1) * (x - 1) = 0 := by
    rw[h₁] at h₂
    exact h₂
  apply eq_zero_or_eq_zero_of_mul_eq_zero at h₃
  rcases h₃ with h₃ | h₃
  · right; exact eq_neg_iff_add_eq_zero.mpr h₃
  · left; exact eq_of_sub_eq_zero h₃

-- solution
example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h' : x ^ 2 - 1 = 0 := by rw [h, sub_self]
  have h'' : (x + 1) * (x - 1) = 0 := by
    rw [← h']
    ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h'' with h1 | h1
  · right
    exact eq_neg_iff_add_eq_zero.mpr h1
  · left
    exact eq_of_sub_eq_zero h1

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h₁ : x ^ 2 - y ^ 2 = 0 := by
    rw[h, sub_self]
  have h₂ : (x - y) * (x + y) = 0 := by
    rw[← h₁]; ring
  apply eq_zero_or_eq_zero_of_mul_eq_zero at h₂
  rcases h₂ with h₂ | h₂
  · left; exact eq_of_sub_eq_zero h₂
  · right; exact eq_neg_iff_add_eq_zero.mpr h₂

-- solution
example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h' : x ^ 2 - y ^ 2 = 0 := by rw [h, sub_self]
  have h'' : (x + y) * (x - y) = 0 := by
    rw [← h']
    ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h'' with h1 | h1
  · right
    exact eq_neg_iff_add_eq_zero.mpr h1
  · left
    exact eq_of_sub_eq_zero h1

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  · by_cases h : P
    · intro h'; right; apply h' h
    · intro h'; left; exact h
  · intro h
    rcases h with h | h
    · intro h'; exfalso; apply h h'
    · intro h'; exact h

-- solution
example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  · intro h
    by_cases h' : P
    · right
      exact h h'
    · left
      exact h'
  rintro (h | h)
  · intro h'
    exact absurd h' h
  · intro
    exact h
