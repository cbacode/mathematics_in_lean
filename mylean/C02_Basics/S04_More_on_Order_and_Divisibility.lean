import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    · apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example : max a b = max b a := by
  apply le_antisymm
  · show max a b ≤ max b a
    apply max_le
    apply le_max_right
    apply le_max_left
  · show max b a ≤ max a b
    apply max_le
    apply le_max_right
    apply le_max_left

-- solution
example : max a b = max b a := by
  apply le_antisymm
  repeat
    apply max_le
    apply le_max_right
    apply le_max_left

example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  · show min (min a b) c ≤ min a (min b c)
    apply le_min
    · show min (min a b) c ≤ a
      calc
        min (min a b) c ≤ min a b := by apply min_le_left
        _ ≤ a := by apply min_le_left
    · show min (min a b) c ≤ min b c
      apply le_min
      · show min (min a b) c ≤ b
        calc
          min (min a b) c ≤ min a b := by apply min_le_left
          _ ≤ b := by apply min_le_right
      · show min (min a b) c ≤ c
        apply min_le_right
  · show min a (min b c) ≤ min (min a b) c
    apply le_min
    · show min a (min b c) ≤ min a b
      apply le_min
      · show min a (min b c) ≤ a
        apply min_le_left
      · show min a (min b c) ≤ b
        calc
          min a (min b c) ≤ min b c := by apply min_le_right
          _ ≤ b := by apply min_le_left
    · show min a (min b c) ≤ c
      calc
        min a (min b c) ≤ min b c := by apply min_le_right
        _ ≤ c := by apply min_le_right

-- solution
example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  · apply le_min
    · apply le_trans
      apply min_le_left
      apply min_le_left
    apply le_min
    · apply le_trans
      apply min_le_left
      apply min_le_right
    apply min_le_right
  apply le_min
  · apply le_min
    · apply min_le_left
    apply le_trans
    apply min_le_right
    apply min_le_left
  apply le_trans
  apply min_le_right
  apply min_le_right

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  · show min a b + c ≤ a + c
    apply add_le_add_right
    apply min_le_left
  · show min a b + c ≤ b + c
    apply add_le_add_right
    apply min_le_right

-- solution
theorem aux_ans : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  · apply add_le_add_right
    apply min_le_left
  apply add_le_add_right
  apply min_le_right

example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  · show min a b + c ≤ min (a + c) (b + c)
    apply aux
  · show min (a + c) (b + c) ≤ min a b + c
    have h₀ : min (a + c) (b + c) + -c ≤ a := by
      have h₁ : min (a + c) (b + c) ≤ (a + c) := by
        apply min_le_left
      rw[← add_zero (min (a + c) (b + c))] at h₁
      rw[← neg_add_cancel c, ← add_assoc] at h₁
      apply le_of_add_le_add_right at h₁
      exact h₁

    have h₂ : min (a + c) (b + c) + -c ≤ b := by
      have h₃ : min (a + c) (b + c) ≤ (b + c) := by
        apply min_le_right
      rw[← add_zero (min (a + c) (b + c))] at h₃
      rw[← neg_add_cancel c, ← add_assoc] at h₃
      apply le_of_add_le_add_right at h₃
      exact h₃
    have h₄ : min (a + c) (b + c) + -c ≤ min a b := by
      apply le_min
      · exact h₀
      · exact h₂
    rw[← add_zero (min a b), ← add_neg_cancel c, ← add_assoc] at h₄
    apply le_of_add_le_add_right at h₄
    exact h₄

example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  · show min a b + c ≤ min (a + c) (b + c)
    apply aux
  · show min (a + c) (b + c) ≤ min a b + c
    rw[← add_neg_cancel_right (min (a + c) (b + c)) (-c)]
    rw[neg_neg]
    apply add_le_add_right
    apply le_min
    · show min (a + c) (b + c) + -c ≤ a
      apply add_neg_le_iff_le_add.mpr
      apply min_le_left
    · show min (a + c) (b + c) + -c ≤ b
      apply add_neg_le_iff_le_add.mpr
      apply min_le_right

-- solution
example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  · apply aux
  have h : min (a + c) (b + c) = min (a + c) (b + c) - c + c := by rw [sub_add_cancel]
  rw [h]
  apply add_le_add_right
  rw [sub_eq_add_neg]
  apply le_trans
  apply aux
  rw [add_neg_cancel_right, add_neg_cancel_right]

#check add_zero a
#check neg_add_cancel
#check add_assoc
#check le_of_add_le_add_right
#check add_neg_cancel_right

#check le_min
#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| := by
  have h₀ : |a| ≤ |a - b| + |b| := by
    nth_rw 1 [← sub_add_cancel a b]
    apply abs_add
  apply sub_le_iff_le_add.mpr
  exact h₀

-- solution
example : |a| - |b| ≤ |a - b| :=
  calc
    |a| - |b| = |a - b + b| - |b| := by rw [sub_add_cancel]
    _ ≤ |a - b| + |b| - |b| := by
      apply sub_le_sub_right
      apply abs_add
    _ ≤ |a - b| := by rw [add_sub_cancel_right]

-- alternatively
example : |a| - |b| ≤ |a - b| := by
  have h := abs_add (a - b) b
  rw [sub_add_cancel] at h
  linarith

example : |a| - |b| ≤ |a - b| := by
  apply sub_le_iff_le_add.mpr
  nth_rw 1 [← sub_add_cancel a b]
  apply abs_add
end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

-- solution
example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

-- solution
example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

-- solution
example : x ∣ x ^ 2 := by
  apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  have h₀ : x ∣ x ^ 2 := by
    apply dvd_mul_left
  have h₁ : x ∣ y * (x * z) := by
    rw[← mul_assoc]
    apply dvd_mul_of_dvd_left
    apply dvd_mul_left
  have h₂ : x ∣ w ^ 2 := by
    have h₃ : w ^ 2 = w * w := by apply pow_two
    rw[h₃]
    apply dvd_mul_of_dvd_left
    exact h
  rw[add_assoc]
  apply dvd_add h₁
  apply dvd_add h₀
  exact h₂

-- solution
example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  apply dvd_add
  · apply dvd_add
    · apply dvd_mul_of_dvd_right
      apply dvd_mul_right
    apply dvd_mul_left
  rw [pow_two]
  apply dvd_mul_of_dvd_right
  exact h

end
#check dvd_mul_left

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  apply Nat.dvd_antisymm
  repeat
    apply Nat.dvd_gcd
    apply Nat.gcd_dvd_right
    apply Nat.gcd_dvd_left

-- solution
example : Nat.gcd m n = Nat.gcd n m := by
  apply Nat.dvd_antisymm
  repeat
    apply Nat.dvd_gcd
    apply Nat.gcd_dvd_right
    apply Nat.gcd_dvd_left

end
