import Mathlib.Tactic
import Mathlib.Util.Delaborators

set_option warningAsError false

-- 2.1
section
variable (a b c : ℝ)

#check mul_comm a b
#check mul_assoc a b c

#check sub_self a
-- "←" can be used to reverse the equation

#check mul_add a b c
#check add_mul a b c
#check two_mul a

#check pow_two a
#check mul_sub a b c
#check add_sub a b c
#check sub_sub a b c
#check add_zero a

-- "at" can be used to rw assumptions
-- e.g. rw [hyp'] at hyp

-- "exact" can be used when assumptions is the same as goal

-- "ring" can be used to calculate equations in communicative ring

-- "nth_rw" can be used to replace particular part of expression

end

-- 2.2

section
variable (R : Type*) [Ring R]

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (neg_add_cancel : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)

#check (neg_add_cancel_left : ∀ a b : R, -a + (a + b) = b)
#check (add_neg_cancel_right : ∀ a b : R , a + b + -b = a)
#check (add_left_cancel : ∀ {a b c : R},a + b = a + c → b = c)
#check (add_right_cancel : ∀ {a b c : R},a + b = c + b -> a = c)
-- → is the same as ->

-- you can use "have" to introduce new expression that is always true

-- you can use "apply" to use theorems and create new goal

-- you can use "rfl" to show left side and right side of an equation is the same
end

section
variable {G : Type*} [Group G]
variable (a : G)
#check a⁻¹ -- inv

end

-- 2.3
variable (a b c d e : ℝ)
-- open Real
-- "₀" _0
-- "≤" le
-- is the same as <=
-- end

-- Do not add "apply" when use things like norm_num
