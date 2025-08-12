import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬ (x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  · show x ⊓ y ≤ y ⊓ x
    apply le_inf
    · show x ⊓ y ≤ y
      exact inf_le_right
    · show x ⊓ y ≤ x
      exact inf_le_left
  · show y ⊓ x ≤ x ⊓ y
    apply le_inf
    exact inf_le_right
    exact inf_le_left

-- solution
example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  repeat
    apply le_inf
    · apply inf_le_right
    apply inf_le_left

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  · show x ⊓ y ⊓ z ≤ x ⊓ (y ⊓ z)
    apply le_inf
    · show x ⊓ y ⊓ z ≤ x
      have h1 : x ⊓ y ⊓ z ≤ x ⊓ y := by
        exact inf_le_left
      have h2 : x ⊓ y ≤ x := by
        exact inf_le_left
      apply le_trans h1 h2
    · show x ⊓ y ⊓ z ≤ y ⊓ z
      apply le_inf
      · show x ⊓ y ⊓ z ≤ y
        calc
        x ⊓ y ⊓ z ≤ x ⊓ y := by
          exact inf_le_left
        _ ≤ y := by
          exact inf_le_right
      · show x ⊓ y ⊓ z ≤ z
        exact inf_le_right
  · show x ⊓ (y ⊓ z) ≤ x ⊓ y ⊓ z
    apply le_inf
    · show x ⊓ (y ⊓ z) ≤ x ⊓ y
      apply le_inf
      · show x ⊓ (y ⊓ z) ≤ x
        exact inf_le_left
      · show x ⊓ (y ⊓ z) ≤ y
        calc
        x ⊓ (y ⊓ z) ≤ y ⊓ z := by
          exact inf_le_right
        _ ≤ y := by
          exact inf_le_left
    · show x ⊓ (y ⊓ z) ≤ z
      trans y ⊓ z
      · show x ⊓ (y ⊓ z) ≤ y ⊓ z
        exact inf_le_right
      · show y ⊓ z ≤ z
        exact inf_le_right

-- solution
example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  · apply le_inf
    · trans x ⊓ y
      apply inf_le_left
      apply inf_le_left
    apply le_inf
    · trans x ⊓ y
      apply inf_le_left
      apply inf_le_right
    apply inf_le_right
  apply le_inf
  · apply le_inf
    · apply inf_le_left
    trans y ⊓ z
    apply inf_le_right
    apply inf_le_left
  trans y ⊓ z
  apply inf_le_right
  apply inf_le_right

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  · show x ⊔ y ≤ y ⊔ x
    apply sup_le
    · show x ≤ y ⊔ x
      exact le_sup_right
    · show y ≤ y ⊔ x
      exact le_sup_left
  · show y ⊔ x ≤ x ⊔ y
    apply sup_le
    · show y ≤ x ⊔ y
      exact le_sup_right
    · show x ≤ x ⊔ y
      exact le_sup_left

-- solution
example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  repeat
    apply sup_le
    · apply le_sup_right
    apply le_sup_left

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  · show x ⊔ y ⊔ z ≤ x ⊔ (y ⊔ z)
    apply sup_le
    · show x ⊔ y ≤ x ⊔ (y ⊔ z)
      apply sup_le
      · show x ≤ x ⊔ (y ⊔ z)
        exact le_sup_left
      · show y ≤ x ⊔ (y ⊔ z)
        calc
        y ≤ y ⊔ z := by
          exact le_sup_left
        _ ≤ x ⊔ (y ⊔ z) := by
          exact le_sup_right
    · show z ≤ x ⊔ (y ⊔ z)
      calc
        z ≤ y ⊔ z := by
          exact le_sup_right
        _ ≤ x ⊔ (y ⊔ z) := by
          exact le_sup_right
  · show x ⊔ (y ⊔ z) ≤ x ⊔ y ⊔ z
    apply sup_le
    · show x ≤ x ⊔ y ⊔ z
      calc
        x ≤ x ⊔ y := by
          exact le_sup_left
        _ ≤ x ⊔ y ⊔ z := by
          exact le_sup_left
    · show y ⊔ z ≤ x ⊔ y ⊔ z
      apply sup_le
      · show y ≤ x ⊔ y ⊔ z
        calc
        y ≤ x ⊔ y := by
          exact le_sup_right
        _ ≤ x ⊔ y ⊔ z := by
          exact le_sup_left
      · show z ≤ x ⊔ y ⊔ z
        exact le_sup_right

-- solution
example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  · apply sup_le
    · apply sup_le
      apply le_sup_left
      · trans y ⊔ z
        apply le_sup_left
        apply le_sup_right
    trans y ⊔ z
    apply le_sup_right
    apply le_sup_right
  apply sup_le
  · trans x ⊔ y
    apply le_sup_left
    apply le_sup_left
  apply sup_le
  · trans x ⊔ y
    apply le_sup_right
    apply le_sup_left
  apply le_sup_right

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  · show x ⊓ (x ⊔ y) ≤ x
    exact inf_le_left
  · show x ≤ x ⊓ (x ⊔ y)
    apply le_inf
    · exact le_refl x
    · exact le_sup_left

-- solution
theorem absorb1_ans : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  · apply inf_le_left
  apply le_inf
  · apply le_refl
  apply le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  · show x ⊔ x ⊓ y ≤ x
    apply sup_le
    · exact le_refl x
    · exact inf_le_left
  · show x ≤ x ⊔ x ⊓ y
    exact le_sup_left

-- solution
theorem absorb2_ans : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  · apply sup_le
    · apply le_refl
    apply inf_le_left
  apply le_sup_left
end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  apply le_antisymm
  · show a ⊔ b ⊓ c ≤ (a ⊔ b) ⊓ (a ⊔ c)
    apply le_inf
    · show a ⊔ b ⊓ c ≤ a ⊔ b
      apply sup_le
      · show a ≤ a ⊔ b
        exact le_sup_left
      · show b ⊓ c ≤ a ⊔ b
        calc
        b ⊓ c ≤ b := by
          exact inf_le_left
        _ ≤ a ⊔ b := by
          exact le_sup_right
    · show a ⊔ b ⊓ c ≤ a ⊔ c
      apply sup_le
      · show a ≤ a ⊔ c
        exact le_sup_left
      · show b ⊓ c ≤ a ⊔ c
        calc
        b ⊓ c ≤ c := by
          exact inf_le_right
        _ ≤ a ⊔ c := by
          exact le_sup_right
  · show (a ⊔ b) ⊓ (a ⊔ c) ≤ a ⊔ b ⊓ c
    have h₁ : b ⊓ (a ⊔ c) = (b ⊓ a) ⊔ (b ⊓ c) := by apply h b a c
    calc
    -- min(b, max(a,c))
    (a ⊔ b) ⊓ (a ⊔ c) ≤ b ⊓ (a ⊔ c) := by
      apply le_inf
      · show (a ⊔ b) ⊓ (a ⊔ c) ≤ b
        sorry
      · show (a ⊔ b) ⊓ (a ⊔ c) ≤ a ⊔ c
        exact inf_le_right
    _ ≤ a ⊔ b ⊓ c := by
      rw[h₁]
      -- max(min(b,a), min(b,c))
      -- max(a, min(b,c))
      apply sup_le
      · show b ⊓ a ≤ a ⊔ b ⊓ c
        -- min(a,b) ≤ max(a, min(b,c))
        calc
        b ⊓ a ≤ a := by
          exact inf_le_right
        _ ≤ a ⊔ b ⊓ c := by
          exact le_sup_left
      · show b ⊓ c ≤ a ⊔ b ⊓ c
        exact le_sup_right

#check le_inf
#check inf_le_left

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  have h₁ : (a ⊔ b) ⊓ (a ⊔ c) = (a ⊔ b) ⊓ a ⊔ (a ⊔ b) ⊓ c := by
    exact h (a ⊔ b) a c
  rw[h₁]
  show a ⊔ b ⊓ c = (a ⊔ b) ⊓ a ⊔ (a ⊔ b) ⊓ c
  have h₂ : (a ⊔ b) ⊓ a = a := by
    apply le_antisymm
    · show (a ⊔ b) ⊓ a ≤ a
      exact inf_le_right
    · show a ≤ (a ⊔ b) ⊓ a
      apply le_inf
      exact le_sup_left
      exact le_refl a
  rw[h₂]
  show a ⊔ b ⊓ c = a ⊔ (a ⊔ b) ⊓ c
  apply le_antisymm
  · show a ⊔ b ⊓ c ≤ a ⊔ (a ⊔ b) ⊓ c
    apply sup_le
    · show a ≤ a ⊔ (a ⊔ b) ⊓ c
      exact le_sup_left
    · show b ⊓ c ≤ a ⊔ (a ⊔ b) ⊓ c
      calc
      b ⊓ c ≤ (a ⊔ b) ⊓ c := by
        apply le_inf
        · show b ⊓ c ≤ a ⊔ b
          calc
          b ⊓ c ≤ b := by
            exact inf_le_left
          _ ≤ a ⊔ b := by
            exact le_sup_right
        · exact inf_le_right
      _ ≤ a ⊔ (a ⊔ b) ⊓ c := by
        exact le_sup_right

  · show a ⊔ (a ⊔ b) ⊓ c ≤ a ⊔ b ⊓ c
    apply sup_le
    · exact le_sup_left
    · show (a ⊔ b) ⊓ c ≤ a ⊔ b ⊓ c
      rw[inf_comm]
      rw[h]
      apply sup_le
      · show c ⊓ a ≤ a ⊔ b ⊓ c
        calc
        c ⊓ a ≤ a := by
          exact inf_le_right
        _ ≤ a ⊔ b ⊓ c := by
          exact le_sup_left
      · show c ⊓ b ≤ a ⊔ b ⊓ c
        rw[inf_comm]
        exact le_sup_right

-- solution
example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  rw [h, @inf_comm _ _ (a ⊔ b), absorb1, @inf_comm _ _ (a ⊔ b), h, ← sup_assoc, @inf_comm _ _ c a,
    absorb2, inf_comm]

-- sorry
example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  rw[h (a ⊔ b) a c]
  rw[inf_comm (a ⊔ b) a]
  rw[absorb1]
  rw[inf_comm (a ⊔ b) c]
  rw[h]
  rw[← sup_assoc]
  rw[inf_comm c a]
  rw[absorb2 a]
  rw[inf_comm]

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : (a ⊔ b) ⊓ c ≤ a ⊔ (b ⊓ c) := by
  rw[inf_comm]
  rw[h]
  apply sup_le
  · show c ⊓ a ≤ a ⊔ b ⊓ c
    calc
    c ⊓ a ≤ a := by
      exact inf_le_right
    _ ≤ a ⊔ b ⊓ c := by
      exact le_sup_left
  · show c ⊓ b ≤ a ⊔ b ⊓ c
    rw[inf_comm]
    exact le_sup_right

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  sorry

-- solution
example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  rw [h, @sup_comm _ _ (a ⊓ b), absorb2, @sup_comm _ _ (a ⊓ b), h, ← inf_assoc, @sup_comm _ _ c a,
    absorb1, sup_comm]

end

section
variable {R : Type*} [StrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

example (h : a ≤ b) : 0 ≤ b - a := by
  rw[← add_neg_cancel a]
  rw[sub_eq_add_neg]
  apply add_le_add_right
  exact h

example (h : a ≤ b) : 0 ≤ b - a := by
  rw[← add_neg_cancel a]
  rw[sub_eq_add_neg]
  repeat rw[add_comm _ (-a)]
  apply add_le_add_left
  exact h

-- solution
theorem aux1 (h : a ≤ b) : 0 ≤ b - a := by
  rw [← sub_self a, sub_eq_add_neg, sub_eq_add_neg, add_comm, add_comm b]
  apply add_le_add_left h

example (h: 0 ≤ b - a) : a ≤ b := by
  rw[← add_zero b]
  rw[← zero_add a]
  nth_rw 2 [← add_neg_cancel (-a)]
  rw[neg_neg, ← add_assoc]
  repeat rw[add_comm _ a]
  apply add_le_add_left
  rw[← sub_eq_add_neg]
  exact h

-- solution
theorem aux2 (h : 0 ≤ b - a) : a ≤ b := by
  rw [← add_zero a, ← sub_add_cancel b a, add_comm (b - a)]
  apply add_le_add_left h

-- sorry
example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  sorry

-- solution
example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  have h1 : 0 ≤ (b - a) * c := mul_nonneg (aux1 _ _ h) h'
  rw [sub_mul] at h1
  exact aux2 _ _ h1
end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  have h : dist x x ≤ dist x y + dist y x := by
    exact dist_triangle x y x
  rw[dist_self x, dist_comm y x] at h
  rw[← two_mul] at h
  linarith

-- solution
example (x y : X) : 0 ≤ dist x y :=by
  have : 0 ≤ dist x y + dist y x := by
    rw [← dist_self x]
    apply dist_triangle
  linarith [dist_comm x y]

end
