import Mathlib

variable {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : (Nat.card G).minFac = p) {P : Sylow p G}

omit [Finite G] in lemma centralizer_le_normalizer (P : Subgroup G) : Subgroup.centralizer (P : Set G) ≤ (P : Subgroup G).normalizer := by
  -- Transfer the problem of subgroup into the problem of subset
  apply Set.le_iff_subset.mpr
  -- Take an element x in the centralizer
  intro x hx
  -- Take any element y in P
  intro y
  constructor
  · -- Assume y is in P
    intro hy
    -- Since x centralizes P, x commutes with y
    have := hx y hy
    -- Simplify the expression
    rw [← this, mul_assoc, mul_inv_cancel, mul_one y]
    -- Show the result is in P
    exact hy
  · -- The converse direction
    intro hy
    -- Use the property of centralizer
    have := hx (x * y * x⁻¹) hy
    -- Simplify the expression
    rw [mul_assoc (x * y), inv_mul_cancel, mul_one] at this
    apply mul_left_cancel at this
    rw [this]
    -- Show the result is in P
    exact hy

include hp in
theorem normalizer_eq_centralizer_of_cyclic_sylow (hP : IsCyclic (P : Subgroup G)) :
    P.normalizer = Subgroup.centralizer (P : Set G) := by
  have CleN := centralizer_le_normalizer (P : Subgroup G)
  have NleC := IsCyclic.normalizer_le_centralizer hp hP
  exact le_antisymm NleC CleN
