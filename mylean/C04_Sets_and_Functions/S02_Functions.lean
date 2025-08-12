import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

#check preimage f
#check f ⁻¹' u

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  · intro h x xs
    show f x ∈ v
    rw [subset_def] at h
    have := h (f x)
    apply this
    simp
    use x
  · intro h x xfs
    simp at xfs
    rcases xfs with ⟨y, ys, fy⟩
    rw [subset_def] at h
    have := h y ys
    rw [← fy]
    simp at this
    exact this

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  intro x h
  simp at h
  rcases h with ⟨y, ys, fy⟩
  have := h fy
  rw [← this]
  exact ys

example : f '' (f ⁻¹' u) ⊆ u := by
  intro x h
  simp at h
  rcases h with ⟨y, fyu, fyx⟩
  rw [fyx] at fyu
  exact fyu

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro x h₁
  simp
  have := h x
  rcases this with ⟨a, fa⟩
  use a
  constructor
  · rw [fa]
    exact h₁
  · assumption

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  intro x hx
  rcases hx with ⟨y, ys, fy⟩
  have := h ys
  use y

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro x hx
  simp at hx
  simp
  exact h hx

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x
  constructor
  · simp
  · simp

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  intro x h
  constructor
  repeat
  rcases h with ⟨y, ⟨ys, yt⟩, fy⟩
  use y

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  intro x hx
  rcases hx with ⟨⟨y, ys, fy⟩, ⟨z, zt, fz⟩⟩
  rw [← fy] at fz
  have zy := h fz
  rw [zy] at zt
  use y
  constructor
  · constructor
    · exact ys
    · exact zt
  · exact fy

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  intro x hx
  rcases hx with ⟨xfs, xft⟩
  rcases xfs with ⟨y, ys, fyx⟩
  use y
  constructor
  · constructor
    · exact ys
    contrapose! xft
    use y
  · exact fyx

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  intro x
  simp
  -- f x ∈ u ∧ f x ∉ v

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext x
  constructor
  · intro h
    rcases h with ⟨xfs, xv⟩
    rcases xfs with ⟨y, ys, xfy⟩
    use y
    constructor
    · constructor
      · exact ys
      · simp
        rw [xfy]
        exact xv
    · exact xfy
  · intro h
    rcases h with ⟨y, yin, fyx⟩
    rcases yin with ⟨ys, vy⟩
    simp at vy
    rw [fyx] at vy
    constructor
    · use y
    · exact vy

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  intro x hx
  rcases hx with ⟨y, yin, xfy⟩
  rcases yin with ⟨ys, fyu⟩
  simp at fyu
  constructor
  · use y
  · rw [xfy] at fyu
    exact fyu

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  intro x hx
  rcases hx with ⟨xs, fxu⟩
  simp at fxu
  simp
  constructor
  · use x
  · exact fxu

-- solution
example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  rintro x ⟨xs, fxu⟩
  exact ⟨⟨x, xs, rfl⟩, fxu⟩

-- another solution
example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  rintro x (xs | fxu)
  · left
    exact ⟨x, xs, rfl⟩
  right; exact fxu

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext x
  simp
  constructor
  · intro h
    rcases h with ⟨y, yAi, fyx⟩
    rcases yAi with ⟨i, yAi⟩
    use i
    use y
  · intro h
    rcases h with ⟨i, y, yAi, fyx⟩
    use y
    constructor
    · use i
    · exact fyx

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  intro x h
  simp
  intro i
  rcases h with ⟨y, hy, fyx⟩
  use y
  constructor
  · simp at hy
    exact hy i
  · exact fyx

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro x hx
  simp at hx
  simp
  rcases hx i with ⟨y, yAi, fyx⟩
  use y
  constructor
  · intro j
    rcases hx j with ⟨y', yAj, fyx'⟩
    unfold Injective at injf
    rw [← fyx] at fyx'
    have := injf fyx'
    rw [this] at yAj
    exact yAj
  · exact fyx

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x
  constructor
  · intro hx
    simp at hx
    rcases hx with ⟨i, hx⟩
    simp
    use i
  · intro hx
    simp
    simp at hx
    exact hx

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x
  constructor
  · simp
  · simp

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x xpos y ypos
  intro hx
  have : √x * √x = √y * √y := by
    rw [hx]
  rw [mul_self_sqrt xpos] at this
  rw [mul_self_sqrt ypos] at this
  exact this

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x xpos y ypos
  intro hx
  simp at hx
  simp at xpos
  simp at ypos
  have eq : (x + y) * (x - y) = 0 := by
    calc
    (x + y) * (x - y) = x ^ 2 - y ^ 2 := by
      ring
    _ = 0 := by field_simp [hx]
  rcases lt_trichotomy x 0 with h | h | h
  · by_contra h₁
    exact not_le_of_lt h xpos
  · rw [h] at eq
    simp at eq
    rw [h, eq]
  · have : x + y > 0 := by exact add_pos_of_pos_of_nonneg h ypos
    rcases mul_eq_zero.1 eq with (hc | hx)
    · rw [hc] at this
      by_contra h₁
      exact lt_irrefl 0 this
    · exact sub_eq_zero.mp hx

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext y
  constructor
  · rintro ⟨x, hx, fyx⟩
    simp at hx
    simp
    rw [← fyx]
    exact sqrt_nonneg x
  · intro ypos
    simp
    simp at ypos
    use y ^ 2
    constructor
    · exact sq_nonneg y
    · exact sqrt_sq ypos

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext y
  constructor
  · intro hx
    simp at hx
    rcases hx with ⟨x, hx⟩
    simp
    rw [← hx]
    exact sq_nonneg x
  · intro ypos
    simp
    simp at ypos
    use sqrt y
    exact sq_sqrt ypos

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  · intro injf
    intro y
    unfold inverse
    have : ∃ x, f x = f y := by use y
    rw [dif_pos this]
    have feq := Classical.choose_spec this
    exact injf feq
  · intro invf
    intro x y
    intro e
    sorry

#check inverse_spec
#check Injective

-- solution

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  · intro h y
    apply h
    apply inverse_spec
    use y
  intro h x1 x2 e
  rw [← h x1, ← h x2, e]

example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  · intro surj
    intro y
    have : ∃ x, f x = y := by
      unfold Surjective at surj
      exact surj y
    exact inverse_spec y this
  · intro invf
    intro y
    have := invf y
    use inverse f y

#check Surjective

example : Surjective f ↔ RightInverse (inverse f) f :=
  sorry

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := h₁
  have h₃ : j ∉ S:= by
    rwa [h] at h₁
  contradiction

-- COMMENTS: TODO: improve this
end
