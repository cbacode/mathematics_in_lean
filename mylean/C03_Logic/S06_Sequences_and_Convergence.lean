import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

-- solution
theorem convergesTo_const_ans (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n neq
  calc
    |s n + t n - (a + b)| = |(s n - a) + (t n  - b)| := by
      congr
      exact add_sub_add_comm (s n) (t n) a b
    _ ≤ |s n - a| + |t n  - b| := by
      exact abs_add_le (s n - a) (t n  - b)
    _ < ε / 2 + ε / 2 := by
      have snneq : |s n - a| < ε / 2 := by
        apply hs n
        exact le_of_max_le_left neq
      have tnneq : |t n - b| < ε / 2 := by
        apply ht n
        exact le_of_max_le_right neq
      exact add_lt_add snneq tnneq
    _ = ε := by norm_num

-- solution
theorem convergesTo_add_ans {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n hn
  have ngeNs : n ≥ Ns := le_of_max_le_left hn
  have ngeNt : n ≥ Nt := le_of_max_le_right hn
  calc
    |s n + t n - (a + b)| = |s n - a + (t n - b)| := by
      congr
      ring
    _ ≤ |s n - a| + |t n - b| := (abs_add _ _)
    _ < ε / 2 + ε / 2 := (add_lt_add (hs n ngeNs) (ht n ngeNt))
    _ = ε := by norm_num

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  intro ε epsne
  have : ε / |c| > 0 := by
    exact div_pos epsne acpos
  specialize cs (ε / |c|) this
  rcases cs with ⟨N, Ns⟩
  use N
  intro n neq
  dsimp
  have : |c * s n - c * a| = |c| * |s n - a| := by
    calc
    |c * s n - c * a| = |c * (s n - a)| := by
      congr
      rw [mul_sub_left_distrib c (s n) a]
    _ = |c| * |s n - a| := by
      exact abs_mul c (s n - a)
  rw [this]
  have : |s n - a| * |c| / |c| < ε / |c| := by
    have : |s n - a| * |c| / |c| = |s n - a| := by field_simp
    rw [this]
    exact Ns n neq
  apply (div_lt_div_iff_of_pos_right acpos).mp at this
  rw [mul_comm]
  exact this
#check div_lt_div_iff_of_pos_right

-- solution
theorem convergesTo_mul_const_ans {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  intro ε εpos
  dsimp
  have εcpos : 0 < ε / |c| := by apply div_pos εpos acpos
  rcases cs (ε / |c|) εcpos with ⟨Ns, hs⟩
  use Ns
  intro n ngt
  calc
    |c * s n - c * a| = |c| * |s n - a| := by rw [← abs_mul, mul_sub]
    _ < |c| * (ε / |c|) := (mul_lt_mul_of_pos_left (hs n ngt) acpos)
    _ = ε := mul_div_cancel₀ _ (ne_of_lt acpos).symm

theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n neq
  have : |s n| - |a| < 1 := by
    calc
      |s n| - |a| ≤ |s n - a| := by
        exact abs_sub_abs_le_abs_sub (s n) a
      _ < 1 := by
        exact h n neq
  linarith

-- solution
theorem exists_abs_le_of_convergesTo_ans {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n ngt
  calc
    |s n| = |s n - a + a| := by
      congr
      abel
    _ ≤ |s n - a| + |a| := (abs_add _ _)
    _ < |a| + 1 := by linarith [h n ngt]

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁
  intro n neq
  simp
  calc
    |s n * t n| = |s n| * |t n| := by
      exact abs_mul (s n) (t n)
    _ < B * (ε / B) := by
      apply mul_lt_mul'
      · have : |s n| < B := by
          apply h₀ n
          exact le_of_max_le_left neq
        exact le_of_lt this
      · have : |t n - 0| = |t n| := by
          congr
          rw [sub_zero]
        rw [← this]
        apply h₁
        exact le_of_max_le_right neq
      · exact abs_nonneg (t n)
      · exact Bpos
    _ = ε := by field_simp

-- solution
theorem aux_ans {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁
  intro n ngt
  have ngeN₀ : n ≥ N₀ := le_of_max_le_left ngt
  have ngeN₁ : n ≥ N₁ := le_of_max_le_right ngt
  calc
    |s n * t n - 0| = |s n| * |t n - 0| := by rw [sub_zero, abs_mul, sub_zero]
    _ < B * (ε / B) := (mul_lt_mul'' (h₀ n ngeN₀) (h₁ n ngeN₁) (abs_nonneg _) (abs_nonneg _))
    _ = ε := mul_div_cancel₀ _ (ne_of_lt Bpos).symm

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

-- solution
theorem convergesTo_mul_ans {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by
    apply abs_pos.mpr
    contrapose! abne
    linarith
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by
    apply hNa
    exact le_max_left Na Nb
  have absb : |s N - b| < ε := by
    apply hNb
    exact le_max_right Na Nb
  have : |a - b| < |a - b| := by
    calc
      |a - b| = |(s N - b) + (a - s N)| := by
        congr
        norm_num
      _ ≤ |s N - b| + |a - s N| := by
        exact abs_add_le (s N - b) (a - s N)
      _ < ε + ε := by
        have : |a - s N| = |s N - a| := by
          rw [← abs_neg (a - s N)]
          congr
          norm_num
        rw [this]
        exact add_lt_add absb absa
      _ = |a - b| / 2 + |a - b| / 2 := by rfl
      _ = |a - b| := by norm_num
  exact lt_irrefl _ this

-- solution
theorem convergesTo_unique_ans {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by
    apply lt_of_le_of_ne
    · apply abs_nonneg
    intro h''
    apply abne
    apply eq_of_abs_sub_eq_zero h''.symm
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by
    apply hNa
    apply le_max_left
  have absb : |s N - b| < ε := by
    apply hNb
    apply le_max_right
  have : |a - b| < |a - b|
  calc
    |a - b| = |(-(s N - a)) + (s N - b)| := by
      congr
      ring
    _ ≤ |(-(s N - a))| + |s N - b| := (abs_add _ _)
    _ = |s N - a| + |s N - b| := by rw [abs_neg]
    _ < ε + ε := (add_lt_add absa absb)
    _ = |a - b| := by norm_num [ε]

  exact lt_irrefl _ this

theorem convergesTo_unique_2 {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
      have h₁ := convergesTo_mul_const (-1) sb
      have h₂ := convergesTo_add sa h₁
      simp at h₂
      rcases lt_trichotomy (a + -b) 0 with h_neg | h_zero | h_pos
      · specialize h₂ (-(a + -b))
        have nlt : (-(a + -b)) > 0 := by
          linarith
        have nle : 0 ≤ (-(a + -b)) := by
          linarith
        have := h₂ nlt
        rcases this with ⟨N, Ne⟩
        dsimp at Ne
        have : |-(a + -b)| < -(a + -b) := by
          calc
            |-(a + -b)| = |0 - (a + -b)| := by norm_num
            _ < -(a + -b) := by
              apply Ne N
              linarith
        rw [abs_of_nonneg nle] at this
        exfalso
        exact lt_irrefl (-(a + -b)) this
      · rw [add_eq_zero_iff_eq_neg] at h_zero
        rw [neg_neg] at h_zero
        exact h_zero
      · specialize h₂ (a + -b)
        have nle : -(a + -b) < 0 := by
          linarith
        have := h₂ h_pos
        rcases this with ⟨N, Ne⟩
        dsimp at Ne
        have : |- (a + -b)| < a + -b := by
          calc
            |- (a + -b)| = |0 - (a + -b)| := by norm_num
            _ < a + -b := by
              apply Ne N
              linarith
        rw [abs_of_neg nle, neg_neg] at this
        exfalso
        exact lt_irrefl (a + -b) this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
