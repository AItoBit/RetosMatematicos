import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace RetosMatematicos13112024

open Polynomial

/-- The polynomial `P(x) = x³ + x² + m x + n`, as a polynomial with real coefficients. -/
noncomputable def P (m n : ℝ) : Polynomial ℝ :=
  X ^ 3 + X ^ 2 + Polynomial.C m * X + Polynomial.C n

/-- The evaluation of `P(x) = x³ + x² + m x + n` at a point of a commutative ring
containing the coefficients (used for `x` real or complex). -/
def Pval {R : Type*} [CommRing R] (m n x : R) : R := x ^ 3 + x ^ 2 + m * x + n

@[simp] lemma eval_P (m n x : ℝ) : (P m n).eval x = Pval m n x := by
  simp [P, Pval]

/-- **Part (a)**: `P(-1) - 2 P(0) + P(1) = 2` for all values of `m` and `n`. -/
theorem part_a (m n : ℝ) :
    (P m n).eval (-1) - 2 * (P m n).eval 0 + (P m n).eval 1 = 2 := by
  simp [P]
  ring

/-- Explicit division of `P` by `X² + 1`: `P = (X²+1)(X+1) + (m-1)X + (n-1)`. -/
lemma P_div_decomposition (m n : ℝ) :
    P m n = (X ^ 2 + 1) * (X + 1) + (Polynomial.C (m - 1) * X + Polynomial.C (n - 1)) := by
  simp only [P, Polynomial.C_sub, Polynomial.C_1]
  ring

/-- **Part (b)**: `P(x) = x³ + x² + m x + n` is divisible by `x² + 1` if and only if
`m = n = 1`. -/
theorem part_b (m n : ℝ) : (X ^ 2 + 1 : Polynomial ℝ) ∣ P m n ↔ m = 1 ∧ n = 1 := by
  constructor
  · intro h
    have hr : (X ^ 2 + 1 : Polynomial ℝ) ∣
        (Polynomial.C (m - 1) * X + Polynomial.C (n - 1)) := by
      have := (Dvd.dvd.sub h (Dvd.intro _ rfl) :
        (X ^ 2 + 1 : Polynomial ℝ) ∣ P m n - (X ^ 2 + 1) * (X + 1))
      simpa [P_div_decomposition m n] using this
    by_cases hz : (Polynomial.C (m - 1) * X + Polynomial.C (n - 1)) = 0
    · have hm : m - 1 = 0 := by
        have := congrArg (fun p => Polynomial.coeff p 1) hz
        simpa [Polynomial.coeff_one] using this
      have hn : n - 1 = 0 := by
        have := congrArg (fun p => Polynomial.coeff p 0) hz
        simpa [Polynomial.coeff_one] using this
      constructor <;> linarith
    · exfalso
      have hdeg := Polynomial.degree_le_of_dvd hr hz
      have h1 : (2 : WithBot ℕ) ≤ (X ^ 2 + 1 : Polynomial ℝ).degree := by
        have : (X ^ 2 + 1 : Polynomial ℝ).degree = 2 := by
          compute_degree!
        simp [this]
      have h2 : (Polynomial.C (m - 1) * X + Polynomial.C (n - 1)).degree ≤ 1 := by
        compute_degree
      have := le_trans h1 (le_trans hdeg h2)
      norm_num at this
  · rintro ⟨rfl, rfl⟩
    refine ⟨X + 1, ?_⟩
    simp only [P_div_decomposition]
    simp

/-- **Part (c)**: if `x₁, x₂, x₃` are the roots of `P` (i.e. `P` factors as
`(x - x₁)(x - x₂)(x - x₃)` over `ℂ`), then
`3(x₁x₂ + x₁x₃ + x₂x₃ + x₁x₂x₃) - (x₁³ + x₂³ + x₃³) = 1`, for all values of `m` and `n`. -/
theorem part_c (m n : ℝ) (x₁ x₂ x₃ : ℂ)
    (h : ∀ x : ℂ, Pval (m : ℂ) (n : ℂ) x = (x - x₁) * (x - x₂) * (x - x₃)) :
    3 * (x₁ * x₂ + x₁ * x₃ + x₂ * x₃ + x₁ * x₂ * x₃) - (x₁ ^ 3 + x₂ ^ 3 + x₃ ^ 3) = 1 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h (-1)
  simp only [Pval] at h0 h1 h2
  -- Vieta: the sum of the roots is `-1`
  have hsum : x₁ + x₂ + x₃ = -1 := by linear_combination (h1 + h2 - 2 * h0) / 2
  linear_combination
    (3 * (x₁ * x₂ + x₁ * x₃ + x₂ * x₃) - (x₁ + x₂ + x₃) ^ 2 + (x₁ + x₂ + x₃) - 1) * hsum

end RetosMatematicos13112024
