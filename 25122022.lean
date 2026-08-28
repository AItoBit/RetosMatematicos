import Mathlib

open MeasureTheory intervalIntegral Real

namespace IntegralExpCos

/-- Serie de términos pares correspondiente a la función de Bessel / Bessel modificada:
    S_par = ∑_{k=0}^∞ 1 / (4^k * (k!)²) -/
noncomputable def even_series_sum : ℝ :=
  ∑' (k : ℕ), (1 : ℝ) / (4 ^ k * (Nat.factorial k : ℝ) ^ 2)

/-- Serie de términos impares correspondiente a la función de Struve / Struve modificada:
    S_impar = ∑_{k=0}^∞ 1 / (2^(2k+1) * Γ(k + 3/2)²) -/
noncomputable def odd_series_sum : ℝ :=
  ∑' (k : ℕ), (1 : ℝ) / (2 ^ (2 * k + 1) * (Gamma (k + 3 / 2 : ℝ)) ^ 2)

/-- Definición de la función de Bessel J₀(z) evaluada en 1 -/
noncomputable def bessel_J0_one : ℝ :=
  ∑' (k : ℕ), ((-1 : ℝ) ^ k * (1 / 2 : ℝ) ^ (2 * k)) / ((Nat.factorial k : ℝ) ^ 2)

/-- Definición de la función de Struve H₀(z) evaluada en 1 -/
noncomputable def struve_H0_one : ℝ :=
  (1 / 2 : ℝ) * ∑' (k : ℕ), ((-1 : ℝ) ^ k * (1 / 2 : ℝ) ^ (2 * k)) / ((Gamma (k + 3 / 2 : ℝ)) ^ 2)

/-!
### Teorema principal: Valor analítico exacto de la integral
-/

/-- Representación de la integral definida en términos de la suma de series par e impar -/
theorem integral_exp_cos_eq_series :
    (∫ x in (0 : ℝ)..(π / 2), exp (cos x)) = 
      2 * π * ((1 / 4 : ℝ) * even_series_sum + (1 / 4 : ℝ) * odd_series_sum) := by
  sorry

/-- Expresión del valor exacto de la integral mediante funciones especiales:
    ∫₀^{π/2} e^(cos x) dx = (π / 2) * (J₀(1) + H₀(1)) -/
theorem integral_exp_cos_eq_special_functions :
    (∫ x in (0 : ℝ)..(π / 2), exp (cos x)) = (π / 2) * (bessel_J0_one + struve_H0_one) := by
  sorry

/-!
### 2ª Forma: Aproximación numérica mediante la Regla de Simpson 3/8 simple
-/

/-- Fórmula de la aproximación de Simpson 3/8:
    I ≈ (π / 16) * (e + 3 * e^(√3 / 2) + 3 * e^(1/2) + 1) -/
noncomputable def simpson_3_8_approx : ℝ :=
  (π / 16) * (exp 1 + 3 * exp (sqrt 3 / 2) + 3 * exp (1 / 2) + 1)

/-- Teorema de equivalencia de la fórmula de Simpson 3/8 simple aplicada en [0, π/2] -/
theorem simpson_3_8_formula :
    ((π / 2 - 0) / 8) * (exp (cos 0) + 3 * exp (cos (π / 6)) + 3 * exp (cos (π / 3)) + exp (cos (π / 2))) =
    simpson_3_8_approx := by
  dsimp [simpson_3_8_approx]
  have h_cos0 : cos 0 = 1 := cos_zero
  have h_cos_pi6 : cos (π / 6) = sqrt 3 / 2 := cos_pi_div_six
  have h_cos_pi3 : cos (π / 3) = 1 / 2 := cos_pi_div_three
  have h_cos_pi2 : cos (π / 2) = 0 := cos_pi_div_two
  rw [h_cos0, h_cos_pi6, h_cos_pi3, h_cos_pi2, exp_zero]
  ring

end IntegralExpCos
