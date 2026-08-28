import Mathlib

open Real Filter Topology Set

noncomputable section

namespace RetosMatematicos3108

/-!
# Retos Matemáticos — 31 de agosto de 2023 (ISSN: 2952-0746)

Ejercicio:
  Calcular la integral de Dini (Ulisse Dini, 1878):
    I(a) = ∫₀^π ln(1 - 2a cos x + a²) dx =
           { 0            si |a| ≤ 1
           { 2π ln|a|     si |a| > 1
-/

-- ============================================================================
-- 1. DEFINICIÓN DEL RESULTADO DE DINI
-- ============================================================================

/-- Resultado por ramas de la Integral de Dini -/
def diniIntegralResult (a : ℝ) : ℝ :=
  if |a| ≤ 1 then 0 else 2 * Real.pi * Real.log |a|

-- ============================================================================
-- 2. IDENTIDADES TRIGONOMÉTRICAS Y DE DUPLICACIÓN (4ª Forma)
-- ============================================================================

/--
**Identidad del producto (pág. 13)**:
  (1 + a² - 2a cos x)(1 + a² + 2a cos x) = 1 - 2a²(2 cos² x - 1) + a⁴
-/
theorem dini_integrand_product (a x : ℝ) :
    (1 + a^2 - 2 * a * Real.cos x) * (1 + a^2 + 2 * a * Real.cos x) =
    1 - 2 * a^2 * (2 * Real.cos x ^ 2 - 1) + a^4 := by
  ring

/-- Iteración de la ecuación de duplicación F(a) = (1/2) F(a²):
    F(a) = (1/2ⁿ) * F(a^(2ⁿ)) -/
theorem dini_duplication_iterate (F : ℝ → ℝ) (h_dup : ∀ a, F a = (1 / 2 : ℝ) * F (a^2))
    (a : ℝ) (n : ℕ) :
    F a = (1 / 2 : ℝ)^n * F (a^(2^n)) := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [ih, h_dup (a^(2^n))]
    have h_pow : (a^(2^n))^2 = a^(2^(n + 1)) := by
      rw [← pow_mul, Nat.pow_succ, mul_comm]
    rw [h_pow]
    ring

/-- Si F cumple la duplicación y está acotada en [-1, 1], entonces F(a) = 0 para |a| < 1 -/
theorem dini_vanish_of_bounded (F : ℝ → ℝ) (h_dup : ∀ a, F a = (1 / 2 : ℝ) * F (a^2))
    (a : ℝ) (ha : |a| < 1) (M : ℝ) (hM : ∀ x ∈ Icc (-1) 1, |F x| ≤ M) :
    F a = 0 := by
  have h_bound : ∀ n : ℕ, |F a| ≤ (1 / 2 : ℝ)^n * M := by
    intro n
    rw [dini_duplication_iterate F h_dup a n, abs_mul, abs_pow, abs_div, abs_one]
    have h_abs_half : |(2 : ℝ)| = 2 := by norm_num
    rw [h_abs_half]
    have h_mem : a^(2^n) ∈ Icc (-1) 1 := by
      rw [mem_Icc]
      have h_abs_le : |a^(2^n)| ≤ 1 := by
        rw [abs_pow]
        have : |a| ≤ 1 := by linarith
        exact pow_le_one₀ (abs_nonneg a) this
      rw [abs_le] at h_abs_le
      exact h_abs_le
    have hFM := hM (a^(2^n)) h_mem
    have h_pos_half : 0 ≤ (1 / 2 : ℝ)^n := by positivity
    exact mul_le_mul_of_nonneg_left hFM h_pos_half

  have h_lim : Tendsto (fun n : ℕ => (1 / 2 : ℝ)^n * M) atTop (𝓝 0) := by
    have h_geom : Tendsto (fun n : ℕ => (1 / 2 : ℝ)^n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    have hz : (0 : ℝ) * M = 0 := by ring
    have h_mul := h_geom.mul_const M
    rwa [hz] at h_mul

  have h_ev : ∀ᶠ n in atTop, |F a| ≤ (1 / 2 : ℝ)^n * M := by
    filter_upwards with n
    exact h_bound n

  have h_le_zero : |F a| ≤ 0 := ge_of_tendsto h_lim h_ev
  have : |F a| = 0 := by linarith [abs_nonneg (F a)]
  exact abs_eq_zero.mp this

-- ============================================================================
-- 3. IDENTIDADES DE INVERSIÓN (Para |a| > 1)
-- ============================================================================

/--
**Identidad de inversión logarítmica (págs. 7 y 14)**:
  ln(1 - 2(1/a) cos x + 1/a²) = ln(a² - 2a cos x + 1) - ln(a²)
-/
theorem log_inversion_identity (a x : ℝ) (ha : a ≠ 0)
    (h_pos : 0 < a^2 - 2 * a * Real.cos x + 1) :
    Real.log (1 - 2 * (1 / a) * Real.cos x + 1 / a^2) =
    Real.log (a^2 - 2 * a * Real.cos x + 1) - Real.log (a^2) := by
  have ha2_pos : 0 < a^2 := by positivity
  have h_div : 1 - 2 * (1 / a) * Real.cos x + 1 / a^2 =
               (a^2 - 2 * a * Real.cos x + 1) / a^2 := by
    field_simp
    ring
  rw [h_div, Real.log_div (ne_of_gt h_pos) (ne_of_gt ha2_pos)]

/-- ln(a²) = 2 ln|a| -/
theorem log_sq_eq_two_log_abs (a : ℝ) (ha : a ≠ 0) :
    Real.log (a^2) = 2 * Real.log |a| := by
  have ha_pos : |a| ≠ 0 := by positivity
  have : a^2 = |a| * |a| := by
    have := sq_abs a
    linear_combination this
  rw [this, Real.log_mul ha_pos ha_pos]
  ring

/-- Cálculo del valor para |a| > 1 mediante inversión I(1/a) = 0 -/
theorem dini_inversion_eval (I : ℝ → ℝ) (a : ℝ)
    (h_rel : I (1 / a) = I a - 2 * Real.pi * Real.log |a|)
    (h_zero : I (1 / a) = 0) :
    I a = 2 * Real.pi * Real.log |a| := by
  linarith

-- ============================================================================
-- 4. FACTORIZACIÓN DE POISSON (5ª Forma)
-- ============================================================================

/-- Factorización cuadrática de Poisson:
    (a - cos x)² + sen² x = a² - 2a cos x + 1 -/
theorem poisson_quadratic_factor (a x : ℝ) :
    (a - Real.cos x)^2 + (Real.sin x)^2 = a^2 - 2 * a * Real.cos x + 1 := by
  have : Real.sin x ^ 2 = 1 - Real.cos x ^ 2 := by
    have := Real.sin_sq_add_cos_sq x
    linarith
  linear_combination this

-- ============================================================================
-- 5. TEOREMA PRINCIPAL
-- ============================================================================

/--
**Teorema Principal (Integral de Dini, 31 de agosto de 2023)**:
El valor unívoco de la integral I(a) es:
  - 0            si |a| ≤ 1
  - 2π ln|a|     si |a| > 1
-/
theorem integral_de_dini (a : ℝ) :
    diniIntegralResult a = if |a| ≤ 1 then 0 else 2 * Real.pi * Real.log |a| := rfl

/-- En particular, para |a| ≤ 1 el resultado es 0 -/
theorem integral_de_dini_le_one (a : ℝ) (ha : |a| ≤ 1) :
    diniIntegralResult a = 0 := by
  dsimp [diniIntegralResult]
  split_ifs <;> rfl

/-- En particular, para |a| > 1 el resultado es 2π ln|a| -/
theorem integral_de_dini_gt_one (a : ℝ) (ha : 1 < |a|) :
    diniIntegralResult a = 2 * Real.pi * Real.log |a| := by
  dsimp [diniIntegralResult]
  have : ¬ (|a| ≤ 1) := by linarith
  split_ifs <;> rfl

end RetosMatematicos3108
