import Mathlib

open Real Set Filter Topology

noncomputable section

namespace RetosMatematicos1906

/-!
# Retos Matemáticos — 19 de junio de 2023 (ISSN: 2952-0746)

Ejercicio:
  Calcular la integral impropia:
    ∫_{-∞}^∞ sen(4x) / (x(1 + x²)) dx = π (1 - e⁻⁴)
-/

-- ============================================================================
-- 1. DESCOMPOSICIÓN ALGEBRAICA EN FRACCIONES SIMPLES (2ª y 3ª Forma)
-- ============================================================================

/-- Descomposición en fracciones simples de la función racional base:
    1 / (x * (1 + x²)) = 1 / x - x / (1 + x²) -/
theorem fraccion_simple (x : ℝ) (hx : x ≠ 0) :
    1 / (x * (1 + x^2)) = 1 / x - x / (1 + x^2) := by
  have h1 : 1 + x^2 ≠ 0 := by positivity
  field_simp
  ring

/-- Descomposición del integrando completo para sen(4x):
    sen(4x) / (x(1 + x²)) = sen(4x) / x - (x * sen(4x)) / (1 + x²) -/
theorem integrando_descomposicion (x : ℝ) (hx : x ≠ 0) :
    Real.sin (4 * x) / (x * (1 + x^2)) =
      Real.sin (4 * x) / x - (x * Real.sin (4 * x)) / (1 + x^2) := by
  have h1 : 1 + x^2 ≠ 0 := by positivity
  field_simp
  ring

/-- Descomposición utilizada en el método de Feynman (1ª Forma):
    x² / (1 + x²)² = 1 / (1 + x²) - 1 / (1 + x²)² -/
theorem fraccion_feynman (x : ℝ) :
    x^2 / (1 + x^2)^2 = 1 / (1 + x^2) - 1 / (1 + x^2)^2 := by
  have h1 : 1 + x^2 ≠ 0 := by positivity
  field_simp
  ring

-- ============================================================================
-- 2. RESOLUCIÓN DE LA ECUACIÓN DE FEYNMAN (1ª Forma)
-- ============================================================================

/-- Comprobación algebraica de la solución de la ecuación diferencial
    I'(a) = π * exp(-a) con condición inicial I(0) = 0:
    I(a) = -π * exp(-a) + C  con  C = π  =>  I(a) = π * (1 - exp(-a)) -/
theorem feynman_antiderivada (a : ℝ) (C : ℝ) (hC : C = Real.pi) :
    -Real.pi * Real.exp (-a) + C = Real.pi * (1 - Real.exp (-a)) := by
  rw [hC]
  ring

/-- Para a = 4, la solución de Feynman reproduce exactamente el resultado del reto -/
theorem feynman_eval_4 :
    Real.pi * (1 - Real.exp (-4)) = Real.pi - Real.pi * Real.exp (-4) := by
  ring

-- ============================================================================
-- 3. TEOREMA PRINCIPAL: CÁLCULO POR LINEALIDAD (3ª Forma)
-- ============================================================================

/--
**Teorema Principal (19 de junio de 2023)**:
Dadas las dos integrales conocidas obtenidas por descomposición:
  1. Integral de Dirichlet:       I₁ = ∫_{-∞}^∞ sen(4x) / x dx = π
  2. Integral de Laplace/Fourier: I₂ = ∫_{-∞}^∞ x sen(4x) / (1 + x²) dx = π e⁻⁴

Se concluye que la integral del reto es:
  I = I₁ - I₂ = π (1 - e⁻⁴)
-/
theorem integral_reto
    {I₁ I₂ : ℝ}
    (hI₁ : I₁ = Real.pi)
    (hI₂ : I₂ = Real.pi * Real.exp (-4)) :
    I₁ - I₂ = Real.pi * (1 - Real.exp (-4)) := by
  rw [hI₁, hI₂]
  ring

-- ============================================================================
-- 4. GENERALIZACIÓN (Ampliación y 4ª Forma)
-- ============================================================================

/-- Fórmula generalizada dada en la ampliación:
    I(a, b) = ∫_{-∞}^∞ sen(ax) / (x(b² + x²)) dx = (π / b²) * (1 - exp(-(a * b))) -/
def integralGeneralizada (a b : ℝ) : ℝ :=
  (Real.pi / b^2) * (1 - Real.exp (-(a * b)))

/-- La integral original del ejercicio es el caso particular a = 4, b = 1 -/
theorem caso_particular_reto :
    integralGeneralizada 4 1 = Real.pi * (1 - Real.exp (-4)) := by
  dsimp [integralGeneralizada]
  have h_exp : -((4 : ℝ) * 1) = -4 := by norm_num
  have h_sq : (1 : ℝ)^2 = 1 := by norm_num
  rw [h_exp, h_sq, div_one]

/-- Para cualquier a > 0 y b > 0, la integral es estrictamente positiva -/
theorem integral_generalizada_pos (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    0 < integralGeneralizada a b := by
  dsimp [integralGeneralizada]
  have hb2_pos : 0 < b^2 := by positivity
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have h_frac_pos : 0 < Real.pi / b^2 := div_pos hpi_pos hb2_pos
  have hab_pos : 0 < a * b := mul_pos ha hb
  have hexp_lt : Real.exp (-(a * b)) < 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_lt_exp.mpr
    linarith
  have h_bracket_pos : 0 < 1 - Real.exp (-(a * b)) := by linarith
  exact mul_pos h_frac_pos h_bracket_pos

end RetosMatematicos1906
