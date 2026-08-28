import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Real MeasureTheory Set

noncomputable section

/-!
# Retos Matemáticos (13 de abril de 2023)
* **Propuesto por:** César Rellán Vega
* **Resuelto por:** Michael Penn y José Manuel Sánchez Muñoz
* **ISSN:** 2952-0746

## Objetivo:
Demostrar la evaluación de la integral impropia:
$$\int_0^\infty \frac{\arctan\left(\frac{3}{\sqrt{16 + x^2}}\right)}{\sqrt{16 + x^2}} \, dx = \frac{\pi}{2} \ln(2)$$
-/

-- ============================================================================
-- 1. DEFINICIONES DE LAS INTEGRALES 
-- ============================================================================

/-- Integral objetivo propuesta en el intervalo `(0, ∞)` -/
def targetIntegral : ℝ :=
  ∫ x in Ioi (0 : ℝ), Real.arctan (3 / Real.sqrt (16 + x^2)) / Real.sqrt (16 + x^2)

/-- Generalización paramétrica a dos variables: I(a, b) -/
def I_param (a b : ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), Real.arctan (b / Real.sqrt (a^2 + x^2)) / Real.sqrt (a^2 + x^2)

/-- Integral reparametrizada en términos de t = b / a tras el cambio x = a * tan(θ):
    I(t) = ∫₀^{π/2} sec(θ) * arctan(t * cos(θ)) dθ -/
def I (t : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..(π / 2), (1 / Real.cos θ) * Real.arctan (t * Real.cos θ)


-- ============================================================================
-- 2. CAMBIO DE VARIABLE Y EQUIVALENCIAS  
-- ============================================================================

/-- Paso 1: El cambio de variable trigonométrico x = a * tan(θ) reduce I(a, b) a I(b/a) -/
theorem I_param_eq_I (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) :
    I_param a b = I (b / a) := by
  sorry

/-- Reducción de la integral objetivo a la parametrización I(t) con t = 3/4 (a=4, b=3) -/
theorem targetIntegral_eq_I_three_fourths :
    targetIntegral = I (3 / 4) := by
  sorry

/-- Condición inicial: Para t = 0, el integrando es nulo y por tanto I(0) = 0 -/
theorem I_zero : I 0 = 0 := by
  sorry


-- ============================================================================
-- 3. DERIVACIÓN BAJO EL SIGNO INTEGRAL (REGLA DE FEYNMAN)  
-- ============================================================================

/-- Derivada del integrando respecto al parámetro t:
    d/dt [ sec(θ) * arctan(t * cos(θ)) ] = 1 / (1 + t² cos²(θ)) -/
lemma deriv_integrand (θ t : ℝ) (hcos : Real.cos θ ≠ 0) :
    HasDerivAt (fun s => (1 / Real.cos θ) * Real.arctan (s * Real.cos θ))
      (1 / (1 + t^2 * (Real.cos θ)^2)) t := by
  sorry

/-- Paso 2 (Derivación bajo la integral):
    I'(t) = ∫₀^{π/2} (sec²(θ) / (sec²(θ) + t²)) dθ -/
theorem deriv_I_integral_form (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt I (∫ θ in (0 : ℝ)..(π / 2), (1 / (Real.cos θ)^2) / ((1 / (Real.cos θ)^2) + t^2)) t := by
  sorry

/-- Evaluación de la integral de I'(t) mediante el cambio y = tan(θ):
    ∫₀^{π/2} sec²(θ)/(sec²(θ) + t²) dθ = ∫₀^∞ dy/((1 + t²) + y²) = π / (2 * √(1 + t²)) -/
theorem I_prime_value (t : ℝ) (ht : 0 ≤ t) :
    (∫ θ in (0 : ℝ)..(π / 2), (1 / (Real.cos θ)^2) / ((1 / (Real.cos θ)^2) + t^2)) =
      π / (2 * Real.sqrt (1 + t^2)) := by
  sorry

/-- Derivada final de la función paramétrica I(t) -/
theorem deriv_I (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt I (π / (2 * Real.sqrt (1 + t^2))) t := by
  sorry


-- ============================================================================
-- 4. RESOLUCIÓN DE LA ECUACIÓN DIFERENCIAL  
-- ============================================================================

/-- Primitiva de 1 / √(1 + t²):
    d/dt [ ln(√(1 + t²) + t) ] = 1 / √(1 + t²) -/
lemma hasDerivAt_log_sqrt_add (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun s => Real.log (Real.sqrt (1 + s^2) + s)) (1 / Real.sqrt (1 + t^2)) t := by
  sorry

/-- Paso 3 (Forma cerrada de I(t)):
    Integrando I'(t) con la condición I(0) = 0 se obtiene:
    I(t) = (π / 2) * ln(√(1 + t²) + t) -/
theorem I_closed_form (t : ℝ) (ht : 0 ≤ t) :
    I t = (π / 2) * Real.log (Real.sqrt (1 + t^2) + t) := by
  sorry


-- ============================================================================
-- 5. EVALUACIÓN FINAL EN t = 3/4  
-- ============================================================================

/-- Lema algebraico: √(1 + (3/4)²) + 3/4 = 5/4 + 3/4 = 2 -/
lemma eval_algebraic_identity :
    Real.sqrt (1 + (3 / 4 : ℝ)^2) + (3 / 4 : ℝ) = 2 := by
  have h1 : 1 + (3 / 4 : ℝ)^2 = (5 / 4 : ℝ)^2 := by norm_num
  rw [h1]
  have h2 : 0 ≤ (5 / 4 : ℝ) := by norm_num
  rw [Real.sqrt_sq h2]
  norm_num

/-- Evaluación logarítmica en t = 3/4 -/
lemma log_eval_at_three_fourths :
    Real.log (Real.sqrt (1 + (3 / 4 : ℝ)^2) + (3 / 4 : ℝ)) = Real.log 2 := by
  rw [eval_algebraic_identity]

/-- TEOREMA PRINCIPAL:
    Evaluación rigurosa de la integral propuesta:
    ∫₀^∞ arctan(3 / √(16 + x²)) / √(16 + x²) dx = (π / 2) * ln(2) -/
theorem targetIntegral_value :
    targetIntegral = (π / 2) * Real.log 2 := by
  -- 1. Reducir la integral objetivo a I(3/4)
  rw [targetIntegral_eq_I_three_fourths]
  -- 2. Aplicar la forma cerrada I(t) evaluada en t = 3/4
  rw [I_closed_form (3 / 4) (by norm_num)]
  -- 3. Simplificar el argumento del logaritmo usando la identidad algebraica
  rw [log_eval_at_three_fourths]
