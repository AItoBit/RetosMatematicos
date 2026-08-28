import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Real MeasureTheory Set

noncomputable section

/-!
# Retos Matemáticos (29 de enero de 2023)
* **Propuesto por:** José Manuel Sánchez Muñoz
* **Resuelto por:** Marcio Eusebio Bautista Perez, Alejandro Paredes, Pablo Vitoria García y el proponente.
* **ISSN:** 2952-0746

## Expresión a evaluar:
$$E = \int_1^{e^5} \sqrt{\ln x} \, dx + \int_{e^5}^{e^{25}} \frac{dx}{\sqrt{\ln x}} + \int_0^{\sqrt{5}} e^{x^2} \, dx + \int_{\sqrt{5}}^5 e^{-x^2} \, dx$$
-/

-- ============================================================================
-- 1. DEFINICIONES DE LAS FUNCIONES DE ERROR 
-- ============================================================================

/-- Función de error estándar: erf(x) := (2 / √π) * ∫₀^x e^(-t²) dt -/
def erf (x : ℝ) : ℝ :=
  (2 / Real.sqrt π) * ∫ t in (0 : ℝ)..x, Real.exp (-t^2)

/-- Función de error imaginaria: erfi(x) := (2 / √π) * ∫₀^x e^(t²) dt -/
def erfi (x : ℝ) : ℝ :=
  (2 / Real.sqrt π) * ∫ t in (0 : ℝ)..x, Real.exp (t^2)


-- ============================================================================
-- 2. DEFINICIÓN DE LAS 4 INTEGRALES DE LA EXPRESIÓN
-- ============================================================================

/-- Primera integral: I₁ = ∫₁^{e⁵} √(ln x) dx -/
def I1 : ℝ :=
  ∫ x in (1 : ℝ)..(Real.exp 5), Real.sqrt (Real.log x)

/-- Segunda integral: I₂ = ∫_{e⁵}^{e²⁵} dx / √(ln x) -/
def I2 : ℝ :=
  ∫ x in (Real.exp 5)..(Real.exp 25), 1 / Real.sqrt (Real.log x)

/-- Tercera integral: I₃ = ∫₀^{√5} e^(x²) dx -/
def I3 : ℝ :=
  ∫ x in (0 : ℝ)..(Real.sqrt 5), Real.exp (x^2)

/-- Cuarta integral: I₄ = ∫_{√5}⁵ e^(-x²) dx -/
def I4 : ℝ :=
  ∫ x in (Real.sqrt 5)..(5 : ℝ), Real.exp (-x^2)

/-- Expresión total propuesta: E = I₁ + I₂ + I₃ + I₄ -/
def totalExpr : ℝ :=
  I1 + I2 + I3 + I4


-- ============================================================================
-- 3. EVALUACIÓN DE CADA INTEGRAL PASO A PASO  
-- ============================================================================

/-- Evaluación de I₁ por partes y cambio √(ln x) = t:
    I₁ = √5 * e⁵ - (√π / 2) * erfi(√5) -/
theorem I1_eq :
    I1 = Real.sqrt 5 * Real.exp 5 - (Real.sqrt π / 2) * erfi (Real.sqrt 5) := by
  sorry

/-- Evaluación de I₂ mediante el cambio de variable √(ln x) = t:
    I₂ = √π * (erfi(5) - erfi(√5)) -/
theorem I2_eq :
    I2 = Real.sqrt π * (erfi 5 - erfi (Real.sqrt 5)) := by
  sorry

/-- Evaluación de I₃ en términos de erfi:
    I₃ = (√π / 2) * erfi(√5) -/
theorem I3_eq :
    I3 = (Real.sqrt π / 2) * erfi (Real.sqrt 5) := by
  sorry

/-- Evaluación de I₄ en términos de erf:
    I₄ = (√π / 2) * (erf(5) - erf(√5)) -/
theorem I4_eq :
    I4 = (Real.sqrt π / 2) * (erf 5 - erf (Real.sqrt 5)) := by
  sorry


-- ============================================================================
-- 4. TEOREMA PRINCIPAL: FORMA CERRADA EXACTA 
-- ============================================================================

/-- Teorema: Valor exacto en forma cerrada de la expresión total.
    Nótese la cancelación exacta del término `(√π / 2) * erfi(√5)` entre I₁ e I₃. -/
theorem totalExpr_closed_form :
    totalExpr = Real.sqrt 5 * Real.exp 5 +
                Real.sqrt π * (erfi 5 - erfi (Real.sqrt 5)) +
                (Real.sqrt π / 2) * (erf 5 - erf (Real.sqrt 5)) := by
  dsimp [totalExpr]
  rw [I1_eq, I2_eq, I3_eq, I4_eq]
  ring

end
