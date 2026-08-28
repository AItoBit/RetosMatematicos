import Mathlib

open Real Set Filter Topology

noncomputable section

namespace RetosMatematicos2004

/-!
# Retos Matemáticos — 20 de abril de 2023 (ISSN: 2952-0746)

Ejercicio:
  Calcular la integral impropia:
    ∫₀^∞ sen³(x) / x³ dx = 3π / 8
-/

-- ============================================================================
-- 1. IDENTIDADES TRIGONOMÉTRICAS Y DEL INTEGRANDO
-- ============================================================================

/-- Fórmula del ángulo triple: sen(3x) = 3 sen(x) - 4 sen³(x) -/
theorem sin_three_x (x : ℝ) :
    Real.sin (3 * x) = 3 * Real.sin x - 4 * (Real.sin x)^3 := by
  have h3 : 3 * x = (x + x) + x := by ring
  rw [h3, Real.sin_add, Real.sin_add, Real.cos_add]
  linear_combination (3 * Real.sin x) * (Real.sin_sq_add_cos_sq x)

/-- Reducción de potencias del seno al cubo: sen³(x) = (3 sen(x) - sen(3x)) / 4 -/
theorem sin_cubed_eq (x : ℝ) :
    (Real.sin x)^3 = (3 * Real.sin x - Real.sin (3 * x)) / 4 := by
  have h := sin_three_x x
  linarith

/-- Descomposición del integrando completo para x ≠ 0 -/
theorem integrando_sin_cubed (x : ℝ) :
    (Real.sin x)^3 / x^3 = (1 / 4 : ℝ) * ((3 * Real.sin x - Real.sin (3 * x)) / x^3) := by
  have h := sin_cubed_eq x
  rw [h]
  ring

-- ============================================================================
-- 2. RESOLUCIÓN POR INTEGRACIÓN POR PARTES (2ª y 3ª Forma)
-- ============================================================================

/--
**Teorema (3ª Forma)**:
Integrando por partes dos veces se llega a la expresión:
  I = (3/8) * (-J(1) + 3*J(3))
donde J(a) = ∫₀^∞ sen(ax)/x dx = π/2 para todo a > 0 (Integral de Dirichlet).
-/
theorem integral_por_partes_eval
    {J₁ J₃ : ℝ}
    (hJ₁ : J₁ = Real.pi / 2)
    (hJ₃ : J₃ = Real.pi / 2) :
    (3 / 8 : ℝ) * (-J₁ + 3 * J₃) = 3 * Real.pi / 8 := by
  rw [hJ₁, hJ₃]
  ring

-- ============================================================================
-- 3. RESOLUCIÓN MEDIANTE EL PARÁMETRO DE FEYNMAN (1ª Forma)
-- ============================================================================

/-- Doble integración de I''(t) = 3π/4 con condiciones I(0) = 0 e I'(0) = 0:
    I(t) = (3π/8) * t² -/
theorem feynman_doble_integral (t : ℝ) :
    (3 * Real.pi / 4) * (t^2 / 2) = (3 * Real.pi / 8) * t^2 := by
  ring

/-- Para t = 1, se recupera exactamente el resultado del reto -/
theorem feynman_caso_t_uno :
    (3 * Real.pi / 8) * (1 : ℝ)^2 = 3 * Real.pi / 8 := by
  ring

-- ============================================================================
-- 4. FÓRMULA GENERALIZADA (págs. 9 y 11)
-- ============================================================================

/--
**Fórmula generalizada (págs. 9–11)** para n = 3:
  ∫₀^∞ senⁿ(x)/xⁿ dx = (π / (2ⁿ (n-1)!)) * ∑_{k=0}^{⌊(n-1)/2⌋} (-1)ᵏ (n choose k) (n - 2k)ⁿ⁻¹
Para n = 3:
  (π / (2³ · 2!)) * [ (3 choose 0)·3² - (3 choose 1)·1² ] = 3π / 8
-/
theorem formula_general_n3 :
    (Real.pi / ((2 : ℝ)^3 * (Nat.factorial 2 : ℝ))) *
      ((Nat.choose 3 0 : ℝ) * 3^2 - (Nat.choose 3 1 : ℝ) * 1^2) =
    3 * Real.pi / 8 := by
  have hc0 : (Nat.choose 3 0 : ℝ) = 1 := by exact_mod_cast (by rfl : Nat.choose 3 0 = 1)
  have hc1 : (Nat.choose 3 1 : ℝ) = 3 := by exact_mod_cast (by rfl : Nat.choose 3 1 = 3)
  have hf2 : (Nat.factorial 2 : ℝ) = 2 := by exact_mod_cast (by rfl : Nat.factorial 2 = 2)
  have h23 : (2 : ℝ)^3 = 8 := by norm_num
  rw [hc0, hc1, hf2, h23]
  ring

/--
**Ejemplo adicional (pág. 11)**:
Cálculo de ∫₀^∞ sen⁷(x) / x³ dx = 7π / 64 mediante la fórmula (4) para m = 3, n = 1:
  (π / (2⁶ · 2! · 2)) * [ (7 choose 0)·7² - (7 choose 1)·5² + (7 choose 2)·3² - (7 choose 3)·1² ] = 7π / 64
-/
theorem ejemplo_adicional_sen7_x3 :
    (Real.pi / ((2 : ℝ)^6 * (Nat.factorial 2 : ℝ) * 2)) *
      ((Nat.choose 7 0 : ℝ) * 7^2 -
       (Nat.choose 7 1 : ℝ) * 5^2 +
       (Nat.choose 7 2 : ℝ) * 3^2 -
       (Nat.choose 7 3 : ℝ) * 1^2) =
    7 * Real.pi / 64 := by
  have hc0 : (Nat.choose 7 0 : ℝ) = 1 := by exact_mod_cast (by rfl : Nat.choose 7 0 = 1)
  have hc1 : (Nat.choose 7 1 : ℝ) = 7 := by exact_mod_cast (by rfl : Nat.choose 7 1 = 7)
  have hc2 : (Nat.choose 7 2 : ℝ) = 21 := by exact_mod_cast (by rfl : Nat.choose 7 2 = 21)
  have hc3 : (Nat.choose 7 3 : ℝ) = 35 := by exact_mod_cast (by rfl : Nat.choose 7 3 = 35)
  have hf2 : (Nat.factorial 2 : ℝ) = 2 := by exact_mod_cast (by rfl : Nat.factorial 2 = 2)
  have h26 : (2 : ℝ)^6 = 64 := by norm_num
  rw [hc0, hc1, hc2, hc3, hf2, h26]
  ring

end RetosMatematicos2004
