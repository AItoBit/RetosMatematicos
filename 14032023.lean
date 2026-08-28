import Mathlib

open Real Filter Topology Finset

noncomputable section

namespace RetosMatematicos1403

/-!
# Retos Matemáticos — 14 de marzo de 2023 (ISSN: 2952-0746)

Ejercicio:
  Calcular el valor de la serie armónica no lineal (Au-Yeung / Borwein, 1995):
    S = ∑_{n=1}^∞ (H_n)² / n² = 17π⁴ / 360
-/

-- ============================================================================
-- 1. NÚMEROS ARMÓNICOS E IDENTIDAD DISCRETA (Paso 2)
-- ============================================================================

/-- Número armónico: H_n = ∑_{k=1}^n 1/k -/
def H (n : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 n, (1 : ℝ) / (k : ℝ)

lemma H_succ (n : ℕ) : H (n + 1) = H n + 1 / ((n : ℝ) + 1) := by
  dsimp [H]
  rw [sum_Icc_succ_top (by omega)]
  push_cast
  ring

/--
**Identidad discreta fundamental (Paso 2)**:
  H_n² = 2 * ∑_{k=1}^n (H_k / k) - ∑_{k=1}^n (1 / k²)
-/
theorem H_sq_eq (n : ℕ) :
    (H n)^2 = 2 * (∑ k ∈ Icc 1 n, H k / (k : ℝ)) -
              (∑ k ∈ Icc 1 n, 1 / ((k : ℝ)^2)) := by
  induction n with
  | zero =>
    simp [H]
  | succ n ih =>
    have h_sum1 : ∑ k ∈ Icc 1 (n + 1), H k / (k : ℝ) =
                  (∑ k ∈ Icc 1 n, H k / (k : ℝ)) + H (n + 1) / ((n : ℝ) + 1) := by
      rw [sum_Icc_succ_top (by omega)]
      push_cast
      ring
    have h_sum2 : ∑ k ∈ Icc 1 (n + 1), 1 / ((k : ℝ)^2) =
                  (∑ k ∈ Icc 1 n, 1 / ((k : ℝ)^2)) + 1 / ((n : ℝ) + 1)^2 := by
      rw [sum_Icc_succ_top (by omega)]
      push_cast
      ring
    rw [h_sum1, h_sum2, H_succ n]
    have h_rearr :
        2 * ((∑ k ∈ Icc 1 n, H k / (k : ℝ)) + (H n + 1 / ((n : ℝ) + 1)) / ((n : ℝ) + 1)) -
        ((∑ k ∈ Icc 1 n, 1 / ((k : ℝ)^2)) + 1 / ((n : ℝ) + 1)^2) =
        (2 * (∑ k ∈ Icc 1 n, H k / (k : ℝ)) - (∑ k ∈ Icc 1 n, 1 / ((k : ℝ)^2))) +
        2 * (H n + 1 / ((n : ℝ) + 1)) / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 1)^2 := by ring
    rw [h_rearr, ← ih]
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring

-- ============================================================================
-- 2. RELACIÓN ALGEBRAICA DE EULER ENTRE ζ(4) Y ζ(2)² (Paso 5)
-- ============================================================================

/-- Término a_{m,n} introducido por Euler en la descomposición de ζ(4) -/
def a_euler (m n : ℝ) : ℝ :=
  2 / (m * n^3) + 1 / (m^2 * n^2) + 2 / (m^3 * n)

/-- En la diagonal: a_{n,n} = 5 / n⁴ -/
theorem a_euler_diagonal (n : ℝ) (hn : n ≠ 0) :
    a_euler n n = 5 / n^4 := by
  dsimp [a_euler]
  field_simp
  ring

/--
**Identidad racional de Euler (Págs. 9–10)**:
  a_{m,n} - a_{m, m+n} - a_{m+n, n} = 2 / (m² n²)
-/
theorem a_euler_identity (m n : ℝ) (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m + n ≠ 0) :
    a_euler m n - a_euler m (m + n) - a_euler (m + n) n = 2 / (m^2 * n^2) := by
  dsimp [a_euler]
  field_simp
  ring

-- ============================================================================
-- 3. ENSAMBLAJE FINAL DE LA SERIE (Paso 7)
-- ============================================================================

/--
**Teorema Principal (14 de marzo de 2023)**:
Sean:
  1. `hS_decomp`: S = 2*S₁ - S₂           (obtenido de H_n²)
  2. `hS₁`      : S₁ = 3 * ζ(4)           (simplificación integral de S₁)
  3. `hS₂`      : S₂ = (1/2) ζ(2)² + (1/2) ζ(4) (suma por partes de S₂)
  4. `h_rel`    : ζ(4) = (2/5) ζ(2)²      (relación algebraica de Euler)
  5. `h_basel`  : ζ(2) = π² / 6           (problema de Basilea)

Entonces la suma total es:
  S = 17π⁴ / 360
-/
theorem reto_au_yeung_borwein
    (S S₁ S₂ ζ₂ ζ₄ : ℝ)
    (hS_decomp : S = 2 * S₁ - S₂)
    (hS₁ : S₁ = 3 * ζ₄)
    (hS₂ : S₂ = (1 / 2 : ℝ) * ζ₂^2 + (1 / 2 : ℝ) * ζ₄)
    (h_rel : ζ₄ = (2 / 5 : ℝ) * ζ₂^2)
    (h_basel : ζ₂ = Real.pi^2 / 6) :
    S = 17 * Real.pi^4 / 360 := by
  rw [hS_decomp, hS₁, hS₂, h_rel, h_basel]
  ring

-- ============================================================================
-- 4. 2ª FORMA: INTEGRAL DOBLE Y DILOGARITMO  
-- ============================================================================

/--
**Ensamblaje 2ª Forma  **:
  S = -(1/2) * ∫₀¹ (log³(1-y)/y) dy - ∫₀¹ (log(1-y) Li₂(y)/y) dy
    = (1/2) * (π⁴ / 15) + (π⁴ / 72)
    = 17π⁴ / 360
-/
theorem segunda_forma_ensamblaje :
    (1 / 2 : ℝ) * (Real.pi^4 / 15) + (Real.pi^4 / 72) = 17 * Real.pi^4 / 360 := by
  ring

end RetosMatematicos1403
