import Mathlib

/-!
# Retos Matemáticos: Problema de los Números de Dos Dígitos

Sean `a` y `b` dígitos distintos entre sí y no nulos (`1 ≤ a, b ≤ 9` con `a ≠ b`).
Definimos el número de dos dígitos `ab₁₀ = 10 * a + b` y `N = ab₁₀ + ba₁₀`.

Se demuestra:
a) `N ≠ 198`
b) Si `5 ∣ ab₁₀` y `N` es un cuadrado perfecto, entonces `ab₁₀ = 65` (es decir, `a = 6` y `b = 5`).
-/

/-- Definición del número de dos dígitos ab₁₀ en base 10 -/
def toDigits (a b : ℕ) : ℕ := 10 * a + b

/-- Definición de N = ab₁₀ + ba₁₀ = 11(a + b) -/
def N (a b : ℕ) : ℕ := toDigits a b + toDigits b a

/-! ### Apartado a: ¿Es posible que N sea igual a 198? -/

theorem part_a (a b : ℕ)
    (ha : 1 ≤ a ∧ a ≤ 9)
    (hb : 1 ≤ b ∧ b ≤ 9)
    (hab : a ≠ b) :
    N a b ≠ 198 := by
  intro h
  -- N = 11(a + b) = 198 implica a + b = 18.
  -- Como a, b ≤ 9, necesariamente a = 9 y b = 9, contradiciendo a ≠ b.
  dsimp [N, toDigits] at h
  omega

/-! ### Apartado b: Determinar ab₁₀ si 5 ∣ ab₁₀ y N es un cuadrado perfecto -/

theorem part_b (a b : ℕ)
    (ha : 1 ≤ a ∧ a ≤ 9)
    (hb : 1 ≤ b ∧ b ≤ 9)
    (hab : a ≠ b)
    (hdiv : 5 ∣ toDigits a b)
    (hsq : ∃ k : ℕ, N a b = k ^ 2) :
    toDigits a b = 65 ∧ a = 6 ∧ b = 5 := by
  -- 1. Como 5 ∣ (10a + b) y 1 ≤ b ≤ 9, necesariamente b = 5
  obtain ⟨m, hm⟩ := hdiv
  dsimp [toDigits] at hm
  have hb_eq : b = 5 := by omega
  subst hb_eq

  -- 2. N = 11(a + 5) = k²
  obtain ⟨k, hk⟩ := hsq
  dsimp [N, toDigits] at hk

  -- 3. Acotamos k: como 1 ≤ a ≤ 9, tenemos 66 ≤ k² ≤ 154, luego 9 ≤ k ≤ 12
  have hk_ge : 9 ≤ k := by nlinarith
  have hk_le : k ≤ 12 := by nlinarith

  -- 4. Analizamos los posibles valores de k (9, 10, 11, 12); el único cuadrado múltiplo de 11 es 11² = 121
  interval_cases k <;> (dsimp [toDigits]; omega)
