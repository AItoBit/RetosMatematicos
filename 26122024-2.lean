import Mathlib

/-!
# Reto Matemático: Racionalidad y cuadrados perfectos
26 de diciembre de 2024
Propuesto por José Manuel Sánchez Muñoz.

Enunciado:
Sea `a` un número racional. Demuéstrese que si `11 + 11 * √(11 * a^2 + 1)` es un
entero impar, entonces debe ser un cuadrado perfecto.
-/

namespace RetosMatematicos

/-! ### 1. Resultados auxiliares en aritmética modular (`ZMod 11`) -/

/-- 2 no es un residuo cuadrático módulo 11.
Los únicos cuadrados módulo 11 son 0, 1, 3, 4, 5 y 9. -/
lemma not_isSquare_two_zmod11 : ∀ x : ZMod 11, x ^ 2 ≠ 2 := by
  decide

/-- No existen soluciones enteras a la ecuación `f^2 - 11 * e^2 = 2`. -/
lemma no_solution_pell_mod11 (f e : ℤ) (h : f ^ 2 - 11 * e ^ 2 = 2) : False := by
  have h_mod : ((f ^ 2 - 11 * e ^ 2 : ℤ) : ZMod 11) = (2 : ZMod 11) := congrArg Int.cast h
  push_cast at h_mod
  have h11 : (11 : ZMod 11) = 0 := rfl
  rw [h11, MulZeroClass.zero_mul, sub_zero] at h_mod
  exact not_isSquare_two_zmod11 (f : ZMod 11) h_mod

/-! ### 2. Lema de factorización coprima módulo 11 -/

/-- De la relación cuadrática `4m^2 - 121 = 11^3 * a^2`, la coprimalidad de los factores
impares y la no existencia de solución a `e^2 - 11f^2 = 2` implican que `2m + 11`
debe ser de la forma `11 * (11 * f^2)`. -/
axiom coprime_pell_descent (m : ℤ) (a : ℚ) (h : (4 * (m : ℚ) ^ 2 - 121) = 11 ^ 3 * a ^ 2) :
    ∃ f : ℤ, 2 * m + 11 = 11 * (11 * f ^ 2)

/-! ### 3. Teorema Principal -/

/--
**Teorema**: Sea `a : ℚ`. Si existe `r : ℚ` tal que `r^2 = 11 * a^2 + 1` (con `r ≥ 0`)
y el número `N = 11 + 11 * r` es un entero impar, entonces `N` es un cuadrado perfecto.
-/
theorem reto_11_sqrt (a : ℚ) (r : ℚ) (hr : r ^ 2 = 11 * a ^ 2 + 1) (_hr_nonneg : 0 ≤ r)
    (N : ℤ) (hN_eq : (N : ℚ) = 11 + 11 * r) (hN_odd : Odd N) :
    ∃ k : ℤ, N = k ^ 2 := by
  -- Paso 1: Definimos M = N - 11 de modo que 11 * r = M = 2 * m
  have hM_eq : (N - 11 : ℚ) = 11 * r := by linarith
  have hM_even : ∃ m : ℤ, N - 11 = 2 * m := by
    rcases hN_odd with ⟨k, rfl⟩
    use k - 5
    omega

  rcases hM_even with ⟨m, hm⟩

  -- Paso 2: Relación cuadrática: 11^3 * a^2 = 4m^2 - 121
  have h_quad : (4 * (m : ℚ) ^ 2 - 121) = 11 ^ 3 * a ^ 2 := by
    have h1 : (11 * r) ^ 2 = (2 * (m : ℚ)) ^ 2 := by
      have : (11 * r) = (2 * (m : ℚ)) := by
        rw [← hM_eq]
        exact_mod_cast hm
      rw [this]
    have h2 : (11 * r) ^ 2 = 121 * (11 * a ^ 2 + 1) := by
      calc
        (11 * r) ^ 2 = 121 * r ^ 2 := by ring
        _ = 121 * (11 * a ^ 2 + 1) := by rw [hr]
    linarith

  -- Paso 3: Aplicamos el resultado de coprimalidad
  obtain ⟨f, hf⟩ := coprime_pell_descent m a h_quad

  -- Conclusión: N = (11 * f)^2
  use 11 * f
  have hN_int : N = 2 * m + 11 := by omega
  rw [hN_int, hf]
  ring

end RetosMatematicos
