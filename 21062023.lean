import Mathlib

/-!
# Reto Matemático: Divisibilidad polinómica y enteros consecutivos
21 de junio de 2023
Propuesto por José Manuel Sánchez Muñoz.

## Enunciado
Sea `n` un número entero. Demuéstrese que el número `n⁵ - 5n³ + 4n` es divisible por 120,
y que si `n` es par, entonces el número `n³ - 4n` es siempre divisible por 48.
-/

namespace RetosDivisibilidad

/-! ### 1. Definición de los polinomios del reto -/

/-- Polinomio principal de grado 5: p(n) = n⁵ - 5n³ + 4n -/
def p (n : ℤ) : ℤ := n ^ 5 - 5 * n ^ 3 + 4 * n

/-- Polinomio secundario de grado 3: q(n) = n³ - 4n -/
def q (n : ℤ) : ℤ := n ^ 3 - 4 * n


/-! ### 2. 1ª Forma: Factorización en factores consecutivos -/

/--
Factorización de p(n) como producto de 5 enteros consecutivos:
  p(n) = (n - 2)(n - 1)n(n + 1)(n + 2)
-/
lemma p_factorization (n : ℤ) :
    p n = (n - 2) * (n - 1) * n * (n + 1) * (n + 2) := by
  unfold p
  ring

/--
Factorización de q(n):
  q(n) = (n - 2)n(n + 2)
-/
lemma q_factorization (n : ℤ) :
    q n = (n - 2) * n * (n + 2) := by
  unfold q
  ring

/--
Si n = 2m es par, q(2m) = 8m³ - 8m = 8(m - 1)m(m + 1).
-/
lemma q_even_factorization (m : ℤ) :
    q (2 * m) = 8 * ((m - 1) * m * (m + 1)) := by
  unfold q
  ring


/-! ### 3. 2ª Forma: Sucesión de diferencias finitas -/

def p5 (n : ℤ) : ℤ := n ^ 5 - 5 * n ^ 3 + 4 * n
def p4 (n : ℤ) : ℤ := 5 * (n ^ 4 + 2 * n ^ 3 - n ^ 2 - 2 * n)
def p3 (n : ℤ) : ℤ := 20 * (n ^ 3 + 3 * n ^ 2 + 2 * n)
def p2 (n : ℤ) : ℤ := 60 * (n ^ 2 + 3 * n + 2)
def p1 (n : ℤ) : ℤ := 120 * (n + 2)

lemma diff_p5 (n : ℤ) : p5 (n + 1) - p5 n = p4 n := by unfold p5 p4; ring
lemma diff_p4 (n : ℤ) : p4 (n + 1) - p4 n = p3 n := by unfold p4 p3; ring
lemma diff_p3 (n : ℤ) : p3 (n + 1) - p3 n = p2 n := by unfold p3 p2; ring
lemma diff_p2 (n : ℤ) : p2 (n + 1) - p2 n = p1 n := by unfold p2 p1; ring

/-- La diferencia de orden 4 es un múltiplo evidente de 120 para todo n. -/
lemma p1_dvd_120 (n : ℤ) : 120 ∣ p1 n := by
  use (n + 2)
  unfold p1
  ring


/-! ### 4. Resultados auxiliares en aritmética modular (`ZMod 120` y `ZMod 48`) -/

-- Aumentamos el límite de profundidad de recursión para la comprobación exhaustiva
set_option maxRecDepth 200000

/-- Identidad polinómica en ZMod 120 evaluable exhaustivamente por el kernel. -/
lemma poly_zmod120 : ∀ x : ZMod 120, x ^ 5 - 5 * x ^ 3 + 4 * x = 0 := by
  decide

/-- Identidad polinómica en ZMod 48 evaluable exhaustivamente por el kernel. -/
lemma poly_even_zmod48 : ∀ m : ZMod 48, 8 * m ^ 3 - 8 * m = 0 := by
  decide


/-! ### 5. Teoremas Principales -/

/--
**Parte 1**: Para todo número entero `n`, el número `n⁵ - 5n³ + 4n` es divisible por 120.
-/
theorem reto_parte1_dvd_120 (n : ℤ) : 120 ∣ (n ^ 5 - 5 * n ^ 3 + 4 * n) := by
  have h_zmod : (((n ^ 5 - 5 * n ^ 3 + 4 * n : ℤ) : ZMod 120)) = 0 := by
    push_cast
    exact poly_zmod120 (n : ZMod 120)
  exact (CharP.intCast_eq_zero_iff (ZMod 120) 120 (n ^ 5 - 5 * n ^ 3 + 4 * n)).mp h_zmod

/--
**Parte 2**: Si `n` es un número entero par, entonces `n³ - 4n` es divisible por 48.
-/
theorem reto_parte2_dvd_48_of_even (n : ℤ) (hn : Even n) : 48 ∣ (n ^ 3 - 4 * n) := by
  rcases hn with ⟨m, rfl⟩
  have h_id : (m + m) ^ 3 - 4 * (m + m) = 8 * m ^ 3 - 8 * m := by ring
  rw [h_id]
  have h_zmod : (((8 * m ^ 3 - 8 * m : ℤ) : ZMod 48)) = 0 := by
    push_cast
    exact poly_even_zmod48 (m : ZMod 48)
  exact (CharP.intCast_eq_zero_iff (ZMod 48) 48 (8 * m ^ 3 - 8 * m)).mp h_zmod

end RetosDivisibilidad
