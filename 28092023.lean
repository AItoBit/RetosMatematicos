import Mathlib

/-!
# Reto Matemático: Ecuación bicuadrada en bases de numeración
28 de septiembre de 2023
Propuesto por José Manuel Sánchez Muñoz.
Resuelto por Raúl Domínguez Sánchez, Francisco Javier García Capitán, Paulo González Ogando,
Antonio Roberto Martínez Fernández, Eduardo Martínez Golvano, Miguel Ángel Morales Medina
y el proponente.

## Enunciado
En un sistema de numeración cuya base se desconoce, dos números se escriben como
`302` y `402` respectivamente. El producto de ambos números es `75583` en el sistema
de numeración de base 9. Hallar la base desconocida.
-/

namespace RetosBases

/-! ### 1. Definición de los números en sus respectivas bases -/

/-- El número 302 en base b: 3b² + 2 -/
def num302 (b : ℕ) : ℕ := 3 * b ^ 2 + 2

/-- El número 402 en base b: 4b² + 2 -/
def num402 (b : ℕ) : ℕ := 4 * b ^ 2 + 2

/-- El número 75583 en base 9: 3 + 8·9 + 5·9² + 5·9³ + 7·9⁴ = 50052 -/
def targetBase9 : ℕ := 3 + 8 * 9 + 5 * 9 ^ 2 + 5 * 9 ^ 3 + 7 * 9 ^ 4

lemma target_val : targetBase9 = 50052 := by
  decide

/-- Predicado de solución: b > 4 (por contener la cifra 4) y cumple la igualdad -/
def isValidBase (b : ℕ) : Prop :=
  b > 4 ∧ num302 b * num402 b = targetBase9


/-! ### 2. 1ª Forma: Factorización de la ecuación bicuadrada -/

/--
Factorización algebraica de la ecuación bicuadrada en ℤ:
  (3b² + 2)(4b² + 2) - 50052 = 2 · (b² - 64) · (6b² + 391)
-/
lemma biquadratic_factorization (b : ℤ) :
    (3 * b ^ 2 + 2) * (4 * b ^ 2 + 2) - 50052 = 2 * (b ^ 2 - 64) * (6 * b ^ 2 + 391) := by
  ring


/-! ### 3. Teoremas Principales: Existencia y Unicidad de la Base -/

/--
**Existencia**: La base b = 8 es una solución válida.
-/
theorem reto_base_ocho_es_solucion : isValidBase 8 := by
  unfold isValidBase num302 num402 targetBase9
  decide

/--
**Unicidad**: La única base natural que satisface las condiciones del enunciado es `b = 8`.
-/
theorem reto_base_es_unicamente_ocho (b : ℕ) (hb : isValidBase b) : b = 8 := by
  rcases hb with ⟨hb_gt, hb_eq⟩
  have hb_val : num302 b * num402 b = 50052 := by
    rw [target_val] at hb_eq
    exact hb_eq

  have hb_poly : 12 * b ^ 4 + 14 * b ^ 2 + 4 = 50052 := by
    calc
      12 * b ^ 4 + 14 * b ^ 2 + 4 = num302 b * num402 b := by
        unfold num302 num402
        ring
      _ = 50052 := hb_val

  -- Acotación superior: si b ≥ 9, el polinomio supera 50052
  have h_le8 : b ≤ 8 := by
    by_contra! h
    have h_b2 : 81 ≤ b ^ 2 := by nlinarith [h]
    have h_b4 : 6561 ≤ b ^ 4 := by nlinarith [h_b2]
    linarith [hb_poly, h_b4]

  -- Comprobación exhaustiva de los posibles valores de b ∈ {5, 6, 7, 8}
  interval_cases b
  · revert hb_val; decide
  · revert hb_val; decide
  · revert hb_val; decide
  · rfl

end RetosBases
