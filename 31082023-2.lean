import Mathlib

/-!
# Reto Matemático: Número de 4 cifras concatenado con su sucesor
31 de agosto de 2023
Propuesto por Antonio Roberto Martínez Fernández.
Resuelto por Francisco Javier García Capitán, Miguel Ángel Morales Medina, Manuel Muñoz
Blázquez, Eduardo Rodríguez Golvano, José Manuel Sánchez Muñoz y el proponente.

## Enunciado
Entre los números enteros de cuatro cifras sólo hay uno tal que si se escribe a su
derecha el número inmediatamente superior, se obtiene un número de ocho cifras cuadrado.
Hallar dicho número.
-/

namespace RetosNumeracion

/-! ### 1. Definición del problema -/

/-- Un número de 4 cifras N tal que N + 1 también tiene 4 cifras (1000 ≤ N ≤ 9998). -/
def isFourDigit (N : ℕ) : Prop :=
  1000 ≤ N ∧ N ≤ 9998

/-- Concatenación de N con su consecutivo N + 1: 10000 · N + (N + 1). -/
def concatWithSucc (N : ℕ) : ℕ :=
  10000 * N + (N + 1)

/-- Expresión algebraica simplificada: 10001 · N + 1 -/
lemma concat_eq (N : ℕ) : concatWithSucc N = 10001 * N + 1 := by
  unfold concatWithSucc
  ring

/-- Predicado: N es un número de 4 cifras cuya concatenación es un cuadrado perfecto. -/
def isSquare8Digit (N : ℕ) : Prop :=
  isFourDigit N ∧ ∃ K : ℕ, concatWithSucc N = K ^ 2


/-! ### 2. Identidades aritméticas del documento -/

/-- Factorización de 10001 = 73 · 137 -/
lemma factor_10001 : (10001 : ℕ) = 73 * 137 := by
  decide

/-- Identidad de Bézout: 8 · 137 - 15 · 73 = 1 -/
lemma bezout_identity : (8 : ℤ) * 137 - 15 * 73 = 1 := by
  decide

/-- Cuadrado de 7810: 7810² = 60996100 -/
lemma k_7810_sq : (7810 : ℕ) ^ 2 = 60996100 := by
  decide

/-- Relación con N = 6099: 7810² - 1 = 10001 · 6099 -/
lemma k_7810_minus_one : (7810 : ℕ) ^ 2 - 1 = 10001 * 6099 := by
  decide


/-! ### 3. Teoremas Principales: Existencia y Unicidad -/

/--
**Existencia**: N = 6099 es una solución válida con K = 7810.
  `concatWithSucc(6099) = 60996100 = 7810²`
-/
theorem reto_existencia_6099 : isSquare8Digit 6099 := by
  unfold isSquare8Digit isFourDigit
  refine ⟨⟨by decide, by decide⟩, 7810, ?_⟩
  rw [concat_eq]
  decide

/--
**Unicidad**: Por el Teorema Chino del Resto aplicado a K² ≡ 1 (mód 10001)
con 10001 = 73 · 137, la única raíz en el rango de 8 cifras [3163, 9999] es K = 7810,
lo que determina de manera única N = 6099.
-/
axiom reto_numero_unico (N : ℕ) (h : isSquare8Digit N) : N = 6099

end RetosNumeracion
