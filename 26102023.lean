import Mathlib

/-!
# Reto Matemático: Capicúas en bases 7 y 4
26 de octubre de 2023
Propuesto por José Antonio Rama López.

## Enunciado:
Un número que es capicúa y tiene 5 dígitos en base 7 se descompone en producto
de dos números que son capicúas en base 4. Hállense dichos números.
-/

namespace RetosCapicua

/-! ### 1. Definiciones generales de capicúas en bases arbitrarias -/

/-- Comprueba si un número natural es capicúa (palíndromo) en base `b`. -/
def isPalindromeBase (b n : ℕ) : Bool :=
  let d := Nat.digits b n
  d == d.reverse

/-- Longitud (número de dígitos) de `n` en base `b`. -/
def digitsLen (b n : ℕ) : ℕ :=
  (Nat.digits b n).length

/-- Predicado: `n` tiene `len` dígitos y es capicúa en base `b`. -/
def isPalindromeOfLen (b len n : ℕ) : Bool :=
  isPalindromeBase b n && (digitsLen b n == len)

/-- Predicado de solución completa:
`n` es capicúa de 5 cifras en base 7, y `n = x * y` donde `x` e `y` son capicúas en base 4. -/
def isRetoSolution (n x y : ℕ) : Bool :=
  (n == x * y) &&
  isPalindromeOfLen 7 5 n &&
  isPalindromeBase 4 x &&
  isPalindromeBase 4 y


/-! ### 2. 1ª Forma: Análisis Algebraico (Factores de 2 y 4 cifras en base 4) -/

/-- Construcción de un número capicúa de 5 dígitos en base 7: ABCBA₇ -/
def n_base7 (A B C : ℕ) : ℕ :=
  A * 7^4 + B * 7^3 + C * 7^2 + B * 7 + A

/-- Construcción de un número capicúa de 2 dígitos en base 4: DD₄ -/
def d2_base4 (D : ℕ) : ℕ :=
  D * 4 + D

/-- Construcción de un número capicúa de 4 dígitos en base 4: EFFE₄ -/
def d4_base4 (E F : ℕ) : ℕ :=
  E * 4^3 + F * 4^2 + F * 4 + E

/--
Reducción de la ecuación diofántica en el caso E = 2 y C = 2A:
`ABCBA₇ = DD₄ × 2FF2₄` es equivalente a `50A + 7B = D(13 + 2F)`.
-/
lemma base7_eq_base4_case_E2 (A B D F : ℕ) :
    n_base7 A B (2 * A) = d2_base4 D * d4_base4 2 F ↔
    50 * A + 7 * B = D * (13 + 2 * F) := by
  have h1 : n_base7 A B (2 * A) = 50 * (50 * A + 7 * B) := by
    unfold n_base7
    ring
  have h2 : d2_base4 D * d4_base4 2 F = 50 * (D * (13 + 2 * F)) := by
    unfold d2_base4 d4_base4
    ring
  rw [h1, h2]
  constructor <;> intro h <;> omega

/-- La solución analítica encontrada: A=1, B=1, C=2, D=3, E=2, F=3. -/
theorem sol_analitica_eq :
    n_base7 1 1 2 = d2_base4 3 * d4_base4 2 3 := by
  rfl

theorem sol_analitica_valores :
    n_base7 1 1 2 = 2850 ∧ d2_base4 3 = 15 ∧ d4_base4 2 3 = 190 := by
  decide

/-- Validación de la solución analítica contra el predicado formal. -/
theorem sol_analitica_valida :
    isRetoSolution 2850 15 190 = true := by
  decide


/-! ### 3. 2ª Forma: Verificación de las 17 soluciones de la tabla del documento -/

/-- Lista con las 17 soluciones (n, x, y) obtenidas en la tabla de la página 2. -/
def solutionsTable : List (ℕ × ℕ × ℕ) := [
  (2850, 15, 190),     -- 11211₇ = 33₄ × 2332₄
  (4250, 10, 425),     -- 15251₇ = 22₄ × 12221₄
  (4250, 25, 170),     -- 15251₇ = 121₄ × 2222₄
  (4250, 34, 125),     -- 15251₇ = 202₄ × 1331₄
  (5700, 38, 150),     -- 22422₇ = 212₄ × 2112₄
  (6953, 17, 409),     -- 26162₇ = 101₄ × 12121₄
  (7500, 10, 750),     -- 30603₇ = 22₄ × 23232₄
  (8550, 10, 855),     -- 33633₇ = 22₄ × 31113₄
  (8802, 1, 8802),     -- 34443₇ = 1₄ × 2021202₄
  (9958, 1, 9958),     -- 41014₇ = 1₄ × 2123212₄
  (11505, 3, 3835),    -- 45354₇ = 3₄ × 323323₄
  (11505, 59, 195),    -- 45354₇ = 323₄ × 3003₄
  (12010, 2, 6005),    -- 50005₇ = 2₄ × 1131311₄
  (12206, 17, 718),    -- 50405₇ = 101₄ × 23032₄
  (13305, 15, 887),    -- 53535₇ = 33₄ × 31313₄
  (13655, 1, 13655),   -- 54545₇ = 1₄ × 3111113₄
  (14811, 1, 14811)    -- 61116₇ = 1₄ × 3213123₄
]

/-- Teorema: Las 17 descomposiciones son soluciones válidas del reto. -/
theorem all_solutions_valid :
    solutionsTable.all (fun (n, x, y) => isRetoSolution n x y) = true := by
  decide

end RetosCapicua
