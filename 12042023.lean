import Mathlib

/-!
# Reto Matemático: Suma de cubos consecutivos y cubos perfectos
12 de abril de 2023
Propuesto por José Manuel Sánchez Muñoz.
Resuelto por Pedro José Rosa González y el proponente.

## Enunciado
Encuéntrense `n` números naturales consecutivos tales que la suma de sus cubos
resulte también un cubo, y que `n` sea a su vez un cubo.
-/

namespace RetosCubos

open Finset

/-! ### 1. Definición de la suma de cubos consecutivos -/

/-- Suma de los cubos de `n` números consecutivos a partir de `x` (es decir, x³ + ... + (x + n - 1)³). -/
def sumConsecutiveCubes (x n : ℕ) : ℕ :=
  ∑ i ∈ range n, (x + i) ^ 3

/--
Fórmula cerrada de la suma de cubos según el teorema de Nicómaco (para x ≥ 1):
  S(x, n) = [(x + n - 1)(x + n) / 2]² - [(x - 1)x / 2]²
-/
def nicomachusDiff (x n : ℕ) : ℕ :=
  ((x + n - 1) * (x + n) / 2) ^ 2 - ((x - 1) * x / 2) ^ 2

/-- Predicado de solución del reto:
`n` números consecutivos a partir de `x` cuya suma de cubos es un cubo `a³`, y `n = t³`. -/
def isCubesSolution (x n a t : ℕ) : Prop :=
  0 < x ∧ 0 < n ∧ n = t ^ 3 ∧ sumConsecutiveCubes x n = a ^ 3


/-! ### 2. 1ª Forma: Familia paramétrica algebraica -/

/-- Fórmula paramétrica de Euler/Matteson para el término inicial:
  x(t) = (t⁴ - 3t³ - 2t² + 4) / 6
-/
def x_param (t : ℚ) : ℚ :=
  (t ^ 4 - 3 * t ^ 3 - 2 * t ^ 2 + 4) / 6

/-- Para t = 4, obtenemos x = 6 y n = 4³ = 64. -/
theorem param_t4 : x_param 4 = 6 := by
  norm_num [x_param]

/-- Para t = 4, la suma de los 64 cubos desde x = 6 es exactamente 180³. -/
theorem param_t4_is_cube :
    nicomachusDiff 6 64 = 180 ^ 3 := by
  decide


/-! ### 3. 2ª Forma: Verificación de las 8 soluciones encontradas en la tabla -/

/-- Predicado booleano computable para verificar las soluciones (p, x, m) donde n = p³:
La suma de n cubos a partir de (x + 1) es igual a m³. -/
def isTableSolution (p x m : ℕ) : Bool :=
  let n := p ^ 3
  let sumCubes := ((x + n) * (x + n + 1) / 2) ^ 2 - (x * (x + 1) / 2) ^ 2
  m ^ 3 == sumCubes

/-- Solución 1: p = 4, x = 5 (secuencia desde 6), n = 64, m = 180 -/
theorem sol_p04 : isTableSolution 4 5 180 = true := by decide

/-- Solución 2: p = 5, x = 33, n = 125, m = 540 -/
theorem sol_p05 : isTableSolution 5 33 540 = true := by decide

/-- Solución 3: p = 7, x = 212, n = 343, m = 2856 -/
theorem sol_p07 : isTableSolution 7 212 2856 = true := by decide

/-- Solución 4: p = 8, x = 405, n = 512, m = 5544 -/
theorem sol_p08 : isTableSolution 8 405 5544 = true := by decide

/-- Solución 5: p = 10, x = 1133, n = 1000, m = 16830 -/
theorem sol_p10 : isTableSolution 10 1133 16830 = true := by decide

/-- Solución 6: p = 11, x = 1734, n = 1331, m = 27060 -/
theorem sol_p11 : isTableSolution 11 1734 27060 = true := by decide

/-- Solución 7: p = 13, x = 3605, n = 2197, m = 62244 -/
theorem sol_p13 : isTableSolution 13 3605 62244 = true := by decide

/-- Solución 8: p = 14, x = 4965, n = 2744, m = 90090 -/
theorem sol_p14 : isTableSolution 14 4965 90090 = true := by decide

/-- Lista de las 8 soluciones tabuladas en las páginas 3 y 4. -/
def solutionsList : List (ℕ × ℕ × ℕ) := [
  (4, 5, 180),
  (5, 33, 540),
  (7, 212, 2856),
  (8, 405, 5544),
  (10, 1133, 16830),
  (11, 1734, 27060),
  (13, 3605, 62244),
  (14, 4965, 90090)
]

/-- Teorema: Las 8 tuplas (p, x, m) de la tabla son soluciones válidas del reto. -/
theorem all_table_solutions_valid :
    solutionsList.all (fun (p, x, m) => isTableSolution p x m) = true := by
  decide


/-! ### 4. Teorema Principal de Existencia -/

/--
**Teorema**: Existen `n` números naturales consecutivos tales que la suma de sus
cubos es un cubo, y `n` es a su vez un cubo perfecto.
-/
theorem reto_cubos_consecutivos_existencia :
    ∃ (x n : ℕ), (∃ t : ℕ, n = t ^ 3) ∧ (∃ a : ℕ, sumConsecutiveCubes x n = a ^ 3) := by
  -- Usamos la primera solución: x = 6, n = 64 = 4³, suma = 180³
  use 6, 64
  constructor
  · -- n = 64 es un cubo perfecto (4³)
    use 4
    rfl
  · -- La suma de los 64 cubos desde 6 es 180³ = 5832000
    use 180
    decide

end RetosCubos
