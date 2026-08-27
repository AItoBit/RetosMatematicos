import Mathlib

/-!
# Reto Matemático: Infinitas soluciones enteras de x³ + y³ + z³ = x² + y² + z²
13 de noviembre de 2023
Propuesto por José Antonio Prado Bassas.
Resuelto por Ignacio Larrosa Cañestro, Manuel Muñoz Blázquez, Antonio Roberto Martínez
Fernández, Eduardo Rodríguez Golvano, Andrés Solano Sola y Pablo Vitoria García.

## Enunciado
Demuéstrese que la ecuación `x³ + y³ + z³ = x² + y² + z²` tiene infinitas soluciones enteras.
-/

namespace RetosCubosCuadrados

/-! ### 1. Definición de la ecuación diofántica -/

/-- Predicado: La terna (x, y, z) de números enteros es solución de la ecuación. -/
def isSolution (x y z : ℤ) : Prop :=
  x ^ 3 + y ^ 3 + z ^ 3 = x ^ 2 + y ^ 2 + z ^ 2

/-- Versión booleana computable para verificar soluciones concretas. -/
def checkSolution (x y z : ℤ) : Bool :=
  (x ^ 3 + y ^ 3 + z ^ 3) == (x ^ 2 + y ^ 2 + z ^ 2)


/-! ### 2. 1ª Forma: Familia paramétrica infinita con z = -y -/

/-- Primera familia infinita de soluciones parametrizada por t ∈ ℤ:
  x(t) = 2t² + 1
  y(t) = t(2t² + 1)
  z(t) = -t(2t² + 1)
-/
def sol1 (t : ℤ) : ℤ × ℤ × ℤ :=
  (2 * t ^ 2 + 1, t * (2 * t ^ 2 + 1), - (t * (2 * t ^ 2 + 1)))

/--
Teorema: Toda terna de la familia sol1(t) satisface exactamente la ecuación
para cualquier número entero t.
-/
theorem sol1_is_solution (t : ℤ) :
    let (x, y, z) := sol1 t
    isSolution x y z := by
  unfold isSolution sol1
  ring


/-! ### 3. Verificación formal de ejemplos de la Tabla 1 del documento -/

theorem table_sol_000 : checkSolution 0 0 0 = true := by decide
theorem table_sol_001 : checkSolution 0 0 1 = true := by decide
theorem table_sol_011 : checkSolution 0 1 1 = true := by decide
theorem table_sol_111 : checkSolution 1 1 1 = true := by decide
theorem table_sol_neg1_neg1_2 : checkSolution (-1) (-1) 2 = true := by decide
theorem table_sol_neg3_neg2_4 : checkSolution (-3) (-2) 4 = true := by decide
theorem table_sol_neg11_neg8_13 : checkSolution (-11) (-8) 13 = true := by decide
theorem table_sol_neg29_neg15_31 : checkSolution (-29) (-15) 31 = true := by decide
theorem table_sol_neg59_neg24_61 : checkSolution (-59) (-24) 61 = true := by decide
theorem table_sol_neg104_neg35_106 : checkSolution (-104) (-35) 106 = true := by decide


/-! ### 4. Teorema Principal: Existencia de infinitas soluciones enteras -/

/--
**Teorema**: La ecuación diofántica `x³ + y³ + z³ = x² + y² + z²` posee infinitas
soluciones enteras distintas.
-/
theorem reto_infinitas_soluciones_enteras :
    ∃ f : ℕ → ℤ × ℤ × ℤ, Function.Injective f ∧ ∀ n,
      let (x, y, z) := f n
      isSolution x y z := by
  -- Usamos la familia paramétrica sol1 restringida a los números naturales
  use (fun n => sol1 (n : ℤ))
  constructor
  · -- Demostramos que la función es inyectiva: si sol1(a) = sol1(b), entonces a = b
    intro a b hab
    unfold sol1 at hab
    injection hab with hx _
    have h_sq : (a : ℤ) ^ 2 = (b : ℤ) ^ 2 := by linarith [hx]
    have h_nonneg_a : 0 ≤ (a : ℤ) := by positivity
    have h_nonneg_b : 0 ≤ (b : ℤ) := by positivity
    have h_eq_int : (a : ℤ) = (b : ℤ) := by nlinarith [h_sq, h_nonneg_a, h_nonneg_b]
    exact Int.ofNat_inj.mp h_eq_int
  · -- Demostramos que cada elemento de la sucesión es una solución válida
    intro n
    exact sol1_is_solution (n : ℤ)

end RetosCubosCuadrados
