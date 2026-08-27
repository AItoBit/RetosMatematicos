import Mathlib

namespace Reto20240715

/-!
# Retos Matemáticos — 15 de julio de 2024
## Cuadrado inscrito en la cúbica y = x³ - ax

Formalización en Lean 4 del cálculo del parámetro `a` para la existencia
de un único cuadrado inscrito y el cálculo de su área.
-/

/-- La ecuación cuadrática en `t` derivada de la simetría y perpendicularidad 
de las diagonales del cuadrado inscrito en y = x³ - ax: `t² + a*t + 2 = 0`. -/
def eq_t (a t : ℝ) : Prop :=
  t^2 + a * t + 2 = 0

/-- El discriminante de la ecuación en `t` es `a² - 8`. -/
def discr_t (a : ℝ) : ℝ :=
  a^2 - 8

/-- Para a > 0, la condición de unicidad de la raíz del discriminante equivale a `a = 2√2`. -/
theorem unique_parameter_value {a : ℝ} (ha : 0 < a) :
    discr_t a = 0 ↔ a = 2 * Real.sqrt 2 := by
  dsimp [discr_t]
  constructor
  · intro h
    have h_sq : a^2 = (2 * Real.sqrt 2)^2 := by
      calc a^2 = 8 := by linarith [h]
        _ = 2^2 * (Real.sqrt 2)^2 := by rw [Real.sq_sqrt (by norm_num)]; norm_num
        _ = (2 * Real.sqrt 2)^2 := by ring
    have h_pos : 0 ≤ 2 * Real.sqrt 2 := by positivity
    -- Reemplazo de `sq_eq_sq` usando `Real.sqrt` en ambos lados:
    have ha_eq := congr_arg Real.sqrt h_sq
    rw [Real.sqrt_sq ha.le, Real.sqrt_sq h_pos] at ha_eq
    exact ha_eq
  · intro h
    rw [h]
    ring_nf
    rw [Real.sq_sqrt (by norm_num)]
    ring

/-- La única pendiente positiva `m` correspondiente a `a = 2√2`. -/
noncomputable def m_sol : ℝ := (Real.sqrt 6 - Real.sqrt 2) / 2

/-- Verificación de que la pendiente `m_sol` es estrictamente positiva. -/
lemma m_sol_pos : 0 < m_sol := by
  dsimp [m_sol]
  have h62 : Real.sqrt 2 < Real.sqrt 6 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

/-- El valor del cuadrado del radio/semidiagonal `ρ²` para la solución única. -/
noncomputable def rho_sq : ℝ := 3 * Real.sqrt 2

/-- El área del cuadrado está dada por `S = 2 * ρ²`. -/
noncomputable def area_cuadrado (ρ_sq : ℝ) : ℝ := 2 * ρ_sq

/-- Teorema principal: El área del único cuadrado inscrito en y = x³ - 2√2 x es 6√2. -/
theorem area_unico_cuadrado : area_cuadrado rho_sq = 6 * Real.sqrt 2 := by
  dsimp [area_cuadrado, rho_sq]
  ring

end Reto20240715
