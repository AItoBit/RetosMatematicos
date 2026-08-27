import Mathlib

/-!
# Un sistema de ecuaciones con radicales

Ejercicio (examen de 1827 del St. John's College de Cambridge; véase Rotherham, 1852, p. 40):

Resuélvase el sistema
```
x + √(3y² + 2x − 11) = 7 + 2y − y²
√(3y − x + 7)        = (x + y)/(x − y)
```

Las únicas soluciones reales son `(x, y) = (6, 0)` y `(x, y) = (4, 2)`.

Como en Lean `Real.sqrt` está definida también para argumentos negativos (con valor `0`),
en la formalización se pide explícitamente que los radicandos sean no negativos y que el
denominador `x − y` no se anule, que es lo que el enunciado presupone.
-/

namespace RetosMatematicos

open Real

/-- El sistema de ecuaciones del enunciado, con las condiciones de existencia implícitas:
los radicandos son no negativos y el denominador no se anula. -/
def Sistema (x y : ℝ) : Prop :=
  0 ≤ 3 * y ^ 2 + 2 * x - 11 ∧
  0 ≤ 3 * y - x + 7 ∧
  x ≠ y ∧
  x + Real.sqrt (3 * y ^ 2 + 2 * x - 11) = 7 + 2 * y - y ^ 2 ∧
  Real.sqrt (3 * y - x + 7) = (x + y) / (x - y)

/-- De la primera ecuación se deduce, elevando al cuadrado, la factorización
`(x − (6 + y − y²))·(x − (10 + 3y − y²)) = 0`. -/
lemma factorizacion {x y : ℝ} (h1 : 0 ≤ 3 * y ^ 2 + 2 * x - 11)
    (heq : x + Real.sqrt (3 * y ^ 2 + 2 * x - 11) = 7 + 2 * y - y ^ 2) :
    (x - (6 + y - y ^ 2)) * (x - (10 + 3 * y - y ^ 2)) = 0 := by
  have hs : Real.sqrt (3 * y ^ 2 + 2 * x - 11) = 7 + 2 * y - y ^ 2 - x := by linarith
  have hsq : 3 * y ^ 2 + 2 * x - 11 = (7 + 2 * y - y ^ 2 - x) ^ 2 := by
    rw [← hs, Real.sq_sqrt h1]
  nlinarith [hsq]

/-- La rama `x = 6 + y − y²` obliga a `y ≥ −1`. -/
lemma rama1_signo {x y : ℝ} (hx : x = 6 + y - y ^ 2)
    (heq : x + Real.sqrt (3 * y ^ 2 + 2 * x - 11) = 7 + 2 * y - y ^ 2) :
    -1 ≤ y := by
  have h := Real.sqrt_nonneg (3 * y ^ 2 + 2 * x - 11)
  nlinarith [h]

/-- La rama `x = 10 + 3y − y²` obliga a `y ≤ −3`. -/
lemma rama2_signo {x y : ℝ} (hx : x = 10 + 3 * y - y ^ 2)
    (heq : x + Real.sqrt (3 * y ^ 2 + 2 * x - 11) = 7 + 2 * y - y ^ 2) :
    y ≤ -3 := by
  have h := Real.sqrt_nonneg (3 * y ^ 2 + 2 * x - 11)
  nlinarith [h]

/-- En la rama `x = 6 + y − y²` (con `y ≥ −1`) la segunda ecuación da `y = 0` o `y = 2`. -/
lemma rama1_solucion {x y : ℝ} (hx : x = 6 + y - y ^ 2) (hy : -1 ≤ y) (hxy : x ≠ y)
    (heq2 : Real.sqrt (3 * y - x + 7) = (x + y) / (x - y)) :
    (x = 6 ∧ y = 0) ∨ (x = 4 ∧ y = 2) := by
  have hden : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hrad : 3 * y - x + 7 = (y + 1) ^ 2 := by rw [hx]; ring
  have hsqrt : Real.sqrt (3 * y - x + 7) = y + 1 := by
    rw [hrad, Real.sqrt_sq (by linarith)]
  rw [hsqrt] at heq2
  have key : (y + 1) * (x - y) = x + y := by
    field_simp at heq2; linarith [heq2]
  -- sustituyendo `x` queda `y * (4 - y²) = 0`
  have hfac : y * (y - 2) * (y + 2) = 0 := by nlinarith [key, hx]
  rcases mul_eq_zero.mp hfac with h | h
  · rcases mul_eq_zero.mp h with h | h
    · left; constructor
      · rw [hx, h]; ring
      · exact h
    · right
      have hy2 : y = 2 := by linarith
      constructor
      · rw [hx, hy2]; ring
      · exact hy2
  · exfalso; linarith

/-- En la rama `x = 10 + 3y − y²` (con `y ≤ −3`) la segunda ecuación es imposible. -/
lemma rama2_imposible {x y : ℝ} (hx : x = 10 + 3 * y - y ^ 2) (hy : y ≤ -3)
    (heq2 : Real.sqrt (3 * y - x + 7) = (x + y) / (x - y)) : False := by
  have hrad : 3 * y - x + 7 = y ^ 2 - 3 := by rw [hx]; ring
  have hy2 : 6 ≤ y ^ 2 - 3 := by nlinarith
  -- la raíz es mayor que 11/5
  have hlow : (11 : ℝ) / 5 < Real.sqrt (3 * y - x + 7) := by
    rw [hrad]
    have : ((11 : ℝ) / 5) ^ 2 < y ^ 2 - 3 := by nlinarith
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ y ^ 2 - 3 by linarith),
      Real.sqrt_nonneg (y ^ 2 - 3)]
  -- el miembro derecho es a lo sumo 11/5
  have hdenpos : x - y < 0 := by nlinarith
  have hup : (x + y) / (x - y) ≤ 11 / 5 := by
    rw [div_le_iff_of_neg hdenpos]
    nlinarith
  linarith [heq2 ▸ hlow]

/-- **Solución del sistema.** Los únicos pares de números reales que satisfacen
`x + √(3y² + 2x − 11) = 7 + 2y − y²` y `√(3y − x + 7) = (x + y)/(x − y)`
son `(6, 0)` y `(4, 2)`. -/
theorem sistema_iff (x y : ℝ) :
    Sistema x y ↔ (x = 6 ∧ y = 0) ∨ (x = 4 ∧ y = 2) := by
  constructor
  · rintro ⟨h1, _h2, hxy, heq1, heq2⟩
    rcases mul_eq_zero.mp (factorizacion h1 heq1) with h | h
    · have hx : x = 6 + y - y ^ 2 := by linarith [sub_eq_zero.mp h]
      exact rama1_solucion hx (rama1_signo hx heq1) hxy heq2
    · have hx : x = 10 + 3 * y - y ^ 2 := by linarith [sub_eq_zero.mp h]
      exact (rama2_imposible hx (rama2_signo hx heq1) heq2).elim
  · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩) <;> subst hx <;> subst hy <;>
      refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
    · rw [show (3 : ℝ) * 0 ^ 2 + 2 * 6 - 11 = 1 by norm_num, Real.sqrt_one]; norm_num
    · rw [show (3 : ℝ) * 0 - 6 + 7 = 1 by norm_num, Real.sqrt_one]; norm_num
    · rw [show (3 : ℝ) * 2 ^ 2 + 2 * 4 - 11 = 3 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]; norm_num
    · rw [show (3 : ℝ) * 2 - 4 + 7 = 3 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]; norm_num

end RetosMatematicos
