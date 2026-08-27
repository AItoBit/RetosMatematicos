import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
# Contraste de hipótesis sobre la ganancia de peso de ratas de laboratorio

Se sabe que las ratas criadas en un determinado laboratorio ganan, en promedio, 60 g en los
tres primeros meses de vida. Se alimentan `n = 10` ratas recién nacidas con la dieta A y se
observan las ganancias de peso (en g) `50, 55, 62, 60, 59, 62, 54, 48, 58, 61`. Suponiendo
que la ganancia en peso se distribuye normalmente:

* a) ¿Puede afirmarse, con `α = 0,05`, que dicha dieta modifica el promedio de la ganancia
  de peso?
* b) Contrástese, con `α = 0,05`, si la varianza es superior a 12.

Aquí se formaliza la parte matemáticamente verificable del ejercicio: el cálculo de la media
muestral, de la cuasivarianza muestral y de los dos estadísticos de contraste, junto con su
posición respecto de las correspondientes regiones de rechazo. Los cuantiles
`t_{9;0,975} = 2,262` y `χ²_{9;0,95} = 16,919` se toman de las tablas, como en el enunciado.

Resultados: `x̄ = 56,9`, `S² = 2229/90 ≈ 24,7667`, `t₀ = -93/√2229 ≈ -1,968` (no cae en la
región de rechazo, luego no se rechaza `H₀ : μ = 60`) y `V = 18,575` (sí cae en la región de
rechazo `[16,919, +∞)`, luego se rechaza `H₀ : σ² = 12` frente a `H₁ : σ² > 12`).
-/

namespace RatasDietaA

/-- Las diez ganancias de peso observadas (en gramos). -/
def data : Fin 10 → ℝ := ![50, 55, 62, 60, 59, 62, 54, 48, 58, 61]

/-- Media muestral `x̄ = (∑ xᵢ)/n`. -/
noncomputable def sampleMean {n : ℕ} (x : Fin n → ℝ) : ℝ := (∑ i, x i) / n

/-- Cuasivarianza muestral `S² = (∑ (xᵢ - x̄)²)/(n-1)`. -/
noncomputable def sampleVar {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  (∑ i, (x i - sampleMean x) ^ 2) / ((n : ℝ) - 1)

/-- Estadístico `T = (x̄ - μ₀)/(S/√n)` del contraste sobre la media con varianza desconocida
(bajo `H₀` sigue una distribución `t` de Student con `n - 1` grados de libertad). -/
noncomputable def tStat {n : ℕ} (x : Fin n → ℝ) (mu0 : ℝ) : ℝ :=
  (sampleMean x - mu0) / (Real.sqrt (sampleVar x) / Real.sqrt n)

/-- Estadístico `V = (n-1)S²/σ₀²` del contraste sobre la varianza (bajo `H₀` sigue una
distribución `χ²` con `n - 1` grados de libertad). -/
noncomputable def chiStat {n : ℕ} (x : Fin n → ℝ) (sigma0sq : ℝ) : ℝ :=
  ((n : ℝ) - 1) * sampleVar x / sigma0sq

/-- Suma de los datos: `∑ xᵢ = 569`. -/
theorem sum_data : ∑ i, data i = 569 := by
  simp [data, Fin.sum_univ_succ]
  norm_num

/-- La media muestral vale `x̄ = 56,9`. -/
theorem sampleMean_data : sampleMean data = 56.9 := by
  rw [sampleMean, sum_data]
  norm_num

/-- La cuasivarianza muestral vale `S² = 2229/90 ≈ 24,7667`. -/
theorem sampleVar_data : sampleVar data = 2229 / 90 := by
  rw [sampleVar, sampleMean_data]
  simp [data, Fin.sum_univ_succ]
  norm_num

/-- Cotas elementales para `√2229`, usadas para acotar el estadístico `t₀`. -/
theorem sqrt2229_bounds : (47.21 : ℝ) < Real.sqrt 2229 ∧ Real.sqrt 2229 < 47.22 := by
  constructor
  · rw [show (47.21 : ℝ) = Real.sqrt (47.21 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by positivity) (by norm_num)
  · rw [show (47.22 : ℝ) = Real.sqrt (47.22 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- El estadístico del contraste sobre la media es exactamente `t₀ = -93/√2229`. -/
theorem tStat_data : tStat data 60 = -93 / Real.sqrt 2229 := by
  have h900 : Real.sqrt 900 = 30 := by
    rw [show (900 : ℝ) = 30 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hs : Real.sqrt (2229 / 90) / Real.sqrt 10 = Real.sqrt 2229 / 30 := by
    rw [← Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2229 / 90)]
    rw [show (2229 / 90 / 10 : ℝ) = 2229 / 900 by norm_num]
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2229), h900]
  rw [tStat, sampleMean_data, sampleVar_data, show ((10 : ℕ) : ℝ) = (10 : ℝ) by norm_num, hs,
    div_div_eq_mul_div]
  norm_num

/-- Aproximación numérica del estadístico: `t₀ ≈ -1,968`. -/
theorem tStat_approx : -1.97 < tStat data 60 ∧ tStat data 60 < -1.96 := by
  obtain ⟨h1, h2⟩ := sqrt2229_bounds
  have hpos : (0 : ℝ) < Real.sqrt 2229 := by linarith
  rw [tStat_data]
  refine ⟨?_, ?_⟩
  · rw [lt_div_iff₀ hpos]; linarith
  · rw [div_lt_iff₀ hpos]; linarith

/-- **Apartado a).** El estadístico no cae en la región de rechazo
`R = (-∞, -2,262] ∪ [2,262, +∞)`, es decir `|t₀| < t_{9;0,975} = 2,262`: no se rechaza
`H₀ : μ = 60` al nivel `α = 0,05`, luego la dieta A no modifica el promedio de la ganancia
de peso. -/
theorem tStat_not_in_rejection_region : |tStat data 60| < 2.262 := by
  obtain ⟨h1, h2⟩ := tStat_approx
  rw [abs_lt]
  exact ⟨by linarith, by linarith⟩

/-- El estadístico del contraste sobre la varianza es `V = 2229/120 = 18,575`. -/
theorem chiStat_data : chiStat data 12 = 18.575 := by
  rw [chiStat, sampleVar_data]
  norm_num

/-- **Apartado b).** El estadístico cae en la región de rechazo
`R = [χ²_{9;0,95}, +∞) = [16,919, +∞)`: se rechaza `H₀ : σ² = 12` frente a `H₁ : σ² > 12`
al nivel `α = 0,05`, es decir, se acepta que la varianza es superior a 12. -/
theorem chiStat_in_rejection_region : 16.919 < chiStat data 12 := by
  rw [chiStat_data]
  norm_num

end RatasDietaA
