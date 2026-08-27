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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# Ajedrez y rendimiento en Matemáticas (Retos Matemáticos, 31/12/2022)

Formalización del ejercicio estadístico: se comparan las calificaciones de Matemáticas de
15 alumnos de un instituto donde se imparte ajedrez (IES1) y de 15 alumnos de un instituto
donde no se imparte (IES2), suponiendo normalidad e independencia.

Los apartados del enunciado son:

* a) contraste `H₀ : σ₁² = σ₂²` frente a `H₁ : σ₁² ≠ σ₂²` al nivel `α = 0.05`,
  mediante el estadístico `t₀ = S₁²/S₂²` y la región de aceptación
  `(F₍₁₄,₁₄₎;₀.₉₇₅ , F₍₁₄,₁₄₎;₀.₀₂₅) = (0.3357, 2.9786)`;
* b) contraste `H₀ : μ₁ ≤ μ₂` frente a `H₁ : μ₁ > μ₂` con varianzas desconocidas pero
  iguales, mediante el estadístico `t` de Student de dos muestras y el valor crítico
  `t₂₈;₀.₀₂₅ = 2.048`.

Lo que es *matemáticamente* demostrable (y es lo que aquí se formaliza) es la parte
determinista del ejercicio: el valor exacto de las medias y cuasivarianzas muestrales, el
valor exacto del estadístico `F`, el valor del estadístico `t`, y el hecho de que ambos
estadísticos caen dentro de las correspondientes regiones de aceptación, es decir, que
en ambos apartados **no se rechaza la hipótesis nula**. Los valores críticos
`0.3357`, `2.9786` y `2.048` provienen de las tablas de la `F` de Snedecor y de la `t` de
Student y se toman aquí como constantes numéricas del enunciado.
-/

namespace RetosMatematicos

/-- Calificaciones de Matemáticas de los 15 alumnos del instituto en el que se imparte
ajedrez (IES1, norte de Extremadura). -/
def gradesChess : List ℚ :=
  [5.6, 4.3, 10, 3.6, 6.5, 7.1, 8.1, 6.8, 6.9, 7.3, 8.2, 7.2, 6.7, 8.5, 9.1]

/-- Calificaciones de Matemáticas de los 15 alumnos del instituto en el que no se imparte
ajedrez (IES2, Madrid). -/
def gradesNoChess : List ℚ :=
  [7.6, 7.3, 10, 3.2, 6.1, 5.1, 6.1, 4.8, 4.9, 5.7, 6.1, 6.9, 6.8, 7.5, 9.2]

/-- Media muestral `x̄ = (∑ xᵢ)/n` de una lista de datos. -/
def sampleMean (l : List ℚ) : ℚ := l.sum / l.length

/-- Cuasivarianza muestral `S² = (∑ (xᵢ - x̄)²)/(n-1)` de una lista de datos. -/
def sampleVar (l : List ℚ) : ℚ :=
  ((l.map (fun x => (x - sampleMean l) ^ 2)).sum) / (l.length - 1)

/-- Estadístico del contraste de igualdad de varianzas: el cociente `S₁²/S₂²`, que bajo
`H₀ : σ₁² = σ₂²` sigue una distribución `F` de Snedecor con `(n₁-1, n₂-1)` grados de
libertad. -/
def fStat (l₁ l₂ : List ℚ) : ℚ := sampleVar l₁ / sampleVar l₂

/-- Estadístico `t` de Student para la comparación de las medias de dos poblaciones
normales independientes con varianzas desconocidas pero iguales:
`t₀ = (x̄₁ - x̄₂) / (√(((n₁-1)S₁² + (n₂-1)S₂²)/(n₁+n₂-2)) · √(1/n₁ + 1/n₂))`. -/
noncomputable def tStat (l₁ l₂ : List ℚ) : ℝ :=
  ((sampleMean l₁ : ℝ) - (sampleMean l₂ : ℝ)) /
    Real.sqrt
      ((((l₁.length : ℝ) - 1) * (sampleVar l₁ : ℝ) + ((l₂.length : ℝ) - 1) * (sampleVar l₂ : ℝ)) /
          ((l₁.length : ℝ) + (l₂.length : ℝ) - 2) *
        (1 / (l₁.length : ℝ) + 1 / (l₂.length : ℝ)))

/-! ### Estadísticos descriptivos -/

/-- La media muestral del grupo con ajedrez es `x̄₁ = 7.06`. -/
theorem sampleMean_gradesChess : sampleMean gradesChess = 7.06 := by
  norm_num [sampleMean, gradesChess]

/-- La media muestral del grupo sin ajedrez es `x̄₂ = 973/150 = 6.4866…`
(en el texto se redondea a `6.487`). -/
theorem sampleMean_gradesNoChess : sampleMean gradesNoChess = 973 / 150 := by
  norm_num [sampleMean, gradesNoChess]

/-- La cuasivarianza muestral del grupo con ajedrez es `S₁² = 9899/3500 = 2.8283 (aprox.)`. -/
theorem sampleVar_gradesChess : sampleVar gradesChess = 9899 / 3500 := by
  norm_num [sampleVar, sampleMean, gradesChess]

/-- La cuasivarianza muestral del grupo sin ajedrez es `S₂² = 31543/10500 = 3.0041 (aprox.)`. -/
theorem sampleVar_gradesNoChess : sampleVar gradesNoChess = 31543 / 10500 := by
  norm_num [sampleVar, sampleMean, gradesNoChess]

/-! ### Apartado a): contraste de igualdad de varianzas -/

/-- El estadístico `F` observado vale exactamente `29697/31543 = 0.9415 (aprox.)`. -/
theorem fStat_value : fStat gradesChess gradesNoChess = 29697 / 31543 := by
  rw [fStat, sampleVar_gradesChess, sampleVar_gradesNoChess]
  norm_num

/-- **Apartado a).** El estadístico `t₀ = S₁²/S₂²` pertenece a la región de aceptación
`(F₍₁₄,₁₄₎;₀.₉₇₅ , F₍₁₄,₁₄₎;₀.₀₂₅) = (0.3357 , 2.9786)`, luego al nivel `α = 0.05` no se
rechaza `H₀ : σ₁² = σ₂²`: no hay diferencias significativas entre las varianzas. -/
theorem fTest_accept_equal_variances :
    (0.3357 : ℚ) < fStat gradesChess gradesNoChess ∧
      fStat gradesChess gradesNoChess < 2.9786 := by
  rw [fStat_value]
  constructor <;> norm_num

/-! ### Apartado b): contraste de igualdad de medias -/

/-- Forma cerrada del estadístico `t` de Student de los datos del enunciado:
`t₀ = (43/75)/√(3062/7875)`. -/
theorem tStat_eq :
    tStat gradesChess gradesNoChess = (43 / 75 : ℝ) / Real.sqrt (3062 / 7875) := by
  have h1 : (gradesChess.length : ℝ) = 15 := by norm_num [gradesChess]
  have h2 : (gradesNoChess.length : ℝ) = 15 := by norm_num [gradesNoChess]
  rw [tStat, h1, h2, sampleMean_gradesChess, sampleMean_gradesNoChess, sampleVar_gradesChess,
    sampleVar_gradesNoChess]
  norm_num

private lemma sqrt_bounds : (0.62355 : ℝ) < Real.sqrt (3062 / 7875) ∧
    Real.sqrt (3062 / 7875) < 0.62356 := by
  constructor
  · rw [show (0.62355 : ℝ) = Real.sqrt (0.62355 ^ 2) by rw [Real.sqrt_sq]; norm_num]
    apply Real.sqrt_lt_sqrt <;> norm_num
  · rw [show (0.62356 : ℝ) = Real.sqrt (0.62356 ^ 2) by rw [Real.sqrt_sq]; norm_num]
    apply Real.sqrt_lt_sqrt <;> norm_num

/-- El valor del estadístico `t` observado es `0.91945 (aprox.)`.

(En el texto original figura `0.9189`; esa pequeña diferencia se debe a que allí se usa la
media redondeada `x̄₂ ≈ 6.487` en lugar del valor exacto `973/150`.) -/
theorem tStat_value_bounds :
    (0.9194 : ℝ) < tStat gradesChess gradesNoChess ∧
      tStat gradesChess gradesNoChess < 0.9195 := by
  obtain ⟨hlo, hhi⟩ := sqrt_bounds
  have hpos : (0 : ℝ) < Real.sqrt (3062 / 7875) := lt_trans (by norm_num) hlo
  rw [tStat_eq]
  constructor
  · rw [lt_div_iff₀ hpos]
    nlinarith
  · rw [div_lt_iff₀ hpos]
    nlinarith

/-- **Apartado b).** El estadístico `t₀` cae dentro del intervalo de aceptación
`(-t₂₈;₀.₀₂₅ , t₂₈;₀.₀₂₅) = (-2.048 , 2.048)`, luego al nivel `α = 0.05` no se rechaza
`H₀ : μ₁ ≤ μ₂`: no puede afirmarse que la práctica del ajedrez mejore significativamente
las calificaciones. -/
theorem tTest_no_significant_improvement :
    |tStat gradesChess gradesNoChess| < 2.048 := by
  obtain ⟨hlo, hhi⟩ := tStat_value_bounds
  rw [abs_lt]
  constructor <;> linarith

end RetosMatematicos
