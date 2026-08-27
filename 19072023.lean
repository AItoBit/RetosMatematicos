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
# Retos Matemáticos (19 de julio de 2023): intervalo de confianza para datos apareados

Se examinan `n = 12` estudiantes antes (`Y`) y después (`X`) de aplicar una nueva
metodología.  Con las diferencias `Dᵢ = Xᵢ - Yᵢ` se construye el intervalo de confianza
al 96 % para la mejora media `μ_D = μ_X - μ_Y`,

  `(D̄ - t₁₁;₀.₀₂ · Ŝ_D/√n , D̄ + t₁₁;₀.₀₂ · Ŝ_D/√n)`,

y se realiza el contraste bilateral `H₀ : μ_D = 0` frente a `H₁ : μ_D ≠ 0`.

El valor crítico `t₁₁;₀.₀₂` se obtiene, como en el enunciado, por interpolación lineal
entre los valores tabulados `t₁₁;₀.₀₂₅ = 2.2010` y `t₁₁;₀.₀₁ = 2.7181`.
-/

namespace Reto19072023

/-- Calificaciones **después** de aplicar la metodología. -/
def X : List ℚ := [53.2, 54.5, 51.6, 54.5, 53.9, 55, 52.5, 53.3, 51.5, 52.7, 52, 51.9]

/-- Calificaciones **antes** de aplicar la metodología. -/
def Y : List ℚ := [52.5, 54, 50.8, 54.4, 53.5, 52, 53, 53.5, 50.7, 51.1, 53.2, 52.3]

/-- Tamaño muestral. -/
def n : ℕ := 12

/-- Diferencias `Dᵢ = Xᵢ - Yᵢ` de las muestras apareadas. -/
def Dif : List ℚ := List.zipWith (· - ·) X Y

/-- Media muestral de las diferencias, `D̄`. -/
def Dbar : ℚ := Dif.sum / (n : ℚ)

/-- Cuasivarianza muestral de las diferencias, `Ŝ²_D`. -/
def S2 : ℚ := (Dif.map fun d => (d - Dbar) ^ 2).sum / ((n : ℚ) - 1)

/-- Cuasidesviación típica muestral de las diferencias, `Ŝ_D`. -/
noncomputable def S : ℝ := Real.sqrt (S2 : ℝ)

/-- Error típico de la media, `Ŝ_D/√n`. -/
noncomputable def SE : ℝ := S / Real.sqrt (n : ℝ)

/-- Valor crítico `t₁₁;₀.₀₂` obtenido por interpolación lineal entre
`t₁₁;₀.₀₂₅ = 2.2010` y `t₁₁;₀.₀₁ = 2.7181`. -/
def tcrit : ℚ := 2.2010 + (2.7181 - 2.2010) / (0.01 - 0.025) * (0.02 - 0.025)

/-- Extremo inferior del intervalo de confianza al 96 %. -/
noncomputable def lower : ℝ := (Dbar : ℝ) - (tcrit : ℝ) * SE

/-- Extremo superior del intervalo de confianza al 96 %. -/
noncomputable def upper : ℝ := (Dbar : ℝ) + (tcrit : ℝ) * SE

/-- Estadístico del contraste bajo `H₀ : μ_D = 0`. -/
noncomputable def t0 : ℝ := (Dbar : ℝ) / SE

/-- Las doce diferencias `Dᵢ`. -/
theorem Dif_eq : Dif = [0.7, 0.5, 0.8, 0.1, 0.4, 3, -0.5, -0.2, 0.8, 1.6, -1.2, -0.4] := by
  norm_num [Dif, X, Y]

/-- `D̄ = 5.6/12 = 7/15 ≈ 0.46667`. -/
theorem Dbar_eq : Dbar = 7 / 15 := by
  norm_num [Dbar, Dif_eq, n]

/-- `Ŝ²_D = (977/75)/11 = 977/825 ≈ 1.1842`. -/
theorem S2_eq : S2 = 977 / 825 := by
  norm_num [S2, Dif_eq, Dbar_eq, n]

/-- El valor crítico interpolado es `t₁₁;₀.₀₂ = 71201/30000 ≈ 2.37337`. -/
theorem tcrit_eq : tcrit = 71201 / 30000 := by
  norm_num [tcrit]

/-- El error típico es `Ŝ_D/√n = √(977/9900)`. -/
theorem SE_eq : SE = Real.sqrt (977 / 9900) := by
  rw [SE, S, S2_eq, show ((n : ℕ) : ℝ) = 12 by norm_num [n],
    ← Real.sqrt_div (by norm_num)]
  norm_num

/-- Acotación numérica del error típico: `Ŝ_D/√n ≈ 0.3141446`. -/
theorem SE_bounds : 0.314144 < SE ∧ SE < 0.314145 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 977 / 9900 by norm_num)
  have h0 := Real.sqrt_nonneg (977 / 9900 : ℝ)
  rw [SE_eq]
  constructor <;> nlinarith [h, h0]

/-- Extremo inferior del intervalo de confianza al 96 %: `≈ -0.27891`. -/
theorem lower_bounds : -0.2790 < lower ∧ lower < -0.2788 := by
  obtain ⟨h1, h2⟩ := SE_bounds
  constructor <;> · rw [lower, Dbar_eq, tcrit_eq]; push_cast; nlinarith

/-- Extremo superior del intervalo de confianza al 96 %: `≈ 1.21225`. -/
theorem upper_bounds : 1.2121 < upper ∧ upper < 1.2124 := by
  obtain ⟨h1, h2⟩ := SE_bounds
  constructor <;> · rw [upper, Dbar_eq, tcrit_eq]; push_cast; nlinarith

/-- El intervalo de confianza al 96 % contiene al `0`: no hay evidencias estadísticas
significativas de que la nueva metodología suponga una mejora. -/
theorem zero_mem_interval : (0 : ℝ) ∈ Set.Ioo lower upper := by
  obtain ⟨h1, h2⟩ := lower_bounds
  obtain ⟨h3, h4⟩ := upper_bounds
  exact ⟨by linarith, by linarith⟩

/-- Valor del estadístico de contraste bajo `H₀`: `t₀ ≈ 1.48552`. -/
theorem t0_bounds : 1.4855 < t0 ∧ t0 < 1.4856 := by
  obtain ⟨h1, h2⟩ := SE_bounds
  have hpos : (0 : ℝ) < SE := by linarith
  rw [t0, Dbar_eq]
  push_cast
  refine ⟨?_, ?_⟩
  · rw [lt_div_iff₀ hpos]; nlinarith
  · rw [div_lt_iff₀ hpos]; nlinarith

/-- El estadístico no cae en la región crítica
`R = (-∞, -t₁₁;₀.₀₂] ∪ [t₁₁;₀.₀₂, +∞)`: no se rechaza `H₀`, luego al 96 % de confianza no
hay evidencias significativas de mejora. -/
theorem t0_not_mem_rejection_region :
    t0 ∉ Set.Iic (-(tcrit : ℝ)) ∪ Set.Ici (tcrit : ℝ) := by
  obtain ⟨h1, h2⟩ := t0_bounds
  have ht : ((tcrit : ℚ) : ℝ) = 71201 / 30000 := by rw [tcrit_eq]; norm_num
  simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, not_or, not_le, ht]
  constructor <;> linarith

end Reto19072023

/-!
## Nota sobre los valores publicados

Con los datos del enunciado se obtiene exactamente `D̄ = 7/15 ≈ 0.46667`,
`Ŝ²_D = 977/825 ≈ 1.18424` (luego `Ŝ_D ≈ 1.08823`), `Ŝ_D/√12 = √(977/9900) ≈ 0.31414`
y `t₁₁;₀.₀₂ = 71201/30000 ≈ 2.37337`, en concordancia con el documento original.

El margen de error es entonces `2.37337 · 0.31414 ≈ 0.74558`, de modo que el intervalo
resulta `(0.46667 - 0.74558, 0.46667 + 0.74558) ≈ (-0.27891, 1.21225)`, tal y como
prueban `Reto19072023.lower_bounds` y `Reto19072023.upper_bounds`.  En el documento
original se escribe `(-0.2123, 1.2789)`: las cifras decimales de ambos extremos están
intercambiadas (el intervalo publicado no es simétrico respecto de `D̄`, lo que confirma
la errata).  Análogamente, el estadístico de contraste es `t₀ ≈ 1.48552` y no `1.4867`.

En cualquier caso, la conclusión del documento no se altera: el intervalo contiene al `0`
(`Reto19072023.zero_mem_interval`) y `t₀` no pertenece a la región crítica
(`Reto19072023.t0_not_mem_rejection_region`), luego al 96 % de confianza no hay evidencias
estadísticas significativas de mejora.
-/
