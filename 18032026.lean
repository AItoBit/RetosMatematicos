import Mathlib

open Real intervalIntegral MeasureTheory

noncomputable section

/-!
# Retos Matemáticos (18 de marzo de 2026) - Problema Suneung 2025 (#28)

Sea la función:
  f(x) = (1/2) * x^2 - x + ln(1 + x)

Para cada t > 0, se define g(t) como el valor s > 0 tal que la distancia entre
la proyección al eje Oy de (s, f(s)) y el corte de la recta tangente con el eje Oy
es igual a t.

Dicha distancia resulta ser:
  d(s) = s^3 / (1 + s)

Por tanto, g(t) es la función inversa de d(s) en (0, ∞).
Se busca calcular:
  ∫_{1/2}^{27/4} g(t) dt = 157 / 12 + ln 2
-/

/-- La función f(x) dada en el enunciado -/
def f (x : ℝ) : ℝ :=
  (1 / 2) * x ^ 2 - x + Real.log (1 + x)

/-- La derivada f'(x) = x^2 / (1 + x) -/
def f' (x : ℝ) : ℝ :=
  x ^ 2 / (1 + x)

/-- Ordenada en el origen de la recta tangente en x = s:
    y(0) = f(s) - s * f'(s) -/
def b (s : ℝ) : ℝ :=
  f s - s * f' s

/-- Distancia d(s) sobre el eje Oy entre (0, f(s)) y (0, b(s)):
    d(s) = f(s) - b(s) = s * f'(s) = s^3 / (1 + s) -/
def d (s : ℝ) : ℝ :=
  s ^ 3 / (1 + s)

/-- Primitiva D(s) = s^3 / 3 - s^2 / 2 + s - ln(1 + s) -/
def D (s : ℝ) : ℝ :=
  s ^ 3 / 3 - s ^ 2 / 2 + s - Real.log (1 + s)

/-! ### Comprobaciones de valores límite -/

lemma d_one : d 1 = 1 / 2 := by
  unfold d
  norm_num

lemma d_three : d 3 = 27 / 4 := by
  unfold d
  norm_num

/-- Integral definida ∫_1^3 d(s) ds = 20/3 - ln 2 -/
theorem integral_d :
    ∫ s in (1 : ℝ)..3, d s = 20 / 3 - Real.log 2 := by
  sorry

/-- Función inversa g(t) tal que d(g(t)) = t para t > 0 -/
def g (t : ℝ) : ℝ :=
  Classical.choose (sorry : ∃ s > 0, d s = t)

/-! ### Teorema Principal -/

/--
El valor de la integral definida:
  ∫_{1/2}^{27/4} g(t) dt = 157 / 12 + Real.log 2
-/
theorem reto_matematico_suneung_2025 :
    ∫ t in (1 / 2 : ℝ)..(27 / 4), g t = 157 / 12 + Real.log 2 := by
  sorry

end
