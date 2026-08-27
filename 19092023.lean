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
# Retos Matemáticos, 19 de septiembre de 2023

**Ejercicio.** Resuélvase la siguiente ecuación para `y` real:
`2 * ∛(2y - 1) = y³ + 1`.

**Solución.** Las soluciones son `y = 1`, `y = (-1 + √5)/2 = Φ - 1` y
`y = (-1 - √5)/2 = -Φ`, donde `Φ` es el número áureo.

Para evitar el uso de la raíz cúbica real (que no es una potencia real cuando el
radicando es negativo), la ecuación se formaliza de manera equivalente diciendo que
existe `x` real con `x³ = 2y - 1` y `2x = y³ + 1`; tal `x` es exactamente `∛(2y-1)`.
-/

namespace RetosMatematicos19092023

/-- La función `f(t) = (t³+1)/2`, cuyos puntos fijos resuelven el problema. -/
noncomputable def f (t : ℝ) : ℝ := (t ^ 3 + 1) / 2

lemma f_strictMono : StrictMono f := by
  intro a b hab
  have h : a ^ 3 < b ^ 3 := by
    nlinarith [sq_nonneg (a + b), sq_nonneg (a - b), sq_nonneg a, sq_nonneg b,
      mul_pos (sub_pos.2 hab) (sub_pos.2 hab)]
  unfold f
  linarith

/-- Factorización de la cúbica `y³ - 2y + 1` y sus raíces. -/
lemma cubic_roots (y : ℝ) :
    y ^ 3 - 2 * y + 1 = 0 ↔
      y = 1 ∨ y = (-1 + Real.sqrt 5) / 2 ∨ y = (-1 - Real.sqrt 5) / 2 := by
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  constructor
  · intro h
    have h2 : (y - 1) *
        ((y - (-1 + Real.sqrt 5) / 2) * (y - (-1 - Real.sqrt 5) / 2)) = 0 := by
      linear_combination h - ((y - 1) / 4) * hs
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact Or.inl (by linarith)
    · rcases mul_eq_zero.1 h3 with h4 | h4
      · exact Or.inr (Or.inl (by linarith))
      · exact Or.inr (Or.inr (by linarith))
  · rintro (rfl | rfl | rfl)
    · ring
    · linear_combination ((Real.sqrt 5 - 3) / 8) * hs
    · linear_combination ((-Real.sqrt 5 - 3) / 8) * hs

/-- Si `f (f y) = y` con `f` estrictamente creciente, entonces `f y = y`. -/
lemma fixed_of_involutive {y : ℝ} (h : f (f y) = y) : f y = y := by
  rcases lt_trichotomy (f y) y with h1 | h1 | h1
  · have h2 := f_strictMono h1
    rw [h] at h2
    linarith
  · exact h1
  · have h2 := f_strictMono h1
    rw [h] at h2
    linarith

/-- **Enunciado y solución.** Las soluciones reales de `2·∛(2y-1) = y³+1` son
exactamente `1`, `(-1+√5)/2` y `(-1-√5)/2`. -/
theorem solutions (y : ℝ) :
    (∃ x : ℝ, x ^ 3 = 2 * y - 1 ∧ 2 * x = y ^ 3 + 1) ↔
      y = 1 ∨ y = (-1 + Real.sqrt 5) / 2 ∨ y = (-1 - Real.sqrt 5) / 2 := by
  constructor
  · rintro ⟨x, hx1, hx2⟩
    have hfy : f y = x := by unfold f; linarith
    have hfx : f x = y := by unfold f; rw [hx1]; ring
    have hff : f (f y) = y := by rw [hfy, hfx]
    have hfix : f y = y := fixed_of_involutive hff
    have : y ^ 3 - 2 * y + 1 = 0 := by
      unfold f at hfix; linarith
    exact (cubic_roots y).1 this
  · intro h
    have hc : y ^ 3 - 2 * y + 1 = 0 := (cubic_roots y).2 h
    exact ⟨y, by linarith, by linarith⟩

/-- Raíz cúbica real, definida para todo real (también para radicandos negativos). -/
noncomputable def cbrt (t : ℝ) : ℝ :=
  if 0 ≤ t then t ^ ((1 : ℝ) / 3) else -((-t) ^ ((1 : ℝ) / 3))

@[simp] lemma cbrt_cube (t : ℝ) : cbrt t ^ 3 = t := by
  have key : ∀ u : ℝ, 0 ≤ u → (u ^ ((1 : ℝ) / 3)) ^ 3 = u := by
    intro u hu
    rw [← Real.rpow_natCast (u ^ ((1 : ℝ) / 3)) 3, ← Real.rpow_mul hu]
    norm_num
  unfold cbrt
  split_ifs with h
  · exact key t h
  · have h' : 0 ≤ -t := by linarith [not_le.1 h]
    have := key (-t) h'
    nlinarith [this]

lemma cube_injective : Function.Injective (fun t : ℝ => t ^ 3) := by
  intro a b hab
  have hf : f a = f b := by unfold f; simp only at hab; rw [hab]
  exact f_strictMono.injective hf

/-- La raíz cúbica real es la única solución de `x³ = t`. -/
lemma eq_cbrt_of_cube_eq {x t : ℝ} (hx : x ^ 3 = t) : x = cbrt t :=
  cube_injective (by simp [hx])

/-- **Enunciado original.** Las soluciones reales de `2·∛(2y-1) = y³+1` son exactamente
`1`, `(-1+√5)/2 = Φ - 1` y `(-1-√5)/2 = -Φ`. -/
theorem solutions_cbrt (y : ℝ) :
    2 * cbrt (2 * y - 1) = y ^ 3 + 1 ↔
      y = 1 ∨ y = (-1 + Real.sqrt 5) / 2 ∨ y = (-1 - Real.sqrt 5) / 2 := by
  rw [← solutions y]
  constructor
  · intro h
    exact ⟨cbrt (2 * y - 1), cbrt_cube _, h⟩
  · rintro ⟨x, hx1, hx2⟩
    have : x = cbrt (2 * y - 1) := eq_cbrt_of_cube_eq hx1
    rw [← this]
    exact hx2

end RetosMatematicos19092023
