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
# Retos Matemáticos, 4 de julio de 2026

**Ejercicio.** Supongamos que las longitudes `a`, `b`, `c` de los lados de un triángulo
`ABC` satisfacen `a < b < c` y forman una progresión aritmética. Demostrar que
`a * c = 6 * R * r`, siendo `R` y `r` los radios de las circunferencias circunscrita
e inscrita de dicho triángulo.

La formalización usa el semiperímetro `s = (a+b+c)/2`, el área `S` dada por la fórmula
de Herón, y caracteriza `R` y `r` mediante las relaciones clásicas `a*b*c = 4*R*S`
y `S = s*r`, tal y como se hace en las soluciones del enunciado.
-/

namespace RetosMatematicos

/-- Semiperímetro de un triángulo de lados `a`, `b`, `c`. -/
noncomputable def semiperimeter (a b c : ℝ) : ℝ := (a + b + c) / 2

/-- Área de un triángulo de lados `a`, `b`, `c`, dada por la fórmula de Herón. -/
noncomputable def heronArea (a b c : ℝ) : ℝ :=
  Real.sqrt (semiperimeter a b c * (semiperimeter a b c - a) *
    (semiperimeter a b c - b) * (semiperimeter a b c - c))

/-- Para un triángulo no degenerado, el semiperímetro es positivo. -/
lemma semiperimeter_pos {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < semiperimeter a b c := by
  unfold semiperimeter; linarith

/-- Para un triángulo no degenerado, el área de Herón es estrictamente positiva. -/
lemma heronArea_pos {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h₁ : a < b + c) (h₂ : b < a + c) (h₃ : c < a + b) :
    0 < heronArea a b c := by
  have hs : 0 < semiperimeter a b c := semiperimeter_pos ha hb hc
  have h₁' : 0 < semiperimeter a b c - a := by unfold semiperimeter; linarith
  have h₂' : 0 < semiperimeter a b c - b := by unfold semiperimeter; linarith
  have h₃' : 0 < semiperimeter a b c - c := by unfold semiperimeter; linarith
  exact Real.sqrt_pos.2 (by positivity)

/-- **Solución.** Si los lados `a < b < c` de un triángulo están en progresión
aritmética, entonces `a * c = 6 * R * r`, donde `R` es el radio de la circunferencia
circunscrita (caracterizado por `a*b*c = 4*R*S`) y `r` el de la inscrita
(caracterizado por `S = s*r`), siendo `S` el área y `s` el semiperímetro.

La desigualdad triangular `c < a + b` (parte de la hipótesis de que `a`, `b`, `c` sean
los lados de un triángulo) garantiza que el área `S` sea positiva, lo que permite
despejar `R` y `r`. -/
theorem mul_eq_six_mul_circumradius_mul_inradius
    {a b c R r : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c) (htri : c < a + b)
    (hprog : b - a = c - b)
    (hR : a * b * c = 4 * R * heronArea a b c)
    (hr : heronArea a b c = semiperimeter a b c * r) :
    a * c = 6 * R * r := by
  have hb : 0 < b := ha.trans hab
  have hc : 0 < c := hb.trans hbc
  have hS : 0 < heronArea a b c :=
    heronArea_pos ha hb hc (by linarith) (by linarith) htri
  have hSne : heronArea a b c ≠ 0 := ne_of_gt hS
  have hbne : b ≠ 0 := ne_of_gt hb
  -- la progresión aritmética da `2s = a + b + c = 3b`
  have hs : semiperimeter a b c = 3 * b / 2 := by unfold semiperimeter; linarith
  rw [hs] at hr
  -- despejamos `R` y `r`
  have hRv : R = a * b * c / (4 * heronArea a b c) := by field_simp; linarith
  have hrv : r = heronArea a b c * 2 / (3 * b) := by field_simp; linarith
  rw [hRv, hrv]
  field_simp
  ring

/-- Comprobación de que las hipótesis del teorema no son vacías: el triángulo
rectángulo de lados `3, 4, 5` tiene área `6`. -/
lemma heronArea_three_four_five : heronArea 3 4 5 = 6 := by
  unfold heronArea semiperimeter
  norm_num

/-- Ejemplo: para el triángulo `3, 4, 5` (lados en progresión aritmética) se tiene
`R = 5/2`, `r = 1` y, en efecto, `a * c = 3 * 5 = 15 = 6 * R * r`. -/
example : (3 : ℝ) * 5 = 6 * (5 / 2) * 1 :=
  mul_eq_six_mul_circumradius_mul_inradius (a := 3) (b := 4) (c := 5) (R := 5 / 2) (r := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [heronArea_three_four_five]; norm_num)
    (by rw [heronArea_three_four_five]; unfold semiperimeter; norm_num)

end RetosMatematicos
