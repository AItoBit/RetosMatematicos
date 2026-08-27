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
# Reto Matemático del 3 de junio de 2023

**Enunciado.** Hállese el lugar geométrico de los centros de las hipérbolas equiláteras
que pasan por los vértices del triángulo determinado por las rectas
`x = 0`, `y = 0`, `x + 2y = 6`.

Los vértices son `O = (0,0)`, `A = (0,3)` y `B = (6,0)`.

**Solución.** El lugar geométrico es la circunferencia de los nueve puntos del triángulo,
de centro `(3/2, 3/4)` y radio `3√5/4`, excluidos los puntos `(0,0)` y `(6/5, 12/5)`
(el primero no es centro de ninguna cónica de la familia, y el segundo corresponde a una
hipérbola degenerada).
-/

namespace RetoHiperbolasEquilateras

/-- Valor en `(x, y)` de la cónica general
`a x² + 2b xy + c y² + 2d x + 2e y + f`. -/
def conicEval (a b c d e f x y : ℝ) : ℝ :=
  a * x ^ 2 + 2 * b * x * y + c * y ^ 2 + 2 * d * x + 2 * e * y + f

/-- Determinante de la matriz proyectiva `!![a, b, d; b, c, e; d, e, f]` asociada a la cónica. -/
def conicDet (a b c d e f : ℝ) : ℝ :=
  a * (c * f - e ^ 2) - b * (b * f - e * d) + d * (b * e - c * d)

/-- La cónica `a x² + 2b xy + c y² + 2d x + 2e y + f = 0` es una hipérbola equilátera
(no degenerada): la traza de su parte cuadrática es nula (`a + c = 0`, condición de
perpendicularidad de las asíntotas) y su determinante proyectivo no se anula. -/
def IsRectangularHyperbola (a b c d e f : ℝ) : Prop :=
  a + c = 0 ∧ conicDet a b c d e f ≠ 0

/-- `P` es el centro de la cónica: anula las dos derivadas parciales. -/
def IsCenter (a b c d e : ℝ) (P : ℝ × ℝ) : Prop :=
  a * P.1 + b * P.2 + d = 0 ∧ b * P.1 + c * P.2 + e = 0

/-- Lugar geométrico de los centros de las hipérbolas equiláteras que pasan por
`(0,0)`, `(0,3)` y `(6,0)`. -/
def centersLocus : Set (ℝ × ℝ) :=
  {P | ∃ a b c d e f : ℝ, IsRectangularHyperbola a b c d e f ∧
    conicEval a b c d e f 0 0 = 0 ∧
    conicEval a b c d e f 0 3 = 0 ∧
    conicEval a b c d e f 6 0 = 0 ∧
    IsCenter a b c d e P}

/-- La circunferencia de los nueve puntos del triángulo: centro `(3/2, 3/4)`,
radio `3√5/4` (cuyo cuadrado es `45/16`). -/
def ninePointCircle : Set (ℝ × ℝ) :=
  {P | (P.1 - 3 / 2) ^ 2 + (P.2 - 3 / 4) ^ 2 = 45 / 16}

/-- Normalización de los coeficientes: si la cónica pasa por los tres vértices y es una
hipérbola equilátera, entonces `c = -a`, `f = 0`, `d = -3a`, `e = 3a/2`, con `a ≠ 0`
y `b ≠ 3a/4`. -/
theorem coeff_normalization {a b c d e f : ℝ}
    (hH : IsRectangularHyperbola a b c d e f)
    (h0 : conicEval a b c d e f 0 0 = 0)
    (hA : conicEval a b c d e f 0 3 = 0)
    (hB : conicEval a b c d e f 6 0 = 0) :
    c = -a ∧ f = 0 ∧ d = -3 * a ∧ e = 3 * a / 2 ∧ a ≠ 0 ∧ b ≠ 3 * a / 4 := by
  obtain ⟨htr, hdet⟩ := hH
  simp only [conicEval] at h0 hA hB
  have hc : c = -a := by linarith
  have hf : f = 0 := by linarith
  have hd : d = -3 * a := by nlinarith [hB]
  have he : e = 3 * a / 2 := by nlinarith [hA]
  subst hc hf hd he
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · rintro rfl
    exact hdet (by simp only [conicDet]; ring)
  · rintro rfl
    exact hdet (by simp only [conicDet]; ring)

/-- Todo centro de una hipérbola equilátera circunscrita al triángulo está en la
circunferencia de los nueve puntos. -/
theorem centersLocus_subset_ninePointCircle : centersLocus ⊆ ninePointCircle := by
  rintro ⟨p, q⟩ ⟨a, b, c, d, e, f, hH, h0, hA, hB, hc1, hc2⟩
  obtain ⟨hc, hf, hd, he, ha, hb⟩ := coeff_normalization hH h0 hA hB
  subst hc hf hd he
  have key : a * (p ^ 2 + q ^ 2 - 3 * p - 3 / 2 * q) = 0 := by
    have hc1 : a * p + b * q + -3 * a = 0 := hc1
    have hc2 : b * p + -a * q + 3 * a / 2 = 0 := hc2
    linear_combination p * hc1 - q * hc2
  have : p ^ 2 + q ^ 2 - 3 * p - 3 / 2 * q = 0 := by
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h ha
    · exact h
  simp only [ninePointCircle, Set.mem_ofPred_eq]
  nlinarith [this]

/-- **Resultado principal.** El lugar geométrico de los centros de las hipérbolas
equiláteras que pasan por los vértices del triángulo determinado por `x = 0`, `y = 0`,
`x + 2y = 6` es exactamente la circunferencia de los nueve puntos del triángulo,
salvo los puntos `(0,0)` y `(6/5, 12/5)`. -/
theorem centersLocus_eq :
    centersLocus = ninePointCircle \ {((0 : ℝ), (0 : ℝ)), ((6 / 5 : ℝ), (12 / 5 : ℝ))} := by
  apply Set.eq_of_subset_of_subset
  · rintro ⟨p, q⟩ hP
    refine ⟨centersLocus_subset_ninePointCircle hP, ?_⟩
    obtain ⟨a, b, c, d, e, f, hH, h0, hA, hB, hc1, hc2⟩ := hP
    obtain ⟨hc, hf, hd, he, ha, hb⟩ := coeff_normalization hH h0 hA hB
    subst hc hf hd he
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq, not_or, not_and]
    constructor
    · intro h1
      rintro rfl
      subst h1
      exact ha (by linarith)
    · intro h1
      rintro rfl
      subst h1
      exact hb (by linarith)
  · rintro ⟨p, q⟩ ⟨hcirc, hne⟩
    simp only [ninePointCircle, Set.mem_ofPred_eq] at hcirc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq, not_or,
      not_and] at hne
    have hcirc' : p ^ 2 + q ^ 2 - 3 * p - 3 / 2 * q = 0 := by nlinarith [hcirc]
    -- `2p + q ≠ 0`, pues en la circunferencia eso forzaría `(p,q) = (0,0)`.
    have hs : 2 * p + q ≠ 0 := by
      intro hs
      have hq : q = -(2 * p) := by linarith
      subst hq
      have hp : p = 0 := by nlinarith [hcirc']
      exact hne.1 hp (by rw [hp]; ring)
    set t : ℝ := (2 * q - p) / (2 * p + q) with ht
    have htmul : t * (2 * p + q) = 2 * q - p := div_mul_cancel₀ _ hs
    -- `t ≠ 3/4`, pues eso corresponde al punto excluido `(6/5, 12/5)`.
    have ht34 : t ≠ 3 / 4 := by
      intro h
      rw [h] at htmul
      have hq : q = 2 * p := by linarith
      have : p * (5 * p - 6) = 0 := by nlinarith [hcirc']
      rcases mul_eq_zero.mp this with h1 | h1
      · exact hne.1 h1 (by rw [hq, h1]; ring)
      · have hp : p = 6 / 5 := by linarith
        exact hne.2 hp (by rw [hq, hp]; ring)
    refine ⟨1, t, -1, -3, 3 / 2, 0, ⟨by ring, ?_⟩, by simp [conicEval], by
      simp [conicEval]; ring, by simp [conicEval]; ring, ?_, ?_⟩
    · simp only [conicDet]
      intro h
      apply ht34
      linarith
    · show (1 : ℝ) * p + t * q + -3 = 0
      have : (p + t * q - 3) * (2 * p + q) = 0 := by nlinarith [htmul, hcirc']
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact absurd h hs
    · show t * p + (-1) * q + 3 / 2 = 0
      have : (t * p - q + 3 / 2) * (2 * p + q) = 0 := by nlinarith [htmul, hcirc']
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact absurd h hs

end RetoHiperbolasEquilateras
