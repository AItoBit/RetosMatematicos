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
# Retos Matemáticos, 25 de enero de 2023

**Ejercicio.** Encuéntrese el valor óptimo de la constante `k` para que la desigualdad
`cos⁴ A + cos⁴ B + cos⁴ C ≥ k` se cumpla en cualquier triángulo acutángulo.

**Respuesta.** `k = 3/16`.

Formalizamos el enunciado (la constante óptima es el máximo del conjunto de constantes
válidas) y la solución, siguiendo esencialmente la *3ª Forma* del documento:

* identidad de Euler `cos²A + cos²B + cos²C = 1 - 2 cos A cos B cos C`;
* la cota `cos A cos B cos C ≤ 1/8`, de donde `cos²A + cos²B + cos²C ≥ 3/4`;
* la desigualdad entre medias `x² + y² + z² ≥ (x+y+z)²/3`, que da
  `cos⁴A + cos⁴B + cos⁴C ≥ (3/4)²/3 = 3/16`.

También se formaliza el Teorema 1 (2ª Forma):
`cos^(2ⁿ) A + cos^(2ⁿ) B + cos^(2ⁿ) C ≥ 3 / 2^(2ⁿ)` para todo `n ≥ 1`.
-/

namespace RetosMatematicos25012023

open Real

/-- `A`, `B`, `C` son los ángulos de un triángulo acutángulo. -/
def IsAcuteTriangle (A B C : ℝ) : Prop :=
  0 < A ∧ A < π / 2 ∧ 0 < B ∧ B < π / 2 ∧ 0 < C ∧ C < π / 2 ∧ A + B + C = π

theorem cos_pos_of_isAcuteTriangle {A B C : ℝ} (h : IsAcuteTriangle A B C) :
    0 < Real.cos A ∧ 0 < Real.cos B ∧ 0 < Real.cos C := by
  obtain ⟨hA, hA', hB, hB', hC, hC', -⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;>
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by assumption⟩

/-- Identidad de Euler: si `A + B + C = π` entonces
`cos²A + cos²B + cos²C = 1 - 2 cos A cos B cos C`. -/
theorem cos_sq_add_cos_sq_add_cos_sq {A B C : ℝ} (h : A + B + C = π) :
    Real.cos A ^ 2 + Real.cos B ^ 2 + Real.cos C ^ 2
      = 1 - 2 * (Real.cos A * Real.cos B * Real.cos C) := by
  have hC : C = π - (A + B) := by linarith
  subst hC
  rw [Real.cos_pi_sub, Real.cos_add]
  nlinarith [Real.sin_sq_add_cos_sq A, Real.sin_sq_add_cos_sq B]

/-- En un triángulo acutángulo, `cos A cos B cos C ≤ 1/8`. -/
theorem cos_mul_cos_mul_cos_le {A B C : ℝ} (h : IsAcuteTriangle A B C) :
    Real.cos A * Real.cos B * Real.cos C ≤ 1 / 8 := by
  obtain ⟨hcA, -, -⟩ := cos_pos_of_isAcuteTriangle h
  obtain ⟨-, -, -, -, -, -, hsum⟩ := h
  -- `2 cos B cos C = cos (B - C) + cos (B + C) = cos (B - C) - cos A`
  have hBC : B + C = π - A := by linarith
  have key : 2 * (Real.cos B * Real.cos C) = Real.cos (B - C) - Real.cos A := by
    have h1 : Real.cos (B - C) + Real.cos (B + C) = 2 * (Real.cos B * Real.cos C) := by
      rw [Real.cos_sub, Real.cos_add]; ring
    rw [hBC, Real.cos_pi_sub] at h1
    linarith
  have h2 : Real.cos (B - C) ≤ 1 := Real.cos_le_one _
  have h3 : Real.cos B * Real.cos C ≤ (1 - Real.cos A) / 2 := by linarith
  nlinarith [sq_nonneg (Real.cos A - 1 / 2)]

/-- En un triángulo acutángulo, `cos²A + cos²B + cos²C ≥ 3/4`. -/
theorem three_quarters_le_cos_sq_sum {A B C : ℝ} (h : IsAcuteTriangle A B C) :
    3 / 4 ≤ Real.cos A ^ 2 + Real.cos B ^ 2 + Real.cos C ^ 2 := by
  have hid := cos_sq_add_cos_sq_add_cos_sq h.2.2.2.2.2.2
  have hprod := cos_mul_cos_mul_cos_le h
  linarith

/-- **Desigualdad del ejercicio**: en cualquier triángulo acutángulo,
`cos⁴A + cos⁴B + cos⁴C ≥ 3/16`. -/
theorem three_div_sixteen_le_cos_pow_four_sum {A B C : ℝ} (h : IsAcuteTriangle A B C) :
    3 / 16 ≤ Real.cos A ^ 4 + Real.cos B ^ 4 + Real.cos C ^ 4 := by
  have hs := three_quarters_le_cos_sq_sum h
  nlinarith [sq_nonneg (Real.cos A ^ 2 - Real.cos B ^ 2),
    sq_nonneg (Real.cos B ^ 2 - Real.cos C ^ 2), sq_nonneg (Real.cos A ^ 2 - Real.cos C ^ 2),
    sq_nonneg (Real.cos A ^ 2 + Real.cos B ^ 2 + Real.cos C ^ 2)]

/-- El triángulo equilátero es acutángulo. -/
theorem isAcuteTriangle_pi_div_three : IsAcuteTriangle (π / 3) (π / 3) (π / 3) := by
  have hpi := Real.pi_pos
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by ring⟩

/-- En el triángulo equilátero se alcanza el valor `3/16`. -/
theorem cos_pow_four_sum_pi_div_three :
    Real.cos (π / 3) ^ 4 + Real.cos (π / 3) ^ 4 + Real.cos (π / 3) ^ 4 = 3 / 16 := by
  rw [Real.cos_pi_div_three]; norm_num

/-- **Enunciado formalizado**: `3/16` es el valor óptimo (el mayor) de la constante `k` para la
cual la desigualdad `cos⁴A + cos⁴B + cos⁴C ≥ k` se cumple en todo triángulo acutángulo. -/
theorem isGreatest_optimal_constant :
    IsGreatest {k : ℝ | ∀ A B C : ℝ, IsAcuteTriangle A B C →
      k ≤ Real.cos A ^ 4 + Real.cos B ^ 4 + Real.cos C ^ 4} (3 / 16) := by
  constructor
  · intro A B C h
    exact three_div_sixteen_le_cos_pow_four_sum h
  · intro k hk
    have := hk (π / 3) (π / 3) (π / 3) isAcuteTriangle_pi_div_three
    rwa [cos_pow_four_sum_pi_div_three] at this

/-- **Teorema 1** (2ª Forma): para cualquier triángulo acutángulo y cualquier `n ≥ 1`,
`cos^(2ⁿ) A + cos^(2ⁿ) B + cos^(2ⁿ) C ≥ 3 / 2^(2ⁿ)`. -/
theorem cos_pow_two_pow_sum_ge {A B C : ℝ} (h : IsAcuteTriangle A B C) (n : ℕ) (hn : 1 ≤ n) :
    3 / (2 : ℝ) ^ (2 ^ n) ≤
      Real.cos A ^ (2 ^ n) + Real.cos B ^ (2 ^ n) + Real.cos C ^ (2 ^ n) := by
  induction n, hn using Nat.le_induction with
  | base =>
      have := three_quarters_le_cos_sq_sum h
      norm_num
      linarith
  | succ n hn ih =>
      have hpow : ∀ x : ℝ, x ^ (2 ^ (n + 1)) = (x ^ (2 ^ n)) ^ 2 := by
        intro x
        rw [← pow_mul, pow_succ]
      have h2 : ((2 : ℝ) ^ (2 ^ (n + 1))) = ((2 : ℝ) ^ (2 ^ n)) ^ 2 := by
        rw [← pow_mul, pow_succ]
      have hpos : (0 : ℝ) < (2 : ℝ) ^ (2 ^ n) := by positivity
      rw [hpow (Real.cos A), hpow (Real.cos B), hpow (Real.cos C), h2]
      set u := Real.cos A ^ (2 ^ n)
      set v := Real.cos B ^ (2 ^ n)
      set w := Real.cos C ^ (2 ^ n)
      set s : ℝ := (2 : ℝ) ^ (2 ^ n) with hs
      rw [div_le_iff₀ (by positivity)]
      have hsum : 3 / s ≤ u + v + w := ih
      have h3 : 3 ≤ (u + v + w) * s := by
        rw [div_le_iff₀ hpos] at hsum; linarith
      nlinarith [sq_nonneg (u - v), sq_nonneg (v - w), sq_nonneg (u - w),
        sq_nonneg (u + v + w), sq_nonneg ((u + v + w) * s - 3), hpos]

end RetosMatematicos25012023
