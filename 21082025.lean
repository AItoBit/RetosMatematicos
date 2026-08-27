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
# Retos Matemáticos, 21 de agosto de 2025

**Ejercicio.** Sean `a`, `b` y `c` números reales que cumplen
`2^a + 4^b = 2^c` y `4^a + 2^b = 4^c`. Obténgase el valor mínimo de `c`.

**Solución.** El valor mínimo es `c = log₂ 3 - 5/3`, alcanzado en `a = -5/3`, `b = -1/3`.

Las potencias se interpretan como potencias reales (`Real.rpow`).
-/

namespace RetosMatematicos21082025

open Real

/-- El conjunto de valores admisibles de `c`: aquellos para los que existen números
reales `a`, `b` con `2^a + 4^b = 2^c` y `4^a + 2^b = 4^c`. -/
def solutionSetC : Set ℝ :=
  {c : ℝ | ∃ a b : ℝ, (2:ℝ) ^ a + (4:ℝ) ^ b = (2:ℝ) ^ c ∧ (4:ℝ) ^ a + (2:ℝ) ^ b = (4:ℝ) ^ c}

/-- Auxiliar: `4 ^ r = (2 ^ r) ^ 2` para potencias reales. -/
private lemma four_rpow_eq (r : ℝ) : (4:ℝ) ^ r = ((2:ℝ) ^ r) ^ 2 := by
  have hp : (0:ℝ) < 2 := by norm_num
  have h42 : (4:ℝ) = (2:ℝ) ^ (2:ℝ) := by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]; norm_num
  rw [h42, ← Real.rpow_mul hp.le, show (2:ℝ) * r = r * 2 by ring, Real.rpow_mul hp.le,
    show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]

/-- Los valores `a = -5/3`, `b = -1/3`, `c = log₂ 3 - 5/3` satisfacen el sistema. -/
theorem logb_three_sub_mem_solutionSetC : Real.logb 2 3 - 5/3 ∈ solutionSetC := by
  have hp : (0:ℝ) < 2 := by norm_num
  have h42 : (4:ℝ) = (2:ℝ) ^ (2:ℝ) := by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have h3 : (2:ℝ) ^ (Real.logb 2 3) = 3 := Real.rpow_logb hp (by norm_num) (by norm_num)
  refine ⟨-5/3, -1/3, ?_, ?_⟩
  · rw [h42, ← Real.rpow_mul hp.le,
      show (2:ℝ) * (-1/3) = 1 + (-5/3) by norm_num,
      show (Real.logb 2 3 - 5/3 : ℝ) = Real.logb 2 3 + (-5/3) by ring,
      Real.rpow_add hp, Real.rpow_add hp, h3, Real.rpow_one]
    ring
  · rw [h42, ← Real.rpow_mul hp.le, ← Real.rpow_mul hp.le,
      show (2:ℝ) * (-5/3) = -10/3 by norm_num,
      show (-1/3 : ℝ) = 3 + (-10/3) by norm_num,
      show (2:ℝ) * (Real.logb 2 3 - 5/3) = Real.logb 2 3 + (Real.logb 2 3 + (-10/3)) by ring,
      Real.rpow_add hp, Real.rpow_add hp, Real.rpow_add hp, h3,
      show ((3:ℝ)) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    ring

/-- Cota inferior: cualquier `c` admisible cumple `c ≥ log₂ 3 - 5/3`. -/
theorem logb_three_sub_le_of_mem_solutionSetC {c : ℝ} (hc : c ∈ solutionSetC) :
    Real.logb 2 3 - 5/3 ≤ c := by
  obtain ⟨a, b, h1, h2⟩ := hc
  have hp : (0:ℝ) < 2 := by norm_num
  set x := (2:ℝ) ^ a with hx
  set y := (2:ℝ) ^ b with hy
  set z := (2:ℝ) ^ c with hz
  have hx0 : 0 < x := Real.rpow_pos_of_pos hp a
  have hy0 : 0 < y := Real.rpow_pos_of_pos hp b
  have hz0 : 0 < z := Real.rpow_pos_of_pos hp c
  rw [four_rpow_eq] at h1
  rw [four_rpow_eq, four_rpow_eq] at h2
  -- De las dos ecuaciones se obtiene `1 = 2xy + y³`, es decir `2yz = 1 + y³`.
  have key : 2 * y * z = 1 + y ^ 3 := by
    nlinarith [sq_nonneg y, sq_nonneg (x + y ^ 2)]
  set t := (2:ℝ) ^ (-1/3 : ℝ) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hp _
  have ht3 : 2 * t ^ 3 = 1 := by
    rw [ht, ← Real.rpow_natCast ((2:ℝ) ^ (-1/3 : ℝ)) 3, ← Real.rpow_mul hp.le]
    norm_num
  -- Desigualdad AM–GM: `2t³ + y³ ≥ 3t²y`, equivalente a `(y - t)²(y + 2t) ≥ 0`.
  have hzge : 3 * t ^ 2 / 2 ≤ z := by
    nlinarith [mul_nonneg (sq_nonneg (y - t)) (by linarith : (0:ℝ) ≤ y + 2 * t)]
  have hval : (2:ℝ) ^ (Real.logb 2 3 - 5/3) = 3 * t ^ 2 / 2 := by
    have h3 : (2:ℝ) ^ (Real.logb 2 3) = 3 := Real.rpow_logb hp (by norm_num) (by norm_num)
    have ht2 : t ^ 2 = (2:ℝ) ^ (-2/3 : ℝ) := by
      rw [ht, ← Real.rpow_natCast ((2:ℝ) ^ (-1/3 : ℝ)) 2, ← Real.rpow_mul hp.le]; norm_num
    rw [ht2, show (Real.logb 2 3 - 5/3 : ℝ) = Real.logb 2 3 + (-5/3) by ring,
      Real.rpow_add hp, h3, show (-2/3 : ℝ) = 1 + (-5/3) by norm_num, Real.rpow_add hp,
      Real.rpow_one]
    ring
  have hfin : (2:ℝ) ^ (Real.logb 2 3 - 5/3) ≤ (2:ℝ) ^ c := by rw [hval]; exact hzge
  exact (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mp hfin

/-- **Resultado.** El valor mínimo de `c` es `log₂ 3 - 5/3 ≈ -0.0817`. -/
theorem min_c_eq : IsLeast solutionSetC (Real.logb 2 3 - 5/3) :=
  ⟨logb_three_sub_mem_solutionSetC, fun _ hc => logb_three_sub_le_of_mem_solutionSetC hc⟩

end RetosMatematicos21082025

#print axioms RetosMatematicos21082025.min_c_eq
