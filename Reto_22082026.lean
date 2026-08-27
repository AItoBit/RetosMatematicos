/-
  ∫₀^{π/4} log(1 + tan x) dx = (π/8) · log 2

  Formalización en Lean 4 / Mathlib del argumento clásico de simetría:
    1. Reflexión  x ↦ π/4 - x
    2. tan(π/4 - x) = (1 - tan x)/(1 + tan x)
    3. 1 + tan(π/4 - x) = 2/(1 + tan x)
    4. log(2/(1+tan x)) = log 2 - log(1+tan x)  ⟹  I = (π/4)·log 2 - I
-/
import Mathlib

open scoped Real
open MeasureTheory

namespace LogTan

variable {x : ℝ}

/-! ### Hechos elementales en el intervalo `[0, π/4]` -/

lemma cos_pos_aux (h0 : 0 ≤ x) (h1 : x ≤ π / 4) : 0 < Real.cos x := by
  have hπ := Real.pi_pos
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩

lemma sin_nonneg_aux (h0 : 0 ≤ x) (h1 : x ≤ π / 4) : 0 ≤ Real.sin x := by
  have hπ := Real.pi_pos
  exact Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith)

/-- El integrando está bien definido: `1 + tan x > 0` en `[0, π/4]`. -/
lemma one_add_tan_pos (h0 : 0 ≤ x) (h1 : x ≤ π / 4) : 0 < 1 + Real.tan x := by
  have hc := cos_pos_aux h0 h1
  have hs := sin_nonneg_aux h0 h1
  have htan : 0 ≤ Real.tan x := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_nonneg hs hc.le
  linarith

/-! ### Pasos 2–4: la identidad puntual -/

/-- Corazón del argumento:
    `log (1 + tan (π/4 - x)) = log 2 - log (1 + tan x)` para `x ∈ [0, π/4]`. -/
lemma log_one_add_tan_reflect (h0 : 0 ≤ x) (h1 : x ≤ π / 4) :
    Real.log (1 + Real.tan (π / 4 - x)) = Real.log 2 - Real.log (1 + Real.tan x) := by
  have hc : 0 < Real.cos x := cos_pos_aux h0 h1
  have hcne : Real.cos x ≠ 0 := hc.ne'
  have hs : 0 ≤ Real.sin x := sin_nonneg_aux h0 h1
  have hsum : 0 < Real.cos x + Real.sin x := by linarith
  have hsumne : Real.cos x + Real.sin x ≠ 0 := hsum.ne'
  -- fórmulas de resta (sustituyen a `tan(A - B)`, evitando sus hipótesis de polos)
  have hsin : Real.sin (π / 4 - x) = Real.sqrt 2 / 2 * (Real.cos x - Real.sin x) := by
    rw [Real.sin_sub, Real.sin_pi_div_four, Real.cos_pi_div_four]; ring
  have hcos : Real.cos (π / 4 - x) = Real.sqrt 2 / 2 * (Real.cos x + Real.sin x) := by
    rw [Real.cos_sub, Real.cos_pi_div_four, Real.sin_pi_div_four]; ring
  have hr2 : (0 : ℝ) < Real.sqrt 2 / 2 := by positivity
  have hden : Real.sqrt 2 / 2 * (Real.cos x + Real.sin x) ≠ 0 := (mul_pos hr2 hsum).ne'
  -- paso 2:  tan(π/4 - x) = (cos x - sin x)/(cos x + sin x) = (1 - tan x)/(1 + tan x)
  have htan : Real.tan (π / 4 - x)
      = (Real.cos x - Real.sin x) / (Real.cos x + Real.sin x) := by
    rw [Real.tan_eq_sin_div_cos, hsin, hcos, div_eq_div_iff hden hsumne]
    ring
  have htanx : 1 + Real.tan x = (Real.cos x + Real.sin x) / Real.cos x := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp
  -- paso 3:  1 + tan(π/4 - x) = 2/(1 + tan x)
  have hkey : 1 + Real.tan (π / 4 - x) = 2 / (1 + Real.tan x) := by
    rw [htan, htanx, div_div_eq_mul_div]
    field_simp
    ring
  -- paso 4:  log(a/b) = log a - log b
  rw [hkey, Real.log_div (by norm_num) (one_add_tan_pos h0 h1).ne']

/-! ### Integrabilidad -/

lemma integrable_log_one_add_tan :
    IntervalIntegrable (fun x => Real.log (1 + Real.tan x)) volume 0 (π / 4) := by
  have hπ := Real.pi_pos
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le (by linarith : (0:ℝ) ≤ π / 4)]
  intro x hx
  obtain ⟨h0, h1⟩ := hx
  have hc : 0 < Real.cos x := cos_pos_aux h0 h1
  have hpos : 0 < 1 + Real.tan x := one_add_tan_pos h0 h1
  have htan : ContinuousAt Real.tan x := Real.continuousAt_tan.mpr hc.ne'
  exact (ContinuousAt.log (continuousAt_const.add htan) hpos.ne').continuousWithinAt

/-! ### Teorema principal -/

theorem integral_log_one_add_tan :
    (∫ x in (0:ℝ)..(π / 4), Real.log (1 + Real.tan x)) = π / 8 * Real.log 2 := by
  have hπ := Real.pi_pos
  have hle : (0 : ℝ) ≤ π / 4 := by linarith
  -- Paso 1: ∫₀^a f(x) dx = ∫₀^a f(a - x) dx
  have hrefl : (∫ x in (0:ℝ)..(π / 4), Real.log (1 + Real.tan (π / 4 - x)))
      = ∫ x in (0:ℝ)..(π / 4), Real.log (1 + Real.tan x) := by
    simpa using
      intervalIntegral.integral_comp_sub_left
        (a := (0:ℝ)) (b := π / 4)
        (f := fun x => Real.log (1 + Real.tan x)) (π / 4)
  -- Pasos 2–4 bajo el signo integral
  have hcongr : (∫ x in (0:ℝ)..(π / 4), Real.log (1 + Real.tan (π / 4 - x)))
      = ∫ x in (0:ℝ)..(π / 4), (Real.log 2 - Real.log (1 + Real.tan x)) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le hle] at hx
    exact log_one_add_tan_reflect hx.1 hx.2
  -- Linealidad: ∫ (log 2 - f) = (π/4)·log 2 - ∫ f
  have hlin : (∫ x in (0:ℝ)..(π / 4), (Real.log 2 - Real.log (1 + Real.tan x)))
      = π / 4 * Real.log 2 - ∫ x in (0:ℝ)..(π / 4), Real.log (1 + Real.tan x) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const integrable_log_one_add_tan,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  -- La ecuación I = (π/4)·log 2 - I
  -- (encadenamos con `calc`: un `rw [← hrefl]` reescribiría también el lado derecho)
  have heq : (∫ x in (0:ℝ)..(π / 4), Real.log (1 + Real.tan x))
      = π / 4 * Real.log 2 - ∫ x in (0:ℝ)..(π / 4), Real.log (1 + Real.tan x) :=
    calc (∫ x in (0:ℝ)..(π / 4), Real.log (1 + Real.tan x))
        = ∫ x in (0:ℝ)..(π / 4), Real.log (1 + Real.tan (π / 4 - x)) := hrefl.symm
      _ = ∫ x in (0:ℝ)..(π / 4), (Real.log 2 - Real.log (1 + Real.tan x)) := hcongr
      _ = π / 4 * Real.log 2 - ∫ x in (0:ℝ)..(π / 4), Real.log (1 + Real.tan x) := hlin
  -- 2I = (π/4)·log 2  ⟹  I = (π/8)·log 2
  linarith

end LogTan
