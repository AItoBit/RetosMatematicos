/-
  Retos Matemáticos — 1 de diciembre de 2024   (ISSN 2952–0746)
  Propuesto y resuelto por Juan Carlos Ampie García.
  https://t.me/Retos_Matematicos

  ─────────────────────────────────────────────────────────────────────────────
  ENUNCIADO

  Hállese el valor de

      P = 2·(∛3)^((∛3)^((∛3)^⋰)) + 4·(⁵√5)^((⁵√5)^((⁵√5)^⋰))
        + 6·(⁷√7)^((⁷√7)^((⁷√7)^⋰)) + …            (25 sumandos)

 
-/

import Mathlib

namespace Reto20241201

/-! ## §1. La suma aritmética (rigurosa) -/

/-- Fórmula cerrada: `3·∑_{n=1}^{N} 2n(2n+1) = N(N+1)(4N+5)`. -/
theorem three_mul_sum (N : ℕ) :
    3 * ∑ n ∈ Finset.range N, (2 * (n + 1)) * (2 * (n + 1) + 1)
      = N * (N + 1) * (4 * N + 5) := by
  induction N with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      ring

/-- El valor de la suma del enunciado. -/
theorem sum_25 :
    ∑ n ∈ Finset.range 25, (2 * (n + 1)) * (2 * (n + 1) + 1) = 22750 := by
  rfl

/-- Valor de `P` suponiendo la afirmación del PDF. -/
theorem P_value (T : ℕ → ℝ) (hT : ∀ n ∈ Finset.range 25, T n = 2 * (n : ℝ) + 3) :
    ∑ n ∈ Finset.range 25, (2 * (n : ℝ) + 2) * T n = 22750 := by
  have h : ∀ n ∈ Finset.range 25,
      (2 * (n : ℝ) + 2) * T n = (2 * (n : ℝ) + 2) * (2 * (n : ℝ) + 3) := by
    intro n hn; rw [hT n hn]
  rw [Finset.sum_congr rfl h]
  norm_num [Finset.sum_range_succ]

/-! ## §2. Los pasos válidos del argumento -/

theorem rpow_inv_rpow_self (a : ℝ) (ha : 0 < a) : (a ^ (a⁻¹ : ℝ)) ^ a = a := by
  rw [← Real.rpow_mul ha.le, inv_mul_cancel₀ ha.ne', Real.rpow_one]

theorem rpow_inv_eq_of_fixed {a x : ℝ} (ha : 0 < a) (hx : 0 < x)
    (h : x = (a ^ (a⁻¹ : ℝ)) ^ x) : x ^ (x⁻¹ : ℝ) = a ^ (a⁻¹ : ℝ) := by
  nth_rewrite 1 [h]
  rw [← Real.rpow_mul ha.le, ← Real.rpow_mul ha.le, mul_assoc,
      mul_inv_cancel₀ hx.ne', mul_one]

/-! ## §3. El contraejemplo: la torre de base `∛3` no tiende a 3 -/

noncomputable def torre (a : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => (a ^ (a⁻¹ : ℝ)) ^ (torre a k)

private lemma one_le_base : (1 : ℝ) ≤ (3 : ℝ) ^ ((3 : ℝ)⁻¹) := by
  have h : ((1 : ℝ)) ^ ((3 : ℝ)⁻¹) ≤ (3 : ℝ) ^ ((3 : ℝ)⁻¹) :=
    Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
  simpa using h

private lemma rpow_five_sixths_le : (3 : ℝ) ^ ((5 : ℝ) / 6) ≤ 5 / 2 := by
  have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ ((5 : ℝ) / 6) := Real.rpow_nonneg (by norm_num) _
  have h52 : (0 : ℝ) ≤ 5 / 2 := by norm_num
  have h6 : (0 : ℝ) < 6 := by norm_num
  rw [← Real.rpow_le_rpow_iff h3 h52 h6]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  have h_exp : ((5 : ℝ) / 6) * 6 = 5 := by ring
  rw [h_exp]
  norm_num

private lemma tower_step_bound : ((3 : ℝ) ^ ((3 : ℝ)⁻¹)) ^ ((5 : ℝ) / 2) ≤ 5 / 2 := by
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      show ((3 : ℝ)⁻¹ * ((5 : ℝ) / 2)) = (5 : ℝ) / 6 by norm_num]
  exact rpow_five_sixths_le

theorem torre_three_le (k : ℕ) : torre 3 k ≤ 5 / 2 := by
  induction k with
  | zero => norm_num [torre]
  | succ k ih =>
      have h : torre 3 (k + 1) = ((3 : ℝ) ^ ((3 : ℝ)⁻¹)) ^ (torre 3 k) := by
        simp only [torre]
      rw [h]
      calc ((3 : ℝ) ^ ((3 : ℝ)⁻¹)) ^ (torre 3 k)
          ≤ ((3 : ℝ) ^ ((3 : ℝ)⁻¹)) ^ ((5 : ℝ) / 2) :=
            Real.rpow_le_rpow_of_exponent_le one_le_base ih
        _ ≤ 5 / 2 := tower_step_bound

theorem torre_three_not_tendsto_three :
    ¬ Filter.Tendsto (torre 3) Filter.atTop (nhds 3) := by
  intro h
  have h3 : (3 : ℝ) ≤ 5 / 2 := le_of_tendsto' h torre_three_le
  norm_num at h3

end Reto20241201
