import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000

/-!
# Retos Matemáticos, 1 de diciembre de 2024

**Ejercicio.** Hállese el valor de
`P = 2 · T(3) + 4 · T(5) + 6 · T(7) + ⋯` (25 sumandos),
donde `T(a)` denota la torre infinita de exponentes
`(ᵃ√a) ^ ((ᵃ√a) ^ ((ᵃ√a) ^ ⋯))`.

La solución propuesta en el PDF caracteriza cada torre `x = T(a)` mediante la
ecuación de punto fijo `x = (ᵃ√a) ^ x`, de la que deduce `x = a`, y concluye

`P = 2·3 + 4·5 + ⋯ + 50·51 = ∑_{n=1}^{25} 2n(2n+1) = 22750`.

Formalizamos exactamente ese razonamiento.  Obsérvese que, para `a > e`, la
ecuación de punto fijo `x = (ᵃ√a) ^ x` tiene *dos* soluciones positivas (una
menor que `e` y otra mayor que `e`, a saber `x = a`); por eso la torre se
normaliza aquí con la hipótesis `e ≤ x`, que es la que selecciona la raíz
`x = a` usada en el PDF.
-/

namespace RetosMatematicos20241201

open Real

/-- La función `x ↦ log x / x` es estrictamente decreciente en `[e, ∞)`. -/
theorem strictAntiOn_log_div_self :
    StrictAntiOn (fun x : ℝ => Real.log x / x) {x : ℝ | Real.exp 1 ≤ x} := by
  intro x hex y hey hxy
  simp only [Set.mem_ofPred_eq] at hex hey
  have x_pos : 0 < x := (Real.exp_pos 1).trans_le hex
  have y_pos : 0 < y := (Real.exp_pos 1).trans_le hey
  have hlogx : 1 ≤ Real.log x := by rwa [Real.le_log_iff_exp_le x_pos]
  have hyx : 0 ≤ y / x - 1 := by
    have : 1 ≤ y / x := (one_le_div x_pos).2 hxy.le
    linarith
  have hne : y / x ≠ 1 := by
    intro h
    rw [div_eq_one_iff_eq x_pos.ne'] at h
    exact absurd h hxy.ne'
  have key : Real.log y - Real.log x < Real.log x / x * y - Real.log x := by
    calc Real.log y - Real.log x = Real.log (y / x) := by
          rw [Real.log_div y_pos.ne' x_pos.ne']
      _ < y / x - 1 := Real.log_lt_sub_one_of_pos (div_pos y_pos x_pos) hne
      _ ≤ Real.log x * (y / x - 1) := le_mul_of_one_le_left hyx hlogx
      _ = Real.log x / x * y - Real.log x := by field_simp
  have hfin : Real.log y < Real.log x / x * y := by linarith
  simpa [div_lt_iff₀ y_pos] using hfin

/-- **Lema clave del PDF.**  Si `x` satisface la ecuación de la torre infinita
`x = (ᵃ√a) ^ x` (con la normalización `e ≤ x`, y `e ≤ a`), entonces `x = a`. -/
theorem tower_eq_base {a x : ℝ} (ha : Real.exp 1 ≤ a) (hx : Real.exp 1 ≤ x)
    (h : x = (a ^ (1 / a : ℝ)) ^ x) : x = a := by
  have a_pos : 0 < a := (Real.exp_pos 1).trans_le ha
  have x_pos : 0 < x := (Real.exp_pos 1).trans_le hx
  have hrw : (a ^ (1 / a : ℝ)) ^ x = a ^ (x / a) := by
    rw [← Real.rpow_mul a_pos.le]
    congr 1
    field_simp
  rw [hrw] at h
  have hlog : Real.log x = x / a * Real.log a := by
    conv_lhs => rw [h]
    rw [Real.log_rpow a_pos]
  have hkey : Real.log x / x = Real.log a / a := by
    field_simp at hlog ⊢
    linarith
  exact strictAntiOn_log_div_self.injOn (by simpa using hx) (by simpa using ha) hkey

/-- **Enunciado del ejercicio.**  Sea `x n` el valor de la torre infinita de
base `ᵃ√a` con `a = 2n+1`, caracterizada (como en el PDF) por la ecuación de
punto fijo `x n = ((2n+1) ^ (1/(2n+1))) ^ (x n)` junto con la normalización
`e ≤ x n`.  Entonces

`P = ∑_{n=1}^{25} 2n · x n = 22750`. -/
theorem P_eq_22750 (x : ℕ → ℝ)
    (hx : ∀ n ∈ Finset.Icc (1 : ℕ) 25, Real.exp 1 ≤ x n)
    (hfix : ∀ n ∈ Finset.Icc (1 : ℕ) 25,
      x n = (((2 * (n : ℝ) + 1) ^ (1 / (2 * (n : ℝ) + 1) : ℝ)) ^ (x n))) :
    ∑ n ∈ Finset.Icc (1 : ℕ) 25, (2 * (n : ℝ)) * x n = 22750 := by
  have hexp3 : Real.exp 1 ≤ 3 := by
    have := Real.exp_one_lt_d9
    linarith
  have hval : ∀ n ∈ Finset.Icc (1 : ℕ) 25, x n = 2 * (n : ℝ) + 1 := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have h3 : (3 : ℝ) ≤ 2 * (n : ℝ) + 1 := by
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      linarith
    exact tower_eq_base (le_trans hexp3 h3) (hx n hn) (hfix n hn)
  calc ∑ n ∈ Finset.Icc (1 : ℕ) 25, (2 * (n : ℝ)) * x n
      = ∑ n ∈ Finset.Icc (1 : ℕ) 25, (2 * (n : ℝ)) * (2 * (n : ℝ) + 1) :=
        Finset.sum_congr rfl (fun n hn => by rw [hval n hn])
    _ = 22750 := by
        norm_num [Finset.sum_Icc_succ_top]

/-- Las hipótesis del enunciado no son vacías: la elección `x n = 2n+1`
(el valor que el PDF asigna a cada torre) las satisface. -/
theorem hypotheses_satisfiable :
    ∃ x : ℕ → ℝ, (∀ n ∈ Finset.Icc (1 : ℕ) 25, Real.exp 1 ≤ x n) ∧
      (∀ n ∈ Finset.Icc (1 : ℕ) 25,
        x n = (((2 * (n : ℝ) + 1) ^ (1 / (2 * (n : ℝ) + 1) : ℝ)) ^ (x n))) := by
  refine ⟨fun n => 2 * (n : ℝ) + 1, ?_, ?_⟩
  · intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hexp3 : Real.exp 1 ≤ 3 := by
      have := Real.exp_one_lt_d9
      linarith
    simpa using hexp3.trans (by linarith : (3 : ℝ) ≤ 2 * (n : ℝ) + 1)
  · intro n _
    have hpos : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
    rw [← Real.rpow_mul hpos.le, one_div, inv_mul_cancel₀ hpos.ne', Real.rpow_one]

end RetosMatematicos20241201

