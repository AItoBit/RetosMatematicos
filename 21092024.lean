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
# Retos Matemáticos (ISSN: 2952–0746), 21 de septiembre de 2024

**Ejercicio.** Si `f(x)` es un polinomio de grado `n` y `Sₖ := ∑_{j=1}^{n} αⱼ^k` es la suma de
las potencias `k`-ésimas de sus raíces `α₁, …, αₙ`, entonces se verifica que

`f'(x) / f(x) = ∑_{k=0}^{∞} Sₖ / x^{k+1}`,

siempre que `|x| > máx{|α₁|, …, |αₙ|}`.

*Formalización.* Se trabaja sobre `ℂ`, donde todo polinomio de grado `n` se factoriza como
`f = C A * ∏_{j} (X - C αⱼ)` con `A ≠ 0` su coeficiente principal y `α : Fin n → ℂ` la lista
de sus raíces contadas con multiplicidad.  La hipótesis `|x| > máx{|α₁|, …, |αₙ|}` se escribe
como `∀ j, ‖α j‖ < ‖x‖` (equivalente, y con sentido también para `n = 0`).  La igualdad con
una serie infinita se formaliza con `HasSum`, que expresa simultáneamente la convergencia
(incondicional) de la serie y el valor de su suma.

La demostración sigue la 1ª forma del documento: desarrollo en serie geométrica de cada
`1 / (x - αⱼ)` y suma finita en `j`, junto con la derivada logarítmica del producto.
-/

namespace RetosMatematicos

open Polynomial

/-- La suma de las potencias `k`-ésimas de las raíces `α₁, …, αₙ`: `Sₖ = ∑_{j} αⱼ^k`. -/
noncomputable def powerSum {n : ℕ} (α : Fin n → ℂ) (k : ℕ) : ℂ := ∑ j, (α j) ^ k

/-- Serie geométrica: si `‖a‖ < ‖x‖`, entonces `∑_{k=0}^∞ a^k / x^{k+1} = 1 / (x - a)`. -/
theorem hasSum_geometric_div_pow_succ {a x : ℂ} (h : ‖a‖ < ‖x‖) :
    HasSum (fun k : ℕ => a ^ k / x ^ (k + 1)) (1 / (x - a)) := by
  have hx : x ≠ 0 := by
    intro hx0
    rw [hx0, norm_zero] at h
    exact absurd h (not_lt.mpr (norm_nonneg a))
  have hax : ‖a / x‖ < 1 := by
    rw [norm_div, div_lt_one (by positivity)]
    exact h
  have hxa : x - a ≠ 0 := by
    intro h0
    have hax' : a = x := by linear_combination -h0
    rw [hax'] at h
    exact lt_irrefl _ h
  have hne : (1 : ℂ) - a / x ≠ 0 := by
    intro h0
    apply hxa
    field_simp at h0
    linear_combination h0
  have H := (hasSum_geometric_of_norm_lt_one hax).mul_left (1 / x)
  have key : (fun k : ℕ => 1 / x * (a / x) ^ k) = fun k : ℕ => a ^ k / x ^ (k + 1) := by
    funext k
    rw [div_pow, pow_succ]
    field_simp
  have hval : 1 / x * (1 - a / x)⁻¹ = 1 / (x - a) := by field_simp
  rw [key, hval] at H
  exact H

/-- Derivada logarítmica de un polinomio factorizado:
si `f = C A * ∏_j (X - C αⱼ)` con `A ≠ 0` y `x` no es raíz, entonces
`f'(x) / f(x) = ∑_j 1 / (x - αⱼ)`. -/
theorem logDeriv_eval_eq_sum {n : ℕ} {A : ℂ} (hA : A ≠ 0) {α : Fin n → ℂ} {x : ℂ}
    (hx : ∀ j, x ≠ α j) :
    (Polynomial.derivative (C A * ∏ j, (X - C (α j)))).eval x /
        (C A * ∏ j, (X - C (α j))).eval x
      = ∑ j, 1 / (x - α j) := by
  have hne : ∀ j : Fin n, x - α j ≠ 0 := fun j => sub_ne_zero.mpr (hx j)
  have hprod : ∀ s : Finset (Fin n), (∏ j ∈ s, (x - α j)) ≠ 0 :=
    fun s => Finset.prod_ne_zero_iff.mpr fun j _ => hne j
  rw [derivative_mul, derivative_C, Polynomial.derivative_prod_finset]
  simp only [derivative_sub, derivative_X, derivative_C, sub_zero, mul_one,
    eval_mul, eval_C, eval_finsetSum, eval_prod, eval_sub, eval_X, zero_mul, zero_add]
  rw [mul_div_mul_left _ _ hA, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.prod_erase_mul Finset.univ (fun i => x - α i) (Finset.mem_univ j),
    div_mul_eq_div_div, div_self (hprod _)]

/-- **Ejercicio (Retos Matemáticos, 21/09/2024).** Sea `f = C A * ∏_j (X - C αⱼ)` un polinomio
complejo de grado `n`, con coeficiente principal `A ≠ 0` y raíces `α₁, …, αₙ` (contadas con
multiplicidad), y sea `Sₖ = ∑_j αⱼ^k`.  Si `|x| > máx{|α₁|, …, |αₙ|}`, entonces la serie
`∑_{k≥0} Sₖ / x^{k+1}` converge y su suma vale `f'(x) / f(x)`. -/
theorem hasSum_powerSum_logDeriv {n : ℕ} {A : ℂ} (hA : A ≠ 0) {α : Fin n → ℂ}
    (f : Polynomial ℂ) (hf : f = C A * ∏ j, (X - C (α j)))
    {x : ℂ} (hx : ∀ j, ‖α j‖ < ‖x‖) :
    HasSum (fun k : ℕ => powerSum α k / x ^ (k + 1))
      ((Polynomial.derivative f).eval x / f.eval x) := by
  have hxne : ∀ j, x ≠ α j := by
    intro j hxj
    rw [hxj] at hx
    exact lt_irrefl _ (hx j)
  rw [hf, logDeriv_eval_eq_sum hA hxne]
  have H : HasSum (fun k : ℕ => ∑ j, (α j) ^ k / x ^ (k + 1)) (∑ j, 1 / (x - α j)) :=
    hasSum_sum fun j _ => hasSum_geometric_div_pow_succ (hx j)
  refine H.congr_fun ?_
  intro k
  rw [powerSum, Finset.sum_div]

/-- Reformulación con la suma de la serie: bajo las mismas hipótesis,
`f'(x) / f(x) = ∑' k, Sₖ / x^{k+1}`. -/
theorem tsum_powerSum_eq_logDeriv {n : ℕ} {A : ℂ} (hA : A ≠ 0) {α : Fin n → ℂ}
    (f : Polynomial ℂ) (hf : f = C A * ∏ j, (X - C (α j)))
    {x : ℂ} (hx : ∀ j, ‖α j‖ < ‖x‖) :
    (Polynomial.derivative f).eval x / f.eval x = ∑' k : ℕ, powerSum α k / x ^ (k + 1) :=
  (hasSum_powerSum_logDeriv hA f hf hx).tsum_eq.symm

end RetosMatematicos
