import Mathlib

/-!
# Retos Matemáticos, 10 de mayo de 2023

**Ejercicio.** Sea `f : ℝ → ℝ` una función tal que
`f (x^2 + x) + 2 * f (x^2 - 3*x + 2) = 9*x^2 - 15*x` para todo `x ∈ ℝ`.
Hallar `f 2023`.

**Solución.** `f 2023 = 6065`.

En este archivo se formaliza el enunciado y la solución:

* `Retos10052023.eq_on_sq_add_self`: para todo `x`, `f (x^2 + x) = 3*(x^2 + x) - 4`
  (se obtiene del cambio de variable `x ↦ 1 - x`, que intercambia las dos parábolas).
* `Retos10052023.eq_of_ge`: por tanto `f t = 3*t - 4` para todo `t ≥ -1/4`
  (todo `t ≥ -1/4` es de la forma `x^2 + x`).
* `Retos10052023.f_2023`: en particular `f 2023 = 6065`.
* `Retos10052023.exists_solution`: la función `t ↦ 3*t - 4` sí satisface la ecuación,
  de modo que el enunciado no es vacío.
-/

namespace Retos10052023

variable {f : ℝ → ℝ}

/-- Con el cambio de variable `x ↦ 1 - x` (que intercambia `x^2 + x` y `x^2 - 3x + 2`)
se despeja `f (x^2 + x) = 3 (x^2 + x) - 4`. -/
theorem eq_on_sq_add_self
    (hf : ∀ x : ℝ, f (x ^ 2 + x) + 2 * f (x ^ 2 - 3 * x + 2) = 9 * x ^ 2 - 15 * x)
    (x : ℝ) : f (x ^ 2 + x) = 3 * (x ^ 2 + x) - 4 := by
  have h1 := hf x
  have h2 := hf (1 - x)
  have e1 : (1 - x) ^ 2 + (1 - x) = x ^ 2 - 3 * x + 2 := by ring
  have e2 : (1 - x) ^ 2 - 3 * (1 - x) + 2 = x ^ 2 + x := by ring
  rw [e1, e2] at h2
  linarith

/-- Todo real `t ≥ -1/4` se escribe como `x^2 + x`. -/
theorem exists_sq_add_self {t : ℝ} (ht : -(1 / 4) ≤ t) :
    ∃ x : ℝ, x ^ 2 + x = t := by
  refine ⟨(Real.sqrt (1 + 4 * t) - 1) / 2, ?_⟩
  have hd : Real.sqrt (1 + 4 * t) ^ 2 = 1 + 4 * t :=
    Real.sq_sqrt (by linarith)
  nlinarith [hd]

/-- Para todo `t ≥ -1/4` se tiene `f t = 3 t - 4`. -/
theorem eq_of_ge
    (hf : ∀ x : ℝ, f (x ^ 2 + x) + 2 * f (x ^ 2 - 3 * x + 2) = 9 * x ^ 2 - 15 * x)
    {t : ℝ} (ht : -(1 / 4) ≤ t) : f t = 3 * t - 4 := by
  obtain ⟨x, hx⟩ := exists_sq_add_self ht
  have := eq_on_sq_add_self hf x
  rwa [hx] at this

/-- **Solución del ejercicio**: `f 2023 = 6065`. -/
theorem f_2023
    (hf : ∀ x : ℝ, f (x ^ 2 + x) + 2 * f (x ^ 2 - 3 * x + 2) = 9 * x ^ 2 - 15 * x) :
    f 2023 = 6065 := by
  rw [eq_of_ge hf (by norm_num)]
  norm_num

/-- La ecuación funcional tiene solución: `f t = 3 t - 4` la satisface. -/
theorem exists_solution :
    ∀ x : ℝ, (fun t : ℝ => 3 * t - 4) (x ^ 2 + x)
      + 2 * (fun t : ℝ => 3 * t - 4) (x ^ 2 - 3 * x + 2) = 9 * x ^ 2 - 15 * x := by
  intro x
  simp only
  ring

end Retos10052023
