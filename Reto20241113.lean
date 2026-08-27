/-
  Retos Matemáticos — 13 de noviembre de 2024   (ISSN 2952–0746)
  Propuesto en M-mate-info #2, 2019, Rumanía.
  https://t.me/Retos_Matematicos

  ─────────────────────────────────────────────────────────────────────────────
  ENUNCIADO

  Sea el polinomio P(x) = x³ + x² + m x + n con P(x) ∈ ℝ[x].

    a) Demuéstrese que P(−1) − 2P(0) + P(1) = 2 para cualesquiera valores de m y n.

    b) Determínense los valores de m y n para los cuales el polinomio P(x) es
       divisible por x² + 1.

    c) Demuéstrese que 3(x₁x₂ + x₁x₃ + x₂x₃ + x₁x₂x₃) − (x₁³ + x₂³ + x₃³) = 1 para
       cualesquiera valores de m, n, donde x₁, x₂, x₃ son raíces del polinomio P(x).

  ─────────────────────────────────────────────────────────────────────────────
  NOTAS DE FORMALIZACIÓN

  • (a) se enuncia con `Polynomial.eval`, calculando P(−1), P(0) y P(1) como lemas
    intermedios, igual que en la solución publicada.

  • (b) "determínense" se formaliza como una equivalencia:
        (X² + 1) ∣ P m n  ↔  m = 1 ∧ n = 1.
    La división euclídea del enunciado es el lema `P_eq_quot_add_rem`; el resto,
    de grado ≤ 1, solo puede ser divisible por X² + 1 si es nulo.

  • (c) "x₁, x₂, x₃ son raíces de P" debe entenderse como *las tres raíces con
    multiplicidad* (si no, tomando x₁ = x₂ = x₃ igual a una misma raíz real el
    enunciado es falso). Se dan dos versiones:
      – `parte_c`  : reproduce paso a paso la solución del PDF, tomando como
                     hipótesis las tres ecuaciones xᵢ³ + xᵢ² + m xᵢ + n = 0 y las
                     relaciones de Cardano–Vieta.
      – `parte_c_of_sum` : observación de que en realidad basta la relación
                     x₁ + x₂ + x₃ = −1 (el coeficiente de x²); m y n desaparecen,
                     lo cual explica el "para cualesquiera m, n" del enunciado.
    Al final, `vieta` deriva las relaciones de Cardano–Vieta de la factorización
    de P en ℂ[X], y `parte_c_complex` cierra el círculo.
-/

import Mathlib

open Polynomial

namespace Reto20241113

/-! ## El polinomio `P(x) = x³ + x² + m x + n` -/

noncomputable def P (m n : ℝ) : ℝ[X] := X ^ 3 + X ^ 2 + C m * X + C n

@[simp]
lemma eval_P (m n x : ℝ) : (P m n).eval x = x ^ 3 + x ^ 2 + m * x + n := by
  simp [P]

lemma isRoot_P_iff (m n x : ℝ) :
    (P m n).IsRoot x ↔ x ^ 3 + x ^ 2 + m * x + n = 0 := by
  simp [Polynomial.IsRoot]

/-! ## Apartado (a)

`P(−1) = −m + n`, `P(0) = n`, `P(1) = 2 + m + n`, luego
`P(−1) − 2P(0) + P(1) = −m + n − 2n + 2 + m + n = 2`. -/

lemma eval_P_neg_one (m n : ℝ) : (P m n).eval (-1) = -m + n := by
  simp only [eval_P]; ring

lemma eval_P_zero (m n : ℝ) : (P m n).eval 0 = n := by
  simp only [eval_P]; ring

lemma eval_P_one (m n : ℝ) : (P m n).eval 1 = 2 + m + n := by
  simp only [eval_P]; ring

theorem parte_a (m n : ℝ) :
    (P m n).eval (-1) - 2 * (P m n).eval 0 + (P m n).eval 1 = 2 := by
  rw [eval_P_neg_one, eval_P_zero, eval_P_one]
  ring

/-! ## Apartado (b)

División euclídea: `P = (x² + 1)(x + 1) + [(m − 1)x + (n − 1)]`.
El resto ha de ser idénticamente nulo, de donde `m = n = 1`. -/

lemma P_eq_quot_add_rem (m n : ℝ) :
    P m n = (X ^ 2 + 1) * (X + 1) + (C (m - 1) * X + C (n - 1)) := by
  simp only [P, C_sub, C_1]
  ring

private lemma natDegree_X_sq_add_one : ((X : ℝ[X]) ^ 2 + 1).natDegree = 2 := by
  compute_degree!

theorem parte_b (m n : ℝ) : (X ^ 2 + 1 : ℝ[X]) ∣ P m n ↔ m = 1 ∧ n = 1 := by
  constructor
  · rintro ⟨Q, hQ⟩
    -- el resto también es divisible por `X² + 1`
    have hrem : (C (m - 1) * X + C (n - 1) : ℝ[X]) = (X ^ 2 + 1) * (Q - (X + 1)) := by
      have h := P_eq_quot_add_rem m n
      rw [hQ] at h
      linear_combination -h
    have hdvd : (X ^ 2 + 1 : ℝ[X]) ∣ (C (m - 1) * X + C (n - 1)) := ⟨Q - (X + 1), hrem⟩
    -- pero su grado es ≤ 1 < 2, luego es nulo
    have hzero : (C (m - 1) * X + C (n - 1) : ℝ[X]) = 0 := by
      by_contra hne
      have h1 := Polynomial.natDegree_le_of_dvd hdvd hne
      have h2 : (C (m - 1) * X + C (n - 1) : ℝ[X]).natDegree ≤ 1 := natDegree_linear_le
      rw [natDegree_X_sq_add_one] at h1
      omega
    -- evaluando el resto en 0 y en 1: `n − 1 = 0` y `(m − 1) + (n − 1) = 0`
    have h0 := congrArg (fun p : ℝ[X] => p.eval 0) hzero
    have h1 := congrArg (fun p : ℝ[X] => p.eval 1) hzero
    simp only [eval_add, eval_mul, eval_C, eval_X, eval_zero] at h0 h1
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨rfl, rfl⟩
    refine ⟨X + 1, ?_⟩
    simp only [P, C_1, one_mul]
    ring

/-! ## Apartado (c) -/

/-- La identidad solo depende de la relación de Cardano–Vieta asociada al
coeficiente de `x²`, es decir, de `x₁ + x₂ + x₃ = −1`; de ahí que valga
"para cualesquiera valores de `m` y `n`". -/
theorem parte_c_of_sum {K : Type*} [CommRing K] {x₁ x₂ x₃ : K}
    (v₁ : x₁ + x₂ + x₃ = -1) :
    3 * (x₁ * x₂ + x₁ * x₃ + x₂ * x₃ + x₁ * x₂ * x₃) - (x₁ ^ 3 + x₂ ^ 3 + x₃ ^ 3) = 1 := by
  linear_combination
    (3 * (x₁ * x₂ + x₁ * x₃ + x₂ * x₃) - (x₁ + x₂ + x₃) ^ 2 + (x₁ + x₂ + x₃) - 1) * v₁

/-- Versión que reproduce paso a paso la demostración publicada:
`∑xᵢ² = 1 − 2m`, `∑xᵢ³ = 3m − 3n − 1` y de ahí la identidad. -/
theorem parte_c (m n x₁ x₂ x₃ : ℝ)
    (hx₁ : x₁ ^ 3 + x₁ ^ 2 + m * x₁ + n = 0)
    (hx₂ : x₂ ^ 3 + x₂ ^ 2 + m * x₂ + n = 0)
    (hx₃ : x₃ ^ 3 + x₃ ^ 2 + m * x₃ + n = 0)
    (v₁ : x₁ + x₂ + x₃ = -1)
    (v₂ : x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = m)
    (v₃ : x₁ * x₂ * x₃ = -n) :
    3 * (x₁ * x₂ + x₁ * x₃ + x₂ * x₃ + x₁ * x₂ * x₃) - (x₁ ^ 3 + x₂ ^ 3 + x₃ ^ 3) = 1 := by
  -- `1 = (∑xᵢ)² = ∑xᵢ² + 2∑_{i<j} xᵢxⱼ`, de donde `∑xᵢ² = 1 − 2m`
  have hsq : x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 = 1 - 2 * m := by
    linear_combination (x₁ + x₂ + x₃ - 1) * v₁ - 2 * v₂
  -- como cada `xᵢ` es raíz, `xᵢ³ = −xᵢ² − m xᵢ − n`; sumando:            … (1)
  have h1 : x₁ ^ 3 + x₂ ^ 3 + x₃ ^ 3
      = -(x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2) - m * (x₁ + x₂ + x₃) - 3 * n := by
    linear_combination hx₁ + hx₂ + hx₃
  -- sustituyendo en (1): `∑xᵢ³ = −(1 − 2m) − m·(−1) − 3n = 3m − 3n − 1`
  have hcube : x₁ ^ 3 + x₂ ^ 3 + x₃ ^ 3 = 3 * m - 3 * n - 1 := by
    rw [h1, hsq, v₁]; ring
  -- por consiguiente `3m − 3n − 3m + 3n + 1 = 1`
  rw [hcube, v₂, v₃]
  ring

/-! ## Las relaciones de Cardano–Vieta -/

section Vieta

/-- Si `x₁, x₂, x₃` son las tres raíces (con multiplicidad) de `P` en `ℂ`, se cumplen
las relaciones de Cardano–Vieta `∑xᵢ = −1`, `∑_{i<j} xᵢxⱼ = m`, `x₁x₂x₃ = −n`.
Basta evaluar la factorización en `z = 1, −1, 0`. -/
theorem vieta {m n : ℝ} {x₁ x₂ x₃ : ℂ}
    (hfac : ∀ z : ℂ, z ^ 3 + z ^ 2 + (m : ℂ) * z + (n : ℂ) = (z - x₁) * (z - x₂) * (z - x₃)) :
    x₁ + x₂ + x₃ = -1 ∧
      x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = (m : ℂ) ∧ x₁ * x₂ * x₃ = -(n : ℂ) := by
  have h₀ := hfac 0
  have h₁ := hfac 1
  have h₂ := hfac (-1)
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (1 / 2 : ℂ) * h₁ + (1 / 2 : ℂ) * h₂ - h₀
  · linear_combination (1 / 2 : ℂ) * h₂ - (1 / 2 : ℂ) * h₁
  · linear_combination h₀

/-- Puente entre la factorización en `ℂ[X]` y la identidad de evaluación. -/
lemma eval_of_factorization {m n : ℝ} {x₁ x₂ x₃ : ℂ}
    (h : (P m n).map (algebraMap ℝ ℂ) = (X - C x₁) * (X - C x₂) * (X - C x₃)) (z : ℂ) :
    z ^ 3 + z ^ 2 + (m : ℂ) * z + (n : ℂ) = (z - x₁) * (z - x₂) * (z - x₃) := by
  have h' := congrArg (fun p : ℂ[X] => p.eval z) h
  simpa [P] using h'

/-- Apartado (c) sin hipótesis auxiliares: para las tres raíces complejas de `P`. -/
theorem parte_c_complex {m n : ℝ} {x₁ x₂ x₃ : ℂ}
    (h : (P m n).map (algebraMap ℝ ℂ) = (X - C x₁) * (X - C x₂) * (X - C x₃)) :
    3 * (x₁ * x₂ + x₁ * x₃ + x₂ * x₃ + x₁ * x₂ * x₃) - (x₁ ^ 3 + x₂ ^ 3 + x₃ ^ 3) = 1 :=
  parte_c_of_sum (vieta (eval_of_factorization h)).1

end Vieta

end Reto20241113
