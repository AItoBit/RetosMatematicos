import Mathlib

/-!
# Reto de «Retos Matemáticos» del 29 de mayo de 2023

**Enunciado.** Calcúlese
`q(A) = A^15 - 7A^14 + 15A^13 - 10A^12 + A^11 - A^8 + 4A^7 + 3A^6 - 17A^5 + 2A^4 - 3A^3
        + 18A^2 - 26A + 2I`,
donde A = !![1, -1, 1; -1, 2, 0; 1, 0, 3].
Si `A` es la matriz de coeficientes de un sistema de ecuaciones diferenciales lineales
homogéneo que describe el movimiento relativo de los fragmentos de chatarra espacial
alrededor de la ISS (centrada en el origen), ¿existe peligro de que alguno de dichos
fragmentos impacte con la ISS?

**Solución formalizada.**

*Parte 1.* El polinomio característico de `A` es `p(x) = x^3 - 6x^2 + 9x - 1`
(`ISS.det_charpoly`) y la división euclídea da
`q(x) = (x^12 - x^11 - x^5 - 2x^4 - 3) p(x) + (x - 1)`, de modo que, por Cayley–Hamilton,
`q(A) = A - I` (`ISS.q_A_eq_sub_one`, `ISS.q_A_value`).  Aquí la identidad matricial se
comprueba directamente por cálculo sobre `ℤ` y se transporta a `ℝ`.

*Parte 2.* Todas las raíces de `p` (los autovalores de `A`) tienen parte real positiva
(`ISS.charpoly_root_re_pos`, `ISS.eigenvalue_re_pos`, `ISS.real_eigenvalue_pos`), luego el
sistema `X' = A X` es un repulsor.  Además `A` es simétrica y definida positiva
(`ISS.quadratic_form_lower`), lo que permite probar directamente que el cuadrado de la
distancia de cualquier fragmento a la ISS crece al menos como `e^{t/5}`
(`ISS.sqDist_ge`); en particular un fragmento que no esté inicialmente en la ISS nunca
la alcanza (`ISS.no_collision`) y se aleja indefinidamente
(`ISS.tendsto_sqDist_atTop`):

  **No hay peligro de colisión de la chatarra espacial con la ISS.**
-/

namespace ISS

open Matrix Filter

/-- La matriz `A` del enunciado, sobre un anillo conmutativo arbitrario. -/
def A (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R := !![1, -1, 1; -1, 2, 0; 1, 0, 3]

/-- El polinomio `q` del enunciado, evaluado en una matriz `M`. -/
def q {R : Type*} [CommRing R] (M : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  M ^ 15 - 7 • M ^ 14 + 15 • M ^ 13 - 10 • M ^ 12 + M ^ 11 - M ^ 8 + 4 • M ^ 7 + 3 • M ^ 6
    - 17 • M ^ 5 + 2 • M ^ 4 - 3 • M ^ 3 + 18 • M ^ 2 - 26 • M + 2 • 1

/-! ## Parte 1: cálculo de `q(A)` -/

set_option maxRecDepth 40000 in
/-- Versión entera de la primera parte: `q(A) = A - I` sobre `ℤ`. -/
theorem q_A_int : q (A ℤ) = A ℤ - 1 := by decide

/-- **Parte 1.** `q(A) = A - I`. -/
theorem q_A_eq_sub_one : q (A ℝ) = A ℝ - 1 := by
  have hmap : ((Int.castRingHom ℝ).mapMatrix (A ℤ)) = A ℝ := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [A]
  have h := congrArg ((Int.castRingHom ℝ).mapMatrix) q_A_int
  simp only [q, map_sub, map_add, map_pow, map_one, map_nsmul, hmap] at h
  exact h

/-- **Parte 1, valor explícito.** `q(A) = !![0, -1, 1; -1, 1, 0; 1, 0, 2]`. -/
theorem q_A_value : q (A ℝ) = !![0, -1, 1; -1, 1, 0; 1, 0, 2] := by
  rw [q_A_eq_sub_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [A, Matrix.one_fin_three] <;> norm_num

/-! ## Parte 2: estabilidad del sistema `X' = A X` -/

/-- El polinomio característico de `A`: `det (x I - A) = x^3 - 6x^2 + 9x - 1`. -/
theorem det_charpoly {R : Type*} [CommRing R] (x : R) :
    (x • (1 : Matrix (Fin 3) (Fin 3) R) - A R).det = x ^ 3 - 6 * x ^ 2 + 9 * x - 1 := by
  simp [Matrix.det_fin_three, A, Matrix.one_fin_three]
  ring

/-- Todo autovalor de `A` (sobre un cuerpo) anula el polinomio característico. -/
theorem eigen_charpoly {K : Type*} [Field K] (z : K) (v : Fin 3 → K) (hv : v ≠ 0)
    (h : (A K).mulVec v = z • v) : z ^ 3 - 6 * z ^ 2 + 9 * z - 1 = 0 := by
  have hz : (z • (1 : Matrix (Fin 3) (Fin 3) K) - A K).mulVec v = 0 := by
    rw [Matrix.sub_mulVec, h]
    simp [Matrix.smul_mulVec]
  have hdet := Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv, hz⟩
  rwa [det_charpoly] at hdet

/-- Toda raíz compleja del polinomio característico tiene parte real positiva.
(El argumento muestra de hecho que ninguna raíz puede ser no real.) -/
theorem charpoly_root_re_pos (z : ℂ) (hz : z ^ 3 - 6 * z ^ 2 + 9 * z - 1 = 0) : 0 < z.re := by
  have h1 := congrArg Complex.re hz
  have h2 := congrArg Complex.im hz
  simp [pow_succ, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.sub_re,
    Complex.sub_im] at h1 h2
  set a := z.re
  set b := z.im
  have h2' : b * (3 * a ^ 2 - b ^ 2 - 12 * a + 9) = 0 := by nlinarith [h2]
  rcases mul_eq_zero.1 h2' with hb0 | _
  · -- raíz real: `a (a - 3)^2 = 1`, luego `a > 0`
    rw [hb0] at h1
    nlinarith [sq_nonneg (a - 3), sq_nonneg a]
  · by_cases hb0 : b = 0
    · rw [hb0] at h1
      nlinarith [sq_nonneg (a - 3), sq_nonneg a]
    · -- una raíz no real llevaría a `8a^3 - 48a^2 + 90a - 53 = 0` con `(a-1)(a-3) > 0`
      exfalso
      have hbsq : 0 < b ^ 2 := by positivity
      have hu : 0 < a ^ 2 - 4 * a + 3 := by nlinarith
      have hcubic : 8 * a ^ 3 - 48 * a ^ 2 + 90 * a - 53 = 0 := by nlinarith
      rcases le_or_gt a 2 with h | h
      · nlinarith [hu, hcubic]
      · nlinarith [hu, hcubic]

/-- **Parte 2.** Todo autovalor complejo de `A` tiene parte real positiva: el sistema
`X' = A X` es un repulsor. -/
theorem eigenvalue_re_pos (z : ℂ) (v : Fin 3 → ℂ) (hv : v ≠ 0) (h : (A ℂ).mulVec v = z • v) :
    0 < z.re :=
  charpoly_root_re_pos z (eigen_charpoly z v hv h)

/-- Todo autovalor real de `A` es positivo. -/
theorem real_eigenvalue_pos (r : ℝ) (v : Fin 3 → ℝ) (hv : v ≠ 0) (h : (A ℝ).mulVec v = r • v) :
    0 < r := by
  have := eigen_charpoly r v hv h
  nlinarith [sq_nonneg (r - 3), sq_nonneg r]

/-- La matriz `A` es simétrica y su forma cuadrática es definida positiva:
`xᵀ A x ≥ ‖x‖² / 10`. -/
theorem quadratic_form_lower (x : Fin 3 → ℝ) :
    (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) / 10 ≤ x ⬝ᵥ (A ℝ).mulVec x := by
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three, A]
  nlinarith [sq_nonneg (9 * x 0 - 10 * x 1 + 10 * x 2), sq_nonneg (71 * x 1 + 100 * x 2),
    sq_nonneg (x 1 + x 2), sq_nonneg (x 2)]

section Solution

variable (X : ℝ → Fin 3 → ℝ)

/-- El cuadrado de la distancia del fragmento a la ISS (situada en el origen). -/
noncomputable def sqDist (t : ℝ) : ℝ := X t 0 ^ 2 + X t 1 ^ 2 + X t 2 ^ 2

theorem sqDist_pos_of_ne (h0 : X 0 ≠ 0) : 0 < sqDist X 0 := by
  rcases Function.ne_iff.1 h0 with ⟨i, hi⟩
  simp only [Pi.zero_apply] at hi
  simp only [sqDist]
  fin_cases i <;> positivity

variable (hX : ∀ t i, HasDerivAt (fun s => X s i) ((A ℝ).mulVec (X t) i) t)

include hX

theorem hasDerivAt_sqDist (t : ℝ) :
    HasDerivAt (sqDist X) (2 * (X t ⬝ᵥ (A ℝ).mulVec (X t))) t := by
  have h0 := (hX t 0).pow 2
  have h1 := (hX t 1).pow 2
  have h2 := (hX t 2).pow 2
  have h := (h0.add h1).add h2
  have h_eq : 2 * (X t ⬝ᵥ (A ℝ).mulVec (X t)) =
      (2 : ℝ) * X t 0 ^ (2 - 1) * (A ℝ).mulVec (X t) 0 +
      (2 : ℝ) * X t 1 ^ (2 - 1) * (A ℝ).mulVec (X t) 1 +
      (2 : ℝ) * X t 2 ^ (2 - 1) * (A ℝ).mulVec (X t) 2 := by
    simp [dotProduct, Fin.sum_univ_three]
    ring
  rw [h_eq]
  exact h

/-- **Parte 2 (crecimiento exponencial).** Toda solución de `X' = A X` satisface
`‖X t‖² ≥ ‖X 0‖² e^{t/5}` para todo `t ≥ 0`. -/
theorem sqDist_ge (t : ℝ) (ht : 0 ≤ t) : sqDist X 0 * Real.exp (t / 5) ≤ sqDist X t := by
  set g : ℝ → ℝ := fun s => sqDist X s * Real.exp (-(s / 5)) with hg
  have hgd : ∀ s, HasDerivAt g
      ((2 * (X s ⬝ᵥ (A ℝ).mulVec (X s)) - sqDist X s / 5) * Real.exp (-(s / 5))) s := by
    intro s
    have h1 := hasDerivAt_sqDist X hX s
    have hlin : HasDerivAt (fun u : ℝ => -(u / 5)) (-(1 / 5 : ℝ)) s := by
      have := (hasDerivAt_id s).div_const 5 |>.neg
      exact this
    have h2 : HasDerivAt (fun u : ℝ => Real.exp (-(u / 5)))
        (Real.exp (-(s / 5)) * (-(1 / 5 : ℝ))) s := by
      exact HasDerivAt.comp s (Real.hasDerivAt_exp (-(s / 5))) hlin
    have h := h1.mul h2
    have heq : 2 * (X s ⬝ᵥ (A ℝ).mulVec (X s)) * Real.exp (-(s / 5)) +
        sqDist X s * (Real.exp (-(s / 5)) * -(1 / 5)) =
        (2 * (X s ⬝ᵥ (A ℝ).mulVec (X s)) - sqDist X s / 5) * Real.exp (-(s / 5)) := by
      ring
    rw [heq] at h
    exact h
  have hmono : Monotone g := by
    apply monotone_of_deriv_nonneg
    · exact fun s => (hgd s).differentiableAt
    · intro s
      rw [(hgd s).deriv]
      have hq := quadratic_form_lower (X s)
      have hle : sqDist X s / 5 ≤ 2 * (X s ⬝ᵥ (A ℝ).mulVec (X s)) := by
        simp only [sqDist]; linarith
      have hexp := Real.exp_pos (-(s / 5))
      nlinarith
  have h := hmono ht
  simp only [hg] at h
  rw [show ((0 : ℝ) / 5) = 0 by ring, neg_zero, Real.exp_zero, mul_one] at h
  calc sqDist X 0 * Real.exp (t / 5)
      ≤ (sqDist X t * Real.exp (-(t / 5))) * Real.exp (t / 5) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = sqDist X t := by
        rw [mul_assoc, ← Real.exp_add]
        have : -(t / 5) + t / 5 = 0 := by ring
        rw [this, Real.exp_zero, mul_one]

/-- **Parte 2 (no hay colisión).** Si en el instante inicial el fragmento no está en la
ISS, entonces nunca la alcanza. -/
theorem no_collision (h0 : X 0 ≠ 0) (t : ℝ) (ht : 0 ≤ t) : X t ≠ 0 := by
  intro hc
  have hpos := sqDist_pos_of_ne X h0
  have h := sqDist_ge X hX t ht
  have : sqDist X t = 0 := by simp [sqDist, hc]
  nlinarith [Real.exp_pos (t / 5)]

/-- **Parte 2 (repulsor).** La distancia del fragmento a la ISS tiende a infinito. -/
theorem tendsto_sqDist_atTop (h0 : X 0 ≠ 0) : Tendsto (sqDist X) atTop atTop := by
  have hpos := sqDist_pos_of_ne X h0
  have hexp : Tendsto (fun t : ℝ => sqDist X 0 * Real.exp (t / 5)) atTop atTop :=
    Tendsto.const_mul_atTop hpos
      (Real.tendsto_exp_atTop.comp (Filter.tendsto_id.atTop_div_const (by norm_num)))
  refine tendsto_atTop_mono' _ ?_ hexp
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht using sqDist_ge X hX t ht

end Solution

end ISS
