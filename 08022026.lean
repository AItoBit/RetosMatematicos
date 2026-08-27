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
# Retos Matemáticos — 8 de febrero de 2026

**Ejercicio.** Hállese, si existe, el logaritmo de la matriz
`A = !![2, 1, 0; 0, 2, 1; 0, 0, 2]`.

**Solución.** Escribiendo `A = 2 I + N`, con `N` nilpotente de índice 3, la serie
del logaritmo se trunca y `log A = (log 2) I + N/2 - N²/8`, es decir
```
log A = !![log 2, 1/2, -1/8; 0, log 2, 1/2; 0, 0, log 2].
```

Se formalizan: la solución general para un bloque de Jordan (`2ª forma`), la
expresión polinómica en `A - 2I` (`3ª forma`) y la comprobación
`exp (log A) = A` (nota adicional), que es el sentido preciso en el que la
matriz obtenida es un logaritmo de `A`.
-/

namespace RetosMatematicos08022026

open Matrix NormedSpace

/-! ## Lemas auxiliares sobre matrices nilpotentes de índice 3 -/

/-- Si `M³ = 0`, entonces `(a M - b M²)² = a² M²`. -/
theorem sq_smul_sub_smul_sq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (a b : ℝ)
    (hM : M ^ 3 = 0) : (a • M - b • M ^ 2) ^ 2 = (a * a) • M ^ 2 := by
  have h3 : M * M * M = 0 := by rw [← pow_two, ← pow_succ]; exact hM
  have h3' : M * (M * M) = 0 := by rw [← mul_assoc]; exact h3
  have h4 : M * M * (M * M) = 0 := by rw [← mul_assoc, h3, zero_mul]
  rw [pow_two, sub_mul, mul_sub, mul_sub, pow_two M]
  simp only [Matrix.smul_mul, Matrix.mul_smul, h3, h3', h4, smul_zero, sub_zero,
    smul_smul, sub_self]

/-- Si `M³ = 0`, entonces `(a M - b M²)³ = 0`. -/
theorem cube_smul_sub_smul_sq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (a b : ℝ)
    (hM : M ^ 3 = 0) : (a • M - b • M ^ 2) ^ 3 = 0 := by
  have hM2M : M ^ 2 * M = 0 := by rw [← pow_succ]; exact hM
  have hM4 : M ^ 2 * M ^ 2 = 0 := by
    rw [← pow_add, show 2 + 2 = 3 + 1 from rfl, pow_add, hM, zero_mul]
  rw [pow_succ, sq_smul_sub_smul_sq M a b hM, mul_sub]
  simp only [Matrix.smul_mul, Matrix.mul_smul, hM2M, hM4, smul_zero, sub_zero]

/-- Para una matriz de cubo nulo la serie exponencial se trunca:
`exp X = I + X + X²/2`. -/
theorem exp_of_cube_eq_zero {n : ℕ} (x : Matrix (Fin n) (Fin n) ℝ) (hx : x ^ 3 = 0) :
    exp x = 1 + x + (2 : ℝ)⁻¹ • x ^ 2 := by
  rw [exp_eq_tsum ℝ]
  simp only
  rw [tsum_eq_sum (s := Finset.range 3) ?_]
  · simp [Finset.sum_range_succ]
  · intro k hk
    simp only [Finset.mem_range, not_lt] at hk
    have hxk : x ^ k = 0 := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
      rw [pow_add, hx, zero_mul]
    simp [hxk]

/-- `exp (c I) = e^c I`. -/
theorem exp_smul_one {n : ℕ} (c : ℝ) :
    exp ((c • 1 : Matrix (Fin n) (Fin n) ℝ)) = (Real.exp c) • 1 := by
  have h : (c • 1 : Matrix (Fin n) (Fin n) ℝ) = diagonal (fun _ => c) := by
    ext i j; by_cases hij : i = j <;> simp [hij]
  rw [h, Matrix.exp_diagonal]
  ext i j
  by_cases hij : i = j <;> simp [hij, ← Real.exp_eq_exp_ℝ]

/-! ## 2ª forma: logaritmo de un bloque de Jordan -/

/-- **2ª forma.** Si `M` es nilpotente con `M³ = 0` y `l > 0`, entonces
`log l · I + M/l - M²/(2 l²)` es un logaritmo del bloque de Jordan `l I + M`. -/
theorem exp_jordan_log {n : ℕ} (l : ℝ) (hl : 0 < l) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M ^ 3 = 0) :
    exp (Real.log l • 1 + (l⁻¹ • M - (2 * l ^ 2)⁻¹ • M ^ 2)) = l • 1 + M := by
  have hcomm : Commute (Real.log l • (1 : Matrix (Fin n) (Fin n) ℝ))
      (l⁻¹ • M - (2 * l ^ 2)⁻¹ • M ^ 2) := (Commute.one_left _).smul_left _
  have hscal : (2 : ℝ)⁻¹ * (l⁻¹ * l⁻¹) = (2 * l ^ 2)⁻¹ := by
    rw [sq, ← mul_inv, ← mul_inv]
  have hkey : (l⁻¹ • M - (2 * l ^ 2)⁻¹ • M ^ 2)
      + (2 : ℝ)⁻¹ • (l⁻¹ • M - (2 * l ^ 2)⁻¹ • M ^ 2) ^ 2 = l⁻¹ • M := by
    rw [sq_smul_sub_smul_sq M _ _ hM, smul_smul, hscal, sub_add_cancel]
  rw [Matrix.exp_add_of_commute _ _ hcomm, exp_smul_one,
    exp_of_cube_eq_zero _ (cube_smul_sub_smul_sq M _ _ hM), Real.exp_log hl, add_assoc, hkey]
  rw [mul_add, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.one_mul,
    smul_smul, mul_inv_cancel₀ (ne_of_gt hl), one_smul]

/-! ## El ejercicio concreto -/

/-- La matriz del enunciado. -/
def A : Matrix (Fin 3) (Fin 3) ℝ := !![2, 1, 0; 0, 2, 1; 0, 0, 2]

/-- La parte nilpotente `N = A - 2 I`. -/
def N : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1, 0; 0, 0, 1; 0, 0, 0]

/-- El logaritmo de `A` obtenido en la solución. -/
noncomputable def logA : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.log 2, 1/2, -(1/8); 0, Real.log 2, 1/2; 0, 0, Real.log 2]

/-- `A = 2 I + N`. -/
theorem A_eq : A = (2 : ℝ) • 1 + N := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [A, N]

/-- `A - 2 I = N`. -/
theorem A_sub_two_smul_one : A - (2 : ℝ) • 1 = N := by rw [A_eq]; abel

/-- `N² = !![0,0,1; 0,0,0; 0,0,0]`. -/
theorem N_sq : N ^ 2 = !![0, 0, 1; 0, 0, 0; 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [N, pow_two, Matrix.mul_apply, Fin.sum_univ_succ]

/-- `N` es nilpotente: `N³ = 0`. -/
theorem N_cube : N ^ 3 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [N, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]

/-- `N² ≠ 0`: el índice de nilpotencia de `N` es exactamente 3. -/
theorem N_sq_ne_zero : N ^ 2 ≠ 0 := by
  intro h
  have h1 : (N ^ 2) 0 2 = 1 := by
    rw [N_sq]; norm_num [Matrix.cons_val_two, Matrix.tail_cons]
  rw [h] at h1
  norm_num at h1

/-- **3ª forma.** `log A = log 2 · I + (A - 2I)/2 - (A - 2I)²/8`. -/
theorem logA_eq_poly :
    logA = Real.log 2 • 1 + (2 : ℝ)⁻¹ • (A - (2 : ℝ) • 1)
      - (8 : ℝ)⁻¹ • (A - (2 : ℝ) • 1) ^ 2 := by
  rw [A_sub_two_smul_one, N_sq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [logA, N]

/-- `log A = log 2 · I + N/2 - N²/(2 · 2²)`, la forma que usa la 1ª solución. -/
theorem logA_eq_smul :
    logA = Real.log 2 • 1 + ((2 : ℝ)⁻¹ • N - (2 * (2 : ℝ) ^ 2)⁻¹ • N ^ 2) := by
  rw [logA_eq_poly, A_sub_two_smul_one]
  norm_num
  abel

/-- **Resultado principal (nota adicional).** `exp (log A) = A`: la matriz `logA`
del enunciado es efectivamente un logaritmo de `A`. -/
theorem exp_logA : exp logA = A := by
  rw [logA_eq_smul, exp_jordan_log 2 (by norm_num) N N_cube, A_eq]

end RetosMatematicos08022026
