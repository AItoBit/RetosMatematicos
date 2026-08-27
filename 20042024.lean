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
# Retos Matemáticos (ISSN: 2952–0746), 20 de abril de 2024

**Enunciado.** Dado `p(x) = a₀ + a₁x + ⋯ + a_m x^m` un polinomio de coeficientes reales, y el
operador `λ` tal que `λ(p) = a₀² + a₁² + ⋯ + a_m²`, y dado `F(x) = 3x² + 7x + 2`, encuéntrese un
polinomio `g(x)` de coeficientes reales tal que:

* i) `g(0) = 1`,
* ii) `λ(Fⁿ) = λ(gⁿ)` para todo número natural `n ≥ 1`.

**Solución.** `g(x) = 6x² + 5x + 1`.

La demostración formalizada utiliza la identidad `λ(p) = [xᵈ](p(x) · p*(x))`, donde
`p*(x) = xᵈ p(1/x)` es el polinomio con coeficientes en orden invertido (`Polynomial.reflect d`),
válida para cualquier `d ≥ deg(p)`. Como `F(x) · F*(x) = (3x+1)(x+2)(2x+1)(x+3) = g(x) · g*(x)`,
se obtiene `(Fⁿ) · (Fⁿ)* = (F · F*)ⁿ = (g · g*)ⁿ = (gⁿ) · (gⁿ)*`, y por consiguiente
`λ(Fⁿ) = λ(gⁿ)`.
-/

namespace RetosMatematicos

open Polynomial

/-- El operador `λ`: suma de los cuadrados de los coeficientes de un polinomio real. -/
noncomputable def lam (p : ℝ[X]) : ℝ := ∑ i ∈ p.support, (p.coeff i) ^ 2

/-- `λ(p)` expresado como suma sobre cualquier rango que contenga al soporte de `p`. -/
lemma lam_eq_sum_range {p : ℝ[X]} {d : ℕ} (hp : p.natDegree ≤ d) :
    lam p = ∑ i ∈ Finset.range (d + 1), (p.coeff i) ^ 2 := by
  refine Finset.sum_subset ?_ ?_
  · intro i hi
    simp only [Finset.mem_range]
    exact Nat.lt_succ_of_le ((le_natDegree_of_ne_zero (mem_support_iff.mp hi)).trans hp)
  · intro i _ hi
    simp [Polynomial.notMem_support_iff.mp hi]

/-- Identidad clave: `λ(p)` es el coeficiente de `x^d` en `p(x) · p*(x)`, donde `p*` es el
polinomio reflejado de grado `d ≥ deg(p)`. -/
lemma lam_eq_coeff_mul_reflect {p : ℝ[X]} {d : ℕ} (hp : p.natDegree ≤ d) :
    lam p = (p * Polynomial.reflect d p).coeff d := by
  rw [lam_eq_sum_range hp, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => p.coeff i * (Polynomial.reflect d p).coeff j)]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hid : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [coeff_reflect, revAt_le (Nat.sub_le d i), Nat.sub_sub_self hid, sq]

/-- El polinomio reflejado de una potencia es la potencia del polinomio reflejado. -/
lemma reflect_pow {p : ℝ[X]} {d : ℕ} (hp : p.natDegree ≤ d) (n : ℕ) :
    Polynomial.reflect (n * d) (p ^ n) = (Polynomial.reflect d p) ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
      have hk : (p ^ k).natDegree ≤ k * d :=
        (natDegree_pow_le).trans (Nat.mul_le_mul_left k hp)
      have : (k + 1) * d = d + k * d := by ring
      rw [this, pow_succ' p k, Polynomial.reflect_mul p (p ^ k) hp hk, ih, pow_succ' _ k]

/-! ## Definición de los polinomios `F` y `g` -/

/-- El polinomio dado en el enunciado: `F(x) = 3x² + 7x + 2`. -/
noncomputable def F : ℝ[X] := 3 * X ^ 2 + 7 * X + 2

/-- El polinomio solución: `g(x) = 6x² + 5x + 1`. -/
noncomputable def g : ℝ[X] := 6 * X ^ 2 + 5 * X + 1

lemma natDegree_F : F.natDegree = 2 := by
  unfold F
  compute_degree!

lemma natDegree_g : g.natDegree = 2 := by
  unfold g
  compute_degree!

/-- Reflejo de `F(x)` respecto a grado 2: `F*(x) = 2x² + 7x + 3`. -/
lemma reflect_F : Polynomial.reflect 2 F = 2 * X ^ 2 + 7 * X + 3 := by
  ext m
  rw [coeff_reflect]
  unfold F
  rcases m with _ | _ | _ | m
  · have h : revAt 2 0 = 2 := revAt_le (by omega)
    rw [h]
    simp [coeff_X, coeff_X_pow]
  · have h : revAt 2 1 = 1 := revAt_le (by omega)
    rw [h]
    simp [coeff_X, coeff_X_pow]
  · have h : revAt 2 2 = 0 := revAt_le (by omega)
    rw [h]
    simp [coeff_X, coeff_X_pow]
  · have h : revAt 2 (m + 3) = m + 3 := revAt_eq_self_of_lt (by omega)
    rw [h]
    simp [coeff_X, coeff_X_pow]

/-- Reflejo de `g(x)` respecto a grado 2: `g*(x) = x² + 5x + 6`. -/
lemma reflect_g : Polynomial.reflect 2 g = X ^ 2 + 5 * X + 6 := by
  ext m
  rw [coeff_reflect]
  unfold g
  rcases m with _ | _ | _ | m
  · have h : revAt 2 0 = 2 := revAt_le (by omega)
    rw [h]
    simp [coeff_X, coeff_X_pow, coeff_one]
  · have h : revAt 2 1 = 1 := revAt_le (by omega)
    rw [h]
    simp [coeff_X, coeff_X_pow, coeff_one]
  · have h : revAt 2 2 = 0 := revAt_le (by omega)
    rw [h]
    simp [coeff_X, coeff_X_pow, coeff_one]
  · have h : revAt 2 (m + 3) = m + 3 := revAt_eq_self_of_lt (by omega)
    rw [h]
    simp [coeff_X, coeff_X_pow, coeff_one]

/-- Núcleo del argumento: `F(x) · F*(x) = g(x) · g*(x) = 6x⁴ + 35x³ + 62x² + 35x + 6`. -/
lemma F_mul_reflect_F : F * Polynomial.reflect 2 F = g * Polynomial.reflect 2 g := by
  rw [reflect_F, reflect_g]
  unfold F g
  ring

/-! ## Demostración de las condiciones del enunciado -/

/-- Condición i): `g(0) = 1`. -/
theorem g_eval_zero : g.eval 0 = 1 := by
  simp [g]

/-- Condición ii): `λ(Fⁿ) = λ(gⁿ)` para todo `n ≥ 1`. -/
theorem lam_pow_F_eq_lam_pow_g (n : ℕ) (_hn : 1 ≤ n) : lam (F ^ n) = lam (g ^ n) := by
  have hF : (F ^ n).natDegree ≤ n * 2 :=
    natDegree_pow_le.trans (by rw [natDegree_F])
  have hg : (g ^ n).natDegree ≤ n * 2 :=
    natDegree_pow_le.trans (by rw [natDegree_g])
  rw [lam_eq_coeff_mul_reflect hF, lam_eq_coeff_mul_reflect hg,
    reflect_pow (le_of_eq natDegree_F) n, reflect_pow (le_of_eq natDegree_g) n,
    ← mul_pow, ← mul_pow, F_mul_reflect_F]

/-- **Teorema principal:** Existe un polinomio real `q` que satisface las dos condiciones
del reto: `q(0) = 1` y `λ(Fⁿ) = λ(qⁿ)` para todo `n ≥ 1`. -/
theorem exists_g :
    ∃ q : ℝ[X], q.eval 0 = 1 ∧ ∀ n : ℕ, 1 ≤ n → lam (F ^ n) = lam (q ^ n) :=
  ⟨g, g_eval_zero, lam_pow_F_eq_lam_pow_g⟩

/-- Comprobación aritmética para el caso `n = 1`:
`λ(F) = 3² + 7² + 2² = 62 = 6² + 5² + 1² = λ(g)`. -/
example : lam F = 62 ∧ lam g = 62 := by
  constructor
  · rw [lam_eq_sum_range (le_of_eq natDegree_F)]
    simp [F, Finset.sum_range_succ, coeff_X, coeff_X_pow]
    norm_num
  · rw [lam_eq_sum_range (le_of_eq natDegree_g)]
    simp [g, Finset.sum_range_succ, coeff_X, coeff_X_pow, coeff_one]
    norm_num

end RetosMatematicos
