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
# Identidad de Weinstein–Aronszajn

Formalización del boletín de *Retos Matemáticos* del 9 de marzo de 2023.

## Ejercicio 1 (matrices cuadradas)

Sean `A, B ∈ Mₙ(ℝ)`. Se prueba `det (I + A * B) = det (I + B * A)` siguiendo los pasos:

* (a) `GLₙ(ℝ) = {A : det A ≠ 0}` es denso en `Mₙ(ℝ)`;
* (b) la identidad cuando `A` es invertible;
* (c) el caso general, por densidad y continuidad.

## Ejercicio 2 (matrices rectangulares)

Sean `A ∈ M_{m×n}(ℝ)` y `B ∈ M_{n×m}(ℝ)`. Se prueba `det (Iₘ + A * B) = det (Iₙ + B * A)`
mediante las fórmulas del complemento de Schur para determinantes por bloques, y se deduce
`det (A * B - λ Iₘ) = (-λ)^(m-n) det (B * A - λ Iₙ)` para `λ ≠ 0`, así como la coincidencia
de los autovalores no nulos de `A * B` y `B * A`.
-/

namespace WeinsteinAronszajn

open Matrix Filter Topology

section Cuadradas

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Para `A ∈ Mₙ(ℝ)` y `t ∈ ℝ`, `det (A + t I)` es el valor en `t` del polinomio
característico de `-A`; en particular es una función polinómica de `t`. -/
theorem det_add_smul_one_eq_eval (A : Matrix n n ℝ) (t : ℝ) :
    (A + t • (1 : Matrix n n ℝ)).det = ((-A).charpoly).eval t := by
  rw [Matrix.eval_charpoly]
  congr 1
  rw [Matrix.smul_one_eq_diagonal]
  ext i j
  simp [Matrix.scalar, Matrix.diagonal]
  ring

/-- **Ejercicio 1 (a).** El grupo lineal `GLₙ(ℝ) = {A ∈ Mₙ(ℝ) : det A ≠ 0}` es denso en
`Mₙ(ℝ)` (con la topología usual, la de la identificación `Mₙ(ℝ) ≃ ℝ^{n²}`).

La demostración usa que `t ↦ det (A + t I)` es un polinomio mónico no nulo (el polinomio
característico de `-A`), luego tiene un número finito de raíces: así se puede elegir una
sucesión `tₖ → 0` con `A + tₖ I` invertible. -/
theorem dense_setOf_det_ne_zero :
    Dense {A : Matrix n n ℝ | A.det ≠ 0} := by
  intro A
  set p : Polynomial ℝ := (-A).charpoly
  have hpne : p ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  have key : ∀ k : ℕ, ∃ t : ℝ, 0 < t ∧ t < 1 / (k + 1) ∧ (A + t • (1 : Matrix n n ℝ)).det ≠ 0 := by
    intro k
    have hlt : (0:ℝ) < 1 / (k + 1) := by positivity
    obtain ⟨t, ht, htn⟩ := (Set.Ioo_infinite hlt).exists_notMem_finset p.roots.toFinset
    refine ⟨t, ht.1, ht.2, ?_⟩
    rw [det_add_smul_one_eq_eval]
    intro h
    exact htn (Multiset.mem_toFinset.2 ((Polynomial.mem_roots hpne).2 h))
  choose t ht0 ht1 ht2 using key
  have htend : Tendsto t atTop (𝓝 0) :=
    squeeze_zero (fun k => (ht0 k).le) (fun k => (ht1 k).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hcont : Continuous (fun s : ℝ => A + s • (1 : Matrix n n ℝ)) := by fun_prop
  have hlim : Tendsto (fun k => A + t k • (1 : Matrix n n ℝ)) atTop (𝓝 A) := by
    simpa [Function.comp_def] using (hcont.tendsto 0).comp htend
  exact mem_closure_of_tendsto hlim (Eventually.of_forall (fun k => ht2 k))

/-- **Ejercicio 1 (b).** La identidad de Weinstein–Aronszajn para `A` invertible:
`I + AB = A (A⁻¹ + B)` y `I + BA = (A⁻¹ + B) A`. -/
theorem det_one_add_mul_comm_of_det_ne_zero (A B : Matrix n n ℝ) (hA : A.det ≠ 0) :
    (1 + A * B).det = (1 + B * A).det := by
  have hu : IsUnit A.det := isUnit_iff_ne_zero.2 hA
  have h1 : (1 : Matrix n n ℝ) + A * B = A * (A⁻¹ + B) := by
    rw [Matrix.mul_add, Matrix.mul_nonsing_inv A hu]
  have h2 : (1 : Matrix n n ℝ) + B * A = (A⁻¹ + B) * A := by
    rw [Matrix.add_mul, Matrix.nonsing_inv_mul A hu]
  rw [h1, h2, Matrix.det_mul, Matrix.det_mul, mul_comm]

/-- **Ejercicio 1 (c).** La identidad de Weinstein–Aronszajn `det (I + AB) = det (I + BA)`
para matrices cuadradas reales arbitrarias: ambos miembros son funciones continuas de `A`
que coinciden en el subconjunto denso `GLₙ(ℝ)`. -/
theorem det_one_add_mul_comm_square (A B : Matrix n n ℝ) :
    (1 + A * B).det = (1 + B * A).det := by
  have hf : Continuous (fun X : Matrix n n ℝ => (1 + X * B).det) :=
    (continuous_const.add (continuous_id.matrix_mul continuous_const)).matrix_det
  have hg : Continuous (fun X : Matrix n n ℝ => (1 + B * X).det) :=
    (continuous_const.add (continuous_const.matrix_mul continuous_id)).matrix_det
  exact congrFun
    (Continuous.ext_on dense_setOf_det_ne_zero hf hg
      (fun X hX => det_one_add_mul_comm_of_det_ne_zero X B hX)) A

end Cuadradas

section Rectangulares

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- **Ejercicio 2 (a) (1).** Fórmula del complemento de Schur: si `P` es invertible,
`det M = det P * det (S - R P⁻¹ Q)` para la matriz por bloques `M = [[P, Q], [R, S]]`. -/
theorem det_fromBlocks_of_det_ne_zero₁₁
    (P : Matrix m m ℝ) (Q : Matrix m n ℝ) (R : Matrix n m ℝ) (S : Matrix n n ℝ)
    (hP : P.det ≠ 0) :
    (fromBlocks P Q R S).det = P.det * (S - R * P⁻¹ * Q).det := by
  have : Invertible P := P.invertibleOfIsUnitDet (isUnit_iff_ne_zero.2 hP)
  rw [Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]

/-- **Ejercicio 2 (a) (2).** Fórmula del complemento de Schur: si `S` es invertible,
`det M = det S * det (P - Q S⁻¹ R)` para la matriz por bloques `M = [[P, Q], [R, S]]`. -/
theorem det_fromBlocks_of_det_ne_zero₂₂
    (P : Matrix m m ℝ) (Q : Matrix m n ℝ) (R : Matrix n m ℝ) (S : Matrix n n ℝ)
    (hS : S.det ≠ 0) :
    (fromBlocks P Q R S).det = S.det * (P - Q * S⁻¹ * R).det := by
  have : Invertible S := S.invertibleOfIsUnitDet (isUnit_iff_ne_zero.2 hS)
  rw [Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv]

/-- **Ejercicio 2 (b).** Identidad de Weinstein–Aronszajn general:
`det (Iₘ + A B) = det (Iₙ + B A)` para `A` de tamaño `m × n` y `B` de tamaño `n × m`.
Se aplican las dos fórmulas del apartado (a) a la matriz `M = [[Iₘ, -A], [B, Iₙ]]`. -/
theorem det_one_add_mul_comm_rect (A : Matrix m n ℝ) (B : Matrix n m ℝ) :
    (1 + A * B).det = (1 + B * A).det := by
  have h1 := det_fromBlocks_of_det_ne_zero₁₁ (1 : Matrix m m ℝ) (-A) B (1 : Matrix n n ℝ) (by simp)
  have h2 := det_fromBlocks_of_det_ne_zero₂₂ (1 : Matrix m m ℝ) (-A) B (1 : Matrix n n ℝ) (by simp)
  rw [h1] at h2
  simpa [sub_eq_add_neg, Matrix.mul_neg, Matrix.neg_mul] using h2.symm

/-- Versión auxiliar de **Ejercicio 2 (c)** sin exponentes negativos:
`det (AB - λIₘ) · (-λ)ⁿ = (-λ)ᵐ · det (BA - λIₙ)`. -/
theorem det_sub_smul_one_mul_pow (A : Matrix m n ℝ) (B : Matrix n m ℝ) {lam : ℝ} (hlam : lam ≠ 0) :
    (A * B - lam • (1 : Matrix m m ℝ)).det * (-lam) ^ (Fintype.card n)
      = (-lam) ^ (Fintype.card m) * (B * A - lam • (1 : Matrix n n ℝ)).det := by
  have hll : (-lam * lam⁻¹) = -1 := by field_simp
  have e1 : A * B - lam • (1 : Matrix m m ℝ)
      = (-lam) • ((1 : Matrix m m ℝ) + (-(lam⁻¹ • A)) * B) := by
    rw [Matrix.neg_mul, Matrix.smul_mul, smul_add, smul_neg, smul_smul, hll]
    simp [neg_smul, sub_eq_add_neg]
    abel
  have e2 : B * A - lam • (1 : Matrix n n ℝ)
      = (-lam) • ((1 : Matrix n n ℝ) + B * (-(lam⁻¹ • A))) := by
    rw [Matrix.mul_neg, Matrix.mul_smul, smul_add, smul_neg, smul_smul, hll]
    simp [neg_smul, sub_eq_add_neg]
    abel
  rw [e1, e2, Matrix.det_smul, Matrix.det_smul, det_one_add_mul_comm_rect (-(lam⁻¹ • A)) B]
  ring

/-- **Ejercicio 2 (c).** Para `λ ≠ 0`, `det (AB - λIₘ) = (-λ)^{m-n} det (BA - λIₙ)`
(exponente entero, posiblemente negativo). -/
theorem det_sub_smul_one_comm (A : Matrix m n ℝ) (B : Matrix n m ℝ) {lam : ℝ} (hlam : lam ≠ 0) :
    (A * B - lam • (1 : Matrix m m ℝ)).det
      = (-lam) ^ ((Fintype.card m : ℤ) - (Fintype.card n : ℤ))
        * (B * A - lam • (1 : Matrix n n ℝ)).det := by
  have hc : (-lam) ≠ 0 := neg_ne_zero.mpr hlam
  have h := det_sub_smul_one_mul_pow A B hlam
  rw [zpow_sub₀ hc, zpow_natCast, zpow_natCast]
  field_simp
  linear_combination h

/-- **Ejercicio 2 (c), consecuencia.** Los autovalores no nulos de `A * B` y de `B * A`
coinciden: para `λ ≠ 0`, `λ` es autovalor de `A * B` si, y sólo si, lo es de `B * A`. -/
theorem det_sub_smul_one_eq_zero_iff (A : Matrix m n ℝ) (B : Matrix n m ℝ) {lam : ℝ}
    (hlam : lam ≠ 0) :
    (A * B - lam • (1 : Matrix m m ℝ)).det = 0 ↔ (B * A - lam • (1 : Matrix n n ℝ)).det = 0 := by
  have hc : (-lam) ≠ 0 := neg_ne_zero.mpr hlam
  rw [det_sub_smul_one_comm A B hlam, mul_eq_zero]
  simp [zpow_ne_zero _ hc]

end Rectangulares

end WeinsteinAronszajn
