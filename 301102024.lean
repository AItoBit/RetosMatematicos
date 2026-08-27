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
# Suneung (Corea del Sur) 1996, ejercicio 13

En la figura, los rectángulos `AODB` y `OFGD` son congruentes, y también lo son
`BDEC` y `DGHE`.  Eligiendo coordenadas cartesianas con origen en `O`, esto
equivale a tomar, para ciertos parámetros reales `a`, `b`, `c`:

`A = (0, a)`, `B = (b, a)`, `C = (c, a)`, `O = (0, 0)`, `D = (b, 0)`,
`E = (c, 0)`, `F = (0, -a)`, `G = (b, -a)`, `H = (c, -a)`.

Una transformación lineal `T` del plano envía `B` a `E` y `D` a `A`.
Se pide la imagen de `A`; la respuesta es la opción (5), el punto `H`.
-/

namespace Suneung1996

/-- El punto `A = (0, a)`. -/
def ptA (a : ℝ) : ℝ × ℝ := (0, a)

/-- El punto `B = (b, a)`. -/
def ptB (a b : ℝ) : ℝ × ℝ := (b, a)

/-- El punto `C = (c, a)`. -/
def ptC (a c : ℝ) : ℝ × ℝ := (c, a)

/-- El origen `O = (0, 0)`. -/
def ptO : ℝ × ℝ := (0, 0)

/-- El punto `D = (b, 0)`. -/
def ptD (b : ℝ) : ℝ × ℝ := (b, 0)

/-- El punto `E = (c, 0)`. -/
def ptE (c : ℝ) : ℝ × ℝ := (c, 0)

/-- El punto `F = (0, -a)`. -/
def ptF (a : ℝ) : ℝ × ℝ := (0, -a)

/-- El punto `G = (b, -a)`. -/
def ptG (a b : ℝ) : ℝ × ℝ := (b, -a)

/-- El punto `H = (c, -a)`. -/
def ptH (a c : ℝ) : ℝ × ℝ := (c, -a)

/-- Relación clave de la figura: `B = D + A`, es decir, `A = B - D`. -/
theorem ptA_eq_ptB_sub_ptD (a b : ℝ) : ptA a = ptB a b - ptD b := by
  simp [ptA, ptB, ptD]

/-- **Solución (2ª forma).** Si una transformación lineal `T` del plano cumple
`T B = E` y `T D = A`, entonces la imagen de `A` es el punto `H`. -/
theorem image_ptA (a b c : ℝ) (T : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))
    (hB : T (ptB a b) = ptE c) (hD : T (ptD b) = ptA a) :
    T (ptA a) = ptH a c := by
  rw [ptA_eq_ptB_sub_ptD a b, map_sub, hB, hD]
  simp [ptE, ptA, ptH]

/-- **Solución (3ª forma).** Cuando la figura es no degenerada (`a ≠ 0`, `b ≠ 0`),
la transformación lineal está determinada: `T (x, y) = (c y / a, a x / b - y)`. -/
theorem eq_of_linear (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (T : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))
    (hB : T (ptB a b) = ptE c) (hD : T (ptD b) = ptA a) (x y : ℝ) :
    T (x, y) = (c * y / a, a * x / b - y) := by
  have h1 : x / b * b = x := div_mul_cancel₀ x hb
  have h2 : y / a * a = y := div_mul_cancel₀ y ha
  have hbase : ((x, y) : ℝ × ℝ) = (x / b) • ptD b + (y / a) • ptA a := by
    simp [ptD, ptA, h1, h2]
  have hA : T (ptA a) = ptH a c := image_ptA a b c T hB hD
  rw [hbase, map_add, map_smul, map_smul, hD, hA]
  simp only [ptA, ptH, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, Prod.mk.injEq]
  constructor
  · field_simp; ring
  · field_simp; ring

/-- La respuesta correcta es la opción (5): en una figura no degenerada, la
imagen de `A` es `H` y no coincide con ninguna de las otras opciones
`B`, `C`, `F`, `G`. -/
theorem image_ptA_eq_ptH_and_ne (a b c : ℝ) (ha : a ≠ 0)
    (hc : c ≠ 0) (hbc : b ≠ c) (T : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))
    (hB : T (ptB a b) = ptE c) (hD : T (ptD b) = ptA a) :
    T (ptA a) = ptH a c ∧ T (ptA a) ≠ ptB a b ∧ T (ptA a) ≠ ptC a c ∧
      T (ptA a) ≠ ptF a ∧ T (ptA a) ≠ ptG a b := by
  have hA : T (ptA a) = ptH a c := image_ptA a b c T hB hD
  refine ⟨hA, ?_, ?_, ?_, ?_⟩ <;> rw [hA] <;> intro h <;>
    rw [Prod.ext_iff] at h <;> obtain ⟨hx, hy⟩ := h
  · exact ha (by simp only [ptH, ptB] at hy; linarith)
  · exact ha (by simp only [ptH, ptC] at hy; linarith)
  · exact hc (by simpa only [ptH, ptF] using hx)
  · exact hbc (by simpa only [ptH, ptG] using hx.symm)

open Matrix in
/-- **Solución (1ª forma), versión matricial.** Con `a ≠ 0` y `b ≠ 0`, la matriz
`M = !![0, c/a; a/b, -1]` envía `B` a `E` y `D` a `A`, y su acción sobre `A`
da el punto `H`. -/
theorem matrix_image_ptA (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (!![0, c / a; a / b, -1] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![b, a] = ![c, 0] ∧
    (!![0, c / a; a / b, -1] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![b, 0] = ![0, a] ∧
    (!![0, c / a; a / b, -1] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![0, a] = ![c, -a] := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · funext i
      fin_cases i <;>
        simp [Matrix.mulVec] <;> field_simp <;> ring

end Suneung1996

#print axioms Suneung1996.image_ptA
#print axioms Suneung1996.eq_of_linear
#print axioms Suneung1996.image_ptA_eq_ptH_and_ne
#print axioms Suneung1996.matrix_image_ptA
