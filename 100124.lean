
import Mathlib

set_option exponentiation.threshold 10000

/-!
# Infinitos enteros positivos no representables como `a³ + b⁵ + c⁷ + d⁹ + e¹¹`

**Ejercicio.** ¿Existen infinitos enteros positivos que no puedan representarse de la
forma `a³ + b⁵ + c⁷ + d⁹ + e¹¹`, donde `a, b, c, d, e` son enteros positivos?

*Propuesto en OME 2013, Fase Nacional, Bilbao.*

**Respuesta.** Sí: `infinitos_no_representables`.

## Estructura de la formalización (2ª Forma)

Se sigue la adaptación de la solución oficial. Con `3465 = 3·1155 = 5·693 = 7·495 =
9·385 = 11·315` (esto es, `3465 = lcm(3,5,7,9,11) = 5·7·9·11`):

* Si `a³ + b⁵ + c⁷ + d⁹ + e¹¹ ≤ N^3465` con todos los sumandos positivos, entonces
  `a ≤ N^1155`, `b ≤ N^693`, `c ≤ N^495`, `d ≤ N^385`, `e ≤ N^315`
  (`mem_image_of_repr`).
* Como `1155 + 693 + 495 + 385 + 315 = 3043`, hay a lo sumo `N^3043` valores
  representables `≤ N^3465` (`card_box`, `card_image_box`).
* Luego entre los primeros `N^3465` naturales hay más de
  `N^3465 − N^3043 > N^3464` no representables (`card_no_repr`).
* Al ser `N ≥ 2` arbitrario, el conjunto de no representables no está acotado
  (`exists_gt_not_repr`) y por tanto es infinito (`infinitos_no_representables`).
-/

namespace RetosMatematicos
namespace OME2013

/-- `Repr5 n` : el entero `n` se escribe como `a³ + b⁵ + c⁷ + d⁹ + e¹¹`
con `a, b, c, d, e` enteros positivos. -/
def Repr5 (n : ℕ) : Prop :=
  ∃ a b c d e : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ 0 < e ∧
    a ^ 3 + b ^ 5 + c ^ 7 + d ^ 9 + e ^ 11 = n

example : Repr5 5 := ⟨1, 1, 1, 1, 1, by decide⟩

/-! ## 1. Preliminares -/

/-- De `x^k ≤ y^k` (con `k ≠ 0`) se sigue `x ≤ y`. -/
private lemma le_of_pow_le_pow' {x y k : ℕ} (hk : k ≠ 0) (h : x ^ k ≤ y ^ k) : x ≤ y := by
  rcases le_or_gt x y with hle | hlt
  · exact hle
  · have := Nat.pow_lt_pow_left hlt hk
    omega

/-- La caja de tuplas `(a,b,c,d,e)` que pueden intervenir en una representación
de un número `≤ N^3465`. -/
private def box (N : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  Finset.Icc 1 (N ^ 1155) ×ˢ Finset.Icc 1 (N ^ 693) ×ˢ Finset.Icc 1 (N ^ 495) ×ˢ
    Finset.Icc 1 (N ^ 385) ×ˢ Finset.Icc 1 (N ^ 315)

/-- El valor `a³ + b⁵ + c⁷ + d⁹ + e¹¹` asociado a una tupla. -/
private def val (p : ℕ × ℕ × ℕ × ℕ × ℕ) : ℕ :=
  p.1 ^ 3 + p.2.1 ^ 5 + p.2.2.1 ^ 7 + p.2.2.2.1 ^ 9 + p.2.2.2.2 ^ 11

/-- `1155 + 693 + 495 + 385 + 315 = 3043`. -/
private lemma card_box (N : ℕ) : (box N).card = N ^ 3043 := by
  simp only [box, Finset.card_product, Nat.card_Icc, Nat.add_sub_cancel]
  repeat rw [← pow_add]
  rfl

private lemma card_image_box (N : ℕ) : ((box N).image val).card ≤ N ^ 3043 := by
  rw [← card_box N]
  exact Finset.card_image_le

/-- **Paso clave.** Todo número representable que sea `≤ N^3465` se obtiene de una
tupla de la caja: cada sumando es `≤ N^3465`, luego `a ≤ N^1155`, etc. -/
private lemma mem_image_of_repr {N n : ℕ} (hrep : Repr5 n) (hn : n ≤ N ^ 3465) :
    n ∈ (box N).image val := by
  obtain ⟨a, b, c, d, e, ha, hb, hc, hd, he, rfl⟩ := hrep
  have ha' : a ≤ N ^ 1155 := by
    refine le_of_pow_le_pow' (k := 3) (by decide) ?_
    calc a ^ 3 ≤ a ^ 3 + b ^ 5 + c ^ 7 + d ^ 9 + e ^ 11 := by omega
      _ ≤ N ^ 3465 := hn
      _ = (N ^ 1155) ^ 3 := by rw [← pow_mul]; rfl
  have hb' : b ≤ N ^ 693 := by
    refine le_of_pow_le_pow' (k := 5) (by decide) ?_
    calc b ^ 5 ≤ a ^ 3 + b ^ 5 + c ^ 7 + d ^ 9 + e ^ 11 := by omega
      _ ≤ N ^ 3465 := hn
      _ = (N ^ 693) ^ 5 := by rw [← pow_mul]; rfl
  have hc' : c ≤ N ^ 495 := by
    refine le_of_pow_le_pow' (k := 7) (by decide) ?_
    calc c ^ 7 ≤ a ^ 3 + b ^ 5 + c ^ 7 + d ^ 9 + e ^ 11 := by omega
      _ ≤ N ^ 3465 := hn
      _ = (N ^ 495) ^ 7 := by rw [← pow_mul]; rfl
  have hd' : d ≤ N ^ 385 := by
    refine le_of_pow_le_pow' (k := 9) (by decide) ?_
    calc d ^ 9 ≤ a ^ 3 + b ^ 5 + c ^ 7 + d ^ 9 + e ^ 11 := by omega
      _ ≤ N ^ 3465 := hn
      _ = (N ^ 385) ^ 9 := by rw [← pow_mul]; rfl
  have he' : e ≤ N ^ 315 := by
    refine le_of_pow_le_pow' (k := 11) (by decide) ?_
    calc e ^ 11 ≤ a ^ 3 + b ^ 5 + c ^ 7 + d ^ 9 + e ^ 11 := by omega
      _ ≤ N ^ 3465 := hn
      _ = (N ^ 315) ^ 11 := by rw [← pow_mul]; rfl
  refine Finset.mem_image.mpr ⟨(a, b, c, d, e), ?_, rfl⟩
  simp only [box, Finset.mem_product, Finset.mem_Icc]
  omega

/-! ## 2. El recuento -/

/-- **2ª Forma.** Para cada `N ≥ 2` hay más de `N^3464` enteros del intervalo
`[1, N^3465]` que no son representables. -/
theorem card_no_repr (N : ℕ) (hN : 2 ≤ N) :
    ∃ S : Finset ℕ, (∀ n ∈ S, 0 < n ∧ n ≤ N ^ 3465 ∧ ¬ Repr5 n) ∧ N ^ 3464 < S.card := by
  refine ⟨Finset.Icc 1 (N ^ 3465) \ (box N).image val, ?_, ?_⟩
  · intro n hn
    rw [Finset.mem_sdiff, Finset.mem_Icc] at hn
    exact ⟨hn.1.1, hn.1.2, fun hrep => hn.2 (mem_image_of_repr hrep hn.1.2)⟩
  · have hsub : Finset.Icc 1 (N ^ 3465) ⊆
        (Finset.Icc 1 (N ^ 3465) \ (box N).image val) ∪ (box N).image val := by
      intro x hx
      by_cases hxr : x ∈ (box N).image val
      · exact Finset.mem_union_right _ hxr
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hxr⟩)
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le
      (Finset.Icc 1 (N ^ 3465) \ (box N).image val) ((box N).image val)
    have h3 : (Finset.Icc 1 (N ^ 3465)).card = N ^ 3465 := by
      rw [Nat.card_Icc]; omega
    have h4 := card_image_box N
    -- `N^3465 ≥ 2·N^3464` y `N^3464 ≥ 2·N^3043`
    have e1 : N ^ 3464 * 2 ≤ N ^ 3465 := by
      calc N ^ 3464 * 2 ≤ N ^ 3464 * N := Nat.mul_le_mul le_rfl hN
        _ = N ^ (3464 + 1) := by rw [← pow_succ]
        _ = N ^ 3465 := rfl
    have e2 : N ^ 3043 * 2 ≤ N ^ 3464 := by
      have h : (2 : ℕ) ≤ N ^ 421 := le_trans hN (Nat.le_self_pow (by decide) N)
      calc N ^ 3043 * 2 ≤ N ^ 3043 * N ^ 421 := Nat.mul_le_mul le_rfl h
        _ = N ^ (3043 + 421) := by rw [← pow_add]
        _ = N ^ 3464 := rfl
    have e3 : 1 ≤ N ^ 3043 := Nat.one_le_pow _ _ (by omega)
    omega

/-! ## 3. Conclusión -/

/-- Hay enteros positivos no representables arbitrariamente grandes. -/
theorem exists_gt_not_repr (M : ℕ) : ∃ n, M < n ∧ 0 < n ∧ ¬ Repr5 n := by
  obtain ⟨S, hS, hcard⟩ := card_no_repr (M + 2) (by omega)
  by_contra hc
  have hcon : ∀ n, M < n → 0 < n → Repr5 n := by
    intro n hMn hn0
    by_contra hnr
    exact hc ⟨n, hMn, hn0, hnr⟩
  -- si no hubiera ninguno mayor que `M`, todo `S` cabría en `[1, M]`
  have hsub : S ⊆ Finset.Icc 1 M := by
    intro n hn
    obtain ⟨hn1, -, hn3⟩ := hS n hn
    rw [Finset.mem_Icc]
    refine ⟨hn1, ?_⟩
    by_contra hlt
    have : M < n := by omega
    exact hn3 (hcon n this hn1)
  have h1 := Finset.card_le_card hsub
  rw [Nat.card_Icc] at h1
  have h2 : M + 2 ≤ (M + 2) ^ 3464 := Nat.le_self_pow (by decide) _
  omega

/-- **Respuesta al ejercicio: sí.** El conjunto de los enteros positivos que *no*
pueden escribirse como `a³ + b⁵ + c⁷ + d⁹ + e¹¹` con `a, b, c, d, e ≥ 1` es infinito. -/
theorem infinitos_no_representables : {n : ℕ | 0 < n ∧ ¬ Repr5 n}.Infinite := by
  intro hfin
  obtain ⟨M, hM⟩ := hfin.bddAbove
  obtain ⟨n, hn, hn0, hnr⟩ := exists_gt_not_repr M
  have : n ≤ M := hM ⟨hn0, hnr⟩
  omega

end OME2013
end RetosMatematicos
