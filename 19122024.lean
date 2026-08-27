import Mathlib

/-!
# Retos Matemáticos, 19 de diciembre de 2024

**Ejercicio.** Hállese la fórmula de la transformación de Möbius `T(z)` que transforma la
circunferencia unidad en la circunferencia `|z - 1 - i| = 1` y que además cumple
`T(0) = (3 + 4i)/5` y `T(-3i) = -i`. Interprétese geométricamente la transformación `T(z)`.

**Solución.** `T(z) = (z + 2 + i)/(-z + 2 - i)`.

This file contains:

* the definition of `T` (`Retos19122024.T`);
* the verification of the two interpolation conditions and of the fact that `T` maps the
  unit circle *onto* the circle of centre `1 + i` and radius `1`;
* the uniqueness of such a Möbius transformation (`Retos19122024.T_unique`);
* the geometric interpretation of `T` as a composition of elementary transformations
  (`Retos19122024.T_eq_elementary` and `Retos19122024.T_eq_comp`).

Throughout, a Möbius transformation `z ↦ (az + b)/(cz + d)` is modelled as a map `ℂ → ℂ`
(with Lean's convention `x / 0 = 0` at the pole) rather than as a map of the Riemann sphere.
-/

open Complex

namespace Retos19122024

/-- The Möbius transformation `T(z) = (z + 2 + i)/(-z + 2 - i)`. -/
noncomputable def T (z : ℂ) : ℂ := (z + 2 + I) / (-z + 2 - I)

/-- `T` is a genuine Möbius transformation: with `a = 1`, `b = 2 + i`, `c = -1`, `d = 2 - i`
we have `ad - bc ≠ 0`. -/
theorem T_nondegenerate : (1 : ℂ) * (2 - I) - (2 + I) * (-1) ≠ 0 := by
  simp [Complex.ext_iff]

/-- First interpolation condition: `T(0) = (3 + 4i)/5`. -/
theorem T_zero : T 0 = (3 + 4 * I) / 5 := by
  have h : (-(0 : ℂ) + 2 - I) ≠ 0 := by simp [Complex.ext_iff]
  rw [T, div_eq_div_iff h (by norm_num)]
  ring_nf
  simp [Complex.I_sq]
  ring

/-- Second interpolation condition: `T(-3i) = -i`. -/
theorem T_neg_three_I : T (-3 * I) = -I := by
  have h : (-(-3 * I) + 2 - I) ≠ 0 := by simp [Complex.ext_iff]
  rw [T, div_eq_iff h]
  ring_nf
  simp [Complex.I_sq]
  ring

/-- Two complex numbers with the same squared modulus have the same modulus. -/
private theorem norm_eq_of_normSq_eq {u v : ℂ} (h : Complex.normSq u = Complex.normSq v) :
    ‖u‖ = ‖v‖ := by
  have h1 := Complex.normSq_eq_norm_sq u
  have h2 := Complex.normSq_eq_norm_sq v
  have : ‖u‖ ^ 2 = ‖v‖ ^ 2 := by rw [← h1, ← h2, h]
  nlinarith [norm_nonneg u, norm_nonneg v]

/-- Cartesian form of the equation of the unit circle. -/
private theorem unit_ns {z : ℂ} (hz : ‖z‖ = 1) : z.re ^ 2 + z.im ^ 2 = 1 := by
  have h := Complex.normSq_eq_norm_sq z
  rw [hz] at h
  simp [Complex.normSq_apply] at h
  nlinarith [h]

/-- Cartesian form of the equation of the circle `|w - 1 - i| = 1`. -/
private theorem circ_ns {w : ℂ} (hw : ‖w - (1 + I)‖ = 1) :
    (w.re - 1) ^ 2 + (w.im - 1) ^ 2 = 1 := by
  have h := Complex.normSq_eq_norm_sq (w - (1 + I))
  rw [hw] at h
  simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at h
  nlinarith [h]

/-- `T` maps the unit circle into the circle `|w - 1 - i| = 1`. -/
theorem T_maps_unit_circle (z : ℂ) (hz : ‖z‖ = 1) : ‖T z - (1 + I)‖ = 1 := by
  have hns := unit_ns hz
  have hden : -z + 2 - I ≠ 0 := by
    intro h
    rw [Complex.ext_iff] at h
    simp [Complex.add_re, Complex.add_im] at h
    nlinarith [h.1, h.2]
  have key : T z - (1 + I) = ((2 + I) * z - 1) / (-z + 2 - I) := by
    rw [T, eq_div_iff hden, sub_mul, div_mul_cancel₀ _ hden]
    ring_nf
    simp [Complex.I_sq]
    ring
  rw [key, norm_div]
  have h2 : ‖(2 + I) * z - 1‖ = ‖-z + 2 - I‖ := by
    apply norm_eq_of_normSq_eq
    simp [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
    nlinarith [hns]
  rw [h2, div_self]
  simpa [norm_eq_zero] using hden

/-- The inverse Möbius transformation, `S(w) = ((2 - i)w - (2 + i))/(w + 1)`. -/
noncomputable def S (w : ℂ) : ℂ := ((2 - I) * w - (2 + I)) / (w + 1)

/-- The point `-1`, the pole of `S`, does not lie on the circle `|w - 1 - i| = 1`. -/
private theorem add_one_ne_zero {w : ℂ} (hw : ‖w - (1 + I)‖ = 1) : w + 1 ≠ 0 := by
  intro h
  have hns := circ_ns hw
  rw [Complex.ext_iff] at h
  simp at h
  rw [h.2] at hns
  nlinarith [h.1, hns]

/-- `S` maps the circle `|w - 1 - i| = 1` into the unit circle. -/
theorem S_maps_circle (w : ℂ) (hw : ‖w - (1 + I)‖ = 1) : ‖S w‖ = 1 := by
  have h := add_one_ne_zero hw
  have hns := circ_ns hw
  rw [S, norm_div]
  have h2 : ‖(2 - I) * w - (2 + I)‖ = ‖w + 1‖ := by
    apply norm_eq_of_normSq_eq
    simp [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im]
    nlinarith [hns]
  rw [h2, div_self]
  simpa [norm_eq_zero] using h

/-- `T ∘ S` is the identity on the circle `|w - 1 - i| = 1`. -/
theorem T_S (w : ℂ) (hw : ‖w - (1 + I)‖ = 1) : T (S w) = w := by
  have h := add_one_ne_zero hw
  have e1 : S w + 2 + I = 4 * w / (w + 1) := by rw [S]; field_simp; ring
  have e2 : -S w + 2 - I = 4 / (w + 1) := by rw [S]; field_simp; ring
  rw [T, e1, e2, div_div_div_cancel_right₀ h]
  ring

/-- `T` maps the unit circle **onto** the circle of centre `1 + i` and radius `1`. -/
theorem T_image_unit_circle :
    T '' {z : ℂ | ‖z‖ = 1} = {w : ℂ | ‖w - (1 + I)‖ = 1} := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact T_maps_unit_circle z hz
  · intro hw
    exact ⟨S w, S_maps_circle w hw, T_S w hw⟩

/-- Algebraic form of the symmetry principle used for the uniqueness proof: if
`|Az + B| = |cz + d|` at the three points `z = 1, -1, i` of the unit circle, then
`A * conj B = c * conj d`. -/
private theorem key_eq {A B c d : ℂ}
    (e1 : Complex.normSq (A * 1 + B) = Complex.normSq (c * 1 + d))
    (e2 : Complex.normSq (A * (-1) + B) = Complex.normSq (c * (-1) + d))
    (e3 : Complex.normSq (A * I + B) = Complex.normSq (c * I + d)) :
    A * (starRingEnd ℂ) B = c * (starRingEnd ℂ) d := by
  have f1 : (A * 1 + B) * (starRingEnd ℂ) (A * 1 + B)
      = (c * 1 + d) * (starRingEnd ℂ) (c * 1 + d) := by
    rw [Complex.mul_conj, Complex.mul_conj, e1]
  have f2 : (A * (-1) + B) * (starRingEnd ℂ) (A * (-1) + B)
      = (c * (-1) + d) * (starRingEnd ℂ) (c * (-1) + d) := by
    rw [Complex.mul_conj, Complex.mul_conj, e2]
  have f3 : (A * I + B) * (starRingEnd ℂ) (A * I + B)
      = (c * I + d) * (starRingEnd ℂ) (c * I + d) := by
    rw [Complex.mul_conj, Complex.mul_conj, e3]
  simp only [map_add, map_neg, map_mul, map_one, Complex.conj_I] at f1 f2 f3
  linear_combination ((1 + I) / 4) * f1 + ((-1 + I) / 4) * f2 + (-I / 2) * f3 +
    ((A * (starRingEnd ℂ) B - (starRingEnd ℂ) A * B - c * (starRingEnd ℂ) d
      + (starRingEnd ℂ) c * d) / 2
      - (A * (starRingEnd ℂ) A * I) / 2 + (c * (starRingEnd ℂ) c * I) / 2) * Complex.I_sq

/-- **Uniqueness.** Any Möbius transformation `z ↦ (az + b)/(cz + d)` sending the unit circle
into the circle `|w - 1 - i| = 1` and satisfying the two interpolation conditions coincides
with `T`. -/
theorem T_unique (a b c d : ℂ)
    (hcirc : ∀ z : ℂ, ‖z‖ = 1 → ‖(a * z + b) / (c * z + d) - (1 + I)‖ = 1)
    (h0 : (a * 0 + b) / (c * 0 + d) = (3 + 4 * I) / 5)
    (h3 : (a * (-3 * I) + b) / (c * (-3 * I) + d) = -I) :
    ∀ z : ℂ, (a * z + b) / (c * z + d) = T z := by
  have hd : d ≠ 0 := by
    intro h
    rw [h] at h0
    simp [Complex.ext_iff] at h0
    exact absurd h0.1 (by norm_num)
  have hb : b = (3 + 4 * I) / 5 * d := by
    simp only [mul_zero, zero_add] at h0
    field_simp at h0
    linear_combination h0 / 5
  have hnz : ∀ z : ℂ, ‖z‖ = 1 → c * z + d ≠ 0 := by
    intro z hz hzero
    have h := hcirc z hz
    rw [hzero, div_zero] at h
    have h2 := Complex.normSq_eq_norm_sq ((0 : ℂ) - (1 + I))
    rw [h] at h2
    simp [Complex.normSq_apply] at h2
  have hkey : ∀ z : ℂ, ‖z‖ = 1 → Complex.normSq ((a - (1 + I) * c) * z + (b - (1 + I) * d))
      = Complex.normSq (c * z + d) := by
    intro z hz
    have hden := hnz z hz
    have h := hcirc z hz
    have e : (a * z + b) / (c * z + d) - (1 + I)
        = ((a - (1 + I) * c) * z + (b - (1 + I) * d)) / (c * z + d) := by
      rw [eq_div_iff hden, sub_mul, div_mul_cancel₀ _ hden]
      ring
    rw [e, norm_div, div_eq_one_iff_eq (by simpa [norm_eq_zero] using hden)] at h
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, h]
  have hsym := key_eq (hkey 1 (by simp)) (hkey (-1) (by simp)) (hkey I (by simp))
  have hB : b - (1 + I) * d = (-2 - I) / 5 * d := by rw [hb]; ring
  rw [hB] at hsym
  have hcd : (starRingEnd ℂ) d ≠ 0 := by simpa using hd
  -- the image of `∞` is `-1`, i.e. `a = -c`
  have hsym2 : (a - (1 + I) * c) * ((-2 + I) / 5) = c := by
    have h : ((a - (1 + I) * c) * ((-2 + I) / 5)) * (starRingEnd ℂ) d = c * (starRingEnd ℂ) d := by
      rw [← hsym]
      simp [map_mul, map_div₀, map_sub, map_neg, map_ofNat, Complex.conj_I]
      ring
    exact mul_right_cancel₀ hcd h
  have ha : a = -c := by
    linear_combination (-2 - I) * hsym2 + ((a - (1 + I) * c) / 5) * Complex.I_sq
  have hden3 : c * (-3 * I) + d ≠ 0 := by
    intro hzero
    rw [hzero, div_zero] at h3
    exact absurd h3.symm (by simp [Complex.ext_iff])
  have E : 3 * I * c + (3 + 4 * I) / 5 * d = -3 * c - I * d := by
    rw [div_eq_iff hden3] at h3
    rw [ha, hb] at h3
    linear_combination h3 + (3 * c) * Complex.I_sq
  have hc : c = (-2 - I) / 5 * d := by
    linear_combination ((1 - I) / 6) * E
      + (c / 2 + (-2 - I) / 5 * d / 2 + d / 10 + 2 * d / 5 + I * d / 10) * Complex.I_sq
  have ha' : a = (2 + I) / 5 * d := by rw [ha, hc]; ring
  intro z
  have hne : (2 + I) / 5 * d ≠ 0 := by
    apply mul_ne_zero _ hd
    simp [Complex.ext_iff]
  have hnum : a * z + b = (z + 2 + I) * ((2 + I) / 5 * d) := by
    rw [ha', hb]; linear_combination (-(d / 5)) * Complex.I_sq
  have hden : c * z + d = (-z + 2 - I) * ((2 + I) / 5 * d) := by
    rw [hc]; linear_combination (d / 5) * Complex.I_sq
  rw [hnum, hden, mul_div_mul_right _ _ hne, T]

/-- The inversion of centre `a` and radius `R`: `w ↦ a + R² / conj (w - a)`. -/
noncomputable def inversion (a : ℂ) (R : ℝ) (w : ℂ) : ℂ :=
    a + (R : ℂ) ^ 2 / (starRingEnd ℂ) (w - a)

/-- Away from its pole, `T(z) = -1 - 4/(z - (2 - i))`. -/
theorem T_eq_sub (z : ℂ) (hz : z ≠ 2 - I) : T z = -1 - 4 / (z - (2 - I)) := by
  have h : z - (2 - I) ≠ 0 := sub_ne_zero.mpr hz
  rw [T, div_eq_iff (by intro hc; apply h; linear_combination -hc)]
  field_simp
  ring

/-- **Geometric interpretation (first form).**  Away from its pole `z = 2 - i`, the map `T`
is the composition of the reflection in the real axis, the inversion of centre `2 + i` and
radius `2`, the central symmetry about the origin, and the translation by `1 + i`. -/
theorem T_eq_elementary (z : ℂ) (hz : z ≠ 2 - I) :
    T z = (1 + I) - inversion (2 + I) 2 ((starRingEnd ℂ) z) := by
  have e : (starRingEnd ℂ) ((starRingEnd ℂ) z - (2 + I)) = z - (2 - I) := by
    simp [Complex.ext_iff]
  rw [inversion, e, T_eq_sub z hz]
  push_cast
  norm_num
  ring

/-- **Geometric interpretation (second form).**  Away from its pole `z = 2 - i`, `T` is the
composition `T₄ ∘ T₃ ∘ T₂ ∘ T₁` of the translation `T₁ z = z - (2 - i)`, the complex inversion
`T₂ z = 1/z`, the homothety `T₃ z = -4z` and the translation `T₄ z = z - 1`. -/
theorem T_eq_comp (z : ℂ) (hz : z ≠ 2 - I) :
    T z = (fun w => w - 1) ((fun w => -4 * w) ((fun w => 1 / w) ((fun w => w - (2 - I)) z))) := by
  rw [T_eq_sub z hz]
  simp only
  rw [mul_one_div]
  ring

end Retos19122024
