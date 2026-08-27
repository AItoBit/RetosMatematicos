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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# El problema del mes (RSME, feb. 2025) — Retos Matemáticos, 5 de septiembre de 2025

**Enunciado.** Si una recta corta a la curva `y = ∛(x²)` en tres puntos de abscisas
`x₁, x₂, x₃`, entonces

`∛(x₁x₂/x₃²) + ∛(x₂x₃/x₁²) + ∛(x₁x₃/x₂²)`

es constante (y vale `3`).

La curva `y = ∛(x²)` es exactamente el conjunto de puntos `(x, y)` con `y³ = x²`.

**Solución formalizada.** Se parametriza la curva por `t ↦ (t³, t²)`. Tres puntos de la
curva con parámetros distintos `p, q, r` están alineados si y sólo si `pq + qr + rp = 0`,
y en ese caso, poniendo `u = pq`, `v = qr`, `w = rp` (con `u + v + w = 0`),

`qr/p² + rp/q² + pq/r² = (u³ + v³ + w³)/(pqr)² = 3uvw/(pqr)² = 3`.
-/

namespace RetosMatematicos

/-! ## Raíz cúbica real -/

/-- Raíz cúbica real (definida también para argumentos negativos). -/
noncomputable def cbrt (x : ℝ) : ℝ := if 0 ≤ x then x ^ ((1:ℝ)/3) else -((-x) ^ ((1:ℝ)/3))

/-- La función `x ↦ x³` es inyectiva en `ℝ`. -/
lemma cube_injective {a b : ℝ} (h : a ^ 3 = b ^ 3) : a = b :=
  (Odd.strictMono_pow (R := ℝ) (by decide : Odd 3)).injective h

@[simp] lemma cbrt_cube (t : ℝ) : cbrt (t ^ 3) = t := by
  have key : ∀ s : ℝ, 0 ≤ s → (s ^ 3) ^ ((1:ℝ)/3) = s := by
    intro s hs
    rw [← Real.rpow_natCast s 3, ← Real.rpow_mul hs]
    norm_num
  rcases le_or_gt 0 t with ht | ht
  · rw [cbrt, ite_eq_left (by positivity)]
    exact key t ht
  · have h3 : ¬ (0 ≤ t ^ 3) := by
      have : t ^ 3 < 0 := by
        nlinarith [mul_pos (neg_pos.mpr ht) (neg_pos.mpr ht)]
      linarith
    rw [cbrt, ite_eq_right h3]
    have h : -(t ^ 3) = (-t) ^ 3 := by ring
    rw [h, key (-t) (by linarith)]
    ring

@[simp] lemma cbrt_pow_three (x : ℝ) : (cbrt x) ^ 3 = x := by
  have key : ∀ s : ℝ, 0 ≤ s → (s ^ ((1:ℝ)/3)) ^ 3 = s := by
    intro s hs
    rw [← Real.rpow_natCast (s ^ ((1:ℝ)/3)) 3, ← Real.rpow_mul hs]
    norm_num
  rcases le_or_gt 0 x with hx | hx
  · rw [cbrt, ite_eq_left hx]; exact key x hx
  · rw [cbrt, ite_eq_right (not_le.mpr hx)]
    have := key (-x) (by linarith)
    nlinarith [this]

lemma cbrt_eq_iff {x t : ℝ} : cbrt x = t ↔ t ^ 3 = x := by
  constructor
  · rintro rfl; exact cbrt_pow_three x
  · rintro rfl; exact cbrt_cube t

/-! ## La curva `y = ∛(x²)` -/

/-- Un punto `(x, y)` está en la curva `y = ∛(x²)` exactamente cuando `y³ = x²`. -/
def OnCurve (x y : ℝ) : Prop := y ^ 3 = x ^ 2

/-- Parametrización de la curva: todo punto de la curva es de la forma `(t³, t²)`. -/
lemma onCurve_iff_exists_param {x y : ℝ} :
    OnCurve x y ↔ ∃ t : ℝ, x = t ^ 3 ∧ y = t ^ 2 := by
  constructor
  · intro h
    have h' : y ^ 3 = x ^ 2 := h
    have hx : cbrt x ^ 3 = x := cbrt_pow_three x
    refine ⟨cbrt x, hx.symm, cube_injective ?_⟩
    linear_combination h' - (cbrt x ^ 3 + x) * hx
  · rintro ⟨t, rfl, rfl⟩
    unfold OnCurve
    ring

/-! ## Condición de alineación -/

/-- Si los tres puntos `(p³, p²)`, `(q³, q²)`, `(r³, r²)` de la curva, con parámetros
distintos, están sobre la recta `y = m x + b`, entonces `pq + qr + rp = 0`. -/
lemma param_sum_prod_eq_zero {m b p q r : ℝ}
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hp : p ^ 2 = m * p ^ 3 + b) (hq : q ^ 2 = m * q ^ 3 + b)
    (hr : r ^ 2 = m * r ^ 3 + b) :
    p * q + q * r + r * p = 0 := by
  have e1 : (p - q) * ((p + q) - m * (p ^ 2 + p * q + q ^ 2)) = 0 := by
    linear_combination hp - hq
  have e2 : (q - r) * ((q + r) - m * (q ^ 2 + q * r + r ^ 2)) = 0 := by
    linear_combination hq - hr
  have e1' : (p + q) - m * (p ^ 2 + p * q + q ^ 2) = 0 :=
    (mul_eq_zero.mp e1).resolve_left (sub_ne_zero.mpr hpq)
  have e2' : (q + r) - m * (q ^ 2 + q * r + r ^ 2) = 0 :=
    (mul_eq_zero.mp e2).resolve_left (sub_ne_zero.mpr hqr)
  have e3 : (p - r) * (1 - m * (p + q + r)) = 0 := by linear_combination e1' - e2'
  have hm : m * (p + q + r) = 1 := by
    have := (mul_eq_zero.mp e3).resolve_left (sub_ne_zero.mpr hpr)
    linarith
  have hm0 : m ≠ 0 := by
    intro h; rw [h] at hm; simp at hm
  have key : m * (p * q + q * r + r * p) = 0 := by
    linear_combination (p + q) * hm + e1'
  exact (mul_eq_zero.mp key).resolve_left hm0

/-- Si `pq + qr + rp = 0` con `p, q, r` distintos, entonces ninguno es nulo. -/
lemma param_ne_zero_of_sum_prod_eq_zero {p q r : ℝ}
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (h : p * q + q * r + r * p = 0) :
    p ≠ 0 ∧ q ≠ 0 ∧ r ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl
  · have h' : q * r = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h' | h'
    · exact hpq h'.symm
    · exact hpr h'.symm
  · have h' : r * p = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h' | h'
    · exact hqr h'.symm
    · exact hpq h'
  · have h' : p * q = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h' | h'
    · exact hpr h'
    · exact hqr h'

/-- Identidad algebraica clave: si `pq + qr + rp = 0` y `p, q, r ≠ 0`, entonces
`qr/p² + rp/q² + pq/r² = 3`. -/
lemma key_identity {p q r : ℝ} (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
    (h : p * q + q * r + r * p = 0) :
    q * r / p ^ 2 + r * p / q ^ 2 + p * q / r ^ 2 = 3 := by
  field_simp
  linear_combination ((p * q) ^ 2 + (q * r) ^ 2 + (r * p) ^ 2 - (p * q) * (q * r)
    - (q * r) * (r * p) - (r * p) * (p * q)) * h

/-! ## Resultado principal -/

/-- **Resultado principal.** Si la recta `y = m x + b` corta a la curva `y = ∛(x²)` en tres
puntos distintos de abscisas `x₁, x₂, x₃`, entonces
`∛(x₁x₂/x₃²) + ∛(x₂x₃/x₁²) + ∛(x₁x₃/x₂²) = 3`. -/
theorem cbrt_sum_eq_three_of_line {m b x₁ x₂ x₃ : ℝ}
    (h₁₂ : x₁ ≠ x₂) (h₁₃ : x₁ ≠ x₃) (h₂₃ : x₂ ≠ x₃)
    (hc₁ : OnCurve x₁ (m * x₁ + b)) (hc₂ : OnCurve x₂ (m * x₂ + b))
    (hc₃ : OnCurve x₃ (m * x₃ + b)) :
    cbrt (x₁ * x₂ / x₃ ^ 2) + cbrt (x₂ * x₃ / x₁ ^ 2) + cbrt (x₁ * x₃ / x₂ ^ 2) = 3 := by
  obtain ⟨p, hxp, hyp⟩ := onCurve_iff_exists_param.mp hc₁
  obtain ⟨q, hxq, hyq⟩ := onCurve_iff_exists_param.mp hc₂
  obtain ⟨r, hxr, hyr⟩ := onCurve_iff_exists_param.mp hc₃
  have hpq : p ≠ q := by rintro rfl; exact h₁₂ (hxp.trans hxq.symm)
  have hpr : p ≠ r := by rintro rfl; exact h₁₃ (hxp.trans hxr.symm)
  have hqr : q ≠ r := by rintro rfl; exact h₂₃ (hxq.trans hxr.symm)
  have hp : p ^ 2 = m * p ^ 3 + b := by rw [← hyp, ← hxp]
  have hq : q ^ 2 = m * q ^ 3 + b := by rw [← hyq, ← hxq]
  have hr : r ^ 2 = m * r ^ 3 + b := by rw [← hyr, ← hxr]
  have hsum := param_sum_prod_eq_zero hpq hpr hqr hp hq hr
  obtain ⟨hp0, hq0, hr0⟩ := param_ne_zero_of_sum_prod_eq_zero hpq hpr hqr hsum
  have c₁ : cbrt (x₁ * x₂ / x₃ ^ 2) = p * q / r ^ 2 := by
    rw [cbrt_eq_iff, hxp, hxq, hxr]; field_simp
  have c₂ : cbrt (x₂ * x₃ / x₁ ^ 2) = q * r / p ^ 2 := by
    rw [cbrt_eq_iff, hxp, hxq, hxr]; field_simp
  have c₃ : cbrt (x₁ * x₃ / x₂ ^ 2) = r * p / q ^ 2 := by
    rw [cbrt_eq_iff, hxp, hxq, hxr]; field_simp
  rw [c₁, c₂, c₃]
  linarith [key_identity hp0 hq0 hr0 hsum]

/-- Tres puntos alineados del plano con dos abscisas distintas están sobre una recta no
vertical `y = m x + b`. -/
lemma exists_line_of_collinear {x₁ x₂ x₃ y₁ y₂ y₃ : ℝ} (h₁₂ : x₁ ≠ x₂)
    (hcol : Collinear ℝ ({(x₁, y₁), (x₂, y₂), (x₃, y₃)} : Set (ℝ × ℝ))) :
    ∃ m b : ℝ, y₁ = m * x₁ + b ∧ y₂ = m * x₂ + b ∧ y₃ = m * x₃ + b := by
  rw [collinear_iff_of_mem (Set.mem_insert _ _)] at hcol
  obtain ⟨⟨v₁, v₂⟩, hv⟩ := hcol
  obtain ⟨t₂, h2⟩ := hv (x₂, y₂) (by simp)
  obtain ⟨t₃, h3⟩ := hv (x₃, y₃) (by simp)
  simp only [Prod.mk.injEq, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, vadd_eq_add] at h2 h3
  obtain ⟨hx2, hy2⟩ := h2
  obtain ⟨hx3, hy3⟩ := h3
  have hv1 : v₁ ≠ 0 := by
    intro h
    exact h₁₂ (by rw [hx2, h]; ring)
  refine ⟨v₂ / v₁, y₁ - (v₂ / v₁) * x₁, by ring, ?_, ?_⟩
  · rw [hy2, hx2]; field_simp; ring
  · rw [hy3, hx3]; field_simp; ring

/-- Versión con la hipótesis geométrica de alineación (`Collinear ℝ`) en lugar de una
ecuación explícita de la recta. -/
theorem cbrt_sum_eq_three_of_collinear {x₁ x₂ x₃ y₁ y₂ y₃ : ℝ}
    (h₁₂ : x₁ ≠ x₂) (h₁₃ : x₁ ≠ x₃) (h₂₃ : x₂ ≠ x₃)
    (hc₁ : OnCurve x₁ y₁) (hc₂ : OnCurve x₂ y₂) (hc₃ : OnCurve x₃ y₃)
    (hcol : Collinear ℝ ({(x₁, y₁), (x₂, y₂), (x₃, y₃)} : Set (ℝ × ℝ))) :
    cbrt (x₁ * x₂ / x₃ ^ 2) + cbrt (x₂ * x₃ / x₁ ^ 2) + cbrt (x₁ * x₃ / x₂ ^ 2) = 3 := by
  obtain ⟨m, b, e₁, e₂, e₃⟩ := exists_line_of_collinear h₁₂ hcol
  subst e₁; subst e₂; subst e₃
  exact cbrt_sum_eq_three_of_line h₁₂ h₁₃ h₂₃ hc₁ hc₂ hc₃

end RetosMatematicos
