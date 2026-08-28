/-
  Retos Matemáticos — 26 de mayo de 2023 (ISSN 2952-0746)

  Ejercicio: una elipse de dimensiones variables en el plano perpendicular al eje x.
  Un vértice recorre la circunferencia (x - r)² + z² = r² (plano y = 0), el otro
  recorre la recta y = m x, z = 0.  Hállese m para que el volumen generado sea el
  de una esfera de radio r.

  Semiejes de la sección en abscisa x ∈ [0, 2r]:

      a(x) = √(r² - (x-r)²) = √(2rx - x²)      (circunferencia)
      b(x) = m x                                (recta)

  Área de la sección: π a(x) b(x).  Volumen: V = ∫₀^{2r} π m x √(2rx - x²) dx.

  Resultado:  V = π² m r³ / 2,  y  V = (4/3)π r³  ⟺  m = 8/(3π).

  ---------------------------------------------------------------------------
  ESTADO: sin `sorry`.
  ---------------------------------------------------------------------------

  La integral I = ∫₀^{2r} x √(2rx - x²) dx = π r³/2 se obtiene siguiendo la
  2ª Forma del boletín, que es con diferencia la más barata de formalizar:
  por la simetría x ↦ 2r - x se tiene

      ∫₀^{2r} x √(2rx-x²) dx = ∫₀^{2r} (2r-x) √(2rx-x²) dx,

  luego 2I = 2r ∫₀^{2r} √(2rx-x²) dx = 2r · (área del semicírculo) = 2r · πr²/2.
  Se evitan así las primitivas de las Alternativas 1–4 (cambio trigonométrico,
  función beta, método alemán), que exigirían FTC a mano.
-/
import Mathlib

open MeasureTheory intervalIntegral
open scoped Real

namespace RetosMatematicos2605

noncomputable section

variable (r m : ℝ)

/-! ## Comprobación de la geometría

El punto `C = (x, 0, √(2rx - x²))` está sobre la circunferencia `(x-r)² + z² = r²`. -/

example (r x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 2 * r) :
    (x - r) ^ 2 + Real.sqrt (2 * r * x - x ^ 2) ^ 2 = r ^ 2 := by
  have h : 0 ≤ 2 * r * x - x ^ 2 := by nlinarith
  rw [Real.sq_sqrt h]
  ring

/-! ## El semicírculo -/

/-- `∫₀^{2r} √(2rx - x²) dx = π r²/2`: el área del semicírculo de radio `r`. -/
theorem integral_semicircle (hr : 0 < r) :
    (∫ x in (0 : ℝ)..(2 * r), Real.sqrt (2 * r * x - x ^ 2)) = π * r ^ 2 / 2 := by
  have hr' : r ≠ 0 := ne_of_gt hr
  -- √(2rx - x²) = r · √(1 - ((x-r)/r)²)
  have hpt : ∀ x : ℝ, Real.sqrt (2 * r * x - x ^ 2)
      = r * Real.sqrt (1 - ((x - r) / r) ^ 2) := by
    intro x
    have h : 1 - ((x - r) / r) ^ 2 = (2 * r * x - x ^ 2) * (r⁻¹) ^ 2 := by
      field_simp
      ring
    rw [h, Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (by positivity : (0:ℝ) ≤ r⁻¹)]
    field_simp
  calc (∫ x in (0 : ℝ)..(2 * r), Real.sqrt (2 * r * x - x ^ 2))
      = ∫ x in (0 : ℝ)..(2 * r), r * Real.sqrt (1 - ((x - r) / r) ^ 2) := by
        simp_rw [hpt]
    _ = r * ∫ x in (0 : ℝ)..(2 * r), Real.sqrt (1 - ((x - r) / r) ^ 2) := by
        rw [intervalIntegral.integral_const_mul]
    _ = r * ∫ y in (0 - r : ℝ)..(2 * r - r), Real.sqrt (1 - (y / r) ^ 2) := by
        rw [intervalIntegral.integral_comp_sub_right
          (fun y => Real.sqrt (1 - (y / r) ^ 2)) r]
    _ = r * ∫ y in (-r : ℝ)..r, Real.sqrt (1 - (y / r) ^ 2) := by
        norm_num
    _ = r * (r • ∫ t in (-r / r : ℝ)..(r / r), Real.sqrt (1 - t ^ 2)) := by
        rw [intervalIntegral.integral_comp_div
          (fun t => Real.sqrt (1 - t ^ 2)) hr']
    _ = r * (r * (π / 2)) := by
        rw [neg_div, div_self hr', smul_eq_mul, integral_sqrt_one_sub_sq]
    _ = π * r ^ 2 / 2 := by ring

/-! ## La integral del enunciado -/

/-- `∫₀^{2r} x √(2rx - x²) dx = π r³/2`, por el argumento de simetría. -/
theorem integral_x_sqrt (hr : 0 < r) :
    (∫ x in (0 : ℝ)..(2 * r), x * Real.sqrt (2 * r * x - x ^ 2)) = π * r ^ 3 / 2 := by
  have hcont : Continuous fun x : ℝ => Real.sqrt (2 * r * x - x ^ 2) :=
    Real.continuous_sqrt.comp (by continuity)
  have h1 : IntervalIntegrable (fun x : ℝ => x * Real.sqrt (2 * r * x - x ^ 2))
      volume 0 (2 * r) := (continuous_id.mul hcont).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun x : ℝ => (2 * r - x) * Real.sqrt (2 * r * x - x ^ 2))
      volume 0 (2 * r) :=
    ((continuous_const.sub continuous_id).mul hcont).intervalIntegrable _ _
  -- simetría x ↦ 2r - x
  have hsym : ∀ x : ℝ, 2 * r * (2 * r - x) - (2 * r - x) ^ 2 = 2 * r * x - x ^ 2 := by
    intro x; ring
  have hJ : (∫ x in (0 : ℝ)..(2 * r), (2 * r - x) * Real.sqrt (2 * r * x - x ^ 2))
      = ∫ x in (0 : ℝ)..(2 * r), x * Real.sqrt (2 * r * x - x ^ 2) := by
    have h := intervalIntegral.integral_comp_sub_left
      (fun y : ℝ => y * Real.sqrt (2 * r * y - y ^ 2)) (2 * r) (a := 0) (b := 2 * r)
    simpa [hsym] using h
  -- I + J = 2r · (área del semicírculo)
  have key : (∫ x in (0 : ℝ)..(2 * r), x * Real.sqrt (2 * r * x - x ^ 2))
      + (∫ x in (0 : ℝ)..(2 * r), (2 * r - x) * Real.sqrt (2 * r * x - x ^ 2))
      = π * r ^ 3 := by
    rw [← intervalIntegral.integral_add h1 h2]
    have hpt : ∀ x : ℝ, x * Real.sqrt (2 * r * x - x ^ 2)
        + (2 * r - x) * Real.sqrt (2 * r * x - x ^ 2)
        = 2 * r * Real.sqrt (2 * r * x - x ^ 2) := by intro x; ring
    simp_rw [hpt]
    rw [intervalIntegral.integral_const_mul, integral_semicircle r hr]
    ring
  rw [hJ] at key
  linarith

/-! ## El volumen -/

/-- El volumen del sólido: `V = π² m r³ / 2`. -/
theorem volume_solid (hr : 0 < r) :
    (∫ x in (0 : ℝ)..(2 * r), π * (m * x) * Real.sqrt (2 * r * x - x ^ 2))
      = π ^ 2 * m * r ^ 3 / 2 := by
  have hpt : ∀ x : ℝ, π * (m * x) * Real.sqrt (2 * r * x - x ^ 2)
      = (π * m) * (x * Real.sqrt (2 * r * x - x ^ 2)) := by intro x; ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul, integral_x_sqrt r hr]
  ring

/-- **Reto (26-V-2023).**  El volumen generado por la elipse coincide con el de la
    esfera de radio `r` si y solo si `m = 8/(3π)`. -/
theorem retos_26052023 (hr : 0 < r) :
    (∫ x in (0 : ℝ)..(2 * r), π * (m * x) * Real.sqrt (2 * r * x - x ^ 2))
      = 4 / 3 * π * r ^ 3 ↔ m = 8 / (3 * π) := by
  rw [volume_solid r m hr]
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hπ' : π ≠ 0 := ne_of_gt hπ
  constructor
  · intro h
    have hne : π * r ^ 3 ≠ 0 := by positivity
    have h2 : (π * r ^ 3) * (3 * π * m) = (π * r ^ 3) * 8 := by linear_combination 6 * h
    have h3 : 3 * π * m = 8 := mul_left_cancel₀ hne h2
    field_simp
    linarith
  · intro h
    subst h
    field_simp
    ring

#print axioms retos_26052023

end

end RetosMatematicos2605
