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
# Retos Matemáticos, 31 de agosto de 2023

**Enunciado.** Estúdiese la curva `C p` cuyos puntos de coordenadas cartesianas `(x, y)`
verifican la ecuación

  `∫ t in x..y, dt / (t² + 2t + 5) = arctan p`,   `p ∈ ℝ`.

Para los valores de `p` en los que `C p` sea una cónica no degenerada centrada, hállese
el lugar geométrico que describen sus centros.

**Solución.** Integrando, la ecuación equivale a
`arctan ((y+1)/2) - arctan ((x+1)/2) = 2 arctan p`, y tomando tangentes se obtiene la
familia de cónicas

  `C p ≡ (1 - p - p²) y + (p² - p - 1) x - p x y - 5 p = 0`,

que son hipérbolas equiláteras no degeneradas exactamente para `p ≠ 0` (para `p = 0` la
cónica degenera en la recta `y = x`).  El centro de `C p` es
`(x_p, y_p) = ((1 - p - p²)/p, (p² - p - 1)/p)` y, al eliminar el parámetro,
`x_p + y_p = -2`: el lugar geométrico de los centros es la recta `x + y = -2`.
-/

namespace Retos31082023

open Real

/-- El integrando del enunciado, `1 / (t² + 2t + 5)`. -/
noncomputable def integrand (t : ℝ) : ℝ := 1 / (t ^ 2 + 2 * t + 5)

/-- La curva `C p` del enunciado: los puntos `(x, y)` con
`∫ t in q.1..q.2, dt/(t²+2t+5) = arctan p`. -/
def CurveC (p : ℝ) : Set (ℝ × ℝ) :=
  {q : ℝ × ℝ | (∫ t in q.1..q.2, integrand t) = Real.arctan p}

/-- Primer miembro de la ecuación cartesiana de la cónica `C p`. -/
noncomputable def conicF (p x y : ℝ) : ℝ :=
  (1 - p - p ^ 2) * y + (p ^ 2 - p - 1) * x - p * x * y - 5 * p

/-- Matriz asociada a la cónica `C p` (respecto de las coordenadas homogéneas `(1, x, y)`). -/
noncomputable def conicMatrix (p : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-5 * p, (p ^ 2 - p - 1) / 2, (1 - p - p ^ 2) / 2;
     (p ^ 2 - p - 1) / 2, 0, -p / 2;
     (1 - p - p ^ 2) / 2, -p / 2, 0]

/-- Matriz de los términos cuadráticos de la cónica `C p`. -/
noncomputable def quadMatrix (p : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, -p / 2; -p / 2, 0]

/-- `c` es centro (de simetría) de la cónica `conicF p = 0`. -/
def IsCenter (p : ℝ) (c : ℝ × ℝ) : Prop :=
  ∀ u v : ℝ, conicF p (c.1 + u) (c.2 + v) = conicF p (c.1 - u) (c.2 - v)

/-- El centro de la cónica `C p` (para `p ≠ 0`). -/
noncomputable def centerC (p : ℝ) : ℝ × ℝ := ((1 - p - p ^ 2) / p, (p ^ 2 - p - 1) / p)

/-- La forma cuadrática asociada a la matriz `conicMatrix p` es, en efecto, `conicF p`. -/
lemma conicMatrix_apply (p x y : ℝ) :
    ∑ i : Fin 3, ∑ j : Fin 3, ![1, x, y] i * conicMatrix p i j * ![1, x, y] j
      = conicF p x y := by
  simp [Fin.sum_univ_three, conicMatrix, conicF]
  ring

-- =========================================================================
-- Integración de la ecuación del enunciado
-- =========================================================================

lemma integrand_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.arctan ((s + 1) / 2) / 2) (integrand t) t := by
  have h1 : HasDerivAt (fun s : ℝ => (s + 1) / 2) ((1 : ℝ) / 2) t := by
    simpa using ((hasDerivAt_id t).add_const 1).div_const 2
  have h2 := ((Real.hasDerivAt_arctan ((t + 1) / 2)).comp t h1).div_const 2
  refine h2.congr_deriv ?_
  unfold integrand
  have hpos : 0 < t ^ 2 + 2 * t + 5 := by nlinarith [sq_nonneg (t + 1)]
  have hstep : 1 + ((t + 1) / 2) ^ 2 = (t ^ 2 + 2 * t + 5) / 4 := by ring
  rw [hstep]
  have hne : t ^ 2 + 2 * t + 5 ≠ 0 := ne_of_gt hpos
  have hne4 : (t ^ 2 + 2 * t + 5) / 4 ≠ 0 := div_ne_zero hne (by norm_num)
  field_simp
  ring

lemma integrand_continuous : Continuous integrand := by
  refine Continuous.div continuous_const (by fun_prop) (fun t => ?_)
  nlinarith [sq_nonneg (t + 1)]

/-- Cálculo de la integral del enunciado. -/
lemma integral_integrand (x y : ℝ) :
    (∫ t in x..y, integrand t)
      = (Real.arctan ((y + 1) / 2) - Real.arctan ((x + 1) / 2)) / 2 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s : ℝ => Real.arctan ((s + 1) / 2) / 2) (f' := integrand)
    (fun t _ => integrand_hasDerivAt t)
    (integrand_continuous.intervalIntegrable x y)
  rw [h]
  ring

/-- Forma trigonométrica de la ecuación de la curva. -/
lemma mem_curveC_iff_arctan (p x y : ℝ) :
    (x, y) ∈ CurveC p ↔
      Real.arctan ((y + 1) / 2) - Real.arctan ((x + 1) / 2) = 2 * Real.arctan p := by
  simp only [CurveC, Set.mem_ofPred_eq, integral_integrand]
  constructor <;> intro h <;> linarith

-- =========================================================================
-- El paso de la tangente
-- =========================================================================

/-- Identidad básica: el seno de `arctan a - arctan b - 2 arctan p`, salvo un factor
positivo, es el primer miembro de la ecuación algebraica de la cónica. -/
lemma sin_arctan_combination (a b p : ℝ) :
    Real.sin (Real.arctan a - Real.arctan b - 2 * Real.arctan p)
        * (Real.sqrt (1 + a ^ 2) * Real.sqrt (1 + b ^ 2) * (1 + p ^ 2))
      = (a - b) * (1 - p ^ 2) - 2 * p * (1 + a * b) := by
  have ha : (0:ℝ) < 1 + a ^ 2 := by positivity
  have hb : (0:ℝ) < 1 + b ^ 2 := by positivity
  have hp : (0:ℝ) < 1 + p ^ 2 := by positivity
  have hsp : Real.sqrt (1 + p ^ 2) ^ 2 = 1 + p ^ 2 := Real.sq_sqrt hp.le
  have hsa0 : (0:ℝ) < Real.sqrt (1 + a ^ 2) := Real.sqrt_pos.mpr ha
  have hsb0 : (0:ℝ) < Real.sqrt (1 + b ^ 2) := Real.sqrt_pos.mpr hb
  have hsp0 : (0:ℝ) < Real.sqrt (1 + p ^ 2) := Real.sqrt_pos.mpr hp
  rw [Real.sin_sub, Real.sin_sub, Real.cos_sub, Real.sin_two_mul, Real.cos_two_mul,
    Real.sin_arctan, Real.cos_arctan, Real.sin_arctan, Real.cos_arctan, Real.sin_arctan,
    Real.cos_arctan]
  field_simp
  rw [hsp]
  ring

/-- Lema clave: `arctan a - arctan b = 2 arctan p` equivale a la ecuación algebraica
obtenida tomando tangentes, junto con la condición de signo que selecciona la rama. -/
lemma arctan_sub_eq_two_arctan_iff (a b p : ℝ) :
    Real.arctan a - Real.arctan b = 2 * Real.arctan p ↔
      ((a - b) * (1 - p ^ 2) = 2 * p * (1 + a * b) ∧ 0 ≤ (a - b) * p) := by
  have hkey := sin_arctan_combination a b p
  have hmono : ∀ x y : ℝ, Real.arctan x < Real.arctan y ↔ x < y :=
    fun x y => Real.arctan_strictMono.lt_iff_lt
  constructor
  · intro h
    have hz : Real.sin (Real.arctan a - Real.arctan b - 2 * Real.arctan p) = 0 := by
      rw [show Real.arctan a - Real.arctan b - 2 * Real.arctan p = 0 by linarith]
      exact Real.sin_zero
    rw [hz, zero_mul] at hkey
    refine ⟨by linarith, ?_⟩
    rcases lt_trichotomy a b with hab | hab | hab
    · have h1 : Real.arctan a < Real.arctan b := (hmono a b).mpr hab
      have h2 : Real.arctan p < Real.arctan 0 := by rw [Real.arctan_zero]; linarith
      have h3 : p < 0 := (hmono p 0).mp h2
      have : 0 < (b - a) * (-p) := mul_pos (by linarith) (by linarith)
      nlinarith
    · subst hab; simp
    · have h1 : Real.arctan b < Real.arctan a := (hmono b a).mpr hab
      have h2 : Real.arctan 0 < Real.arctan p := by rw [Real.arctan_zero]; linarith
      have h3 : 0 < p := (hmono 0 p).mp h2
      exact le_of_lt (mul_pos (by linarith) h3)
  · rintro ⟨h1, h2⟩
    have hz : Real.sin (Real.arctan a - Real.arctan b - 2 * Real.arctan p) = 0 := by
      have hzz : Real.sin (Real.arctan a - Real.arctan b - 2 * Real.arctan p)
          * (Real.sqrt (1 + a ^ 2) * Real.sqrt (1 + b ^ 2) * (1 + p ^ 2)) = 0 := by
        rw [hkey]; linarith
      exact (mul_eq_zero.mp hzz).resolve_right (by positivity)
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hz
    have hA := Real.arctan_lt_pi_div_two a
    have hA' := Real.neg_pi_div_two_lt_arctan a
    have hB := Real.arctan_lt_pi_div_two b
    have hB' := Real.neg_pi_div_two_lt_arctan b
    have hC := Real.arctan_lt_pi_div_two p
    have hC' := Real.neg_pi_div_two_lt_arctan p
    have hpi := Real.pi_pos
    have hlt : (n:ℝ) < 2 := by nlinarith
    have hgt : (-2:ℝ) < (n:ℝ) := by nlinarith
    have hn2 : n < 2 := by exact_mod_cast hlt
    have hn3 : -2 < n := by exact_mod_cast hgt
    have hcases : n = -1 ∨ n = 0 ∨ n = 1 := by omega
    rcases hcases with rfl | rfl | rfl
    · push_cast at hn
      have hplt : 0 < p := by
        have : Real.arctan 0 < Real.arctan p := by rw [Real.arctan_zero]; linarith
        exact (hmono 0 p).mp this
      have hab : a < b := by
        have : Real.arctan a < Real.arctan b := by linarith
        exact (hmono a b).mp this
      nlinarith
    · push_cast at hn; linarith
    · push_cast at hn
      have hplt : p < 0 := by
        have : Real.arctan p < Real.arctan 0 := by rw [Real.arctan_zero]; linarith
        exact (hmono p 0).mp this
      have hab : b < a := by
        have : Real.arctan b < Real.arctan a := by linarith
        exact (hmono b a).mp this
      nlinarith

-- =========================================================================
-- Ecuación cartesiana de la familia de cónicas
-- =========================================================================

/-- **Ecuación cartesiana de la curva.** `C p` es la rama de la cónica
`(1 - p - p²) y + (p² - p - 1) x - p x y - 5 p = 0` determinada por la condición de signo
`0 ≤ (y - x) p`. -/
theorem mem_curveC_iff (p x y : ℝ) :
    (x, y) ∈ CurveC p ↔ conicF p x y = 0 ∧ 0 ≤ (y - x) * p := by
  rw [mem_curveC_iff_arctan, arctan_sub_eq_two_arctan_iff]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · rw [conicF]; nlinarith [h1]
    · nlinarith [h2]
  · rintro ⟨h1, h2⟩
    rw [conicF] at h1
    constructor
    · nlinarith [h1]
    · nlinarith [h2]

-- Nota sobre la ecuación de la familia: la ecuación (2) tal como aparece en el
-- artículo original, `(p² - p + 1) y - (p² + p + 1) x - p x y - 5 p = 0`, contiene
-- una errata de signos en los coeficientes lineales: para `p = 1/2` el punto `(-1, 5/3)`
-- pertenece a la curva pero no a dicha ecuación. La ecuación correcta es `conicF p x y = 0`.

/-- Comprobación numérica: el punto `(-1, 5/3)` pertenece a `C (1/2)`. -/
example : ((-1 : ℝ), (5 / 3 : ℝ)) ∈ CurveC (1 / 2) := by
  rw [mem_curveC_iff]
  refine ⟨?_, by norm_num⟩
  rw [conicF]
  norm_num

/-- La curva está contenida en la cónica. -/
theorem curveC_subset_conic (p : ℝ) :
    CurveC p ⊆ {q : ℝ × ℝ | conicF p q.1 q.2 = 0} := by
  rintro ⟨x, y⟩ hq
  exact ((mem_curveC_iff p x y).mp hq).1

-- =========================================================================
-- Clasificación de la cónica
-- =========================================================================

/-- Determinante de la matriz de los términos cuadráticos: `-p²/4`. -/
lemma det_quadMatrix (p : ℝ) : (quadMatrix p).det = -(p ^ 2) / 4 := by
  simp [quadMatrix, Matrix.det_fin_two_of]
  ring

/-- Determinante de la matriz de la cónica: `p (p² + 1)² / 4`. -/
lemma det_conicMatrix (p : ℝ) : (conicMatrix p).det = p * (p ^ 2 + 1) ^ 2 / 4 := by
  simp [conicMatrix, Matrix.det_fin_three]
  ring

/-- Para `p ≠ 0` la cónica es no degenerada. -/
theorem conic_nondegenerate {p : ℝ} (hp : p ≠ 0) : (conicMatrix p).det ≠ 0 := by
  rw [det_conicMatrix]
  intro h
  have h2 : p * (p ^ 2 + 1) ^ 2 = 0 := by linarith
  rcases mul_eq_zero.mp h2 with h' | h'
  · exact hp h'
  · nlinarith [sq_nonneg p, sq_nonneg (p ^ 2 + 1)]

/-- Para `p ≠ 0` la cónica es una hipérbola (determinante del menor cuadrático negativo)
y además equilátera (traza nula). -/
theorem conic_hyperbola {p : ℝ} (hp : p ≠ 0) :
    (quadMatrix p).det < 0 ∧ (quadMatrix p).trace = 0 := by
  constructor
  · rw [det_quadMatrix]
    have : 0 < p ^ 2 := by positivity
    linarith
  · simp [quadMatrix, Matrix.trace_fin_two_of]

/-- Para `p = 0` la cónica degenera: se reduce a la recta `y = x`. -/
theorem conic_degenerate_zero :
    (conicMatrix 0).det = 0 ∧ ∀ x y : ℝ, conicF 0 x y = 0 ↔ y = x := by
  refine ⟨by rw [det_conicMatrix]; ring, fun x y => ?_⟩
  rw [conicF]
  constructor <;> intro h <;> linarith

-- =========================================================================
-- Centros y lugar geométrico
-- =========================================================================

/-- Para `p ≠ 0`, el único centro de la cónica `C p` es `centerC p`. -/
theorem isCenter_iff {p : ℝ} (hp : p ≠ 0) (c : ℝ × ℝ) : IsCenter p c ↔ c = centerC p := by
  constructor
  · intro h
    have h1 := h 1 0
    have h2 := h 0 1
    simp only [conicF] at h1 h2
    have hc2 : c.2 = (p ^ 2 - p - 1) / p := by
      field_simp
      nlinarith [h1]
    have hc1 : c.1 = (1 - p - p ^ 2) / p := by
      field_simp
      nlinarith [h2]
    exact Prod.ext_iff.mpr ⟨hc1, hc2⟩
  · intro h u v
    subst h
    simp only [conicF, centerC]
    field_simp
    ring

/-- El centro de `C p` está en la recta `x + y = -2`. -/
lemma centerC_sum {p : ℝ} (hp : p ≠ 0) : (centerC p).1 + (centerC p).2 = -2 := by
  simp only [centerC]
  field_simp
  ring

/-- **Lugar geométrico de los centros**: la recta `x + y = -2`, recorrida por completo. -/
theorem locus_of_centers :
    {c : ℝ × ℝ | ∃ p : ℝ, p ≠ 0 ∧ IsCenter p c} = {q : ℝ × ℝ | q.1 + q.2 = -2} := by
  ext c
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨p, hp, hc⟩
    rw [isCenter_iff hp] at hc
    rw [hc]
    exact centerC_sum hp
  · intro h
    set x := c.1 with hx
    set s := Real.sqrt ((1 + x) ^ 2 + 4) with hs
    have hs2 : s ^ 2 = (1 + x) ^ 2 + 4 := Real.sq_sqrt (by positivity)
    have hsgt : |1 + x| < s := by
      have : |1 + x| ^ 2 < s ^ 2 := by rw [hs2, sq_abs]; linarith
      nlinarith [abs_nonneg (1 + x), Real.sqrt_nonneg ((1 + x) ^ 2 + 4)]
    have hs1 : 1 + x < s := lt_of_le_of_lt (le_abs_self _) hsgt
    set p := (s - (1 + x)) / 2 with hpdef
    have hp0 : 0 < p := by rw [hpdef]; linarith
    have hproot : p ^ 2 + (1 + x) * p - 1 = 0 := by
      rw [hpdef]
      field_simp
      nlinarith [hs2]
    refine ⟨p, ne_of_gt hp0, ?_⟩
    rw [isCenter_iff (ne_of_gt hp0)]
    have hc1 : c.1 = (1 - p - p ^ 2) / p := by
      field_simp
      nlinarith [hproot]
    have hc2 : c.2 = (p ^ 2 - p - 1) / p := by
      have : c.2 = -2 - c.1 := by linarith
      rw [this, hc1]
      field_simp
      ring
    exact Prod.ext_iff.mpr ⟨hc1, hc2⟩

end Retos31082023
