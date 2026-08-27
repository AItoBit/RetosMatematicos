import Mathlib

/-!
# Retos Matemáticos, 31 de octubre de 2024: el folium parabólico

**Enunciado.** Dado el rectángulo `OABC`, con `OA = a` y `OC = AB = b`, se traza la recta
vertical `AB` y se selecciona un punto genérico `D` de ella.  Se une `D` con el origen `O`
y se traza la perpendicular a `OD` que corta a la recta `CB` en el punto `E`.  Se traza la
perpendicular a `DE` por `E`, que corta a `AB` en el punto `F`.  Por último, se traza la
perpendicular a `EF` por `F`, que corta a la recta `OD` en el punto `G`.  Obténgase la
expresión del lugar geométrico `L` del punto `G` al variar `D` a lo largo de la recta `AB`.

**Solución.** Con `O = (0,0)`, `A = (a,0)`, `B = (a,b)`, `C = (0,b)` y `D = (a,t)` se obtiene

* `E = (a - t(b-t)/a, b)`,
* `F = (a, b + t²(b-t)/a²)`,
* `G = ((a² + bt - t²)/a, t(a² + bt - t²)/a²)`,

y eliminando el parámetro `t` resulta el *folium parabólico*

`L : x³ - a(x² - y²) = b x y`.

En este archivo se formalizan la construcción (cada uno de los puntos `E`, `F`, `G` queda
caracterizado de manera única por sus condiciones de incidencia y perpendicularidad) y la
solución (`folium_locus`: el lugar geométrico de `G` es exactamente la curva `L`), junto
con algunas propiedades adicionales de la curva mencionadas en la solución.
-/

namespace FoliumParabolico

set_option autoImplicit false

/-- Dirección de la recta `OD`, donde `D = (a, t)`. -/
def dirOD (a t : ℝ) : ℝ × ℝ := (a, t)

/-- Dirección perpendicular a `OD` (giro de 90°). -/
def dirPerp (a t : ℝ) : ℝ × ℝ := (-t, a)

/-- El punto `D = (a, t)` de la recta `AB`. -/
def Dpt (a t : ℝ) : ℝ × ℝ := (a, t)

/-- El punto `E`: intersección de la perpendicular a `OD` por `D` con la recta `CB : y = b`. -/
noncomputable def Ept (a b t : ℝ) : ℝ × ℝ := (a - t * (b - t) / a, b)

/-- El punto `F`: intersección de la perpendicular a `DE` por `E` con la recta `AB : x = a`. -/
noncomputable def Fpt (a b t : ℝ) : ℝ × ℝ := (a, b + t ^ 2 * (b - t) / a ^ 2)

/-- El punto `G`: intersección de la perpendicular a `EF` por `F` con la recta `OD`. -/
noncomputable def Gpt (a b t : ℝ) : ℝ × ℝ :=
  ((a ^ 2 + b * t - t ^ 2) / a, t * (a ^ 2 + b * t - t ^ 2) / a ^ 2)

/-- El folium parabólico `L : x³ - a(x² - y²) = b x y`. -/
def Folium (a b : ℝ) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | p.1 ^ 3 - a * (p.1 ^ 2 - p.2 ^ 2) = b * p.1 * p.2}

/-- Caracterización del punto `E`: es el único punto de la recta que pasa por `D` con
dirección perpendicular a `OD` que está sobre la recta `CB : y = b`. -/
theorem Ept_iff (a b t : ℝ) (ha : 0 < a) (P : ℝ × ℝ) :
    ((∃ s : ℝ, P = Dpt a t + s • dirPerp a t) ∧ P.2 = b) ↔ P = Ept a b t := by
  have ha' : a ≠ 0 := ne_of_gt ha
  constructor
  · rintro ⟨⟨s, rfl⟩, h2⟩
    simp only [Dpt, dirPerp, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at h2 ⊢
    have hs : s = (b - t) / a := by field_simp; linarith
    subst hs
    simp only [Ept, Prod.mk.injEq]
    refine ⟨by field_simp; ring, by field_simp; ring⟩
  · rintro rfl
    refine ⟨⟨(b - t) / a, ?_⟩, rfl⟩
    simp only [Ept, Dpt, dirPerp, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, Prod.mk.injEq]
    refine ⟨by ring, by field_simp; ring⟩

/-- Caracterización del punto `F`: es el único punto de la recta que pasa por `E` con
dirección perpendicular a `DE` (es decir, paralela a `OD`) que está sobre la recta
`AB : x = a`. -/
theorem Fpt_iff (a b t : ℝ) (ha : 0 < a) (P : ℝ × ℝ) :
    ((∃ s : ℝ, P = Ept a b t + s • dirOD a t) ∧ P.1 = a) ↔ P = Fpt a b t := by
  have ha' : a ≠ 0 := ne_of_gt ha
  constructor
  · rintro ⟨⟨s, rfl⟩, h1⟩
    simp only [Ept, dirOD, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at h1 ⊢
    have hs : s = t * (b - t) / a ^ 2 := by
      have h1' : (a - t * (b - t) / a + s * a) * a = a * a := by rw [h1]
      have h1'' : -(t * (b - t)) + s * a ^ 2 = 0 := by
        have : (a - t * (b - t) / a + s * a) * a = a ^ 2 - t * (b - t) + s * a ^ 2 := by
          field_simp
        rw [this] at h1'
        nlinarith [h1']
      field_simp
      linarith [h1'']
    subst hs
    simp only [Fpt, Prod.mk.injEq]
    refine ⟨by field_simp; ring, by field_simp⟩
  · rintro rfl
    refine ⟨⟨t * (b - t) / a ^ 2, ?_⟩, rfl⟩
    simp only [Ept, Fpt, dirOD, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, Prod.mk.injEq]
    refine ⟨by field_simp; ring, by field_simp⟩

/-- Caracterización del punto `G`: es el único punto de la recta que pasa por `F` con
dirección perpendicular a `EF` (es decir, perpendicular a `OD`) que está sobre la recta
`OD`. -/
theorem Gpt_iff (a b t : ℝ) (ha : 0 < a) (P : ℝ × ℝ) :
    ((∃ s : ℝ, P = Fpt a b t + s • dirPerp a t) ∧ (∃ r : ℝ, P = r • dirOD a t)) ↔
      P = Gpt a b t := by
  have ha' : a ≠ 0 := ne_of_gt ha
  constructor
  · rintro ⟨⟨s, rfl⟩, ⟨r, hr⟩⟩
    simp only [Fpt, dirOD, dirPerp, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul,
      Prod.mk.injEq] at hr
    obtain ⟨hr1, hr2⟩ := hr
    have hs : s = (t - b) / a := by
      have h1 : (a - s * t) * t * a = r * t * a ^ 2 := by
        have : a - s * t = r * a := by linarith [hr1]
        rw [show (a - s * t) * t * a = (a - s * t) * (t * a) by ring, this]; ring
      have h2 : b * a ^ 2 + t ^ 2 * (b - t) + s * a ^ 3 = r * t * a ^ 2 := by
        have h := hr2
        calc b * a ^ 2 + t ^ 2 * (b - t) + s * a ^ 3
            = (b + t ^ 2 * (b - t) / a ^ 2 + s * a) * a ^ 2 := by field_simp
          _ = r * t * a ^ 2 := by rw [h]
      have key : (s * a - (t - b)) * (a ^ 2 + t ^ 2) = 0 := by linear_combination h2 - h1
      have hpos : a ^ 2 + t ^ 2 ≠ 0 := by positivity
      have : s * a = t - b := by
        rcases mul_eq_zero.mp key with h | h
        · linarith
        · exact absurd h hpos
      field_simp
      linarith [this]
    subst hs
    simp only [Fpt, dirPerp, Gpt, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, Prod.mk.injEq]
    refine ⟨by field_simp; ring, by field_simp; ring⟩
  · rintro rfl
    refine ⟨⟨(t - b) / a, ?_⟩, ⟨(a ^ 2 + b * t - t ^ 2) / a ^ 2, ?_⟩⟩
    · simp only [Fpt, dirPerp, Gpt, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, Prod.mk.injEq]
      refine ⟨by field_simp; ring, by field_simp; ring⟩
    · simp only [Gpt, dirOD, Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]
      refine ⟨by field_simp, by field_simp⟩

/-- Cada punto `G` de la construcción está en el folium parabólico. -/
theorem Gpt_mem_Folium (a b t : ℝ) (ha : 0 < a) : Gpt a b t ∈ Folium a b := by
  have ha' : a ≠ 0 := ne_of_gt ha
  simp only [Folium, Gpt, Set.mem_ofPred_eq]
  field_simp
  ring

/-- **Solución.** El lugar geométrico del punto `G`, al variar `D = (a,t)` sobre la recta
`AB`, es exactamente el folium parabólico `L : x³ - a(x² - y²) = b x y`. -/
theorem folium_locus (a b : ℝ) (ha : 0 < a) :
    {P : ℝ × ℝ | ∃ t : ℝ, P = Gpt a b t} = Folium a b := by
  have ha' : a ≠ 0 := ne_of_gt ha
  ext P
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨t, rfl⟩
    exact Gpt_mem_Folium a b t ha
  · intro hP
    simp only [Folium, Set.mem_ofPred_eq] at hP
    obtain ⟨x, y⟩ := P
    simp only at hP
    by_cases hx : x = 0
    · -- sobre la curva, `x = 0` obliga a `y = 0`, y el origen se alcanza
      subst hx
      have hy : y = 0 := by
        have h0 : a * y ^ 2 = 0 := by linear_combination hP
        rcases mul_eq_zero.mp h0 with h | h
        · exact absurd h ha'
        · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
      subst hy
      -- `t = (b + √(b² + 4a²))/2` anula `a² + bt - t²`
      refine ⟨(b + Real.sqrt (b ^ 2 + 4 * a ^ 2)) / 2, ?_⟩
      have hsq : Real.sqrt (b ^ 2 + 4 * a ^ 2) ^ 2 = b ^ 2 + 4 * a ^ 2 :=
        Real.sq_sqrt (by positivity)
      have hzero : a ^ 2 + b * ((b + Real.sqrt (b ^ 2 + 4 * a ^ 2)) / 2)
          - ((b + Real.sqrt (b ^ 2 + 4 * a ^ 2)) / 2) ^ 2 = 0 := by
        nlinarith [hsq]
      simp only [Gpt, hzero, Prod.mk.injEq]
      exact ⟨by simp, by simp⟩
    · refine ⟨y * a / x, ?_⟩
      have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
      simp only [Gpt, Prod.mk.injEq]
      constructor
      · field_simp
        linear_combination hP
      · field_simp
        linear_combination y * hP

/-- Intersección de la recta `y = m x` con la curva: se obtiene `x²(x - a - bm + am²) = 0`. -/
theorem line_inter_folium (a b m x : ℝ) :
    ((x, m * x) ∈ Folium a b) ↔ x ^ 2 * (x - a - b * m + a * m ^ 2) = 0 := by
  simp only [Folium, Set.mem_ofPred_eq]
  constructor <;> intro h <;> linear_combination h

/-- Las dos tangentes a la curva en el punto doble `O` son perpendiculares: sus pendientes
son las raíces de `a m² - b m - a = 0`, cuyo producto es `-1`. -/
theorem tangents_at_origin_perp (a b m₁ m₂ : ℝ) (ha : 0 < a)
    (h₁ : a * m₁ ^ 2 - b * m₁ - a = 0) (h₂ : a * m₂ ^ 2 - b * m₂ - a = 0) (hne : m₁ ≠ m₂) :
    m₁ * m₂ = -1 := by
  have ha' : a ≠ 0 := ne_of_gt ha
  have hd : m₁ - m₂ ≠ 0 := sub_ne_zero.mpr hne
  have hfac : (m₁ - m₂) * (a * (m₁ + m₂) - b) = 0 := by linear_combination h₁ - h₂
  have hsum : a * (m₁ + m₂) = b := by
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd h hd
    · linarith
  have hkey : a * (m₁ * m₂ + 1) = 0 := by linear_combination m₁ * hsum - h₁
  rcases mul_eq_zero.mp hkey with h | h
  · exact absurd h ha'
  · linarith

/-- La curva corta al eje de abscisas exactamente en `O = (0,0)` y en `A = (a,0)`. -/
theorem folium_inter_x_axis (a b x : ℝ) (ha : 0 < a) :
    ((x, (0 : ℝ)) ∈ Folium a b) ↔ x = 0 ∨ x = a := by
  simp only [Folium, Set.mem_ofPred_eq]
  constructor
  · intro h
    have h' : x ^ 2 * (x - a) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h1 | h1
    · exact Or.inl (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1)
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl) <;> ring

end FoliumParabolico
