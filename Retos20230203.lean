import Mathlib

/-!
# Retos Matemáticos, 3 de febrero de 2023

**Enunciado.** Determínense los siete primeros términos de una progresión geométrica,
sabiendo que la suma de sus tres primeros términos es `49/9`, y la suma de sus tres
últimos términos (se sobreentiende que de dichos siete) sea `30625/729`.

Trabajamos sobre `ℂ`, como en la solución del PDF, que contempla también las razones
imaginarias `± 5i/3`.  Una progresión geométrica de primer término `a₁` y razón `r`
tiene términos `aₙ = a₁ · r^(n-1)`; aquí se indexan desde `0`, es decir
`geomTerm a₁ r k = a₁ * r ^ k` para `k = 0, …, 6`.

Se demuestra:

* `Retos20230203.ratio_cases`: la razón cumple `r⁴ = 625/81`, luego
  `r ∈ {5/3, -5/3, 5i/3, -5i/3}`;
* `Retos20230203.isSolution_iff`: los pares `(a₁, r)` que resuelven el problema son
  exactamente los cuatro de la solución;
* `Retos20230203.sevenTerms_case_one` … `sevenTerms_case_four`: la lista explícita de
  los siete términos en cada caso.
-/

open Complex

namespace Retos20230203

/-- Término de índice `k` (empezando en `k = 0`) de la progresión geométrica de
primer término `a₁` y razón `r`. -/
noncomputable def geomTerm (a₁ r : ℂ) (k : ℕ) : ℂ := a₁ * r ^ k

/-- Los siete primeros términos de la progresión geométrica de primer término `a₁`
y razón `r`. -/
noncomputable def sevenTerms (a₁ r : ℂ) : List ℂ :=
  (List.range 7).map (geomTerm a₁ r)

/-- Condición del enunciado: la suma de los tres primeros términos es `49/9`
y la suma de los tres últimos (de los siete primeros) es `30625/729`. -/
def IsSolution (a₁ r : ℂ) : Prop :=
  geomTerm a₁ r 0 + geomTerm a₁ r 1 + geomTerm a₁ r 2 = 49 / 9 ∧
  geomTerm a₁ r 4 + geomTerm a₁ r 5 + geomTerm a₁ r 6 = 30625 / 729

/-- Potencias sucesivas de la unidad imaginaria, usadas en los cálculos. -/
private lemma I_pow_values :
    (I : ℂ) ^ 2 = -1 ∧ (I : ℂ) ^ 3 = -I ∧ (I : ℂ) ^ 4 = 1 ∧ (I : ℂ) ^ 5 = I ∧
      (I : ℂ) ^ 6 = -1 ∧ (I : ℂ) ^ 7 = -I := by
  refine ⟨Complex.I_sq, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [pow_succ]

/-- Si `(a₁, r)` cumple las condiciones del enunciado, entonces `1 + r + r² ≠ 0`. -/
lemma one_add_r_add_r_sq_ne_zero {a₁ r : ℂ} (h : IsSolution a₁ r) :
    1 + r + r ^ 2 ≠ 0 := by
  intro h0
  obtain ⟨h1, -⟩ := h
  simp only [geomTerm] at h1
  have h2 : a₁ * (1 + r + r ^ 2) = 49 / 9 := by linear_combination h1
  rw [h0, mul_zero] at h2
  norm_num at h2

/-- La razón satisface `r⁴ = 625/81` (dividiendo las dos condiciones). -/
lemma r_pow_four {a₁ r : ℂ} (h : IsSolution a₁ r) : r ^ 4 = 625 / 81 := by
  have hne := one_add_r_add_r_sq_ne_zero h
  obtain ⟨h1, h2⟩ := h
  simp only [geomTerm] at h1 h2
  have key : (a₁ * (1 + r + r ^ 2)) * (r ^ 4 - 625 / 81) = 0 := by
    linear_combination h2 - (625 / 81 : ℂ) * h1
  have ha : a₁ ≠ 0 := by
    rintro rfl
    simp at h1
    exact absurd h1 (by norm_num)
  rcases mul_eq_zero.1 key with hk | hk
  · exact absurd hk (mul_ne_zero ha hne)
  · exact sub_eq_zero.1 hk

/-- Las cuatro razones posibles: `r = ±5/3` o `r = ±5i/3`. -/
lemma ratio_cases {a₁ r : ℂ} (h : IsSolution a₁ r) :
    r = 5 / 3 ∨ r = -(5 / 3) ∨ r = 5 * I / 3 ∨ r = -(5 * I / 3) := by
  have h4 := r_pow_four h
  have hfac : (r - 5 / 3) * (r + 5 / 3) * (r - 5 * I / 3) * (r + 5 * I / 3) = 0 := by
    have hI : I ^ 2 = -1 := Complex.I_sq
    linear_combination h4 + (625 / 81 - 25 / 9 * r ^ 2) * hI
  rcases mul_eq_zero.1 hfac with h' | h'
  · rcases mul_eq_zero.1 h' with h'' | h''
    · rcases mul_eq_zero.1 h'' with h3 | h3
      · exact Or.inl (by linear_combination h3)
      · exact Or.inr (Or.inl (by linear_combination h3))
    · exact Or.inr (Or.inr (Or.inl (by linear_combination h'')))
  · exact Or.inr (Or.inr (Or.inr (by linear_combination h')))

/-- **Solución completa**: los pares `(a₁, r)` que cumplen el enunciado son
exactamente los cuatro descritos  -/
theorem isSolution_iff (a₁ r : ℂ) :
    IsSolution a₁ r ↔
      (r = 5 / 3 ∧ a₁ = 1) ∨
      (r = -(5 / 3) ∧ a₁ = 49 / 19) ∨
      (r = 5 * I / 3 ∧ a₁ = 49 / 481 * (-16 - 15 * I)) ∨
      (r = -(5 * I / 3) ∧ a₁ = 49 / 481 * (-16 + 15 * I)) := by
  obtain ⟨p2, p3, p4, p5, p6, p7⟩ := I_pow_values
  constructor
  · intro h
    have h1 := h.1
    simp only [geomTerm] at h1
    rcases ratio_cases h with rfl | rfl | rfl | rfl
    · exact Or.inl ⟨rfl, by linear_combination (9 / 49 : ℂ) * h1⟩
    · refine Or.inr (Or.inl ⟨rfl, ?_⟩)
      linear_combination (9 / 19 : ℂ) * h1
    · refine Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩))
      linear_combination (9 / 481 * (-16 - 15 * I)) * h1 +
        (25 / 9 * (9 / 481 * (-16 - 15 * I)) * a₁ + a₁ * 1025 / 481 + a₁ * I * 750 / 481) * p2
    · refine Or.inr (Or.inr (Or.inr ⟨rfl, ?_⟩))
      linear_combination (9 / 481 * (-16 + 15 * I)) * h1 +
        (25 / 9 * (9 / 481 * (-16 + 15 * I)) * a₁ + a₁ * 1025 / 481 - a₁ * I * 750 / 481) * p2
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      refine ⟨?_, ?_⟩ <;> simp only [geomTerm] <;> ring_nf <;>
      simp only [p2, p3, p4, p5, p6, p7] <;> ring

/-- Caso 1 (`r = 5/3`, `a₁ = 1`): los siete términos. -/
theorem sevenTerms_case_one :
    sevenTerms 1 (5 / 3) =
      [1, 5 / 3, 25 / 9, 125 / 27, 625 / 81, 3125 / 243, 15625 / 729] := by
  norm_num [sevenTerms, geomTerm, List.range_succ]

/-- Caso 2 (`r = -5/3`, `a₁ = 49/19`): los siete términos. -/
theorem sevenTerms_case_two :
    sevenTerms (49 / 19) (-(5 / 3)) =
      [49 / 19, -(245 / 57), 1225 / 171, -(6125 / 513), 30625 / 1539,
        -(153125 / 4617), 765625 / 13851] := by
  norm_num [sevenTerms, geomTerm, List.range_succ]

/-- Caso 3 (`r = 5i/3`, `a₁ = (49/481)(-16-15i)`): los siete términos. -/
theorem sevenTerms_case_three :
    sevenTerms (49 / 481 * (-16 - 15 * I)) (5 * I / 3) =
      [49 / 481 * (-16 - 15 * I), 245 / 1443 * (15 - 16 * I),
        1225 / 4329 * (16 + 15 * I), 6125 / 12987 * (-15 + 16 * I),
        30625 / 38961 * (-16 - 15 * I), 153125 / 116883 * (15 - 16 * I),
        765625 / 350649 * (16 + 15 * I)] := by
  obtain ⟨p2, p3, p4, p5, p6, p7⟩ := I_pow_values
  simp only [sevenTerms, geomTerm, List.range_succ, List.range_zero, List.map_nil,
    List.map_cons, List.nil_append, List.cons_append, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring_nf <;>
    simp only [p2, p3, p4, p5, p6, p7] <;> ring

/-- Caso 4 (`r = -5i/3`, `a₁ = (49/481)(-16+15i)`): los siete términos.

**Corrección  .**   
`a₄ = (6125/12987)(15 + 16i)`, pero el valor correcto es
`a₄ = (6125/12987)(-15 - 16i)` (el opuesto): el error proviene del signo del término
`r² = -25/9` al calcular `r + r² + r³ = (-75 + 80i)/27` en la expresión (2)
(en el PDF aparece `+75` en lugar de `-75`).  Obsérvese que el caso 4 debe ser el
conjugado del caso 3, y que los valores `a₅, a₆, a₇` que da  son los que
se obtienen de este `a₄` corregido.  El resto de términos coincide con el PDF. -/
theorem sevenTerms_case_four :
    sevenTerms (49 / 481 * (-16 + 15 * I)) (-(5 * I / 3)) =
      [49 / 481 * (-16 + 15 * I), 245 / 1443 * (15 + 16 * I),
        1225 / 4329 * (16 - 15 * I), 6125 / 12987 * (-15 - 16 * I),
        30625 / 38961 * (-16 + 15 * I), 153125 / 116883 * (15 + 16 * I),
        765625 / 350649 * (16 - 15 * I)] := by
  obtain ⟨p2, p3, p4, p5, p6, p7⟩ := I_pow_values
  simp only [sevenTerms, geomTerm, List.range_succ, List.range_zero, List.map_nil,
    List.map_cons, List.nil_append, List.cons_append, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring_nf <;>
    simp only [p2, p3, p4, p5, p6, p7] <;> ring

/-- El valor `a₄ = (6125/12987)(15 + 16i)` que aparece en el   caso 4
es **incorrecto**: el cuarto término de esa progresión es su opuesto. -/
theorem pdf_case_four_a4_incorrect :
    geomTerm (49 / 481 * (-16 + 15 * I)) (-(5 * I / 3)) 3 ≠ 6125 / 12987 * (15 + 16 * I) := by
  obtain ⟨-, p3, p4, -, -, -⟩ := I_pow_values
  have hval : geomTerm (49 / 481 * (-16 + 15 * I)) (-(5 * I / 3)) 3
      = 6125 / 12987 * (-15 - 16 * I) := by
    simp only [geomTerm]; ring_nf; simp only [p3, p4]; ring
  rw [hval]
  simp [Complex.ext_iff]
  norm_num

end Retos20230203
