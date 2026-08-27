import Mathlib

/-!
# Retos Matemáticos, 12 de enero de 2024

**Ejercicio.** Dados dos puntos distintos cualesquiera `P` y `Q` del plano, ¿existe alguna curva
(no tiene por qué ser diferenciable) tal que empiece en `P`, acabe en `Q` y no contenga ningún
punto racional (con ambas coordenadas racionales)?

**Respuesta: sí** (salvo, necesariamente, en los propios extremos `P` y `Q`, que pueden ser
racionales).

Formalizamos la solución general (2ª/4ª forma del documento): si `A ⊆ ℝ²` es numerable, entonces
dados `P ≠ Q` existe una curva continua de `P` a `Q` cuyos puntos interiores evitan `A`.

La familia no numerable de curvas que usamos es la de los "arcos abombados"
`γ_r(t) = (1-t)P + tQ + t(1-t)·r·N`, donde `N` es un vector normal a `Q - P`. Dos de ellas
sólo se cortan en `P` y `Q`, así que si todas ellas cortasen a `A` obtendríamos una inyección
de `ℝ` en `A`, lo cual es imposible por ser `A` numerable.
-/

namespace RetosMatematicos

open Set

/-- Familia de curvas de `P` a `Q`: el segmento `[P,Q]` deformado por un "abombamiento"
de amplitud `r` en la dirección normal a `Q - P`. -/
noncomputable def bulgePath (P Q : ℝ × ℝ) (r : ℝ) (t : ℝ) : ℝ × ℝ :=
  ((1 - t) * P.1 + t * Q.1 - t * (1 - t) * r * (Q.2 - P.2),
   (1 - t) * P.2 + t * Q.2 + t * (1 - t) * r * (Q.1 - P.1))

/-- El conjunto de los puntos racionales del plano: aquellos con ambas coordenadas racionales. -/
def rationalPoints : Set (ℝ × ℝ) :=
  {z | z.1 ∈ Set.range ((↑) : ℚ → ℝ) ∧ z.2 ∈ Set.range ((↑) : ℚ → ℝ)}

theorem rationalPoints_countable : rationalPoints.Countable := by
  have : rationalPoints = (Set.range ((↑) : ℚ → ℝ)) ×ˢ (Set.range ((↑) : ℚ → ℝ)) := rfl
  rw [this]
  exact (Set.countable_range _).prod (Set.countable_range _)

theorem bulgePath_continuous (P Q : ℝ × ℝ) (r : ℝ) : Continuous (bulgePath P Q r) := by
  unfold bulgePath
  fun_prop

@[simp] theorem bulgePath_zero (P Q : ℝ × ℝ) (r : ℝ) : bulgePath P Q r 0 = P := by
  simp [bulgePath]

@[simp] theorem bulgePath_one (P Q : ℝ × ℝ) (r : ℝ) : bulgePath P Q r 1 = Q := by
  simp [bulgePath]

/-- Las curvas de la familia son disjuntas dos a dos fuera de los extremos: si dos de ellas
pasan por el mismo punto con parámetros interiores, coinciden el parámetro y la amplitud. -/
theorem bulgePath_injective {P Q : ℝ × ℝ} (hPQ : P ≠ Q) {r r' t t' : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (ht' : t' ∈ Ioo (0 : ℝ) 1)
    (h : bulgePath P Q r t = bulgePath P Q r' t') : t = t' ∧ r = r' := by
  obtain ⟨ht0, ht1⟩ := ht
  obtain ⟨ht0', ht1'⟩ := ht'
  set d1 : ℝ := Q.1 - P.1 with hd1
  set d2 : ℝ := Q.2 - P.2 with hd2
  have hd : 0 < d1 ^ 2 + d2 ^ 2 := by
    rcases lt_or_eq_of_le (add_nonneg (sq_nonneg d1) (sq_nonneg d2)) with hpos | hzero
    · exact hpos
    · exfalso
      have h1 : d1 = 0 := by nlinarith [sq_nonneg d1, sq_nonneg d2]
      have h2 : d2 = 0 := by nlinarith [sq_nonneg d1, sq_nonneg d2]
      refine hPQ (Prod.ext ?_ ?_)
      · simp only [hd1] at h1; linarith
      · simp only [hd2] at h2; linarith
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  simp only [bulgePath] at hx hy
  set u : ℝ := t * (1 - t) * r with hu
  set u' : ℝ := t' * (1 - t') * r' with hu'
  have e1 : (t - t') * d1 - (u - u') * d2 = 0 := by
    simp only [hd1, hd2, hu, hu']; nlinarith [hx]
  have e2 : (t - t') * d2 + (u - u') * d1 = 0 := by
    simp only [hd1, hd2, hu, hu']; nlinarith [hy]
  have k1 : (t - t') * (d1 ^ 2 + d2 ^ 2) = 0 := by linear_combination d1 * e1 + d2 * e2
  have k2 : (u - u') * (d1 ^ 2 + d2 ^ 2) = 0 := by linear_combination (-d2) * e1 + d1 * e2
  have hteq : t = t' := by
    rcases mul_eq_zero.mp k1 with hk | hk
    · linarith
    · exact absurd hk (ne_of_gt hd)
  refine ⟨hteq, ?_⟩
  have hueq : u = u' := by
    rcases mul_eq_zero.mp k2 with hk | hk
    · linarith
    · exact absurd hk (ne_of_gt hd)
  have hne : t * (1 - t) ≠ 0 := by
    have : (0 : ℝ) < t * (1 - t) := by nlinarith
    exact ne_of_gt this
  rw [hu, hu', ← hteq] at hueq
  exact mul_left_cancel₀ hne hueq

/-- **Proposición general.** Si `A ⊆ ℝ²` es numerable y `P ≠ Q`, existe una curva continua
`γ : [0,1] → ℝ²` con `γ 0 = P`, `γ 1 = Q` cuyos puntos interiores evitan `A`. -/
theorem exists_continuous_path_avoiding_countable
    (A : Set (ℝ × ℝ)) (hA : A.Countable) (P Q : ℝ × ℝ) (hPQ : P ≠ Q) :
    ∃ γ : ℝ → ℝ × ℝ, Continuous γ ∧ γ 0 = P ∧ γ 1 = Q ∧ ∀ t ∈ Ioo (0 : ℝ) 1, γ t ∉ A := by
  classical
  set B : Set ℝ := {r | ∃ t ∈ Ioo (0 : ℝ) 1, bulgePath P Q r t ∈ A} with hB
  -- una elección de parámetro malo para cada `r ∈ B`
  set f : ℝ → ℝ := fun r => if h : ∃ t ∈ Ioo (0 : ℝ) 1, bulgePath P Q r t ∈ A then h.choose else 0
    with hf
  have hfspec : ∀ r ∈ B, f r ∈ Ioo (0 : ℝ) 1 ∧ bulgePath P Q r (f r) ∈ A := by
    intro r hr
    have h : ∃ t ∈ Ioo (0 : ℝ) 1, bulgePath P Q r t ∈ A := hr
    simp only [hf, dite_eq_left h]
    exact ⟨h.choose_spec.1, h.choose_spec.2⟩
  have hBc : B.Countable := by
    refine Set.MapsTo.countable_of_injOn (f := fun r => bulgePath P Q r (f r)) ?_ ?_ hA
    · intro r hr
      exact (hfspec r hr).2
    · intro r hr r' hr' hEq
      exact (bulgePath_injective hPQ (hfspec r hr).1 (hfspec r' hr').1 hEq).2
  -- existe una amplitud buena, pues `ℝ` no es numerable
  have : ∃ r : ℝ, r ∉ B := by
    by_contra hcon
    have hBuniv : ∀ x : ℝ, x ∈ B := fun x => by_contra fun hx => hcon ⟨x, hx⟩
    exact Cardinal.not_countable_real (hBc.mono (fun x _ => hBuniv x))
  obtain ⟨r, hr⟩ := this
  refine ⟨bulgePath P Q r, bulgePath_continuous P Q r, bulgePath_zero P Q r,
    bulgePath_one P Q r, ?_⟩
  intro t ht hmem
  exact hr ⟨t, ht, hmem⟩

/-- Versión con imágenes: la traza de la curva, salvo sus extremos, está contenida en el
complementario de `A`. -/
theorem exists_continuous_path_image_avoiding_countable
    (A : Set (ℝ × ℝ)) (hA : A.Countable) (P Q : ℝ × ℝ) (hPQ : P ≠ Q) :
    ∃ γ : ℝ → ℝ × ℝ, Continuous γ ∧ γ 0 = P ∧ γ 1 = Q ∧
      (γ '' Icc (0 : ℝ) 1) \ {P, Q} ⊆ Aᶜ := by
  obtain ⟨γ, hcont, h0, h1, hint⟩ :=
    exists_continuous_path_avoiding_countable A hA P Q hPQ
  refine ⟨γ, hcont, h0, h1, ?_⟩
  rintro z ⟨⟨t, ht, rfl⟩, hz⟩
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hz
  have ht' : t ∈ Ioo (0 : ℝ) 1 := by
    rcases lt_or_eq_of_le ht.1 with h | h
    · rcases lt_or_eq_of_le ht.2 with h' | h'
      · exact ⟨h, h'⟩
      · exact absurd (h' ▸ h1) hz.2
    · exact absurd (h ▸ h0) hz.1
  exact hint t ht'

/-- **Corolario (respuesta al ejercicio).** Dados dos puntos distintos `P`, `Q` del plano,
existe una curva continua que empieza en `P`, acaba en `Q` y no contiene ningún punto racional
salvo, a lo sumo, los propios extremos. -/
theorem exists_continuous_path_avoiding_rationalPoints (P Q : ℝ × ℝ) (hPQ : P ≠ Q) :
    ∃ γ : ℝ → ℝ × ℝ, Continuous γ ∧ γ 0 = P ∧ γ 1 = Q ∧
      ∀ t ∈ Ioo (0 : ℝ) 1, γ t ∉ rationalPoints :=
  exists_continuous_path_avoiding_countable rationalPoints rationalPoints_countable P Q hPQ

/-- **Corolario, versión conjuntista.** La traza de la curva, quitando los extremos, no contiene
ningún punto de coordenadas ambas racionales. -/
theorem exists_continuous_path_image_avoiding_rationalPoints (P Q : ℝ × ℝ) (hPQ : P ≠ Q) :
    ∃ γ : ℝ → ℝ × ℝ, Continuous γ ∧ γ 0 = P ∧ γ 1 = Q ∧
      ((γ '' Icc (0 : ℝ) 1) \ {P, Q}) ∩ rationalPoints = ∅ := by
  obtain ⟨γ, hcont, h0, h1, hsub⟩ :=
    exists_continuous_path_image_avoiding_countable rationalPoints rationalPoints_countable P Q hPQ
  exact ⟨γ, hcont, h0, h1, by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hz1, hz2⟩
    exact hsub hz1 hz2⟩

/-- Si además ninguno de los extremos es racional, la curva entera evita los puntos racionales. -/
theorem exists_continuous_path_no_rationalPoints
    (P Q : ℝ × ℝ) (hPQ : P ≠ Q) (hP : P ∉ rationalPoints) (hQ : Q ∉ rationalPoints) :
    ∃ γ : ℝ → ℝ × ℝ, Continuous γ ∧ γ 0 = P ∧ γ 1 = Q ∧
      ∀ t ∈ Icc (0 : ℝ) 1, γ t ∉ rationalPoints := by
  obtain ⟨γ, hcont, h0, h1, hint⟩ := exists_continuous_path_avoiding_rationalPoints P Q hPQ
  refine ⟨γ, hcont, h0, h1, ?_⟩
  intro t ht
  rcases lt_or_eq_of_le ht.1 with h | h
  · rcases lt_or_eq_of_le ht.2 with h' | h'
    · exact hint t ⟨h, h'⟩
    · rw [h', h1]; exact hQ
  · rw [← h, h0]; exact hP

/-- La excepción en los extremos es necesaria: si `P` es un punto racional, ninguna curva que
empiece en `P` puede evitar todos los puntos racionales. -/
theorem endpoint_exception_necessary (γ : ℝ → ℝ × ℝ) (P : ℝ × ℝ) (h0 : γ 0 = P)
    (hP : P ∈ rationalPoints) : ∃ t ∈ Icc (0 : ℝ) 1, γ t ∈ rationalPoints :=
  ⟨0, ⟨le_rfl, zero_le_one⟩, h0 ▸ hP⟩

end RetosMatematicos
