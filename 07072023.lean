import Mathlib

/-!
# Retos Matemáticos, 7 de julio de 2023

Dado el polinomio con coeficientes complejos (`α β : ℂ`)

  `P(x) = (x^4 + 5x^3 + α x - 13^4) * (x^3 - 10x^2 + β x + 6i)`

se pide

a) demostrar que `P` tiene a lo sumo tres raíces enteras (para cualesquiera `α, β ∈ ℂ`);
b) demostrar que existen valores de `α` y `β` para los que `P` tiene tres raíces enteras
   distintas de la forma `n`, `-n` y `m`.

La solución sigue el argumento del enunciado: el primer factor tiene a lo sumo dos raíces
enteras y el segundo a lo sumo una; y para `α = -845`, `β = 9 - 6i` se obtienen las raíces
`13`, `-13` y `1`.
-/

namespace RetoJul2023

open Complex

/-- El primer factor: `f α x = x^4 + 5x^3 + α x - 13^4`. -/
noncomputable def f (α x : ℂ) : ℂ := x ^ 4 + 5 * x ^ 3 + α * x - 13 ^ 4

/-- El segundo factor: `g β x = x^3 - 10x^2 + β x + 6i`. -/
noncomputable def g (β x : ℂ) : ℂ := x ^ 3 - 10 * x ^ 2 + β * x + 6 * Complex.I

/-- El polinomio del enunciado: `P α β x = f α x * g β x`. -/
noncomputable def P (α β x : ℂ) : ℂ := f α x * g β x

/-! ### Análisis entero del primer factor -/

/-- Toda raíz entera `x` de `x^4 + 5x^3 + a x - 13^4` (con `a ∈ ℤ`) divide a `13^4`, y el
valor de `a` queda determinado por la raíz. -/
lemma int_root_char (a x : ℤ) (h : x ^ 4 + 5 * x ^ 3 + a * x = 28561) :
    (x = 1 ∧ a = 28555) ∨ (x = -1 ∧ a = -28565) ∨ (x = 13 ∧ a = -845) ∨
    (x = -13 ∧ a = -845) ∨ (x = 169 ∧ a = -4969445) ∨ (x = -169 ∧ a = 4683835) ∨
    (x = 2197 ∧ a = -10628633405) ∨ (x = -2197 ∧ a = 10580365315) ∨
    (x = 28561 ∧ a = -23302163776085) ∨ (x = -28561 ∧ a = 23294006468875) := by
  have hdvd : x ∣ 28561 := ⟨x ^ 3 + 5 * x ^ 2 + a, by linear_combination -h⟩
  have h2 : x.natAbs ∣ (13 : ℕ) ^ 4 := by
    have := Int.natAbs_dvd_natAbs.mpr hdvd
    simpa using this
  obtain ⟨i, hi, hx⟩ := (Nat.dvd_prime_pow (by norm_num)).mp h2
  interval_cases i <;> simp at hx <;>
    rcases Int.natAbs_eq_iff.mp hx with h' | h' <;> subst h' <;> norm_num at h ⊢ <;> omega

/-- Si `x^4 + 5x^3 + a x - 13^4` tiene dos raíces enteras distintas, entonces `a = -845`
y las raíces son `13` y `-13`. -/
lemma int_two_roots (a r s : ℤ) (hrs : r ≠ s)
    (hr : r ^ 4 + 5 * r ^ 3 + a * r = 28561) (hs : s ^ 4 + 5 * s ^ 3 + a * s = 28561) :
    a = -845 ∧ (r = 13 ∨ r = -13) ∧ (s = 13 ∨ s = -13) := by
  have h1 := int_root_char a r hr
  have h2 := int_root_char a s hs
  rcases h1 with ⟨e1, e2⟩|⟨e1, e2⟩|⟨e1, e2⟩|⟨e1, e2⟩|⟨e1, e2⟩|⟨e1, e2⟩|⟨e1, e2⟩|⟨e1, e2⟩|
      ⟨e1, e2⟩|⟨e1, e2⟩ <;>
    rcases h2 with ⟨f1, f2⟩|⟨f1, f2⟩|⟨f1, f2⟩|⟨f1, f2⟩|⟨f1, f2⟩|⟨f1, f2⟩|⟨f1, f2⟩|⟨f1, f2⟩|
      ⟨f1, f2⟩|⟨f1, f2⟩ <;> omega

/-! ### Traducción a ℂ: el primer factor tiene a lo sumo dos raíces enteras -/

/-- Si `α` es (la imagen de) un entero `a`, una raíz entera de `f α` da una ecuación
entera. -/
lemma f_int_eq (a r : ℤ) (h : f ((a : ℤ) : ℂ) ((r : ℤ) : ℂ) = 0) :
    r ^ 4 + 5 * r ^ 3 + a * r = 28561 := by
  have : ((r ^ 4 + 5 * r ^ 3 + a * r : ℤ) : ℂ) = ((28561 : ℤ) : ℂ) := by
    push_cast
    unfold f at h
    linear_combination h
  exact_mod_cast this

/-- Dos raíces enteras distintas de `f α` determinan `α`, que resulta ser un entero. -/
lemma f_alpha_int (α : ℂ) (r s : ℤ) (hrs : r ≠ s) (hr : f α r = 0) (hs : f α s = 0) :
    α = ((-(r ^ 3 + r ^ 2 * s + r * s ^ 2 + s ^ 3) - 5 * (r ^ 2 + r * s + s ^ 2) : ℤ) : ℂ) := by
  have hne : ((r : ℂ) - s) ≠ 0 := by
    simp only [sub_ne_zero]
    exact_mod_cast fun hc => hrs (by exact_mod_cast hc)
  have key : (α - ((-(r ^ 3 + r ^ 2 * s + r * s ^ 2 + s ^ 3) - 5 * (r ^ 2 + r * s + s ^ 2) : ℤ) : ℂ))
      * ((r : ℂ) - s) = 0 := by
    unfold f at hr hs
    push_cast
    linear_combination hr - hs
  rcases mul_eq_zero.mp key with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hne

/-- Si `f α` tiene dos raíces enteras distintas, necesariamente `α = -845`. -/
lemma f_two_roots_alpha (α : ℂ) (r s : ℤ) (hrs : r ≠ s) (hr : f α r = 0) (hs : f α s = 0) :
    α = ((-845 : ℤ) : ℂ) := by
  have hα := f_alpha_int α r s hrs hr hs
  set a : ℤ := -(r ^ 3 + r ^ 2 * s + r * s ^ 2 + s ^ 3) - 5 * (r ^ 2 + r * s + s ^ 2) with ha
  rw [hα] at hr hs
  have h1 := f_int_eq a r hr
  have h2 := f_int_eq a s hs
  have := (int_two_roots a r s hrs h1 h2).1
  rw [hα, this]

/-! ### El segundo factor tiene a lo sumo una raíz entera -/

/-- Un entero más `6i` nunca es cero. -/
lemma int_add_six_I_ne_zero (X : ℤ) : ((X : ℂ) + 6 * Complex.I) ≠ 0 := by
  intro h
  have h3 := congrArg Complex.im h
  simp at h3

/-- `g β` no puede tener dos raíces enteras distintas: el término `6i` lo impide. -/
lemma g_no_two_roots (β : ℂ) (m k : ℤ) (hmk : m ≠ k) (hm : g β m = 0) (hk : g β k = 0) :
    False := by
  have hne : ((m : ℂ) - k) ≠ 0 := by
    simp only [sub_ne_zero]
    exact_mod_cast fun hc => hmk (by exact_mod_cast hc)
  have key : (β - ((10 * (m + k) - (m ^ 2 + m * k + k ^ 2) : ℤ) : ℂ)) * ((m : ℂ) - k) = 0 := by
    unfold g at hm hk
    push_cast
    linear_combination hm - hk
  have hβ : β = ((10 * (m + k) - (m ^ 2 + m * k + k ^ 2) : ℤ) : ℂ) := by
    rcases mul_eq_zero.mp key with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hne
  rw [hβ] at hm
  unfold g at hm
  refine int_add_six_I_ne_zero (m ^ 3 - 10 * m ^ 2 + (10 * (m + k) - (m ^ 2 + m * k + k ^ 2)) * m) ?_
  push_cast
  push_cast at hm
  linear_combination hm

/-! ### Las raíces enteras de cada factor caben en un conjunto pequeño -/

/-- Las raíces enteras de `f α` están contenidas en un conjunto de a lo sumo dos elementos. -/
lemma f_roots_finset (α : ℂ) : ∃ T : Finset ℤ, T.card ≤ 2 ∧ ∀ n : ℤ, f α n = 0 → n ∈ T := by
  by_cases h : ∃ r s : ℤ, r ≠ s ∧ f α r = 0 ∧ f α s = 0
  · obtain ⟨r, s, hrs, hr, hs⟩ := h
    have hα : α = ((-845 : ℤ) : ℂ) := f_two_roots_alpha α r s hrs hr hs
    refine ⟨{13, -13}, by decide, ?_⟩
    intro n hn
    rw [hα] at hn
    have := f_int_eq (-845) n hn
    have hc := int_root_char (-845) n this
    have : n = 13 ∨ n = -13 := by omega
    rcases this with h' | h' <;> simp [h']
  · push_neg at h
    by_cases h0 : ∃ r : ℤ, f α r = 0
    · obtain ⟨r, hr⟩ := h0
      refine ⟨{r}, by simp, ?_⟩
      intro n hn
      by_cases hnr : n = r
      · simp [hnr]
      · exact absurd hr (h n r hnr hn)
    · push_neg at h0
      exact ⟨∅, by simp, fun n hn => absurd hn (h0 n)⟩

/-- Las raíces enteras de `g β` están contenidas en un conjunto de a lo sumo un elemento. -/
lemma g_roots_finset (β : ℂ) : ∃ T : Finset ℤ, T.card ≤ 1 ∧ ∀ n : ℤ, g β n = 0 → n ∈ T := by
  by_cases h0 : ∃ r : ℤ, g β r = 0
  · obtain ⟨r, hr⟩ := h0
    refine ⟨{r}, by simp, ?_⟩
    intro n hn
    by_cases hnr : n = r
    · simp [hnr]
    · exact absurd (g_no_two_roots β n r hnr hn hr) (by simp)
  · push_neg at h0
    exact ⟨∅, by simp, fun n hn => absurd hn (h0 n)⟩

/-! ### Apartado (a) -/

/-- **Apartado (a)**: para cualesquiera `α, β ∈ ℂ`, el conjunto de las raíces enteras de
`P` es finito y tiene a lo sumo tres elementos. -/
theorem part_a (α β : ℂ) :
    {n : ℤ | P α β (n : ℂ) = 0}.Finite ∧ {n : ℤ | P α β (n : ℂ) = 0}.ncard ≤ 3 := by
  obtain ⟨T₁, hT₁card, hT₁⟩ := f_roots_finset α
  obtain ⟨T₂, hT₂card, hT₂⟩ := g_roots_finset β
  have hsub : {n : ℤ | P α β (n : ℂ) = 0} ⊆ ↑(T₁ ∪ T₂) := by
    intro n hn
    have hn' : f α n * g β n = 0 := hn
    rcases mul_eq_zero.mp hn' with h | h
    · simp [hT₁ n h]
    · simp [hT₂ n h]
  have hfin : {n : ℤ | P α β (n : ℂ) = 0}.Finite :=
    Set.Finite.subset (T₁ ∪ T₂).finite_toSet hsub
  refine ⟨hfin, ?_⟩
  have hcard : (T₁ ∪ T₂).card ≤ 3 :=
    le_trans (Finset.card_union_le T₁ T₂) (by omega)
  calc {n : ℤ | P α β (n : ℂ) = 0}.ncard ≤ (↑(T₁ ∪ T₂) : Set ℤ).ncard :=
        Set.ncard_le_ncard hsub (T₁ ∪ T₂).finite_toSet
    _ = (T₁ ∪ T₂).card := Set.ncard_coe_finset _
    _ ≤ 3 := hcard

/-! ### Apartado (b) -/

/-- **Apartado (b)**: para `α = -845` y `β = 9 - 6i`, el polinomio `P` tiene las tres
raíces enteras distintas `13`, `-13` y `1`, es decir, de la forma `n`, `-n` y `m`. -/
theorem part_b : ∃ (α β : ℂ) (n m : ℤ), n ≠ 0 ∧ m ≠ n ∧ m ≠ -n ∧
    P α β ((n : ℤ) : ℂ) = 0 ∧ P α β ((-n : ℤ) : ℂ) = 0 ∧ P α β ((m : ℤ) : ℂ) = 0 := by
  refine ⟨-845, 9 - 6 * Complex.I, 13, 1, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩ <;>
    simp only [P, f, g] <;> push_cast <;> ring_nf
