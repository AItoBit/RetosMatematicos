/-
  Retos Matemáticos — 5 de febrero de 2023 (ISSN 2952-0746)

  Ejercicio: hállese la suma infinita

    S = 1 - 1/3 - 2/9 + 1/27 - 1/81 - 2/243 + 1/729 - 1/2187 - 2/6561 + ...

  Resultado:  S = 6/13.

  Estrategia de la formalización:
  el patrón de coeficientes es periódico de periodo 3, (+1, -1, -2), sobre
  las potencias de 1/3.  Descomponemos la serie en las tres subseries
  soportadas en las progresiones aritméticas 3k, 3k+1, 3k+2; cada una es
  (una traslación de) la serie geométrica de razón 1/27.  Sumando:

      27/26 - 9/26 - 3/13 = 6/13.

  Esto es esencialmente la "2ª Forma" del boletín, pero justificando el
  reagrupamiento vía `Function.Injective.hasSum_iff` (que es incondicional
  para `HasSum` en ℝ, sin necesidad de invocar convergencia absoluta a mano).
-/
import Mathlib

namespace RetosMatematicos

/-! ### El término general -/

/-- Término general de la serie: coeficiente `+1, -1, -2` según `n % 3`,
    multiplicado por `(1/3)^n`. -/
noncomputable def a (n : ℕ) : ℝ :=
  if n % 3 = 0 then (1 / 3 : ℝ) ^ n
  else if n % 3 = 1 then -(1 / 3 : ℝ) ^ n
  else -2 * (1 / 3 : ℝ) ^ n

/-- Comprobación de que `a` reproduce los nueve primeros términos del enunciado. -/
example :
    a 0 = 1 ∧ a 1 = -(1 / 3) ∧ a 2 = -(2 / 9) ∧
    a 3 = 1 / 27 ∧ a 4 = -(1 / 81) ∧ a 5 = -(2 / 243) ∧
    a 6 = 1 / 729 ∧ a 7 = -(1 / 2187) ∧ a 8 = -(2 / 6561) := by
  norm_num [a]

/-! ### Las tres subseries -/

noncomputable def a₀ (n : ℕ) : ℝ := if n % 3 = 0 then (1 / 3 : ℝ) ^ n else 0
noncomputable def a₁ (n : ℕ) : ℝ := if n % 3 = 1 then -(1 / 3 : ℝ) ^ n else 0
noncomputable def a₂ (n : ℕ) : ℝ := if n % 3 = 2 then -2 * (1 / 3 : ℝ) ^ n else 0

theorem a_eq (n : ℕ) : a n = a₀ n + a₁ n + a₂ n := by
  have h : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h with h | h | h <;> simp [a, a₀, a₁, a₂, h]

/-! ### La serie geométrica de razón 1/27 -/

private theorem h27 : ((1 : ℝ) / 3) ^ 3 = 1 / 27 := by norm_num

theorem hasSum_geom : HasSum (fun k : ℕ => ((1 : ℝ) / 27) ^ k) (27 / 26) := by
  have h : HasSum (fun k : ℕ => ((1 : ℝ) / 27) ^ k) (1 - 1 / 27)⁻¹ :=
    hasSum_geometric_of_lt_one (by norm_num) (by norm_num)
  have e : (1 - (1 : ℝ) / 27)⁻¹ = 27 / 26 := by norm_num
  rwa [e] at h

/-! ### Suma de cada subserie -/

theorem hasSum_a₀ : HasSum a₀ (27 / 26) := by
  have hinj : Function.Injective (fun k : ℕ => 3 * k) := by
    intro x y hxy
    have h : 3 * x = 3 * y := hxy
    omega
  have hzero : ∀ n ∉ Set.range (fun k : ℕ => 3 * k), a₀ n = 0 := by
    intro n hn
    have h3 : n % 3 ≠ 0 := by
      intro h
      exact hn ⟨n / 3, by show 3 * (n / 3) = n; omega⟩
    simp [a₀, h3]
  rw [← hinj.hasSum_iff hzero]
  have hfun : (a₀ ∘ fun k : ℕ => 3 * k) = fun k : ℕ => ((1 : ℝ) / 27) ^ k := by
    funext k
    have hmod : 3 * k % 3 = 0 := by omega
    simp only [Function.comp_apply, a₀, hmod, eq_self_iff_true, if_true]
    rw [pow_mul, h27]
  rw [hfun]
  exact hasSum_geom

theorem hasSum_a₁ : HasSum a₁ (-(9 / 26)) := by
  have hinj : Function.Injective (fun k : ℕ => 3 * k + 1) := by
    intro x y hxy
    have h : 3 * x + 1 = 3 * y + 1 := hxy
    omega
  have hzero : ∀ n ∉ Set.range (fun k : ℕ => 3 * k + 1), a₁ n = 0 := by
    intro n hn
    have h3 : n % 3 ≠ 1 := by
      intro h
      exact hn ⟨n / 3, by show 3 * (n / 3) + 1 = n; omega⟩
    simp [a₁, h3]
  rw [← hinj.hasSum_iff hzero]
  have hfun : (a₁ ∘ fun k : ℕ => 3 * k + 1)
      = fun k : ℕ => -(1 / 3 : ℝ) * ((1 : ℝ) / 27) ^ k := by
    funext k
    have hmod : (3 * k + 1) % 3 = 1 := by omega
    simp only [Function.comp_apply, a₁, hmod, eq_self_iff_true, if_true]
    rw [pow_add, pow_mul, h27]
    ring
  have hval : (-(1 / 3 : ℝ)) * (27 / 26) = -(9 / 26) := by norm_num
  rw [hfun, ← hval]
  exact hasSum_geom.mul_left _

theorem hasSum_a₂ : HasSum a₂ (-(3 / 13)) := by
  have hinj : Function.Injective (fun k : ℕ => 3 * k + 2) := by
    intro x y hxy
    have h : 3 * x + 2 = 3 * y + 2 := hxy
    omega
  have hzero : ∀ n ∉ Set.range (fun k : ℕ => 3 * k + 2), a₂ n = 0 := by
    intro n hn
    have h3 : n % 3 ≠ 2 := by
      intro h
      exact hn ⟨n / 3, by show 3 * (n / 3) + 2 = n; omega⟩
    simp [a₂, h3]
  rw [← hinj.hasSum_iff hzero]
  have hfun : (a₂ ∘ fun k : ℕ => 3 * k + 2)
      = fun k : ℕ => -(2 / 9 : ℝ) * ((1 : ℝ) / 27) ^ k := by
    funext k
    have hmod : (3 * k + 2) % 3 = 2 := by omega
    simp only [Function.comp_apply, a₂, hmod, eq_self_iff_true, if_true]
    rw [pow_add, pow_mul, h27]
    ring
  have hval : (-(2 / 9 : ℝ)) * (27 / 26) = -(3 / 13) := by norm_num
  rw [hfun, ← hval]
  exact hasSum_geom.mul_left _

/-! ### El resultado -/

/-- **Reto (5-II-2023).**
    `1 - 1/3 - 2/9 + 1/27 - 1/81 - 2/243 + ⋯ = 6/13`. -/
theorem hasSum_a : HasSum a (6 / 13) := by
  have h := (hasSum_a₀.add hasSum_a₁).add hasSum_a₂
  have hfun : (fun n => a₀ n + a₁ n + a₂ n) = a := (funext a_eq).symm
  have hval : (27 / 26 : ℝ) + -(9 / 26) + -(3 / 13) = 6 / 13 := by norm_num
  rw [hfun, hval] at h
  exact h

/-- Versión con `tsum`. -/
theorem tsum_a : ∑' n : ℕ, a n = 6 / 13 := hasSum_a.tsum_eq

theorem summable_a : Summable a := hasSum_a.summable

/-! ### Apéndice: la serie agrupada  

Agrupando de tres en tres, cada bloque vale `1/3⁰ - 1/3¹ - 2/3² = 4/9`
multiplicado por `(1/27)^k`, y la suma es `(4/9)·(27/26) = 6/13`. -/

theorem hasSum_bloques :
    HasSum (fun k : ℕ => (4 / 9 : ℝ) * ((1 : ℝ) / 27) ^ k) (6 / 13) := by
  have hval : (4 / 9 : ℝ) * (27 / 26) = 6 / 13 := by norm_num
  rw [← hval]
  exact hasSum_geom.mul_left _

-- Comprobación: sin `sorryAx`.
#print axioms hasSum_a

end RetosMatematicos
