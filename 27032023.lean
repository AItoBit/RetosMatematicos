import Mathlib

/-!
# Reto Matemático del 27 de marzo de 2023

**Enunciado.** Si `x ∈ ℕ` verifica
`(x+5)^x = 11*x^x + 3 + α`, donde `α` es el valor del radical infinito
`α = ˣ√(x·ˣ√(x·ˣ√(x ⋯)))`, calcúlese la suma
`S = 3 + 7/x^x + 11/x^(2x) + 15/x^(3x) + 19/x^(4x) + ⋯`.

**Solución.** El radical infinito `α` es un real `α ≥ 1` con `α^x = x·α`
(concretamente `α = x^(1/(x-1))` cuando `x > 1`). La ecuación del enunciado obliga a
`x = 2` (y entonces `α = 2`), de donde `x^x = 4` y

`S = ∑_{n=0}^∞ (4n+3)/4^n = 52/9`.

En la formalización el radical infinito se representa por un número real `A`
caracterizado por sus dos propiedades: `1 ≤ A` y `A^x = x·A`.
-/

namespace Reto27Marzo2023

open scoped BigOperators

/-! ## El radical infinito -/

/-- El valor del radical infinito `ˣ√(x·ˣ√(x·ˣ√(x ⋯)))` para `x > 1`,
es decir `α(x) = x^(1/(x-1))`. -/
noncomputable def alpha (x : ℝ) : ℝ := x ^ (1 / (x - 1) : ℝ)

/-- `α(x)` satisface la ecuación característica del radical infinito: `α^x = x·α`
(potencias reales). -/
theorem alpha_rpow_self (x : ℝ) (hx : 1 < x) :
    (alpha x) ^ x = x * alpha x := by
  have hx0 : (0:ℝ) < x := lt_trans zero_lt_one hx
  have hne : x - 1 ≠ 0 := by linarith
  have h2 : x * x ^ (1 / (x - 1) : ℝ) = x ^ (1 + 1 / (x - 1) : ℝ) := by
    rw [Real.rpow_add hx0, Real.rpow_one]
  unfold alpha
  rw [h2, ← Real.rpow_mul hx0.le]
  congr 1
  field_simp
  ring

/-- `α(x) > 1` para `x > 1`. -/
theorem one_lt_alpha (x : ℝ) (hx : 1 < x) : 1 < alpha x := by
  unfold alpha
  exact (Real.one_lt_rpow_iff_of_pos (by linarith)).2
    (Or.inl ⟨hx, div_pos one_pos (by linarith)⟩)

/-- Unicidad: si `x > 1` y `A > 1` verifica la ecuación característica `A^x = x·A`
(potencias reales), entonces `A = α(x) = x^(1/(x-1))`. -/
theorem alpha_unique (x A : ℝ) (hx : 1 < x) (hA : 1 < A) (h : A ^ x = x * A) : A = alpha x := by
  have hA0 : (0:ℝ) < A := lt_trans zero_lt_one hA
  have hne : x - 1 ≠ 0 := by linarith
  have h1 : A ^ (x - 1 : ℝ) = x := by
    have hsub : A ^ (x - 1 : ℝ) = A ^ x / A ^ (1:ℝ) := by rw [← Real.rpow_sub hA0]
    rw [hsub, h, Real.rpow_one]
    field_simp
  have h2 : (A ^ (x - 1 : ℝ)) ^ (1 / (x - 1) : ℝ) = A := by
    rw [← Real.rpow_mul hA0.le, mul_one_div, div_self hne, Real.rpow_one]
  rw [← h2, h1]
  rfl

/-- Versión con exponente natural: para `x ≥ 2` natural, el único real `A > 1` con
`A^x = x·A` es el radical infinito `α(x)`. -/
theorem alpha_eq_of_pow (x : ℕ) (hx : 2 ≤ x) (A : ℝ) (hA : 1 < A) (h : A ^ x = (x : ℝ) * A) :
    A = alpha x := by
  have hx1 : (1:ℝ) < (x : ℝ) := by exact_mod_cast hx.trans_lt' one_lt_two
  refine alpha_unique (x : ℝ) A hx1 hA ?_
  rw [Real.rpow_natCast, h]

/-! ## La ecuación del enunciado obliga a `x = 2` -/

/-- Para `k ≥ 2` se tiene `k + 1 < 2^k`. -/
theorem lt_two_pow_of_two_le (k : ℕ) (hk : 2 ≤ k) : (k : ℤ) + 1 < 2 ^ k := by
  induction k with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n
      · omega
      · norm_num
    · have hn := ih h
      have h2 : (0:ℤ) < 2 ^ n := by positivity
      push_cast
      rw [pow_succ]
      linarith

/-- Si `x ∈ ℕ` y `A ≥ 1` es un real con `A^x = x·A` (la ecuación que caracteriza al
radical infinito) y se cumple la ecuación del enunciado `(x+5)^x = 11·x^x + 3 + A`,
entonces necesariamente `x = 2` y `A = 2`. -/
theorem eq_two_of_equation (x : ℕ) (A : ℝ) (hA : 1 ≤ A) (hpow : A ^ x = x * A)
    (heq : ((x : ℝ) + 5) ^ x = 11 * (x : ℝ) ^ x + 3 + A) : x = 2 ∧ A = 2 := by
  -- El miembro izquierdo y `11·x^x + 3` son enteros, luego `A` es un entero `z ≥ 1`.
  set z : ℤ := ((x : ℤ) + 5) ^ x - 11 * (x : ℤ) ^ x - 3 with hz
  have hzA : (z : ℝ) = A := by
    rw [hz]; push_cast; linarith [heq]
  have hz1 : 1 ≤ z := by
    have h : (1:ℝ) ≤ (z : ℝ) := by rw [hzA]; exact hA
    exact_mod_cast h
  have hzpow : z ^ x = (x : ℤ) * z := by
    have h : ((z ^ x : ℤ) : ℝ) = (((x : ℤ) * z : ℤ) : ℝ) := by push_cast [hzA]; exact hpow
    exact_mod_cast h
  match x, hzpow, heq with
  | 0, hzpow, heq => simp at hzpow
  | (k+1), hzpow, heq =>
    -- Cancelando un factor `z > 0`: `z^k = k+1`.
    have hzpos : (0:ℤ) < z := by omega
    have hzk : z ^ k = (k : ℤ) + 1 := by
      rw [pow_succ] at hzpow
      push_cast at hzpow
      exact mul_right_cancel₀ (ne_of_gt hzpos) hzpow
    rcases Nat.lt_or_ge k 2 with hk | hk
    · interval_cases k
      · -- `x = 1` no cumple la ecuación: el miembro izquierdo vale 6 y el derecho 14 + A ≥ 15.
        exfalso
        norm_num at heq
        linarith
      · -- `x = 2`, y entonces `z = 2`, es decir `A = 2`.
        simp only [pow_one] at hzk
        refine ⟨rfl, ?_⟩
        rw [← hzA, hzk]
        norm_num
    · -- Para `x = k+1 ≥ 3` sería `z^k = k+1` con `z ≥ 2`, imposible pues `2^k > k+1`.
      exfalso
      have hz2 : 2 ≤ z := by
        rcases eq_or_lt_of_le hz1 with h | h
        · exfalso; rw [← h] at hzk; simp at hzk; omega
        · omega
      have h1 : (2:ℤ) ^ k ≤ z ^ k := pow_le_pow_left₀ (by norm_num) hz2 k
      have h2 := lt_two_pow_of_two_le k hk
      omega

/-! ## La suma aritmético-geométrica -/

/-- Fórmula de la suma de una progresión aritmético-geométrica:
`∑_{n=0}^∞ (a·n + b)·r^n = a·r/(1-r)^2 + b/(1-r)` para `|r| < 1`. -/
theorem tsum_arith_geom (a b r : ℝ) (hr : |r| < 1) :
    ∑' n : ℕ, (a * n + b) * r ^ n = a * r / (1 - r) ^ 2 + b / (1 - r) := by
  have hr' : ‖r‖ < 1 := hr
  have h1 : HasSum (fun n : ℕ ↦ a * ((n : ℝ) * r ^ n)) (a * (r / (1 - r) ^ 2)) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hr').mul_left a
  have h2 : HasSum (fun n : ℕ ↦ b * r ^ n) (b * (1 - r)⁻¹) :=
    (hasSum_geometric_of_norm_lt_one hr').mul_left b
  have h3 := h1.add h2
  have h4 : HasSum (fun n : ℕ ↦ (a * n + b) * r ^ n) (a * r / (1 - r) ^ 2 + b / (1 - r)) := by
    have hfun : (fun n : ℕ ↦ a * ((n : ℝ) * r ^ n) + b * r ^ n)
        = fun n : ℕ ↦ (a * n + b) * r ^ n := by
      funext n; ring
    rw [hfun] at h3
    convert h3 using 1
    field_simp
  exact h4.tsum_eq

/-- La suma pedida (para `x = 2`, es decir `x^x = 4`): `∑_{n=0}^∞ (4n+3)/4^n = 52/9`. -/
theorem tsum_sol : ∑' n : ℕ, (4 * (n : ℝ) + 3) / 4 ^ n = 52 / 9 := by
  have h := tsum_arith_geom 4 3 (1 / 4) (by norm_num)
  norm_num at h ⊢
  rw [← h]
  congr 1
  funext n
  rw [div_pow, one_pow]
  ring

/-! ## Solución completa del problema -/

/-- **Solución del reto.** Si `x ∈ ℕ` y el radical infinito `A` (caracterizado por
`1 ≤ A` y `A^x = x·A`) verifican la ecuación `(x+5)^x = 11·x^x + 3 + A`, entonces
`x = 2`, `A = 2` y la suma
`S = 3 + 7/x^x + 11/x^(2x) + 15/x^(3x) + ⋯ = ∑_{n≥0} (4n+3)/(x^x)^n` vale `52/9`. -/
theorem reto_27_marzo_2023 (x : ℕ) (A : ℝ) (hA : 1 ≤ A) (hpow : A ^ x = x * A)
    (heq : ((x : ℝ) + 5) ^ x = 11 * (x : ℝ) ^ x + 3 + A) :
    x = 2 ∧ A = 2 ∧ ∑' n : ℕ, (4 * (n : ℝ) + 3) / ((x : ℝ) ^ x) ^ n = 52 / 9 := by
  obtain ⟨hx, hA2⟩ := eq_two_of_equation x A hA hpow heq
  refine ⟨hx, hA2, ?_⟩
  subst hx
  norm_num
  exact tsum_sol

end Reto27Marzo2023

namespace Reto27Marzo2023

/-- Las hipótesis del reto son satisfacibles: `x = 2`, `A = 2` las cumple
(y por el teorema anterior es la única posibilidad). -/
example : (1:ℝ) ≤ 2 ∧ (2:ℝ) ^ (2:ℕ) = ((2:ℕ) : ℝ) * 2 ∧
    (((2:ℕ) : ℝ) + 5) ^ (2:ℕ) = 11 * ((2:ℕ) : ℝ) ^ (2:ℕ) + 3 + 2 := by
  norm_num

end Reto27Marzo2023
