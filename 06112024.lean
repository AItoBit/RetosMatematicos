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
# Retos Matemáticos, 6 de noviembre de 2024

Ejercicio (International Baccalaureate, Mayo 2024, AA HL P1 #7).

* a) `g(x) = 2x³ - 7x² + dx - e`, con `d, e ∈ ℝ`, tiene las tres raíces reales
  `α, β, γ`.  Determinar `α + β + γ`.
* b) `h(z) = 2z⁵ - 11z⁴ + rz³ + sz² + tz - 20`, con `r, s, t ∈ ℝ`, tiene entre sus
  raíces a `α, β, γ` y también a `p + 3i`.  Demostrar que `p = 1`.
* c) Si además `h(1/2) = 0`, `α, β` son enteros positivos con `α < β` y `γ ∈ ℚ`,
  determinar `αβ` y los valores de `α` y `β`.

En cada apartado la hipótesis "α, β, γ son las tres raíces de g" (resp. "α, β, γ,
p + 3i, p - 3i son las cinco raíces de h") se formaliza mediante la
descomposición factorial correspondiente, tal y como se usa en la solución.
-/

namespace RetosMatematicos20241106

open Complex

/-- El polinomio `g(x) = 2x³ - 7x² + dx - e` del apartado a). -/
def gPoly (d e x : ℝ) : ℝ := 2 * x ^ 3 - 7 * x ^ 2 + d * x - e

/-- El polinomio `h(z) = 2z⁵ - 11z⁴ + rz³ + sz² + tz - 20` de los apartados b) y c). -/
def hPoly (r s t : ℝ) (z : ℂ) : ℂ :=
  2 * z ^ 5 - 11 * z ^ 4 + (r : ℂ) * z ^ 3 + (s : ℂ) * z ^ 2 + (t : ℂ) * z - 20

/-! ### Apartado a) -/

/-- **Apartado a).**  Si `α, β, γ` son las tres raíces reales de
`g(x) = 2x³ - 7x² + dx - e` (es decir, `g(x) = 2(x-α)(x-β)(x-γ)`), entonces
`α + β + γ = 7/2`. -/
theorem sum_roots_g (d e a b c : ℝ)
    (hg : ∀ x : ℝ, gPoly d e x = 2 * (x - a) * (x - b) * (x - c)) :
    a + b + c = 7 / 2 := by
  have h1 := hg 1
  have h2 := hg (-1)
  have h3 := hg 2
  have h4 := hg (-2)
  simp only [gPoly] at h1 h2 h3 h4
  linear_combination (1 / 12) * h3 + (1 / 12) * h4 - (1 / 12) * h1 - (1 / 12) * h2

/-! ### Apartado b) -/

/-- **Apartado b).**  Si `α, β, γ, p + 3i, p - 3i` son las cinco raíces de
`h(z) = 2z⁵ - 11z⁴ + rz³ + sz² + tz - 20` y `α + β + γ = 7/2`, entonces `p = 1`. -/
theorem p_eq_one (r s t : ℝ) (a b c p : ℝ)
    (hsum : a + b + c = 7 / 2)
    (hh : ∀ z : ℂ, hPoly r s t z =
      2 * (z - (a : ℂ)) * (z - (b : ℂ)) * (z - (c : ℂ)) *
        (z - ((p : ℂ) + 3 * Complex.I)) * (z - ((p : ℂ) - 3 * Complex.I))) :
    p = 1 := by
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hsumC : (a : ℂ) + (b : ℂ) + (c : ℂ) = 7 / 2 := by
    have h := congrArg (fun x : ℝ => (x : ℂ)) hsum
    push_cast at h
    linear_combination h
  have h0 := hh 0
  have h1 := hh 1
  have h2 := hh (-1)
  have h3 := hh 2
  have h4 := hh (-2)
  simp only [hPoly] at h0 h1 h2 h3 h4
  have hp : (p : ℂ) = 1 := by
    linear_combination (1 / 96) * h3 + (1 / 96) * h4 - (1 / 24) * h1 - (1 / 24) * h2
      + (1 / 16) * h0 - (1 / 2) * hsumC
  exact_mod_cast hp

/-! ### Apartado c) -/

section PartC

variable (r s t : ℝ) (m n : ℤ) (c p : ℝ)

/-- Bajo las hipótesis del apartado c), la raíz racional `γ` vale `1/2`. -/
theorem gamma_eq_half
    (hm : 0 < m) (hn : 0 < n)
    (hsum : (m : ℝ) + (n : ℝ) + c = 7 / 2)
    (hh : ∀ z : ℂ, hPoly r s t z =
      2 * (z - (m : ℂ)) * (z - (n : ℂ)) * (z - (c : ℂ)) *
        (z - ((p : ℂ) + 3 * Complex.I)) * (z - ((p : ℂ) - 3 * Complex.I)))
    (hhalf : hPoly r s t (1 / 2) = 0) :
    c = 1 / 2 := by
  have hp : p = 1 := p_eq_one r s t (m : ℝ) (n : ℝ) c p hsum hh
  subst hp
  have hev := hh (1 / 2 : ℂ)
  rw [hhalf] at hev
  push_cast at hev
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  -- El factor cuadrático correspondiente al par conjugado vale `37/4 ≠ 0`.
  have hev' : ((2 * (1 / 2 - (m : ℝ)) * (1 / 2 - (n : ℝ)) * (1 / 2 - c) * (37 / 4) : ℝ) : ℂ)
      = ((0 : ℝ) : ℂ) := by
    push_cast
    linear_combination -hev
      + 18 * (1 / 2 - (m : ℂ)) * (1 / 2 - (n : ℂ)) * (1 / 2 - (c : ℂ)) * hI
  have hR : (2 * (1 / 2 - (m : ℝ)) * (1 / 2 - (n : ℝ)) * (1 / 2 - c) * (37 / 4) : ℝ) = 0 := by
    exact_mod_cast hev'
  have hmne : (1 / 2 - (m : ℝ)) ≠ 0 := by
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    intro hcon; linarith
  have hnne : (1 / 2 - (n : ℝ)) ≠ 0 := by
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    intro hcon; linarith
  have hzero : (1 / 2 - c) = 0 := by
    rcases mul_eq_zero.1 hR with h | h
    · rcases mul_eq_zero.1 h with h' | h'
      · rcases mul_eq_zero.1 h' with h'' | h''
        · rcases mul_eq_zero.1 h'' with h₃ | h₃
          · norm_num at h₃
          · exact absurd h₃ hmne
        · exact absurd h'' hnne
      · exact h'
    · norm_num at h
  linarith

/-- **Apartado c-i).**  El producto de las dos raíces enteras positivas es `2`.

La hipótesis `hrat` («γ es racional»), que figura en el enunciado, no resulta
necesaria: se deduce de las demás que `γ = 1/2`. -/
theorem product_eq_two
    (hm : 0 < m) (hn : 0 < n) (hmn : m < n)
    (hrat : ∃ q : ℚ, c = (q : ℝ))
    (hsum : (m : ℝ) + (n : ℝ) + c = 7 / 2)
    (hh : ∀ z : ℂ, hPoly r s t z =
      2 * (z - (m : ℂ)) * (z - (n : ℂ)) * (z - (c : ℂ)) *
        (z - ((p : ℂ) + 3 * Complex.I)) * (z - ((p : ℂ) - 3 * Complex.I)))
    (hhalf : hPoly r s t (1 / 2) = 0) :
    m * n = 2 := by
  have hc : c = 1 / 2 := gamma_eq_half r s t m n c p hm hn hsum hh hhalf
  subst hc
  have h3 : (m : ℝ) + (n : ℝ) = 3 := by linarith
  have h3' : m + n = 3 := by exact_mod_cast h3
  have hm1 : m = 1 := by omega
  have hn2 : n = 2 := by omega
  subst hm1; subst hn2; norm_num

/-- **Apartado c-ii).**  Los valores de las dos raíces enteras positivas son
`α = 1` y `β = 2`.

Como antes, la hipótesis `hrat` («γ es racional») del enunciado no es necesaria. -/
theorem roots_eq_one_two
    (hm : 0 < m) (hn : 0 < n) (hmn : m < n)
    (hrat : ∃ q : ℚ, c = (q : ℝ))
    (hsum : (m : ℝ) + (n : ℝ) + c = 7 / 2)
    (hh : ∀ z : ℂ, hPoly r s t z =
      2 * (z - (m : ℂ)) * (z - (n : ℂ)) * (z - (c : ℂ)) *
        (z - ((p : ℂ) + 3 * Complex.I)) * (z - ((p : ℂ) - 3 * Complex.I)))
    (hhalf : hPoly r s t (1 / 2) = 0) :
    m = 1 ∧ n = 2 := by
  have hc : c = 1 / 2 := gamma_eq_half r s t m n c p hm hn hsum hh hhalf
  subst hc
  have h3 : (m : ℝ) + (n : ℝ) = 3 := by linarith
  have h3' : m + n = 3 := by exact_mod_cast h3
  constructor <;> omega

end PartC

/-! ### Enunciado completo -/

/-- **El ejercicio completo.**

Sean `d, e, r, s, t ∈ ℝ`, sean `α = m` y `β = n` enteros con `0 < α < β`, sea
`γ ∈ ℝ` racional y sea `p ∈ ℝ`.  Supongamos que:

* `α, β, γ` son las tres raíces reales de `g(x) = 2x³ - 7x² + dx - e`;
* `α, β, γ, p + 3i, p - 3i` son las cinco raíces de
  `h(z) = 2z⁵ - 11z⁴ + rz³ + sz² + tz - 20`;
* `h(1/2) = 0`.

Entonces:  a) `α + β + γ = 7/2`;  b) `p = 1`;  c-i) `αβ = 2`;  c-ii) `α = 1`, `β = 2`. -/
theorem exercise_2024_11_06 (d e r s t : ℝ) (m n : ℤ) (c p : ℝ)
    (hm : 0 < m) (hn : 0 < n) (hmn : m < n)
    (hrat : ∃ q : ℚ, c = (q : ℝ))
    (hg : ∀ x : ℝ, gPoly d e x = 2 * (x - (m : ℝ)) * (x - (n : ℝ)) * (x - c))
    (hh : ∀ z : ℂ, hPoly r s t z =
      2 * (z - (m : ℂ)) * (z - (n : ℂ)) * (z - (c : ℂ)) *
        (z - ((p : ℂ) + 3 * Complex.I)) * (z - ((p : ℂ) - 3 * Complex.I)))
    (hhalf : hPoly r s t (1 / 2) = 0) :
    ((m : ℝ) + (n : ℝ) + c = 7 / 2) ∧ p = 1 ∧ m * n = 2 ∧ m = 1 ∧ n = 2 := by
  have hsum : (m : ℝ) + (n : ℝ) + c = 7 / 2 := sum_roots_g d e (m : ℝ) (n : ℝ) c hg
  have hp : p = 1 := p_eq_one r s t (m : ℝ) (n : ℝ) c p hsum hh
  have hprod : m * n = 2 :=
    product_eq_two r s t m n c p hm hn hmn hrat hsum hh hhalf
  have hmn' : m = 1 ∧ n = 2 :=
    roots_eq_one_two r s t m n c p hm hn hmn hrat hsum hh hhalf
  exact ⟨hsum, hp, hprod, hmn'.1, hmn'.2⟩

end RetosMatematicos20241106
