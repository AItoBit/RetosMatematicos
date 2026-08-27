import Mathlib

/-!
# Retos Matemáticos: Divisibilidad de $5^{2n} - 2^{3n}$ entre 17

Demostración de que para todo $n \in \mathbb{N}$:
$$17 \mid (5^{2n} - 2^{3n})$$
-/

/-! ### 1ª y 2ª Forma: Demostración por Inducción Matemática -/

theorem five_pow_two_sub_two_pow_three_dvd (n : ℕ) :
    (17 : ℤ) ∣ 5 ^ (2 * n) - 2 ^ (3 * n) := by
  induction n with
  | zero =>
    -- Caso base n = 0: 5^0 - 2^0 = 1 - 1 = 0, y 17 ∣ 0
    use 0
    ring
  | succ n ih =>
    -- Caso inductivo n + 1:
    -- Por hipótesis de inducción, 5^(2n) - 2^(3n) = 17 * k
    obtain ⟨k, hk⟩ := ih
    use 5 ^ (2 * n) + 8 * k

    -- Separamos las potencias: 5^(2(n+1)) = 5^(2n) * 25  y  2^(3(n+1)) = 2^(3n) * 8
    have h1 : (5 : ℤ) ^ (2 * (n + 1)) = 5 ^ (2 * n) * 25 := by
      calc
        (5 : ℤ) ^ (2 * (n + 1)) = 5 ^ (2 * n + 2) := by ring_nf
        _ = 5 ^ (2 * n) * 5 ^ 2                   := by rw [pow_add]
        _ = 5 ^ (2 * n) * 25                      := by norm_num

    have h2 : (2 : ℤ) ^ (3 * (n + 1)) = 2 ^ (3 * n) * 8 := by
      calc
        (2 : ℤ) ^ (3 * (n + 1)) = 2 ^ (3 * n + 3) := by ring_nf
        _ = 2 ^ (3 * n) * 2 ^ 3                   := by rw [pow_add]
        _ = 2 ^ (3 * n) * 8                       := by norm_num

    -- Sustituimos y cerramos algebraicamente usando la hipótesis de inducción
    rw [h1, h2]
    linear_combination 8 * hk

/-! ### Nota Adicional: Demostración por Aritmética Modular en `ZMod 17` -/

theorem five_pow_two_sub_two_pow_three_mod (n : ℕ) :
    ((5 : ZMod 17) ^ (2 * n) - (2 : ZMod 17) ^ (3 * n) = 0) := by
  -- 5^2 ≡ 25 ≡ 8 (mod 17)
  have h1 : (5 : ZMod 17) ^ 2 = 8 := by decide
  -- 2^3 ≡ 8 (mod 17)
  have h2 : (2 : ZMod 17) ^ 3 = 8 := by decide

  -- 5^(2n) - 2^(3n) = (5^2)^n - (2^3)^n = 8^n - 8^n = 0
  calc
    (5 : ZMod 17) ^ (2 * n) - (2 : ZMod 17) ^ (3 * n)
      = (5 ^ 2) ^ n - (2 ^ 3) ^ n             := by rw [← pow_mul, ← pow_mul]
    _ = (8 : ZMod 17) ^ n - (8 : ZMod 17) ^ n := by rw [h1, h2]
    _ = 0                                     := sub_self _
