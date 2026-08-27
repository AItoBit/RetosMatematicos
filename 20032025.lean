import Mathlib

/-!
# Retos Matemáticos: Divisibilidad de $5n^3 - 5n$ entre 30

Demostración de que para todo número natural $n \in \mathbb{N}$:
$$30 \mid (5n^3 - 5n)$$
-/

/-! ### 1ª Forma: Demostración por Inducción Matemática -/

theorem five_cube_sub_five_mul_dvd_thirty (n : ℕ) :
    (30 : ℤ) ∣ 5 * (n : ℤ) ^ 3 - 5 * (n : ℤ) := by
  induction n with
  | zero =>
    -- Caso base n = 0: 5(0)³ - 5(0) = 0, y 30 ∣ 0
    use 0
    ring
  | succ n ih =>
    -- Hipótesis de inducción: 5n³ - 5n = 30 * k
    obtain ⟨k, hk⟩ := ih
    -- Analizamos si n es par o impar para probar que 15n(n+1) es múltiplo de 30
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- Caso 1: n es par (n = 2 * m)
      have hn : (n : ℤ) = 2 * (m : ℤ) := by
        rw [hm]
        push_cast
        ring
      use k + m * (2 * m + 1)
      calc
        5 * (n + 1 : ℤ) ^ 3 - 5 * (n + 1 : ℤ)
          = (5 * (n : ℤ) ^ 3 - 5 * (n : ℤ)) + 15 * (n : ℤ) * (n + 1) := by ring
        _ = 30 * k + 15 * (2 * m) * (2 * m + 1)                      := by rw [hk, hn]
        _ = 30 * (k + m * (2 * m + 1))                               := by ring
    · -- Caso 2: n es impar (n = 2 * m + 1)
      have hn : (n : ℤ) = 2 * (m : ℤ) + 1 := by
        rw [hm]
        push_cast
        ring
      use k + (2 * m + 1) * (m + 1)
      calc
        5 * (n + 1 : ℤ) ^ 3 - 5 * (n + 1 : ℤ)
          = (5 * (n : ℤ) ^ 3 - 5 * (n : ℤ)) + 15 * (n : ℤ) * (n + 1) := by ring
        _ = 30 * k + 15 * (2 * m + 1) * (2 * m + 1 + 1)              := by rw [hk, hn]
        _ = 30 * (k + (2 * m + 1) * (m + 1))                         := by ring

/-! ### 2ª Forma: Demostración directa en Aritmética Modular (`ZMod 30`) -/

/-- En el anillo finito ℤ/30ℤ, todo elemento satisface 5x³ - 5x = 0 -/
theorem five_cube_sub_five_mul_zmod_thirty (n : ZMod 30) :
    5 * n ^ 3 - 5 * n = 0 := by
  revert n
  decide
