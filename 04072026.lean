import Mathlib

theorem ac_eq_6Rr_of_arithmetic_progression
    (a b c R r S s : ℝ)
    -- Los lados forman una progresión aritmética:
    (h_AP : 2 * b = a + c)
    -- Definición del semiperímetro:
    (hs : s = (a + b + c) / 2)
    -- Fórmulas del área respecto a R y r:
    (hR : R = (a * b * c) / (4 * S))
    (hr : r = S / s)
    -- Condiciones de no nulidad geométricas:
    (hS : S ≠ 0)
    (hb : b ≠ 0) :
    a * c = 6 * R * r := by
  -- 1. Obtenemos s = 3 * b / 2 linealmente a partir de hs y h_AP:
  have hs_val : s = 3 * b / 2 := by
    linarith [hs, h_AP]

  -- 2. Sustituimos R, r y s en la meta:
  rw [hR, hr, hs_val]

  -- 3. field_simp cancela los denominadores usando hS y hb, y ring concluye:
  field_simp
  ring
