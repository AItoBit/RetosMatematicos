import Mathlib

namespace ProgresionGeometrica

/-
Enunciado:

Determinar los siete primeros términos de una progresión geométrica,
sabiendo que la suma de sus tres primeros términos es 49/9 y que
la suma de sus tres últimos términos es 30625/729.

Si `a` es el primer término y `r` es la razón, entonces:

  a + a*r + a*r^2 = 49/9

y

  a*r^4 + a*r^5 + a*r^6 = 30625/729.

Las dos soluciones racionales son:

  a = 1,     r = 5/3

o bien

  a = 49/19, r = -5/3.
-/
theorem enunciado_y_solucion
    (a r : ℚ)
    (hPrimeros :
      a + a * r + a * r^2 = (49 : ℚ) / 9)
    (hUltimos :
      a * r^4 + a * r^5 + a * r^6 = (30625 : ℚ) / 729) :
    (a = 1 ∧ r = (5 : ℚ) / 3) ∨
    (a = (49 : ℚ) / 19 ∧ r = -(5 : ℚ) / 3) := by

  have hPrimerosFactor :
      a * (1 + r + r^2) = (49 : ℚ) / 9 := by
    nlinarith [hPrimeros]

  have hUltimosFactor :
      a * (1 + r + r^2) * r^4 = (30625 : ℚ) / 729 := by
    calc
      a * (1 + r + r^2) * r^4
          = a * r^4 + a * r^5 + a * r^6 := by ring
      _ = (30625 : ℚ) / 729 := hUltimos

  have hr4 : r^4 = (625 : ℚ) / 81 := by
    rw [hPrimerosFactor] at hUltimosFactor
    norm_num at hUltimosFactor ⊢
    nlinarith [hUltimosFactor]

  have hr2 : r^2 = (25 : ℚ) / 9 := by
    have hr2_nonneg : 0 ≤ r^2 := sq_nonneg r
    nlinarith [hr4, sq_nonneg (r^2 + (25 : ℚ) / 9)]

  have hfactor :
      (r - (5 : ℚ) / 3) * (r + (5 : ℚ) / 3) = 0 := by
    nlinarith [hr2]

  rcases mul_eq_zero.mp hfactor with hpos | hneg

  · left

    have hr : r = (5 : ℚ) / 3 := by
      nlinarith [hpos]

    constructor

    · rw [hr] at hPrimeros
      norm_num at hPrimeros ⊢
      linarith [hPrimeros]

    · exact hr

  · right

    have hr : r = -(5 : ℚ) / 3 := by
      nlinarith [hneg]

    constructor

    · rw [hr] at hPrimeros
      norm_num at hPrimeros ⊢
      linarith [hPrimeros]

    · exact hr

end ProgresionGeometrica
