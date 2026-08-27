import Mathlib

/-!
# `sen 10°` es irracional

Formalización del enunciado y de la solución (1ª forma) del reto propuesto por
José Manuel Sánchez Muñoz (Retos Matemáticos, 3 de octubre de 2023).

**Enunciado.** Demuéstrese que `sen 10°` es irracional.

**Solución.** A partir de la fórmula del seno del ángulo triple,
`sen 30° = 3 sen 10° − 4 sen³ 10°`, y de `sen 30° = 1/2`, se obtiene
`8 sen³ 10° − 6 sen 10° + 1 = 0`. Con el cambio `x = 2 sen 10°` esto es
`x³ − 3x + 1 = 0`, ecuación mónica con coeficientes enteros que, por el teorema
de la raíz racional, sólo podría tener raíces racionales enteras que dividieran
al término independiente, esto es `±1`; como ninguna de ellas es raíz, la
ecuación no tiene raíces racionales y por tanto `sen 10°` es irracional.
-/

open Real

namespace Sin10

/-- `10°` en radianes. -/
noncomputable def tenDeg : ℝ := Real.pi / 18

/-- La ecuación cúbica satisfecha por `sen 10°`:
`8 sen³ 10° − 6 sen 10° + 1 = 0`. -/
theorem cubic_sin_tenDeg :
    8 * Real.sin tenDeg ^ 3 - 6 * Real.sin tenDeg + 1 = 0 := by
  have h3 : Real.sin (3 * tenDeg) = 3 * Real.sin tenDeg - 4 * Real.sin tenDeg ^ 3 :=
    Real.sin_three_mul tenDeg
  have hpi : 3 * tenDeg = Real.pi / 6 := by
    unfold tenDeg; ring
  rw [hpi, Real.sin_pi_div_six] at h3
  linarith

/-- Ningún número entero es raíz de `x³ − 3x + 1`. -/
theorem no_int_root (n : ℤ) : n ^ 3 - 3 * n + 1 ≠ 0 := by
  intro h
  have hdvd : n ∣ 1 := ⟨3 - n ^ 2, by linarith [h]⟩
  have := Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd)
  rcases this with h1 | h1 <;> subst h1 <;> norm_num at h

/-- Ningún número racional es raíz de `x³ − 3x + 1` (teorema de la raíz racional
en este caso particular: el denominador debe ser `1` y el numerador debe dividir
al término independiente). -/
theorem no_rat_root (x : ℚ) : x ^ 3 - 3 * x + 1 ≠ 0 := by
  intro hx
  set n : ℤ := x.num with hn
  set d : ℤ := (x.den : ℤ) with hd
  have hd0 : (d : ℚ) ≠ 0 := by
    simp [hd, Rat.den_ne_zero]
  have hnum : (n : ℚ) = x * (d : ℚ) := by
    conv_rhs => rw [← Rat.num_div_den x]
    field_simp
    rw [hn, hd]
    push_cast
    ring
  -- la ecuación homogeneizada: `n³ = 3 n d² − d³`
  have hZ : (n : ℚ) ^ 3 = 3 * (n : ℚ) * (d : ℚ) ^ 2 - (d : ℚ) ^ 3 := by
    rw [hnum]
    have : x ^ 3 = 3 * x - 1 := by linarith
    calc (x * (d:ℚ)) ^ 3 = x ^ 3 * (d:ℚ) ^ 3 := by ring
      _ = (3 * x - 1) * (d:ℚ) ^ 3 := by rw [this]
      _ = 3 * (x * (d:ℚ)) * (d:ℚ) ^ 2 - (d:ℚ) ^ 3 := by ring
  have hZ' : n ^ 3 = 3 * n * d ^ 2 - d ^ 3 := by
    exact_mod_cast hZ
  -- el denominador divide a `n³`, y es coprimo con él, luego vale `1`
  have hdvd : d ∣ n ^ 3 := ⟨3 * n * d - d ^ 2, by linarith [hZ']⟩
  have hcop : Nat.Coprime (n.natAbs ^ 3) x.den := Nat.Coprime.pow_left 3 x.reduced
  have hdvd' : x.den ∣ n.natAbs ^ 3 := by
    have : d.natAbs ∣ (n ^ 3).natAbs := Int.natAbs_dvd_natAbs.mpr hdvd
    simpa [hd, Int.natAbs_pow] using this
  have hden : x.den = 1 := (Nat.Coprime.symm hcop).eq_one_of_dvd hdvd'
  -- luego `x` es entero y se aplica `no_int_root`
  have hxn : x = (n : ℚ) := by
    rw [hn, ← Rat.num_div_den x, hden]
    simp
  apply no_int_root n
  have : ((n ^ 3 - 3 * n + 1 : ℤ) : ℚ) = 0 := by
    push_cast
    rw [← hxn]
    linarith
  exact_mod_cast this

/-- **`sen 10°` es irracional.** -/
theorem irrational_sin_tenDeg : Irrational (Real.sin tenDeg) := by
  rintro ⟨q, hq⟩
  have hcube : 8 * (q : ℝ) ^ 3 - 6 * (q : ℝ) + 1 = 0 := by
    rw [hq]; exact cubic_sin_tenDeg
  have hQ : (2 * q) ^ 3 - 3 * (2 * q) + 1 = 0 := by
    have : ((8 * q ^ 3 - 6 * q + 1 : ℚ) : ℝ) = 0 := by push_cast; linarith [hcube]
    have h' : (8 * q ^ 3 - 6 * q + 1 : ℚ) = 0 := by exact_mod_cast this
    linarith [h']
  exact no_rat_root (2 * q) hQ

/-- El enunciado tal como se propone: `sen 10°` (con el ángulo en grados,
es decir, `π/18` radianes) es irracional. -/
theorem irrational_sin_ten_degrees : Irrational (Real.sin (Real.pi / 18)) :=
  irrational_sin_tenDeg

end Sin10
