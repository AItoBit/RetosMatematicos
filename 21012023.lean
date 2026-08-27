import Mathlib

/-!
# Retos Matemáticos, 21 de enero de 2023

**Enunciado.** Sean `a, b, c, x, y, z ∈ ℝ` tales que

  `a + b + c + x + y + z = 4`   y   `a² + b² + c² + x² + y² + z² = 16`.

Calcúlese `mín(abcxyz)`.

**Solución.** El mínimo es `-8192/729`, alcanzado (por ejemplo) en
`a = b = c = x = y = 4/3`, `z = -8/3`.

Este archivo contiene:

* `RetoMin.cota_inferior`: la cota `-8192/729 ≤ abcxyz` bajo las dos restricciones;
* `RetoMin.alcanzado`: el valor `-8192/729` se alcanza;
* `RetoMin.min_producto`: `-8192/729` es el mínimo (`IsLeast`) del conjunto de valores
  de `abcxyz` sujeto a las restricciones.

La demostración formalizada sigue la idea de la solución: se separan las variables según
su signo; si el número de variables negativas es par el producto es no negativo, y si es
impar (1, 3 ó 5 negativas) se combinan la desigualdad de Cauchy–Schwarz (para acotar las
sumas) con la desigualdad entre las medias aritmética y geométrica (para acotar los
productos). El caso de 5 variables negativas es imposible, el de 3 da la cota `4096/729`
y el de 1 da la cota óptima `8192/729`.
-/

namespace RetoMin

/-- Desigualdad AM–GM para cuatro números no negativos. -/
theorem amgm4 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    a * b * c * d ≤ ((a + b + c + d) / 4) ^ 4 := by
  have h1 : a * b ≤ ((a + b) / 2) ^ 2 := by nlinarith [sq_nonneg (a - b)]
  have h2 : c * d ≤ ((c + d) / 2) ^ 2 := by nlinarith [sq_nonneg (c - d)]
  have h3 : (a * b) * (c * d) ≤ ((a + b) / 2) ^ 2 * ((c + d) / 2) ^ 2 :=
    mul_le_mul h1 h2 (mul_nonneg hc hd) (sq_nonneg _)
  have hA0 : (0:ℝ) ≤ (a + b) / 2 := by linarith
  have hB0 : (0:ℝ) ≤ (c + d) / 2 := by linarith
  have h4 : ((a + b) / 2) * ((c + d) / 2) ≤ ((a + b + c + d) / 4) ^ 2 := by
    nlinarith [sq_nonneg ((a + b) / 2 - (c + d) / 2)]
  have h5 : (((a + b) / 2) * ((c + d) / 2)) ^ 2 ≤ (((a + b + c + d) / 4) ^ 2) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hA0 hB0) h4 2
  calc a * b * c * d = (a * b) * (c * d) := by ring
    _ ≤ ((a + b) / 2) ^ 2 * ((c + d) / 2) ^ 2 := h3
    _ = (((a + b) / 2) * ((c + d) / 2)) ^ 2 := by ring
    _ ≤ (((a + b + c + d) / 4) ^ 2) ^ 2 := h5
    _ = ((a + b + c + d) / 4) ^ 4 := by ring

/-- Desigualdad AM–GM para tres números no negativos. -/
theorem amgm3 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a * b * c ≤ ((a + b + c) / 3) ^ 3 := by
  set m := (a + b + c) / 3 with hm
  have hm0 : 0 ≤ m := by rw [hm]; linarith
  have h := amgm4 a b c m ha hb hc hm0
  have he : (a + b + c + m) / 4 = m := by rw [hm]; ring
  rw [he] at h
  rcases eq_or_lt_of_le hm0 with h0 | h0
  · have ha0 : a = 0 := by rw [hm] at h0; linarith
    have hz : a * b * c = 0 := by rw [ha0]; ring
    rw [hz]; exact pow_nonneg hm0 3
  · refine le_of_mul_le_mul_right ?_ h0
    calc a * b * c * m ≤ m ^ 4 := h
      _ = m ^ 3 * m := by ring

/-- Paso auxiliar: `p⁴q⁴ ≤ ((p+q)/2)⁸` para `p, q ≥ 0`. -/
theorem pow4_mul_pow4_le (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    p ^ 4 * q ^ 4 ≤ ((p + q) / 2) ^ 8 := by
  have h1 : p * q ≤ ((p + q) / 2) ^ 2 := by nlinarith [sq_nonneg (p - q)]
  have h2 : (p * q) ^ 4 ≤ (((p + q) / 2) ^ 2) ^ 4 :=
    pow_le_pow_left₀ (mul_nonneg hp hq) h1 4
  calc p ^ 4 * q ^ 4 = (p * q) ^ 4 := by ring
    _ ≤ (((p + q) / 2) ^ 2) ^ 4 := h2
    _ = ((p + q) / 2) ^ 8 := by ring

/-- Desigualdad AM–GM para ocho números no negativos. -/
theorem amgm8 (a b c d e f g h : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (he : 0 ≤ e) (hf : 0 ≤ f) (hg : 0 ≤ g) (hh : 0 ≤ h) :
    a * b * c * d * e * f * g * h ≤ ((a + b + c + d + e + f + g + h) / 8) ^ 8 := by
  have h1 := amgm4 a b c d ha hb hc hd
  have h2 := amgm4 e f g h he hf hg hh
  have hp : (0:ℝ) ≤ (a + b + c + d) / 4 := by linarith
  have hq : (0:ℝ) ≤ (e + f + g + h) / 4 := by linarith
  have h3 : (a * b * c * d) * (e * f * g * h)
      ≤ ((a + b + c + d) / 4) ^ 4 * ((e + f + g + h) / 4) ^ 4 :=
    mul_le_mul h1 h2 (by positivity) (by positivity)
  have h6 := pow4_mul_pow4_le ((a + b + c + d) / 4) ((e + f + g + h) / 4) hp hq
  have heq : (((a + b + c + d) / 4) + ((e + f + g + h) / 4)) / 2
      = (a + b + c + d + e + f + g + h) / 8 := by ring
  rw [heq] at h6
  calc a * b * c * d * e * f * g * h = (a * b * c * d) * (e * f * g * h) := by ring
    _ ≤ ((a + b + c + d) / 4) ^ 4 * ((e + f + g + h) / 4) ^ 4 := h3
    _ ≤ ((a + b + c + d + e + f + g + h) / 8) ^ 8 := h6

/-- Desigualdad AM–GM para cinco números no negativos. -/
theorem amgm5 (a b c d e : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (he : 0 ≤ e) : a * b * c * d * e ≤ ((a + b + c + d + e) / 5) ^ 5 := by
  set m := (a + b + c + d + e) / 5 with hm
  have hm0 : 0 ≤ m := by rw [hm]; linarith
  have h := amgm8 a b c d e m m m ha hb hc hd he hm0 hm0 hm0
  have hev : (a + b + c + d + e + m + m + m) / 8 = m := by rw [hm]; ring
  rw [hev] at h
  rcases eq_or_lt_of_le hm0 with h0 | h0
  · have ha0 : a = 0 := by rw [hm] at h0; linarith
    have hz : a * b * c * d * e = 0 := by rw [ha0]; ring
    rw [hz]; exact pow_nonneg hm0 5
  · refine le_of_mul_le_mul_right ?_ (pow_pos h0 3)
    calc (a * b * c * d * e) * m ^ 3 = a * b * c * d * e * m * m * m := by ring
      _ ≤ m ^ 8 := h
      _ = m ^ 5 * m ^ 3 := by ring

/-- Caso de exactamente una variable negativa: si `u ≥ 0`, `v₁, …, v₅ ≥ 0`,
`v₁ + ⋯ + v₅ - u = 4` y `u² + v₁² + ⋯ + v₅² = 16`, entonces `u · v₁⋯v₅ ≤ 8192/729`. -/
theorem one_neg (u v1 v2 v3 v4 v5 : ℝ) (hu : 0 ≤ u) (h1 : 0 ≤ v1) (h2 : 0 ≤ v2) (h3 : 0 ≤ v3)
    (h4 : 0 ≤ v4) (h5 : 0 ≤ v5) (hs : v1 + v2 + v3 + v4 + v5 - u = 4)
    (hq : u ^ 2 + v1 ^ 2 + v2 ^ 2 + v3 ^ 2 + v4 ^ 2 + v5 ^ 2 = 16) :
    u * (v1 * v2 * v3 * v4 * v5) ≤ 8192 / 729 := by
  have hcs : (v1 + v2 + v3 + v4 + v5) ^ 2
      ≤ 5 * (v1 ^ 2 + v2 ^ 2 + v3 ^ 2 + v4 ^ 2 + v5 ^ 2) := by
    nlinarith [sq_nonneg (v1 - v2), sq_nonneg (v1 - v3), sq_nonneg (v1 - v4), sq_nonneg (v1 - v5),
      sq_nonneg (v2 - v3), sq_nonneg (v2 - v4), sq_nonneg (v2 - v5), sq_nonneg (v3 - v4),
      sq_nonneg (v3 - v5), sq_nonneg (v4 - v5)]
  have hu83 : u ≤ 8 / 3 := by nlinarith [hcs]
  have hprod : v1 * v2 * v3 * v4 * v5 ≤ ((4 + u) / 5) ^ 5 := by
    have hg := amgm5 v1 v2 v3 v4 v5 h1 h2 h3 h4 h5
    have he : (v1 + v2 + v3 + v4 + v5) / 5 = (4 + u) / 5 := by
      rw [show v1 + v2 + v3 + v4 + v5 = 4 + u by linarith]
    rw [he] at hg
    exact hg
  have ht0 : (0:ℝ) ≤ (4 + u) / 5 := by linarith
  have ht : ((4 + u) / 5) ≤ 4 / 3 := by linarith
  have ht5 : ((4 + u) / 5) ^ 5 ≤ (4 / 3 : ℝ) ^ 5 := pow_le_pow_left₀ ht0 ht 5
  calc u * (v1 * v2 * v3 * v4 * v5) ≤ u * ((4 + u) / 5) ^ 5 := mul_le_mul_of_nonneg_left hprod hu
    _ ≤ u * (4 / 3 : ℝ) ^ 5 := mul_le_mul_of_nonneg_left ht5 hu
    _ ≤ (8 / 3) * (4 / 3 : ℝ) ^ 5 := mul_le_mul_of_nonneg_right hu83 (by norm_num)
    _ = 8192 / 729 := by norm_num

/-- Caso de exactamente tres variables negativas. -/
theorem three_neg (u1 u2 u3 v1 v2 v3 : ℝ) (hu1 : 0 ≤ u1) (hu2 : 0 ≤ u2) (hu3 : 0 ≤ u3)
    (hv1 : 0 ≤ v1) (hv2 : 0 ≤ v2) (hv3 : 0 ≤ v3)
    (hs : v1 + v2 + v3 - (u1 + u2 + u3) = 4)
    (hq : u1 ^ 2 + u2 ^ 2 + u3 ^ 2 + v1 ^ 2 + v2 ^ 2 + v3 ^ 2 = 16) :
    (u1 * u2 * u3) * (v1 * v2 * v3) ≤ 8192 / 729 := by
  have hcs1 : (u1 + u2 + u3) ^ 2 ≤ 3 * (u1 ^ 2 + u2 ^ 2 + u3 ^ 2) := by
    nlinarith [sq_nonneg (u1 - u2), sq_nonneg (u1 - u3), sq_nonneg (u2 - u3)]
  have hcs2 : (v1 + v2 + v3) ^ 2 ≤ 3 * (v1 ^ 2 + v2 ^ 2 + v3 ^ 2) := by
    nlinarith [sq_nonneg (v1 - v2), sq_nonneg (v1 - v3), sq_nonneg (v2 - v3)]
  have hUV : (u1 + u2 + u3) * (v1 + v2 + v3) ≤ 16 := by nlinarith [hcs1, hcs2]
  have hu := amgm3 u1 u2 u3 hu1 hu2 hu3
  have hv := amgm3 v1 v2 v3 hv1 hv2 hv3
  have hUn : (0:ℝ) ≤ (u1 + u2 + u3) / 3 := by linarith
  have hVn : (0:ℝ) ≤ (v1 + v2 + v3) / 3 := by linarith
  have step : (u1 * u2 * u3) * (v1 * v2 * v3)
      ≤ ((u1 + u2 + u3) / 3) ^ 3 * ((v1 + v2 + v3) / 3) ^ 3 :=
    mul_le_mul hu hv (by positivity) (by positivity)
  have hmul0 : (0:ℝ) ≤ ((u1 + u2 + u3) / 3) * ((v1 + v2 + v3) / 3) := mul_nonneg hUn hVn
  have hmul : ((u1 + u2 + u3) / 3) * ((v1 + v2 + v3) / 3) ≤ 16 / 9 := by nlinarith [hUV]
  have hcube : (((u1 + u2 + u3) / 3) * ((v1 + v2 + v3) / 3)) ^ 3 ≤ (16 / 9 : ℝ) ^ 3 :=
    pow_le_pow_left₀ hmul0 hmul 3
  calc (u1 * u2 * u3) * (v1 * v2 * v3)
      ≤ ((u1 + u2 + u3) / 3) ^ 3 * ((v1 + v2 + v3) / 3) ^ 3 := step
    _ = (((u1 + u2 + u3) / 3) * ((v1 + v2 + v3) / 3)) ^ 3 := by ring
    _ ≤ (16 / 9 : ℝ) ^ 3 := hcube
    _ ≤ 8192 / 729 := by norm_num

/-- Caso de cinco variables negativas: las restricciones obligan a que todas ellas sean
nulas, de modo que el producto es `0`. -/
theorem five_neg (u1 u2 u3 u4 u5 v : ℝ) (hu1 : 0 ≤ u1) (hu2 : 0 ≤ u2) (hu3 : 0 ≤ u3)
    (hu4 : 0 ≤ u4) (hu5 : 0 ≤ u5) (hv : 0 ≤ v)
    (hs : v - (u1 + u2 + u3 + u4 + u5) = 4)
    (hq : u1 ^ 2 + u2 ^ 2 + u3 ^ 2 + u4 ^ 2 + u5 ^ 2 + v ^ 2 = 16) :
    (u1 * u2 * u3 * u4 * u5) * v ≤ 8192 / 729 := by
  have h0 : u1 = 0 := by nlinarith [sq_nonneg u1, sq_nonneg u2, sq_nonneg u3]
  have hz : (u1 * u2 * u3 * u4 * u5) * v = 0 := by rw [h0]; ring
  rw [hz]; norm_num

/-- **Cota inferior.** Si `a + b + c + x + y + z = 4` y `a² + b² + c² + x² + y² + z² = 16`,
entonces `abcxyz ≥ -8192/729`. -/
theorem cota_inferior (a b c x y z : ℝ) (hs : a + b + c + x + y + z = 4)
    (hq : a ^ 2 + b ^ 2 + c ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = 16) :
    -(8192 / 729) ≤ a * b * c * x * y * z := by
  rcases le_or_gt 0 a with ha | ha <;> rcases le_or_gt 0 b with hb | hb <;>
    rcases le_or_gt 0 c with hc | hc <;> rcases le_or_gt 0 x with hx | hx <;>
    rcases le_or_gt 0 y with hy | hy <;> rcases le_or_gt 0 z with hz | hz
  · -- ++++++
    have hnn : (0:ℝ) ≤ a * b * c * x * y * z :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ha hb) hc) hx) hy) hz
    linarith [hnn]
  · -- +++++-
    have pz : (0:ℝ) ≤ -z := by linarith
    have hkey := one_neg (-z) a b c x y pz ha hb hc hx hy (by linarith) (by linear_combination hq)
    linarith [hkey]
  · -- ++++-+
    have py : (0:ℝ) ≤ -y := by linarith
    have hkey := one_neg (-y) a b c x z py ha hb hc hx hz (by linarith) (by linear_combination hq)
    linarith [hkey]
  · -- ++++--
    have py : (0:ℝ) ≤ -y := by linarith
    have pz : (0:ℝ) ≤ -z := by linarith
    have hnn : (0:ℝ) ≤ a * b * c * x * (-y) * (-z) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ha hb) hc) hx) py) pz
    linarith [hnn]
  · -- +++-++
    have px : (0:ℝ) ≤ -x := by linarith
    have hkey := one_neg (-x) a b c y z px ha hb hc hy hz (by linarith) (by linear_combination hq)
    linarith [hkey]
  · -- +++-+-
    have px : (0:ℝ) ≤ -x := by linarith
    have pz : (0:ℝ) ≤ -z := by linarith
    have hnn : (0:ℝ) ≤ a * b * c * (-x) * y * (-z) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ha hb) hc) px) hy) pz
    linarith [hnn]
  · -- +++--+
    have px : (0:ℝ) ≤ -x := by linarith
    have py : (0:ℝ) ≤ -y := by linarith
    have hnn : (0:ℝ) ≤ a * b * c * (-x) * (-y) * z :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ha hb) hc) px) py) hz
    linarith [hnn]
  · -- +++---
    have px : (0:ℝ) ≤ -x := by linarith
    have py : (0:ℝ) ≤ -y := by linarith
    have pz : (0:ℝ) ≤ -z := by linarith
    have hkey := three_neg (-x) (-y) (-z) a b c px py pz ha hb hc (by linarith) (by linear_combination hq)
    linarith [hkey]
  · -- ++-+++
    have pc : (0:ℝ) ≤ -c := by linarith
    have hkey := one_neg (-c) a b x y z pc ha hb hx hy hz (by linarith) (by linear_combination hq)
    linarith [hkey]
  · -- ++-++-
    have pc : (0:ℝ) ≤ -c := by linarith
    have pz : (0:ℝ) ≤ -z := by linarith
    have hnn : (0:ℝ) ≤ a * b * (-c) * x * y * (-z) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ha hb) pc) hx) hy) pz
    linarith [hnn]
  · -- ++-+-+
    have pc : (0:ℝ) ≤ -c := by linarith
    have py : (0:ℝ) ≤ -y := by linarith
    have hnn : (0:ℝ) ≤ a * b * (-c) * x * (-y) * z :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ha hb) pc) hx) py) hz
    linarith [hnn]
  · -- ++-+--
    have pc : (0:ℝ) ≤ -c := by linarith
    have py : (0:ℝ) ≤ -y := by linarith
    have pz : (0:ℝ) ≤ -z := by linarith
    have hkey := three_neg (-c) (-y) (-z) a b x pc py pz ha hb hx (by linarith) (by linear_combination hq)
    linarith [hkey]
  · -- ++--++
    have pc : (0:ℝ) ≤ -c := by linarith
    have px : (0:ℝ) ≤ -x := by linarith
    have hnn : (0:ℝ) ≤ a * b * (-c) * (-x) * y * z :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ha hb) pc) px) hy) hz
    linarith [hnn]
  · -- ++--+-
    have pc : (0:ℝ) ≤ -c := by linarith
    have px : (0:ℝ) ≤ -x := by linarith
    have pz : (0:ℝ) ≤ -z := by linarith
    have hkey := three_neg (-c) (-x) (-z) a b y pc px pz ha hb hy (by linarith) (by linear_combination hq)
    linarith [hkey]
  · -- ++---+
    have pc : (0:ℝ) ≤ -c := by linarith
    have px : (0:ℝ) ≤ -x := by linarith
    have py : (0:ℝ) ≤ -y := by linarith
    have hkey := three_neg (-c) (-x) (-y) a b z pc px py ha hb hz (by linarith) (by linear_combination hq)
    linarith [hkey]
  · -- ++----
    have pc : (0:ℝ) ≤ -c := by linarith
    have px : (0:ℝ) ≤ -x := by linarith
    have py : (0:ℝ) ≤ -y := by linarith
    have pz : (0:ℝ) ≤ -z := by linarith
    have hnn : (0:ℝ) ≤ a * b * (-c) * (-x) * (-y) * (-z) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ha hb) pc) px) py) pz
    linarith [hnn]
  · -- +-++++
    have pb : (0:ℝ) ≤ -b := by linarith
    have hkey := one_neg (-b) a c x y z pb ha hc hx hy hz (by linarith) (by linear_combination hq)
    linarith [hkey]
  · -- +-+++-
    have pb : (0:ℝ) ≤ -b := by linarith
    have pz : (0:ℝ) ≤ -z := by linarith
    have hnn : (0:ℝ) ≤ a * (-b) * c * x * y * (-z) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ha pb) hc) hx) hy) pz
    linarith [hnn]
  · -- +-++-+
    have pb : (0:ℝ) ≤ -b := by linarith
    have py : (0:ℝ) ≤ -y := by linarith
    have hnn : (0:ℝ) ≤ a * (-b) * c * x * (-y) * z :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ha pb) hc) hx) py) hz
    linarith [hnn]
  · -- +-++--
    have pb : (0:ℝ) ≤ -b := by linarith
    have py : (0:ℝ) ≤ -y := by linarith
    have pz : (0:ℝ) ≤ -z := by linarith
    have hkey := three_neg (-b) (-y) (-z) a c x pb py pz ha hc hx (by linarith) (by linear_combination hq)
    linarith [hkey]
  · -- +-+-++
    have pb : (0:ℝ) ≤ -b := by linarith
    have px : (0:ℝ) ≤ -x := by linarith
    have hnn : (0:ℝ) ≤ a * (-b) * c * (-x) * y * z :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ha pb) hc) px) hy) hz
    linarith [hnn]
  · -- +-+-+-
    have pb : (0:ℝ) ≤ -b := by linarith
    have px : (0:ℝ) ≤ -x := by linarith
    have pz : (0:ℝ) ≤ -z := by linarith
    have hkey := three_neg (-b) (-x) (-z) a c y pb px pz ha hc hy (by linarith) (by linear_combination hq)
    linarith [hkey]
  · -- +-+--+
    have pb : (0:ℝ) ≤ -b := by linarith
    have px : (0:ℝ) ≤ -x := by linarith
    have py : (0:ℝ) ≤ -y := by linarith
    have hkey := three_neg (-b) (-x) (-y) a c z pb px py ha hc hz (by linarith) (by linear_combination hq)
    linarith [hkey]
  · -- +-+---
    have pb : (0:ℝ) ≤ -b := by linarith
    have px : (0:ℝ) ≤ -x := by linarith
    have py : (0:ℝ) ≤ -y := by linarith
    have pz : (0:ℝ) ≤ -z := by linarith
    have hnn : (0:ℝ) ≤ a * (-b) * c * (-x) * (-y) * (-z) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ha pb) hc) px) py) pz
    linarith [hnn]
  · -- +--+++
    have pb : (0:ℝ) ≤ -b := by linarith
    have pc : (0:ℝ) ≤ -c := by linarith
    have hnn : (0:ℝ) ≤ a * (-b) * (-c) * x * y * z :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ha pb) pc) hx) hy) hz
    linarith [hnn]
  · -- +--++-
    have pb : (0:ℝ) ≤ -b := by linarith
    have pc : (0:ℝ) ≤ -c := by linarith
    have pz : (0:ℝ) ≤ -z := by linarith
    have hkey := three_neg (-b) (-c) (-z) a x y pb pc pz ha hx hy (by linarith) (by linear_combination hq)
    linarith [hkey]
  · -- +--+-+
    have pb : (0:ℝ) ≤ -b := by linarith
    have pc : (0:ℝ) ≤ -c := by linarith
    have py : (0:ℝ) ≤ -y := by linarith
    have hkey := three_neg (-b) (-c) (-y) a x z pb pc py ha hx hz (by linarith) (by linear_combination hq)
    linarith [hkey]
  · -- +--+--
    have pb : (0:ℝ) ≤ -b := by linarith
    have pc : (0:ℝ) ≤ -c := by linarith
    have py : (0:ℝ) ≤ -y := by linarith
    have pz : (0:ℝ) ≤ -z := by linarith
    have hnn : (0:ℝ) ≤ a * (-b) * (-c) * x * (-y) * (-z) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ha pb) pc) hx) py) pz
    linarith [hnn]
  · -- +---++
    have pb : (0:ℝ) ≤ -b := by linarith
    have pc : (0:ℝ) ≤ -c := by linarith
    have px : (0:ℝ) ≤ -x := by linarith
    have hkey := three_neg (-b) (-c) (-x) a y z pb pc px ha hy hz (by linarith) (by linear_combination hq)
    linarith [hkey]
  · -- +---+-
    have pb : (0:ℝ) ≤ -b := by linarith
    have pc : (0:ℝ) ≤ -c := by linarith
    have px : (0:ℝ) ≤ -x := by linarith
    have pz : (0:ℝ) ≤ -z := by linarith
    have hnn : (0:ℝ) ≤ a * (-b) * (-c) * (-x) * y * (-z) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ha pb) pc) px) hy) pz
    linarith [hnn]
  · -- +----+
    have pb : (0:ℝ) ≤ -b := by linarith
    have pc : (0:ℝ) ≤ -c := by linarith
    have px : (0:ℝ) ≤ -x := by linarith
    have py : (0:ℝ) ≤ -y := by linarith
    have hnn : (0:ℝ) ≤ a * (-b) * (-c) * (-x) * (-y) * z :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ha pb) pc) px) py) hz
    linarith [hnn]
  · -- +-----
    have pb : (0:ℝ) ≤ -b := by linarith
    have pc : (0:ℝ) ≤ -c := by linarith
    have px : (0:ℝ) ≤ -x := by linarith
    have py : (0:ℝ) ≤ -y := by linarith
    have pz : (0:ℝ) ≤ -z := by linarith
    have hkey := five_neg (-b) (-c) (-x) (-y) (-z) a pb pc px py pz ha (by linarith) (by linear_combination hq)
    linarith [hkey]
  · -- -+++++
    have pa : (0:ℝ) ≤ -a := by linarith
    have hkey := one_neg (-a) b c x y z pa hb hc hx hy hz (by linarith) (by linear_combination hq)
    linarith [hkey]
  · -- -++++-
    have pa : (0:ℝ) ≤ -a := by linarith
    have pz : (0:ℝ) ≤ -z := by linarith
    have hnn : (0:ℝ) ≤ (-a) * b * c * x * y * (-z) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg pa hb) hc) hx) hy) pz
    linarith [hnn]
  · -- -+++-+
    have pa : (0:ℝ) ≤ -a := by linarith
    have py : (0:ℝ) ≤ -y := by linarith
    have hnn : (0:ℝ) ≤ (-a) * b * c * x * (-y) * z :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg pa hb) hc) hx) py) hz
    linarith [hnn]
  · -- -+++--
    have pa : (0:ℝ) ≤ -a := by linarith
    have py : (0:ℝ) ≤ -y := by linarith
    have pz : (0:ℝ) ≤ -z := by linarith
    have hkey := three_neg (-a) (-y) (-z) b c x pa py pz hb hc hx (by linarith) (by linear_combination hq)
    linarith [hkey]
  · -- -++-++
    have pa : (0:ℝ) ≤ -a := by linarith
    have px : (0:ℝ) ≤ -x := by linarith
    have hnn : (0:ℝ) ≤ (-a) * b * c * (-x) * y * z :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg pa hb) hc) px) hy) hz
    linarith [hnn]
  · -- -++-+-
    have pa : (0:ℝ) ≤ -a := by linarith
    have px : (0:ℝ) ≤ -x := by linarith
    have pz : (0:ℝ) ≤ -z := by linarith
    have hkey := three_neg (-a) (-x) (-z) b c y pa px pz hb hc hy (by linarith) (by linear_combination hq)
    linarith [hkey]
  · -- -++--+
    have pa : (0:ℝ) ≤ -a := by linarith
    have px : (0:ℝ) ≤ -x := by linarith
    have py : (0:ℝ) ≤ -y := by linarith
    have hkey := three_neg (-a) (-x) (-y) b c z pa px py hb hc hz (by linarith) (by linear_combination hq)
    linarith [hkey]
  · -- -++---
    have pa : (0:ℝ) ≤ -a := by linarith
    have px : (0:ℝ) ≤ -x := by linarith
    have py : (0:ℝ) ≤ -y := by linarith
    have pz : (0:ℝ) ≤ -z := by linarith
    have hnn : (0:ℝ) ≤ (-a) * b * c * (-x) * (-y) * (-z) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg pa hb) hc) px) py) pz
    linarith [hnn]
  · -- -+-+++
    have pa : (0:ℝ) ≤ -a := by linarith
    have pc : (0:ℝ) ≤ -c := by linarith
    have hnn : (0:ℝ) ≤ (-a) * b * (-c) * x * y * z :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg pa hb) pc) hx) hy) hz
    linarith [hnn]
  · -- -+-++-
    have pa : (0:ℝ) ≤ -a := by linarith
    have pc : (0:ℝ) ≤ -c := by linarith
    have pz : (0:ℝ) ≤ -z := by linarith
    have hkey := three_neg (-a) (-c) (-z) b x y pa pc pz hb hx hy (by linarith) (by linear_combination hq)
    linarith [hkey]
  · -- -+-+-+
    have pa : (0:ℝ) ≤ -a := by linarith
    have pc : (0:ℝ) ≤ -c := by linarith
    have py : (0:ℝ) ≤ -y := by linarith
    have hkey := three_neg (-a) (-c) (-y) b x z pa pc py hb hx hz (by linarith) (by linear_combination hq)
    linarith [hkey]
  · -- -+-+--
    have pa : (0:ℝ) ≤ -a := by linarith
    have pc : (0:ℝ) ≤ -c := by linarith
    have py : (0:ℝ) ≤ -y := by linarith
    have pz : (0:ℝ) ≤ -z := by linarith
    have hnn : (0:ℝ) ≤ (-a) * b * (-c) * x * (-y) * (-z) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg pa hb) pc) hx) py) pz
    linarith [hnn]
  · -- -+--++
    have pa : (0:ℝ) ≤ -a := by linarith
    have pc : (0:ℝ) ≤ -c := by linarith
    have px : (0:ℝ) ≤ -x := by linarith
    have hkey := three_neg (-a) (-c) (-x) b y z pa pc px hb hy hz (by linarith) (by linear_combination hq)
    linarith [hkey]
  · -- -+--+-
    have pa : (0:ℝ) ≤ -a := by linarith
    have pc : (0:ℝ) ≤ -c := by linarith
    have px : (0:ℝ) ≤ -x := by linarith
    have pz : (0:ℝ) ≤ -z := by linarith
    have hnn : (0:ℝ) ≤ (-a) * b * (-c) * (-x) * y * (-z) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg pa hb) pc) px) hy) pz
    linarith [hnn]
  · -- -+---+
    have pa : (0:ℝ) ≤ -a := by linarith
    have pc : (0:ℝ) ≤ -c := by linarith
    have px : (0:ℝ) ≤ -x := by linarith
    have py : (0:ℝ) ≤ -y := by linarith
    have hnn : (0:ℝ) ≤ (-a) * b * (-c) * (-x) * (-y) * z :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg pa hb) pc) px) py) hz
    linarith [hnn]
  · -- -+----
    have pa : (0:ℝ) ≤ -a := by linarith
    have pc : (0:ℝ) ≤ -c := by linarith
    have px : (0:ℝ) ≤ -x := by linarith
    have py : (0:ℝ) ≤ -y := by linarith
    have pz : (0:ℝ) ≤ -z := by linarith
    have hkey := five_neg (-a) (-c) (-x) (-y) (-z) b pa pc px py pz hb (by linarith) (by linear_combination hq)
    linarith [hkey]
  · -- --++++
    have pa : (0:ℝ) ≤ -a := by linarith
    have pb : (0:ℝ) ≤ -b := by linarith
    have hnn : (0:ℝ) ≤ (-a) * (-b) * c * x * y * z :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg pa pb) hc) hx) hy) hz
    linarith [hnn]
  · -- --+++-
    have pa : (0:ℝ) ≤ -a := by linarith
    have pb : (0:ℝ) ≤ -b := by linarith
    have pz : (0:ℝ) ≤ -z := by linarith
    have hkey := three_neg (-a) (-b) (-z) c x y pa pb pz hc hx hy (by linarith) (by linear_combination hq)
    linarith [hkey]
  · -- --++-+
    have pa : (0:ℝ) ≤ -a := by linarith
    have pb : (0:ℝ) ≤ -b := by linarith
    have py : (0:ℝ) ≤ -y := by linarith
    have hkey := three_neg (-a) (-b) (-y) c x z pa pb py hc hx hz (by linarith) (by linear_combination hq)
    linarith [hkey]
  · -- --++--
    have pa : (0:ℝ) ≤ -a := by linarith
    have pb : (0:ℝ) ≤ -b := by linarith
    have py : (0:ℝ) ≤ -y := by linarith
    have pz : (0:ℝ) ≤ -z := by linarith
    have hnn : (0:ℝ) ≤ (-a) * (-b) * c * x * (-y) * (-z) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg pa pb) hc) hx) py) pz
    linarith [hnn]
  · -- --+-++
    have pa : (0:ℝ) ≤ -a := by linarith
    have pb : (0:ℝ) ≤ -b := by linarith
    have px : (0:ℝ) ≤ -x := by linarith
    have hkey := three_neg (-a) (-b) (-x) c y z pa pb px hc hy hz (by linarith) (by linear_combination hq)
    linarith [hkey]
  · -- --+-+-
    have pa : (0:ℝ) ≤ -a := by linarith
    have pb : (0:ℝ) ≤ -b := by linarith
    have px : (0:ℝ) ≤ -x := by linarith
    have pz : (0:ℝ) ≤ -z := by linarith
    have hnn : (0:ℝ) ≤ (-a) * (-b) * c * (-x) * y * (-z) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg pa pb) hc) px) hy) pz
    linarith [hnn]
  · -- --+--+
    have pa : (0:ℝ) ≤ -a := by linarith
    have pb : (0:ℝ) ≤ -b := by linarith
    have px : (0:ℝ) ≤ -x := by linarith
    have py : (0:ℝ) ≤ -y := by linarith
    have hnn : (0:ℝ) ≤ (-a) * (-b) * c * (-x) * (-y) * z :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg pa pb) hc) px) py) hz
    linarith [hnn]
  · -- --+---
    have pa : (0:ℝ) ≤ -a := by linarith
    have pb : (0:ℝ) ≤ -b := by linarith
    have px : (0:ℝ) ≤ -x := by linarith
    have py : (0:ℝ) ≤ -y := by linarith
    have pz : (0:ℝ) ≤ -z := by linarith
    have hkey := five_neg (-a) (-b) (-x) (-y) (-z) c pa pb px py pz hc (by linarith) (by linear_combination hq)
    linarith [hkey]
  · -- ---+++
    have pa : (0:ℝ) ≤ -a := by linarith
    have pb : (0:ℝ) ≤ -b := by linarith
    have pc : (0:ℝ) ≤ -c := by linarith
    have hkey := three_neg (-a) (-b) (-c) x y z pa pb pc hx hy hz (by linarith) (by linear_combination hq)
    linarith [hkey]
  · -- ---++-
    have pa : (0:ℝ) ≤ -a := by linarith
    have pb : (0:ℝ) ≤ -b := by linarith
    have pc : (0:ℝ) ≤ -c := by linarith
    have pz : (0:ℝ) ≤ -z := by linarith
    have hnn : (0:ℝ) ≤ (-a) * (-b) * (-c) * x * y * (-z) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg pa pb) pc) hx) hy) pz
    linarith [hnn]
  · -- ---+-+
    have pa : (0:ℝ) ≤ -a := by linarith
    have pb : (0:ℝ) ≤ -b := by linarith
    have pc : (0:ℝ) ≤ -c := by linarith
    have py : (0:ℝ) ≤ -y := by linarith
    have hnn : (0:ℝ) ≤ (-a) * (-b) * (-c) * x * (-y) * z :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg pa pb) pc) hx) py) hz
    linarith [hnn]
  · -- ---+--
    have pa : (0:ℝ) ≤ -a := by linarith
    have pb : (0:ℝ) ≤ -b := by linarith
    have pc : (0:ℝ) ≤ -c := by linarith
    have py : (0:ℝ) ≤ -y := by linarith
    have pz : (0:ℝ) ≤ -z := by linarith
    have hkey := five_neg (-a) (-b) (-c) (-y) (-z) x pa pb pc py pz hx (by linarith) (by linear_combination hq)
    linarith [hkey]
  · -- ----++
    have pa : (0:ℝ) ≤ -a := by linarith
    have pb : (0:ℝ) ≤ -b := by linarith
    have pc : (0:ℝ) ≤ -c := by linarith
    have px : (0:ℝ) ≤ -x := by linarith
    have hnn : (0:ℝ) ≤ (-a) * (-b) * (-c) * (-x) * y * z :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg pa pb) pc) px) hy) hz
    linarith [hnn]
  · -- ----+-
    have pa : (0:ℝ) ≤ -a := by linarith
    have pb : (0:ℝ) ≤ -b := by linarith
    have pc : (0:ℝ) ≤ -c := by linarith
    have px : (0:ℝ) ≤ -x := by linarith
    have pz : (0:ℝ) ≤ -z := by linarith
    have hkey := five_neg (-a) (-b) (-c) (-x) (-z) y pa pb pc px pz hy (by linarith) (by linear_combination hq)
    linarith [hkey]
  · -- -----+
    have pa : (0:ℝ) ≤ -a := by linarith
    have pb : (0:ℝ) ≤ -b := by linarith
    have pc : (0:ℝ) ≤ -c := by linarith
    have px : (0:ℝ) ≤ -x := by linarith
    have py : (0:ℝ) ≤ -y := by linarith
    have hkey := five_neg (-a) (-b) (-c) (-x) (-y) z pa pb pc px py hz (by linarith) (by linear_combination hq)
    linarith [hkey]
  · -- ------
    have pa : (0:ℝ) ≤ -a := by linarith
    have pb : (0:ℝ) ≤ -b := by linarith
    have pc : (0:ℝ) ≤ -c := by linarith
    have px : (0:ℝ) ≤ -x := by linarith
    have py : (0:ℝ) ≤ -y := by linarith
    have pz : (0:ℝ) ≤ -z := by linarith
    have hnn : (0:ℝ) ≤ (-a) * (-b) * (-c) * (-x) * (-y) * (-z) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg pa pb) pc) px) py) pz
    linarith [hnn]

/-- **El valor se alcanza**: para `a = b = c = x = y = 4/3` y `z = -8/3` se cumplen las dos
restricciones y `abcxyz = -8192/729`. -/
theorem alcanzado : ∃ a b c x y z : ℝ, a + b + c + x + y + z = 4 ∧
    a ^ 2 + b ^ 2 + c ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = 16 ∧
    a * b * c * x * y * z = -(8192 / 729) :=
  ⟨4/3, 4/3, 4/3, 4/3, 4/3, -8/3, by norm_num, by norm_num, by norm_num⟩

/-- **Solución del problema**: el mínimo de `abcxyz` sujeto a `a + b + c + x + y + z = 4` y
`a² + b² + c² + x² + y² + z² = 16` es `-8192/729`. -/
theorem min_producto :
    IsLeast {p : ℝ | ∃ a b c x y z : ℝ, a + b + c + x + y + z = 4 ∧
      a ^ 2 + b ^ 2 + c ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = 16 ∧ p = a * b * c * x * y * z}
      (-(8192 / 729)) := by
  constructor
  · exact ⟨4/3, 4/3, 4/3, 4/3, 4/3, -8/3, by norm_num, by norm_num, by norm_num⟩
  · rintro p ⟨a, b, c, x, y, z, hs, hq, rfl⟩
    exact cota_inferior a b c x y z hs hq

end RetoMin
