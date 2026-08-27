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
# Retos Matemáticos, 25 de abril de 2025

Sean `a` y `b` dos enteros positivos y sea `X` una variable aleatoria discreta con valores
enteros estrictamente positivos tal que

  `P(X = x) = 1/a - 1/b` si `1 ≤ x ≤ ab`, y `P(X = x) = 0` si `x > ab`.

* a) ¿Qué condición deben cumplir `a` y `b` para que `p(x) = P(X = x)` sea una ley de
     probabilidad?  Respuesta: `b = a + 1`.
* b) Función de distribución `F(x)` y soluciones de `F(x) = 1/2` (las medianas de `X`).
     Respuesta: `F` es escalonada, y el conjunto de medianas es el intervalo
     `[a(a+1)/2, a(a+1)/2 + 1)`.
* c) Esperanza de `X`: `E(X) = (1 + ab)/2`; `E(X) = 13/2` sii `a = 3`, `b = 4`.
-/

namespace RetosMatematicos20250425

/-- La ley puntual del enunciado: `p a b x = 1/a - 1/b` si `1 ≤ x ≤ a·b`, y `0` si `x > a·b`. -/
noncomputable def p (a b : ℕ) (x : ℕ) : ℝ :=
  if 1 ≤ x ∧ x ≤ a * b then (1 : ℝ) / a - 1 / b else 0

/-- La función de distribución `F(x) = ∑_{t ≤ x} P(X = t)` (la suma recorre los enteros
positivos `t ≤ x`). -/
noncomputable def F (a b : ℕ) (x : ℝ) : ℝ := ∑ t ∈ Finset.Icc 1 ⌊x⌋₊, p a b t

section Basic

lemma p_of_gt (a b : ℕ) {x : ℕ} (hx : a * b < x) : p a b x = 0 := by
  unfold p
  split_ifs with h
  · omega
  · rfl

lemma sum_p_Icc (a b : ℕ) :
    (∑ x ∈ Finset.Icc 1 (a * b), p a b x) = (a * b : ℕ) * ((1 : ℝ) / a - 1 / b) := by
  have h : ∀ x ∈ Finset.Icc 1 (a * b), p a b x = (1 : ℝ) / a - 1 / b := by
    intro x hx
    simp only [Finset.mem_Icc] at hx
    unfold p
    split_ifs with h_cond
    · rfl
    · omega
  rw [Finset.sum_congr rfl h, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  push_cast
  ring

/-- Suma de Gauss en `ℕ`. -/
lemma gauss_nat (n : ℕ) : (∑ i ∈ Finset.Icc 1 n, i) * 2 = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      ring_nf
      ring_nf at ih
      omega

/-- Suma de Gauss, con valores reales. -/
lemma gauss_real (n : ℕ) : (∑ i ∈ Finset.Icc 1 n, (i : ℝ)) = (n : ℝ) * (n + 1) / 2 := by
  have h : ((∑ i ∈ Finset.Icc 1 n, i : ℕ) : ℝ) * 2 = (n : ℝ) * (n + 1) := by
    exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) (gauss_nat n)
  push_cast at h
  linarith

end Basic

/-! ## a) La condición para que `p` sea una ley de probabilidad -/

/-- La suma total de la ley puntual vale `b - a`. -/
theorem tsum_p (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (∑' x : ℕ, p a b x) = (b : ℝ) - a := by
  have ha' : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ha.ne'
  have hb' : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
  rw [tsum_eq_sum (s := Finset.Icc 1 (a * b)) (fun x hx => ?_), sum_p_Icc]
  · push_cast
    field_simp
  · simp only [Finset.mem_Icc, not_and, not_le] at hx
    unfold p
    split_ifs with h
    · have := hx h.1
      omega
    · rfl

/-- **a)** Para enteros positivos `a`, `b`, la sucesión `p(x)` es una ley de probabilidad
(suma total igual a `1`) si y sólo si `b = a + 1`. -/
theorem tsum_p_eq_one_iff (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (∑' x : ℕ, p a b x) = 1 ↔ b = a + 1 := by
  rw [tsum_p a b ha hb]
  constructor
  · intro h
    have : (b : ℝ) = (a + 1 : ℕ) := by push_cast; linarith
    exact_mod_cast this
  · rintro rfl
    push_cast
    ring

/-- Cuando `b = a + 1`, la ley puntual es uniforme sobre `{1, …, a(a+1)}`. -/
theorem p_succ (a : ℕ) (ha : 0 < a) (x : ℕ) :
    p a (a + 1) x = if 1 ≤ x ∧ x ≤ a * (a + 1) then (1 : ℝ) / (a * (a + 1)) else 0 := by
  have ha' : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ha.ne'
  have ha1 : (a : ℝ) + 1 ≠ 0 := by positivity
  unfold p
  push_cast
  congr 1
  field_simp
  ring

/-! ## b) La función de distribución y las medianas -/

/-- Forma cerrada de la función de distribución: `F(x) = min(⌊x⌋, a(a+1)) / (a(a+1))`. -/
theorem F_eq_min (a : ℕ) (ha : 0 < a) (x : ℝ) :
    F a (a + 1) x = (min ⌊x⌋₊ (a * (a + 1)) : ℕ) / (a * (a + 1) : ℝ) := by
  have key : (Finset.Icc 1 ⌊x⌋₊).filter (fun t => 1 ≤ t ∧ t ≤ a * (a + 1))
      = Finset.Icc 1 (min ⌊x⌋₊ (a * (a + 1))) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_Icc, le_min_iff]
    omega
  unfold F
  simp only [p_succ a ha]
  rw [← Finset.sum_filter, key, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  push_cast
  ring

/-- **b)** `F(x) = 0` para `x < 1`. -/
theorem F_of_lt_one (a : ℕ) (ha : 0 < a) {x : ℝ} (hx : x < 1) : F a (a + 1) x = 0 := by
  rw [F_eq_min a ha, Nat.floor_eq_zero.mpr hx]
  simp

/-- **b)** `F(x) = ⌊x⌋ / (a(a+1))` para `1 ≤ x < a(a+1)`. -/
theorem F_of_mem (a : ℕ) (ha : 0 < a) {x : ℝ} (hx : 1 ≤ x) (hx' : x < a * (a + 1)) :
    F a (a + 1) x = (⌊x⌋₊ : ℝ) / (a * (a + 1) : ℝ) := by
  have h0 : (0 : ℝ) ≤ x := le_trans zero_le_one hx
  have h : ⌊x⌋₊ < a * (a + 1) := by
    rw [Nat.floor_lt h0]
    push_cast
    exact hx'
  rw [F_eq_min a ha, min_eq_left h.le]

/-- **b)** `F(x) = 1` para `x ≥ a(a+1)`. -/
theorem F_of_ge (a : ℕ) (ha : 0 < a) {x : ℝ} (hx : (a * (a + 1) : ℝ) ≤ x) :
    F a (a + 1) x = 1 := by
  have hpos : (0 : ℝ) < (a : ℝ) * (a + 1) := by positivity
  have h : a * (a + 1) ≤ ⌊x⌋₊ := Nat.le_floor (by push_cast; exact hx)
  rw [F_eq_min a ha, min_eq_right h]
  push_cast
  field_simp

/-- `a(a+1)/2` es un número natural. -/
theorem two_dvd_mul_succ (a : ℕ) : 2 ∣ a * (a + 1) := (Nat.even_mul_succ_self a).two_dvd

/-- **b)** El conjunto de medianas de `X`, es decir el conjunto de soluciones de
`F(x) = 1/2`, es el intervalo `[a(a+1)/2, a(a+1)/2 + 1)`. -/
theorem median_iff (a : ℕ) (ha : 0 < a) (x : ℝ) :
    F a (a + 1) x = 1 / 2 ↔ x ∈ Set.Ico ((a * (a + 1) : ℝ) / 2) ((a * (a + 1) : ℝ) / 2 + 1) := by
  obtain ⟨k, hk⟩ : 2 ∣ a * (a + 1) := two_dvd_mul_succ a
  have hkpos : 0 < k := by nlinarith [Nat.succ_le_of_lt ha]
  have hn : (0 : ℝ) < (a : ℝ) * (a + 1) := by positivity
  have hkr : ((k : ℝ)) = ((a : ℝ) * (a + 1)) / 2 := by
    have h : ((a * (a + 1) : ℕ) : ℝ) = ((2 * k : ℕ) : ℝ) := by rw [hk]
    push_cast at h
    linarith
  rw [F_eq_min a ha, Set.mem_Ico]
  set M : ℕ := min ⌊x⌋₊ (a * (a + 1)) with hM
  constructor
  · intro h
    rw [div_eq_div_iff hn.ne' two_ne_zero] at h
    have hMk : M = k := by
      have : (M : ℝ) = (k : ℝ) := by rw [hkr]; linarith
      exact_mod_cast this
    have hfl : ⌊x⌋₊ = k := by omega
    have h2 := (Nat.floor_eq_iff' (a := x) (n := k) hkpos.ne').mp hfl
    exact ⟨by rw [← hkr]; exact h2.1, by rw [← hkr]; exact h2.2⟩
  · rintro ⟨h1, h2⟩
    have hfl : ⌊x⌋₊ = k := by
      rw [Nat.floor_eq_iff' hkpos.ne', hkr]
      exact ⟨h1, h2⟩
    have hmin : M = k := by omega
    rw [hmin, hkr]
    field_simp

/-! ## c) La esperanza -/

/-- **c)** `E(X) = (1 + a(a+1))/2`. -/
theorem expectation (a : ℕ) (ha : 0 < a) :
    (∑ x ∈ Finset.Icc 1 (a * (a + 1)), (x : ℝ) * p a (a + 1) x)
      = (1 + (a : ℝ) * (a + 1)) / 2 := by
  have hn : (0 : ℝ) < (a : ℝ) * (a + 1) := by positivity
  have h : ∀ x ∈ Finset.Icc 1 (a * (a + 1)), (x : ℝ) * p a (a + 1) x
      = (1 / ((a : ℝ) * (a + 1))) * (x : ℝ) := by
    intro x hx
    simp only [Finset.mem_Icc] at hx
    rw [p_succ a ha]
    split_ifs with h_cond
    · ring
    · omega
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum, gauss_real]
  push_cast
  field_simp
  ring

/-- Si `a(a+1) = 12` con `a` natural, entonces `a = 3`. -/
lemma eq_three_of_mul_succ_eq_twelve {a : ℕ} (h : a * (a + 1) = 12) : a = 3 := by
  have ha : a ≤ 12 := by nlinarith
  interval_cases a <;> omega

/-- **c)** `E(X) = 13/2` si y sólo si `a = 3` (y por tanto `b = a + 1 = 4`). -/
theorem expectation_eq_iff (a : ℕ) (ha : 0 < a) :
    (∑ x ∈ Finset.Icc 1 (a * (a + 1)), (x : ℝ) * p a (a + 1) x) = 13 / 2 ↔ a = 3 := by
  rw [expectation a ha]
  constructor
  · intro h
    have h12 : ((a * (a + 1) : ℕ) : ℝ) = ((12 : ℕ) : ℝ) := by push_cast; linarith
    exact eq_three_of_mul_succ_eq_twelve (by exact_mod_cast h12)
  · rintro rfl
    norm_num

/-- **c)** Solución final: los únicos parámetros enteros positivos para los que `p` es una ley
de probabilidad y `E(X) = 13/2` son `a = 3`, `b = 4`. -/
theorem final_answer (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ((∑' x : ℕ, p a b x) = 1 ∧
      (∑ x ∈ Finset.Icc 1 (a * b), (x : ℝ) * p a b x) = 13 / 2) ↔ (a = 3 ∧ b = 4) := by
  constructor
  · rintro ⟨h1, h2⟩
    have hb' : b = a + 1 := (tsum_p_eq_one_iff a b ha hb).mp h1
    subst hb'
    have ha3 : a = 3 := (expectation_eq_iff a ha).mp h2
    exact ⟨ha3, by omega⟩
  · rintro ⟨rfl, rfl⟩
    refine ⟨(tsum_p_eq_one_iff 3 4 (by norm_num) (by norm_num)).mpr rfl, ?_⟩
    have h : (3 : ℕ) * 4 = 3 * (3 + 1) := by norm_num
    rw [h]
    exact (expectation_eq_iff 3 (by norm_num)).mpr rfl

end RetosMatematicos20250425
