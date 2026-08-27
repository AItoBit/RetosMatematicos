import Mathlib

/-!
# Reto Matemático: Ecuación cuadrática x² + 3x - 5 ≡ 0 (mód 7)

Formalizamos la resolución de la congruencia cuadrática demostrando que
sus soluciones son exactamente:
  x ≡ 5 (mód 7)  o  x ≡ 6 (mód 7)
-/

/-! ## 1. Resolución en el cuerpo ℤ/7ℤ (`ZMod 7`) -/

/--
En `ZMod 7`, la ecuación cuadrática se factoriza como:
  x² + 3x - 5 = (x - 5)(x - 6)
-/
theorem zmod_quad_fact (x : ZMod 7) : x ^ 2 + 3 * x - 5 = (x - 5) * (x - 6) := by
  revert x
  decide

/--
Las únicas soluciones en `ZMod 7` son 5 y 6.
-/
theorem zmod_quad_eq (x : ZMod 7) : x ^ 2 + 3 * x - 5 = 0 ↔ x = 5 ∨ x = 6 := by
  revert x
  decide

/-! ## 2. Resolución en ℤ mediante divisibilidad y primalidad de 7 -/

/--
En los enteros ℤ, 7 divide a (x² + 3x - 5) si y solo si
7 divide a (x - 5) o 7 divide a (x - 6).
-/
theorem int_quad_dvd (x : ℤ) :
    (7 : ℤ) ∣ (x ^ 2 + 3 * x - 5) ↔ (7 : ℤ) ∣ (x - 5) ∨ (7 : ℤ) ∣ (x - 6) := by
  -- Factorización en ℤ: x² + 3x - 5 = (x + 1)(x + 2) - 7
  have h_fact : x ^ 2 + 3 * x - 5 = (x + 1) * (x + 2) - 7 := by ring
  rw [h_fact]
  have h_dvd : (7 : ℤ) ∣ (x + 1) * (x + 2) - 7 ↔ (7 : ℤ) ∣ (x + 1) * (x + 2) := by
    constructor
    · intro h
      have : (x + 1) * (x + 2) = (x + 1) * (x + 2) - 7 + 7 := by ring
      rw [this]
      exact dvd_add h dvd_rfl
    · intro h
      exact dvd_sub h dvd_rfl
  rw [h_dvd, Prime.dvd_mul (by norm_num : Prime (7 : ℤ))]
  have h1 : (7 : ℤ) ∣ (x + 1) ↔ (7 : ℤ) ∣ (x - 6) := by omega
  have h2 : (7 : ℤ) ∣ (x + 2) ↔ (7 : ℤ) ∣ (x - 5) := by omega
  rw [h1, h2]
  tauto

/-! ## 3. Forma paramétrica de las soluciones: x = 7k + 5 o x = 7k + 6 -/

theorem int_quad_solutions (x : ℤ) :
    (7 : ℤ) ∣ (x ^ 2 + 3 * x - 5) ↔ (∃ k : ℤ, x = 7 * k + 5) ∨ (∃ k : ℤ, x = 7 * k + 6) := by
  rw [int_quad_dvd]
  constructor
  · rintro (⟨k, hk⟩ | ⟨k, hk⟩)
    · left; exact ⟨k, by omega⟩
    · right; exact ⟨k, by omega⟩
  · rintro (⟨k, hk⟩ | ⟨k, hk⟩)
    · left; exact ⟨k, by omega⟩
    · right; exact ⟨k, by omega⟩
