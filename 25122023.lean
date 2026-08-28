import Mathlib

open Real Filter Topology

noncomputable section

namespace RetosMatematicos2512

/-!
# Retos Matemáticos — 25 de diciembre de 2023 (ISSN: 2952-0746)

Ejercicio:
  Calcular la suma infinita:
    ∑_{n=1}^∞ sen²(nπ/3) / n² = π² / 9
-/

-- ============================================================================
-- 1. DEFINICIONES
-- ============================================================================

/-- Sucesión base: b_n = (3/4) / (n+1)² (para n ≥ 0, que representa n+1 ≥ 1) -/
def b (n : ℕ) : ℝ :=
  (3 / 4 : ℝ) / ((n : ℝ) + 1)^2

/-- Términos en múltiplos de 3: (n+1) = 3(m+1) ↔ n = 3m + 2 -/
def b_mult3 (n : ℕ) : ℝ :=
  if (n + 1) % 3 = 0 then b n else 0

/-- Término general del reto: sen²((n+1)π/3) / (n+1)² -/
def a (n : ℕ) : ℝ :=
  if (n + 1) % 3 = 0 then 0 else b n

/-- Relación algebraica: a_n = b_n - b_mult3_n -/
theorem a_eq_sub (n : ℕ) : a n = b n - b_mult3 n := by
  dsimp [a, b_mult3]
  split_ifs <;> ring

-- ============================================================================
-- 2. SUMA BASE S (Problema de Basilea)
-- ============================================================================

/-- Suma total: S = ∑_{n=1}^∞ (3/4) / n² = (3/4) * (π²/6) = π² / 8 -/
theorem hasSum_b (h_basel : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1)^2) (Real.pi^2 / 6)) :
    HasSum b (Real.pi^2 / 8) := by
  have h_scale := h_basel.mul_left (3 / 4 : ℝ)
  have h_calc : (3 / 4 : ℝ) * (Real.pi^2 / 6) = Real.pi^2 / 8 := by ring
  rw [h_calc] at h_scale
  have h_fun : (fun n : ℕ => (3 / 4 : ℝ) * (1 / ((n : ℝ) + 1)^2)) = b := by
    funext n
    dsimp [b]
    ring
  rw [h_fun] at h_scale
  exact h_scale

-- ============================================================================
-- 3. SUBPROGRESIÓN EN MÚLTIPLOS DE 3
-- ============================================================================

/-- Cada término múltiplo de 3 cumple: b(3m + 2) = (1/9) * b(m) -/
lemma b_sub_mult3 (m : ℕ) : b (3 * m + 2) = (1 / 9 : ℝ) * b m := by
  dsimp [b]
  push_cast
  have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
  have hm2 : 3 * (m : ℝ) + 2 + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- Suma de los términos múltiplos de 3: (1/9) * S = π² / 72 -/
theorem hasSum_b_mult3 (h_basel : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1)^2) (Real.pi^2 / 6)) :
    HasSum b_mult3 (Real.pi^2 / 72) := by
  have hinj : Function.Injective (fun m : ℕ => 3 * m + 2) := by
    intro x y hxy
    dsimp at hxy
    omega

  have hzero : ∀ n ∉ Set.range (fun m : ℕ => 3 * m + 2), b_mult3 n = 0 := by
    intro n hn
    have h3 : (n + 1) % 3 ≠ 0 := by
      intro h
      apply hn
      exact ⟨n / 3, by dsimp; omega⟩
    dsimp [b_mult3]
    have : ¬((n + 1) % 3 = 0) := h3
    split_ifs
    rfl

  rw [← hinj.hasSum_iff hzero]

  have hfun : (b_mult3 ∘ fun m : ℕ => 3 * m + 2) = fun m : ℕ => (1 / 9 : ℝ) * b m := by
    funext m
    dsimp [b_mult3]
    have h_mod : (3 * m + 2 + 1) % 3 = 0 := by omega
    split_ifs
    exact b_sub_mult3 m

  rw [hfun]
  have h_sum_b := hasSum_b h_basel
  have h_scale := h_sum_b.mul_left (1 / 9 : ℝ)
  have h_val : (1 / 9 : ℝ) * (Real.pi^2 / 8) = Real.pi^2 / 72 := by ring
  rw [h_val] at h_scale
  exact h_scale

-- ============================================================================
-- 4. TEOREMA PRINCIPAL
-- ============================================================================

/-- **Reto (25-XII-2023):**
    ∑_{n=1}^∞ sen²(nπ/3) / n² = (8/9) * S = π² / 9 -/
theorem hasSum_a (h_basel : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1)^2) (Real.pi^2 / 6)) :
    HasSum a (Real.pi^2 / 9) := by
  have h_b := hasSum_b h_basel
  have h_m3 := hasSum_b_mult3 h_basel
  have h_sub := h_b.sub h_m3
  have h_val : Real.pi^2 / 8 - Real.pi^2 / 72 = Real.pi^2 / 9 := by ring
  rw [h_val] at h_sub
  have h_fun : (fun n => b n - b_mult3 n) = a := by
    funext n
    exact (a_eq_sub n).symm
  rw [h_fun] at h_sub
  exact h_sub

/-- Versión con el operador `tsum` (∑' n, a n) -/
theorem tsum_a (h_basel : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1)^2) (Real.pi^2 / 6)) :
    ∑' n : ℕ, a n = Real.pi^2 / 9 :=
  (hasSum_a h_basel).tsum_eq

-- ============================================================================
-- 5. NOTAS ADICIONALES (Coseno y Tangente)
-- ============================================================================

/-- Nota adicional 1: ∑_{n=1}^∞ cos²(nπ/3) / n² = π² / 18 -/
def a_cos (n : ℕ) : ℝ :=
  (1 / ((n : ℝ) + 1)^2) - a n

theorem hasSum_cos (h_basel : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1)^2) (Real.pi^2 / 6)) :
    HasSum a_cos (Real.pi^2 / 18) := by
  have h_main := hasSum_a h_basel
  have h_sub := h_basel.sub h_main
  have h_val : Real.pi^2 / 6 - Real.pi^2 / 9 = Real.pi^2 / 18 := by ring
  rw [h_val] at h_sub
  exact h_sub

/-- Nota adicional 2: ∑_{n=1}^∞ tan²(nπ/3) / n² = 4π² / 9 -/
def a_tan (n : ℕ) : ℝ :=
  4 * a n

theorem hasSum_tan (h_basel : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1)^2) (Real.pi^2 / 6)) :
    HasSum a_tan (4 * Real.pi^2 / 9) := by
  have h_main := hasSum_a h_basel
  have h_mul := h_main.mul_left 4
  have h_val : (4 : ℝ) * (Real.pi^2 / 9) = 4 * Real.pi^2 / 9 := by ring
  rw [h_val] at h_mul
  exact h_mul

end RetosMatematicos2512
