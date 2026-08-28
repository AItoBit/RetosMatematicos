import Mathlib

open Real Filter Topology intervalIntegral

noncomputable section

namespace RetosMatematicos

/-!
# Retos Matemáticos — 6 de enero de 2023 (ISSN: 2952-0746)

Problema:
  Sea γ_n = -ln(n) + ∑_{k=1}^n (1/k) y γ = lim_{n→∞} γ_n.
  Para f : (0, +∞) → (0, +∞) continua, calcular:
    lim_{n→∞} ((2n - 1)!!)^(1/n) * ∫_γ^{γ_n} f(x) dx = f(γ) / e
-/

-- ============================================================================
-- 1. DEFINICIONES BÁSICAS
-- ============================================================================

/-- Doble factorial (2n - 1)!! = ∏_{i=0}^{n-1} (2i + 1) -/
def doubleFact (n : ℕ) : ℕ :=
  ∏ i ∈ Finset.range n, (2 * i + 1)

/-- Sucesión armónica H_n = ∑_{k=1}^n 1/k -/
def harmonic (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, (1 : ℝ) / (k + 1 : ℝ)

/-- Sucesión de Euler-Mascheroni: γ_n = H_n - ln(n) -/
def gammaSeq (n : ℕ) : ℝ :=
  harmonic n - Real.log (n : ℝ)

-- ============================================================================
-- 2. LEMAS PREVIOS
-- ============================================================================

/-- Límite de la cota inferior del Lema 1: lim_{n→∞} n / (2(n + 1)) = 1/2 -/
lemma tendsto_cota_inferior :
    Tendsto (fun n : ℕ => (n : ℝ) / (2 * ((n : ℝ) + 1))) atTop (𝓝 (1 / 2)) := by
  have h_eq : (fun n : ℕ => (n : ℝ) / (2 * ((n : ℝ) + 1))) =
              (fun n : ℕ => (1 / 2 : ℝ) - (1 / 2 : ℝ) * (1 / ((n : ℝ) + 1))) := by
    funext n
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  rw [h_eq]
  have h_inv : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat

  -- Usamos const_mul (multiplicación por la izquierda)
  have h_prod : Tendsto (fun n : ℕ => (1 / 2 : ℝ) * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    have h := h_inv.const_mul (1 / 2 : ℝ)
    have hz : (1 / 2 : ℝ) * 0 = 0 := by ring
    rwa [hz] at h

  -- Restamos el límite constante 1/2 y el límite 0
  have h_sub := (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub h_prod
  have h_sub_val : (1 / 2 : ℝ) - 0 = 1 / 2 := by ring
  rwa [h_sub_val] at h_sub

/-- **Lema 1 (Regla del Sándwich para γ_n - γ)**:
    Dado que n / (2(n+1)) < n(γ_n - γ) < 1/2, se concluye que lim n(γ_n - γ) = 1/2. -/
theorem lema1_sandwich (γ : ℝ)
    (h_bounds : ∀ᶠ (n : ℕ) in atTop,
      (n : ℝ) / (2 * ((n : ℝ) + 1)) ≤ (n : ℝ) * (gammaSeq n - γ) ∧
      (n : ℝ) * (gammaSeq n - γ) ≤ (1 / 2 : ℝ)) :
    Tendsto (fun n : ℕ => (n : ℝ) * (gammaSeq n - γ)) atTop (𝓝 (1 / 2)) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_cota_inferior tendsto_const_nhds
  · filter_upwards [h_bounds] with n hn; exact hn.1
  · filter_upwards [h_bounds] with n hn; exact hn.2

-- ============================================================================
-- 3. TEOREMA PRINCIPAL (Combinación asintótica)
-- ============================================================================

/--
**Teorema:**
Sean:
1. `h_fact`: lim_{n→∞} ((2n - 1)!!)^(1/n) / (2n) = 1/e   (Lema 3 / Stirling)
2. `h_int` : lim_{n→∞} 2n * ∫_γ^{γ_n} f(x) dx = f(γ)     (Lema 2 / TFC)

Entonces:
  lim_{n→∞} ((2n - 1)!!)^(1/n) * ∫_γ^{γ_n} f(x) dx = f(γ) / e
-/
theorem limite_reto (γ : ℝ) (f : ℝ → ℝ)
    (h_fact : Tendsto (fun n : ℕ => ((doubleFact n : ℝ) ^ ((1 : ℝ) / (n : ℝ))) / (2 * (n : ℝ)))
              atTop (𝓝 (1 / Real.exp 1)))
    (h_int  : Tendsto (fun n : ℕ => 2 * (n : ℝ) * (∫ x in γ..(gammaSeq n), f x))
              atTop (𝓝 (f γ))) :
    Tendsto (fun n : ℕ => ((doubleFact n : ℝ) ^ ((1 : ℝ) / (n : ℝ))) * (∫ x in γ..(gammaSeq n), f x))
      atTop (𝓝 (f γ / Real.exp 1)) := by

  have h_mul := h_fact.mul h_int
  have h_val : (1 / Real.exp 1) * f γ = f γ / Real.exp 1 := by ring
  rw [h_val] at h_mul

  refine Tendsto.congr' ?_ h_mul
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  have h2n : 2 * (n : ℝ) ≠ 0 := by positivity

  calc
    (((doubleFact n : ℝ) ^ ((1 : ℝ) / (n : ℝ))) / (2 * (n : ℝ))) *
        (2 * (n : ℝ) * (∫ x in γ..(gammaSeq n), f x))
      = ((doubleFact n : ℝ) ^ ((1 : ℝ) / (n : ℝ))) * (∫ x in γ..(gammaSeq n), f x) *
        ((2 * (n : ℝ)) / (2 * (n : ℝ))) := by ring
    _ = ((doubleFact n : ℝ) ^ ((1 : ℝ) / (n : ℝ))) * (∫ x in γ..(gammaSeq n), f x) := by
      rw [div_self h2n, mul_one]

end RetosMatematicos
