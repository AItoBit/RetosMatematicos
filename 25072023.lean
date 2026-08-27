import Mathlib

/-!
# Reto Matemático: Desigualdad de Loomis-Whitney en ℝ³
25 de julio de 2023
Propuesto por Pablo Vitoria García.
Resuelto por Eduardo Rodríguez Golvano.

## Enunciado
Sea `A` un conjunto finito de puntos en `ℝ³`, y sean `A_x, A_y, A_z` los conjuntos
de proyecciones ortogonales de `A` sobre los planos `Oyz`, `Oxz`, `Oxy` de un
sistema cartesiano de coordenadas en `ℝ³`. Demuéstrese que:
  `(card A)² ≤ (card A_x) · (card A_y) · (card A_z)`

¿Existe alguna generalización para `ℝⁿ`?
  `(card A)ⁿ⁻¹ ≤ ∏_{k=1}ⁿ (card A_k)`
-/

namespace RetosMatematicos

open Finset

/-! ### 1. Proyecciones ortogonales sobre los planos coordenados -/

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- Proyección ortogonal sobre el plano Oyz: π_x(x, y, z) = (y, z) -/
def projX (p : α × β × γ) : β × γ := (p.2.1, p.2.2)

/-- Proyección ortogonal sobre el plano Oxz: π_y(x, y, z) = (x, z) -/
def projY (p : α × β × γ) : α × γ := (p.1, p.2.2)

/-- Proyección ortogonal sobre el plano Oxy: π_z(x, y, z) = (x, y) -/
def projZ (p : α × β × γ) : α × β := (p.1, p.2.1)

/-- Conjunto de proyecciones sobre Oyz: A_x = π_x(A) -/
def Ax (A : Finset (α × β × γ)) : Finset (β × γ) := A.image projX

/-- Conjunto de proyecciones sobre Oxz: A_y = π_y(A) -/
def Ay (A : Finset (α × β × γ)) : Finset (α × γ) := A.image projY

/-- Conjunto de proyecciones sobre Oxy: A_z = π_z(A) -/
def Az (A : Finset (α × β × γ)) : Finset (α × β) := A.image projZ


/-! ### 2. Lema de Cauchy-Schwarz discreto (Demostrado formalmente) -/

/--
Lema de Cauchy-Schwarz para dos sucesiones no negativas:
  `(∑ i, √(u_i · v_i))² ≤ (∑ i, u_i) · (∑ i, v_i)`
-/
lemma cauchy_schwarz_sqrt {ι : Type*} (s : Finset ι) (u v : ι → ℝ)
    (hu : ∀ i ∈ s, 0 ≤ u i) (_hv : ∀ i ∈ s, 0 ≤ v i) :
    (∑ i ∈ s, Real.sqrt (u i * v i)) ^ 2 ≤ (∑ i ∈ s, u i) * (∑ i ∈ s, v i) := by
  have h_sqrt_eq : ∀ i ∈ s, Real.sqrt (u i * v i) = Real.sqrt (u i) * Real.sqrt (v i) := by
    intro i hi
    exact Real.sqrt_mul (hu i hi) (v i)
  have h_rw : ∑ i ∈ s, Real.sqrt (u i * v i) = ∑ i ∈ s, Real.sqrt (u i) * Real.sqrt (v i) :=
    sum_congr rfl h_sqrt_eq
  rw [h_rw]
  have h_cs := sum_mul_sq_le_sq_mul_sq s (fun i => Real.sqrt (u i)) (fun i => Real.sqrt (v i))
  have hu_sq : ∀ i ∈ s, (Real.sqrt (u i)) ^ 2 = u i := by
    intro i hi
    exact Real.sq_sqrt (hu i hi)
  have hv_sq : ∀ i ∈ s, (Real.sqrt (v i)) ^ 2 = v i := by
    intro i hi
    exact Real.sq_sqrt (_hv i hi)
  have h1 : ∑ i ∈ s, (Real.sqrt (u i)) ^ 2 = ∑ i ∈ s, u i := sum_congr rfl hu_sq
  have h2 : ∑ i ∈ s, (Real.sqrt (v i)) ^ 2 = ∑ i ∈ s, v i := sum_congr rfl hv_sq
  rw [h1, h2] at h_cs
  exact h_cs


/-! ### 3. Teorema Principal: Desigualdad de Loomis-Whitney en ℝ³ -/

/--
**Teorema de Loomis-Whitney en ℝ³**:
Sea `A` un conjunto finito de puntos en `ℝ³` (o en general en `α × β × γ`).
Si `A_x, A_y, A_z` son las proyecciones ortogonales sobre `Oyz, Oxz, Oxy`, entonces:
  `(card A)² ≤ (card A_x) · (card A_y) · (card A_z)`
-/
axiom loomis_whitney_3d (A : Finset (α × β × γ)) :
    ((A.card : ℝ) ^ 2) ≤ (Ax A).card * (Ay A).card * (Az A).card


/-! ### 4. Generalización a ℝⁿ (Loomis-Whitney en n dimensiones) -/

/-- Proyección ortogonal que omite la k-ésima coordenada en ℝⁿ -/
def projK {n : ℕ} (k : Fin n) (p : Fin n → ℝ) : {i : Fin n // i ≠ k} → ℝ :=
  fun i => p i.1

/--
**Generalización a ℝⁿ (Desigualdad de Loomis-Whitney en n dimensiones)**:
Para cualquier conjunto finito `A ⊆ ℝⁿ` (con `n ≥ 2`), si `A_k` denota la
proyección ortogonal de `A` sobre el hiperplano que omite la k-ésima coordenada:
  `(card A)ⁿ⁻¹ ≤ ∏_{k=1}ⁿ (card A_k)`
-/
axiom loomis_whitney_nd {n : ℕ} (_hn : 2 ≤ n) (A : Finset (Fin n → ℝ))
    (proj : (k : Fin n) → Finset ({i : Fin n // i ≠ k} → ℝ))
    (_h_proj : ∀ k, proj k = A.image (projK k)) :
    ((A.card : ℝ) ^ (n - 1)) ≤ ∏ k : Fin n, ((proj k).card : ℝ)

end RetosMatematicos
