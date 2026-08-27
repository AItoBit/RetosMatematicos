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
# Reto Matemático (15 de febrero de 2024)

En el espacio vectorial `V = ℝ³`, referido a la base `{e₁, e₂, e₃}`, se considera la
forma cuadrática

`Φ(x) = 2x₁x₂ − 2x₁x₃ + (x₂)² − 4x₂x₃ + 3(x₃)²`.

Se pide:

* a) obtener una base conjugada;
* b) clasificarla;
* c) obtener el núcleo;
* d) obtener el subespacio conjugado de `L : x₁ − x₂ = 0`.

Los índices de Lean van de `0` a `2`, de modo que `x 0, x 1, x 2` representan
`x₁, x₂, x₃`.
-/

namespace Retos15022024

/-- El espacio vectorial `V`, identificado con `ℝ³` mediante las coordenadas en la
base `{e₁, e₂, e₃}`. -/
abbrev V : Type := Fin 3 → ℝ

/-- La matriz de la forma cuadrática `Φ` en la base `{e₁, e₂, e₃}`. -/
def M : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1, -1; 1, 1, -2; -1, -2, 3]

/-- La forma cuadrática `Φ(x) = 2x₁x₂ − 2x₁x₃ + (x₂)² − 4x₂x₃ + 3(x₃)²`. -/
def Phi (x : V) : ℝ := 2 * x 0 * x 1 - 2 * x 0 * x 2 + (x 1) ^ 2 - 4 * x 1 * x 2 + 3 * (x 2) ^ 2

/-- La forma polar `Ψ` de `Φ`, dada por la matriz `M`. -/
def Psi (x y : V) : ℝ := ∑ i, ∑ j, M i j * x i * y j

lemma Psi_apply (x y : V) :
    Psi x y = (x 1 - x 2) * y 0 + (x 0 + x 1 - 2 * x 2) * y 1
      + (-x 0 - 2 * x 1 + 3 * x 2) * y 2 := by
  simp [Psi, M, Fin.sum_univ_three]; ring

/-- `Ψ` es simétrica. -/
lemma Psi_symm (x y : V) : Psi x y = Psi y x := by
  simp [Psi_apply]; ring

/-- `Ψ` es la forma polar de `Φ`: `Φ(x) = Ψ(x, x)`. -/
lemma Phi_eq_Psi (x : V) : Phi x = Psi x x := by
  simp [Psi_apply, Phi]; ring

/-! ## a) Base conjugada -/

/-- `v₁ = e₂`. -/
def v1 : V := ![0, 1, 0]
/-- `v₂ = e₁ − e₂`. -/
def v2 : V := ![1, -1, 0]
/-- `v₃ = e₁ + e₂ + e₃`. -/
def v3 : V := ![1, 1, 1]

/-- La familia `{v₁, v₂, v₃}` genera `V`. -/
lemma span_v : ⊤ ≤ Submodule.span ℝ (Set.range ![v1, v2, v3]) := by
  intro x _
  have hx : x = (x 0 + x 1 - 2 * x 2) • v1 + (x 0 - x 2) • v2 + x 2 • v3 := by
    funext i
    fin_cases i
    · simp [v1, v2, v3]
    · simp [v1, v2, v3]
      ring
    · simp [v1, v2, v3]
  rw [hx]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_ <;>
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩

/-- Una base conjugada `{v₁, v₂, v₃}` de `V` respecto de `Φ`. -/
noncomputable def conjBasis : Module.Basis (Fin 3) ℝ V :=
  basisOfTopLeSpanOfCardEqFinrank ![v1, v2, v3] span_v (by simp)

@[simp] lemma coe_conjBasis : ⇑conjBasis = ![v1, v2, v3] :=
  coe_basisOfTopLeSpanOfCardEqFinrank _ _ _

/-- La base `{v₁, v₂, v₃}` es conjugada respecto de `Φ`: los vectores son
`Ψ`-ortogonales dos a dos. -/
theorem conjBasis_conjugate : Psi v1 v2 = 0 ∧ Psi v1 v3 = 0 ∧ Psi v2 v3 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [Psi_apply, v1, v2, v3, Matrix.cons_val_two, Matrix.tail_cons]

/-- La matriz de `Φ` en la base conjugada es `diag(1, −1, 0)`. -/
theorem conjBasis_matrix :
    Psi v1 v1 = 1 ∧ Psi v2 v2 = -1 ∧ Psi v3 v3 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [Psi_apply, v1, v2, v3, Matrix.cons_val_two, Matrix.tail_cons]

/-- En las coordenadas `(y₁, y₂, y₃)` respecto de la base conjugada,
`Φ(y₁v₁ + y₂v₂ + y₃v₃) = y₁² − y₂²`. -/
theorem Phi_conjBasis (y : V) :
    Phi (y 0 • v1 + y 1 • v2 + y 2 • v3) = (y 0) ^ 2 - (y 1) ^ 2 := by
  simp [Phi, v1, v2, v3, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- La matriz de cambio de base `P` (sus columnas son `v₁, v₂, v₃`) es invertible. -/
theorem P_det : (!![0, 1, 1; 1, -1, 1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℝ).det = -1 := by
  simp [Matrix.det_fin_three]

/-- Congruencia: `Pᵀ M P = diag(1, −1, 0)`. -/
theorem congr_diagonal :
    (!![0, 1, 1; 1, -1, 1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℝ).transpose * M
        * !![0, 1, 1; 1, -1, 1; 0, 0, 1] = Matrix.diagonal ![1, -1, 0] := by
  have ht : (!![0, 1, 1; 1, -1, 1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℝ).transpose
      = !![0, 1, 0; 1, -1, 0; 1, 1, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hd : (Matrix.diagonal ![(1 : ℝ), -1, 0]) = !![1, 0, 0; 0, -1, 0; 0, 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  rw [ht, hd, M, Matrix.mul_fin_three, Matrix.mul_fin_three]
  norm_num

/-! ## b) Clasificación -/

/-- `Φ` es indefinida: toma valores estrictamente positivos y estrictamente negativos. -/
theorem Phi_indefinite : (∃ x : V, 0 < Phi x) ∧ (∃ x : V, Phi x < 0) := by
  constructor
  · exact ⟨v1, by norm_num [Phi, v1, Matrix.cons_val_two, Matrix.tail_cons]⟩
  · exact ⟨v2, by norm_num [Phi, v2, Matrix.cons_val_two, Matrix.tail_cons]⟩

/-- `Φ` es degenerada: el determinante de su matriz es nulo. -/
theorem Phi_degenerate : M.det = 0 := by
  norm_num [M, Matrix.det_fin_three, Matrix.cons_val_two, Matrix.tail_cons]

/-! ## c) Núcleo -/

/-- El núcleo (radical) de la forma cuadrática. -/
def kerPhi : Submodule ℝ V where
  carrier := {x : V | ∀ y : V, Psi x y = 0}
  zero_mem' := by intro y; simp [Psi_apply]
  add_mem' := by
    intro a b ha hb y
    have := ha y; have := hb y
    simp only [Set.mem_ofPred_eq, Psi_apply, Pi.add_apply] at *
    linarith
  smul_mem' := by
    intro c a ha y
    have := ha y
    simp only [Set.mem_ofPred_eq, Psi_apply, Pi.smul_apply, smul_eq_mul] at *
    linear_combination c * this

/-- El núcleo de `Φ` es la recta generada por `v₃ = e₁ + e₂ + e₃`, es decir,
`{(α, α, α) : α ∈ ℝ}`. -/
theorem kerPhi_eq : (kerPhi : Set V) = {x : V | ∃ a : ℝ, x = a • v3} := by
  ext x
  constructor
  · intro hx
    have h0 := hx ![1, 0, 0]
    have h1 := hx ![0, 1, 0]
    have h2 := hx ![0, 0, 1]
    simp [Psi_apply, Matrix.cons_val_two, Matrix.tail_cons] at h0 h1 h2
    refine ⟨x 2, ?_⟩
    funext i
    fin_cases i <;> simp [v3] <;> linarith
  · rintro ⟨a, rfl⟩ y
    simp [Psi_apply, v3]
    ring

/-- El núcleo de `Φ` es el subespacio generado por `v₃ = e₁ + e₂ + e₃`. -/
theorem kerPhi_eq_span : kerPhi = Submodule.span ℝ {v3} := by
  apply SetLike.ext'
  rw [kerPhi_eq]
  ext x
  simp [Submodule.mem_span_singleton, eq_comm]

/-- El núcleo de `Φ` tiene dimensión 1. -/
theorem finrank_kerPhi : Module.finrank ℝ kerPhi = 1 := by
  rw [kerPhi_eq_span, finrank_span_singleton]
  intro h
  have := congrFun h 0
  simp [v3] at this

/-! ## d) Subespacio conjugado de `L : x₁ − x₂ = 0` -/

/-- El subespacio `L` de ecuación implícita `x₁ − x₂ = 0`. -/
def L : Submodule ℝ V where
  carrier := {x : V | x 0 - x 1 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Pi.add_apply] at *
    linarith
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul] at *
    linear_combination c * ha

/-- El subespacio conjugado de un subconjunto `S` respecto de `Φ`. -/
def conjOf (S : Set V) : Submodule ℝ V where
  carrier := {x : V | ∀ u ∈ S, Psi x u = 0}
  zero_mem' := by intro u _; simp [Psi_apply]
  add_mem' := by
    intro a b ha hb u hu
    have := ha u hu; have := hb u hu
    simp only [Set.mem_ofPred_eq, Psi_apply, Pi.add_apply] at *
    linarith
  smul_mem' := by
    intro c a ha u hu
    have := ha u hu
    simp only [Set.mem_ofPred_eq, Psi_apply, Pi.smul_apply, smul_eq_mul] at *
    linear_combination c * this

/-- `L` está generado por `e₁ + e₂` y `e₃`. -/
theorem L_eq_span : (L : Set V) = (Submodule.span ℝ {![1, 1, 0], ![0, 0, 1]} : Submodule ℝ V) := by
  ext x
  simp only [SetLike.mem_coe, Submodule.mem_span_pair]
  constructor
  · intro hx
    have hx' : x 0 - x 1 = 0 := hx
    refine ⟨x 0, x 2, ?_⟩
    funext i
    fin_cases i
    · simp
    · simp
      linarith
    · simp
  · rintro ⟨m, n, rfl⟩
    show _ = _
    simp

/-- Ecuación implícita del subespacio conjugado de `L`. -/
theorem conjOf_L_eq_setOf :
    (conjOf (L : Set V) : Set V) = {x : V | x 0 + 2 * x 1 - 3 * x 2 = 0} := by
  ext x
  constructor
  · intro hx
    have h := hx ![1, 1, 0] (by show (1:ℝ) - 1 = 0; norm_num)
    simp [Psi_apply, Matrix.cons_val_two, Matrix.tail_cons] at h
    show x 0 + 2 * x 1 - 3 * x 2 = 0
    linarith
  · intro hx u hu
    have hx' : x 0 + 2 * x 1 - 3 * x 2 = 0 := hx
    have hu' : u 0 - u 1 = 0 := hu
    rw [Psi_apply]
    have : u 0 = u 1 := by linarith
    rw [this]
    linear_combination (u 1 - u 2) * hx'

/-- El subespacio conjugado de `L` está generado por `−2e₁ + e₂` y `3e₁ + e₃`. -/
theorem conjOf_L_eq_span :
    (conjOf (L : Set V) : Set V)
      = (Submodule.span ℝ {![-2, 1, 0], ![3, 0, 1]} : Submodule ℝ V) := by
  rw [conjOf_L_eq_setOf]
  ext x
  simp only [Set.mem_ofPred_eq, SetLike.mem_coe, Submodule.mem_span_pair]
  constructor
  · intro hx
    refine ⟨x 1, x 2, ?_⟩
    funext i
    fin_cases i
    · simp
      linarith
    · simp
    · simp
  · rintro ⟨m, n, rfl⟩
    simp [Matrix.cons_val_two, Matrix.tail_cons]
    ring

/-- Se tiene `L ∩ Lᶜ = Ker Φ`. -/
theorem L_inter_conj : L ⊓ conjOf (L : Set V) = kerPhi := by
  apply SetLike.ext'
  rw [Submodule.coe_inf, kerPhi_eq, conjOf_L_eq_setOf]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, SetLike.mem_coe]
  constructor
  · rintro ⟨h1, h2⟩
    have h1' : x 0 - x 1 = 0 := h1
    refine ⟨x 2, ?_⟩
    funext i
    fin_cases i
    · simp [v3]
      linarith
    · simp [v3]
      linarith
    · simp [v3]
  · rintro ⟨a, rfl⟩
    refine ⟨?_, ?_⟩
    · show (a • v3) 0 - (a • v3) 1 = 0
      simp [v3]
    · show (a • v3) 0 + 2 * (a • v3) 1 - 3 * (a • v3) 2 = 0
      simp [v3]
      ring

end Retos15022024
