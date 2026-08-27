import Mathlib

/-!
# Reto Matemático: Números de Lucas y el número áureo
14 de mayo de 2024
Propuesto por José Manuel Sánchez.

## Enunciado
Los números de Lucas, `L_n`, satisfacen la misma relación que los números de Fibonacci,
con la excepción de que `L₀ = 2`, `L₁ = 1`, `L₂ = 3`, etc.
Si llamamos `φ = (1 + √5) / 2` al número áureo:
a) Demuéstrese que `φ⁻ⁿ` es una de las raíces del polinomio:
   `P_n(x) = x² + ((-1)ⁿ⁺¹ L_n) x + (-1)ⁿ`
b) ¿Cuál es la otra raíz de dicho polinomio?
-/

namespace RetosLucas

/-! ### 1. Definiciones principales -/

/-- Definición inductiva de los números de Lucas. -/
def lucas : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas (n + 1) + lucas n

/-- Número áureo: φ = (1 + √5) / 2 -/
noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2

/-- Conjugado del número áureo: ψ = (1 - √5) / 2 -/
noncomputable def psi : ℝ := (1 - Real.sqrt 5) / 2

/-- Polinomio P_n(x) evaluado en un número real x. -/
noncomputable def P (n : ℕ) (x : ℝ) : ℝ :=
  x ^ 2 + ((-1 : ℝ) ^ (n + 1) * (lucas n : ℝ)) * x + (-1 : ℝ) ^ n

/-- Primera raíz propuesta: r₁ = φ⁻ⁿ = (φⁿ)⁻¹ -/
noncomputable def r1 (n : ℕ) : ℝ := (phi ^ n)⁻¹

/-- Segunda raíz propuesta: r₂ = (-1)ⁿ φⁿ = (-φ)ⁿ -/
noncomputable def r2 (n : ℕ) : ℝ := (-1 : ℝ) ^ n * phi ^ n


/-! ### 2. Propiedades algebraicas del número áureo -/

lemma sqrt5_sq : (Real.sqrt 5) ^ 2 = 5 :=
  Real.sq_sqrt (by norm_num)

lemma phi_sq : phi ^ 2 = phi + 1 := by
  unfold phi
  have h := sqrt5_sq
  nlinarith

lemma psi_sq : psi ^ 2 = psi + 1 := by
  unfold psi
  have h := sqrt5_sq
  nlinarith

lemma phi_ne_zero : phi ≠ 0 := by
  unfold phi
  have h : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  positivity

lemma phi_mul_psi : phi * psi = -1 := by
  unfold phi psi
  have h := sqrt5_sq
  nlinarith

lemma psi_eq_neg_inv_phi : psi = - (phi⁻¹) := by
  have h := phi_mul_psi
  have hphi := phi_ne_zero
  apply mul_left_cancel₀ hphi
  rw [h, mul_neg, mul_inv_cancel₀ hphi]

lemma psi_pow (n : ℕ) : psi ^ n = (-1 : ℝ) ^ n * (phi ^ n)⁻¹ := by
  have h : psi = -1 * phi⁻¹ := by
    calc
      psi = -(phi⁻¹) := psi_eq_neg_inv_phi
      _ = -1 * phi⁻¹ := by ring
  rw [h, mul_pow, inv_pow]


/-! ### 3. Fórmula de Binet para los números de Lucas -/

/-- Principio de inducción en 2 pasos para naturales. -/
lemma nat_two_step_induction {P : ℕ → Prop} (h0 : P 0) (h1 : P 1)
    (hrec : ∀ n, P n → P (n + 1) → P (n + 2)) (n : ℕ) : P n := by
  have H : ∀ k, P k ∧ P (k + 1) := by
    intro k
    induction k with
    | zero => exact ⟨h0, h1⟩
    | succ k ih => exact ⟨ih.2, hrec k ih.1 ih.2⟩
  exact (H n).1

/-- Fórmula de Binet: L_n = φⁿ + ψⁿ -/
theorem lucas_binet (n : ℕ) : (lucas n : ℝ) = phi ^ n + psi ^ n := by
  induction n using nat_two_step_induction with
  | h0 =>
    have h_L0 : (lucas 0 : ℝ) = 2 := by norm_num [lucas]
    rw [h_L0]
    ring
  | h1 =>
    have h_L1 : (lucas 1 : ℝ) = 1 := by norm_num [lucas]
    rw [h_L1]
    unfold phi psi
    ring
  | hrec n ih0 ih1 =>
    have h_phi_pow : phi ^ (n + 2) = phi ^ (n + 1) + phi ^ n := by
      calc
        phi ^ (n + 2) = phi ^ n * phi ^ 2 := by ring
        _ = phi ^ n * (phi + 1) := by rw [phi_sq]
        _ = phi ^ (n + 1) + phi ^ n := by ring

    have h_psi_pow : psi ^ (n + 2) = psi ^ (n + 1) + psi ^ n := by
      calc
        psi ^ (n + 2) = psi ^ n * psi ^ 2 := by ring
        _ = psi ^ n * (psi + 1) := by rw [psi_sq]
        _ = psi ^ (n + 1) + psi ^ n := by ring

    calc
      (lucas (n + 2) : ℝ) = ((lucas (n + 1) + lucas n : ℤ) : ℝ) := rfl
      _ = (lucas (n + 1) : ℝ) + (lucas n : ℝ) := by push_cast; rfl
      _ = (phi ^ (n + 1) + psi ^ (n + 1)) + (phi ^ n + psi ^ n) := by rw [ih0, ih1]
      _ = (phi ^ (n + 1) + phi ^ n) + (psi ^ (n + 1) + psi ^ n) := by ring
      _ = phi ^ (n + 2) + psi ^ (n + 2) := by rw [← h_phi_pow, ← h_psi_pow]


/-! ### 4. Relaciones de Cardano-Vieta y factorización -/

lemma neg_one_pow_mul_neg_one_pow (n : ℕ) : (-1 : ℝ) ^ (n + 1) * (-1 : ℝ) ^ n = -1 := by
  have h : (-1 : ℝ) ^ (n + 1) = - ((-1 : ℝ) ^ n) := by
    calc
      (-1 : ℝ) ^ (n + 1) = (-1 : ℝ) ^ n * (-1 : ℝ) ^ 1 := by rw [pow_add]
      _ = - ((-1 : ℝ) ^ n) := by ring
  rw [h]
  have h2 : ((-1 : ℝ) ^ n) * (-1 : ℝ) ^ n = ((-1 : ℝ) * (-1 : ℝ)) ^ n := (mul_pow (-1) (-1) n).symm
  have h3 : (-1 : ℝ) * (-1 : ℝ) = 1 := by norm_num
  rw [h3, one_pow] at h2
  linarith

/-- Producto de raíces: r₁ * r₂ = (-1)ⁿ -/
lemma root_mul (n : ℕ) : r1 n * r2 n = (-1 : ℝ) ^ n := by
  have hphi : phi ^ n ≠ 0 := pow_ne_zero n phi_ne_zero
  unfold r1 r2
  calc
    (phi ^ n)⁻¹ * ((-1 : ℝ) ^ n * phi ^ n) = (-1 : ℝ) ^ n * ((phi ^ n)⁻¹ * phi ^ n) := by ring
    _ = (-1 : ℝ) ^ n * 1 := by rw [inv_mul_cancel₀ hphi]
    _ = (-1 : ℝ) ^ n := by ring

/-- Coeficiente lineal: (-1)ⁿ⁺¹ L_n = -(r₁ + r₂) -/
lemma coeff_x (n : ℕ) :
    (-1 : ℝ) ^ (n + 1) * (lucas n : ℝ) = - (r1 n + r2 n) := by
  rw [lucas_binet, psi_pow]
  have h_neg := neg_one_pow_mul_neg_one_pow n
  have h_step : (-1 : ℝ) ^ (n + 1) = - ((-1 : ℝ) ^ n) := by
    calc
      (-1 : ℝ) ^ (n + 1) = (-1 : ℝ) ^ n * (-1 : ℝ) ^ 1 := by rw [pow_add]
      _ = - ((-1 : ℝ) ^ n) := by ring
  unfold r1 r2
  calc
    (-1 : ℝ) ^ (n + 1) * (phi ^ n + (-1 : ℝ) ^ n * (phi ^ n)⁻¹)
      = (-1 : ℝ) ^ (n + 1) * phi ^ n + ((-1 : ℝ) ^ (n + 1) * (-1 : ℝ) ^ n) * (phi ^ n)⁻¹ := by ring
    _ = (-1 : ℝ) ^ (n + 1) * phi ^ n + (-1) * (phi ^ n)⁻¹ := by rw [h_neg]
    _ = - ((-1 : ℝ) ^ n) * phi ^ n - (phi ^ n)⁻¹ := by rw [h_step]; ring
    _ = - ((phi ^ n)⁻¹ + (-1 : ℝ) ^ n * phi ^ n) := by ring

/-- Factorización completa: P_n(x) = (x - r₁)(x - r₂) -/
theorem P_factorization (n : ℕ) (x : ℝ) :
    P n x = (x - r1 n) * (x - r2 n) := by
  unfold P
  rw [coeff_x, ← root_mul]
  ring


/-! ### 5. Solución a los apartados del reto -/

/-- Relación entre (-φ)ⁿ y r₂ = (-1)ⁿ φⁿ. -/
lemma neg_phi_pow (n : ℕ) : (-phi) ^ n = r2 n := by
  unfold r2
  calc
    (-phi) ^ n = (-1 * phi) ^ n := by ring_nf
    _ = (-1 : ℝ) ^ n * phi ^ n := mul_pow (-1) phi n

/--
**Apartado a**:
`φ⁻ⁿ` es raíz del polinomio `P_n(x) = x² + ((-1)ⁿ⁺¹ L_n) x + (-1)ⁿ`.
-/
theorem reto_apartado_a (n : ℕ) : P n (r1 n) = 0 := by
  rw [P_factorization]
  ring

/--
**Apartado b**:
La otra raíz del polinomio `P_n(x)` es `(-φ)ⁿ = (-1)ⁿ φⁿ`.
-/
theorem reto_apartado_b (n : ℕ) : P n ((-phi) ^ n) = 0 := by
  rw [neg_phi_pow, P_factorization]
  ring

end RetosLucas
