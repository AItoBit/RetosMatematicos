import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

/-!
# Reto Matemático: Tres últimos dígitos de 75^(88^101)

Demostramos formalmente que:
  75 ^ (88 ^ 101) ≡ 625 [MOD 1000]
-/

/-- Lema base: 625^(m+1) ≡ 625 [MOD 1000] para todo m : ℕ por inducción simple. -/
lemma pow_625_succ_modeq_1000 (m : ℕ) : 625 ^ (m + 1) ≡ 625 [MOD 1000] := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ 625 (m + 1)]
    have h1 : 625 ^ (m + 1) * 625 ≡ 625 * 625 [MOD 1000] := Nat.ModEq.mul_right 625 ih
    have h2 : 625 * 625 ≡ 625 [MOD 1000] := by decide
    exact Nat.ModEq.trans h1 h2

/-- Lema 1: 625 es idempotente módulo 1000 para todo exponente k ≥ 1. -/
lemma pow_625_modeq_1000 (k : ℕ) (hk : 1 ≤ k) : 625 ^ k ≡ 625 [MOD 1000] := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk)
  exact pow_625_succ_modeq_1000 m

/-- Lema 2: Cualquier potencia par de 75 (mayor que 0) es congruente con 625 mod 1000. -/
lemma pow_75_even_modeq_1000 (m : ℕ) (hm : 1 ≤ m) : 75 ^ (2 * m) ≡ 625 [MOD 1000] := by
  rw [pow_mul 75 2 m]
  have h_base : 75 ^ 2 ≡ 625 [MOD 1000] := by decide
  have h_pow : (75 ^ 2) ^ m ≡ 625 ^ m [MOD 1000] := Nat.ModEq.pow m h_base
  exact Nat.ModEq.trans h_pow (pow_625_modeq_1000 m hm)

/-- Teorema Principal: Los tres últimos dígitos de 75^(88^101) son 625. -/
theorem tres_ultimos_digitos_75_pow_88_pow_101 :
    75 ^ (88 ^ 101) ≡ 625 [MOD 1000] := by
  have h_exp : 88 ^ 101 = 2 * (44 * 88 ^ 100) := by
    change 88 ^ (1 + 100) = 2 * (44 * 88 ^ 100)
    rw [pow_add, pow_one]
    ring
  rw [h_exp]
  have hm_pos : 1 ≤ 44 * 88 ^ 100 := by
    apply Nat.succ_le_of_lt
    positivity
  exact pow_75_even_modeq_1000 (44 * 88 ^ 100) hm_pos

/-- Expresado directamente mediante la operación módulo (% 1000 = 625). -/
theorem tres_ultimos_digitos_mod :
    75 ^ (88 ^ 101) % 1000 = 625 := by
  exact tres_ultimos_digitos_75_pow_88_pow_101

/-!
### Generalización a las 4 últimas cifras (Páginas 5-6 del PDF)
75^(88^101) ≡ 0625 [MOD 10000]
-/

/-- Lema base para módulo 10000. -/
lemma pow_625_succ_modeq_10000 (m : ℕ) : 625 ^ (m + 1) ≡ 625 [MOD 10000] := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ 625 (m + 1)]
    have h1 : 625 ^ (m + 1) * 625 ≡ 625 * 625 [MOD 10000] := Nat.ModEq.mul_right 625 ih
    have h2 : 625 * 625 ≡ 625 [MOD 10000] := by decide
    exact Nat.ModEq.trans h1 h2

lemma pow_625_modeq_10000 (k : ℕ) (hk : 1 ≤ k) : 625 ^ k ≡ 625 [MOD 10000] := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk)
  exact pow_625_succ_modeq_10000 m

/-- Cuatro últimas cifras: 75^(88^101) % 10000 = 625 (es decir, ...0625). -/
theorem cuatro_ultimos_digitos_mod :
    75 ^ (88 ^ 101) % 10000 = 625 := by
  have h_exp : 88 ^ 101 = 4 * (22 * 88 ^ 100) := by
    change 88 ^ (1 + 100) = 4 * (22 * 88 ^ 100)
    rw [pow_add, pow_one]
    ring
  rw [h_exp, pow_mul 75 4 (22 * 88 ^ 100)]
  have h_base : 75 ^ 4 ≡ 625 [MOD 10000] := by decide
  have h_pow : (75 ^ 4) ^ (22 * 88 ^ 100) ≡ 625 ^ (22 * 88 ^ 100) [MOD 10000] :=
    Nat.ModEq.pow (22 * 88 ^ 100) h_base
  have hm_pos : 1 ≤ 22 * 88 ^ 100 := by
    apply Nat.succ_le_of_lt
    positivity
  exact Nat.ModEq.trans h_pow (pow_625_modeq_10000 (22 * 88 ^ 100) hm_pos)
