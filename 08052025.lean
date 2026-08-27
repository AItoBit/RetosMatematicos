import Mathlib

/-!
# Retos Matemáticos: Problema 21 Canguro 2025 (2º Bachillerato)

Ejercicio: Se empieza con dos números en la pizarra. En cada paso se borran y se
escriben su suma y su diferencia positiva. Si se empieza con 5 y 3 y se repite
el proceso 50 veces, ¿cuáles son los números finales?
-/

/-- Operación en la pizarra: suma y diferencia positiva de la pareja (a, b) con a ≥ b. -/
def step (p : ℕ × ℕ) : ℕ × ℕ :=
  (p.1 + p.2, p.1 - p.2)

/-- Lema fundamental: Tras 2 pasos consecutivos, ambos números se duplican exactamente:
    (a, b) ↦ (a + b, a - b) ↦ (2a, 2b). -/
theorem step_two (a b : ℕ) (h : b ≤ a) :
    step (step (a, b)) = (2 * a, 2 * b) := by
  dsimp [step]
  ext <;> omega

/-- Teorema general: Al cabo de 2n pasos, el estado resultante es (2ⁿ · a, 2ⁿ · b). -/
theorem step_iter_two_mul (n : ℕ) (a b : ℕ) (h : b ≤ a) :
    (step^[2 * n]) (a, b) = (2 ^ n * a, 2 ^ n * b) := by
  induction n with
  | zero =>
    -- Caso base 2 * 0 = 0 pasos:
    simp
  | succ n ih =>
    -- Caso inductivo 2(n + 1) = 2 + 2n pasos:
    rw [show 2 * (n + 1) = 2 + 2 * n by omega]
    rw [Function.iterate_add_apply, ih]
    have h_le : 2 ^ n * b ≤ 2 ^ n * a := Nat.mul_le_mul_left (2 ^ n) h
    -- Aplicamos el lema de los dos pasos a (2ⁿa, 2ⁿb):
    change step (step (2 ^ n * a, 2 ^ n * b)) = _
    rw [step_two (2 ^ n * a) (2 ^ n * b) h_le]
    ext
    · rw [pow_succ']; ring
    · rw [pow_succ']; ring

/-- Teorema específico: Partiendo de (5, 3), tras 50 pasos (2 · 25 pasos),
    se obtienen 2²⁵ · 5 = 167772160 y 2²⁵ · 3 = 100663296. -/
theorem canguro_2025_solution :
    (step^[50]) (5, 3) = (167772160, 100663296) := by
  -- Aplicamos el teorema general con n = 25:
  have h := step_iter_two_mul 25 5 3 (by decide)
  rw [h]
  decide

/-! ### Comprobación computacional directa por evaluación -/

#eval (step^[50]) (5, 3)
-- Resultado: (167772160, 100663296)
