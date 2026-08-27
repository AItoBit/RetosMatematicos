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
# Retos Matemáticos, 31 de marzo de 2023

**Ejercicio.** Obténgase el conjunto de soluciones naturales de la expresión
`(x + y + z)^2 / (x*y*z)` con `x, y, z ∈ ℕ` (positivos).

**Solución.** El conjunto buscado es `{1, 2, 3, 4, 5, 6, 8, 9}`.
-/

namespace RetosMatematicos31032023

/-- Conjunto de los valores naturales que toma `(x+y+z)^2 / (x*y*z)`
para `x, y, z` naturales positivos. -/
def solutionSet : Set ℕ :=
  {n : ℕ | ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ (x + y + z) ^ 2 = n * (x * y * z)}

/-- Toda terna se puede ordenar conservando suma y producto. -/
lemma sort3 (x y z : ℕ) :
    ∃ a b c : ℕ, a ≤ b ∧ b ≤ c ∧ a + b + c = x + y + z ∧ a * b * c = x * y * z := by
  rcases le_total x y with h1 | h1 <;> rcases le_total y z with h2 | h2 <;>
      rcases le_total x z with h3 | h3 <;>
    first
      | exact ⟨x, y, z, by omega, by omega, by ring, by ring⟩
      | exact ⟨x, z, y, by omega, by omega, by ring, by ring⟩
      | exact ⟨y, x, z, by omega, by omega, by ring, by ring⟩
      | exact ⟨y, z, x, by omega, by omega, by ring, by ring⟩
      | exact ⟨z, x, y, by omega, by omega, by ring, by ring⟩
      | exact ⟨z, y, x, by omega, by omega, by ring, by ring⟩

/-- Descenso (salto de Vieta): a partir de cualquier solución se obtiene una solución
ordenada `a ≤ b ≤ c` con `c ≤ a + b`, para el mismo valor de `n`. -/
lemma descent (n : ℕ) : ∀ s x y z : ℕ, x + y + z = s → 0 < x → 0 < y → 0 < z →
    (x + y + z) ^ 2 = n * (x * y * z) →
    ∃ a b c : ℕ, 0 < a ∧ a ≤ b ∧ b ≤ c ∧ c ≤ a + b ∧ (a + b + c) ^ 2 = n * (a * b * c) := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro x y z hs hx hy hz h
    obtain ⟨a, b, c, hab, hbc, hsum, hprod⟩ := sort3 x y z
    have h' : (a + b + c) ^ 2 = n * (a * b * c) := by rw [hsum, hprod]; exact h
    have hpos : 0 < a * b * c := by rw [hprod]; positivity
    have ha : 0 < a := by rcases Nat.eq_zero_or_pos a with rfl | h1; · simp at hpos
                          · exact h1
    have hb : 0 < b := lt_of_lt_of_le ha hab
    have hc : 0 < c := lt_of_lt_of_le hb hbc
    by_cases hcab : c ≤ a + b
    · exact ⟨a, b, c, ha, hab, hbc, hcab, h'⟩
    · push Not at hcab
      have key : (a + b) ^ 2 + (2 * (a + b) * c + c ^ 2) = n * (a * b * c) := by
        rw [← h']; ring
      have hdvd : c ∣ (a + b) ^ 2 := by
        have h1 : c ∣ 2 * (a + b) * c + c ^ 2 := ⟨2 * (a + b) + c, by ring⟩
        have h2 : c ∣ (a + b) ^ 2 + (2 * (a + b) * c + c ^ 2) := ⟨n * (a * b), by rw [key]; ring⟩
        simpa using Nat.dvd_sub h2 h1
      obtain ⟨d, hd⟩ := hdvd
      have hdpos : 0 < d := by
        rcases Nat.eq_zero_or_pos d with rfl | h1
        · simp at hd; omega
        · exact h1
      have hdc : d < c := by nlinarith
      have hn : n * (a * b) = d + 2 * (a + b) + c := by
        have hmul : c * (n * (a * b)) = c * (d + 2 * (a + b) + c) := by
          rw [hd] at key; nlinarith [key]
        exact Nat.eq_of_mul_eq_mul_left hc hmul
      have hnew : (a + b + d) ^ 2 = n * (a * b * d) := by
        have e1 : (a + b + d) ^ 2 = (a + b) ^ 2 + (2 * (a + b) * d + d ^ 2) := by ring
        rw [e1, hd, show n * (a * b * d) = (n * (a * b)) * d from by ring, hn]; ring
      exact ih (a + b + d) (by omega) a b d rfl ha hb hdpos hnew

/-- Para una solución ordenada con `c ≤ a + b`, el valor de `n` está en `{1,…,6,8,9}`. -/
lemma bound {n a b c : ℕ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) (hc : c ≤ a + b)
    (h : (a + b + c) ^ 2 = n * (a * b * c)) :
    n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 8 ∨ n = 9 := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hcpos : 0 < c := lt_of_lt_of_le hb hbc
  have hn0 : n ≠ 0 := by rintro rfl; simp at h; omega
  have hna : n * a ≤ 12 := by
    have h1 : n * a * (b * c) ≤ 12 * (b * c) := by nlinarith
    exact Nat.le_of_mul_le_mul_right h1 (by positivity)
  rcases Nat.lt_or_ge a 2 with h1 | h1
  · -- a = 1
    have ha1 : a = 1 := by omega
    subst ha1
    have hcases : c = b ∨ c = b + 1 := by omega
    rcases hcases with rfl | rfl
    · have hdb : c ∣ 1 := by
        have e : n * (1 * c * c) = (4 * c * c + 4 * c) + 1 := by rw [← h]; ring
        have h2 : c ∣ n * (1 * c * c) := ⟨n * c, by ring⟩
        have h3 : c ∣ 4 * c * c + 4 * c := ⟨4 * c + 4, by ring⟩
        rw [e] at h2
        simpa using Nat.dvd_sub h2 h3
      have hc1 : c = 1 := Nat.dvd_one.mp hdb
      subst hc1
      simp at h
      omega
    · have e2 : 4 * (b + 1) = n * b := by
        have hmul : (b + 1) * (4 * (b + 1)) = (b + 1) * (n * b) := by nlinarith [h]
        exact Nat.eq_of_mul_eq_mul_left (by omega) hmul
      have hb4 : b ∣ 4 := by
        have h2 : b ∣ n * b := ⟨n, by ring⟩
        rw [← e2] at h2
        have h3 : b ∣ 4 * b := ⟨4, by ring⟩
        have := Nat.dvd_sub h2 h3
        simpa [Nat.mul_add] using this
      have hble : b ≤ 4 := Nat.le_of_dvd (by norm_num) hb4
      interval_cases b <;> omega
  · -- a ≥ 2
    have : n * 2 ≤ n * a := Nat.mul_le_mul_left n h1
    omega

/-- **Solución del ejercicio**: el conjunto de valores naturales de `(x+y+z)^2/(x*y*z)`
es exactamente `{1, 2, 3, 4, 5, 6, 8, 9}`. -/
theorem solutionSet_eq : solutionSet = {1, 2, 3, 4, 5, 6, 8, 9} := by
  ext n
  constructor
  · rintro ⟨x, y, z, hx, hy, hz, h⟩
    obtain ⟨a, b, c, ha, hab, hbc, hc, h'⟩ := descent n (x + y + z) x y z rfl hx hy hz h
    have := bound ha hab hbc hc h'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  · intro hn
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨9, 9, 9, by norm_num⟩
    · exact ⟨4, 4, 8, by norm_num⟩
    · exact ⟨3, 3, 3, by norm_num⟩
    · exact ⟨2, 2, 4, by norm_num⟩
    · exact ⟨1, 4, 5, by norm_num⟩
    · exact ⟨1, 2, 3, by norm_num⟩
    · exact ⟨1, 1, 2, by norm_num⟩
    · exact ⟨1, 1, 1, by norm_num⟩

end RetosMatematicos31032023
