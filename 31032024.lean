import Mathlib

/-!
# Reto Matemático: Primos y polinomios cuadráticos/cúbicos
31 de marzo de 2024
Propuesto por Francisco Javier García Capitán.

## Enunciado
Dado un número primo `p`, tal que `p² + 2` es primo también, demuéstrese que
`p³ + 2` también es primo.
-/

namespace RetosMatematicos

/-! ### 1. Lema auxiliar (2ª Forma): Primos módulo 6 -/

/--
**Lema**: Cualquier número primo `p > 3` es congruente con `1` o con `5` módulo `6`
(es decir, `p ≡ ±1 (mód 6)`).
-/
lemma prime_mod_six (p : ℕ) (hp : Nat.Prime p) (hp_gt_3 : 3 < p) :
    p % 6 = 1 ∨ p % 6 = 5 := by
  have h_rem : p % 6 < 6 := Nat.mod_lt p (by decide)
  interval_cases h : p % 6
  · -- Resto 0: 6 ∣ p, luego 2 ∣ p
    have h6 : 6 ∣ p := Nat.dvd_of_mod_eq_zero h
    have hdvd : 2 ∣ p := dvd_trans (by decide) h6
    have hp2 : p = 2 := ((Nat.dvd_prime hp).mp hdvd).resolve_left (by decide) |>.symm
    omega
  · -- Resto 1: Válido (p ≡ 1 mód 6)
    exact Or.inl rfl
  · -- Resto 2: 2 ∣ p
    obtain ⟨k, hk⟩ : ∃ k, p = 6 * k + 2 := ⟨p / 6, by omega⟩
    have hdvd : 2 ∣ p := ⟨3 * k + 1, by rw [hk]; ring⟩
    have hp2 : p = 2 := ((Nat.dvd_prime hp).mp hdvd).resolve_left (by decide) |>.symm
    omega
  · -- Resto 3: 3 ∣ p
    obtain ⟨k, hk⟩ : ∃ k, p = 6 * k + 3 := ⟨p / 6, by omega⟩
    have hdvd : 3 ∣ p := ⟨2 * k + 1, by rw [hk]; ring⟩
    have hp3 : p = 3 := ((Nat.dvd_prime hp).mp hdvd).resolve_left (by decide) |>.symm
    omega
  · -- Resto 4: 2 ∣ p
    obtain ⟨k, hk⟩ : ∃ k, p = 6 * k + 4 := ⟨p / 6, by omega⟩
    have hdvd : 2 ∣ p := ⟨3 * k + 2, by rw [hk]; ring⟩
    have hp2 : p = 2 := ((Nat.dvd_prime hp).mp hdvd).resolve_left (by decide) |>.symm
    omega
  · -- Resto 5: Válido (p ≡ 5 ≡ -1 mód 6)
    exact Or.inr rfl


/-! ### 2. Teorema Principal -/

/--
**Teorema**: Dado un número primo `p`, si `p² + 2` es primo, entonces `p³ + 2`
es también primo.
-/
theorem reto_prime_cubed_add_two (p : ℕ) (hp : Nat.Prime p) (hp2 : Nat.Prime (p ^ 2 + 2)) :
    Nat.Prime (p ^ 3 + 2) := by
  have hmod : p % 3 < 3 := Nat.mod_lt p (by decide)
  interval_cases h : p % 3
  · -- Caso 1: p % 3 = 0 → 3 ∣ p → p = 3
    have h3_dvd_p : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
    have hp_eq_3 : p = 3 := ((Nat.dvd_prime hp).mp h3_dvd_p).resolve_left (by decide) |>.symm
    subst hp_eq_3
    decide

  · -- Caso 2: p % 3 = 1 → 3 ∣ p² + 2 → p² + 2 = 3 → p = 1 (Contradicción con p primo)
    obtain ⟨k, hk⟩ : ∃ k, p = 3 * k + 1 := ⟨p / 3, by omega⟩
    have hdvd : 3 ∣ p ^ 2 + 2 := ⟨3 * k ^ 2 + 2 * k + 1, by rw [hk]; ring⟩
    have h_eq : p ^ 2 + 2 = 3 :=
      ((Nat.dvd_prime hp2).mp hdvd).resolve_left (by decide) |>.symm
    have hp_lt_2 : p < 2 := by nlinarith [h_eq]
    interval_cases p
    · omega
    · exact False.elim (hp.ne_one rfl)

  · -- Caso 3: p % 3 = 2 → 3 ∣ p² + 2 → p² + 2 = 3 → p = 1 (Contradicción con p primo)
    obtain ⟨k, hk⟩ : ∃ k, p = 3 * k + 2 := ⟨p / 3, by omega⟩
    have hdvd : 3 ∣ p ^ 2 + 2 := ⟨3 * k ^ 2 + 4 * k + 2, by rw [hk]; ring⟩
    have h_eq : p ^ 2 + 2 = 3 :=
      ((Nat.dvd_prime hp2).mp hdvd).resolve_left (by decide) |>.symm
    have hp_lt_2 : p < 2 := by nlinarith [h_eq]
    interval_cases p
    · omega
    · exact False.elim (hp.ne_one rfl)

end RetosMatematicos
