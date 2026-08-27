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
# Retos Matemáticos, 19 de enero de 2025
**Ejercicio.** En un sistema de numeración de base desconocida se cumple que
`(xx)² = yyzz`, con `y = x - 1` y `z = y - 1`, siendo `x`, `y`, `z` dígitos
desconocidos. ¿Cuál es la base de dicho sistema de numeración?
**Respuesta.** La base es `8`, con `x = 6`, `y = 5`, `z = 4`, es decir
`(66₍₈₎)² = 5544₍₈₎`.
Los números escritos en base `t` se representan aquí mediante `Nat.ofDigits`,
que recibe la lista de dígitos en orden *little-endian*: así `Nat.ofDigits t [x, x]`
es el número `xx` en base `t`, y `Nat.ofDigits t [z, z, y, y]` es `yyzz` en base `t`.
-/
namespace RetosMatematicos
/-- Núcleo aritmético del problema: si `t` es una base en la que los dígitos
`z`, `z + 1`, `z + 2` cumplen la ecuación `(xx)² = yyzz` (con `x = z + 2`,
`y = z + 1`), entonces `t = 8` y `z = 4`. -/
theorem base_core (t z : ℕ) (hx : z + 1 + 1 < t)
    (heq : (z + 1 + 1 + t * (z + 1 + 1)) ^ 2 = z + t * (z + t * (z + 1 + t * (z + 1)))) :
    t = 8 ∧ z = 4 := by
  -- Dividiendo entre `t + 1`: `x²(t+1) = y t² + z`.
  have key : (z + 2) ^ 2 * (t + 1) = (z + 1) * t ^ 2 + z := by
    have h1 : ((z + 2) ^ 2 * (t + 1)) * (t + 1) = ((z + 1) * t ^ 2 + z) * (t + 1) := by
      rw [show ((z + 2) ^ 2 * (t + 1)) * (t + 1) = (z + 1 + 1 + t * (z + 1 + 1)) ^ 2 by ring, heq]
      ring
    exact Nat.eq_of_mul_eq_mul_right (by omega) h1
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
  -- Módulo `t + 1 = u + 2` la ecuación dice que `t + 1` divide a `2z + 1`.
  have heq2 : (z + 2) ^ 2 * (u + 2) = (2 * z + 1) + ((z + 1) * u) * (u + 2) := by rw [key]; ring
  have h2 : (z + 2) ^ 2 * (u + 2) - ((z + 1) * u) * (u + 2) = 2 * z + 1 := by omega
  have hdvd : (u + 2) ∣ (2 * z + 1) := by
    rw [← h2]
    exact Nat.dvd_sub (dvd_mul_left _ _) (dvd_mul_left _ _)
  obtain ⟨m, hm⟩ := hdvd
  -- Como `0 < 2z + 1 < 2(t + 1)`, forzosamente `2z + 1 = t + 1`, o sea `t = 2z`.
  have hm1 : m = 1 := by
    match m with
    | 0 => omega
    | 1 => rfl
    | (m + 2) => exfalso; nlinarith [hm]
  subst hm1
  obtain ⟨c, rfl⟩ : ∃ c, z = c + 3 := ⟨z - 3, by omega⟩
  have hu : u = 2 * c + 5 := by omega
  subst hu
  -- Sustituyendo, `2c³ + 13c² + 13c = 28`, cuya única solución natural es `c = 1`.
  have hc : c ≤ 1 := by nlinarith [key]
  interval_cases c
  · simp at key
  · constructor <;> omega
/-- **Solución del reto.** Si `x`, `y`, `z` son dígitos de una base `t ≥ 2` con
`x = y + 1`, `y = z + 1`, entonces `(xx)₍t₎² = yyzz₍t₎` si y sólo si
`t = 8`, `x = 6`, `y = 5` y `z = 4`. -/
theorem base_iff (t x y z : ℕ) (ht : 2 ≤ t) (hx : x < t) (hy : y < t) (hz : z < t)
    (hxy : x = y + 1) (hyz : y = z + 1) :
    Nat.ofDigits t [x, x] ^ 2 = Nat.ofDigits t [z, z, y, y] ↔
      (t = 8 ∧ x = 6 ∧ y = 5 ∧ z = 4) := by
  subst hxy; subst hyz
  constructor
  · intro heq
    simp [Nat.ofDigits] at heq
    obtain ⟨ht8, hz4⟩ := base_core t z (by omega) heq
    exact ⟨ht8, by omega, by omega, hz4⟩
  · rintro ⟨rfl, -, -, rfl⟩
    simp [Nat.ofDigits]
/-- Comprobación: en base `8` se cumple `(66)² = 5544`. -/
theorem sixtysix_sq_base_eight :
    Nat.ofDigits 8 [6, 6] ^ 2 = Nat.ofDigits 8 [4, 4, 5, 5] := by
  simp [Nat.ofDigits]
end RetosMatematicos
