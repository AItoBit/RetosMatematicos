import Mathlib

/-!
# Reto Matemático: Ecuación diofántica y puntos en el interior de una circunferencia
(Pruebas de Madurez, Curso Preuniversitario, España 1968)

Problema:
  Dada la ecuación diofántica $7x - 12y = 13$:
  a) Hallar todas sus soluciones en $\mathbb{Z}$.
  b) Determinar los puntos enteros solución que quedan en el interior de la
     circunferencia de centro $(10, 10)$ y tangente a los ejes (radio 10).
-/

/-- Predicado de pertenencia al conjunto de soluciones de la ecuación diofántica. -/
def IsDiofantineSol (x y : ℤ) : Prop :=
  7 * x - 12 * y = 13

/-- Interior del círculo de centro (10, 10) y radio 10. -/
def InsideCircle (x y : ℤ) : Prop :=
  (x - 10) ^ 2 + (y - 10) ^ 2 < 100

/-! ## Apartado a: Solución general de la ecuación diofántica -/

theorem diofantine_solutions (x y : ℤ) :
    IsDiofantineSol x y ↔ ∃ k : ℤ, x = 7 + 12 * k ∧ y = 3 + 7 * k := by
  constructor
  · intro h
    dsimp [IsDiofantineSol] at h
    -- Proporcionamos el parámetro entero k derivado de los coeficientes de Bézout
    use 3 * x - 5 * y - 6
    omega
  · rintro ⟨k, rfl, rfl⟩
    dsimp [IsDiofantineSol]
    ring

/-! ## Apartado b: Puntos enteros en el interior de la circunferencia -/

/-- Lema auxiliar: la inecuación cuadrática solo admite k = 0 o k = 1. -/
lemma k_bound_of_inside {k : ℤ} (h : (12 * k - 3) ^ 2 + (7 * k - 7) ^ 2 < 100) :
    k = 0 ∨ k = 1 := by
  rcases lt_or_ge k 0 with hk_neg | hk_nonneg
  · -- Si k ≤ -1, entonces (7k - 7) ≤ -14, luego (7k - 7)² ≥ 196 > 100 (contradicción)
    have h1 : 7 * k - 7 ≤ -14 := by omega
    have h2 : (7 * k - 7) ^ 2 ≥ 196 := by
      have : 14 ≤ -(7 * k - 7) := by omega
      nlinarith
    nlinarith
  · rcases le_or_gt 2 k with hk_ge2 | hk_lt2
    · -- Si k ≥ 2, entonces (12k - 3) ≥ 21, luego (12k - 3)² ≥ 441 > 100 (contradicción)
      have h1 : 12 * k - 3 ≥ 21 := by omega
      have h2 : (12 * k - 3) ^ 2 ≥ 441 := by nlinarith
      nlinarith
    · -- Por tanto, 0 ≤ k < 2, es decir, k = 0 ∨ k = 1
      omega

/--
Teorema Final: Los únicos puntos solución en el interior de la circunferencia
son B = (7, 3) y C = (19, 10).
-/
theorem solutions_inside_circle (x y : ℤ) :
    (IsDiofantineSol x y ∧ InsideCircle x y) ↔ (x = 7 ∧ y = 3) ∨ (x = 19 ∧ y = 10) := by
  constructor
  · rintro ⟨h_dio, h_circ⟩
    rw [diofantine_solutions] at h_dio
    rcases h_dio with ⟨k, rfl, rfl⟩
    dsimp [InsideCircle] at h_circ
    have hk_geom : (12 * k - 3) ^ 2 + (7 * k - 7) ^ 2 < 100 := by
      have hx : 7 + 12 * k - 10 = 12 * k - 3 := by ring
      have hy : 3 + 7 * k - 10 = 7 * k - 7 := by ring
      rw [hx, hy] at h_circ
      exact h_circ
    rcases k_bound_of_inside hk_geom with rfl | rfl
    · left; omega
    · right; omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · dsimp [IsDiofantineSol, InsideCircle]
      decide
    · dsimp [IsDiofantineSol, InsideCircle]
      decide
