import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Tactic

open Polynomial

/--
Si un polinomio con coeficientes reales se descompone completamente
sobre ℝ, entonces su derivada también se descompone completamente
sobre ℝ.

Esto equivale a afirmar que, si todas las raíces de `P` son reales,
todas las raíces de `P.derivative` también son reales.
-/
theorem derivative_splits_of_splits
    (P : ℝ[X])
    (hP : P.Splits) :
    P.derivative.Splits := by
  rw [Polynomial.splits_iff_card_roots]

  -- Como `P` se descompone sobre ℝ, tiene tantas raíces,
  -- contando multiplicidades, como indica su grado.
  have hroots :
      P.roots.card = P.natDegree :=
    Polynomial.splits_iff_card_roots.mp hP

  -- Versión formal del teorema de Rolle:
  -- entre las raíces de P aparecen suficientes raíces de P'.
  have hrolle :
      P.roots.card ≤ P.derivative.roots.card + 1 :=
    Polynomial.card_roots_le_derivative P

  -- La derivada tiene grado `natDegree P - 1`.
  have hdegree :
      P.derivative.natDegree = P.natDegree - 1 :=
    Polynomial.natDegree_derivative P

  -- El número de raíces de cualquier polinomio no nulo
  -- no supera su grado.
  have hupper :
      P.derivative.roots.card ≤ P.derivative.natDegree := by
    by_cases hd : P.derivative = 0
    · simp [hd]
    · have h :=
        Polynomial.card_roots (p := P.derivative) hd
      rw [Polynomial.degree_eq_natDegree hd] at h
      exact_mod_cast h

  -- Rolle proporciona la desigualdad contraria.
  have hlower :
      P.derivative.natDegree ≤ P.derivative.roots.card := by
    omega

  exact Nat.le_antisymm hupper hlower
