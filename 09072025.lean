import Mathlib

namespace MCM1515

def EsSolucion (p : ℕ × ℕ) : Prop :=
  p.1 ≤ p.2 ∧ Nat.lcm p.1 p.2 = 1515

instance (p : ℕ × ℕ) : Decidable (EsSolucion p) := by
  unfold EsSolucion
  infer_instance

def soluciones : Finset (ℕ × ℕ) :=
  ((Finset.range 1516).product (Finset.range 1516)).filter EsSolucion

def solucionesEsperadas : Finset (ℕ × ℕ) :=
  {
    (1, 1515),
    (3, 505),
    (3, 1515),
    (5, 303),
    (5, 1515),
    (15, 101),
    (15, 303),
    (15, 505),
    (15, 1515),
    (101, 1515),
    (303, 505),
    (303, 1515),
    (505, 1515),
    (1515, 1515)
  }

theorem soluciones_eq_esperadas :
    soluciones = solucionesEsperadas := by
  native_decide

theorem numero_de_soluciones :
    soluciones.card = 14 := by
  native_decide

end MCM1515
