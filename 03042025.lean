import Mathlib

namespace RetoMatematico

/--
Parejas de números naturales positivos `(m,n)` tales que:

* `m ≤ n`;
* `mcm(m,n) = 1515`.

El intervalo `Icc 1 1515` excluye el cero, pues en Lean `ℕ` contiene a `0`.
No es necesario examinar números mayores que `1515`, ya que cada miembro
de una pareja divide a su mínimo común múltiplo.
-/
def soluciones1515 : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 1515).product (Finset.Icc 1 1515)).filter
    (fun p => p.1 ≤ p.2 ∧ Nat.lcm p.1 p.2 = 1515)

/-- Lista explícita de las catorce soluciones. -/
def listaSoluciones1515 : Finset (ℕ × ℕ) :=
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

/--
La búsqueda finita coincide exactamente con la lista explícita.
Por tanto, no falta ninguna solución ni aparece ninguna pareja adicional.
-/
theorem soluciones1515_eq_lista :
    soluciones1515 = listaSoluciones1515 := by
  native_decide

/-- El número de parejas solicitadas es 14. -/
theorem numero_de_soluciones1515 :
    soluciones1515.card = 14 := by
  native_decide

/--
Versión que muestra simultáneamente la lista completa y su cardinal.
-/
theorem clasificacion_completa :
    soluciones1515 = listaSoluciones1515 ∧
      soluciones1515.card = 14 := by
  constructor
  · exact soluciones1515_eq_lista
  · exact numero_de_soluciones1515

end RetoMatematico
