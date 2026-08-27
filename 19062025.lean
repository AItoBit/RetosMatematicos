import Mathlib

namespace EstrellaSeisPuntas

/-- Un punto de la retícula triangular en coordenadas axiales. -/
abbrev Punto := ℤ × ℤ

/-- Distancia cuadrática en coordenadas axiales. -/
def distancia2 (p q : Punto) : ℤ :=
  let dq := p.1 - q.1
  let dr := p.2 - q.2
  dq * dq + dq * dr + dr * dr

/--
Los trece puntos de la estrella:

* `0`: centro;
* `1,...,6`: puntos interiores;
* `7,...,12`: vértices exteriores.
-/
def punto : Fin 13 → Punto
  | 0  => (0, 0)
  | 1  => (1, 0)
  | 2  => (0, 1)
  | 3  => (-1, 1)
  | 4  => (-1, 0)
  | 5  => (0, -1)
  | 6  => (1, -1)
  | 7  => (1, 1)
  | 8  => (-1, 2)
  | 9  => (-2, 1)
  | 10 => (-1, -1)
  | 11 => (1, -2)
  | 12 => (2, -1)

/-- Los tres puntos forman un triángulo equilátero no degenerado. -/
def EsEquilatero (i j k : Fin 13) : Prop :=
  distancia2 (punto i) (punto j) ≠ 0 ∧
  distancia2 (punto i) (punto j) =
    distancia2 (punto i) (punto k) ∧
  distancia2 (punto i) (punto j) =
    distancia2 (punto j) (punto k)

/-- Instancia de decidibilidad para `EsEquilatero`. -/
instance (i j k : Fin 13) : Decidable (EsEquilatero i j k) := by
  unfold EsEquilatero
  infer_instance

/-- Una coloración de los trece puntos con dos colores. -/
abbrev Coloracion := Fin 13 → Bool

/-- Los tres puntos poseen el mismo color. -/
def EsMonocromatico
    (c : Coloracion) (i j k : Fin 13) : Prop :=
  c i = c j ∧ c j = c k

/-- Instancia de decidibilidad para `EsMonocromatico`. -/
instance (c : Coloracion) (i j k : Fin 13) : Decidable (EsMonocromatico c i j k) := by
  unfold EsMonocromatico
  infer_instance

/--
Toda coloración de los trece puntos contiene un triángulo
equilátero monocromático.
-/
theorem existe_triangulo_equilatero_monocromatico
    (c : Coloracion) :
    ∃ i j k : Fin 13,
      EsEquilatero i j k ∧ EsMonocromatico c i j k := by
  revert c
  decide

end EstrellaSeisPuntas
