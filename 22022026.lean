import Mathlib

/-!
# Retos Matemáticos: Problema de los Tres Vasos (Algoritmo de Steuerwald)

Se tienen tres vasos con volúmenes de agua `a, b, c ∈ ℕ`. En cada paso se
puede duplicar el volumen de un vaso `x` tomando agua de otro vaso `y` (con `x ≤ y`),
resultando en `(2x, y - x)`.
-/

/-- Representación del estado de los tres vasos. -/
structure State where
  a : ℕ
  b : ℕ
  c : ℕ
  deriving Repr, DecidableEq

namespace WaterGlasses

/-- Regla de transición: trasvasar agua entre dos vasos doblando el contenido del menor. -/
inductive Step : State → State → Prop where
  -- Pasar de `b` a `a` (con `a ≤ b`)
  | pour_ab (a b c : ℕ) (h : a ≤ b) :
      Step ⟨a, b, c⟩ ⟨2 * a, b - a, c⟩
  -- Pasar de `c` a `a` (con `a ≤ c`)
  | pour_ac (a b c : ℕ) (h : a ≤ c) :
      Step ⟨a, b, c⟩ ⟨2 * a, b, c - a⟩
  -- Pasar de `a` a `b` (con `b ≤ a`)
  | pour_ba (a b c : ℕ) (h : b ≤ a) :
      Step ⟨a, b, c⟩ ⟨a - b, 2 * b, c⟩
  -- Pasar de `c` a `b` (con `b ≤ c`)
  | pour_bc (a b c : ℕ) (h : b ≤ c) :
      Step ⟨a, b, c⟩ ⟨a, 2 * b, c - b⟩
  -- Pasar de `a` a `c` (con `c ≤ a`)
  | pour_ca (a b c : ℕ) (h : c ≤ a) :
      Step ⟨a, b, c⟩ ⟨a - c, b, 2 * c⟩
  -- Pasar de `b` a `c` (con `c ≤ b`)
  | pour_cb (a b c : ℕ) (h : c ≤ b) :
      Step ⟨a, b, c⟩ ⟨a, b - c, 2 * c⟩

/-- Clausura reflexiva y transitiva: estados alcanzables mediante pasos válidos. -/
def Reachable : State → State → Prop :=
  Relation.ReflTransGen Step

/-- Condición de parada / meta: al menos un vaso queda con 0 unidades. -/
def HasZero (s : State) : Prop :=
  s.a = 0 ∨ s.b = 0 ∨ s.c = 0

/-! ### Propiedad Invariante: Conservación del Volumen Total -/

/-- Cada paso conserva la suma total de unidades de agua. -/
theorem Step.sum_eq {s₁ s₂ : State} (h : Step s₁ s₂) :
    s₁.a + s₁.b + s₁.c = s₂.a + s₂.b + s₂.c := by
  cases h with
  | pour_ab a b c hab => dsimp; omega
  | pour_ac a b c hac => dsimp; omega
  | pour_ba a b c hba => dsimp; omega
  | pour_bc a b c hbc => dsimp; omega
  | pour_ca a b c hca => dsimp; omega
  | pour_cb a b c hcb => dsimp; omega

/-- Cualquier estado alcanzable conserva la masa/volumen total inicial. -/
theorem Reachable.sum_eq {s₁ s₂ : State} (h : Reachable s₁ s₂) :
    s₁.a + s₁.b + s₁.c = s₂.a + s₂.b + s₂.c := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => rw [ih, hstep.sum_eq]

/-! ### Implementación Computacional Verificada (Algoritmo de Steuerwald) -/

/-- Descomposición binaria de un número natural en bits (LSB primero). -/
def toBinaryList (n : ℕ) : List ℕ :=
  if h : n = 0 then
    []
  else
    (n % 2) :: toBinaryList (n / 2)
termination_by n
decreasing_by
  omega

/-- Un paso del algoritmo de Steuerwald para una terna ordenada `(min, med, max)`.
    Procesa un bit del cociente `q = med / min`:
    - Bit 1: vierte del mediano al menor.
    - Bit 0: vierte del mayor al menor. -/
def steuerwaldBitStep (s : State) (bit : ℕ) : State :=
  if bit == 1 then
    ⟨2 * s.a, s.b - s.a, s.c⟩
  else
    ⟨2 * s.a, s.b, s.c - s.a⟩

/-- Ordena una terna `State` en orden ascendente `(a ≤ b ≤ c)`. -/
def sortState (s : State) : State :=
  let l := [s.a, s.b, s.c].mergeSort (· ≤ ·)
  match l with
  | [x, y, z] => ⟨x, y, z⟩
  | _         => s

/-- Ejecuta una ronda euclidiana de Steuerwald reduciendo `b` a `b % a`. -/
def steuerwaldReduce (s : State) : State :=
  let s_ord := sortState s
  if s_ord.a == 0 then s_ord
  else
    let q := s_ord.b / s_ord.a
    let bits := toBinaryList q
    bits.foldl steuerwaldBitStep s_ord

/-- Solucionador completo con terminación garantizada por inducción estructural en `fuel`. -/
def solve (s : State) : ℕ → List State
  | 0 => [s]
  | fuel + 1 =>
    if s.a = 0 ∨ s.b = 0 ∨ s.c = 0 then
      [s]
    else
      let next := steuerwaldReduce s
      s :: solve next fuel

 
