import Mathlib

/-!
# Retos Matemáticos, 22 de febrero de 2026: los tres vasos

**Enunciado.** Se tienen tres vasos conteniendo un cierto número de unidades de volumen de
agua. Se puede pasar agua de un vaso a otro únicamente doblando el volumen del vaso de
destino (por tanto el vaso de origen debe contener al menos tanta agua como el de destino).
Se pide determinar si, aplicando este procedimiento un número finito de veces, es posible
vaciar alguno de los vasos.

**Respuesta.** Sí, siempre es posible.

La formalización representa un estado por una terna `(a, b, c) : ℕ × ℕ × ℕ`, un movimiento
por la relación `Vasos.Move` (seis constructores, uno por cada par ordenado de vasos) y
"llegar a un estado en un número finito de pasos" por la clausura reflexivo-transitiva
`Vasos.Reach`.

La demostración sigue la primera forma del documento: usando la escritura binaria del
cociente `q = b / a` se transforma la terna `(a, b, c)` (con `a ≤ b ≤ c`) en otra que
contiene el resto `b % a`, y se itera al estilo del algoritmo de Euclides hasta obtener
un cero.
-/

namespace Vasos

/-- Un estado del problema: el contenido de los tres vasos. -/
abbrev State := ℕ × ℕ × ℕ

/-- Un movimiento legal: se vierte agua de un vaso en otro, doblando el contenido del vaso
de destino. El vaso de origen debe contener al menos tanto como el de destino.
El nombre de cada constructor indica origen y destino. -/
inductive Move : State → State → Prop
  /-- Del segundo vaso al primero. -/
  | ba {a b c : ℕ} : a ≤ b → Move (a, b, c) (2 * a, b - a, c)
  /-- Del primer vaso al segundo. -/
  | ab {a b c : ℕ} : b ≤ a → Move (a, b, c) (a - b, 2 * b, c)
  /-- Del tercer vaso al primero. -/
  | ca {a b c : ℕ} : a ≤ c → Move (a, b, c) (2 * a, b, c - a)
  /-- Del primer vaso al tercero. -/
  | ac {a b c : ℕ} : c ≤ a → Move (a, b, c) (a - c, b, 2 * c)
  /-- Del tercer vaso al segundo. -/
  | cb {a b c : ℕ} : b ≤ c → Move (a, b, c) (a, 2 * b, c - b)
  /-- Del segundo vaso al tercero. -/
  | bc {a b c : ℕ} : c ≤ b → Move (a, b, c) (a, b - c, 2 * c)

/-- `Reach s t` significa que se puede pasar del estado `s` al estado `t` en un número
finito (posiblemente nulo) de movimientos legales. -/
def Reach : State → State → Prop := Relation.ReflTransGen Move

/-- Un estado en el que algún vaso está vacío. -/
def HasZero (s : State) : Prop := s.1 = 0 ∨ s.2.1 = 0 ∨ s.2.2 = 0

/-- El contenido del vaso más vacío. -/
def min3 (s : State) : ℕ := min s.1 (min s.2.1 s.2.2)

/-! ### Ejemplos -/

/-- El ejemplo del enunciado: con vasos de 2, 3 y 5 unidades se puede pasar del vaso de 3
al de 2, quedando vasos con 4, 1 y 5 unidades. -/
example : Move (2, 3, 5) (4, 1, 5) := by
  simpa using Move.ba (a := 2) (b := 3) (c := 5) (by norm_num)

/-- Una sucesión concreta de movimientos que vacía un vaso partiendo de `(2, 3, 5)`. -/
example : Reach (2, 3, 5) (0, 2, 8) := by
  refine Relation.ReflTransGen.head (b := (4, 1, 5))
    (by simpa using Move.ba (a := 2) (b := 3) (c := 5) (by norm_num)) ?_
  refine Relation.ReflTransGen.head (b := (3, 2, 5))
    (by simpa using Move.ab (a := 4) (b := 1) (c := 5) (by norm_num)) ?_
  refine Relation.ReflTransGen.head (b := (1, 4, 5))
    (by simpa using Move.ab (a := 3) (b := 2) (c := 5) (by norm_num)) ?_
  refine Relation.ReflTransGen.head (b := (1, 8, 1))
    (by simpa using Move.cb (a := 1) (b := 4) (c := 5) (by norm_num)) ?_
  refine Relation.ReflTransGen.head (b := (1, 7, 2))
    (by simpa using Move.bc (a := 1) (b := 8) (c := 1) (by norm_num)) ?_
  refine Relation.ReflTransGen.head (b := (1, 5, 4))
    (by simpa using Move.bc (a := 1) (b := 7) (c := 2) (by norm_num)) ?_
  refine Relation.ReflTransGen.head (b := (1, 1, 8))
    (by simpa using Move.bc (a := 1) (b := 5) (c := 4) (by norm_num)) ?_
  exact Relation.ReflTransGen.single
    (by simpa using Move.ab (a := 1) (b := 1) (c := 8) (by norm_num))

/-! ### Simetría: los movimientos son invariantes por permutación de los vasos -/

theorem Move.swap12 {x y : State} (h : Move x y) :
    Move (x.2.1, x.1, x.2.2) (y.2.1, y.1, y.2.2) := by
  cases h with
  | ba h => exact Move.ab h
  | ab h => exact Move.ba h
  | ca h => exact Move.cb h
  | ac h => exact Move.bc h
  | cb h => exact Move.ca h
  | bc h => exact Move.ac h

theorem Move.swap23 {x y : State} (h : Move x y) :
    Move (x.1, x.2.2, x.2.1) (y.1, y.2.2, y.2.1) := by
  cases h with
  | ba h => exact Move.ca h
  | ab h => exact Move.ac h
  | ca h => exact Move.ba h
  | ac h => exact Move.ab h
  | cb h => exact Move.bc h
  | bc h => exact Move.cb h

theorem Reach.swap12 {x y : State} (h : Reach x y) :
    Reach (x.2.1, x.1, x.2.2) (y.2.1, y.1, y.2.2) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hst ih => exact Relation.ReflTransGen.tail ih hst.swap12

theorem Reach.swap23 {x y : State} (h : Reach x y) :
    Reach (x.1, x.2.2, x.2.1) (y.1, y.2.2, y.2.1) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hst ih => exact Relation.ReflTransGen.tail ih hst.swap23

/-! ### El paso clave: reducir el vaso mediano módulo el pequeño -/

/-- Núcleo de la solución (escritura binaria del cociente `q`): si `0 < a` y
`q * a ≤ c + a`, entonces desde `(a, q * a + r, c)` se puede llegar a un estado cuyo
segundo vaso contiene exactamente `r`.

Cada paso duplica el vaso pequeño: si el bit actual de `q` es `1` se vierte desde el
mediano y si es `0` se vierte desde el grande. -/
theorem reduce : ∀ q a c r : ℕ, 0 < a → q * a ≤ c + a →
    ∃ a' c', Reach (a, q * a + r, c) (a', r, c') := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro a c r ha hc
    rcases Nat.eq_zero_or_pos q with hq | hq
    · subst hq
      simp only [zero_mul, zero_add]
      exact ⟨a, c, Relation.ReflTransGen.refl⟩
    · rcases Nat.even_or_odd q with he | ho
      · -- `q` par: se vierte del vaso grande al pequeño
        obtain ⟨m, hm⟩ := he
        have hm1 : 1 ≤ m := by omega
        have hac : a ≤ c := by nlinarith [hm, hc]
        have hstep : Move (a, q * a + r, c) (2 * a, q * a + r, c - a) := Move.ca hac
        obtain ⟨a', c', hrec⟩ :=
          ih m (by omega) (2 * a) (c - a) r (by omega) (by
            have : m * (2 * a) = q * a := by subst hm; ring
            omega)
        refine ⟨a', c', ?_⟩
        refine Relation.ReflTransGen.head hstep ?_
        have hqa : m * (2 * a) = q * a := by subst hm; ring
        rw [hqa] at hrec
        exact hrec
      · -- `q` impar: se vierte del vaso mediano al pequeño
        obtain ⟨m, hm⟩ := ho
        have hab : a ≤ q * a + r := by nlinarith
        have hstep : Move (a, q * a + r, c) (2 * a, q * a + r - a, c) := Move.ba hab
        have hkey : q * a + r - a = m * (2 * a) + r := by
          subst hm; cases a with
          | zero => omega
          | succ k => ring_nf; omega
        obtain ⟨a', c', hrec⟩ :=
          ih m (by omega) (2 * a) c r (by omega) (by
            have : m * (2 * a) + a ≤ q * a := by subst hm; nlinarith
            omega)
        refine ⟨a', c', ?_⟩
        refine Relation.ReflTransGen.head hstep ?_
        rw [hkey]
        exact hrec

/-- Si `0 < a` y `b ≤ c`, desde `(a, b, c)` se llega a un estado cuyo vaso más vacío
contiene estrictamente menos de `a` unidades (a saber, a lo sumo `b % a`). -/
theorem sorted_step (a b c : ℕ) (ha : 0 < a) (hbc : b ≤ c) :
    ∃ s, Reach (a, b, c) s ∧ min3 s < a := by
  obtain ⟨a', c', h⟩ := reduce (b / a) a c (b % a) ha (by
    have := Nat.div_mul_le_self b a
    omega)
  have hb : b / a * a + b % a = b := Nat.div_add_mod' b a
  rw [hb] at h
  refine ⟨(a', b % a, c'), h, ?_⟩
  have : b % a < a := Nat.mod_lt _ ha
  simp only [min3]
  omega

/-! ### Solución del problema -/

/-- Desde cualquier estado con todos los vasos no vacíos se puede llegar a un estado
con menos agua en el vaso más vacío. -/
theorem exists_reach_min3_lt (s : State) (h : 0 < min3 s) :
    ∃ t, Reach s t ∧ min3 t < min3 s := by
  obtain ⟨a, b, c⟩ := s
  simp only [min3] at h ⊢
  have ha : 0 < a := by omega
  have hb : 0 < b := by omega
  have hc : 0 < c := by omega
  rcases le_total a b with hab | hab <;> rcases le_total b c with hbc | hbc <;>
    rcases le_total a c with hac | hac
  -- a ≤ b ≤ c, a ≤ c
  · obtain ⟨⟨x, y, z⟩, hr, hm⟩ := sorted_step a b c ha hbc
    exact ⟨(x, y, z), hr, by simp only [min3] at hm ⊢; omega⟩
  · -- a ≤ b ≤ c ≤ a
    obtain ⟨⟨x, y, z⟩, hr, hm⟩ := sorted_step a b c ha hbc
    exact ⟨(x, y, z), hr, by simp only [min3] at hm ⊢; omega⟩
  · -- a ≤ b, c ≤ b, a ≤ c : orden a ≤ c ≤ b
    obtain ⟨⟨x, y, z⟩, hr, hm⟩ := sorted_step a c b ha hbc
    exact ⟨(x, z, y), hr.swap23, by simp only [min3] at hm ⊢; omega⟩
  · -- a ≤ b, c ≤ b, c ≤ a : orden c ≤ a ≤ b
    obtain ⟨⟨x, y, z⟩, hr, hm⟩ := sorted_step c a b hc hab
    exact ⟨(y, z, x), by simpa using ((hr.swap12).swap23), by
      simp only [min3] at hm ⊢; omega⟩
  · -- b ≤ a, b ≤ c, a ≤ c : orden b ≤ a ≤ c
    obtain ⟨⟨x, y, z⟩, hr, hm⟩ := sorted_step b a c hb hac
    exact ⟨(y, x, z), hr.swap12, by simp only [min3] at hm ⊢; omega⟩
  · -- b ≤ a, b ≤ c, c ≤ a : orden b ≤ c ≤ a
    obtain ⟨⟨x, y, z⟩, hr, hm⟩ := sorted_step b c a hb hac
    refine ⟨(z, x, y), ?_, by simp only [min3] at hm ⊢; omega⟩
    simpa using ((hr.swap23).swap12)
  · -- c ≤ b ≤ a ≤ c
    obtain ⟨⟨x, y, z⟩, hr, hm⟩ := sorted_step c b a hc hab
    refine ⟨(z, y, x), ?_, by simp only [min3] at hm ⊢; omega⟩
    simpa using ((hr.swap12).swap23).swap12
  · -- c ≤ b ≤ a : orden c ≤ b ≤ a
    obtain ⟨⟨x, y, z⟩, hr, hm⟩ := sorted_step c b a hc hab
    refine ⟨(z, y, x), ?_, by simp only [min3] at hm ⊢; omega⟩
    simpa using ((hr.swap12).swap23).swap12

theorem reach_hasZero_aux : ∀ (m : ℕ) (s : State), min3 s ≤ m →
    ∃ t, Reach s t ∧ HasZero t := by
  intro m
  induction m with
  | zero =>
    intro s hs
    refine ⟨s, Relation.ReflTransGen.refl, ?_⟩
    obtain ⟨a, b, c⟩ := s
    simp only [min3] at hs
    simp only [HasZero]
    omega
  | succ m ih =>
    intro s hs
    rcases Nat.eq_zero_or_pos (min3 s) with h0 | hpos
    · refine ⟨s, Relation.ReflTransGen.refl, ?_⟩
      obtain ⟨a, b, c⟩ := s
      simp only [min3] at h0
      simp only [HasZero]
      omega
    · obtain ⟨t, hst, hlt⟩ := exists_reach_min3_lt s hpos
      obtain ⟨u, htu, hu⟩ := ih t (by omega)
      exact ⟨u, Relation.ReflTransGen.trans hst htu, hu⟩

/-- **Solución.** Desde cualquier estado inicial de los tres vasos se puede, en un número
finito de movimientos legales, llegar a un estado en el que alguno de los vasos está
vacío. -/
theorem exists_reach_hasZero (a b c : ℕ) :
    ∃ t, Reach (a, b, c) t ∧ HasZero t :=
  reach_hasZero_aux (min3 (a, b, c)) (a, b, c) le_rfl

/-- Versión con la hipótesis del enunciado (los tres vasos contienen inicialmente una
cantidad positiva de agua): siempre es posible vaciar alguno de los vasos. -/
theorem vaciar_un_vaso (a b c : ℕ) (_ha : 0 < a) (_hb : 0 < b) (_hc : 0 < c) :
    ∃ t : State, Reach (a, b, c) t ∧ (t.1 = 0 ∨ t.2.1 = 0 ∨ t.2.2 = 0) :=
  exists_reach_hasZero a b c

end Vasos
