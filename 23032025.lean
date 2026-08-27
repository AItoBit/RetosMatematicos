import Mathlib

/-!
# Retos Matemáticos (23 de marzo de 2025)

**Enunciado.** Determínese la ecuación de la cónica `P` tangente a las rectas
`x = 2`, `y = -1`, `x + y = 3`, `x - 3y = 11`, `3x - y = 1`. A continuación:

* a) Demuéstrese que `P` es una parábola.
* b) Hállese el eje de `P`.
* c) Hállese el vértice `V` de `P`.
* d) Hállese el foco `F` de `P`, así como su directriz.
* e) Hállese la ecuación reducida de `P`.

**Solución** (la del documento):

`P : x² + y² - 2xy - 14x - 2y + 33 = 0`, que es una parábola de eje `x - y - 3 = 0`,
vértice `V(3,0)`, foco `F(4,1)`, directriz `x + y - 1 = 0` y ecuación reducida
`y² = 4√2 x`.

Este archivo formaliza el enunciado y la solución.
-/

namespace Retos23032025

open Real

/-! ## La cónica y las cinco rectas -/

/-- La cónica `P : x² + y² - 2xy - 14x - 2y + 33 = 0`, como subconjunto del plano. -/
def P : Set (ℝ × ℝ) :=
  {p | p.1 ^ 2 + p.2 ^ 2 - 2 * p.1 * p.2 - 14 * p.1 - 2 * p.2 + 33 = 0}

/-- La recta `r₁ : x = 2`. -/
def r₁ : Set (ℝ × ℝ) := {p | p.1 = 2}

/-- La recta `r₂ : y = -1`. -/
def r₂ : Set (ℝ × ℝ) := {p | p.2 = -1}

/-- La recta `r₃ : x + y = 3`. -/
def r₃ : Set (ℝ × ℝ) := {p | p.1 + p.2 = 3}

/-- La recta `r₄ : x - 3y = 11`. -/
def r₄ : Set (ℝ × ℝ) := {p | p.1 - 3 * p.2 = 11}

/-- La recta `r₅ : 3x - y = 1`. -/
def r₅ : Set (ℝ × ℝ) := {p | 3 * p.1 - p.2 = 1}

/-! ## Tangencia a las cinco rectas

Cada recta corta a `P` en un único punto (el punto de tangencia). -/

/-- `P` es tangente a `r₁ : x = 2` en el punto `T₄ = (2,3)`. -/
theorem tangente_r₁ : r₁ ∩ P = {((2 : ℝ), (3 : ℝ))} := by
  ext ⟨x, y⟩
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff, r₁, P, Prod.mk.injEq]
  constructor
  · rintro ⟨hx, hP⟩
    subst hx
    refine ⟨rfl, ?_⟩
    nlinarith [sq_nonneg (y - 3)]
  · rintro ⟨hx, hy⟩
    subst hx; subst hy
    norm_num

/-- `P` es tangente a `r₂ : y = -1` en el punto `T = (6,-1)`. -/
theorem tangente_r₂ : r₂ ∩ P = {((6 : ℝ), (-1 : ℝ))} := by
  ext ⟨x, y⟩
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff, r₂, P, Prod.mk.injEq]
  constructor
  · rintro ⟨hy, hP⟩
    subst hy
    refine ⟨?_, rfl⟩
    nlinarith [sq_nonneg (x - 6)]
  · rintro ⟨hx, hy⟩
    subst hx; subst hy
    norm_num

/-- `P` es tangente a `r₃ : x + y = 3` en el punto `T₁ = (3,0)`. -/
theorem tangente_r₃ : r₃ ∩ P = {((3 : ℝ), (0 : ℝ))} := by
  ext ⟨x, y⟩
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff, r₃, P, Prod.mk.injEq]
  constructor
  · rintro ⟨hxy, hP⟩
    have hy : y = 3 - x := by linarith
    subst hy
    have hx : x = 3 := by nlinarith [sq_nonneg (x - 3)]
    exact ⟨hx, by rw [hx]; ring⟩
  · rintro ⟨hx, hy⟩
    subst hx; subst hy
    norm_num

/-- `P` es tangente a `r₄ : x - 3y = 11` en el punto `T₂ = (11,0)`. -/
theorem tangente_r₄ : r₄ ∩ P = {((11 : ℝ), (0 : ℝ))} := by
  ext ⟨x, y⟩
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff, r₄, P, Prod.mk.injEq]
  constructor
  · rintro ⟨hxy, hP⟩
    have hx : x = 11 + 3 * y := by linarith
    subst hx
    have hy : y = 0 := by nlinarith [sq_nonneg y]
    exact ⟨by rw [hy]; ring, hy⟩
  · rintro ⟨hx, hy⟩
    subst hx; subst hy
    norm_num

/-- `P` es tangente a `r₅ : 3x - y = 1` en el punto `T₃ = (3,8)`. -/
theorem tangente_r₅ : r₅ ∩ P = {((3 : ℝ), (8 : ℝ))} := by
  ext ⟨x, y⟩
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff, r₅, P, Prod.mk.injEq]
  constructor
  · rintro ⟨hxy, hP⟩
    have hy : y = 3 * x - 1 := by linarith
    subst hy
    have hx : x = 3 := by nlinarith [sq_nonneg (x - 3)]
    exact ⟨hx, by rw [hx]; ring⟩
  · rintro ⟨hx, hy⟩
    subst hx; subst hy
    norm_num

/-! ## Unicidad

Los cinco puntos de tangencia determinan la cónica: toda cónica
`a x² + b xy + c y² + d x + e y + f = 0` que pase por los cinco puntos de contacto
`(6,-1)`, `(3,0)`, `(11,0)`, `(3,8)`, `(2,3)` es proporcional a `P`. -/

/-- Unicidad de la cónica que pasa por los cinco puntos de tangencia. -/
theorem conica_unica (a b c d e f : ℝ)
    (h₁ : a * 6 ^ 2 + b * 6 * (-1) + c * (-1) ^ 2 + d * 6 + e * (-1) + f = 0)
    (h₂ : a * 3 ^ 2 + b * 3 * 0 + c * 0 ^ 2 + d * 3 + e * 0 + f = 0)
    (h₃ : a * 11 ^ 2 + b * 11 * 0 + c * 0 ^ 2 + d * 11 + e * 0 + f = 0)
    (h₄ : a * 3 ^ 2 + b * 3 * 8 + c * 8 ^ 2 + d * 3 + e * 8 + f = 0)
    (h₅ : a * 2 ^ 2 + b * 2 * 3 + c * 3 ^ 2 + d * 2 + e * 3 + f = 0) :
    b = -2 * a ∧ c = a ∧ d = -14 * a ∧ e = -2 * a ∧ f = 33 * a := by
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- Consecuencia: si además `a = 1`, la ecuación es exactamente la de `P`. -/
theorem conica_unica_monica (b c d e f : ℝ)
    (h₁ : 6 ^ 2 + b * 6 * (-1) + c * (-1) ^ 2 + d * 6 + e * (-1) + f = 0)
    (h₂ : (3 : ℝ) ^ 2 + b * 3 * 0 + c * 0 ^ 2 + d * 3 + e * 0 + f = 0)
    (h₃ : (11 : ℝ) ^ 2 + b * 11 * 0 + c * 0 ^ 2 + d * 11 + e * 0 + f = 0)
    (h₄ : (3 : ℝ) ^ 2 + b * 3 * 8 + c * 8 ^ 2 + d * 3 + e * 8 + f = 0)
    (h₅ : (2 : ℝ) ^ 2 + b * 2 * 3 + c * 3 ^ 2 + d * 2 + e * 3 + f = 0) :
    ∀ x y : ℝ, x ^ 2 + b * x * y + c * y ^ 2 + d * x + e * y + f
      = x ^ 2 + y ^ 2 - 2 * x * y - 14 * x - 2 * y + 33 := by
  obtain ⟨hb, hc, hd, he, hf⟩ := conica_unica 1 b c d e f (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith)
  intro x y
  rw [hb, hc, hd, he, hf]; ring

/-! ## 1ª Forma: la cónica dual

La cónica dual `P*` pasa por los puntos (coordenadas homogéneas de las cinco rectas)
`A = [1:0:-2]`, `B = [0:1:1]`, `C = [1:1:-3]`, `D = [1:-3:-11]`, `E = [3:-1:-1]`, y resulta
ser `P* : 2x² - y² + 5xy + xz + yz = 0`, de matriz proyectiva (salvo proporcionalidad)
`A*`. La matriz adjunta de `A*` da la ecuación de `P`. -/

/-- La forma cuadrática de la cónica dual `P* : 2x² - y² + 5xy + xz + yz = 0`. -/
def qDual (u v w : ℝ) : ℝ := 2 * u ^ 2 - v ^ 2 + 5 * u * v + u * w + v * w

/-- `P*` pasa por los cinco puntos duales asociados a las cinco rectas. -/
theorem qDual_puntos :
    qDual 1 0 (-2) = 0 ∧ qDual 0 1 1 = 0 ∧ qDual 1 1 (-3) = 0 ∧
      qDual 1 (-3) (-11) = 0 ∧ qDual 3 (-1) (-1) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [qDual]

/-- Unicidad de la cónica dual: toda cónica `a u² + b v² + c w² + d uv + e uw + f vw = 0`
que pase por los cinco puntos duales es proporcional a `P*`. -/
theorem dual_conica_unica (a b c d e f : ℝ)
    (hA : a * 1 ^ 2 + b * 0 ^ 2 + c * (-2) ^ 2 + d * 1 * 0 + e * 1 * (-2) + f * 0 * (-2) = 0)
    (hB : a * 0 ^ 2 + b * 1 ^ 2 + c * 1 ^ 2 + d * 0 * 1 + e * 0 * 1 + f * 1 * 1 = 0)
    (hC : a * 1 ^ 2 + b * 1 ^ 2 + c * (-3) ^ 2 + d * 1 * 1 + e * 1 * (-3) + f * 1 * (-3) = 0)
    (hD : a * 1 ^ 2 + b * (-3) ^ 2 + c * (-11) ^ 2 + d * 1 * (-3) + e * 1 * (-11)
      + f * (-3) * (-11) = 0)
    (hE : a * 3 ^ 2 + b * (-1) ^ 2 + c * (-1) ^ 2 + d * 3 * (-1) + e * 3 * (-1)
      + f * (-1) * (-1) = 0) :
    b = -(a / 2) ∧ c = 0 ∧ d = 5 * (a / 2) ∧ e = a / 2 ∧ f = a / 2 := by
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- Matriz proyectiva de la cónica dual `P*` (salvo un factor escalar). -/
def matDual : Matrix (Fin 3) (Fin 3) ℝ := !![4, 5, 1; 5, -2, 1; 1, 1, 0]

/-! ## 2ª Forma: la envolvente de una familia de rectas

La recta `L(t) : (1+t)x + (3-t)y = 2 + 5t - t²` es tangente a `P` para todo `t`, y `P` es
su envolvente: un punto está en `P` exactamente cuando pertenece a una única recta de la
familia. Las cinco rectas del enunciado son `L(3)`, `L(-1)`, `L(1)`, `L(-3)` y `L(5)`. -/

/-- La familia de rectas `L(t) : (1+t)x + (3-t)y = 2 + 5t - t²`. -/
def L (t : ℝ) : Set (ℝ × ℝ) := {p | (1 + t) * p.1 + (3 - t) * p.2 = 2 + 5 * t - t ^ 2}

/-- Identidad clave: la forma de `P` es un cuadrado perfecto módulo la ecuación de `L t`. -/
theorem P_identidad (t x y : ℝ) :
    x ^ 2 + y ^ 2 - 2 * x * y - 14 * x - 2 * y + 33
      = (x - y - 5 + 2 * t) ^ 2
        - 4 * ((1 + t) * x + (3 - t) * y - (2 + 5 * t - t ^ 2)) := by
  ring

/-- Cada recta de la familia es tangente a `P`, con punto de contacto explícito. -/
theorem tangente_familia (t : ℝ) :
    L t ∩ P = {(((t ^ 2 - 6 * t + 17) / 4 : ℝ), ((t ^ 2 + 2 * t - 3) / 4 : ℝ))} := by
  ext ⟨x, y⟩
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff, L, P, Prod.mk.injEq]
  constructor
  · rintro ⟨hL, hP⟩
    rw [P_identidad t x y] at hP
    have hsq : (x - y - 5 + 2 * t) ^ 2 = 0 := by linarith
    have hxy : x - y - 5 + 2 * t = 0 := by
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
    have hy : y = x - 5 + 2 * t := by linarith
    subst hy
    exact ⟨by linear_combination hL / 4, by linear_combination hL / 4⟩
  · rintro ⟨hx, hy⟩
    subst hx; subst hy
    constructor <;> ring

/-- Las cinco rectas del enunciado pertenecen a la familia. -/
theorem rectas_en_familia :
    L 3 = r₁ ∧ L (-1) = r₂ ∧ L 1 = r₃ ∧ L (-3) = r₄ ∧ L 5 = r₅ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> ext ⟨x, y⟩ <;>
    simp only [L, r₁, r₂, r₃, r₄, r₅, Set.mem_ofPred_eq] <;> constructor <;> intro h <;>
    norm_num at h ⊢ <;> linarith

/-- **Envolvente**: un punto está en `P` si y sólo si pertenece a exactamente una recta de
la familia (es decir, la ecuación en `t` tiene raíz doble). -/
theorem P_envolvente (x y : ℝ) :
    (x, y) ∈ P ↔ ∃! t : ℝ, t ^ 2 + (x - y - 5) * t + (x + 3 * y - 2) = 0 := by
  simp only [P, Set.mem_ofPred_eq]
  constructor
  · intro h
    refine ⟨-(x - y - 5) / 2, by nlinarith, ?_⟩
    intro t ht
    have : (t + (x - y - 5) / 2) ^ 2 = 0 := by nlinarith
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linarith
  · rintro ⟨t, ht, huniq⟩
    have ht2 : (-(x - y - 5) - t) ^ 2 + (x - y - 5) * (-(x - y - 5) - t)
        + (x + 3 * y - 2) = 0 := by nlinarith
    have := huniq _ ht2
    nlinarith [ht, this]

/-- La recta `L t` es efectivamente la recta que une el punto `(2, t)` de `r₁` con el punto
`(5 - t, -1)` de `r₂` (homografía usada en la segunda forma). -/
theorem L_pasa_por (t : ℝ) : ((2 : ℝ), t) ∈ L t ∧ ((5 - t : ℝ), (-1 : ℝ)) ∈ L t := by
  constructor <;> simp only [L, Set.mem_ofPred_eq] <;> ring

/-! ## a) `P` es una parábola

Invariantes métricos: la matriz proyectiva `A` de `P` tiene determinante `Δ = -64 ≠ 0`
(cónica no degenerada) y la matriz principal tiene determinante `δ = 0`, luego `P` es
una parábola. Además se da la caracterización foco-directriz. -/

/-- Matriz proyectiva de `P`. -/
def matA : Matrix (Fin 3) (Fin 3) ℝ := !![1, -1, -7; -1, 1, -1; -7, -1, 33]

/-- Matriz principal (parte cuadrática) de `P`. -/
def matPrincipal : Matrix (Fin 2) (Fin 2) ℝ := !![1, -1; -1, 1]

/-- La matriz proyectiva representa efectivamente la ecuación de `P`
(en coordenadas homogéneas, con `z = 1`). -/
theorem matA_repr (x y : ℝ) :
    (Matrix.of ![![x, y, 1]] * matA * Matrix.of ![![x], ![y], ![1]]) 0 0
      = x ^ 2 + y ^ 2 - 2 * x * y - 14 * x - 2 * y + 33 := by
  simp [matA, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

/-- `Δ = |A| = -64 ≠ 0`: la cónica `P` no es degenerada. -/
theorem det_matA : matA.det = -64 := by
  simp [matA, Matrix.det_fin_three]
  norm_num

/-- La adjunta de la matriz de la cónica dual devuelve (salvo signo) la matriz de `P`,
es decir, la ecuación `x² + y² - 2xy - 14x - 2y + 33 = 0`. -/
theorem adjugate_matDual : Matrix.adjugate matDual = -matA := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matDual, matA, Matrix.adjugate_fin_three] <;> norm_num

/-- `δ = 0`: la parte cuadrática es degenerada, luego `P` es una parábola. -/
theorem det_matPrincipal : matPrincipal.det = 0 := by
  simp [matPrincipal, Matrix.det_fin_two]

/-- El foco de `P`. -/
def F : ℝ × ℝ := (4, 1)

/-- El vértice de `P`. -/
def V : ℝ × ℝ := (3, 0)

/-- La directriz de `P` : `x + y - 1 = 0`. -/
def directriz : Set (ℝ × ℝ) := {p | p.1 + p.2 - 1 = 0}

/-- El eje de `P` : `x - y - 3 = 0`. -/
def eje : Set (ℝ × ℝ) := {p | p.1 - p.2 - 3 = 0}

/-- **a) y d)** `P` es exactamente el lugar geométrico de los puntos que equidistan del
foco `F = (4,1)` y de la directriz `x + y - 1 = 0`; en particular `P` es una parábola
con dicho foco y dicha directriz. -/
theorem P_eq_foco_directriz :
    P = {p : ℝ × ℝ | √((p.1 - 4) ^ 2 + (p.2 - 1) ^ 2) = |p.1 + p.2 - 1| / √2} := by
  ext ⟨x, y⟩
  simp only [P, Set.mem_ofPred_eq]
  have hb2 : |x + y - 1| / √2 = √((x + y - 1) ^ 2 / 2) := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_sq_eq_abs]
  rw [hb2, Real.sqrt_inj (by positivity) (by positivity)]
  constructor <;> intro h <;> nlinarith [h]

/-! ## b) El eje -/

/-- La reflexión respecto de la recta `x - y - 3 = 0`. -/
def refl (p : ℝ × ℝ) : ℝ × ℝ := (p.2 + 3, p.1 - 3)

/-- `refl` es la simetría ortogonal respecto del eje: es una isometría. -/
theorem refl_isometria (p q : ℝ × ℝ) :
    (refl p).1 - (refl q).1 = p.2 - q.2 ∧ (refl p).2 - (refl q).2 = p.1 - q.1 := by
  constructor <;> simp [refl]

/-- Los puntos fijos de `refl` son exactamente los puntos del eje. -/
theorem refl_fixed_iff (p : ℝ × ℝ) : refl p = p ↔ p ∈ eje := by
  obtain ⟨x, y⟩ := p
  simp only [refl, eje, Set.mem_ofPred_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2⟩; linarith
  · intro h; exact ⟨by linarith, by linarith⟩

/-- **b)** El eje `x - y - 3 = 0` es eje de simetría de `P`. -/
theorem eje_simetria (p : ℝ × ℝ) : p ∈ P ↔ refl p ∈ P := by
  obtain ⟨x, y⟩ := p
  simp only [P, refl, Set.mem_ofPred_eq]
  constructor <;> intro h <;> nlinarith [h]

/-- El eje pasa por el vértice y por el foco. -/
theorem V_mem_eje : V ∈ eje := by simp [V, eje]

theorem F_mem_eje : F ∈ eje := by norm_num [F, eje]

/-- El eje es perpendicular a la directriz: sus vectores directores `(1,1)` y `(1,-1)`
son ortogonales. -/
theorem eje_perp_directriz : (1 : ℝ) * 1 + 1 * (-1) = 0 := by norm_num

/-! ## c) El vértice -/

/-- **c)** El vértice de `P` es `V = (3,0)`: es el único punto de `P` sobre el eje. -/
theorem vertice : P ∩ eje = {V} := by
  ext ⟨x, y⟩
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff, P, eje, V,
    Prod.mk.injEq]
  constructor
  · rintro ⟨hP, hE⟩
    have hy : y = x - 3 := by linarith
    subst hy
    have hx : x = 3 := by nlinarith
    exact ⟨hx, by linarith⟩
  · rintro ⟨hx, hy⟩
    subst hx; subst hy
    norm_num

/-! ## d) Foco y directriz -/

/-- El foco `F = (4,1)` no pertenece a `P` (es interior a la parábola). -/
theorem F_not_mem_P : F ∉ P := by
  simp [F, P]
  norm_num

/-- La distancia del vértice al foco es `√2` (es decir, `p/2 = √2` con `p = 2√2`). -/
theorem dist_V_F : √((F.1 - V.1) ^ 2 + (F.2 - V.2) ^ 2) = √2 := by
  norm_num [F, V]

/-! ## e) Ecuación reducida

En el sistema de referencia con origen en el vértice `V(3,0)` y ejes las direcciones
`(1,1)/√2` (eje de la parábola) y `(-1,1)/√2`, la ecuación de `P` es `y² = 4√2 x`. -/

/-- Cambio de referencia: giro de 45° y traslación al vértice. -/
noncomputable def Phi (u v : ℝ) : ℝ × ℝ := (3 + (u - v) / √2, (u + v) / √2)

/-- `Phi` es una isometría (conserva las distancias al cuadrado). -/
theorem Phi_isometria (u v u' v' : ℝ) :
    ((Phi u v).1 - (Phi u' v').1) ^ 2 + ((Phi u v).2 - (Phi u' v').2) ^ 2
      = (u - u') ^ 2 + (v - v') ^ 2 := by
  have h2 : (√2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2' : √2 ≠ 0 := by positivity
  simp only [Phi]
  rw [show 3 + (u - v) / √2 - (3 + (u' - v') / √2) = ((u - v) - (u' - v')) / √2 by ring,
    show (u + v) / √2 - (u' + v') / √2 = ((u + v) - (u' + v')) / √2 by ring,
    div_pow, div_pow, h2]
  ring

/-- `Phi` lleva el origen al vértice. -/
theorem Phi_zero : Phi 0 0 = V := by simp [Phi, V]

/-- **e)** La ecuación reducida de `P` es `y² = 4√2 x`. -/
theorem ecuacion_reducida (u v : ℝ) : Phi u v ∈ P ↔ v ^ 2 = 4 * √2 * u := by
  have h2 : (√2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2' : √2 ≠ 0 := by positivity
  simp only [P, Phi, Set.mem_ofPred_eq]
  have key : (3 + (u - v) / √2) ^ 2 + ((u + v) / √2) ^ 2
      - 2 * (3 + (u - v) / √2) * ((u + v) / √2) - 14 * (3 + (u - v) / √2)
      - 2 * ((u + v) / √2) + 33 = 2 * v ^ 2 - 8 * √2 * u := by
    have hd : ∀ a : ℝ, a / √2 = a * √2 / 2 := by
      intro a
      rw [div_eq_div_iff h2' (by norm_num : (2 : ℝ) ≠ 0)]
      linear_combination (-a) * h2
    simp only [hd]
    linear_combination (v ^ 2) * h2
  rw [key]
  constructor <;> intro h <;> linarith

/-! ## Determinación de la cónica: unicidad de la cónica tangente a las cinco rectas

Toda cónica no degenerada `a x² + b xy + c y² + d x + e y + f = 0` tangente a las cinco
rectas dadas (es decir, cuya restricción a cada una de ellas es un cuadrado perfecto, lo
que expresa el contacto doble) es proporcional a `P`. -/

/-- La forma cuadrática general de una cónica. -/
def Qc (a b c d e f x y : ℝ) : ℝ := a * x ^ 2 + b * x * y + c * y ^ 2 + d * x + e * y + f

/-- `P` es el conjunto de ceros de `Qc 1 (-2) 1 (-14) (-2) 33`. -/
theorem P_eq_Qc : P = {p : ℝ × ℝ | Qc 1 (-2) 1 (-14) (-2) 33 p.1 p.2 = 0} := by
  ext ⟨x, y⟩
  simp only [P, Qc, Set.mem_ofPred_eq]
  constructor <;> intro h <;> linarith

/-- Tangencia (contacto doble) de la cónica de coeficientes `a,…,f` con la recta que pasa
por `(px, py)` con vector director `(vx, vy)`: la restricción de la forma cuadrática a la
recta es un cuadrado perfecto. -/
def Tang (a b c d e f px py vx vy : ℝ) : Prop :=
  ∃ A t₀ : ℝ, ∀ t : ℝ, Qc a b c d e f (px + t * vx) (py + t * vy) = A * (t - t₀) ^ 2

/-- Un trinomio de segundo grado que es un cuadrado perfecto tiene discriminante nulo. -/
theorem disc_cero {al be ga A t₀ : ℝ}
    (h : ∀ t : ℝ, al * t ^ 2 + be * t + ga = A * (t - t₀) ^ 2) :
    be ^ 2 - 4 * al * ga = 0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h (-1)
  have hal : al = A := by nlinarith [h0, h1, h2]
  have hbe : be = -2 * (A * t₀) := by nlinarith [h0, h1, h2]
  have hga : ga = A * t₀ ^ 2 := by nlinarith [h0]
  rw [hal, hbe, hga]; ring

/-- Matriz proyectiva de la cónica `a x² + b xy + c y² + d x + e y + f = 0`. -/
noncomputable def matConica (a b c d e f : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![a, b / 2, d / 2; b / 2, c, e / 2; d / 2, e / 2, f]

/-- Adjunta de la matriz proyectiva de una cónica general. -/
theorem adjugate_matConica (a b c d e f : ℝ) :
    Matrix.adjugate (matConica a b c d e f) =
      !![c * f - e ^ 2 / 4, d * e / 4 - b * f / 2, b * e / 4 - c * d / 2;
         d * e / 4 - b * f / 2, a * f - d ^ 2 / 4, b * d / 4 - a * e / 2;
         b * e / 4 - c * d / 2, b * d / 4 - a * e / 2, a * c - b ^ 2 / 4] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matConica, Matrix.adjugate_fin_three] <;> ring

/-- Si la matriz adjunta de una cónica es proporcional a la de la cónica dual `P*` y la
cónica es no degenerada, entonces su matriz es proporcional a la de `P`. -/
theorem matConica_prop_of_adjugate (a b c d e f lam : ℝ)
    (hN : Matrix.adjugate (matConica a b c d e f) = lam • matDual)
    (hdet : (matConica a b c d e f).det ≠ 0) :
    ∃ k : ℝ, k ≠ 0 ∧ matConica a b c d e f = k • matA := by
  set M := matConica a b c d e f with hM
  have hcard : Fintype.card (Fin 3) ≠ 1 := by simp
  have hlam : lam ≠ 0 := by
    rintro rfl
    have hd : (Matrix.adjugate M).det = M.det ^ 2 := by
      rw [Matrix.det_adjugate]; norm_num
    rw [hN, zero_smul, Matrix.det_zero] at hd
    exact hdet (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hd.symm)
  have h1 : Matrix.adjugate (Matrix.adjugate M) = M.det • M := by
    rw [Matrix.adjugate_adjugate M hcard]
    norm_num
  rw [hN, Matrix.adjugate_smul, adjugate_matDual] at h1
  simp only [Fintype.card_fin] at h1
  norm_num at h1
  refine ⟨-(lam ^ 2) / M.det, div_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 hlam)) hdet, ?_⟩
  have key : M.det • M = M.det • ((-(lam ^ 2) / M.det) • matA) := by
    rw [smul_smul, mul_div_cancel₀ _ hdet, ← h1]
    module
  exact smul_right_injective (Matrix (Fin 3) (Fin 3) ℝ) hdet key

/-- **Determinación de la cónica.** Si la cónica `a x² + b xy + c y² + d x + e y + f = 0`
es no degenerada y es tangente a las cinco rectas `x = 2`, `y = -1`, `x + y = 3`,
`x - 3y = 11`, `3x - y = 1`, entonces sus coeficientes son proporcionales a los de
`P : x² + y² - 2xy - 14x - 2y + 33 = 0`. -/
theorem conica_tangente_unica (a b c d e f : ℝ)
    (hdet : (matConica a b c d e f).det ≠ 0)
    (h₁ : Tang a b c d e f 2 0 0 1)
    (h₂ : Tang a b c d e f 0 (-1) 1 0)
    (h₃ : Tang a b c d e f 0 3 1 (-1))
    (h₄ : Tang a b c d e f 11 0 3 1)
    (h₅ : Tang a b c d e f 0 (-1) 1 3) :
    ∃ k : ℝ, k ≠ 0 ∧ a = k ∧ b = -2 * k ∧ c = k ∧ d = -14 * k ∧ e = -2 * k ∧ f = 33 * k := by
  obtain ⟨A₁, s₁, hf₁⟩ := h₁
  obtain ⟨A₂, s₂, hf₂⟩ := h₂
  obtain ⟨A₃, s₃, hf₃⟩ := h₃
  obtain ⟨A₄, s₄, hf₄⟩ := h₄
  obtain ⟨A₅, s₅, hf₅⟩ := h₅
  have hd₁ : (2 * b + e) ^ 2 - 4 * c * (4 * a + 2 * d + f) = 0 :=
    disc_cero (al := c) (be := 2 * b + e) (ga := 4 * a + 2 * d + f)
      (fun t => by rw [← hf₁ t]; simp [Qc]; ring)
  have hd₂ : (d - b) ^ 2 - 4 * a * (c - e + f) = 0 :=
    disc_cero (al := a) (be := d - b) (ga := c - e + f)
      (fun t => by rw [← hf₂ t]; simp [Qc]; ring)
  have hd₃ : (3 * b - 6 * c + d - e) ^ 2 - 4 * (a - b + c) * (9 * c + 3 * e + f) = 0 :=
    disc_cero (al := a - b + c) (be := 3 * b - 6 * c + d - e) (ga := 9 * c + 3 * e + f)
      (fun t => by rw [← hf₃ t]; simp [Qc]; ring)
  have hd₄ : (66 * a + 11 * b + 3 * d + e) ^ 2
      - 4 * (9 * a + 3 * b + c) * (121 * a + 11 * d + f) = 0 :=
    disc_cero (al := 9 * a + 3 * b + c) (be := 66 * a + 11 * b + 3 * d + e)
      (ga := 121 * a + 11 * d + f)
      (fun t => by rw [← hf₄ t]; simp [Qc]; ring)
  have hd₅ : (-b - 6 * c + d + 3 * e) ^ 2 - 4 * (a + 3 * b + 9 * c) * (c - e + f) = 0 :=
    disc_cero (al := a + 3 * b + 9 * c) (be := -b - 6 * c + d + 3 * e) (ga := c - e + f)
      (fun t => by rw [← hf₅ t]; simp [Qc]; ring)
  obtain ⟨hb', hc', hd', he', hf'⟩ :=
    dual_conica_unica (c * f - e ^ 2 / 4) (a * f - d ^ 2 / 4) (a * c - b ^ 2 / 4)
      (2 * (d * e / 4 - b * f / 2)) (2 * (b * e / 4 - c * d / 2)) (2 * (b * d / 4 - a * e / 2))
      (by linear_combination (-1 / 4 : ℝ) * hd₁)
      (by linear_combination (-1 / 4 : ℝ) * hd₂)
      (by linear_combination (-1 / 4 : ℝ) * hd₃)
      (by linear_combination (-1 / 4 : ℝ) * hd₄)
      (by linear_combination (-1 / 4 : ℝ) * hd₅)
  have hN : Matrix.adjugate (matConica a b c d e f) = ((c * f - e ^ 2 / 4) / 4) • matDual := by
    rw [adjugate_matConica]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [matDual] <;> linarith
  obtain ⟨k, hk, hMk⟩ := matConica_prop_of_adjugate a b c d e f _ hN hdet
  refine ⟨k, hk, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := congrFun (congrFun hMk 0) 0; simpa [matConica, matA] using this
  · have := congrFun (congrFun hMk 0) 1; simp [matConica, matA] at this; linarith
  · have := congrFun (congrFun hMk 1) 1; simpa [matConica, matA] using this
  · have := congrFun (congrFun hMk 0) 2; simp [matConica, matA] at this; linarith
  · have := congrFun (congrFun hMk 1) 2; simp [matConica, matA] at this; linarith
  · have := congrFun (congrFun hMk 2) 2; simp [matConica, matA] at this; linarith

/-- **Conclusión:** la cónica no degenerada tangente a las cinco rectas es exactamente `P`. -/
theorem conica_tangente_eq_P (a b c d e f : ℝ)
    (hdet : (matConica a b c d e f).det ≠ 0)
    (h₁ : Tang a b c d e f 2 0 0 1)
    (h₂ : Tang a b c d e f 0 (-1) 1 0)
    (h₃ : Tang a b c d e f 0 3 1 (-1))
    (h₄ : Tang a b c d e f 11 0 3 1)
    (h₅ : Tang a b c d e f 0 (-1) 1 3) :
    {p : ℝ × ℝ | Qc a b c d e f p.1 p.2 = 0} = P := by
  obtain ⟨k, hk, ha, hb, hc, hd, he, hf⟩ := conica_tangente_unica a b c d e f hdet h₁ h₂ h₃ h₄ h₅
  ext ⟨x, y⟩
  simp only [Qc, P, Set.mem_ofPred_eq, ha, hb, hc, hd, he, hf]
  constructor
  · intro h
    have hkey : k * (x ^ 2 + y ^ 2 - 2 * x * y - 14 * x - 2 * y + 33) = 0 := by linear_combination h
    rcases mul_eq_zero.mp hkey with h' | h'
    · exact absurd h' hk
    · exact h'
  · intro h
    linear_combination k * h

end Retos23032025
