import Mathlib

open Finset

/-!
# Reto Matemático: Demostración de 6...6 × 6...67 = 4...42...2

Demostramos formalmente que para todo $n \in \mathbb{N}$:
  $\underbrace{6\dots6}_{n} \times \underbrace{6\dots6}_{n-1}7 = \underbrace{4\dots4}_{n}\underbrace{2\dots2}_{n}$
-/

/-- El repunit $R_n = \sum_{k=0}^{n-1} 10^k = \underbrace{1\dots1}_n$. -/
def repunit (n : ℕ) : ℕ :=
  ∑ i ∈ range n, 10 ^ i

/-- Número formado por $n$ repeticiones del dígito $d$: $\underbrace{d\dots d}_n = d \cdot R_n$. -/
def repdigit (d n : ℕ) : ℕ :=
  d * repunit n

/-- El número $\underbrace{6\dots6}_{n-1}7 = 6 R_n + 1$. -/
def sixes_then_seven (n : ℕ) : ℕ :=
  6 * repunit n + 1

/-- El número yuxtapuesto $\underbrace{4\dots4}_n\underbrace{2\dots2}_n = 4 R_n \cdot 10^n + 2 R_n$. -/
def fours_then_twos (n : ℕ) : ℕ :=
  repdigit 4 n * 10 ^ n + repdigit 2 n

/-! ## Lema fundamental: $9 R_n + 1 = 10^n$ -/

lemma nine_mul_repunit_add_one (n : ℕ) : 9 * repunit n + 1 = 10 ^ n := by
  induction n with
  | zero =>
    simp [repunit]
  | succ n ih =>
    rw [repunit, sum_range_succ, mul_add, pow_succ]
    have h_rec : (∑ i ∈ range n, 10 ^ i) = repunit n := rfl
    rw [h_rec]
    linarith [ih]

/-! ## Teorema Principal -/

theorem seis_por_siete_eq_cuatro_dos (n : ℕ) :
    repdigit 6 n * sixes_then_seven n = fours_then_twos n := by
  dsimp [repdigit, sixes_then_seven, fours_then_twos]
  have h : 10 ^ n = 9 * repunit n + 1 := (nine_mul_repunit_add_one n).symm
  rw [h]
  ring

/-! ## Teorema General (Variantes de la página 3 del documento) -/

/--
Para cualesquiera dígitos $(a, b, c, d)$ que cumplan:
  $a \cdot b = 9 \cdot c$  y  $c + d = a$,
se cumple la identidad de dígitos yuxtapuestos:
  $(a \cdot R_n) \cdot (b \cdot R_n + 1) = c \cdot R_n \cdot 10^n + d \cdot R_n$
-/
theorem general_repdigit_product (a b c d n : ℕ)
    (h1 : a * b = 9 * c)
    (h2 : c + d = a) :
    (a * repunit n) * (b * repunit n + 1) = (c * repunit n) * 10 ^ n + (d * repunit n) := by
  have h : 10 ^ n = 9 * repunit n + 1 := (nine_mul_repunit_add_one n).symm
  rw [h]
  calc (a * repunit n) * (b * repunit n + 1)
    _ = (a * b) * (repunit n)^2 + a * repunit n := by ring
    _ = (9 * c) * (repunit n)^2 + (c + d) * repunit n := by rw [h1, h2]
    _ = (c * repunit n) * (9 * repunit n + 1) + d * repunit n := by ring
