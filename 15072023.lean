/-
  Retos Matemáticos — 15 de julio de 2023 (ISSN 2952-0746)

  Ejercicio:  aₙ > 0 para todo n, aₙ → 0.  Calcúlese

      lím_{n→∞}  (1/n) ∑_{k=1}^{n} ln(k/n + aₙ)   =  ∫₀¹ ln x dx  =  -1.

  ---------------------------------------------------------------------------
  ESTADO: un único `sorry`, en el Lema B (la perturbación).  El Lema A
  (Stirling) y el ensamblaje están probados.
  ---------------------------------------------------------------------------

  Arquitectura: se evita por completo la teoría de sumas de Riemann (que aquí
  además sería delicada, porque ln no está definida en 0).  Se parte en

      (1/n) ∑ ln(k/n + aₙ)  =  (1/n) ∑ ln(k/n)  +  (1/n) ∑ [ln(k/n + aₙ) - ln(k/n)]
                                 └── Lema A ──┘     └────────── Lema B ──────────┘
                                     → -1                        → 0

  El Lema A es puro Stirling: ∑_{k=1}^n ln(k/n) = ln(n!) - n ln n, y
  ln(n!)/n - ln n → -1.  Es la vía que el propio boletín menciona en la 2ª Forma.
-/
import Mathlib

open Filter Topology Finset
open scoped Nat

namespace RetosMatematicos1507

noncomputable section

/-! ## Identidad algebraica: la suma de Riemann de ln es un factorial -/

theorem sum_log_div (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Icc 1 n, Real.log ((k : ℝ) / n) = Real.log (n !) - n * Real.log n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  -- ln(n!) = ∑_{k=1}^n ln k
  have hfac : ((n ! : ℕ) : ℝ) = ∏ k ∈ Icc 1 n, (k : ℝ) := by
    rw [← Finset.prod_Icc_id_eq_factorial]
    push_cast
    ring
  have hlogfac : Real.log (n !) = ∑ k ∈ Icc 1 n, Real.log k := by
    rw [hfac, Real.log_prod]
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have : (0 : ℝ) < k := by exact_mod_cast hk1
    exact ne_of_gt this
  -- cada término: ln(k/n) = ln k - ln n
  have hterm : ∀ k ∈ Icc 1 n, Real.log ((k : ℝ) / n) = Real.log k - Real.log n := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    exact Real.log_div (ne_of_gt hk0) (ne_of_gt hn0)
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← hlogfac,
    Finset.sum_const, Nat.card_Icc]
  simp
  ring

/-! ## Lema A (Stirling): (1/n) ∑_{k=1}^n ln(k/n) → -1 -/

/-- `ln(n!)/n - ln n → -1`, consecuencia directa de la fórmula de Stirling. -/
theorem tendsto_logFactorial :
    Tendsto (fun n : ℕ => Real.log (n !) / n - Real.log n) atTop (𝓝 (-1)) := by
  have hpi : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hlogS : Tendsto (fun n : ℕ => Real.log (Stirling.stirlingSeq n)) atTop
      (𝓝 (Real.log (Real.sqrt Real.pi))) :=
    (Real.continuousAt_log (ne_of_gt hpi)).tendsto.comp Stirling.tendsto_stirlingSeq_sqrt_pi
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun n : ℕ => Real.log (Stirling.stirlingSeq n) / n) atTop (𝓝 0) :=
    hlogS.div_atTop hcast
  have h2 : Tendsto (fun n : ℕ => Real.log (2 * n) / (2 * n)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      (Filter.Tendsto.const_mul_atTop (by norm_num : (0:ℝ) < 2) hcast)
  have hlim : Tendsto (fun n : ℕ =>
      Real.log (Stirling.stirlingSeq n) / n + Real.log (2 * n) / (2 * n) - 1)
      atTop (𝓝 (-1)) := by
    have := (h1.add h2).sub (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ)))
    norm_num at this
    exact this
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  -- desarrollo de log(stirlingSeq n) = log n! - log√(2n) - n·log(n/e)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hfac0 : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast n.factorial_pos
  have hsq : (0 : ℝ) < Real.sqrt (2 * n) := Real.sqrt_pos.mpr (by linarith)
  have hpow : (0 : ℝ) < ((n : ℝ) / Real.exp 1) ^ n := by positivity
  have hs : Stirling.stirlingSeq n
      = (n ! : ℝ) / (Real.sqrt (2 * n) * ((n : ℝ) / Real.exp 1) ^ n) := rfl
  rw [hs, Real.log_div (ne_of_gt hfac0) (by positivity),
    Real.log_mul (ne_of_gt hsq) (ne_of_gt hpow),
    Real.log_sqrt (by linarith), Real.log_pow,
    Real.log_div (ne_of_gt hn0) (Real.exp_ne_zero 1), Real.log_exp]
  field_simp
  ring

/-- **Lema A.**  `(1/n) ∑_{k=1}^n ln(k/n) → -1`  (es decir, `∫₀¹ ln x dx = -1`). -/
theorem tendsto_riemann_log :
    Tendsto (fun n : ℕ => (1 / n : ℝ) * ∑ k ∈ Icc 1 n, Real.log ((k : ℝ) / n))
      atTop (𝓝 (-1)) := by
  refine tendsto_logFactorial.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) ≠ n := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact ne_of_lt this
  rw [sum_log_div n hn]
  field_simp
  ring

/-! ## Lema B (la perturbación) -/

/--
**Lema B.**  `(1/n) ∑_{k=1}^n [ln(k/n + aₙ) - ln(k/n)] → 0`.

PENDIENTE.  Ruta elemental (evita integrales impropias y sumas de Riemann):

* Cada término es `ln(1 + n aₙ / k) ≥ 0`, luego basta acotar por arriba.
* Sea `m := ⌈n aₙ⌉`.  Entonces `1 + n aₙ/k ≤ (k+m)/k`, y

      ∏_{k=1}^{n} (k+m)/k  =  (n+m)! / (n! m!)  =  C(n+m, m).

* Con `C(n+m,m) ≤ (n+m)^m / m!` y `m! ≥ (m/e)^m` resulta

      (1/n) ln C(n+m,m)  ≤  c (1 + ln(1 + 1/c)),   c := m/n.

* Como `m ≤ n aₙ + 1`, se tiene `c → 0`, y `c(1 + ln(1+1/c)) → 0`.
* Sándwich con `0 ≤ ·`.

Piezas de Mathlib que hacen falta: `Nat.choose_le_pow_div` (o
`Nat.choose_le_descFactorial_div_factorial` + `Nat.descFactorial_le_pow`),
una cota `(m/e)^m ≤ m!` (de `Real.sum_le_exp_of_nonneg` con un solo término),
y el límite `t ln(1+1/t) → 0` cuando `t → 0⁺`.

Caso borde a tratar aparte: `m = 0` (entonces el producto vale 1 y el término es 0).
-/
theorem tendsto_perturbation (a : ℕ → ℝ) (hpos : ∀ n, 0 < a n)
    (ha : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (1 / n : ℝ) *
      ∑ k ∈ Icc 1 n, (Real.log ((k : ℝ) / n + a n) - Real.log ((k : ℝ) / n)))
      atTop (𝓝 0) := by
  sorry

/-! ## Resultado -/

/-- **Reto (15-VII-2023).**  Si `aₙ > 0` y `aₙ → 0`, entonces
    `(1/n) ∑_{k=1}^n ln(k/n + aₙ) → -1`. -/
theorem retos_15072023 (a : ℕ → ℝ) (hpos : ∀ n, 0 < a n) (ha : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (1 / n : ℝ) * ∑ k ∈ Icc 1 n, Real.log ((k : ℝ) / n + a n))
      atTop (𝓝 (-1)) := by
  have h := tendsto_riemann_log.add (tendsto_perturbation a hpos ha)
  rw [add_zero] at h
  refine h.congr fun n => ?_
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

-- Mostrará `sorryAx` mientras el Lema B siga pendiente.
#print axioms retos_15072023

end

end RetosMatematicos1507
