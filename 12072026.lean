import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

open MeasureTheory

variable {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
variable (X Y : Ω → ℝ) (ϕ : ℝ → ℝ)

/-- Si X ≤ Y casi seguramente y ϕ es monótona no decreciente, 
    entonces ϕ(X) ≤ ϕ(Y) casi seguramente. -/
theorem ae_le_image_of_monotone (h_mono : Monotone ϕ) (h : X ≤ᵐ[P] Y) :
    (fun ω => ϕ (X ω)) ≤ᵐ[P] (fun ω => ϕ (Y ω)) := by
  filter_upwards [h] with ω hω
  exact h_mono hω
