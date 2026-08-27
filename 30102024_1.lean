import Mathlib

theorem imagen_de_A_es_H
    {R : Type*} [Field R]
    (a b c : R)
    (f : (R × R) →ₗ[R] (R × R))
    (hB : f (b, a) = (c, 0))
    (hD : f (b, 0) = (0, a)) :
    f (0, a) = (c, -a) := by
  have hA : (0, a) = (b, a) - (b, 0) := by
    ext <;> simp

  calc
    f (0, a) = f ((b, a) - (b, 0)) := by rw [hA]
    _ = f (b, a) - f (b, 0) := by rw [f.map_sub]
    _ = (c, 0) - (0, a) := by rw [hB, hD]
    _ = (c, -a) := by
      ext <;> simp
