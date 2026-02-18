import Mathlib

-- 1.2.1 example
example {a b : ℚ} (h1 : a - b = 4) (h2 : a * b = 1) : (a + b) ^ 2 = 20 :=
  calc
    (a + b) ^ 2 = (a - b) ^ 2 + 4 * a * b := by ring
    _ = 4^2 +4*a*b:= by rw [h1]
    _= 16 + 4 * (a * b) := by ring
    _ = 16 + 4 * 1 := by rw [h2]
    _ = 20 := by norm_num
