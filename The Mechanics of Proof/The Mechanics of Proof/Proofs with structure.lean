-- 2. Proofs with structure
import Mathlib


-- 2.1.3 example
example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 := by
  have h3 : r ≤ 3 + s := by linarith
  have h4 : r ≤ 3 - s := by linarith
  calc
  r = (r + r) / 2 := by linarith
  _ ≤ (3 - s + (3 + s)) / 2 := by linarith
  _ = 3 := by linarith


-- 2.1.6 example
example {x y : ℤ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 := by
  have hx_simple : x ≤ -1 := by linarith
  have hy_simple : y ≥ 3 - 2 * x := by linarith
  linarith [hx_simple, hy_simple]



-- 2.1.7 example
example (a b : ℝ) (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  have h1_simple : a+b ≥ 0 := by linarith
  have h2_simple : b-a ≥ 0 := by linarith
  have h3 : (a+b) * (b-a) ≥ 0 := by nlinarith [h1_simple,h2_simple]
  nlinarith [h3]


-- 2.1.8 example
example (a b : ℝ) (h : a ≤ b) : a ^ 3 ≤ b ^ 3 := by
  have h1 : b-a ≥ 0 := by linarith
  have h2 : (b-a) * ((b-a)^2 + 3*(b+a)^2)/4 ≥ 0 := by nlinarith [h1]
  calc
    a^3 ≤ a^3 + (b-a) * ((b-a)^2 + 3*(b+a)^2)/4 := by linarith
    _ = b^3 := by ring


--2.1.9 exercise
--1
example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  have h3 : x^2 - 4 = 0 := by linarith
  have h4 : (x-2) * (x+2) = 0 := by linarith
  have h5 :x*(x+2) = 2*(x+2) := by linarith
  have h6 : x+2 ≠ 0 := by linarith
  nlinarith

--2
example {n : ℤ} (hn : n ^ 2 + 4 = 4 * n) : n = 2 := by
  have h1 : n^2 - 4*n + 4 = 0 := by linarith
  have h2 : (n-2)^2 = 0 := by linarith
  have h3 : n-2 = 0 := by nlinarith
  linarith


--3
example (x y : ℚ) (h : x * y = 1) (h2 : x ≥ 1) : y ≤ 1 := by
  have h3 : x * y >0 := by linarith
  have h4 : y > 0 := by nlinarith
  nlinarith


-- 2.2.2 example
example {y : ℝ} : y ^ 2 + 1 ≠ 0 := by
  apply ne_of_gt
  have h1 : y^2 ≥ 0 := by nlinarith
  linarith


-- 2.2.4 exercise
--1
example {m : ℤ} (hm : m + 1 = 5) : 3 * m ≠ 6 := by
  apply ne_of_gt
  have h1 : m = 4 := by linarith
  linarith


--2
example {s : ℚ} (h1 : 3 * s ≤ -6) (h2 : 2 * s ≥ -4) : s = -2 := by
  have h3 : s ≤ -2 := by linarith
  have h4 : s ≥ -2 := by linarith
  apply le_antisymm
  {
    linarith
  }
  {
    nlinarith [ h4]
  }


-- 2.3.2 example
example {n : ℕ} : n ^ 2 ≠ 2 := by
-- "le_or_succ_le" no longer works, so we use "omega" to get the same result
  have hn : n ≤ 1 ∨ 2 ≤ n := by omega
  obtain hn | hn := hn
  · apply ne_of_lt
    calc
      n ^ 2 ≤ 1 ^ 2 := by rel [hn]
      _ < 2 := by norm_num
  · apply ne_of_gt
    calc
      2 < 2 ^ 2 := by norm_num
      _ ≤ n ^ 2 := by rel [hn]


-- 2.3.4 example
example {x : ℝ} (hx : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 := by
  have h1 :=
  calc
    (x - 1) * (x - 2) = x ^ 2 - 3 * x + 2 := by ring
    _ = 0 := by rw [hx]
  rcases mul_eq_zero.mp h1 with hx1 | hx2
  · left
    {
      nlinarith [hx1]
    }
  · right
    {
      nlinarith [hx2]
    }

-- 2.3.4 example with "obtain"
example {x : ℝ} (hx : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 := by
  have h1 :=
  calc
    (x - 1) * (x - 2) = x ^ 2 - 3 * x + 2 := by ring
    _ = 0 := by rw [hx]
  obtain hx1 | hx2 := mul_eq_zero.mp h1
  · left
    {
      nlinarith [hx1]
    }
  · right
    {
      nlinarith [hx2]
    }


--2.3.5 example
example {n : ℤ} : n ^ 2 ≠ 2 := by
  have hn0 : n ≤ 0 ∨ 1 ≤ n := by omega
  obtain hn0 | hn0 := hn0
  · have hnn : (0 : ℤ) ≤ -n := by linarith
    have hn : -n ≤ 1 ∨ 2 ≤ -n := by omega
    obtain hn | hn := hn
    · apply ne_of_lt
      calc
        n ^ 2 = (-n) ^ 2 := by ring
        _ ≤ 1 ^ 2 := by rel [hn]
        _ < 2 := by norm_num
    · apply ne_of_gt
      calc
        (2:ℤ) < 2 ^ 2 := by norm_num
        _ ≤ (-n) ^ 2 := by rel [hn]
        _ = n ^ 2 := by ring
  · have hn : n ≤ 1 ∨ 2 ≤ n := by omega
    obtain hn | hn := hn
    · apply ne_of_lt
      calc
        n ^ 2 ≤ 1 ^ 2 := by rel [hn]
        _ < 2 := by norm_num
    · apply ne_of_gt
      calc
        (2:ℤ) < 2 ^ 2 := by norm_num
        _ ≤ n ^ 2 := by rel [hn]

--2.3.6 exercise
--1
example {x : ℚ} (h : x = 4 ∨ x = -4) : x ^ 2 + 1 = 17 := by
  obtain h1 | h1 := h
  · calc
      x^2 + 1 = 4^2 + 1 := by rw [h1]
      _ = 17 := by norm_num
  · calc
      x^2 + 1 = (-4)^2 + 1 := by rw [h1]
      _ = 17 := by norm_num

--2
example {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  obtain h1 | h1 := h
  · calc
      x^2 - 3*x + 2 = 1^2 - 3*1 + 2 := by rw [h1]
      _ = 0 := by norm_num
  · calc
      x^2 - 3*x + 2 = 2^2 - 3*2 + 2 := by rw [h1]
      _ = 0 := by norm_num


--3
example {t : ℚ} (h : t = -2 ∨ t = 3) : t ^ 2 - t - 6 = 0 := by
  obtain h1 | h1 := h
  · calc
      t^2 - t - 6 = (-2)^2 - (-2) - 6 := by rw [h1]
      _ = 0 := by norm_num
  · calc
      t^2 - t - 6 = 3^2 - 3 - 6 := by rw [h1]
      _ = 0 := by norm_num




--4
example {x y : ℝ} (h : x = 2 ∨ y = -2) : x * y + 2 * x = 2 * y + 4 := by
  obtain h1 | h1 := h
  · calc
      x*y + 2*x = 2*y + 2*2 := by rw [h1]
      _ = 2*y + 4 := by norm_num
  · calc
      x*y + 2*x = x*(-2) + 2*x := by rw [h1]
      _ = 0 := by linarith
      _ = 2*(-2) + 4 := by ring
      _= 2*y + 4 := by rw [h1]


--5
example {s t : ℚ} (h : s = 3 - t) : s + t = 3 ∨ s + t = 5 := by
  have h1 : s + t = 3 := by linarith
  left
  {
    linarith
  }


--6
example {a b : ℚ} (h : a + 2 * b < 0) : b < a / 2 ∨ b < - a / 2 := by
  right
  nlinarith [h]


--7
example {x y : ℝ} (h : y = 2 * x + 1) : x < y / 2 ∨ x > y / 2 := by
  have hx:y/2 - 1/2 = x := by linarith [h]
  left
  linarith [hx]


--8
example {x : ℝ} (hx : x ^ 2 + 2 * x - 3 = 0) : x = -3 ∨ x = 1 := by
  have h1 : (x+3) * (x-1) = x^2 + 2*x - 3 := by ring
  rw [hx] at h1
  obtain h2 | h2 := mul_eq_zero.mp h1
  · left
    linarith [h2]
  · right
    linarith [h2]

--9
example {a b : ℝ} (hab : a ^ 2 + 2 * b ^ 2 = 3 * a * b) : a = b ∨ a = 2 * b := by
  have h1 : (a-2*b) * (a-b) = a^2 + 2*b^2 - 3*a*b := by ring
  rw [hab] at h1
  have heq: (a-2*b) * (a-b) =0 := by linarith
  obtain h2 | h2 := mul_eq_zero.mp heq
  · right
    nlinarith
  · left
    nlinarith

--10
example {t : ℝ} (ht : t ^ 3 = t ^ 2) : t = 1 ∨ t = 0 := by
  have h1 : t^3 - t^2 = 0 := by linarith
  have h2 : t^2 * (t-1) = 0 := by linarith
  obtain h3 | h3 := mul_eq_zero.mp h2
  · right
    nlinarith [h3]
  · left
    nlinarith [h3]

--11
example {n : ℕ} : n ^ 2 ≠ 7 := by
  have hn : n ≤ 2 ∨ 3 ≤ n := by omega
  obtain hn1 | hn2 := hn
  · apply ne_of_lt
    calc
      n ^ 2 ≤ 2 ^ 2 := by rel [hn1]
      _ < 7 := by norm_num
  · apply ne_of_gt
    calc
      7 < 3 ^ 2 := by norm_num
      _ ≤ n ^ 2 := by rel [hn2]

--12
example {x : ℤ} : 2 * x ≠ 3 := by
  have hx : x ≤ 1 ∨ 2 ≤ x := by omega
  obtain hx1 | hx2 := hx
  · apply ne_of_lt
    calc
      2*x ≤ 2*1 := by rel [hx1]
      _ < 3 := by norm_num
  · apply ne_of_gt
    calc
      3 < 2*2 := by norm_num
      _ ≤ 2*x := by rel [hx2]


--13
example {t : ℤ} : 5 * t ≠ 18 := by
  have ht : t ≤ 3 ∨ 4 ≤ t := by omega
  obtain ht1 | ht2 := ht
  · apply ne_of_lt
    calc
      5*t ≤ 5*3 := by rel [ht1]
      _ < 18 := by norm_num
  · apply ne_of_gt
    calc
      18 < 5*4 := by norm_num
      _ ≤ 5*t := by rel [ht2]


--14
example {m : ℕ} : m ^ 2 + 4 * m ≠ 46 := by
  have hm : m ≤ 5 ∨ 6 ≤ m := by omega
  obtain hm1 | hm2 := hm
  · apply ne_of_lt
    calc
      m^2 + 4*m ≤ 5^2 + 4*5 := by rel [hm1]
      _ < 46 := by norm_num
  · apply ne_of_gt
    calc
      46 < 6^2 + 4*6 := by norm_num
      _ ≤ m^2 + 4*m := by rel [hm2]
