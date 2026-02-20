-- 1. Proofs by calculation
import Mathlib

-- 1.2.1 example
example {a b : ℚ} (h1 : a - b = 4) (h2 : a * b = 1) : (a + b) ^ 2 = 20 :=
  calc
    (a + b) ^ 2 = (a - b) ^ 2 + 4 * a * b := by ring
    _ = 4^2 +4*a*b:= by rw [h1]
    _= 16 + 4 * (a * b) := by ring
    _ = 16 + 4 * 1 := by rw [h2]
    _ = 20 := by norm_num

-- 1.2.2 example
example {r s : ℝ} (h1 : s = 3) (h2 : r + 2 * s = -1) : r = -7 :=
  calc
    r = r + 2 * s - 2 * s := by ring
    _ = -1 - 2 * s := by rw [h2]
    _ = -1 - 2 * 3 := by rw [h1]
    _ = -7 := by norm_num

-- 1.2.3 example
example {a b m n : ℤ} (h1 : a * m + b * n = 1) (h2 : b ^ 2 = 2 * a ^ 2) :
    (2 * a * n + b * m) ^ 2 = 2 :=
  calc
    (2 * a * n + b * m) ^ 2
      = 2 * (a * m + b * n) ^ 2 + (m ^ 2 - 2 * n ^ 2) * (b ^ 2 - 2 * a ^ 2) := by ring
    _ = 2 * 1 ^ 2 + (m ^ 2 - 2 * n ^ 2) * (2 * a ^ 2 - 2 * a ^ 2) := by rw [h1, h2]
    _ = 2 := by ring

-- 1.2.4 example
example {a b c d e f : ℤ} (h1 : a * d = b * c) (h2 : c * f = d * e) :
    d * (a * f - b * e) = 0 :=
  calc
    d * (a * f - b * e) = a * d * f - b * d * e := by ring
    _ = b * c * f - b * d * e := by rw [h1]
    _ = b * (c * f) - b * d * e := by ring
    _ = b * (d * e) - b * d * e := by rw [h2]
    _ = 0 := by ring


-- 1.3.1 example
example {a b : ℤ} (h1 : a = 2 * b + 5) (h2 : b = 3) : a = 11 :=
  calc
    a = 2 * b + 5 := by rw [h1]
    _ = 2 * 3 + 5 := by rw [h2]
    _ = 11 := by norm_num


-- 1.3.2 example
example {x : ℤ} (h1 : x + 4 = 2) : x = -2 :=
  calc
    x = x + 4 - 4 := by ring
    _ = 2 - 4 := by rw [h1]
    _ = -2 := by norm_num


-- 1.3.3 example
example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 :=
  have h3: b = 3 - 2 := by linarith
  calc
    a = a - 5 * b + 5 * b := by ring
    _ = 4 + 5 * b := by rw [h1]
    _ = 4 + 5 * (3 - 2) := by rw [h3]
    _ = 9 := by linarith


-- 1.3.4 example
example {w : ℚ} (h1 : 3 * w + 1 = 4) : w = 1 :=
  have h2: 3 * w = 4 - 1 := by linarith
  calc
    w = (3 * w) / 3 := by ring
    _ = (4 - 1) / 3 := by rw [h2]
    _ = 1 := by norm_num


-- 1.3.5 example
example {x : ℤ} (h1 : 2 * x + 3 = x) : x = -3 :=
  calc
    x = 2 * x + 3 := by linarith only [h1]
    _ = x + x + 3 := by ring
    _ = -3 := by linarith


-- 1.3.6 example
example {x y : ℤ} (h1 : 2 * x - y = 4) (h2 : y - x + 1 = 2) : x = 5 :=
  have h3 : y - x = 1 := by linarith [h2]
  have h4 : y = x + 1 := by linarith [h3]
  calc
    x = 2 * x - y - x + y := by ring
    _ = 4 - x + y := by rw [h1]
    _ = 4 - x + (x + 1) := by rw [h4]
    _ = 5 := by linarith


-- 1.3.7 example
example {u v : ℚ} (h1 : u + 2 * v = 4) (h2 : u - 2 * v = 6) : u = 5 :=
  calc
    u = ((u + 2 * v) + (u - 2 * v)) / 2 := by ring
    _ = (4 + 6) / 2 := by rw [h1, h2]
    _ = 10 / 2 := by norm_num
    _ = 5 := by norm_num



-- 1.3.8 example
example {x y : ℝ} (h1 : x + y = 4) (h2 : 5 * x - 3 * y = 4) : x = 2 :=
  calc
    x = (3 * (x + y) + (5 * x - 3 * y)) / 8 := by ring
    _ = (3 * 4 + 4) / 8 := by rw [h1, h2]
    _ = 16 / 8 := by norm_num
    _ = 2 := by norm_num


-- 1.3.9 example
example {a b : ℚ} (h1 : a - 3 = 2 * b) : a ^ 2 - a + 3 = 4 * b ^ 2 + 10 * b + 9 :=
  calc
    a^2 - a + 3 = (a - 3) ^ 2 + 5 * (a - 3) + 9:= by ring
    _=(2*b)^2 + 5*(2*b) + 9:= by rw [h1]
    _=4*b^2 + 10*b + 9:= by ring



-- 1.3.10 example
example {z : ℝ} (h1 : z ^ 2 - 2 = 0) : z ^ 4 - z ^ 3 - z ^ 2 + 2 * z + 1 = 3 :=
  calc
    z^4 - z^3 - z^2 + 2 * z + 1 = (z^2-z+1)*(z^2-2)+3 := by ring
    _=(z^2-z+1)*0+3:= by rw [h1]
    _=3:= by ring


-- 1.3.11 exericises

-- 1
example {x y : ℝ} (h1 : x = 3) (h2 : y = 4 * x - 3) : y = 9 :=
  calc
    y = 4 * x - 3 := by rw [h2]
    _ = 4 * 3 - 3 := by rw [h1]
    _ = 9 := by norm_num

-- 2
example {a b : ℤ} (h : a - b = 0) : a = b :=
  calc
    a = a - b + b := by ring
    _ = 0 + b := by rw [h]
    _ = b := by ring

-- 3
example {x y : ℤ} (h1 : x - 3 * y = 5) (h2 : y = 3) : x = 14 :=
  calc
    x = x - 3 * y + 3 * y := by ring
    _ = 5 + 3 * y := by rw [h1]
    _ = 5 + 3 * 3 := by rw [h2]
    _ = 14 := by norm_num


-- 4
example {p q : ℚ} (h1 : p - 2 * q = 1) (h2 : q = -1) : p = -1 :=
  calc
    p = p - 2 * q + 2 * q := by ring
    _ = 1 + 2 * q := by rw [h1]
    _ = 1 + 2 * (-1) := by rw [h2]
    _ = -1 := by norm_num


-- 5
example {x y : ℚ} (h1 : y + 1 = 3) (h2 : x + 2 * y = 3) : x = -1 :=
  have h3 : y = 3 - 1 := by linarith [h1]
  calc
    x = x + 2 * y - 2 * y := by ring
    _ = 3 - 2 * y := by rw [h2]
    _ = 3 - 2 * (3 - 1) := by rw [h3]
    _ = -1 := by norm_num


-- 6
example {p q : ℤ} (h1 : p + 4 * q = 1) (h2 : q - 1 = 2) : p = -11 :=
  calc
    p = p + 4 * q - 4 * q := by ring
    _ = 1 - 4 * q := by rw [h1]
    _ = 1 - 4 * (2 + 1) := by linarith [h2]
    _ = -11 := by norm_num


--7
example {a b c : ℝ} (h1 : a + 2 * b + 3 * c = 7) (h2 : b + 2 * c = 3)
    (h3 : c = 1) : a = 2 :=
  calc
    a = a + 2 * b + 3 * c - 2 * b - 3 * c := by ring
    _ = 7 - 2 * b - 3 * c := by rw [h1]
    _ = 7 - 2 * (3 - 2 * c) - 3 * c := by linarith [h2]
    _ = 7 - 2 * (3 - 2 * 1) - 3 * 1 := by rw [h3]
    _ = 2 := by norm_num


--8
example {u v : ℚ} (h1 : 4 * u + v = 3) (h2 : v = 2) : u = 1 / 4 :=
  calc
    u = 4 * u / 4 := by ring
    _ = (3 - v) / 4 := by linarith [h1]
    _ = (3 - 2) / 4 := by rw [h2]
    _ = 1 / 4 := by norm_num


--9
example {c : ℚ} (h1 : 4 * c + 1 = 3 * c - 2) : c = -3 := by
  linarith

--10
example {p : ℝ} (h1 : 5 * p - 3 = 3 * p + 1) : p = 2 := by
  linarith

--11
example {x y : ℤ} (h1 : 2 * x + y = 4) (h2 : x + y = 1) : x = 3 :=
  calc
    x = 2 * x + y - (x + y) := by ring
    _ = 4 - 1 := by rw [h1, h2]
    _ = 3 := by norm_num


--12
example {a b : ℝ} (h1 : a + 2 * b = 4) (h2 : a - b = 1) : a = 2 :=
  calc
    a = (a + 2 * b) -2*b := by ring
    _ = 4 - 2 * b := by rw [h1]
    _ = 4 - 2 * (a - 1) := by linarith [h2]
    _ = 2 := by linarith


--13
example {u v : ℝ} (h1 : u + 1 = v) : u ^ 2 + 3 * u + 1 = v ^ 2 + v - 1 :=
  calc
    u^2 + 3 * u + 1 = (u + 1)^2 + (u + 1) - 1 := by ring
    _ = v^2 + v - 1 := by rw [h1]



--14
example {t : ℚ} (ht : t ^ 2 - 4 = 0) :
    t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 = 10 * t + 2 :=
  calc
    t^4 + 3 * t^3 - 3 * t^2 - 2 * t - 2 = (t^2 - 4) * (t^2 + 3 * t + 1) + (10 * t + 2) := by ring
    _ = 0 * (t^2 + 3 * t + 1) + (10 * t + 2) := by rw [ht]
    _ = 10 * t + 2 := by ring


--15
example {x y : ℝ} (h1 : x + 3 = 5) (h2 : 2 * x - y * x = 0) : y = 2 :=
  have x_value : x = 2 := by linarith [h1]
  have h2' : 2 * 2 - y * 2 = 0 := by simpa [x_value] using h2
  by linarith [h2']


--16
example {p q r : ℚ} (h1 : p + q + r = 0) (h2 : p * q + p * r + q * r = 2) :
    p ^ 2 + q ^ 2 + r ^ 2 = -4 :=
  calc
    p^2 + q^2 + r^2 = (p + q + r)^2 - 2 * (p * q + p * r + q * r) := by ring
    _ = 0^2 - 2 * 2 := by rw [h1, h2]
    _ = -4 := by norm_num


--1.4.1 example
example {x y : ℤ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 :=
  calc
    y = y + 2 * x - 2 * x := by ring
    _ ≥ 3 - 2 * x := by rel [hy]
    _ = 9 - 2 * (x + 3) := by ring
    _ ≥ 9 - 2 * 2 := by rel [hx]
    _ > 3 := by norm_num


-- 1.4.2 example
example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 :=
  calc
    r = (s + r + r - s) / 2 := by ring
    _ ≤ (3 + (s + 3) - s) / 2 := by linarith [h1, h2]
    _ = 6/2 := by linarith
    _ = 3 := by norm_num


-- 1.4.3 example
example {x y : ℝ} (h1 : y ≤ x + 5) (h2 : x ≤ -2) : x + y < 2 :=
  calc
    x + y ≤ x + (x + 5) := by linarith [h1]
    _ = 2 * x + 5 := by ring
    _ ≤ 2 * (-2) + 5 := by linarith [h2]
    _ = 1 := by norm_num
    _ < 2 := by norm_num


--1.4.4 example
example {u v x y A B : ℝ} (h1 : 0 < A) (h2 : A ≤ 1) (h3 : 1 ≤ B) (h4 : x ≤ B)
    (h5 : y ≤ B) (h6 : 0 ≤ u) (h7 : 0 ≤ v) (h8 : u < A) (h9 : v < A) :
    u * y + v * x + u * v < 3 * A * B :=
  calc
    u * y + v * x + u * v
      ≤ u * B + v * B + u * v := by nlinarith
    _ ≤ A * B + A * B + A * v := by rel [h1, h2, h3, h4, h5, h6, h7, h8, h9]
    _ ≤ A * B + A * B + 1 * v := by rel [h1, h2, h3, h4, h5, h6, h7, h8, h9]
    _ ≤ A * B + A * B + B * v := by rel [h1, h2, h3, h4, h5, h6, h7, h8, h9]
    _ < A * B + A * B + B * A := by nlinarith [h1, h2, h3, h6, h7, h8, h9]
    _ = 3 * A * B := by ring


-- 1.4.5 example
example {t : ℚ} (ht : t ≥ 10) : t ^ 2 - 3 * t - 17 ≥ 5 :=
  calc
    t ^ 2 - 3 * t - 17
      = t * t - 3 * t - 17 := by ring
    _ ≥ 10 * t - 3 * t - 17 := by nlinarith [ht]
    _ = 7 * t - 17 := by ring
    _ ≥ 7 * 10 - 17 := by linarith [ht]
    _ ≥ 5 := by norm_num


-- 1.4.6 example
example {n : ℤ} (hn : n ≥ 5) : n ^ 2 > 2 * n + 11 :=
  calc
    n^2 = n*n := by ring
    _ ≥ 5*n := by rel [hn]
    _ =2*n + 3*n := by ring
    _ > 2*n + 11 := by linarith [hn]


-- 1.4.7 example
example {m n : ℤ} (h : m ^ 2 + n ≤ 2) : n ≤ 2 :=
  have h1 : m^2 ≥ 0 := by nlinarith
  calc
    n ≤ m ^ 2 + n := by nlinarith [h1]
    _ ≤ 2 := by rel [h]


-- 1.4.8 example
example {x y : ℝ} (h : x ^ 2 + y ^ 2 ≤ 1) : (x + y) ^ 2 < 3 :=
  calc
    (x + y) ^ 2 ≤ (x + y) ^ 2 + (x - y) ^ 2 := by nlinarith
    _ = 2 * (x ^ 2 + y ^ 2) := by ring
    _ ≤ 2 * 1 := by linarith [h]
    _ < 3 := by norm_num


--1.4.9 example
example {a b : ℚ} (h1 : a ≥ 0) (h2 : b ≥ 0) (h3 : a + b ≤ 8) :
    3 * a * b + a ≤ 7 * b + 72 :=
  calc
    3 * a * b + a
      ≤ 2 * b ^ 2 + a ^ 2 + (3 * a * b + a) := by nlinarith [h1, h2]
    _ = 2 * ((a + b) * b) + (a + b) * a + a := by ring
    _ ≤ 2 * (8 * b) + 8 * a + a := by nlinarith [h1, h2, h3]
    _ = 7 * b + 9 * (a + b) := by ring
    _ ≤ 7 * b + 9 * 8 := by linarith [h3]
    _ = 7 * b + 72 := by ring


-- 1.4.10 example
example {a b c : ℝ} :
    a ^ 2 * (a ^ 6 + 8 * b ^ 3 * c ^ 3) ≤ (a ^ 4 + b ^ 4 + c ^ 4) ^ 2 :=
  calc
    a ^ 2 * (a ^ 6 + 8 * b ^ 3 * c ^ 3)
      ≤ 2 * (a ^ 2 * (b ^ 2 - c ^ 2)) ^ 2 + (b ^ 4 - c ^ 4) ^ 2
          + 4 * (a ^ 2 * b * c - b ^ 2 * c ^ 2) ^ 2
          + a ^ 2 * (a ^ 6 + 8 * b ^ 3 * c ^ 3) := by
      have h1 := sq_nonneg (a ^ 2 * (b ^ 2 - c ^ 2))
      have h2 := sq_nonneg (b ^ 4 - c ^ 4)
      have h3 := sq_nonneg (a ^ 2 * b * c - b ^ 2 * c ^ 2)
      nlinarith [h1, h2, h3]
    _ = (a ^ 4 + b ^ 4 + c ^ 4) ^ 2 := by ring


--1.4.11 exercises
-- 1
example {x y : ℤ} (h1 : x + 3 ≥ 2 * y) (h2 : 1 ≤ y) : x ≥ -1 :=
  calc
    x = x + 3 - 3 := by ring
    _ ≥ 2 * y - 3 := by linarith [h1]
    _ ≥ 2 * 1 - 3 := by linarith [h2]
    _ = -1 := by norm_num


-- 2
example {a b : ℚ} (h1 : 3 ≤ a) (h2 : a + 2 * b ≥ 4) : a + b ≥ 3 :=
  have h3: b ≥ (4 - a) / 2 := by linarith [h2]
  calc
    a + b ≥ a + (4 - a) / 2 := by linarith [h3]
    _ = (a + 4) / 2 := by ring
    _ ≥ (3 + 4) / 2 := by linarith [h1]
    _ = 7 / 2 := by norm_num
    _ ≥ 3 := by norm_num


-- 3
example {x : ℤ} (hx : x ≥ 9) : x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 3 :=
  calc
    x^3 - 8 * x^2 + 2 * x = x^2 * (x - 8) + 2 * x := by ring
    _ ≥ 9^2 * (9 - 8) + 2 * 9 := by nlinarith [hx]
    _ = 81 + 18 := by norm_num
    _ = 99 := by norm_num
    _ ≥ 3 := by norm_num


-- 4
example {n : ℤ} (hn : n ≥ 10) : n ^ 4 - 2 * n ^ 2 > 3 * n ^ 3 :=
  by
    have h0 : 0 < n ^ 2 := by nlinarith [hn]
    have h1 : 0 < n ^ 2 - 3 * n - 2 := by nlinarith [hn]
    have h2 : 0 < n ^ 2 * (n ^ 2 - 3 * n - 2) := by nlinarith [h0, h1]
    have h3 : n ^ 4 - 2 * n ^ 2 - 3 * n ^ 3 = n ^ 2 * (n ^ 2 - 3 * n - 2) := by ring
    nlinarith [h2, h3]


-- 5
example {n : ℤ} (h1 : n ≥ 5) : n ^ 2 - 2 * n + 3 > 14 :=
  calc
    n ^ 2 - 2 * n + 3 = (n - 1) ^ 2 + 2 := by ring
    _ ≥ (5 - 1) ^ 2 + 2 := by nlinarith [h1]
    _ = 16 + 2 := by norm_num
    _ = 18 := by norm_num
    _ > 14 := by norm_num


-- 6
example {x : ℚ} : x ^ 2 - 2 * x ≥ -1 :=
  calc
    x ^ 2 - 2 * x = (x - 1) ^ 2 - 1 := by ring
    _ ≥ 0 - 1 := by nlinarith
    _ = -1 := by norm_num


-- 7
example (a b : ℝ) : a ^ 2 + b ^ 2 ≥ 2 * a * b :=
  calc
    a ^ 2 + b ^ 2 = (a - b) ^ 2 + 2 * a * b := by ring
    _ ≥ 0 + 2 * a * b := by nlinarith [sq_nonneg (a - b)]
    _ = 2 * a * b := by ring


--1.5
example {w : ℚ} (h1 : 3 * w + 1 = 4) : w = 1 := by linarith [h1]
