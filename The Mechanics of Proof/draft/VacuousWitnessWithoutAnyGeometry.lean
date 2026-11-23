import Lean

/-
不使用 anyGeometry 的独立玩具模型。
结论仍是原玩具命题：∀ D : Nat, ∀ z : OffLineZero D, False。
OffLineZero 要求同一对象体积等于 0 且严格大于 0，因此不存在。
这不是关于真实黎曼 ζ 函数的黎曼猜想。
-/
namespace WithoutAnyGeometry

structure DivX (D : Nat) where
  lat : Nat → Nat → Int
  h : Nat → Int
  vol : Int
  geo : Nat → Bool

abbrev GeoP (D : Nat) : Type := DivX D → Prop

def realGeometry (D : Nat) : GeoP D := fun X =>
  X.h 0 > 100 ∧ X.vol > 0 ∧ ∀ j k, X.lat j k ≠ 0

def mjLat (D : Nat) (j k : Nat) : Int := if j = k then 1 else 0

def seed (D : Nat) : DivX D where
  lat := mjLat D
  h := fun _ => 0
  vol := 0
  geo := fun _ => false

structure OffLineZero (D : Nat) where
  row : DivX D
  loc : Nat
  inFam : row = seed D
  cert : realGeometry D row

def EveryCharacter (D : Nat) : Prop := ∀ z : OffLineZero D, False

abbrev RiemannHypothesisToy : Prop := ∀ D : Nat, EveryCharacter D

-- 直接使用假想反例携带的条件，不构造 HypsAlt 或任何几何证书。
theorem riemannHypothesisToy : RiemannHypothesisToy := by
  intro D z
  have hreal : realGeometry D (seed D) := z.inFam ▸ z.cert
  have hv : (0 : Int) > 0 := hreal.2.1
  exact (Int.lt_irrefl 0) hv

#print axioms riemannHypothesisToy

end WithoutAnyGeometry
