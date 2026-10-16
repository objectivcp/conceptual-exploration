import Order2.Superposition

/-! Magmas and the ETP laws of the rules, defined as in the ETP. -/

class Magma (α : Type _) where
  op : α → α → α

infix:65 " ◇ " => Magma.op

/-- Eq2: x = y -/
abbrev Equation2 (G : Type _) [Magma G] := ∀ x y : G, x = y

/-- Eq3: x = (x * x) -/
abbrev Equation3 (G : Type _) [Magma G] := ∀ x : G, x = (x ◇ x)

/-- Eq5: x = (y * x) -/
abbrev Equation5 (G : Type _) [Magma G] := ∀ x y : G, x = (y ◇ x)

/-- Eq8: x = (x * (x * x)) -/
abbrev Equation8 (G : Type _) [Magma G] := ∀ x : G, x = (x ◇ (x ◇ x))

/-- Eq9: x = (x * (x * y)) -/
abbrev Equation9 (G : Type _) [Magma G] := ∀ x y : G, x = (x ◇ (x ◇ y))

/-- Eq10: x = (x * (y * x)) -/
abbrev Equation10 (G : Type _) [Magma G] := ∀ x y : G, x = (x ◇ (y ◇ x))

/-- Eq11: x = (x * (y * y)) -/
abbrev Equation11 (G : Type _) [Magma G] := ∀ x y : G, x = (x ◇ (y ◇ y))

/-- Eq16: x = (y * (y * x)) -/
abbrev Equation16 (G : Type _) [Magma G] := ∀ x y : G, x = (y ◇ (y ◇ x))

/-- Eq23: x = ((x * x) * x) -/
abbrev Equation23 (G : Type _) [Magma G] := ∀ x : G, x = ((x ◇ x) ◇ x)

/-- Eq24: x = ((x * x) * y) -/
abbrev Equation24 (G : Type _) [Magma G] := ∀ x y : G, x = ((x ◇ x) ◇ y)

/-- Eq25: x = ((x * y) * x) -/
abbrev Equation25 (G : Type _) [Magma G] := ∀ x y : G, x = ((x ◇ y) ◇ x)

/-- Eq26: x = ((x * y) * y) -/
abbrev Equation26 (G : Type _) [Magma G] := ∀ x y : G, x = ((x ◇ y) ◇ y)

/-- Eq28: x = ((y * x) * x) -/
abbrev Equation28 (G : Type _) [Magma G] := ∀ x y : G, x = ((y ◇ x) ◇ x)

/-- Eq29: x = ((y * x) * y) -/
abbrev Equation29 (G : Type _) [Magma G] := ∀ x y : G, x = ((y ◇ x) ◇ y)

/-- Eq31: x = ((y * y) * x) -/
abbrev Equation31 (G : Type _) [Magma G] := ∀ x y : G, x = ((y ◇ y) ◇ x)

/-- Eq38: (x * x) = (x * y) -/
abbrev Equation38 (G : Type _) [Magma G] := ∀ x y : G, (x ◇ x) = (x ◇ y)

/-- Eq39: (x * x) = (y * x) -/
abbrev Equation39 (G : Type _) [Magma G] := ∀ x y : G, (x ◇ x) = (y ◇ x)

/-- Eq40: (x * x) = (y * y) -/
abbrev Equation40 (G : Type _) [Magma G] := ∀ x y : G, (x ◇ x) = (y ◇ y)

/-- Eq41: (x * x) = (y * z) -/
abbrev Equation41 (G : Type _) [Magma G] := ∀ x y z : G, (x ◇ x) = (y ◇ z)

/-- Eq43: (x * y) = (y * x) -/
abbrev Equation43 (G : Type _) [Magma G] := ∀ x y : G, (x ◇ y) = (y ◇ x)
