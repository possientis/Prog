import data.real.basic


def upperBounds (A : set ℝ) := { x : ℝ | ∀ a ∈ A, a ≤ x }

def isMaxOf (a : ℝ) (A : set ℝ) := a ∈ A ∧ a ∈ upperBounds A
