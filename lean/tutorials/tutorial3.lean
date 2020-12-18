import data.real.basic
import algebra.group.pi


def even_fun (f : ℝ → ℝ) := ∀ x, f(-x) = f x

def odd_fun (f : ℝ → ℝ) := ∀ x, f (-x) = - f x

