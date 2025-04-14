import Mathlib.Data.Real.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {ι : Type*} [Fintype ι] (B : Basis ι ℝ V) (v : V) (i : ι)


-- relu: Scalar function
def relu (x : ℝ) : ℝ := max 0 x

-- ReLU: Vector function
noncomputable def ReLU (v : V) : V := ∑ i : ι, relu (B.repr v i) • (B i)
