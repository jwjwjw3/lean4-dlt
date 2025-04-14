import Mathlib.Data.Real.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {ι : Type*} [Fintype ι] (B : Basis ι ℝ V) (v : V) (i : ι)


noncomputable def sign_nonneg (x : ℝ) : ℝ := if 0 ≤ x then 1 else 0
