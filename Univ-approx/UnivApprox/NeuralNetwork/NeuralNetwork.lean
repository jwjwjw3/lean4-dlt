import Mathlib.Data.Real.Basic
import UnivApprox.NeuralNetwork.SIGN


-------------------------------------------------------------------
-------------- Nd to 1d SIGN 2-layer Neural Network ---------------
noncomputable section

def NNsign2layer (m : PNat)
    (A : Matrix (Fin 1) (Fin m) ℝ)
    (B : Matrix (Fin 1) (Fin m) ℝ)
    (x : ℝ) : ℝ :=
  ∑ i : Fin m, (A 0 i) * sign_nonneg ( x - (B 0 i) )

end
-------------------------------------------------------------------
