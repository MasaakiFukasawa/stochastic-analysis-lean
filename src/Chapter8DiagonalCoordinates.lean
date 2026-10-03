import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped BigOperators
namespace Asakura.Chapter8
noncomputable section

def diagonalEuclideanEquiv {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (hc : ∀ i,c i≠0) : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι where
  toFun x := WithLp.toLp 2 (fun i => c i*x i)
  invFun x := WithLp.toLp 2 (fun i => (c i)⁻¹*x i)
  left_inv x := by ext i; simp [hc,mul_assoc]
  right_inv x := by ext i; simp [hc,mul_assoc]
  map_add' x y := by ext i; simp [mul_add]
  map_smul' a x := by ext i; simp [mul_assoc,mul_comm,mul_left_comm]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

end
end Asakura.Chapter8
