import Chapter12GaussianVectorFunction
import Chapter12GaussianJetAlgebra

namespace Asakura.Chapter12
set_option maxHeartbeats 1800000

noncomputable def gaussianVectorNormSquare {N:ℕ} (u:Fin N → GaussianJet N) : GaussianJet N :=
  GaussianJet.finsetSum Finset.univ (fun i => (u i).mul (u i))

theorem gaussianVectorNormSquare_value {H:Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {N:ℕ} (u:Fin N → GaussianJet N) (e:Fin N → H) (he:Orthonormal ℝ e) :
    (gaussianVectorNormSquare u).f=(fun x => ‖x‖^2) ∘ gaussianVectorFunction u e := by
  funext x
  change (∑i,(u i).f x*(u i).f x)=‖∑i,(u i).f x • e i‖^2
  rw [orthonormal_sum_norm e he,Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  simp only [pow_two]
end Asakura.Chapter12
#print axioms Asakura.Chapter12.gaussianVectorNormSquare_value
