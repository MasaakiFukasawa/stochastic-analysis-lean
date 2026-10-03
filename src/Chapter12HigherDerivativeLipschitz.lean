import Chapter12SuperpositionSmooth

open scoped ContDiff NNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 1200000

theorem bounded_next_derivative_lipschitz {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : ContDiff ℝ ∞ f) (k : ℕ) (C : ℝ≥0)
    (hb : ∀x,‖iteratedFDeriv ℝ (k+1) f x‖≤(C:ℝ)) :
    LipschitzWith C (iteratedFDeriv ℝ k f) := by
  have hd : Differentiable ℝ (iteratedFDeriv ℝ k f) := fun x =>
    hf.contDiffAt.differentiableAt_iteratedFDeriv (m:=k) (by exact_mod_cast ENat.natCast_lt_top k)
  apply lipschitzWith_of_nnnorm_fderiv_le hd
  intro x
  have hh : ‖fderiv ℝ (iteratedFDeriv ℝ k f) x‖≤(C:ℝ) := by
    simpa only [norm_fderiv_iteratedFDeriv] using hb x
  exact_mod_cast hh
end Asakura.Chapter12
#print axioms Asakura.Chapter12.bounded_next_derivative_lipschitz
