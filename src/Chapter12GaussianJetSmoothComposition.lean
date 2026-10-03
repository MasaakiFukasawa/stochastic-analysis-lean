import Chapter12GaussianJetCylinder
import Chapter12DerivativeGrowthComposition
import Chapter12CylinderSmoothChain

open scoped ContDiff
namespace Asakura.Chapter12
set_option maxHeartbeats 1800000

noncomputable def GaussianJet.compSmooth {N : ℕ} (f : GaussianJet N)
    (b : ℝ → ℝ) (hb : ContDiff ℝ ∞ b)
    (hB : ∀k:ℕ,∃C:ℝ,0≤C ∧ ∃a:ℕ,∀x,‖iteratedFDeriv ℝ k b x‖≤C*(1+‖x‖)^a) : GaussianJet N :=
  ⟨b ∘ f.f,hb.comp f.smooth,iterated_polynomial_growth_comp f.f b f.smooth hb f.growth hB⟩

end Asakura.Chapter12
#print axioms Asakura.Chapter12.GaussianJet.compSmooth
