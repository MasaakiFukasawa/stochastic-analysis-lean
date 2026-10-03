import Chapter4OUKernelConstructed

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter4
noncomputable section

def ouStationaryVariance (κ σ : ℝ) (hκ : 0 < κ) : ℝ≥0 :=
  ⟨σ^2/(2*κ),div_nonneg (sq_nonneg _) (by positivity)⟩

/-- The Gaussian transition previously constructed from the Ito solution
preserves variance σ²/(2κ), including the zero-noise case. -/
theorem ou_stationary_gaussian (κ σ : ℝ) (hκ : 0 < κ) (t : ℝ≥0) :
    (gaussianReal 0 (ouStationaryVariance κ σ hκ)).map (fun x => Real.exp (-κ*(t:ℝ))*x) ∗
      gaussianReal 0 (ouVariance κ σ hκ t) = gaussianReal 0 (ouStationaryVariance κ σ hκ) := by
  rw [gaussianReal_map_const_mul,gaussianReal_conv_gaussianReal]
  apply congrArg₂ gaussianReal
  · simp
  · apply NNReal.eq
    change Real.exp (-κ*(t:ℝ))^2*(σ^2/(2*κ))+
      σ^2*(1-Real.exp (-2*κ*(t:ℝ)))/(2*κ) = σ^2/(2*κ)
    rw [pow_two,← Real.exp_add]
    rw [show -κ*(t:ℝ)+ -κ*(t:ℝ) = -2*κ*(t:ℝ) by ring]
    ring

/-- The exercise's stationary variance equals the Gibbs variance exactly
when the scalar Einstein relation holds. -/
theorem scalar_einstein_variance_iff (μ k σ β : ℝ) (hμ : 0 < μ) (hk : 0 < k) (hβ : 0 < β) :
    σ^2/(2*μ*k) = (β*k)⁻¹ ↔ σ^2 = 2*β⁻¹*μ := by
  have hμ0 := hμ.ne'
  have hk0 := hk.ne'
  have hβ0 := hβ.ne'
  constructor
  · intro h
    field_simp at h ⊢
    nlinarith only [h]
  · intro h
    rw [h]
    field_simp

end
end Asakura.Chapter8
