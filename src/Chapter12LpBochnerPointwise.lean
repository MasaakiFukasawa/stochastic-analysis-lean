import Chapter12LpInclusion
import Chapter2L2BochnerPointwise

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
open Asakura.Chapter2Complete
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Identify a scalar-valued pointwise integral with its Lp Bochner
integral for p >= 2, through the continuous inclusion into L2. -/
theorem Lp_bochner_integral_pointwise {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    (μ : Measure α) [SigmaFinite μ] (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 ≤ p)
    (S : α × Ω → ℝ) (hSm : Measurable S) (hL : ∀ x, MemLp (fun w => S (x,w)) p P)
    (hi : Integrable (fun x => (hL x).toLp _) μ) :
    ((∫ x,(hL x).toLp _ ∂μ : Lp ℝ p P) : Ω → ℝ) =ᵐ[P] (fun w => ∫ x,S (x,w) ∂μ) := by
  let J := probabilityLpInclusion (E := ℝ) P 2 p hp
  have hL2 (x) : MemLp (fun w => S (x,w)) 2 P := (hL x).mono_exponent hp
  have he (x) : J ((hL x).toLp _) = (hL2 x).toLp _ := by
    apply Lp.ext
    exact (probabilityLpInclusion_coe P 2 p hp ((hL x).toLp _)).trans
      ((hL x).coeFn_toLp.trans (hL2 x).coeFn_toLp.symm)
  have hi2 : Integrable (fun x => (hL2 x).toLp _) μ := by
    simpa only [he] using J.integrable_comp hi
  have hJ : J (∫ x,(hL x).toLp _ ∂μ) = ∫ x,(hL2 x).toLp _ ∂μ := by
    rw [←J.integral_comp_comm hi]
    simp only [he]
  have hraw := l2_bochner_integral_pointwise μ P S hSm hL2 hi2
  have hcoe := probabilityLpInclusion_coe P 2 p hp (∫ x,(hL x).toLp _ ∂μ)
  change (J (∫ x,(hL x).toLp _ ∂μ) : Ω → ℝ) =ᵐ[P] _ at hcoe
  rw [hJ] at hcoe
  exact hcoe.symm.trans hraw

end Asakura.Chapter12
