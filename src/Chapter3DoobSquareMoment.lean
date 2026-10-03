import Chapter3BDGTwo

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Doob's M₂ bound expressed in the squared path moments used by BDG. -/
theorem continuous_m2_path_square_moment
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (Y : ClosedTime T → Ω → ℝ) (hY : ContinuousM2Witness P F Y) :
    Integrable (fun ω => ‖continuousPath Y hY.path ω‖^2) P ∧
    (∫ ω, ‖continuousPath Y hY.path ω‖^2 ∂P) ≤ 4*(∫ ω, Y ⊤ ω^2 ∂P) := by
  have hm := continuous_martingale_path_memLp P F hF hle Y hY.adapted hY.moment hY.path hY.martingale
  have hn := continuous_martingale_path_norm P F hF hle Y hY.adapted hY.moment hY.path hY.martingale
  have hmn := hm.norm
  have he1 := real_eLpNorm_two_energy P (fun ω => ‖continuousPath Y hY.path ω‖) hmn
  have he2 := real_eLpNorm_two_energy P (Y ⊤) (hY.moment ⊤)
  rw [← eLpNorm_norm (continuousPath Y hY.path) hm.aestronglyMeasurable,he1,he2] at hn
  have hreal := ENNReal.toReal_mono (by finiteness) hn
  have hA : 0 ≤ ∫ ω, ‖continuousPath Y hY.path ω‖^2 ∂P := integral_nonneg (fun ω => sq_nonneg _)
  have hB : 0 ≤ ∫ ω, Y ⊤ ω^2 ∂P := integral_nonneg (fun ω => sq_nonneg _)
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofNat,← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal hA,ENNReal.toReal_ofReal hB,← Real.sqrt_eq_rpow] at hreal
  refine ⟨hm.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0),?_⟩
  nlinarith [Real.sq_sqrt hA,Real.sq_sqrt hB,Real.sqrt_nonneg (∫ ω, Y ⊤ ω^2 ∂P),
    Real.sqrt_nonneg (∫ ω, ‖continuousPath Y hY.path ω‖^2 ∂P)]

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.continuous_m2_path_square_moment
