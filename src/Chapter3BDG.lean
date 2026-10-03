import Chapter3BDGLocalization
import Chapter3BDGNormRepresentation

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Full BDG in moment form for the original local martingale and any
quadratic-variation representative, including infinite moments. -/
theorem bdg_lintegrals
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hA : LocalCovarianceWitness P F X X A)
    (p : ℝ) (hp : 0 < p) (b : ClosedTime T) (hb : b < ⊤) :
    (∫⁻ ω, (ENNReal.ofReal (runningMaximum X (hX.path P F) b ω))^p ∂P) ≤
      ENNReal.ofReal (bdgUpperMomentConstant p)*(∫⁻ ω, (ENNReal.ofReal (A b ω))^(p/2) ∂P) ∧
    (∫⁻ ω, (ENNReal.ofReal (A b ω))^(p/2) ∂P) ≤
      ENNReal.ofReal (bdgReverseMomentConstant p)*(∫⁻ ω, (ENNReal.ofReal (runningMaximum X (hX.path P F) b ω))^p ∂P) := by
  obtain ⟨Q,hQ,hQm,hQc,hQ0⟩ := local_quadratic_variation_regular_choice P F hF hle hnull X hX
  have h := bdg_lintegrals_regular P hT F hF hle hnull X Q hX hQ hQm hQc hQ0 p hp b hb
  have he := hA.unique P F hF hle hQ
  have hei : (∫⁻ ω, (ENNReal.ofReal (A b ω))^(p/2) ∂P) =
      (∫⁻ ω, (ENNReal.ofReal (Q b ω))^(p/2) ∂P) :=
    lintegral_congr_ae (he.mono (fun ω hω => congrArg (fun x : ℝ => (ENNReal.ofReal x)^(p/2)) (hω b hb)))
  simpa only [hei] using h

/-- The manuscript's two-sided BDG inequality, in extended Lp norms.
The constants depend only on p and are explicitly positive. -/
theorem bdg_norms
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hA : LocalCovarianceWitness P F X X A)
    (p : ℝ) (hp : 0 < p) (b : ClosedTime T) (hb : b < ⊤) :
    eLpNorm (runningMaximum X (hX.path P F) b) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (bdgUpperMomentConstant p^(1/p))*
        eLpNorm (fun ω => Real.sqrt (A b ω)) (ENNReal.ofReal p) P ∧
    eLpNorm (fun ω => Real.sqrt (A b ω)) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (bdgReverseMomentConstant p^(1/p))*
        eLpNorm (runningMaximum X (hX.path P F) b) (ENNReal.ofReal p) P := by
  obtain ⟨Q,hQ,hQm,hQc,hQ0⟩ := local_quadratic_variation_regular_choice P F hF hle hnull X hX
  have hQp ω : 0 ≤ Q b ω := by rw [← hQ0 ω]; exact hQm ω hT hb bot_le
  have he := hA.unique P F hF hle hQ
  have hnorm : eLpNorm (fun ω => Real.sqrt (A b ω)) (ENNReal.ofReal p) P =
      eLpNorm (fun ω => Real.sqrt (Q b ω)) (ENNReal.ofReal p) P :=
    eLpNorm_congr_ae (he.mono (fun ω hω => congrArg Real.sqrt (hω b hb)))
  rw [hnorm,nonnegative_eLpNorm_moment P _
    ((runningMaximum_adapted F hF X (hX.path P F) (hX.adapted P F) b hb).mono (hle b) le_rfl)
    (fun ω => runningMaximum_nonneg X (hX.path P F) b ω) p hp,
    sqrt_eLpNorm_moment P (Q b) ((hQ.adapted P F hX hX b hb).mono (hle b) le_rfl) hQp p hp]
  have h := bdg_lintegrals_regular P hT F hF hle hnull X Q hX hQ hQm hQc hQ0 p hp b hb
  have hcp := bdg_moment_constants_positive p hp
  constructor
  · have hh := ENNReal.rpow_le_rpow h.1 (by positivity : 0 ≤ 1/p)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ 1/p),
      ENNReal.ofReal_rpow_of_nonneg hcp.1.le (by positivity)] at hh
    exact hh
  · have hh := ENNReal.rpow_le_rpow h.2 (by positivity : 0 ≤ 1/p)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ 1/p),
      ENNReal.ofReal_rpow_of_nonneg hcp.2.le (by positivity)] at hh
    exact hh

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.bdg_lintegrals
#print axioms Asakura.Chapter3Complete.bdg_norms
