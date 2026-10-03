import Chapter4BrownianFiniteMoment
import Chapter4CoefficientEnergy
import Chapter3ContinuousItoEnergy
import Chapter3LocalEnergyMaximal
import Chapter4ClockVariationIntegral

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- The actual drift plus Ito integral satisfies the squared path estimate.
Both square-integrability conclusions are derived from coefficient energy. -/
theorem drift_noise_path_moment
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (W C H Z : ClosedTime T → Ω → ℝ)
    (hW : LocalMProcessWitness P F W) (hC : LocalCovarianceWitness P F W W C)
    (hCm : ∀ ω, MonotoneOn (fun t => C t ω) (Iio ⊤))
    (hCc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => C s ω) t)
    (hclock : ∀ ω (r : ℝ), 0 ≤ r → (r:EReal) < T → C (realTimeClamp r) ω = r)
    (hHm : ∀ t, t < ⊤ → Measurable[F t] (H t))
    (hHc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => H s ω) t)
    (hZ : LocalMProcessWitness P F Z)
    (hZI : ItoCovarianceFormula P F W (fun z => H (realTimeClamp z.2) z.1) Z)
    (d : ℝ) (hd : 0 ≤ d) (hdT : (d:EReal) < T)
    (hHi : MemLp (fun z : Ω × ℝ => H (realTimeClamp z.2) z.1) 2
      (P.prod (volume.restrict (Ioc (0:ℝ) d))))
    (U : Ω × ℝ → ℝ) (hUm : Measurable U)
    (hUi : MemLp U 2 (P.prod (volume.restrict (Ioc (0:ℝ) d))))
    (D : Ω → C(Icc (0:ℝ) d,ℝ)) (hDm : AEStronglyMeasurable D P)
    (hD : ∀ᵐ ω ∂P, ∀ t, D ω t = ∫ r in 0..t.val, U (ω,r)) :
    ∃ hc : ∀ ω, Continuous (fun t => Z (min (realTimeClamp d) t) ω),
      MemLp (fun ω => D ω+finiteRealPath Z d hc ω) 2 P ∧
      (∫ ω, ‖D ω+finiteRealPath Z d hc ω‖^2 ∂P) ≤
        2*d*(∫ z, U z^2 ∂(P.prod (volume.restrict (Ioc (0:ℝ) d))))+
        8*(∫ z : Ω × ℝ, H (realTimeClamp z.2) z.1^2
          ∂(P.prod (volume.restrict (Ioc (0:ℝ) d)))) := by
  let ν := volume.restrict (Ioc (0:ℝ) d)
  have hiH := (memLp_two_iff_integrable_sq hHi.aestronglyMeasurable).1 hHi
  have hiU := (memLp_two_iff_integrable_sq hUi.aestronglyMeasurable).1 hUi
  have hi : Integrable (fun ω => ∫ r in 0..d, H (realTimeClamp r) ω^2) P := by
    simpa only [intervalIntegral.integral_of_le hd] using hiH.integral_prod_left
  obtain ⟨hc,hZ2,hZb⟩ := brownian_ito_finite_path_moment P hT F hF hle hnull
    W C H Z hW hC hCm hCc hclock hHm hHc hZ hZI d hd hdT hi
  obtain ⟨hD2,hDb⟩ := drift_path_moment_bound P d hd U hUm hUi D hDm hD
  have heU : (∫ r in 0..d, (∫ ω, U (ω,r)^2 ∂P)) = ∫ z, U z^2 ∂(P.prod ν) := by
    rw [intervalIntegral.integral_of_le hd,← integral_integral_swap hiU]
    exact (integral_prod _ hiU).symm
  have heH : (∫ ω, (∫ r in 0..d, H (realTimeClamp r) ω^2) ∂P) =
      ∫ z : Ω × ℝ, H (realTimeClamp z.2) z.1^2 ∂(P.prod ν) := by
    simp_rw [intervalIntegral.integral_of_le hd]
    exact (integral_prod _ hiH).symm
  rw [heU] at hDb
  rw [heH] at hZb
  obtain ⟨hL,hb⟩ := path_sum_square_moment P D (finiteRealPath Z d hc) hD2 hZ2
  exact ⟨hc,hL,by nlinarith⟩

end Asakura.Chapter4
