import Chapter11ConstantIntegral
import Chapter6BoundedItoCrossDensity

open MeasureTheory Set Filter
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- Construct both covariance densities for an arbitrary locally square
 integrable Brownian integrand. No boundedness of the integrand is used. -/
theorem brownian_integral_covariances {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (H : Ω × ℝ → ℝ) (hHm : Measurable H)
    (N : HalfClosedTime → Ω → ℝ) (hN : LocalMProcessWitness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W 0) H N)
    (hH2 : ∀ R : ℝ,0≤R → ∀ᵐ w ∂P,IntervalIntegrable (fun r => H (w,r)^2) volume 0 R) :
    ∃ A D : HalfClosedTime → Ω → ℝ,
      LocalCovarianceWitness P B.F N N A ∧ LocalCovarianceWitness P B.F (B.W 0) N D ∧
      (∀ R : ℝ,0≤R → A (realTimeClamp R)=ᵐ[P] fun w => ∫ r in 0..R,H (w,r)^2) ∧
      (∀ R : ℝ,0≤R → D (realTimeClamp R)=ᵐ[P] fun w => ∫ r in 0..R,H (w,r)) := by
  have hWI : ItoCovarianceFormula P B.F (B.W 0) (fun _ => 1) (B.W 0) := by
    simpa only [one_mul] using constant_ito_integral P (by simp : (0:EReal)<⊤) B.F B.mono B.le B.null (B.W 0) (B.martingale 0) 1
  obtain ⟨D,hD,hDe⟩ := bounded_ito_cross_density P B (fun _ => 1) H measurable_const hHm 1
    (fun _ => by norm_num) (B.W 0) N (B.martingale 0) hN hWI hNI hH2
  have hDe' (R : ℝ) (hR : 0≤R) : D (realTimeClamp R)=ᵐ[P] fun w => ∫ r in 0..R,H (w,r) := by
    simpa only [one_mul] using hDe R hR
  have hi R (hR : 0≤R) : ∀ᵐ w ∂P,IntervalIntegrable (fun r => H (w,r)) volume 0 R := by
    filter_upwards [hH2 R hR] with w hw
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mpr
    have hh : MemLp (fun r => H (w,r)) 2 (volume.restrict (Ioc 0 R)) :=
      (memLp_two_iff_integrable_sq (hHm.comp measurable_prodMk_left).aestronglyMeasurable).mpr
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mp hw)
    exact hh.integrable (by norm_num)
  have hDcomm := covariance_density_common_time P B.F (B.W 0) N D (B.martingale 0) hN hD H hi hDe'
  obtain ⟨A,hA,hAe⟩ := measurable_ito_covariance_density P B.F (B.W 0) N N D hN hD H H
    (fun w => hHm.comp measurable_prodMk_left) (fun w => hHm.comp measurable_prodMk_left) hNI hi
    (fun R hR => by simpa only [←pow_two] using hH2 R hR) hDcomm
  exact ⟨A,D,hA,hD,(fun R hR => by simpa only [←pow_two] using hAe R hR),hDe'⟩

end Asakura.Chapter11
