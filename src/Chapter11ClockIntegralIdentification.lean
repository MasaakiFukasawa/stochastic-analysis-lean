import Chapter6MeasurableCovarianceDensity
import Chapter6CovarianceCommonTime
import Chapter4CovarianceEquality

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

/-- The bracket and the cross bracket with the Brownian driver identify
 an integral with a merely measurable integrand. This is the step needed
 after changing measure; no continuity of the hedging strategy is assumed. -/
theorem clock_integral_identification
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (W X N A B C : HalfClosedTime → Ω → ℝ)
    (hW : LocalMProcessWitness P F W) (hX : LocalMProcessWitness P F X)
    (hN : LocalMProcessWitness P F N)
    (hA : LocalCovarianceWitness P F X X A)
    (hB : LocalCovarianceWitness P F N N B)
    (hC : LocalCovarianceWitness P F W X C)
    (H : Ω × ℝ → ℝ) (hHm : ∀ w,Measurable (fun r => H (w,r)))
    (hNI : ItoCovarianceFormula P F W H N)
    (hH2 : ∀ R : ℝ,0≤R → ∀ᵐ w ∂P,IntervalIntegrable (fun r => H (w,r)^2) volume 0 R)
    (hAe : ∀ R : ℝ,0≤R → A (realTimeClamp R)=ᵐ[P] fun w => ∫ r in 0..R,H (w,r)^2)
    (hBe : ∀ R : ℝ,0≤R → B (realTimeClamp R)=ᵐ[P] fun w => ∫ r in 0..R,H (w,r)^2)
    (hCe : ∀ R : ℝ,0≤R → C (realTimeClamp R)=ᵐ[P] fun w => ∫ r in 0..R,H (w,r)) :
    ∀ᵐ w ∂P,∀ t,t<⊤ → X t w=N t w := by
  have hH1 R (hR : 0≤R) : ∀ᵐ w ∂P,IntervalIntegrable (fun r => H (w,r)) volume 0 R := by
    filter_upwards [hH2 R hR] with w hw
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mpr
    have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mp hw
    have h2 : MemLp (fun r => H (w,r)) 2 (volume.restrict (Ioc 0 R)) :=
      (memLp_two_iff_integrable_sq (hHm w).aestronglyMeasurable).mpr hi
    exact h2.integrable (by norm_num)
  have hcommon := covariance_density_common_time P F W X C hW hX hC H hH1 hCe
  obtain ⟨D,hD,hDe⟩ := measurable_ito_covariance_density P F W X N C hX hC H H hHm hHm hNI
    hH1 (fun R hR => by simpa only [pow_two] using hH2 R hR) hcommon
  have hab := local_covariance_common_time_equality P (by simp : (0:EReal)<⊤) F X X A B hX hX hA
    (hB.continuous_open_paths P F N N B hN hN) (by
      intro t ht
      obtain ⟨r,hr,_,rfl⟩ := finite_closed_time_real t ht
      exact (hAe r hr).trans (hBe r hr).symm)
  have had := local_covariance_common_time_equality P (by simp : (0:EReal)<⊤) F X X A D hX hX hA
    (hD.continuous_open_paths P F N X D hN hX) (by
      intro t ht
      obtain ⟨r,hr,_,rfl⟩ := finite_closed_time_real t ht
      exact (hAe r hr).trans (by simpa only [pow_two] using (hDe r hr).symm))
  apply local_equal_of_three_covariances P F hF hle X N A B D hX hN hA hB (hD.symm P F)
  filter_upwards [hab,had] with w hw hd
  intro t ht
  rw [←hw t ht,←hd t ht]
  ring

end Asakura.Chapter11
