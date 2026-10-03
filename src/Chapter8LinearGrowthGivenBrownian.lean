import Chapter6LinearGrowthMeanOne
import Chapter6GivenIntegralDensity
import Chapter6ContinuousGivenBrownian

open MeasureTheory Set
open scoped ENNReal BigOperators
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6 Asakura.Chapter7
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- The linear-growth exponential theorem applies to the score integrals
already constructed for the likelihood, by uniqueness of Ito integration. -/
theorem linear_growth_given_integral_brownian {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (H : Fin d → Ω × ℝ → ℝ) (hHm : ∀ i,Measurable (H i))
    (hHp : ∀ i b,0<b → @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) b => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) b => H i (z.1,z.2.val)))
    (hHc : ∀ j w,Continuous (fun r => H j (w,r)))
    (R : ℝ) (hR : 0≤R) (K : ℝ) (hK : 0≤K)
    (hHb : ∀ w r,r∈Icc 0 R → ‖WithLp.toLp 2 (fun j => H j (w,r))‖≤
      K*(1+‖WithLp.toLp 2 (fun j => B.W j (realTimeClamp r) w)‖))
    (N : Fin d → HalfClosedTime → Ω → ℝ) (hN : ∀ i,LocalMProcessWitness P B.F (N i))
    (hNI : ∀ i,ItoCovarianceFormula P B.F (B.W i) (H i) (N i)) :
    let D := fun w => Real.exp ((∑ i,N i (realTimeClamp R) w)-(∫ r in 0..R,∑ i,(H i (w,r))^2)/2)
    ∃ hQp : IsProbabilityMeasure (P.withDensity (fun w => ENNReal.ofReal (D w))),
      ∃ BQ : BrownianSystem (P.withDensity (fun w => ENNReal.ofReal (D w))) d,
        BQ.F=B.F ∧ ∀ j r,0≤r → BQ.W j (realTimeClamp r)=ᵐ[P.withDensity (fun w => ENNReal.ofReal (D w))]
          fun w => B.W j (realTimeClamp r) w-∫ s in 0..min R r,H j (w,s) := by
  obtain ⟨M,C,hM,hMI,hC,hCe,hDi,hmean⟩ :=
    linear_growth_exponential_mean_one P B H hHm hHp hHc R hR K hK hHb
  have he i := ItoCovarianceFormula.unique P (by simp : (0:EReal)<⊤) B.F B.mono B.le B.null
    (B.W i) (M i) (N i) (H i) (B.martingale i) (hM i) (hN i) (hMI i) (hNI i)
  let D := fun w => Real.exp ((∑ i,N i (realTimeClamp R) w)-(∫ r in 0..R,∑ i,(H i (w,r))^2)/2)
  have hD : (fun w => Real.exp ((∑ i,M i (realTimeClamp R) w)-C (realTimeClamp R) w/2))=ᵐ[P] D := by
    filter_upwards [ae_all_iff.2 he,hCe R hR] with w hw hc
    dsimp only [D]
    rw [hc]
    congr 2
    exact Finset.sum_congr rfl (fun i _ => hw i _ (changed_time_finite R hR))
  have hi : Integrable D P := hDi.congr hD
  have hm : (∫ w,D w ∂P)=1 := (integral_congr_ae hD).symm.trans hmean
  let Q := P.withDensity (fun w => ENNReal.ofReal (D w))
  haveI hQp : IsProbabilityMeasure Q := mean_one_density_probability P D hi
    (ae_of_all _ fun _ => (Real.exp_pos _).le) hm
  have hQD : Q=P.withDensity (fun w => ENNReal.ofReal (Real.exp ((∑ i,M i (realTimeClamp R) w)-C (realTimeClamp R) w/2))) :=
    withDensity_congr_ae (hD.symm.mono (fun _ h => congrArg ENNReal.ofReal h))
  obtain ⟨BQ,hF,hW⟩ := continuous_given_density_brownian P Q B H hHm hHc M hM hMI C hC R hR hmean hQD
  exact ⟨hQp,BQ,hF,hW⟩
end Asakura.Chapter8
