import Chapter6BoundedGirsanovData

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- The exponential density can be written using any already constructed
Ito integrals of the coefficient, by the manuscript's uniqueness theorem. -/
theorem bounded_given_integral_density {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (H : Fin d → Ω × ℝ → ℝ) (hHm : ∀ i,Measurable (H i))
    (hHp : ∀ i b,0<b → @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) b => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) b => H i (z.1,z.2.val)))
    (K : ℝ) (hK : 0≤K) (hHb : ∀ i z,|H i z|≤K)
    (N : Fin d → HalfClosedTime → Ω → ℝ) (hN : ∀ i,LocalMProcessWitness P B.F (N i))
    (hNI : ∀ i,ItoCovarianceFormula P B.F (B.W i) (H i) (N i))
    (R : ℝ) (hR : 0≤R) :
    let D := fun w => Real.exp ((∑ i,N i (realTimeClamp R) w)-(∫ r in 0..R,∑ i,(H i (w,r))^2)/2)
    Integrable D P ∧ (∫ w,D w ∂P)=1 ∧ IsProbabilityMeasure (P.withDensity (fun w => ENNReal.ofReal (D w))) := by
  obtain ⟨M,C,hM,hMI,_,hCe,Q,hQp,hQD,hmean,hD2,_⟩ := bounded_girsanov_density_data P B H hHm hHp K hK hHb R hR
  have he i := ItoCovarianceFormula.unique P (show (0:EReal)<⊤ by simp) B.F B.mono B.le B.null
    (B.W i) (M i) (N i) (H i) (B.martingale i) (hM i) (hN i) (hMI i) (hNI i)
  let D := fun w => Real.exp ((∑ i,N i (realTimeClamp R) w)-(∫ r in 0..R,∑ i,(H i (w,r))^2)/2)
  let D' := fun w => Real.exp ((∑ i,M i (realTimeClamp R) w)-C (realTimeClamp R) w/2)
  have hD : D'=ᵐ[P] D := by
    filter_upwards [ae_all_iff.2 he,hCe R hR] with w hw hc
    dsimp [D',D]
    rw [hc]
    congr 2
    exact Finset.sum_congr rfl (fun i _ => hw i _ (changed_time_finite R hR))
  have hi : Integrable D P := (hD2.integrable (by norm_num)).congr hD
  have hm : (∫ w,D w ∂P)=1 := (integral_congr_ae hD).symm.trans hmean
  have hQ : Q=P.withDensity (fun w => ENNReal.ofReal (D w)) := hQD.trans (withDensity_congr_ae (hD.mono (fun w hw => congrArg ENNReal.ofReal hw)))
  exact ⟨hi,hm,hQ ▸ hQp⟩

end Asakura.Chapter6
