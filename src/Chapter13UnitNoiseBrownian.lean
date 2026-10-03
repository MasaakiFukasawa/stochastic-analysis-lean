import Chapter6BoundedVectorConstruction
import Chapter4LevyConstructed
import Chapter2CommonTimeEquality
import Chapter3OpenProcessRegularity

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter13
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6 Asakura.Chapter7
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- A bounded progressive unit row of a multidimensional Brownian driver is Brownian.
The unit length is needed only almost everywhere in time and probability. -/
theorem progressive_unit_noise_brownian {Ω:Type*} {m:MeasurableSpace Ω}
    (P:Measure Ω) [IsProbabilityMeasure P] {d:ℕ} (B:BrownianSystem P (d+1))
    (H:Fin (d+1) → Ω × ℝ → ℝ) (hHm:∀i,Measurable (H i))
    (hHp:∀i b,0<b → @Measurable _ _
      (progressiveSpace (fun t:Icc (0:ℝ) b => B.F (realTimeClamp t.val))) inferInstance
      (fun z:Ω × Icc (0:ℝ) b => H i (z.1,z.2.val)))
    (hb:∀i z,|H i z|≤1)
    (hu:∀ᵐw∂P,∀ᵐr∂volume,0≤r → ∑i,(H i (w,r))^2=1) :
    ∃N:Fin (d+1) → HalfClosedTime → Ω → ℝ,
      (∀i,LocalMProcessWitness P B.F (N i)) ∧
      (∀i,ItoCovarianceFormula P B.F (B.W i) (H i) (N i)) ∧
      LocalMProcessWitness P B.F (fun t w => ∑i,N i t w) ∧
      LocalCovarianceWitness P B.F (fun t w => ∑i,N i t w) (fun t w => ∑i,N i t w) (B.C 0 0) ∧
      ∀R,0≤R → ∀s (hs:s∈Icc 0 R),
        HasLaw (fun w => (∑i,N i (realTimeClamp R) w)-(∑i,N i (realTimeClamp s) w))
          (gaussianReal 0 ⟨R-s,sub_nonneg.mpr hs.2⟩) P ∧
        Indep (MeasurableSpace.comap (fun w => (∑i,N i (realTimeClamp R) w)-(∑i,N i (realTimeClamp s) w)) inferInstance)
          (B.F (realTimeClamp s)) P := by
  obtain ⟨N,hN,hNI⟩:=bounded_vector_integrals_constructed P B H hHm hHp 1 (by norm_num) hb
  obtain ⟨hZ,C,_,hC,_,hCe,_⟩:=bounded_vector_integral_covariances P B H hHm 1 (by norm_num) hb N hN hNI
  let Z:=fun t w => ∑i,N i t w
  have he:∀t,t<⊤ → C t=ᵐ[P] B.C 0 0 t := by
    intro t ht
    obtain ⟨r,hr,_,rfl⟩:=finite_closed_time_real t ht
    filter_upwards [hCe r hr,hu] with w hw hu
    rw [hw,B.diagonal_clock 0 w r hr]
    calc
      (∫s in 0..r,∑i,(H i (w,s))^2)=∫s in 0..r,(1:ℝ) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hu] with s hs hsi
        exact hs ((show s∈Ioc 0 r from by simpa only [uIoc_of_le hr] using hsi).1.le)
      _=r := by simp
  have hcommon:=local_covariance_common_time_equality P (by simp : (0:EReal)<⊤) B.F Z Z C (B.C 0 0) hZ hZ hC
    ((B.cov 0 0).continuous_open_paths P B.F _ _ _ (B.martingale 0) (B.martingale 0)) he
  have hV:=covariance_adapted_variation P B.F B.mono B.le (B.martingale 0) (B.martingale 0) (B.cov 0 0)
  have hclock:LocalCovarianceWitness P B.F Z Z (B.C 0 0) := by
    refine ⟨Asakura.Chapter3Complete.LocalMProcessWitness.congr_ae_open P B.F B.mono hC.defect ?_ ?_ ?_,(B.cov 0 0).variation⟩
    · intro t ht
      exact ((hZ.adapted P B.F t ht).mul (hZ.adapted P B.F t ht)).sub (hV.adapted t ht)
    · intro w t ht
      exact ((hZ.path P B.F w t ht).mul (hZ.path P B.F w t ht)).sub
        (local_covariance_path_continuous P B.F _ _ _ (B.martingale 0) (B.martingale 0) (B.cov 0 0) w t ht)
    · filter_upwards [hcommon] with w hw
      intro t ht
      rw [hw t ht]
  refine ⟨N,hN,hNI,hZ,hclock,?_⟩
  intro R hR s hs
  exact levy_gaussian_increment_constructed P (by simp : (0:EReal)<⊤) B.F B.mono B.le B.null Z (B.C 0 0) hZ hclock
    (fun w r hr _ => B.diagonal_clock 0 w r hr) R hR (EReal.coe_lt_top R) s hs
end Asakura.Chapter13
#print axioms Asakura.Chapter13.progressive_unit_noise_brownian
