import Chapter13NormalizedRow
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
theorem normalized_market_noise_brownian {Ω:Type*} {m:MeasurableSpace Ω}
    (P:Measure Ω) [IsProbabilityMeasure P] {d:ℕ} (B:BrownianSystem P (d+1))
    (σ:Ω × ℝ → EuclideanSpace ℝ (Fin (d+1))) (hσ:Measurable σ)
    (hσp:∀b,0<b → @Measurable _ _
      (progressiveSpace (fun t:Icc (0:ℝ) b => B.F (realTimeClamp t.val))) inferInstance
      (fun z:Ω × Icc (0:ℝ) b => σ (z.1,z.2.val)))
    (hn:∀ᵐw∂P,∀ᵐr∂volume,0≤r → σ (w,r)≠0) :
    ∃N:Fin (d+1) → HalfClosedTime → Ω → ℝ,
      (∀i,LocalMProcessWitness P B.F (N i)) ∧
      (∀i,ItoCovarianceFormula P B.F (B.W i) (fun z => σ z i/‖σ z‖) (N i)) ∧
      LocalMProcessWitness P B.F (fun t w => ∑i,N i t w) ∧
      LocalCovarianceWitness P B.F (fun t w => ∑i,N i t w) (fun t w => ∑i,N i t w) (B.C 0 0) ∧
      ∀R,0≤R → ∀s (hs:s∈Icc 0 R),
        HasLaw (fun w => (∑i,N i (realTimeClamp R) w)-(∑i,N i (realTimeClamp s) w))
          (gaussianReal 0 ⟨R-s,sub_nonneg.mpr hs.2⟩) P ∧
        Indep (MeasurableSpace.comap (fun w => (∑i,N i (realTimeClamp R) w)-(∑i,N i (realTimeClamp s) w)) inferInstance)
          (B.F (realTimeClamp s)) P := by
  obtain ⟨hm,hp,hb,hu⟩:=normalized_row_data P B σ hσ hσp hn
  exact progressive_unit_noise_brownian P B (fun i z => σ z i/‖σ z‖) hm hp hb hu
end Asakura.Chapter13
#print axioms Asakura.Chapter13.normalized_market_noise_brownian
