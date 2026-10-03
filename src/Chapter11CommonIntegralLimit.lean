import Chapter8ProbabilityMeasureChange
import Chapter2CommonTimeEquality

open MeasureTheory Set Filter TopologicalSpace
open scoped Topology
namespace Asakura.Chapter11

/-- A common sequence of elementary gains identifies stochastic integrals
 under equivalent measures. No integrability of the likelihood ratio is used. -/
theorem common_integral_limit {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsFiniteMeasure Q] (hQP : Q ≪ P)
    (J : ℕ → Ω → ℝ) (I K : Ω → ℝ)
    (hJ : ∀ n,AEStronglyMeasurable (J n) Q)
    (hP : TendstoInMeasure P J atTop I) (hQ : TendstoInMeasure Q J atTop K) : I=ᵐ[Q] K :=
  tendstoInMeasure_ae_unique (Asakura.Chapter8.probability_absolutely_continuous P Q hQP J I hJ hP) hQ

/-- Pointwise identification on a countable dense set yields the equality
 of the continuous integral processes, as used throughout the manuscript. -/
theorem common_integral_process_limit {Ω D : Type*} [MeasurableSpace Ω]
    [TopologicalSpace D] [SeparableSpace D] [Nonempty D]
    (P Q : Measure Ω) [IsFiniteMeasure Q] (hQP : Q ≪ P)
    (J : ℕ → D → Ω → ℝ) (I K : D → Ω → ℝ)
    (hI : ∀ w,Continuous (fun t => I t w)) (hK : ∀ w,Continuous (fun t => K t w))
    (hJ : ∀ n t,AEStronglyMeasurable (J n t) Q)
    (hP : ∀ t,TendstoInMeasure P (fun n => J n t) atTop (I t))
    (hQ : ∀ t,TendstoInMeasure Q (fun n => J n t) atTop (K t)) :
    ∀ᵐ w ∂Q,∀ t,I t w=K t w := by
  have he t := common_integral_limit P Q hQP (fun n => J n t) (I t) (K t) (fun n => hJ n t) (hP t) (hQ t)
  filter_upwards [ae_all_iff.mpr (fun n => he (TopologicalSpace.denseSeq D n))] with w hw
  intro t
  exact (TopologicalSpace.denseRange_denseSeq D).induction_on t (isClosed_eq (hI w) (hK w)) hw

end Asakura.Chapter11
