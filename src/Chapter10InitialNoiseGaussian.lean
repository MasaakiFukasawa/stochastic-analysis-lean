import Chapter10MultitimeIntegralGaussian
import Chapter10MultitimeIntegralIndependence
import Chapter10StoppedCoefficientRegularity
import Chapter10DeterministicIntegralGaussian
import Chapter5StoppedIntegralFormula
import Chapter6FiniteWeightedIto

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6 Asakura.Chapter8
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem initial_and_multitime_integrals_gaussian {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d p : ℕ} (B : BrownianSystem P d)
    (G : Fin p → Fin d → ℝ → ℝ) (hG : ∀ i j,Continuous (G i j))
    (N : Fin p → Fin d → HalfClosedTime → Ω → ℝ)
    (hN : ∀ i j,LocalMProcessWitness P B.F (N i j))
    (hNI : ∀ i j,ItoCovarianceFormula P B.F (B.W j) (fun z => G i j z.2) (N i j))
    {k : ℕ} (ξ : Ω → Fin k → ℝ) (hξ : Measurable[B.F ⊥] ξ)
    (hξg : HasGaussianLaw ξ P)
    (R : ℝ) (hR : 0≤R) (τ : Fin p → ℝ) (hτ : ∀ i,τ i∈Icc 0 R) :
    HasGaussianLaw (fun w => (ξ w,fun i => ∑ j,N i j (realTimeClamp (τ i)) w)) P := by
  have hg := deterministic_integral_multitime_gaussian P B G hG N hN hNI R hR τ hτ
  have hi := deterministic_integral_multitime_independent_initial P B G hG N hN hNI R hR τ hτ
  have hind : IndepFun ξ (fun w i => ∑ j,N i j (realTimeClamp (τ i)) w) P :=
    indep_of_indep_of_le_left hi.symm hξ.comap_le
  exact hind.hasGaussianLaw hξg hg

end Asakura.Chapter10
