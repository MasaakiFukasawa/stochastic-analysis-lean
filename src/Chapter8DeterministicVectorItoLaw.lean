import Chapter8DeterministicBracketLaw
import Chapter8ContinuousScoreCross
import Chapter6FiniteWeightedIto

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

/-- Every linear combination of deterministic vector Wiener integrals has
its exact Gaussian law. Correlation and singular covariance are allowed. -/
theorem deterministic_vector_ito_projection_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d p : ℕ} (B : BrownianSystem P d)
    (G : Fin p → Fin d → ℝ → ℝ) (hG : ∀ i j,Continuous (G i j))
    (N : Fin p → Fin d → HalfClosedTime → Ω → ℝ)
    (hN : ∀ i j,LocalMProcessWitness P B.F (N i j))
    (hNI : ∀ i j,ItoCovarianceFormula P B.F (B.W j) (fun z => G i j z.2) (N i j))
    (v : Fin p → ℝ) (R : ℝ) (hR : 0≤R) :
    HasLaw (fun w => ∑ i,v i*(∑ j,N i j (realTimeClamp R) w))
      (gaussianReal 0 ⟨∫ r in 0..R,∑ j,(∑ i,v i*G i j r)^2,
        intervalIntegral.integral_nonneg_of_forall hR (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))⟩) P := by
  let Z := fun j t w => ∑ i,v i*N i j t w
  let H := fun j (z : Ω × ℝ) => ∑ i,v i*G i j z.2
  have hZ j := finite_weighted_ito P (by simp : (0:EReal)<⊤) B.F B.mono B.le B.null
    (B.W j) (B.martingale j) (fun i z => G i j z.2) (fun i => N i j) (fun i => hN i j) (fun i => hNI i j) v
  have hc j w : Continuous (fun r => H j (w,r)) :=
    continuous_finset_sum _ (fun i _ => continuous_const.mul (hG i j))
  have hm j : Measurable (H j) := by
    exact Finset.measurable_sum _ (fun i _ => measurable_const.mul ((hG i j).measurable.comp measurable_snd))
  obtain ⟨C,hC,hCe⟩ := continuous_score_cross P B H H hm hm hc hc Z Z
    (fun j => (hZ j).1) (fun j => (hZ j).1) (fun j => (hZ j).2) (fun j => (hZ j).2)
  have hM : LocalMProcessWitness P B.F (fun t w => ∑ j,Z j t w) :=
    local_martingale_finset_sum P (by simp) B.F B.mono B.le Finset.univ Z (fun j _ => (hZ j).1)
  let f := fun r => ∑ j,(∑ i,v i*G i j r)^2
  have hf : Continuous f := continuous_finset_sum _ (fun j _ => (continuous_finset_sum _ (fun i _ => continuous_const.mul (hG i j))).pow 2)
  have he (r : ℝ) (hr : 0≤r) : C (realTimeClamp r)=ᵐ[P] fun _ => ∫ s in 0..r,f s := by
    simpa only [H,f,pow_two] using hCe r hr
  have hh := continuous_deterministic_bracket_law P B.F B.mono B.le B.null _ C hM hC f hf
    (fun r _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) he R hR
  convert hh using 1
  funext w
  simp only [Z,Finset.mul_sum]
  exact Finset.sum_comm

end Asakura.Chapter8
