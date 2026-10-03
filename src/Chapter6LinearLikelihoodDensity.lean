import Chapter6GivenIntegralDensity
import Chapter6FiniteWeightedIto
import Chapter6LikelihoodEnergy

open MeasureTheory Set Filter Finset Matrix
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option maxHeartbeats 4200000
set_option backward.isDefEq.respectTransparency false

/-- The actual finite collection of score Ito integrals determines a
probability density for every parameter in the whole Euclidean parameter space. -/
theorem linear_likelihood_density {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P d)
    (H N : Fin n → Fin d → HalfClosedTime → Ω → ℝ)
    (hHa : ∀ k j t,Measurable[B.F t] (H k j t))
    (hHc : ∀ k j w,Continuous (fun t => H k j t w))
    (hN : ∀ k j,LocalMProcessWitness P B.F (N k j))
    (hNI : ∀ k j,ItoCovarianceFormula P B.F (B.W j) (fun z => H k j (realTimeClamp z.2) z.1) (N k j))
    (K : ℝ) (hK : 0≤K) (hHb : ∀ k j t w,|H k j t w|≤K)
    (R : ℝ) (hR : 0≤R) (θ : Fin n → ℝ) :
    let score := fun w k => ∑ j,N k j (realTimeClamp R) w
    let info := fun w k l => ∫ r in 0..R,∑ j,H k j (realTimeClamp r) w*H l j (realTimeClamp r) w
    let D := fun w => Real.exp (quadraticLogLikelihood (info w) (score w) θ)
    Integrable D P ∧ (∫ w,D w ∂P)=1 ∧ IsProbabilityMeasure (P.withDensity (fun w => ENNReal.ofReal (D w))) := by
  let A := fun j t w => ∑ k,θ k*H k j t w
  let M := fun j t w => ∑ k,θ k*N k j t w
  let G := fun j (z : Ω × ℝ) => A j (realTimeClamp z.2) z.1
  have hAi j t : Measurable[B.F t] (A j t) := Finset.measurable_sum _ (fun k _ => (hHa k j t).const_mul _)
  have hAc j w : Continuous (fun t => A j t w) := continuous_finsetSum _ (fun k _ => (hHc k j w).const_mul _)
  have hGr j w : Continuous (fun r => G j (w,r)) := (hAc j w).comp real_time_clamp_continuous
  have hGm j : Measurable (G j) := by
    have hm r : Measurable (A j (realTimeClamp r)) := (hAi j _).mono (B.le _) le_rfl
    simpa only [G,Function.comp_def,Function.uncurry_def,Prod.swap] using
      (measurable_uncurry_of_continuous_of_measurable (hGr j) hm).comp measurable_swap
  have hGp j r (hr : 0<r) := continuous_adapted_real_progressive B.F B.mono (G j) r hr.le
    (fun s _ => hAi j _) (fun w => (hGr j w).continuousOn)
  have hMb j := finite_weighted_ito P (show (0:EReal)<⊤ by simp) B.F B.mono B.le B.null
    (B.W j) (B.martingale j) (fun k z => H k j (realTimeClamp z.2) z.1) (fun k => N k j)
    (fun k => hN k j) (fun k => hNI k j) θ
  let C := ∑ k,|θ k| * K
  have hC : 0≤C := Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) hK)
  have hGb j z : |G j z|≤C := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro k _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hHb k j _ _) (abs_nonneg _)
  have hd := bounded_given_integral_density P B G hGm hGp C hC hGb M (fun j => (hMb j).1)
    (fun j => (hMb j).2) R hR
  have he w : Real.exp ((∑ j,M j (realTimeClamp R) w)-(∫ r in 0..R,∑ j,(G j (w,r))^2)/2)=
      Real.exp (quadraticLogLikelihood
        (fun k l => ∫ r in 0..R,∑ j,H k j (realTimeClamp r) w*H l j (realTimeClamp r) w)
        (fun k => ∑ j,N k j (realTimeClamp R) w) θ) := by
    have hc := likelihood_energy_gram (fun k j r => H k j (realTimeClamp r) w) R hR
      (fun k j => ((hHc k j w).comp real_time_clamp_continuous).continuousOn) θ
    change Real.exp ((∑ j,∑ k,θ k*N k j (realTimeClamp R) w)-(∫ r in 0..R,∑ j,(∑ k,θ k*H k j (realTimeClamp r) w)^2)/2)=_
    rw [hc,Finset.sum_comm]
    simp only [quadraticLogLikelihood,dotProduct,mul_sum]
  simpa only [he] using hd

end Asakura.Chapter6
