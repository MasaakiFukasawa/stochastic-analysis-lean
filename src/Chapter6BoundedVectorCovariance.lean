import Chapter6BoundedIntegrand
import Chapter6CovarianceCommonTime
import Chapter4BrownianSystem
import Chapter4CovarianceSumsDensity

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false

/-- The density exponential's scalar martingale, its bracket and its cross
brackets with every Brownian coordinate, for bounded measurable integrands. -/
theorem bounded_vector_integral_covariances
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {noise : ℕ} (B : BrownianSystem P noise)
    (H : Fin noise → Ω × ℝ → ℝ) (hHm : ∀ i,Measurable (H i))
    (K : ℝ) (hK : 0 ≤ K) (hHb : ∀ i z,|H i z| ≤ K)
    (N : Fin noise → HalfClosedTime → Ω → ℝ)
    (hN : ∀ i,LocalMProcessWitness P B.F (N i))
    (hNI : ∀ i,ItoCovarianceFormula P B.F (B.W i) (H i) (N i)) :
    let Z := fun t w => ∑ i,N i t w
    LocalMProcessWitness P B.F Z ∧
      ∃ (C : HalfClosedTime → Ω → ℝ) (L : Fin noise → HalfClosedTime → Ω → ℝ),LocalCovarianceWitness P B.F Z Z C ∧
        (∀ j,LocalCovarianceWitness P B.F Z (B.W j) (L j)) ∧
        (∀ b : ℝ,0 ≤ b → C (realTimeClamp b) =ᵐ[P] fun w => ∫ r in 0..b,∑ i,(H i (w,r))^2) ∧
        (∀ j (b : ℝ),0 ≤ b → L j (realTimeClamp b) =ᵐ[P] fun w => ∫ r in 0..b,H j (w,r)) := by
  classical
  have hT : (0:EReal) < ⊤ := by simp
  have hm i w : Measurable (fun r => H i (w,r)) := (hHm i).comp measurable_prodMk_left
  have hi i w b hb := bounded_time_integrable _ (hm i w) K (fun r => hHb i (w,r)) b hb
  have hpi i j w b hb := bounded_product_time_integrable _ _ (hm i w) (hm j w) K hK
    (fun r => hHb i (w,r)) (fun r => hHb j (w,r)) b hb
  choose A hA hAe using fun i j => measurable_ito_clock_cross P B.F (B.W i) (B.W j) (N i) (B.C i j)
    (B.martingale j) (hN i) (B.cov i j) (H i) (hNI i) (i=j) (B.clock i j) (hi i)
  have hAC i j (b : ℝ) (hb : 0 ≤ b) : ∀ᵐ w ∂P,∀ r ∈ Icc 0 b,
      A i j (realTimeClamp r) w = ∫ s in 0..r,(if i=j then H i (w,s) else 0) := by
    apply covariance_density_common_time P B.F (N i) (B.W j) (A i j) (hN i) (B.martingale j) (hA i j)
      (fun z => if i=j then H i z else 0) _ _ b hb
    · intro b hb
      exact ae_of_all _ fun w => by
        split_ifs
        · exact hi _ w b hb
        · exact intervalIntegrable_const
    · intro r hr
      by_cases hij : i=j <;> simpa [hij] using hAe i j r hr
  have hpair i j : ∃ D,LocalCovarianceWitness P B.F (N i) (N j) D ∧ ∀ b : ℝ,0 ≤ b →
      D (realTimeClamp b) =ᵐ[P] fun w => ∫ r in 0..b,H i (w,r)*(if j=i then H j (w,r) else 0) := by
    apply measurable_ito_covariance_density P B.F (B.W i) (N j) (N i) (A j i) (hN j)
      ((hA j i).symm P B.F) (H i) (fun z => if j=i then H j z else 0) (hm i)
    · intro w
      split_ifs <;> fun_prop
    · exact hNI i
    · intro b hb
      exact ae_of_all _ fun w => by
        split_ifs
        · exact hi _ w b hb
        · exact intervalIntegrable_const
    · intro b hb
      exact ae_of_all _ fun w => by
        split_ifs
        · exact hpi i j w b hb
        · simpa only [mul_zero] using (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0:ℝ)) volume 0 b)
    · exact hAC j i
  choose D hD hDe using hpair
  let C := fun t w => ∑ j,∑ i,D i j t w
  let L := fun j t w => ∑ i,A i j t w
  have hZ := local_martingale_finset_sum P hT B.F B.mono B.le Finset.univ N (fun i _ => hN i)
  have hC := covariance_two_finite_sums P hT B.F B.mono B.le N N D hD
  have hL j : LocalCovarianceWitness P B.F (fun t w => ∑ i,N i t w) (B.W j) (L j) := by
    simpa only [one_mul] using weighted_covariance_finset_left P hT B.F B.mono B.le Finset.univ
      N (fun i => A i j) (B.W j) (fun _ => 1) (fun i _ => hA i j)
  refine ⟨hZ,C,L,hC,hL,?_,?_⟩
  · intro b hb
    filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => hDe i j b hb))] with w hw
    change (∑ j,∑ i,D i j (realTimeClamp b) w) = _
    have he j : (∑ i,D i j (realTimeClamp b) w) = ∫ r in 0..b,(H j (w,r))^2 := by
      simp_rw [hw]
      rw [Finset.sum_eq_single j]
      · simp only [ite_true,pow_two]
      · intro i _ hij
        have hji : j ≠ i := Ne.symm hij
        simp only [if_neg hji,mul_zero,intervalIntegral.integral_zero]
      · simp
    simp_rw [he]
    symm
    apply intervalIntegral.integral_finsetSum
    intro i _
    simpa only [pow_two] using hpi i i w b hb
  · intro j b hb
    filter_upwards [ae_all_iff.mpr (fun i => hAe i j b hb)] with w hw
    change (∑ i,A i j (realTimeClamp b) w) = _
    simp_rw [hw]
    simp

end Asakura.Chapter6
