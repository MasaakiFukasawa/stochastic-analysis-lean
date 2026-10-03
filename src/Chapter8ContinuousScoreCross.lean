import Chapter6ContinuousVectorCovariance
import Chapter6ContinuousVectorConstruction

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
  Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false

/-- Cross brackets of two vector stochastic integrals. The coefficients
are continuous and adapted; no boundedness assumption is imposed. -/
theorem continuous_score_cross {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (H G : Fin d → Ω × ℝ → ℝ)
    (hHm : ∀ i,Measurable (H i)) (hGm : ∀ i,Measurable (G i))
    (hHc : ∀ i w,Continuous (fun r => H i (w,r)))
    (hGc : ∀ i w,Continuous (fun r => G i (w,r)))
    (N M : Fin d → HalfClosedTime → Ω → ℝ)
    (hN : ∀ i,LocalMProcessWitness P B.F (N i))
    (hM : ∀ i,LocalMProcessWitness P B.F (M i))
    (hNI : ∀ i,ItoCovarianceFormula P B.F (B.W i) (H i) (N i))
    (hMI : ∀ i,ItoCovarianceFormula P B.F (B.W i) (G i) (M i)) :
    ∃ C,LocalCovarianceWitness P B.F (fun t w => ∑ i,N i t w)
      (fun t w => ∑ i,M i t w) C ∧
      ∀ b : ℝ,0 ≤ b → C (realTimeClamp b)=ᵐ[P] fun w => ∫ r in 0..b,∑ i,H i (w,r)*G i (w,r) := by
  classical
  have hT : (0:EReal)<⊤ := by simp
  have hi i w b (hb : 0≤b) : IntervalIntegrable (fun r => G i (w,r)) volume 0 b :=
    (hGc i w).intervalIntegrable _ _
  choose A hA hAe using fun i j => measurable_ito_clock_cross P B.F (B.W i) (B.W j) (M i) (B.C i j)
    (B.martingale j) (hM i) (B.cov i j) (G i) (hMI i) (i=j) (B.clock i j) (hi i)
  have hAC i j (b : ℝ) (hb : 0≤b) : ∀ᵐ w ∂P,∀ r ∈ Icc 0 b,
      A i j (realTimeClamp r) w=∫ s in 0..r,(if i=j then G i (w,s) else 0) := by
    apply covariance_density_common_time P B.F (M i) (B.W j) (A i j) (hM i) (B.martingale j) (hA i j)
      (fun z => if i=j then G i z else 0) _ _ b hb
    · intro b hb
      exact ae_of_all _ fun w => by
        split_ifs
        · exact hi _ w b hb
        · exact intervalIntegrable_const
    · intro r hr
      by_cases hij : i=j <;> simpa [hij] using hAe i j r hr
  have hpair i j : ∃ D,LocalCovarianceWitness P B.F (N i) (M j) D ∧ ∀ b : ℝ,0≤b →
      D (realTimeClamp b)=ᵐ[P] fun w => ∫ r in 0..b,H i (w,r)*(if j=i then G j (w,r) else 0) := by
    apply measurable_ito_covariance_density P B.F (B.W i) (M j) (N i) (A j i) (hM j)
      ((hA j i).symm P B.F) (H i) (fun z => if j=i then G j z else 0)
      (fun w => (hHm i).comp measurable_prodMk_left)
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
        · exact ((hHc i w).mul (hGc j w)).intervalIntegrable _ _
        · simpa only [mul_zero] using (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0:ℝ)) volume 0 b)
    · exact hAC j i
  choose D hD hDe using hpair
  refine ⟨fun t w => ∑ j,∑ i,D i j t w,
    covariance_two_finite_sums P hT B.F B.mono B.le N M D hD,?_⟩
  intro b hb
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => hDe i j b hb))] with w hw
  have he j : (∑ i,D i j (realTimeClamp b) w)=∫ r in 0..b,H j (w,r)*G j (w,r) := by
    simp_rw [hw]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [Ne.symm hij]
    · simp
  simp_rw [he]
  symm
  apply intervalIntegral.integral_finsetSum
  intro i _
  exact ((hHc i w).mul (hGc i w)).intervalIntegrable _ _

end Asakura.Chapter8
