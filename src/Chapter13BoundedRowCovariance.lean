import Chapter6BoundedVectorConstruction

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter13
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem bounded_row_cross_covariance {Ω:Type*} {m:MeasurableSpace Ω}
    (P:Measure Ω) [IsProbabilityMeasure P] {d:ℕ} (B:BrownianSystem P d)
    (H G:Fin d → Ω × ℝ → ℝ) (hHm:∀i,Measurable (H i)) (hGm:∀i,Measurable (G i))
    (K:ℝ) (hK:0≤K) (hHb:∀i z,|H i z|≤K) (hGb:∀i z,|G i z|≤K)
    (N M:Fin d → HalfClosedTime → Ω → ℝ)
    (hN:∀i,LocalMProcessWitness P B.F (N i)) (hM:∀i,LocalMProcessWitness P B.F (M i))
    (hNI:∀i,ItoCovarianceFormula P B.F (B.W i) (H i) (N i))
    (hMI:∀i,ItoCovarianceFormula P B.F (B.W i) (G i) (M i)) :
    ∃C,LocalCovarianceWitness P B.F (fun t w => ∑i,N i t w) (fun t w => ∑i,M i t w) C ∧
      ∀b,0≤b → C (realTimeClamp b)=ᵐ[P] (fun w => ∫r in 0..b,∑i,H i (w,r)*G i (w,r)) := by
  classical
  have hT:(0:EReal)<⊤ := by simp
  have hi i w b hb:=bounded_time_integrable _ ((hGm i).comp measurable_prodMk_left) K (fun r => hGb i (w,r)) b hb
  have hpi i j w b hb:=bounded_product_time_integrable _ _ ((hHm i).comp measurable_prodMk_left)
    ((hGm j).comp measurable_prodMk_left) K hK (fun r => hHb i (w,r)) (fun r => hGb j (w,r)) b hb
  choose A hA hAe using fun i j => measurable_ito_clock_cross P B.F (B.W j) (B.W i) (M j) (B.C j i)
    (B.martingale i) (hM j) (B.cov j i) (G j) (hMI j) (j=i) (B.clock j i) (hi j)
  have hAC i j (b:ℝ) (hb:0≤b):∀ᵐw∂P,∀r∈Icc 0 b,
      A i j (realTimeClamp r) w=∫s in 0..r,if j=i then G j (w,s) else 0 := by
    apply covariance_density_common_time P B.F (M j) (B.W i) (A i j) (hM j) (B.martingale i) (hA i j)
      (fun z => if j=i then G j z else 0) _ _ b hb
    · intro b hb
      exact ae_of_all _ fun w => by split_ifs;exact hi j w b hb;exact intervalIntegrable_const
    · intro r hr
      by_cases hij:j=i <;> simpa [hij] using hAe i j r hr
  have hpair i j:∃D,LocalCovarianceWitness P B.F (N i) (M j) D ∧ ∀b,0≤b →
      D (realTimeClamp b)=ᵐ[P] (fun w => ∫r in 0..b,H i (w,r)*(if j=i then G j (w,r) else 0)) := by
    apply measurable_ito_covariance_density P B.F (B.W i) (M j) (N i) (A i j) (hM j)
      ((hA i j).symm P B.F) (H i) (fun z => if j=i then G j z else 0)
      (fun w => (hHm i).comp measurable_prodMk_left)
    · intro w
      split_ifs <;> fun_prop
    · exact hNI i
    · intro b hb
      exact ae_of_all _ fun w => by split_ifs;exact hi j w b hb;exact intervalIntegrable_const
    · intro b hb
      exact ae_of_all _ fun w => by
        split_ifs
        · exact hpi i j w b hb
        · simpa only [mul_zero] using (intervalIntegrable_const : IntervalIntegrable (fun _ :ℝ => (0:ℝ)) volume 0 b)
    · exact hAC i j
  choose D hD hDe using hpair
  refine ⟨(fun t w => ∑j,∑i,D i j t w),covariance_two_finite_sums P hT B.F B.mono B.le N M D hD,?_⟩
  intro b hb
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => hDe i j b hb))] with w hw
  simp only [hw]
  have he j:(∑i,∫r in 0..b,H i (w,r)*(if j=i then G j (w,r) else 0))=∫r in 0..b,H j (w,r)*G j (w,r) := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [Ne.symm hij]
    · simp
  simp_rw [he]
  symm
  exact intervalIntegral.integral_finsetSum (fun i _ => hpi i i w b hb)
end Asakura.Chapter13
#print axioms Asakura.Chapter13.bounded_row_cross_covariance
