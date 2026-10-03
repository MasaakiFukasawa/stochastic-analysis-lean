import Chapter6ContinuousVectorCovariance

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- Covariance of the actual time-dependent deterministic vector Ito noise. -/
theorem deterministic_noise_covariance
    {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d n : ℕ} (B : BrownianSystem P n)
    (G : Fin d → Fin n → ℝ → ℝ) (hG : ∀ i j,Continuous (G i j))
    (N : Fin d → Fin n → HalfClosedTime → Ω → ℝ)
    (hN : ∀ i j,LocalMProcessWitness P B.F (N i j))
    (hNI : ∀ i j,ItoCovarianceFormula P B.F (B.W j) (fun z => G i j z.2) (N i j)) :
    ∃ C : Fin d → Fin d → HalfClosedTime → Ω → ℝ,
      (∀ i l,LocalCovarianceWitness P B.F (fun t w => ∑ j,N i j t w)
        (fun t w => ∑ j,N l j t w) (C i l)) ∧
      ∀ i l (b : ℝ),0≤b → ∀ᵐ w ∂P,∀ r∈Icc 0 b,
        C i l (realTimeClamp r) w=∫ s in 0..r,∑ j,G i j s*G l j s := by
  classical
  have hi i j w (b : ℝ) (hb : 0≤b) :
      IntervalIntegrable (fun r => (fun z : Ω × ℝ => G i j z.2) (w,r)) volume 0 b :=
    (hG i j).intervalIntegrable _ _
  choose A hA hAe using fun i j k => measurable_ito_clock_cross P B.F (B.W j) (B.W k)
    (N i j) (B.C j k) (B.martingale k) (hN i j) (B.cov j k)
    (fun z => G i j z.2) (hNI i j) (j=k) (B.clock j k) (hi i j)
  have hAC i j k (b : ℝ) (hb : 0≤b) : ∀ᵐ w ∂P,∀ r∈Icc 0 b,
      A i j k (realTimeClamp r) w=∫ s in 0..r,if j=k then G i j s else 0 := by
    apply covariance_density_common_time P B.F (N i j) (B.W k) (A i j k)
      (hN i j) (B.martingale k) (hA i j k) (fun z => if j=k then G i j z.2 else 0) _ _ b hb
    · intro c hc
      exact ae_of_all _ fun _ => by
        split_ifs
        · exact (hG i j).intervalIntegrable _ _
        · exact intervalIntegrable_const
    · intro r hr
      by_cases hjk : j=k <;> simpa [hjk] using hAe i j k r hr
  have hpair i l j k : ∃ D,LocalCovarianceWitness P B.F (N i j) (N l k) D ∧
      ∀ b : ℝ,0≤b → D (realTimeClamp b) =ᵐ[P]
        fun _ => ∫ s in 0..b,G i j s*(if k=j then G l k s else 0) := by
    apply measurable_ito_covariance_density P B.F (B.W j) (N l k) (N i j) (A l k j)
      (hN l k) ((hA l k j).symm P B.F) (fun z => G i j z.2)
      (fun z => if k=j then G l k z.2 else 0) (fun _ => (hG i j).measurable)
    · intro w
      split_ifs <;> fun_prop
    · exact hNI i j
    · intro b hb
      exact ae_of_all _ fun _ => by
        split_ifs
        · exact (hG l k).intervalIntegrable _ _
        · exact intervalIntegrable_const
    · intro b hb
      exact ae_of_all _ fun _ => by
        split_ifs
        · exact ((hG i j).mul (hG l k)).intervalIntegrable _ _
        · simpa only [mul_zero] using (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0:ℝ)) volume 0 b)
    · exact hAC l k j
  choose D hD hDe using hpair
  let C := fun i l t w => ∑ k,∑ j,D i l j k t w
  have hC i l := covariance_two_finite_sums P (by simp : (0:EReal)<⊤)
    B.F B.mono B.le (N i) (N l) (D i l) (hD i l)
  refine ⟨C,hC,?_⟩
  intro i l b hb
  apply covariance_density_common_time P B.F _ _ (C i l)
    (local_martingale_finset_sum P (by simp) B.F B.mono B.le Finset.univ (N i) (fun j _ => hN i j))
    (local_martingale_finset_sum P (by simp) B.F B.mono B.le Finset.univ (N l) (fun j _ => hN l j))
    (hC i l) (fun z => ∑ j,G i j z.2*G l j z.2) _ _ b hb
  · intro r hr
    exact ae_of_all _ fun _ => (continuous_finsetSum _ (fun j _ => (hG i j).mul (hG l j))).intervalIntegrable _ _
  · intro r hr
    filter_upwards [ae_all_iff.mpr (fun j => ae_all_iff.mpr (fun k => hDe i l j k r hr))] with w hw
    change (∑ k,∑ j,D i l j k (realTimeClamp r) w)=_
    simp_rw [hw]
    have hs k : (∑ j,∫ s in 0..r,G i j s*(if k=j then G l k s else 0))=
        ∫ s in 0..r,G i k s*G l k s := by
      rw [Finset.sum_eq_single k]
      · simp only [ite_true]
      · intro j _ hj
        simp only [if_neg (Ne.symm hj),mul_zero,intervalIntegral.integral_zero]
      · simp
    simp_rw [hs]
    symm
    exact intervalIntegral.integral_finsetSum (fun j _ => ((hG i j).mul (hG l j)).intervalIntegrable _ _)

end Asakura.Chapter10
