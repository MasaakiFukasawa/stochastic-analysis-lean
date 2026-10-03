import Chapter8BrownianForcingPath
import Chapter8DominatedItoGrid
import Chapter8ProbabilitySquareLimit
import Chapter8ProbabilityMeasureChange
import Chapter8ProbabilityLinear
import Chapter8ContinuousWeightedRiemann
import Chapter6DriftGridIdentity

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators NNReal
namespace Asakura.Chapter8
open Asakura.Chapter6 Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Identify the changed Brownian integral by left sums and convergence
in probability. Absolute continuity suffices for the change of measure. -/
theorem ito_change_endpoint_probability {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hQP : Q ≪ P)
    {d : ℕ} (B : BrownianSystem P d) (BQ : BrownianSystem Q d) (hF : BQ.F=B.F) (j : Fin d)
    (H N M : HalfClosedTime → Ω → ℝ)
    (hHa : ∀ t,Measurable[B.F t] (H t)) (hHc : ∀ w,Continuous (fun t => H t w))
    (hN : LocalMProcessWitness P B.F N) (hM : LocalMProcessWitness Q BQ.F M)
    (hNI : ItoCovarianceFormula P B.F (B.W j) (fun z => H (realTimeClamp z.2) z.1) N)
    (hMI : ItoCovarianceFormula Q BQ.F (BQ.W j) (fun z => H (realTimeClamp z.2) z.1) M)
    (R : ℝ) (hR : 0<R) (KP KQ : Ω → ℝ)
    (hKP : MemLp KP 2 P) (hKQ : MemLp KQ 2 Q) (hKPp : ∀ w,0≤KP w) (hKQp : ∀ w,0≤KQ w)
    (hHP : ∀ w r,r∈Icc 0 R → |H (realTimeClamp r) w|≤KP w)
    (hHQb : ∀ w r,r∈Icc 0 R → |H (realTimeClamp r) w|≤KQ w)
    (β : Ω × ℝ → ℝ) (hβm : Measurable β) (hβc : ∀ w,Continuous (fun r => β (w,r)))
    (hW : ∀ r,r∈Icc 0 R → B.W j (realTimeClamp r)=ᵐ[Q]
      fun w => BQ.W j (realTimeClamp r) w+∫ s in 0..r,β (w,s)) :
    N (realTimeClamp R)=ᵐ[Q] fun w => M (realTimeClamp R) w+∫ r in 0..R,H (realTimeClamp r) w*β (w,r) := by
  have hHQ t : Measurable[BQ.F t] (H t) := by rw [hF]; exact hHa t
  let SP := fun n w => ∑ k∈range (n+1),H (realTimeClamp ((k:ℝ)*(R/(n+1)))) w*
    (B.W j (realTimeClamp (((k:ℝ)+1)*(R/(n+1)))) w-B.W j (realTimeClamp ((k:ℝ)*(R/(n+1)))) w)
  let SQ := fun n w => ∑ k∈range (n+1),H (realTimeClamp ((k:ℝ)*(R/(n+1)))) w*
    (BQ.W j (realTimeClamp (((k:ℝ)+1)*(R/(n+1)))) w-BQ.W j (realTimeClamp ((k:ℝ)*(R/(n+1)))) w)
  let U := fun n w => ∑ k∈range (n+1),H (realTimeClamp ((k:ℝ)*(R/(n+1)))) w*
    ∫ r in (k:ℝ)*(R/(n+1))..((k:ℝ)+1)*(R/(n+1)),β (w,r)
  let A := fun w => ∫ r in 0..R,H (realTimeClamp r) w*β (w,r)
  have hLP := dominated_ito_grid_square_limit P B j H N hHa hHc hN hNI R hR KP hKP hKPp hHP
  have hLQ := dominated_ito_grid_square_limit Q BQ j H M hHQ hHc hM hMI R hR KQ hKQ hKQp hHQb
  have hHm t : Measurable (H t) := (hHa t).mono (B.le _) le_rfl
  have hSP n : Measurable (SP n) := by
    apply Finset.measurable_sum
    intro k _
    apply (hHm _).mul
    exact (((B.martingale j).adapted P B.F _ (half_real_time_finite _)).mono (B.le _) le_rfl).sub
      (((B.martingale j).adapted P B.F _ (half_real_time_finite _)).mono (B.le _) le_rfl)
  have hP : TendstoInMeasure Q SP atTop (N (realTimeClamp R)) :=
    probability_absolutely_continuous P Q hQP SP _ (fun n => (hSP n).aestronglyMeasurable)
      (probability_of_square_error P SP _ hLP.1 hLP.2)
  have hQ : TendstoInMeasure Q SQ atTop (M (realTimeClamp R)) :=
    probability_of_square_error Q SQ _ hLQ.1 hLQ.2
  have hUm n : Measurable (U n) := by
    apply Finset.measurable_sum
    intro k _
    apply (hHm _).mul
    simp_rw [intervalIntegral.integral_of_le (show (k:ℝ)*(R/(n+1))≤((k:ℝ)+1)*(R/(n+1)) by
      have : 0≤R/((n:ℝ)+1) := by positivity
      nlinarith)]
    exact (show StronglyMeasurable (Function.uncurry (fun w r => β (w,r))) from hβm.stronglyMeasurable).integral_prod_right.measurable
  have hU : TendstoInMeasure Q U atTop A := by
    apply tendstoInMeasure_of_tendsto_ae (fun n => (hUm n).aestronglyMeasurable)
    exact ae_of_all _ (fun w => continuous_weighted_riemann R hR _ _
      ((hHc w).comp real_time_clamp_continuous) (hβc w))
  have he n : SP n=ᵐ[Q] fun w => SQ n w+U n w := drift_grid_sum_identity Q
    (fun r => B.W j (realTimeClamp r)) (fun r => BQ.W j (realTimeClamp r))
    (fun r => H (realTimeClamp r)) β R hR (fun w => (hβc w).intervalIntegrable _ _) hW n
  have hsum := probability_add_filter Q atTop SQ U _ A hQ hU
  have hsum' : TendstoInMeasure Q SP atTop (fun w => M (realTimeClamp R) w+A w) :=
    TendstoInMeasure.congr (fun n => (he n).symm) (Filter.Eventually.of_forall (fun _ => rfl)) hsum
  exact tendstoInMeasure_ae_unique hP hsum'
end Asakura.Chapter8
