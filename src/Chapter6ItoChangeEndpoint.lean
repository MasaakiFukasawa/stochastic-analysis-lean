import Chapter6BoundedContinuousItoMoment
import Chapter6DensityL1Limit
import Chapter6WeightedRiemannL1
import Chapter6ThreeL1Limits
import Chapter6DriftGridIdentity
import Chapter6SquareMeanToL1

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators NNReal ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

/-- Directly identify the changed-measure Ito integral at the observation
time by the actual left sums. The drift term is derived from the driver identity. -/
theorem ito_change_endpoint {Ω : Type*} {m : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {d : ℕ}
    (B : BrownianSystem P d) (BQ : BrownianSystem Q d) (hF : BQ.F=B.F) (j : Fin d)
    (density : Ω → ℝ≥0) (hd : Measurable density)
    (hQ : Q=P.withDensity (fun w => (density w:ℝ≥0∞))) (hd2 : MemLp (fun w => (density w:ℝ)) 2 P)
    (H N M : HalfClosedTime → Ω → ℝ)
    (hHa : ∀ t,Measurable[B.F t] (H t)) (hHc : ∀ w,Continuous (fun t => H t w))
    (hN : LocalMProcessWitness P B.F N) (hM : LocalMProcessWitness Q BQ.F M)
    (hNI : ItoCovarianceFormula P B.F (B.W j) (fun z => H (realTimeClamp z.2) z.1) N)
    (hMI : ItoCovarianceFormula Q BQ.F (BQ.W j) (fun z => H (realTimeClamp z.2) z.1) M)
    (K L : ℝ) (hK : 0≤K) (hL : 0≤L) (hHb : ∀ t w,|H t w|≤K)
    (β : Ω × ℝ → ℝ) (hβm : Measurable β) (hβb : ∀ z,|β z|≤L)
    (R : ℝ) (hR : 0<R)
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
  have hLP := continuous_ito_grid_square_limit P B j H N hHa hHc hN hNI R hR K hK (fun w r _ => hHb _ _)
  have hLQ := continuous_ito_grid_square_limit Q BQ j H M hHQ hHc hM hMI R hR K hK (fun w r _ => hHb _ _)
  have hNP := bounded_continuous_ito_terminal_memLp P B j H N hHa hHc hN hNI K hHb R hR.le
  have hMQ := bounded_continuous_ito_terminal_memLp Q BQ j H M hHQ hHc hM hMI K hHb R hR.le
  have hNi := square_integrable_density_transfer P Q density hd hQ hd2 _ hNP
  have hMi := hMQ.integrable (by norm_num)
  have hSP n : Integrable (SP n) Q := by
    have hi := hNi.sub (square_integrable_density_transfer P Q density hd hQ hd2 _ (hLP.1 n))
    convert hi using 1
    funext w
    simp only [Pi.sub_apply]
    ring
  have hSQ n : Integrable (SQ n) Q := by
    have hi := hMi.sub ((hLQ.1 n).integrable (by norm_num))
    convert hi using 1
    funext w
    simp only [Pi.sub_apply]
    ring
  let G := fun z : Ω × ℝ => H (realTimeClamp z.2) z.1
  have hGc w : Continuous (fun r => G (w,r)) := (hHc w).comp real_time_clamp_continuous
  have hGm : Measurable G := by
    have hm r : Measurable (H (realTimeClamp r)) := (hHa _).mono (B.le _) le_rfl
    simpa only [G,Function.comp_def,Function.uncurry_def,Prod.swap] using (measurable_uncurry_of_continuous_of_measurable hGc hm).comp measurable_swap
  have hAi : Integrable A Q := by
    have hi : Integrable (fun z => G z*β z) (Q.prod (volume.restrict (Ioc 0 R))) :=
      Integrable.of_bound (hGm.mul hβm).aestronglyMeasurable (K*L) (ae_of_all _ (fun z => by
        rw [Real.norm_eq_abs,abs_mul]
        exact mul_le_mul (hHb _ _) (hβb _) (abs_nonneg _) hK))
    simpa only [A,G,intervalIntegral.integral_of_le hR.le] using hi.integral_prod_left
  have hβi w := bounded_time_integrable _ (hβm.comp measurable_prodMk_left) L (fun r => hβb (w,r)) R hR.le
  have he n : SP n=ᵐ[Q] fun w => SQ n w+U n w := drift_grid_sum_identity Q
    (fun r => B.W j (realTimeClamp r)) (fun r => BQ.W j (realTimeClamp r)) (fun r => H (realTimeClamp r)) β R hR hβi hW n
  have hUi n : Integrable (U n) Q := (hSP n |>.sub (hSQ n)).congr ((he n).mono (fun w hw => by
    change SP n w-SQ n w=U n w
    linarith))
  apply three_L1_limits_identity Q _ _ A hNi hMi hAi SP SQ U hSP hSQ hUi he
  · exact density_transfer_square_limit P Q density hd hQ hd2 _ hLP.1 hLP.2
  · simpa only [Real.norm_eq_abs] using square_mean_zero_implies_L1_zero Q _ hLQ.1 hLQ.2
  · exact uniform_weighted_riemann_L1 Q R hR G β hGm hβm (fun w => (hGc w).continuousOn) K L hK hL (fun w r _ => hHb _ _) hβb

end Asakura.Chapter6
