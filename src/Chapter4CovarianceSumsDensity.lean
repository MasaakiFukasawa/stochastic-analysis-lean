import Chapter4FiniteCovarianceSum
import Chapter5BracketCommonTime

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem covariance_two_finite_sums
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    {p q : ℕ} (X : Fin p → ClosedTime T → Ω → ℝ) (Y : Fin q → ClosedTime T → Ω → ℝ)
    (C : Fin p → Fin q → ClosedTime T → Ω → ℝ)
    (hC : ∀ i j,LocalCovarianceWitness P F (X i) (Y j) (C i j)) :
    LocalCovarianceWitness P F (fun t w => ∑ i,X i t w) (fun t w => ∑ j,Y j t w)
      (fun t w => ∑ j,∑ i,C i j t w) := by
  have hh j : LocalCovarianceWitness P F (fun t w => ∑ i,X i t w) (Y j)
      (fun t w => ∑ i,C i j t w) := by
    simpa only [one_mul] using weighted_covariance_finset_left P hT F hF hle Finset.univ
      X (fun i => C i j) (Y j) (fun _ => 1) (fun i _ => hC i j)
  have hz := weighted_covariance_finset_left P hT F hF hle Finset.univ Y
    (fun j t w => ∑ i,C i j t w) (fun t w => ∑ i,X i t w) (fun _ => 1)
    (fun j _ => (hh j).symm P F)
  simpa only [one_mul] using hz.symm P F

/-- Densities commute with both finite sums in vector covariation. -/
theorem finite_sum_density_identity {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {T : EReal} [Fact (0≤T)] {p q : ℕ}
    (C : Fin p → Fin q → ClosedTime T → Ω → ℝ) (G : Fin p → Fin q → Ω × ℝ → ℝ)
    (b : ℝ) (hb : 0≤b)
    (hi : ∀ i j,∀ᵐ w ∂P,IntervalIntegrable (fun r => G i j (w,r)) volume 0 b)
    (he : ∀ i j,∀ᵐ w ∂P,∀ r∈Icc 0 b,C i j (realTimeClamp r) w=∫ s in 0..r,G i j (w,s)) :
    ∀ᵐ w ∂P,∀ r∈Icc 0 b,(∑ j,∑ i,C i j (realTimeClamp r) w)=∫ s in 0..r,∑ j,∑ i,G i j (w,s) := by
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (hi i)),
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (he i))] with w hiw hew
  intro r hr
  have his i j : IntervalIntegrable (fun s => G i j (w,s)) volume 0 r :=
    (hiw i j).mono_set (by rw [uIcc_of_le hr.1,uIcc_of_le hb];exact Icc_subset_Icc_right hr.2)
  have hj j : IntervalIntegrable (fun s => ∑ i,G i j (w,s)) volume 0 r := by
    convert IntervalIntegrable.sum Finset.univ (fun i _ => his i j) using 1
    ext s
    simp only [Finset.sum_apply]
  rw [intervalIntegral.integral_finsetSum (fun j _ => hj j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [intervalIntegral.integral_finsetSum (fun i _ => his i j)]
  exact Finset.sum_congr rfl (fun i _ => hew i j r hr)

end Asakura.Chapter4
