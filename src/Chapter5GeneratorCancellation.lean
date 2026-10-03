import Chapter5MultivariateDensityIto

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter5
set_option maxHeartbeats 2200000

/-- A pointwise backward heat equation cancels the actual drift
integrals in the multidimensional Ito formula. -/
theorem integrated_generator_cancellation
    (d : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (B : Fin d → ℝ → ℝ) (G : Fin d → Fin d → ℝ → ℝ)
    (hB : ∀ i,IntervalIntegrable (B i) volume 0 R)
    (hG : ∀ i j,IntervalIntegrable (G i j) volume 0 R)
    (hzero : ∀ r∈Icc 0 R,(∑ i,B i r)+(∑ i,∑ j,G i j r)/2=0) :
    (∑ i,∫ r in 0..R,B i r)+(∑ i,∑ j,∫ r in 0..R,G i j r)/2=0 := by
  have hBg : IntervalIntegrable (fun r => ∑ i,B i r) volume 0 R := by
    convert IntervalIntegrable.sum Finset.univ (fun i _ => hB i) using 1
    ext r; simp only [Finset.sum_apply]
  have hGrow i : IntervalIntegrable (fun r => ∑ j,G i j r) volume 0 R := by
    convert IntervalIntegrable.sum Finset.univ (fun j _ => hG i j) using 1
    ext r; simp only [Finset.sum_apply]
  have hGg : IntervalIntegrable (fun r => ∑ i,∑ j,G i j r) volume 0 R := by
    convert IntervalIntegrable.sum Finset.univ (fun i _ => hGrow i) using 1
    ext r; simp only [Finset.sum_apply]
  calc
    _ = ∫ r in 0..R,(∑ i,B i r)+(∑ i,∑ j,G i j r)/2 := by
      rw [intervalIntegral.integral_add hBg (hGg.div_const 2),intervalIntegral.integral_div]
      simp_rw [intervalIntegral.integral_finsetSum (fun i _ => hB i)]
      rw [intervalIntegral.integral_finsetSum (fun i _ => hGrow i)]
      simp_rw [intervalIntegral.integral_finsetSum (fun j _ => hG _ j)]
    _ = ∫ _r in 0..R,(0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro r hr
      exact hzero r (by simpa [uIcc_of_le hR] using hr)
    _ = 0 := by simp

theorem integrated_generator_cancellation_interval
    (d : ℕ) (a R : ℝ) (hR : a ≤ R)
    (B : Fin d → ℝ → ℝ) (G : Fin d → Fin d → ℝ → ℝ)
    (hB : ∀ i,IntervalIntegrable (B i) volume a R)
    (hG : ∀ i j,IntervalIntegrable (G i j) volume a R)
    (hzero : ∀ r∈Icc a R,(∑ i,B i r)+(∑ i,∑ j,G i j r)/2=0) :
    (∑ i,∫ r in a..R,B i r)+(∑ i,∑ j,∫ r in a..R,G i j r)/2=0 := by
  have hBg : IntervalIntegrable (fun r => ∑ i,B i r) volume a R := by
    convert IntervalIntegrable.sum Finset.univ (fun i _ => hB i) using 1
    ext r; simp only [Finset.sum_apply]
  have hGrow i : IntervalIntegrable (fun r => ∑ j,G i j r) volume a R := by
    convert IntervalIntegrable.sum Finset.univ (fun j _ => hG i j) using 1
    ext r; simp only [Finset.sum_apply]
  have hGg : IntervalIntegrable (fun r => ∑ i,∑ j,G i j r) volume a R := by
    convert IntervalIntegrable.sum Finset.univ (fun i _ => hGrow i) using 1
    ext r; simp only [Finset.sum_apply]
  calc
    _ = ∫ r in a..R,(∑ i,B i r)+(∑ i,∑ j,G i j r)/2 := by
      rw [intervalIntegral.integral_add hBg (hGg.div_const 2),intervalIntegral.integral_div]
      simp_rw [intervalIntegral.integral_finsetSum (fun i _ => hB i)]
      rw [intervalIntegral.integral_finsetSum (fun i _ => hGrow i)]
      simp_rw [intervalIntegral.integral_finsetSum (fun j _ => hG _ j)]
    _ = ∫ _r in a..R,(0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro r hr
      exact hzero r (by simpa [uIcc_of_le hR] using hr)
    _ = 0 := by simp

end Asakura.Chapter5
