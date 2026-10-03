import Chapter4C12DensityIto

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4

/-- Finite sums in the generator commute with time integration. -/
theorem generator_integral_identity {d : ℕ} (r : ℝ)
    (a D : ℝ → ℝ) (b : Fin d → ℝ → ℝ) (g : Fin d → Fin d → ℝ → ℝ)
    (ha : IntervalIntegrable a volume 0 r)
    (hb : ∀ i,IntervalIntegrable (b i) volume 0 r)
    (hg : ∀ i j,IntervalIntegrable (g i j) volume 0 r)
    (he : ∀ s∈uIcc 0 r,a s+(∑ i,b i s)+(∑ i,∑ j,g i j s)/2=D s) :
    (∫ s in 0..r,a s)+(∑ i,∫ s in 0..r,b i s)+(∑ i,∑ j,∫ s in 0..r,g i j s)/2=∫ s in 0..r,D s := by
  have hb' : IntervalIntegrable (fun s => ∑ i,b i s) volume 0 r := by
    convert IntervalIntegrable.sum Finset.univ (fun i _ => hb i) using 1
    ext s
    simp only [Finset.sum_apply]
  have hg' : IntervalIntegrable (fun s => ∑ i,∑ j,g i j s) volume 0 r := by
    convert IntervalIntegrable.sum Finset.univ (fun i _ =>
      IntervalIntegrable.sum Finset.univ (fun j _ => hg i j)) using 1
    ext s
    simp only [Finset.sum_apply]
  have hgi' i : IntervalIntegrable (fun s => ∑ j,g i j s) volume 0 r := by
    convert IntervalIntegrable.sum Finset.univ (fun j _ => hg i j) using 1
    ext s
    simp only [Finset.sum_apply]
  have hi : (∫ s in 0..r,a s+(∑ i,b i s)+(∑ i,∑ j,g i j s)/2)=∫ s in 0..r,D s :=
    intervalIntegral.integral_congr he
  rw [intervalIntegral.integral_add (ha.add hb') (hg'.div_const 2),
    intervalIntegral.integral_add ha hb',intervalIntegral.integral_div] at hi
  rw [intervalIntegral.integral_finsetSum (fun i _ => hb i),
    intervalIntegral.integral_finsetSum (fun i _ => hgi' i)] at hi
  simp_rw [intervalIntegral.integral_finsetSum (fun j _ => hg _ j)] at hi
  exact hi

end Asakura.Chapter4
