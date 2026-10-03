import Chapter6GridPrefix

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped Topology ENNReal NNReal BigOperators
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

lemma covariance_congr_ae {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {X X' Y Y' : Ω → ℝ} (hx : X=ᵐ[P] X') (hy : Y=ᵐ[P] Y') :
    cov[X,Y;P]=cov[X',Y';P] := by
  unfold covariance
  rw [integral_congr_ae hx,integral_congr_ae hy]
  apply integral_congr_ae
  filter_upwards [hx,hy] with w hx hy
  rw [hx,hy]

/-- Gaussianity and the exact covariance of arbitrary coordinates at
finitely many times on one grid, for the original Brownian process. -/
theorem brownian_grid_samples_gaussian {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P d)
    (h : ℝ) (hh : 0≤h) (k : ι → ℕ) (hk : ∀ i,k i≤n) (j : ι → Fin d) :
    let X := fun w i => B.W (j i) (realTimeClamp ((k i:ℝ)*h)) w
    HasGaussianLaw X P ∧ (∀ i,(∫ w,X w i ∂P)=0) ∧
      (∀ i l,cov[(fun w => X w i),(fun w => X w l);P]=if j i=j l then (min (k i) (k l):ℕ)*h else 0) := by
  let Z := finiteNoiseGrid (fun i r => B.W i (realTimeClamp r)) h n
  let L : (Fin n → Fin d → ℝ) →L[ℝ] (ι → ℝ) := ContinuousLinearMap.pi (fun i => gridPrefix (k i) (j i))
  have he i : (fun w => gridPrefix (k i) (j i) (Z w))=ᵐ[P] B.W (j i) (realTimeClamp ((k i:ℝ)*h)) :=
    gridPrefix_brownian_sample P B h (k i) (hk i) (j i)
  have hall : (fun w => L (Z w))=ᵐ[P] (fun w i => B.W (j i) (realTimeClamp ((k i:ℝ)*h)) w) := by
    filter_upwards [ae_all_iff.mpr he] with w hw
    funext i
    exact hw i
  have hg := (brownian_grid_has_gaussian_law P B h hh n).map L
  refine ⟨hg.congr hall,?_,?_⟩
  · intro i
    rw [← integral_congr_ae (he i)]
    exact (brownian_grid_linear_moments P B h hh n (gridPrefix (k i) (j i))).1
  · intro i l
    rw [← covariance_congr_ae P (he i) (he l)]
    have hv := brownian_grid_linear_covariance P B h hh n (gridPrefix (k i) (j i)) (gridPrefix (k l) (j l))
    rw [gridPrefix_covariance_sum (k i) (k l) (hk i) (hk l) (j i) (j l)] at hv
    simpa only [mul_ite,mul_zero,mul_comm] using hv

end Asakura.Chapter6
