import EndToEndGaussianSmoothedTests
import EndToEndGaussianFirstMoment
import EndToEndSmoothingTestBound
import Chapter7CramerWold

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BoundedContinuousFunction NNReal
namespace Asakura.EndToEnd
open Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

/-- The appendix's Gaussian-smoothing proof of weak convergence from
 characteristic functions. The proof does not invoke Levy convergence. -/
theorem characteristic_smoothing_convergence {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : ℕ → Measure E) (ν : Measure E)
    [∀ n,IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    (hlim : ∀ ξ,Tendsto (fun n => charFun (μ n) ξ) atTop (𝓝 (charFun ν ξ))) :
    Tendsto (fun n => (μ n).toProbabilityMeasure) atTop
      (𝓝 ν.toProbabilityMeasure) := by
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  intro f hfb hfl
  obtain ⟨L,hL⟩ := hfl
  let φ : E →ᵇ ℝ := ⟨⟨f,hL.continuous⟩,hfb⟩
  let γ := volume.withDensity (fun x : E => ENNReal.ofReal (normalizedGaussianKernel (1/4) x))
  letI : IsProbabilityMeasure γ :=
    (normalized_gaussian_kernel_properties (E:=E) (1/4) (by norm_num)).2.2.2.2.2
  have hg : Integrable (fun x : E => ‖x‖) γ := gaussian_kernel_first_moment
  let C := (L:ℝ)*(∫ x,‖x‖ ∂γ)
  have hC : 0 ≤ C := mul_nonneg L.property (integral_nonneg (fun _ => norm_nonneg _))
  change Tendsto (fun n => ∫ x,φ x ∂μ n) atTop (𝓝 (∫ x,φ x ∂ν))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let r := ε/(8*(C+1))
  have hr : 0 < r := div_pos hε (by positivity)
  have hrEq : r*(8*(C+1))=ε := div_mul_cancel₀ ε (by positivity)
  have hrsmall : 2*r*C < ε/2 := by nlinarith
  have ht := gaussian_smoothed_tests μ ν hlim r hr φ
  have hevent := Metric.tendsto_nhds.mp ht (ε/2) (by positivity)
  filter_upwards [hevent] with n hn
  have h1 := smoothing_test_bound (μ n) γ hg φ L hL r
  have h2 := smoothing_test_bound ν γ hg φ L hL r
  rw [abs_of_pos hr] at h1 h2
  have h1' : |(∫ x,φ x ∂μ n)-(∫ z : E × E,φ (z.1+r • z.2) ∂(μ n).prod γ)| ≤ r*C := by
    rw [abs_sub_comm]
    dsimp only [C]
    nlinarith [h1]
  have h2' : |(∫ z : E × E,φ (z.1+r • z.2) ∂ν.prod γ)-(∫ x,φ x ∂ν)| ≤ r*C := by
    dsimp only [C]
    nlinarith [h2]
  rw [Real.dist_eq] at hn ⊢
  have htri := abs_sub_le (∫ x,φ x ∂μ n)
    (∫ z : E × E,φ (z.1+r • z.2) ∂(μ n).prod γ) (∫ x,φ x ∂ν)
  have htri' := abs_sub_le (∫ z : E × E,φ (z.1+r • z.2) ∂(μ n).prod γ)
    (∫ z : E × E,φ (z.1+r • z.2) ∂ν.prod γ) (∫ x,φ x ∂ν)
  nlinarith

/-- Cramer--Wold with the printed Gaussian-smoothing argument, including
 construction of the smoothed laws and removal of the independent noise. -/
theorem cramer_wold_written {Ω Γ ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ] [Fintype ι]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : ℕ → Ω → EuclideanSpace ℝ ι) (Y : Γ → EuclideanSpace ℝ ι)
    (hX : ∀ n,AEMeasurable (X n) P) (hY : AEMeasurable Y Q)
    (h : ∀ v,TendstoInDistribution (fun n w => inner ℝ (X n w) v) atTop
      (fun z => inner ℝ (Y z) v) (fun _ => P) Q) :
    TendstoInDistribution X atTop Y (fun _ => P) Q := by
  letI : ∀ n, IsProbabilityMeasure (P.map (X n)) := fun n => (Measure.isProbabilityMeasure_map_iff (hX n)).mpr inferInstance
  letI : IsProbabilityMeasure (Q.map Y) := (Measure.isProbabilityMeasure_map_iff hY).mpr inferInstance
  refine ⟨hX,hY,?_⟩
  apply characteristic_smoothing_convergence
  intro v
  simpa only [charFun_map_eq_charFun_map_inner_one (hX _) v,
    charFun_map_eq_charFun_map_inner_one hY v] using (h v).tendsto_charFun 1

#print axioms characteristic_smoothing_convergence
#print axioms cramer_wold_written
end Asakura.EndToEnd
