import Chapter2CovarianceProbabilityBound
import Chapter2ProbabilityErrorSum
import Chapter2CumulativeBound

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- Cauchy-Schwarz for the actual product integral, in the square-root
notation of the manuscript. No finite-total-mass assumption is needed. -/
theorem integral_product_square_bound
    {S : Type*} [MeasurableSpace S] (μ : Measure S) (f g : S → ℝ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ r, f r*g r ∂μ| ≤ Real.sqrt (∫ r, f r^2 ∂μ)*Real.sqrt (∫ r, g r^2 ∂μ) := by
  have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hf : MemLp f (ENNReal.ofReal 2) μ)
    (by simpa using hg : MemLp g (ENNReal.ofReal 2) μ)
  have hn := norm_integral_le_integral_norm (fun r => f r*g r) (μ := μ)
  simp only [Real.norm_eq_abs,abs_mul] at hn
  have hcs : (∫ r, |f r| * |g r| ∂μ) ≤
      Real.sqrt (∫ r, f r^2 ∂μ)*Real.sqrt (∫ r, g r^2 ∂μ) := by
    simpa only [Real.norm_eq_abs,Real.rpow_two,sq_abs,← Real.sqrt_eq_rpow] using h
  exact hn.trans hcs

/-- The square integral of an approximation is expanded using its error
and the fixed target, with all three integrals justified by L2 membership. -/
theorem integral_square_error_identity
    {S : Type*} [MeasurableSpace S] (μ : Measure S) (f g : S → ℝ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ r, f r^2 ∂μ)-(∫ r, g r^2 ∂μ) =
      (∫ r, (f r-g r)^2 ∂μ)+2*(∫ r, (f r-g r)*g r ∂μ) := by
  have he := hf.sub hg
  have hi := (memLp_two_iff_integrable_sq he.aestronglyMeasurable).1 he
  have hj := (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).1 hg
  have hk := he.integrable_mul hg
  have hfun : (fun r => f r^2) = (fun r => (f r-g r)^2+2*((f r-g r)*g r)+g r^2) := by
    funext r
    ring
  have hadd := integral_add (hi.add (hk.const_mul 2)) hj
  have hadd2 := integral_add hi (hk.const_mul 2)
  simp only [Pi.add_apply,Pi.sub_apply,Pi.mul_apply] at hadd hadd2
  rw [hfun,hadd,hadd2,integral_const_mul]
  ring

/-- Pathwise L2-error convergence in probability implies convergence of
actual square integrals. The target energy is only finite almost surely. -/
theorem square_integral_probability_continuity
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Ω → Measure S)
    (J : ℕ → Ω → S → ℝ) (H : Ω → S → ℝ)
    (hJ : ∀ n, ∀ᵐ ω ∂P, MemLp (J n ω) 2 (μ ω))
    (hH : ∀ᵐ ω ∂P, MemLp (H ω) 2 (μ ω))
    (hm : Measurable (fun ω => ∫ r, H ω r^2 ∂μ ω))
    (he : ∀ δ > 0, Tendsto (fun n => P {ω | δ ≤ ∫ r, (J n ω r-H ω r)^2 ∂μ ω}) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => P {ω | ε ≤ |(∫ r, J n ω r^2 ∂μ ω)-(∫ r, H ω r^2 ∂μ ω)|}) atTop (𝓝 0) := by
  let R := fun n ω => ∫ r, (J n ω r-H ω r)^2 ∂μ ω
  let C := fun n ω => ∫ r, (J n ω r-H ω r)*H ω r ∂μ ω
  have hcp := covariance_probability_from_square_bound P C R (fun ω => ∫ r, H ω r^2 ∂μ ω) hm
    (fun n => by
      filter_upwards [hJ n,hH] with ω hj hh
      exact integral_product_square_bound (μ ω) _ _ (hj.sub hh) hh) he
  apply probability_error_sum_limit P _ R (fun n ω => |C n ω|) 2 (by norm_num) _ he hcp ε hε
  intro n
  filter_upwards [hJ n,hH] with ω hj hh
  rw [integral_square_error_identity (μ ω) _ _ hj hh]
  change |R n ω+2*C n ω| ≤ 2*(R n ω+|C n ω|)
  have hr : 0 ≤ R n ω := integral_nonneg (fun r => sq_nonneg _)
  have h := abs_add_le (R n ω) (2*C n ω)
  rw [abs_of_nonneg hr,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at h
  linarith

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.integral_product_square_bound
#print axioms Asakura.Chapter2Complete.integral_square_error_identity
#print axioms Asakura.Chapter2Complete.square_integral_probability_continuity
