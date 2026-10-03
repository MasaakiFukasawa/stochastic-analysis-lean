import Chapter2CappedStieltjes
import Chapter2WeightedIntegralFormula
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 1000000

/-- Measurability of a pathwise integral without a uniform bound on the
random Stieltjes mass. On each path the capped measures are eventually
identical to the original measure. -/
theorem random_stieltjes_integral_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (a b : ℝ) (hab : a ≤ b) (A : Ω → ℝ → ℝ)
    (hA : ∀ ω, MonotoneOn (A ω) (Icc a b))
    (hc : ∀ ω, ContinuousOn (A ω) (Icc a b))
    (hm : ∀ r, Measurable (fun ω => A ω r))
    (f : Ω × ℝ → ℝ) (hf : Measurable f) :
    Measurable (fun ω => ∫ r, f (ω,r) ∂(intervalStieltjes a b hab (A ω) (hA ω)
      (fun r hr => (hc ω r hr).mono inter_subset_left)).measure) := by
  let B := fun n : ℕ => fun ω => cappedPath a (n:ℝ) (A ω)
  let hBn := fun n ω => capped_path_monotone a b (n:ℝ) (A ω) (hA ω)
  let hBc := fun n ω => capped_path_continuous a b (n:ℝ) (A ω) (hc ω)
  let hBr := fun n ω r (hr : r ∈ Icc a b) =>
    (hBc n ω r hr).mono (inter_subset_left (t := Ici r))
  let hBm := fun n r => capped_path_measurable a (n:ℝ) A hm r
  let κ := fun n => randomStieltjesKernel a b hab (B n) (hBn n) (hBr n) (hBm n)
  have hfin n : IsFiniteKernel (κ n) := random_stieltjes_kernel_finite a b hab
    (B n) (hBn n) (hBr n) (hBm n) n
      (fun ω => capped_path_mass_bound a b n (A ω) (Nat.cast_nonneg n))
  have hmeas n : Measurable (fun ω => ∫ r, f (ω,r) ∂κ n ω) := by
    letI := hfin n
    exact hf.stronglyMeasurable.integral_kernel_prod_right'.measurable
  apply measurable_of_tendsto_metrizable hmeas
  apply tendsto_pi_nhds.2
  intro ω
  obtain ⟨N,hN⟩ := exists_nat_ge (A ω b-A ω a)
  have he : (fun n => ∫ r, f (ω,r) ∂κ n ω) =ᶠ[atTop]
      fun _ => ∫ r, f (ω,r) ∂(intervalStieltjes a b hab (A ω) (hA ω)
        (fun r hr => (hc ω r hr).mono inter_subset_left)).measure := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have hg : A ω b-A ω a ≤ (n:ℝ) := hN.trans (by exact_mod_cast hn)
    have he := capped_stieltjes_measure_agrees a b n hab (Nat.cast_nonneg n)
      (A ω) (hA ω) (hc ω) hg
    change (∫ r, f (ω,r) ∂(intervalStieltjes a b hab (B n ω) (hBn n ω) (hBr n ω)).measure) = _
    rw [he]
  exact tendsto_const_nhds.congr' he.symm

/-- A measurable nonnegative error converging almost surely to zero
also converges to zero at every positive probability threshold. -/
theorem nonnegative_ae_limit_probability
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (R : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (R n))
    (hn : ∀ n ω, 0 ≤ R n ω)
    (hl : ∀ᵐ ω ∂P, Tendsto (fun n => R n ω) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => P {ω | ε ≤ R n ω}) atTop (𝓝 0) := by
  have h := tendstoInMeasure_of_tendsto_ae (μ := P)
    (fun n => (hm n).aestronglyMeasurable) hl (ENNReal.ofReal ε)
      (ENNReal.ofReal_pos.2 hε)
  have he n : {ω | ENNReal.ofReal ε ≤ edist (R n ω) (0:ℝ)} = {ω | ε ≤ R n ω} := by
    ext ω
    simp only [mem_setOf_eq, edist_dist, Real.dist_eq, sub_zero, abs_of_nonneg (hn n ω)]
    exact ENNReal.ofReal_le_ofReal_iff (hn n ω)
  simpa only [he] using h

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.random_stieltjes_integral_measurable
#print axioms Asakura.Chapter2Complete.nonnegative_ae_limit_probability
