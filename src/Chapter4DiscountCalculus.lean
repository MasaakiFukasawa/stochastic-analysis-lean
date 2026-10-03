import Chapter4LinearODEFactor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory Set
open scoped Topology
namespace Asakura.Chapter4
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

noncomputable def discountFactor (k : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-(∫ r in 0..t,k r))

lemma discount_factor_derivative (k : ℝ → ℝ) (hk : Continuous k) (t : ℝ) :
    HasDerivAt (discountFactor k) (-k t*discountFactor k t) t := by
  have hi := intervalIntegral.integral_hasDerivAt_right (hk.intervalIntegrable 0 t)
    hk.stronglyMeasurable.stronglyMeasurableAtFilter hk.continuousAt
  convert hi.neg.exp using 1 <;> (try funext r) <;> (try dsimp only [discountFactor,Pi.neg_apply]) <;> ring

lemma discount_factor_continuous (k : ℝ → ℝ) (hk : Continuous k) :
    Continuous (discountFactor k) :=
  continuous_iff_continuousAt.mpr fun t => (discount_factor_derivative k hk t).continuousAt

lemma discount_factor_zero (k : ℝ → ℝ) : discountFactor k 0=1 := by
  simp [discountFactor]

lemma discount_factor_bounds (k : ℝ → ℝ) (t : ℝ) (ht : 0≤t)
    (hk : ∀ r∈Icc 0 t,0≤k r) : 0<discountFactor k t ∧ discountFactor k t≤1 := by
  refine ⟨Real.exp_pos _,Real.exp_le_one_iff.mpr ?_⟩
  apply neg_nonpos.mpr
  apply intervalIntegral.integral_nonneg ht
  intro r hr
  exact hk r hr

/-- Ordinary integration by parts for the finite-variation part of a
discounted semimartingale. -/
theorem discount_primitive_product (k b : ℝ → ℝ) (hk : Continuous k) (hb : Continuous b)
    (a t : ℝ) :
    discountFactor k t*(a+∫ r in 0..t,b r)=a+
      ∫ r in 0..t,discountFactor k r*(b r-k r*(a+∫ s in 0..r,b s)) := by
  let B : ℝ → ℝ := fun r => a+∫ s in 0..r,b s
  have hB r : HasDerivAt B (b r) r := by
    simpa only [zero_add] using
      (intervalIntegral.integral_hasDerivAt_right (hb.intervalIntegrable 0 r)
        hb.stronglyMeasurable.stronglyMeasurableAtFilter hb.continuousAt).const_add a
  have hBc : Continuous B := continuous_iff_continuousAt.mpr fun r => (hB r).continuousAt
  have hder r : HasDerivAt (fun s => discountFactor k s*B s)
      (discountFactor k r*(b r-k r*B r)) r := by
    convert (discount_factor_derivative k hk r).mul (hB r) using 1 <;> ring
  have hcont : Continuous (fun r => discountFactor k r*(b r-k r*B r)) :=
    (discount_factor_continuous k hk).mul (hb.sub (hk.mul hBc))
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r (_ : r∈uIcc 0 t) => hder r) (hcont.intervalIntegrable 0 t)
  simp only [discount_factor_zero,one_mul,B,intervalIntegral.integral_same,add_zero] at hi
  linarith

end Asakura.Chapter4
