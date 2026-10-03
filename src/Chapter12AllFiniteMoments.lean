import Chapter12IBPTestMoments

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def AllFiniteMoments {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) (f : Ω → E) : Prop := ∀ p : ℝ≥0∞, p ≠ ⊤ → MemLp f p P

namespace AllFiniteMoments
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {f g : Ω → ℝ}

theorem const (c : ℝ) : AllFiniteMoments P (fun _ : Ω => c) := fun _ _ => memLp_const c

theorem add (hf : AllFiniteMoments P f) (hg : AllFiniteMoments P g) :
    AllFiniteMoments P (fun w => f w+g w) := fun p hp => (hf p hp).add (hg p hp)

theorem sub (hf : AllFiniteMoments P f) (hg : AllFiniteMoments P g) :
    AllFiniteMoments P (fun w => f w-g w) := fun p hp => (hf p hp).sub (hg p hp)

theorem const_mul (hf : AllFiniteMoments P f) (c : ℝ) :
    AllFiniteMoments P (fun w => c*f w) := fun p hp => (hf p hp).const_mul c

theorem mul (hf : AllFiniteMoments P f) (hg : AllFiniteMoments P g) :
    AllFiniteMoments P (fun w => f w*g w) := by
  intro p hp
  letI := holder_double_exponent p
  exact (hf (2*p) (ENNReal.mul_ne_top (by simp) hp)).mul
    (hg (2*p) (ENNReal.mul_ne_top (by simp) hp))

theorem sq (hf : AllFiniteMoments P f) : AllFiniteMoments P (fun w => f w^2) := by
  have hm := hf.mul hf
  simpa only [pow_two] using hm

theorem call (hf : AllFiniteMoments P f) (K : ℝ) :
    AllFiniteMoments P (fun w => max (f w-K) 0) := by
  intro p hp
  exact ((hf p hp).sub (memLp_const K)).pos_part

end AllFiniteMoments

/-- The square-integrability assertion for the Monte Carlo integrand
follows from the initial all-order moment estimates, not just L2 duality. -/
theorem asian_weighted_payoffs_memLp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (I0 I1 I2 J0 J1 WT : Ω → ℝ)
    (h0 : AllFiniteMoments P I0) (h2 : AllFiniteMoments P I2)
    (hj0 : AllFiniteMoments P J0) (hj1 : AllFiniteMoments P J1)
    (hw : AllFiniteMoments P WT) (hi : AllFiniteMoments P (fun w => (I1 w)⁻¹))
    (x σ T K : ℝ) :
    AllFiniteMoments P (fun w => max (I0 w/T-K) 0*
      ((1/x)*(I0 w*WT w/(σ*I1 w)-1+I0 w*I2 w/(I1 w)^2))) ∧
    AllFiniteMoments P (fun w => max (I0 w/T-K) 0*
      (J0 w*WT w/(σ*I1 w)-J1 w/I1 w-1/σ+J0 w*I2 w/(I1 w)^2)) := by
  have hp := (h0.const_mul (1/T)).call K
  have hd := (((h0.mul hw).mul hi).const_mul (1/σ) |>.sub (AllFiniteMoments.const 1)).add
    ((h0.mul h2).mul hi.sq)
  have hv := ((((hj0.mul hw).mul hi).const_mul (1/σ)).sub (hj1.mul hi) |>.sub
    (AllFiniteMoments.const (1/σ))).add ((hj0.mul h2).mul hi.sq)
  constructor
  · convert hp.mul (hd.const_mul (1/x)) using 1
    funext w
    simp only [div_eq_mul_inv,mul_inv_rev,inv_pow]
    ring
  · convert hp.mul hv using 1
    funext w
    simp only [div_eq_mul_inv,mul_inv_rev,inv_pow]
    ring

end Asakura.Chapter12
