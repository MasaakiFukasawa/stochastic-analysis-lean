import Chapter9JacobiDerivative
import Chapter9ReverseGenerator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory Set
namespace Asakura.Chapter9
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- Constancy on a closed interval uses continuity at both endpoints and
actual derivatives in its interior. -/
theorem interval_constant_of_zero_derivative (f : ℝ → ℝ) (T : ℝ) (hT : 0≤T)
    (hc : ContinuousOn f (Icc 0 T)) (hd : ∀ s∈Ioo 0 T,HasDerivAt f 0 s) : f T=f 0 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT hc hd
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0:ℝ)) volume 0 T)
  simpa only [intervalIntegral.integral_zero,sub_eq_zero] using h.symm

/-- The variational equation gives the exponential Jacobian formula.
In particular positivity is derived and invertibility is not an input. -/
theorem variational_determinant_formula {n : Type*} [Fintype n] [DecidableEq n]
    (J A : ℝ → Matrix n n ℝ) (hcJ : Continuous J) (hcA : Continuous A)
    (T : ℝ) (hT : 0≤T)
    (hJ : ∀ s∈Ioo 0 T,HasDerivAt J (A s * J s) s) :
    (J T).det=(J 0).det*Real.exp (∫ s in 0..T,(A s).trace) := by
  let b := fun s => (A s).trace
  have hb : Continuous b := by dsimp [b,Matrix.trace]; fun_prop
  let B := fun t => ∫ s in 0..t,b s
  have hB t : HasDerivAt B (b t) t :=
    intervalIntegral.integral_hasDerivAt_right (hb.intervalIntegrable 0 t)
      hb.aestronglyMeasurable.stronglyMeasurableAtFilter hb.continuousAt
  have hcB : Continuous B := continuous_iff_continuousAt.mpr (fun t => (hB t).continuousAt)
  let q := fun t => (J t).det*Real.exp (-B t)
  have hq : Continuous q := by dsimp [q]; fun_prop
  have hd s (hs : s∈Ioo 0 T) : HasDerivAt q 0 s := by
    have hh := (determinant_variational_derivative J (A s) s (hJ s hs)).mul
      (hB s).neg.exp
    convert hh using 1 <;> dsimp [q,b] <;> ring
  have he := interval_constant_of_zero_derivative q T hT hq.continuousOn hd
  have he' : (J T).det*Real.exp (-B T)=(J 0).det := by simpa [q,B] using he
  have hh := congrArg (fun r : ℝ => r*Real.exp (B T)) he'
  simpa only [mul_assoc,←Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one] using hh

 theorem variational_determinant_positive {n : Type*} [Fintype n] [DecidableEq n]
    (J A : ℝ → Matrix n n ℝ) (hcJ : Continuous J) (hcA : Continuous A)
    (T : ℝ) (hT : 0≤T) (h0 : J 0=1)
    (hJ : ∀ s∈Ioo 0 T,HasDerivAt J (A s * J s) s) : 0<(J T).det := by
  rw [variational_determinant_formula J A hcJ hcA T hT hJ,h0,Matrix.det_one,one_mul]
  exact Real.exp_pos _

/-- Density times the actual matrix determinant is conserved along a
variational flow whenever the density satisfies its along-path equation. -/
theorem density_jacobian_conservation {n : Type*} [Fintype n] [DecidableEq n]
    (J A : ℝ → Matrix n n ℝ) (p : ℝ → ℝ)
    (hcJ : Continuous J) (hcp : Continuous p) (T : ℝ) (hT : 0≤T)
    (hJ : ∀ s∈Ioo 0 T,HasDerivAt J (A s * J s) s)
    (hp : ∀ s∈Ioo 0 T,HasDerivAt p (-p s*(A s).trace) s) :
    p T*(J T).det=p 0*(J 0).det := by
  apply interval_constant_of_zero_derivative _ T hT
  · exact (hcp.mul (by fun_prop : Continuous (fun s => (J s).det))).continuousOn
  · intro s hs
    exact transported_density_derivative p (fun r => (J r).det) s (A s).trace
      (hp s hs) (determinant_variational_derivative J (A s) s (hJ s hs))
end Asakura.Chapter9
