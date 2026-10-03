import Chapter5ExpectedEnergy

open MeasureTheory Set Filter
namespace Asakura.Chapter5
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Integrate the manuscript's pointwise Young bound. Integrability of the
mixed generator term is deduced from the three square energies. -/
theorem integrated_young_generator_bound
    {S : Type*} [MeasurableSpace S] (μ : Measure S)
    (w y z d f : S → ℝ)
    (hw : AEStronglyMeasurable w μ) (hy : AEStronglyMeasurable y μ)
    (hf : AEStronglyMeasurable f μ) (hw0 : ∀ᵐ x ∂μ, 0 ≤ w x)
    (iy : Integrable (fun x => w x*y x^2) μ)
    (iz : Integrable (fun x => w x*z x^2) μ)
    (id : Integrable (fun x => w x*d x^2) μ)
    (C l m : ℝ) (hC : 0 ≤ C) (hl : 0 < l) (hm : 0 < m)
    (hbound : ∀ᵐ x ∂μ, |f x| ≤ C*(|y x|+|z x|)+|d x|) :
    Integrable (fun x => 2*w x*y x*f x) μ ∧
      (∫ x, 2*w x*y x*f x ∂μ) ≤
        (2*C+C*l+m)*(∫ x, w x*y x^2 ∂μ)+
        (C/l)*(∫ x, w x*z x^2 ∂μ)+(∫ x, w x*d x^2 ∂μ)/m := by
  let R := fun x => (2*C+C*l+m)*(w x*y x^2)+(C/l)*(w x*z x^2)+(w x*d x^2)/m
  have iR : Integrable R μ := ((iy.const_mul _).add (iz.const_mul _)).add (id.div_const m)
  have hdom : ∀ᵐ x ∂μ, ‖2*w x*y x*f x‖ ≤ R x := by
    filter_upwards [hw0,hbound] with x hx hfx
    rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),abs_of_nonneg hx]
    calc
      _ ≤ 2*w x*|y x| *(C*(|y x|+|z x|)+|d x|) :=
        mul_le_mul_of_nonneg_left hfx (by positivity)
      _ = w x*(2*|y x| *(C*(|y x|+|z x|)+|d x|)) := by ring
      _ ≤ w x*((2*C+C*l+m)*(y x)^2+C/l*(z x)^2+(d x)^2/m) :=
        mul_le_mul_of_nonneg_left (young_generator_bound C l m (y x) (z x) (d x) hC hl hm) hx
      _ = R x := by dsimp [R]; ring
  have ih : Integrable (fun x => 2*w x*y x*f x) μ := by
    exact iR.mono' (((hw.const_mul 2).mul hy).mul hf) hdom
  refine ⟨ih,?_⟩
  have he : (∫ x, R x ∂μ) = (2*C+C*l+m)*(∫ x,w x*y x^2 ∂μ)+
      (C/l)*(∫ x,w x*z x^2 ∂μ)+(∫ x,w x*d x^2 ∂μ)/m := by
    dsimp [R]
    rw [integral_add (f := fun x => (2*C+C*l+m)*(w x*y x^2)+(C/l)*(w x*z x^2))
      (g := fun x => (w x*d x^2)/m) ((iy.const_mul _).add (iz.const_mul _)) (id.div_const m),
      integral_add (iy.const_mul (2*C+C*l+m)) (iz.const_mul (C/l)),integral_const_mul,integral_const_mul,integral_div]
  rw [← he]
  apply integral_mono_ae ih iR
  exact hdom.mono fun x hx => (le_abs_self _).trans hx

end Asakura.Chapter5
