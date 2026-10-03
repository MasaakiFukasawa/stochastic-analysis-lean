import Chapter10KalmanObservationBrownian

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter10
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- The Gaussian conditional increment formula passes to a continuous
terminal limit. This includes the maturity endpoint of the Kyle order flow. -/
theorem conditional_gaussian_characteristic_limit {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (H : MeasurableSpace Ω) (hle : H≤m)
    (X : ℕ → Ω → ℝ) (Y : Ω → ℝ) (hX : ∀ n,Measurable[m] (X n))
    (hlim : ∀ᵐ w ∂P,Tendsto (fun n => X n w) atTop (𝓝 (Y w)))
    (v : ℕ → ℝ) (v0 u : ℝ) (hv : ∀ n,0≤v n) (hvl : Tendsto v atTop (𝓝 v0))
    (he : ∀ n,P[(fun w => Complex.exp (((u*X n w:ℝ):ℂ)*Complex.I))|H]=ᵐ[P]
      fun _ => Complex.exp ((-(v n)*u^2/2:ℝ):ℂ)) :
    P[(fun w => Complex.exp (((u*Y w:ℝ):ℂ)*Complex.I))|H]=ᵐ[P]
      fun _ => Complex.exp ((-v0*u^2/2:ℝ):ℂ) := by
  letI : MeasurableSpace Ω := m
  let fs := fun n w => Complex.exp (((u*X n w:ℝ):ℂ)*Complex.I)
  let gs := fun n (_ : Ω) => Complex.exp ((-(v n)*u^2/2:ℝ):ℂ)
  have hfbound n w : ‖fs n w‖≤(1:ℝ) := by
    simp only [fs,Complex.norm_exp_ofReal_mul_I,le_refl]
  have hgbound n w : ‖gs n w‖≤(1:ℝ) := by
    rw [show gs n w=Complex.exp ((-(v n)*u^2/2:ℝ):ℂ) from rfl,Complex.norm_exp_ofReal]
    exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hv n)) (sq_nonneg u)) (by norm_num))
  have hfi n : Integrable (fs n) P :=
    (integrable_const (1:ℝ)).mono' (Complex.continuous_exp.measurable.comp
      ((Complex.continuous_ofReal.measurable.comp (measurable_const.mul (hX n))).mul measurable_const)).aestronglyMeasurable (ae_of_all _ (hfbound n))
  have hgi n : Integrable (gs n) P := integrable_const _
  have hf : ∀ᵐ w ∂P,Tendsto (fun n => fs n w) atTop
      (𝓝 (Complex.exp (((u*Y w:ℝ):ℂ)*Complex.I))) := by
    filter_upwards [hlim] with w hw
    exact Complex.continuous_exp.continuousAt.tendsto.comp
      ((Complex.continuous_ofReal.continuousAt.tendsto.comp (hw.const_mul u)).mul_const Complex.I)
  have hg : ∀ᵐ w ∂P,Tendsto (fun n => gs n w) atTop
      (𝓝 (Complex.exp ((-v0*u^2/2:ℝ):ℂ))) := by
    apply ae_of_all
    intro w
    exact Complex.continuous_exp.continuousAt.tendsto.comp
      (Complex.continuous_ofReal.continuousAt.tendsto.comp ((hvl.neg.mul_const (u^2)).div_const 2))
  have hh := tendsto_condExp_unique (m := H) (μ := P) fs gs _ _ hfi hgi hf hg
    (fun _ => (1:ℝ)) (integrable_const _) (fun _ => (1:ℝ)) (integrable_const _)
    (fun n => ae_of_all _ (hfbound n)) (fun n => ae_of_all _ (hgbound n)) (by
      intro n
      simpa only [gs,condExp_const hle] using he n)
  simpa only [condExp_const hle] using hh

end Asakura.Chapter10
