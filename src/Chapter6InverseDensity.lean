import Chapter6DensityMartingale

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace Asakura.Chapter6
open Asakura.FullAudit
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Integrability of the reciprocal density follows by cancellation under P;
no moment of the reciprocal under P is needed. -/
theorem inverse_density_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P]
    (d : Ω → ℝ≥0) (hd : Measurable d)
    (hp : ∀ᵐ w ∂P,0 < (d w : ℝ))
    (hQ : Q = P.withDensity (fun w => (d w : ℝ≥0∞))) :
    Integrable (fun w => (d w : ℝ)⁻¹) Q := by
  rw [hQ]
  apply (integrable_withDensity_iff_integrable_coe_smul hd).mpr
  apply (integrable_const (1 : ℝ)).congr
  filter_upwards [hp] with w hw
  simp only [smul_eq_mul]
  exact (mul_inv_cancel₀ (ne_of_gt hw)).symm

/-- The reciprocal conditional density in the printed symmetry argument. -/
theorem inverse_density_conditional {Ω : Type*} {G m : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hG : G ≤ m) (d : Ω → ℝ≥0) (hd : Measurable d)
    (hi : Integrable (fun w => (d w : ℝ)) P)
    (hp : ∀ᵐ w ∂P,0 < (d w : ℝ))
    (hQ : Q = P.withDensity (fun w => (d w : ℝ≥0∞))) :
    Q[(fun w => (d w : ℝ)⁻¹)|G] =ᵐ[P] fun w => (P[(fun w => (d w : ℝ))|G] w)⁻¹ := by
  letI : MeasurableSpace Ω := m
  have hb := bayes_written_with_unbounded_pullout P Q hG d hd hi hp hQ _
    (inverse_density_integrable P Q d hd hp hQ)
  have he : (fun w => (d w : ℝ)*(d w : ℝ)⁻¹) =ᵐ[P] (fun _ => (1:ℝ)) :=
    hp.mono fun _ hw => mul_inv_cancel₀ (ne_of_gt hw)
  have hce := (condExp_congr_ae (m := G) he).trans
    (Filter.EventuallyEq.of_eq (condExp_const (μ := P) hG (1:ℝ)))
  filter_upwards [hb,hce] with w hb hc
  rw [hb,hc,one_div]

/-- Reversing the change of measure recovers P exactly. -/
theorem inverse_density_measure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (d : Ω → ℝ≥0) (hd : Measurable d)
    (hp : ∀ᵐ w ∂P,0 < (d w : ℝ)) :
    (P.withDensity (fun w => (d w : ℝ≥0∞))).withDensity
      (fun w => ((d w : ℝ≥0∞))⁻¹) = P := by
  apply withDensity_inv_same hd.coe_nnreal_ennreal _ (ae_of_all _ fun _ => ENNReal.coe_ne_top)
  filter_upwards [hp] with w hw
  intro hz
  have hz' : d w = 0 := ENNReal.coe_eq_zero.mp hz
  simp [hz'] at hw


/-- The reversed density in the nonnegative-real convention used by Bayes. -/
theorem inverse_nnreal_density_measure {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) (d : Ω → ℝ≥0) (hd : Measurable d)
    (hp : ∀ᵐ w ∂P,0 < (d w : ℝ))
    (hQ : Q = P.withDensity (fun w => (d w : ℝ≥0∞))) :
    P = Q.withDensity (fun w => (((d w)⁻¹ : ℝ≥0) : ℝ≥0∞)) := by
  have he : (fun w => (((d w)⁻¹ : ℝ≥0) : ℝ≥0∞)) =ᵐ[Q] (fun w => (d w : ℝ≥0∞)⁻¹) := by
    rw [hQ]
    apply (positive_density_ae_iff P d hd hp _).mpr
    filter_upwards [hp] with w hw
    exact ENNReal.coe_inv (ne_of_gt (show 0 < d w from hw))
  rw [withDensity_congr_ae he,hQ,inverse_density_measure P d hd hp]

end Asakura.Chapter6
