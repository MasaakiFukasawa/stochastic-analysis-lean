import Chapter12UniformCovarianceDeterminant
import Chapter12AllFiniteMoments

open MeasureTheory Matrix
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

/-- Uniform ellipticity gives every finite inverse-determinant moment.
The exceptional null set may depend on neither the vector nor the exponent. -/
theorem covariance_inverse_all_moments {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Ω → Matrix ι ι ℝ) (hm : Measurable (fun w => (A w).det))
    (c : ℝ) (hc : 0<c)
    (hb : ∀ᵐ w ∂P,(A w).IsHermitian ∧
      ∀ v : ι → ℝ,c*(∑ i,(v i)^2)≤∑ i,v i*((A w).mulVec v) i) :
    (∀ᵐ w ∂P,0<(A w).det) ∧
      AllFiniteMoments P (fun w => (A w).det⁻¹) := by
  have hh : ∀ᵐ w ∂P,0<(A w).det ∧
      (A w).det⁻¹≤(c^(Fintype.card ι))⁻¹ := by
    filter_upwards [hb] with w hw
    exact covariance_inverse_determinant_bound (A w) hw.1 c hc hw.2
  refine ⟨hh.mono (fun _ h => h.1),?_⟩
  intro p _
  apply (memLp_const ((c^(Fintype.card ι))⁻¹) :
    MemLp (fun _ : Ω => (c^(Fintype.card ι))⁻¹) p P).mono'
    hm.inv.aestronglyMeasurable
  filter_upwards [hh] with w hw
  change ‖(A w).det⁻¹‖ ≤ (c^(Fintype.card ι))⁻¹
  simpa only [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hw.1)] using hw.2

end Asakura.Chapter12
