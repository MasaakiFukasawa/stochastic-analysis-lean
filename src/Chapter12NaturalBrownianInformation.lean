import Chapter7NaturalBrownianSystem
import Chapter12NullAugmentationMeasurable
import Chapter12BrownianCylinderDensity

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

variable {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P)
    (hm : ∀ t,Measurable (B t)) (hc : ∀ w,Continuous (fun t => B t w))

theorem natural_brownian_coordinate (T : ℝ) (z : BrownianTimeCoordinates 0 T) (w : Ω) :
    brownianTimeCoordinate P (naturalBrownianSystem P B hB hm hc) T z w=
      B ⟨z.2.val,z.2.property.1⟩ w := by
  change B (halfTimeReal (realTimeClamp z.2.val)) w=_
  congr 1
  exact Subtype.ext (changed_time_real _ z.2.property.1)

theorem natural_brownian_filtration_real (t : ℝ) (ht : 0≤t) :
    (naturalBrownianSystem P B hB hm hc).F (realTimeClamp t)=
      Asakura.nullAugmentation (m := m) P (pastSigma B ⟨t,ht⟩) := by
  change halfClosedFiltration m (fun s => Asakura.nullAugmentation (m := m) P (pastSigma B s))
    (realTimeClamp t)=_
  rw [halfClosedFiltration,if_pos (changed_time_finite t ht)]
  congr 2
  exact Subtype.ext (changed_time_real t ht)

theorem natural_brownian_past_le_coordinates (T : ℝ) (hT : 0≤T) :
    pastSigma B ⟨T,hT⟩ ≤ MeasurableSpace.comap
      (fun w z => brownianTimeCoordinate P (naturalBrownianSystem P B hB hm hc) T z w) inferInstance := by
  apply iSup_le
  intro t
  let z : BrownianTimeCoordinates 0 T := (0,⟨t.val.val,t.val.property,t.property⟩)
  have hz := (measurable_pi_apply z).comp
    (comap_measurable (fun w z => brownianTimeCoordinate P (naturalBrownianSystem P B hB hm hc) T z w))
  have he : (fun w => brownianTimeCoordinate P (naturalBrownianSystem P B hB hm hc) T z w)=B t.val := by
    funext w
    exact natural_brownian_coordinate P B hB hm hc T z w
  simp only [Function.comp_def] at hz
  rw [he] at hz
  exact hz.comap_le

theorem natural_brownian_measurable_information (T : ℝ) (hT : 0≤T) (f : Ω → ℝ)
    (hf : Measurable[(naturalBrownianSystem P B hB hm hc).F (realTimeClamp T)] f) :
    AEStronglyMeasurable[MeasurableSpace.comap
      (fun w z => brownianTimeCoordinate P (naturalBrownianSystem P B hB hm hc) T z w) inferInstance] f P := by
  rw [natural_brownian_filtration_real P B hB hm hc T hT] at hf
  exact (null_augmentation_aestronglyMeasurable P (pastSigma B ⟨T,hT⟩)
    (past_sigma_le B hm _) f hf).mono (natural_brownian_past_le_coordinates P B hB hm hc T hT)

end Asakura.Chapter12
