import Chapter6MappedDensity
import Mathlib.MeasureTheory.Group.MeasurableEquiv

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter6
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

noncomputable def affineMeasurableEquiv {d : ℕ}
    (L : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) (x : Fin d → ℝ) :
    (Fin d → ℝ) ≃ᵐ (Fin d → ℝ) :=
  L.toHomeomorph.toMeasurableEquiv.trans (MeasurableEquiv.addLeft x)

theorem affine_map_volume {d : ℕ} (L : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) (x : Fin d → ℝ) :
    (volume : Measure (Fin d → ℝ)).map (affineMeasurableEquiv L x)=
      ENNReal.ofReal (|(LinearMap.det L.toLinearMap)⁻¹|) • volume := by
  have hd : LinearMap.det L.toLinearMap≠0 := L.toLinearEquiv.isUnit_det'.ne_zero
  have he : (affineMeasurableEquiv L x : (Fin d → ℝ) → (Fin d → ℝ))=(fun y => x+y) ∘ L := rfl
  rw [he,←Measure.map_map (by fun_prop) L.continuous.measurable]
  have hm : (volume : Measure (Fin d → ℝ)).map L=ENNReal.ofReal (|(LinearMap.det L.toLinearMap)⁻¹|) • volume := Real.map_linearMap_volume_pi_eq_smul_volume_pi hd
  rw [hm,Measure.map_smul,
    Measure.IsAddLeftInvariant.map_add_left_eq_self]
  fun_prop

theorem affine_map_real_density {d : ℕ} (L : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) (x : Fin d → ℝ)
    (g : (Fin d → ℝ) → ℝ) (hg : Measurable g) :
    ((volume : Measure (Fin d → ℝ)).withDensity (fun y => ENNReal.ofReal (g y))).map (affineMeasurableEquiv L x)=
      volume.withDensity (fun y => ENNReal.ofReal (|(LinearMap.det L.toLinearMap)⁻¹| * g (L.symm (y-x)))) := by
  have hgm : Measurable (fun y => ENNReal.ofReal (g ((affineMeasurableEquiv L x).symm y))) := hg.ennreal_ofReal.comp (affineMeasurableEquiv L x).symm.measurable
  rw [measurable_equiv_map_density _ _ _ hg.ennreal_ofReal,affine_map_volume,
    withDensity_smul_measure,←withDensity_smul _ hgm]
  congr 1
  funext y
  simp only [Pi.smul_apply,smul_eq_mul,←ENNReal.ofReal_mul (abs_nonneg _)]
  congr 2
  congr 1
  change L.symm (-x+y)=L.symm (y-x)
  congr 1
  abel

end Asakura.Chapter6
