import Chapter6AffineDensity
import Chapter6PositiveRealDensity

open MeasureTheory Set Filter
open scoped ENNReal
namespace Asakura.Chapter6
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem affine_marginal_lower_bound {d : ℕ}
    (μ ν : Measure (Fin d → ℝ)) (L : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) (x : Fin d → ℝ)
    (g q a : (Fin d → ℝ) → ℝ) (hgm : Measurable g) (hqm : Measurable q) (ham : Measurable a)
    (hgp : ∀ y,0<g y) (hμ : μ=volume.withDensity (fun y => ENNReal.ofReal (g y)))
    (hν : ν=μ.withDensity (fun y => ENNReal.ofReal (q y))) (hqa : ∀ᵐ y ∂μ,a y≤q y) :
    let G := fun y => |(LinearMap.det L.toLinearMap)⁻¹| * g (L.symm (y-x))
    let p := fun y => G y*q (L.symm (y-x))
    (∀ y,0<G y) ∧
    μ.map (affineMeasurableEquiv L x)=volume.withDensity (fun y => ENNReal.ofReal (G y)) ∧
    ν.map (affineMeasurableEquiv L x)=volume.withDensity (fun y => ENNReal.ofReal (p y)) ∧
    (∀ᵐ y ∂(volume : Measure (Fin d → ℝ)),G y*a (L.symm (y-x))≤p y) := by
  let e := affineMeasurableEquiv L x
  let G := fun y => |(LinearMap.det L.toLinearMap)⁻¹| * g (L.symm (y-x))
  let p := fun y => G y*q (L.symm (y-x))
  have hdet : 0 < |(LinearMap.det L.toLinearMap)⁻¹| := abs_pos.mpr (inv_ne_zero L.toLinearEquiv.isUnit_det'.ne_zero)
  have hGp y : 0<G y := mul_pos hdet (hgp _)
  have hGm : Measurable G := measurable_const.mul (hgm.comp (L.symm.continuous.measurable.comp (measurable_id.sub_const x)))
  have hbase : μ.map e=volume.withDensity (fun y => ENNReal.ofReal (G y)) := by
    rw [hμ]
    exact affine_map_real_density L x g hgm
  have hν' : ν=volume.withDensity (fun y => ENNReal.ofReal (g y*q y)) := by
    rw [hν,hμ,←withDensity_mul _ hgm.ennreal_ofReal hqm.ennreal_ofReal]
    congr 1
    funext y
    exact (ENNReal.ofReal_mul (hgp y).le).symm
  have htarget : ν.map e=volume.withDensity (fun y => ENNReal.ofReal (p y)) := by
    rw [hν']
    have hm : Measurable (fun y => g y*q y) := hgm.mul hqm
    rw [affine_map_real_density L x (fun y => g y*q y) hm]
    congr 1
    funext y
    dsimp [p,G]
    rw [mul_assoc]
  have hmap : ∀ᵐ y ∂μ.map e,a (e.symm y)≤q (e.symm y) := by
    apply (ae_map_iff e.measurable.aemeasurable (measurableSet_le (ham.comp e.symm.measurable) (hqm.comp e.symm.measurable))).2
    simpa only [Function.comp_def,e.symm_apply_apply] using hqa
  have hvol := (positive_real_density_ae_iff volume (μ.map e) G hGm (ae_of_all _ hGp) hbase _).mpr hmap
  refine ⟨hGp,hbase,htarget,?_⟩
  filter_upwards [hvol] with y hy
  have he : e.symm y=L.symm (y-x) := by
    change L.symm (-x+y)=L.symm (y-x)
    congr 1
    abel
  rw [he] at hy
  exact mul_le_mul_of_nonneg_left hy (hGp y).le

end Asakura.Chapter6
