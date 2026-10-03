import Chapter8PhaseVolume
import Mathlib.MeasureTheory.Measure.WithDensity

open MeasureTheory
open scoped ENNReal
namespace Asakura.Chapter8
set_option maxHeartbeats 1400000

theorem density_map_equiv {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure E) (ν : Measure F) (e : E ≃ᵐ F) (he : MeasurePreserving e μ ν)
    (ρ : F → ℝ≥0∞) : (μ.withDensity (fun x => ρ (e x))).map e=ν.withDensity ρ := by
  ext s hs
  rw [Measure.map_apply e.measurable hs,withDensity_apply _ (e.measurable hs),withDensity_apply _ hs]
  exact he.setLIntegral_comp_preimage_emb e.measurableEmbedding ρ s

/-- A density factoring in position and velocity becomes the product
measure under the volume-preserving phase coordinates. -/
theorem phase_product_density {d : ℕ} (f g : (Fin d → ℝ) → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hp : ∀ x,0≤f x) (hq : ∀ x,0≤g x) :
    ((volume : Measure (Fin (d+d) → ℝ)).withDensity
      (fun z => ENNReal.ofReal (f (positionProjection d z)*g (velocityProjection d z)))).map
        (phaseMeasurableEquiv d)=
      (volume.withDensity (fun x => ENNReal.ofReal (f x))).prod
        (volume.withDensity (fun x => ENNReal.ofReal (g x))) := by
  rw [prod_withDensity hf.ennreal_ofReal hg.ennreal_ofReal]
  have he : (fun z : Fin (d+d) → ℝ => ENNReal.ofReal (f (positionProjection d z)*g (velocityProjection d z)))=
      fun z => ENNReal.ofReal (f (phaseMeasurableEquiv d z).1)*ENNReal.ofReal (g (phaseMeasurableEquiv d z).2) := by
    funext z
    rw [ENNReal.ofReal_mul (hp _)]
    rfl
  rw [he]
  exact density_map_equiv (volume : Measure (Fin (d+d) → ℝ))
    (volume : Measure ((Fin d → ℝ) × (Fin d → ℝ))) (phaseMeasurableEquiv d) (phase_volume_preserving d)
    (fun p : (Fin d → ℝ) × (Fin d → ℝ) => ENNReal.ofReal (f p.1)*ENNReal.ofReal (g p.2))

end Asakura.Chapter8
