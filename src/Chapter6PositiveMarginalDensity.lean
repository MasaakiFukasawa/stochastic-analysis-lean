import Chapter6ConditionalPushforwardDensity

open MeasureTheory Set Filter
open scoped ENNReal
namespace Asakura.Chapter6
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Multiply the reference marginal density by the positive conditional
density. This is the marginal-density formula in the Girsanov application. -/
theorem positive_marginal_density {Ω E : Type*} {m : MeasurableSpace Ω} [MeasurableSpace E]
    (P Q : Measure Ω) [IsProbabilityMeasure P] (ν : Measure E)
    (X : Ω → E) (hX : Measurable X) (g : E → ℝ) (hgm : Measurable g)
    (hgp : ∀ᵐ y ∂ν,0<g y) (hbase : P.map X=ν.withDensity (fun y => ENNReal.ofReal (g y)))
    (D : Ω → ℝ) (hD : Integrable D P) (hp : ∀ᵐ w ∂P,0<D w)
    (hQ : Q=P.withDensity (fun w => ENNReal.ofReal (D w))) :
    ∃ r : E → ℝ,Measurable r ∧
      P[D|MeasurableSpace.comap X inferInstance]=r ∘ X ∧
      (∀ᵐ y ∂ν,0<g y*r y) ∧
      Q.map X=ν.withDensity (fun y => ENNReal.ofReal (g y*r y)) := by
  obtain ⟨r,hr,he,hp',hmap⟩ := conditional_pushforward_density P Q X hX D hD hp hQ
  have hrp : ∀ᵐ y ∂ν,0<r y :=
    (positive_real_density_ae_iff ν (P.map X) g hgm hgp hbase _).mpr hp'
  refine ⟨r,hr,he,hgp.and hrp |>.mono (fun _ h => mul_pos h.1 h.2),?_⟩
  rw [hmap,hbase,← withDensity_mul ν hgm.ennreal_ofReal hr.ennreal_ofReal]
  apply withDensity_congr_ae
  filter_upwards [hgp] with y hy
  exact (ENNReal.ofReal_mul hy.le).symm

end Asakura.Chapter6
