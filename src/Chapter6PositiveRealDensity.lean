import Chapter6DensityMartingale

open MeasureTheory Set Filter
open scoped ENNReal
namespace Asakura.Chapter6

lemma positive_real_density_ae_iff
    {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω)
    (D : Ω → ℝ) (hm : Measurable D) (hp : ∀ᵐ w ∂P,0 < D w)
    (hQ : Q = P.withDensity (fun w => ENNReal.ofReal (D w))) (p : Ω → Prop) :
    (∀ᵐ w ∂P,p w) ↔ ∀ᵐ w ∂Q,p w := by
  let d := fun w => (D w).toNNReal
  have hd : Measurable d := hm.real_toNNReal
  have hdp : ∀ᵐ w ∂P,0 < (d w:ℝ) := hp.mono fun w hw => by
    simpa only [d,Real.coe_toNNReal _ hw.le] using hw
  rw [hQ]
  exact (positive_density_ae_iff P d hd hdp p).symm

lemma null_sets_transfer_to_equivalent_measure
    {Ω ι : Type*} {m : MeasurableSpace Ω} (P Q : Measure Ω)
    (F : ι → MeasurableSpace Ω)
    (hnull : ∀ t E,MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    (he : ∀ p : Ω → Prop,(∀ᵐ w ∂P,p w) ↔ ∀ᵐ w ∂Q,p w) :
    ∀ t E,MeasurableSet[m] E → Q E = 0 → MeasurableSet[F t] E := by
  intro t E hm hz
  apply hnull t E hm
  have hq : ∀ᵐ w ∂Q,w ∉ E := by simpa only [ae_iff,not_not,Set.setOf_mem_eq] using hz
  have hp := (he _).mpr hq
  simpa only [ae_iff,not_not,Set.setOf_mem_eq] using hp

end Asakura.Chapter6
