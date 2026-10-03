import Chapter5BSDEFiniteEnergyData
import Chapter5FrozenQuotient

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 3800000
set_option backward.isDefEq.respectTransparency false

/-- Equality of finite-horizon drivers for the sample-time measure lets
us use the desired pointwise driver in the semimartingale data. The
actual paths and Ito integral stay the same; the drift identities are
transported via almost-everywhere equality of all time primitives. -/
noncomputable def BSDEFiniteEnergyData.replaceFiniteDriver
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (F : ClosedTime T → MeasurableSpace Ω)
    (W : ClosedTime T → Ω → ℝ) (c : ℕ → ℝ) (hc : ∀ j,0≤c j) (R : ℝ)
    (u : BSDEFiniteEnergyData P F W c R) (G : Ω × ℝ → ℝ) (hGm : Measurable G)
    (he : u.B =ᵐ[P.prod (volume.restrict (Ioc 0 R))] G) : BSDEFiniteEnergyData P F W c R := by
  let B := fun z : Ω × ℝ => if z.2∈Icc 0 R then G z else u.B z
  have hBm : Measurable B := Measurable.ite (measurableSet_Icc.preimage measurable_snd) hGm u.measurableB
  have hec : ∀ j,∀ᵐ w ∂P,(fun r => B (w,r)) =ᵐ[volume.restrict (Ioc 0 (c j))] fun r => u.B (w,r) := by
    intro j
    filter_upwards [Measure.ae_ae_of_ae_prod he] with w hw
    have hi := (ae_restrict_iff' measurableSet_Ioc).mp hw
    filter_upwards [ae_restrict_of_ae hi,ae_restrict_mem measurableSet_Ioc] with r hr hrj
    by_cases hrr : r≤R
    · exact (show B (w,r)=G (w,r) from if_pos ⟨hrj.1.le,hrr⟩).trans (hr ⟨hrj.1,hrr⟩).symm
    · exact if_neg (fun h => hrr h.2)
  have heR : B =ᵐ[P.prod (volume.restrict (Ioc 0 R))] u.B := by
    have hs : ∀ᵐ z ∂P.prod (volume.restrict (Ioc 0 R)),z.2∈Ioc 0 R := by
      apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_snd)).mpr
      exact ae_of_all _ fun _ => ae_restrict_mem measurableSet_Ioc
    filter_upwards [he,hs] with z hz hr
    exact (if_pos ⟨hr.1.le,hr.2⟩).trans hz.symm
  refine { u with
    B := B
    measurableB := hBm
    energyB := u.energyB.ae_eq heR.symm
    integrableB := ?_
    drift := ?_ }
  · intro j
    filter_upwards [u.integrableB j,hec j] with w hw hew
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (hc j)).mpr
      (((intervalIntegrable_iff_integrableOn_Ioc_of_le (hc j)).mp hw).congr hew.symm)
  · intro j
    filter_upwards [u.drift j,hec j] with w hw hew
    intro r hr
    rw [hw r hr]
    congr 1
    simp only [intervalIntegral.integral_of_le hr.1]
    exact integral_congr_ae (ae_mono (Measure.restrict_mono (Ioc_subset_Ioc_right hr.2) le_rfl) hew.symm)

end Asakura.Chapter5
