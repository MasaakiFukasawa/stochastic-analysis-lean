import Chapter12CompactEnergyIsometry
import Chapter12BoundedStepEnergy

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter2Written Asakura.Chapter2Complete
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000

theorem compact_step_zero_extension {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ) (hT : 0≤T)
    (a b : Icc (0:ℝ) T) (G : Ω → ℝ) :
    compactZeroExtension T hT (fun z => (Ico a b).indicator (fun _ => G z.1) z.2)
      =ᵐ[P.prod (volume.restrict (Ioi (0:ℝ)))]
        (fun z => (Ioc a.val b.val).indicator (fun _ => G z.1) z.2) := by
  have ht : ∀ᵐ r ∂volume.restrict (Ioi (0:ℝ)),0<r ∧ r≠a.val ∧ r≠b.val := by
    have hne (x : ℝ) : ∀ᵐ r ∂volume.restrict (Ioi (0:ℝ)),r≠x := by
      rw [ae_iff]
      simpa using (measure_singleton (μ:=volume.restrict (Ioi (0:ℝ))) x)
    filter_upwards [ae_restrict_mem measurableSet_Ioi,hne a.val,hne b.val] with r hr ha hb
    exact ⟨hr,ha,hb⟩
  filter_upwards [(Measure.quasiMeasurePreserving_snd (μ:=P) (ν:=volume.restrict (Ioi (0:ℝ)))).ae ht]
    with z hz
  change (Iic T).indicator (fun r => (Ico a b).indicator (fun _ => G z.1) (projIcc 0 T hT r)) z.2 = _
  by_cases htz : z.2≤T
  · rw [indicator_of_mem (show z.2∈Iic T from htz),projIcc_of_mem hT ⟨hz.1.le,htz⟩]
    have he : (⟨z.2,hz.1.le,htz⟩ : Icc (0:ℝ) T)∈Ico a b ↔ z.2∈Ioc a.val b.val := by
      change (a.val≤z.2 ∧ z.2<b.val) ↔ (a.val<z.2 ∧ z.2≤b.val)
      constructor
      · intro h; exact ⟨lt_of_le_of_ne h.1 hz.2.1.symm,h.2.le⟩
      · intro h; exact ⟨h.1.le,lt_of_le_of_ne h.2 hz.2.2⟩
    by_cases h : z.2∈Ioc a.val b.val <;> simp [h,he]
  · have hb : z.2∉Ioc a.val b.val := fun h => htz (h.2.trans b.property.2)
    simp [htz,hb]

theorem compact_energy_elementary {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ) (hT : 0<T) [Fact (0≤T)]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (c : ℕ → ℝ) (a b : Icc (0:ℝ) T) (G : Ω → ℝ)
    (hG : Measurable[F (realTimeClamp a.val)] G) (hGinf : MemLp G ∞ P) :
    compactEnergyIsometry P T hT.le F hF hle c
      (timeElementaryLp P T hT (fun t => F (realTimeClamp t.val))
        (hF.comp (real_time_clamp_mono.comp (Subtype.mono_coe _))) (fun _ => hle _) a b G hG hGinf) =
    ⟨progressiveEnergyToLp F c _ (boundedStepEnergy P F hF hle c a.val b.val G hG hGinf),
      LinearMap.mem_range_self _ _⟩ := by
  apply Subtype.ext
  apply Lp.ext
  have hu := (time_elementary_memLp P T hT (fun t => F (realTimeClamp t.val))
    (hF.comp (real_time_clamp_mono.comp (Subtype.mono_coe _))) (fun _ => hle _) a b G hG hGinf).coeFn_toLp
  have he := compact_zero_extension_ae P T hT.le _ _ (ae_eq_of_ae_eq_trim hu)
  exact ((compactProgressiveEnergy P T hT.le F hF hle c _).property.2.2.coeFn_toLp).trans
    (he.trans ((compact_step_zero_extension P T hT.le a b G).trans
      (boundedStepEnergy P F hF hle c a.val b.val G hG hGinf).property.2.2.coeFn_toLp.symm))

end Asakura.Chapter12
