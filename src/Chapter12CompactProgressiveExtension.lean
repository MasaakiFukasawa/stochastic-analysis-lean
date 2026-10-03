import Chapter12AdaptedWienerEmbedding
import Chapter12FiniteCompactTime
import Chapter5ProgressiveZeroExtension
import Chapter2ProgressiveEnergySpace

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter5
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

noncomputable def compactZeroExtension {Ω : Type*} (T : ℝ) (hT : 0≤T)
    (f : Ω × Icc (0:ℝ) T → ℝ) : Ω × ℝ → ℝ :=
  fun z => (Iic T).indicator (fun r => f (z.1,projIcc 0 T hT r)) z.2

theorem compact_zero_extension_memLp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ) (hT : 0≤T)
    (f : Ω × Icc (0:ℝ) T → ℝ)
    (hf : MemLp f 2 (P.prod (compactTimeMeasure T hT))) :
    MemLp (compactZeroExtension T hT f) 2 (P.prod (volume.restrict (Ioi (0:ℝ)))) := by
  have hp := (MeasurePreserving.id P).prod (compact_time_proj_preserving T hT)
  have hh := hf.comp_measurePreserving hp
  have he : (P.prod (volume.restrict (Ioi (0:ℝ)))).restrict
      (Prod.snd ⁻¹' Iic T) = P.prod ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T)) := by
    rw [show (Prod.snd ⁻¹' Iic T : Set (Ω × ℝ))=univ ×ˢ Iic T by ext z;simp,
      ←Measure.prod_restrict,Measure.restrict_univ]
  apply (memLp_indicator_iff_restrict (measurableSet_Iic.preimage measurable_snd)).mpr
  rw [he]
  exact hh

/-- A compact progressive L2 process has an actual progressive extension
by zero in the energy space used to construct the Ito integral. -/
noncomputable def compactProgressiveEnergy {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ) (hT : 0≤T) [Fact (0≤T)]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (c : ℕ → ℝ) :
    let Fc := fun t : Icc (0:ℝ) T => F (realTimeClamp t.val)
    letI : MeasurableSpace (Ω × Icc (0:ℝ) T) := progressiveSpace Fc
    Lp ℝ 2 ((P.prod (compactTimeMeasure T hT)).trim
      (progressive_space_le_product Fc (fun t => hle _))) →
    progressiveEnergyIntegrands F c (P.prod (volume.restrict (Ioi (0:ℝ)))) := by
  dsimp only
  let Fc := fun t : Icc (0:ℝ) T => F (realTimeClamp t.val)
  intro U
  have hu : @Measurable _ _ (progressiveSpace Fc) inferInstance U := (Lp.stronglyMeasurable U).measurable
  have hm : Measurable (U : Ω × Icc (0:ℝ) T → ℝ) :=
    hu.mono (progressive_space_le_product Fc (fun t => hle _)) le_rfl
  have hL : MemLp (U : Ω × Icc (0:ℝ) T → ℝ) 2 (P.prod (compactTimeMeasure T hT)) := by
    exact (Lp.memLp (trimLpIsometry (E:=ℝ) (P.prod (compactTimeMeasure T hT))
      (progressiveSpace Fc) (progressive_space_le_product Fc (fun t => hle _)) U)).ae_eq
        (trimLpIsometry_coe _ _ _ U)
  let H := fun z : Ω × ℝ => U (z.1,projIcc 0 T hT z.2)
  have hH : Measurable H := hm.comp (measurable_fst.prodMk
    (continuous_projIcc.measurable.comp measurable_snd))
  have hp : @Measurable _ _ (progressiveSpace Fc) inferInstance
      (fun z : Ω × Icc (0:ℝ) T => H (z.1,z.2.val)) := by
    convert hu using 1
    funext z
    simp only [H,projIcc_of_mem hT z.2.property]
  refine ⟨compactZeroExtension T hT U,?_,?_,compact_zero_extension_memLp P T hT U hL⟩
  · exact hH.indicator (measurableSet_Iic.preimage measurable_snd)
  · intro n
    exact progressive_finite_zero_extension (fun r => F (realTimeClamp r))
      (hF.comp real_time_clamp_mono) T hT H hp (c n)

end Asakura.Chapter12
