import Chapter12CompactProgressiveExtension

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter2Written Asakura.Chapter2Complete
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000

theorem compact_zero_extension_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ) (hT : 0≤T)
    (f g : Ω × Icc (0:ℝ) T → ℝ)
    (he : f=ᵐ[P.prod (compactTimeMeasure T hT)] g) :
    compactZeroExtension T hT f=ᵐ[P.prod (volume.restrict (Ioi (0:ℝ)))]
      compactZeroExtension T hT g := by
  have hp := (MeasurePreserving.id P).prod (compact_time_proj_preserving T hT)
  have hh := hp.quasiMeasurePreserving.ae_eq_comp he
  have hm : (P.prod (volume.restrict (Ioi (0:ℝ)))).restrict
      (Prod.snd ⁻¹' Iic T) = P.prod ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T)) := by
    rw [show (Prod.snd ⁻¹' Iic T : Set (Ω × ℝ))=univ ×ˢ Iic T by ext z;simp,
      ←Measure.prod_restrict,Measure.restrict_univ]
  apply (ae_eq_restrict_iff_indicator_ae_eq (measurableSet_Iic.preimage measurable_snd)).mp
  rw [hm]
  exact hh

theorem compact_zero_extension_eLpNorm {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ) (hT : 0≤T)
    (f : Ω × Icc (0:ℝ) T → ℝ)
    (hf : AEStronglyMeasurable f (P.prod (compactTimeMeasure T hT))) :
    eLpNorm (compactZeroExtension T hT f) 2 (P.prod (volume.restrict (Ioi (0:ℝ))))=
      eLpNorm f 2 (P.prod (compactTimeMeasure T hT)) := by
  change eLpNorm ((Prod.snd ⁻¹' Iic T).indicator (fun z : Ω × ℝ => f (z.1,projIcc 0 T hT z.2))) 2 _ = _
  rw [eLpNorm_indicator_eq_eLpNorm_restrict (measurableSet_Iic.preimage measurable_snd)]
  rw [show (Prod.snd ⁻¹' Iic T : Set (Ω × ℝ))=univ ×ˢ Iic T by ext z;simp,
    ←Measure.prod_restrict,Measure.restrict_univ]
  exact eLpNorm_comp_measurePreserving hf ((MeasurePreserving.id P).prod (compact_time_proj_preserving T hT))

noncomputable def compactEnergyIsometry {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ) (hT : 0≤T) [Fact (0≤T)]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (c : ℕ → ℝ) :
    let Fc := fun t : Icc (0:ℝ) T => F (realTimeClamp t.val)
    letI : MeasurableSpace (Ω × Icc (0:ℝ) T) := progressiveSpace Fc
    Lp ℝ 2 ((P.prod (compactTimeMeasure T hT)).trim
      (progressive_space_le_product Fc (fun t => hle _))) →ₗᵢ[ℝ]
    progressiveEnergyRange F c (P.prod (volume.restrict (Ioi (0:ℝ)))) := by
  dsimp only
  let Fc := fun t : Icc (0:ℝ) T => F (realTimeClamp t.val)
  let μ := P.prod (volume.restrict (Ioi (0:ℝ)))
  let L := compactProgressiveEnergy P T hT F hF hle c
  let J := fun U => (⟨progressiveEnergyToLp F c μ (L U),LinearMap.mem_range_self _ (L U)⟩ : progressiveEnergyRange F c μ)
  have hj U : ((J U : Lp ℝ 2 μ) : Ω × ℝ → ℝ)=ᵐ[μ] compactZeroExtension T hT U :=
    (L U).property.2.2.coeFn_toLp
  refine { toLinearMap := { toFun := J,map_add' := ?_,map_smul' := ?_ },norm_map' := ?_ }
  · intro U V
    apply Subtype.ext
    apply Lp.ext
    have hh := compact_zero_extension_ae P T hT (↑↑(U+V)) (fun z => U z+V z)
      (ae_eq_of_ae_eq_trim (Lp.coeFn_add U V))
    filter_upwards [hj (U+V),hj U,hj V,Lp.coeFn_add (J U : Lp ℝ 2 μ) (J V : Lp ℝ 2 μ),hh] with z h1 h2 h3 h4 h5
    change (J (U+V) : Lp ℝ 2 μ) z = ((J U : Lp ℝ 2 μ)+(J V : Lp ℝ 2 μ)) z
    rw [h1,h4,Pi.add_apply,h2,h3,h5]
    by_cases hz : z.2∈Iic T <;> simp [compactZeroExtension,hz]
  · intro a U
    apply Subtype.ext
    apply Lp.ext
    have hh := compact_zero_extension_ae P T hT (↑↑(a • U)) (fun z => a • U z)
      (ae_eq_of_ae_eq_trim (Lp.coeFn_smul a U))
    filter_upwards [hj (a • U),hj U,Lp.coeFn_smul a (J U : Lp ℝ 2 μ),hh] with z h1 h2 h3 h4
    change (J (a • U) : Lp ℝ 2 μ) z = (a • (J U : Lp ℝ 2 μ)) z
    rw [h1,h3,Pi.smul_apply,h2,h4]
    by_cases hz : z.2∈Iic T <;> simp [compactZeroExtension,hz]
  · intro U
    change ‖(L U).property.2.2.toLp _‖=‖U‖
    rw [Lp.norm_toLp,Lp.norm_def]
    congr 1
    change eLpNorm (compactZeroExtension T hT U) 2 _ = _
    rw [compact_zero_extension_eLpNorm]
    · exact (eLpNorm_trim _ (Lp.stronglyMeasurable U)).symm
    · exact ((Lp.stronglyMeasurable U).measurable.mono
        (progressive_space_le_product Fc (fun t => hle _)) le_rfl).aestronglyMeasurable

end Asakura.Chapter12
