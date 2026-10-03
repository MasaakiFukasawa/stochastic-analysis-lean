import Chapter12CompactItoIsometry
import Chapter12CompactStepExtension

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000

theorem compact_ito_elementary {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (i : Fin d) (c : ℕ → ℝ)
    (I : progressiveEnergyRange B.F c (P.prod (volume.restrict (Ioi (0:ℝ)))) →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hI : ∀ H : progressiveEnergyIntegrands B.F c (P.prod (volume.restrict (Ioi (0:ℝ)))),
      ∃ N : HalfClosedTime → Ω → ℝ,∃ hN : ContinuousM2Witness P B.F N,
        ItoCovarianceFormula P B.F (B.W i) H.val N ∧
        I ⟨progressiveEnergyToLp B.F c _ H,LinearMap.mem_range_self _ H⟩ = (hN.moment ⊤).toLp (N ⊤))
    (T : ℝ) (hT : 0<T) [Fact (0≤T)]
    (a b : Icc (0:ℝ) T) (hab : a≤b) (G : Ω → ℝ)
    (hG : Measurable[B.F (realTimeClamp a.val)] G) (hGinf : MemLp G ∞ P) :
    (compactItoIsometry P B i c I hI T hT.le
      (timeElementaryLp P T hT (fun t => B.F (realTimeClamp t.val))
        (B.mono.comp (real_time_clamp_mono.comp (Subtype.mono_coe _)))
        (fun _ => B.le _) a b G hG hGinf) : Ω → ℝ)
      =ᵐ[P.trim (B.le (realTimeClamp T))]
        (fun w => G w*(B.W i (realTimeClamp b.val) w-B.W i (realTimeClamp a.val) w)) := by
  have he := compactItoIsometry_coe P B i c I hI T hT.le
    (timeElementaryLp P T hT (fun t => B.F (realTimeClamp t.val))
      (B.mono.comp (real_time_clamp_mono.comp (Subtype.mono_coe _)))
      (fun _ => B.le _) a b G hG hGinf)
  rw [compact_energy_elementary] at he
  have hs := (actual_ito_step_isometry P B i c I hI a b a.property.1 hab G hG hGinf).1
  have hfin (t : Icc (0:ℝ) T) : realTimeClamp (T := (⊤:EReal)) t.val < ⊤ := by
    change (realTimeClamp (T := (⊤:EReal)) t.val).val < (⊤:EReal)
    rw [real_time_clamp_eq _ t.property.1 le_top]
    exact EReal.coe_lt_top _
  apply ae_eq_trim_of_measurable (B.le (realTimeClamp T)) (Lp.stronglyMeasurable _).measurable
  · exact (hG.mono (B.mono (real_time_clamp_mono a.property.2)) le_rfl).mul
      (((B.martingale i).adapted P B.F _ (hfin b)).mono (B.mono (real_time_clamp_mono b.property.2)) le_rfl |>.sub
        (((B.martingale i).adapted P B.F _ (hfin a)).mono (B.mono (real_time_clamp_mono a.property.2)) le_rfl))
  · exact he.trans hs

end Asakura.Chapter12
