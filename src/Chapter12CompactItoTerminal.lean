import Chapter12CompactEnergyIsometry
import Chapter12ProgressiveSupportedTerminal
import Chapter12ItoPositiveTimeCongruence
import Chapter12ItoStepIsometry

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000

theorem compact_ito_terminal_measurable {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (i : Fin d) (c : ℕ → ℝ)
    (I : progressiveEnergyRange B.F c (P.prod (volume.restrict (Ioi (0:ℝ)))) →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hI : ∀ H : progressiveEnergyIntegrands B.F c (P.prod (volume.restrict (Ioi (0:ℝ)))),
      ∃ N : HalfClosedTime → Ω → ℝ,∃ hN : ContinuousM2Witness P B.F N,
        ItoCovarianceFormula P B.F (B.W i) H.val N ∧
        I ⟨progressiveEnergyToLp B.F c _ H,LinearMap.mem_range_self _ H⟩ = (hN.moment ⊤).toLp (N ⊤))
    (T : ℝ) (hT : 0≤T) [Fact (0≤T)] :
    let Fc := fun t : Icc (0:ℝ) T => B.F (realTimeClamp t.val)
    letI : MeasurableSpace (Ω × Icc (0:ℝ) T) := progressiveSpace Fc
    ∀ U : Lp ℝ 2 ((P.prod (compactTimeMeasure T hT)).trim
      (progressive_space_le_product Fc (fun _ => B.le _))),
    AEStronglyMeasurable[B.F (realTimeClamp T)]
      (I (compactEnergyIsometry P T hT B.F B.mono B.le c U) : Ω → ℝ) P := by
  dsimp only
  intro U
  let H := compactProgressiveEnergy P T hT B.F B.mono B.le c U
  obtain ⟨N,hN,hNI,he⟩ := hI H
  let f := fun z : Ω × ℝ => U (z.1,projIcc 0 T hT z.2)
  have hf : Measurable f := by
    have hu := (Lp.stronglyMeasurable U).measurable.mono
      (progressive_space_le_product _ (fun _ => B.le _)) le_rfl
    exact hu.comp (measurable_fst.prodMk (continuous_projIcc.measurable.comp measurable_snd))
  have hNI' : ItoCovarianceFormula P B.F (B.W i)
      (fun z => (Ioc (0:ℝ) T).indicator (fun t => f (z.1,t)) z.2) N := by
    apply ito_formula_congr_positive_time P B.F (B.W i) N H.val _ hNI
    intro w r hr _
    change (Iic T).indicator (fun t => f (w,t)) r = (Ioc 0 T).indicator (fun t => f (w,t)) r
    by_cases ht : r≤T <;> simp [ht,hr]
  have hend := supported_progressive_ito_terminal_identity P B i T hT f
    (fun w => hf.comp (measurable_const.prodMk measurable_id)) N hN hNI'
  have hcoe : (I (compactEnergyIsometry P T hT B.F B.mono B.le c U) : Ω → ℝ)
      =ᵐ[P] N (realTimeClamp T) := by
    change (I ⟨progressiveEnergyToLp B.F c _ H,LinearMap.mem_range_self _ H⟩ : Ω → ℝ) =ᵐ[P] _
    rw [he]
    exact (hN.moment ⊤).coeFn_toLp.trans hend
  exact (hN.adapted _).aestronglyMeasurable.congr hcoe.symm

end Asakura.Chapter12
