import Chapter12SupportedItoTerminal
import Chapter12WienerIndicator

open MeasureTheory Set Filter
open scoped ENNReal
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Zero extension of a finite-horizon time integrand can be represented
by an actual function supported in (0,T]. -/
theorem zero_extension_supported (T : ℝ)
    (f : Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T))) :
    (L2ZeroExtension (volume.restrict (Ioi (0:ℝ))) (Iic T) measurableSet_Iic f : ℝ → ℝ) =ᵐ[volume.restrict (Ioi (0:ℝ))]
      (Ioc 0 T).indicator (f : ℝ → ℝ) := by
  filter_upwards [L2ZeroExtension_coe (volume.restrict (Ioi (0:ℝ))) (Iic T) measurableSet_Iic f,
    ae_restrict_mem measurableSet_Ioi] with t ht ht0
  rw [ht]
  by_cases h : t ≤ T
  · rw [Set.indicator_of_mem (show t ∈ Iic T from h),Set.indicator_of_mem (show t ∈ Ioc 0 T from ⟨ht0,h⟩)]
  · simp [Set.mem_Iic,h,Set.mem_Ioc]

/-- Each coordinate integral restricted to [0,T] is measurable for F_T,
even though it was first constructed on a space carrying future Brownian
increments. This is used before trimming the probability space to F_T. -/
theorem coordinate_wiener_terminal_measurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (i : Fin d) (J : Lp ℝ 2 (volume.restrict (Ioi (0:ℝ))) →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hJ : ∀ (f : ℝ → ℝ) (hm : Measurable f) (hi : MemLp f 2 (volume.restrict (Ioi (0:ℝ)))),
      ∃ N : HalfClosedTime → Ω → ℝ, ∃ hN : ContinuousM2Witness P B.F N,
        ItoCovarianceFormula P B.F (B.W i) (fun z => f z.2) N ∧
        J (hi.toLp f) = (hN.moment ⊤).toLp (N ⊤))
    (T : ℝ) (hT : 0 ≤ T)
    (f : Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T))) :
    AEStronglyMeasurable[B.F (realTimeClamp T)]
      (J (L2ZeroExtension (volume.restrict (Ioi (0:ℝ))) (Iic T) measurableSet_Iic f) : Ω → ℝ) P := by
  let E := L2ZeroExtension (E := ℝ) (volume.restrict (Ioi (0:ℝ))) (Iic T) measurableSet_Iic
  have he := zero_extension_supported T f
  let hi := (Lp.memLp (E f)).ae_eq he
  have hep : hi.toLp ((Ioc 0 T).indicator (f : ℝ → ℝ)) = E f := by
    apply Lp.ext
    exact hi.coeFn_toLp.trans he.symm
  obtain ⟨N,hN,hNI,heJ⟩ := hJ _ ((Lp.stronglyMeasurable f).measurable.indicator measurableSet_Ioc) hi
  rw [hep] at heJ
  have heN := supported_ito_terminal_identity P B i T hT f (Lp.stronglyMeasurable f).measurable N hN hNI
  have hM : AEStronglyMeasurable[B.F (realTimeClamp T)] (N (realTimeClamp T)) P :=
    (hN.adapted _).stronglyMeasurable.aestronglyMeasurable
  apply hM.congr
  exact (heN.symm.trans (hN.moment ⊤).coeFn_toLp.symm).trans
    (Filter.EventuallyEq.of_eq (congrArg (fun g : Lp ℝ 2 P => (g : Ω → ℝ)) heJ.symm))

end Asakura.Chapter12
