import Chapter12BrownianConditionalMartingale
import Chapter12ConditionalTrim
import Chapter12VectorWienerGaussian
import Chapter12ConditionalProgressive
import Chapter12ItoIncrementPairing

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter4 Asakura.Chapter5
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

/-- The representation used in chapter 12 is obtained from the checked
chapter-5 construction for the same Brownian system. -/
theorem brownian_terminal_conditional_process {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P (d+1))
    (c : ℕ → ℝ) (hc : ∀ n,0<c n) (hcm : StrictMono c)
    (hct : StrictMono (fun n => realTimeClamp (T := ⊤) (c n)))
    (hcut : ∀ n,realTimeClamp (T := ⊤) (c n)<⊤)
    (hcc : ∀ t : HalfClosedTime,t<⊤ → ∃ n,t<realTimeClamp (c n))
    (hco : ∀ r : ℝ,∃ n,r≤c n)
    (T : ℝ)
    (U : Lp ℝ 2 (P.trim (B.le (realTimeClamp T))))
    (hU : AEStronglyMeasurable[MeasurableSpace.comap
      (fun w (z : Σ _ : Fin (d+1),{r : ℝ // 0≤r ∧ (r:EReal)<⊤}) =>
        B.W z.1 (realTimeClamp z.2.val) w) inferInstance] (U : Ω → ℝ) P) :
    letI : MeasurableSpace Ω := B.F (realTimeClamp T)
    ∃ C : Ω × Icc (0:ℝ) T → ℝ,
      @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) T => B.F (realTimeClamp t.val))) inferInstance C ∧
      ∀ t : Icc (0:ℝ) T,(fun w => C (w,t)) =ᵐ[P.trim (B.le (realTimeClamp T))]
        (P.trim (B.le (realTimeClamp T)))[(U : Ω → ℝ)|B.F (realTimeClamp t.val)] := by
  have hu := memLp_of_memLp_trim (B.le (realTimeClamp T)) (Lp.memLp U)
  let Y := hu.toLp (U : Ω → ℝ)
  have hY : AEStronglyMeasurable[MeasurableSpace.comap
      (fun w (z : Σ _ : Fin (d+1),{r : ℝ // 0≤r ∧ (r:EReal)<⊤}) =>
        B.W z.1 (realTimeClamp z.2.val) w) inferInstance] Y P := hU.congr hu.coeFn_toLp.symm
  obtain ⟨M,hM,he⟩ := brownian_system_conditional_martingale P B c hc hcm hct hcut hcc hco Y hY
  have hrep : (U : Ω → ℝ) =ᵐ[P] fun w => (∫ z,Y z ∂P)+M ⊤ w := hu.coeFn_toLp.symm.trans he
  have hp := represented_conditional_progressive P B.F B.mono B.le U hu M hM (∫ z,Y z ∂P) hrep T
  refine ⟨(fun z => (∫ w,Y w ∂P)+M (realTimeClamp z.2.val) z.1),hp.1,?_⟩
  intro t
  have hqm : Measurable[B.F (realTimeClamp t.val)]
      (fun w => (∫ z,Y z ∂P)+M (realTimeClamp t.val) w) := measurable_const.add (hM.adapted _)
  have hqi : Integrable (fun w => (∫ z,Y z ∂P)+M (realTimeClamp t.val) w) P :=
    (integrable_const _).add ((hM.moment _).integrable (by norm_num))
  exact conditional_expectation_on_terminal_space P (B.F (realTimeClamp T))
    (B.F (realTimeClamp t.val)) (B.le _) (B.mono (real_time_clamp_mono t.property.2))
    U _ (Lp.stronglyMeasurable U).measurable hqm (hu.integrable (by norm_num)) hqi (hp.2 t)

end Asakura.Chapter12
