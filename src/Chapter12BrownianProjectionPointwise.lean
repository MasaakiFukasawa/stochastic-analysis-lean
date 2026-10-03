import Chapter12BrownianTerminalConditional
import Chapter12ProgressiveConditionalProjection
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
theorem brownian_terminal_projection_pointwise {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P (d+1))
    (c : ℕ → ℝ) (hc : ∀ n,0<c n) (hcm : StrictMono c)
    (hct : StrictMono (fun n => realTimeClamp (T := ⊤) (c n)))
    (hcut : ∀ n,realTimeClamp (T := ⊤) (c n)<⊤)
    (hcc : ∀ t : HalfClosedTime,t<⊤ → ∃ n,t<realTimeClamp (c n))
    (hco : ∀ r : ℝ,∃ n,r≤c n)
    (T : ℝ) (hT : 0<T) [Fact (0≤T)]
    (hgen : ∀ U : Lp ℝ 2 (P.trim (B.le (realTimeClamp T))),
      AEStronglyMeasurable[MeasurableSpace.comap
        (fun w (z : Σ _ : Fin (d+1),{r : ℝ // 0≤r ∧ (r:EReal)<⊤}) =>
          B.W z.1 (realTimeClamp z.2.val) w) inferInstance] (U : Ω → ℝ) P) :
    let R := P.trim (B.le (realTimeClamp T))
    letI := probability_trim P _ (B.le (realTimeClamp T))
    letI : MeasurableSpace Ω := B.F (realTimeClamp T)
    ∀ u : Lp ℝ 2 (R.prod (compactTimeMeasure T hT.le)),
    let q : Lp ℝ 2 (R.prod (compactTimeMeasure T hT.le)) :=
      condExpL2 ℝ ℝ (progressive_space_le_product
        (fun t : Icc (0:ℝ) T => B.F (realTimeClamp t.val))
        (fun t => B.mono (real_time_clamp_mono t.property.2))) u
    ∀ᵐ t ∂compactTimeMeasure T hT.le,(fun w => q (w,t)) =ᵐ[R]
      R[(fun w => u (w,t))|B.F (realTimeClamp t.val)] := by
  have hex := fun U => brownian_terminal_conditional_process P B c hc hcm hct hcut hcc hco T U (hgen U)
  let R := P.trim (B.le (realTimeClamp T))
  letI := probability_trim P _ (B.le (realTimeClamp T))
  letI : MeasurableSpace Ω := B.F (realTimeClamp T)
  dsimp only
  intro u
  have hnull : ∀ (t : Icc (0:ℝ) T) N,MeasurableSet N → R N=0 →
      MeasurableSet[B.F (realTimeClamp t.val)] N := by
    intro t N hN hz
    have he : R N=P N := trim_measurableSet_eq (B.le _) hN
    exact B.null _ N (B.le _ N hN) (he.symm.trans hz)
  exact progressive_projection_is_time_conditional R T hT
    (fun t : Icc (0:ℝ) T => B.F (realTimeClamp t.val))
    (fun s t hst => B.mono (real_time_clamp_mono hst))
    (fun t => B.mono (real_time_clamp_mono t.property.2)) hnull hex u

end Asakura.Chapter12
