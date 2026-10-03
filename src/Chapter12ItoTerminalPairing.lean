import Chapter12ItoCompactPairing
import Chapter12TerminalIntegrandRestriction
import Chapter12TerminalStepPairing
import Mathlib.Analysis.InnerProductSpace.PiL2

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- Ito isometry gives the other side of the Clark--Ocone increment test,
using the concrete chapter-5 integral and the proved step-increment identity. -/
theorem actual_ito_terminal_increment_pairing {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (c : ℕ → ℝ) (hco : ∀ r,∃ n,r ≤ c n)
    (I : Fin d → progressiveEnergyRange B.F c (P.prod (volume.restrict (Ioi (0:ℝ)))) →ₗᵢ[ℝ] Lp ℝ 2 P)
    (L : PiLp 2 (fun _ : Fin d => progressiveEnergyRange B.F c (P.prod (volume.restrict (Ioi (0:ℝ))))) →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hL : ∀ x,L x=∑ i,I i (x i))
    (hI : ∀ i,∀ H : progressiveEnergyIntegrands B.F c (P.prod (volume.restrict (Ioi (0:ℝ)))),
      ∃ N : HalfClosedTime → Ω → ℝ,∃ hN : ContinuousM2Witness P B.F N,
        ItoCovarianceFormula P B.F (B.W i) H.val N ∧
        I i ⟨progressiveEnergyToLp B.F c _ H,LinearMap.mem_range_self _ H⟩ = (hN.moment ⊤).toLp (N ⊤))
    (Y : Lp ℝ 2 P) (m : ℝ)
    (ψ : PiLp 2 (fun _ : Fin d => progressiveEnergyRange B.F c (P.prod (volume.restrict (Ioi (0:ℝ))))))
    (hrep : Y = (memLp_const m : MemLp (fun _ : Ω => m) 2 P).toLp _+L ψ)
    (T : ℝ) (hT : 0 ≤ T) (i : Fin d) (a b : Icc (0:ℝ) T) (hab : a ≤ b)
    (G : Ω → ℝ) (hGm : Measurable[B.F (realTimeClamp a.val)] G) (hG : MemLp G ∞ (P.trim (B.le (realTimeClamp T))))
    (H : progressiveEnergyIntegrands B.F c (P.prod (volume.restrict (Ioi (0:ℝ)))))
    (hH : progressiveEnergyToLp B.F c _ H = (ψ i).val)
    (Y₀ : Ω → ℝ) (hY₀ : Measurable[B.F (realTimeClamp T)] Y₀)
    (hYeq : (Y : Ω → ℝ) =ᵐ[P] Y₀) :
    (@integral (Ω × Icc (0:ℝ) T) ℝ _ _ ((B.F (realTimeClamp T)).prod inferInstance)
      (@Measure.prod Ω (Icc (0:ℝ) T) (B.F (realTimeClamp T)) inferInstance
        (P.trim (B.le (realTimeClamp T))) (compactTimeMeasure T hT))
      (fun z => H.val (z.1,z.2.val)*(Ico a b).indicator (fun _ => G z.1) z.2)) =
    (@integral Ω ℝ _ _ (B.F (realTimeClamp T)) (P.trim (B.le (realTimeClamp T)))
      (fun w => Y₀ w*G w*(B.W i (realTimeClamp b.val) w-B.W i (realTimeClamp a.val) w))) := by
  letI : Fact (0 ≤ T) := ⟨hT⟩
  have he := actual_ito_compact_increment_pairing P B c I L hL hI Y m ψ hrep T hT i a b hab
    G hGm (memLp_of_memLp_trim (B.le _) hG) H hH
  have hraw : (∫ z : Ω × Icc (0:ℝ) T,H.val (z.1,z.2.val)*
      (Ico a b).indicator (fun _ => G z.1) z.2 ∂P.prod (compactTimeMeasure T hT)) =
      ∫ w,Y₀ w*G w*(B.W i (realTimeClamp b.val) w-B.W i (realTimeClamp a.val) w) ∂P := by
    rw [he]
    apply integral_congr_ae
    filter_upwards [hYeq] with w hw
    rw [hw]
  apply terminal_step_pairing P (B.F (realTimeClamp T)) (B.le _) (compactTimeMeasure T hT)
    _ (terminal_integrand_restriction P B.F B.mono B.le c hco H T hT).1 G Y₀ _
    (hGm.mono (B.mono (real_time_clamp_mono a.property.2)) le_rfl) hY₀ _ (Ico a b) measurableSet_Ico hraw
  have hfin (t : Icc (0:ℝ) T) : realTimeClamp (T := (⊤:EReal)) t.val < ⊤ := by
    change (realTimeClamp (T := (⊤:EReal)) t.val).val < (⊤:EReal)
    rw [real_time_clamp_eq _ t.property.1 le_top]
    exact EReal.coe_lt_top _
  exact (((B.martingale i).adapted P B.F _ (hfin b)).mono
    (B.mono (real_time_clamp_mono b.property.2)) le_rfl).sub
    (((B.martingale i).adapted P B.F _ (hfin a)).mono
      (B.mono (real_time_clamp_mono a.property.2)) le_rfl)

end Asakura.Chapter12
