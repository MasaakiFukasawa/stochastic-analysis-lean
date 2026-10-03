import Chapter12ItoIncrementPairing
import Chapter12CompactStepIntegral
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
theorem actual_ito_compact_increment_pairing {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (c : ℕ → ℝ)
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
    (G : Ω → ℝ) (hGm : Measurable[B.F (realTimeClamp a.val)] G) (hG : MemLp G ∞ P)
    (H : progressiveEnergyIntegrands B.F c (P.prod (volume.restrict (Ioi (0:ℝ)))))
    (hH : progressiveEnergyToLp B.F c _ H = (ψ i).val) :
    (∫ z : Ω × Icc (0:ℝ) T,H.val (z.1,z.2.val)*
      (Ico a b).indicator (fun _ => G z.1) z.2 ∂P.prod (compactTimeMeasure T hT)) =
      ∫ w,Y w*G w*(B.W i (realTimeClamp b.val) w-B.W i (realTimeClamp a.val) w) ∂P := by
  have he := actual_ito_representation_increment_pairing P B c I L hL hI Y m ψ hrep i
    a.val b.val a.property.1 hab G hGm hG
  have hae : ((ψ i).val : Ω × ℝ → ℝ) =ᵐ[P.prod (volume.restrict (Ioi (0:ℝ)))] H.val := by
    rw [← hH]
    exact H.property.2.2.coeFn_toLp
  rw [← compact_step_integral P T hT a b H.val H.property.1 G
    (hGm.mono (B.le _) le_rfl)]
  calc
    _ = ∫ z,((ψ i).val : Ω × ℝ → ℝ) z*
        (Ioc a.val b.val).indicator (fun _ => G z.1) z.2
        ∂P.prod (volume.restrict (Ioi (0:ℝ))) := by
      apply integral_congr_ae
      filter_upwards [hae] with z hz
      rw [hz]
    _ = _ := he

end Asakura.Chapter12
