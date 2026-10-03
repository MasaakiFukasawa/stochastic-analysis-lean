import Chapter12ClarkActualIto
import Chapter12BrownianProjectionPointwise
import Chapter12ClarkProjectionConnected
import Chapter12FiniteBrownianTrim
import Chapter12TerminalIntegrandRestriction
import Chapter12TerminalStepPairing
import Mathlib.Analysis.InnerProductSpace.PiL2

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology RealInnerProductSpace
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- Ito isometry gives the other side of the Clark--Ocone increment test,
using the concrete chapter-5 integral and the proved step-increment identity. -/
theorem clark_actual_time_conditional {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P (d+1))
    (c : ℕ → ℝ) (hco : ∀ r,∃ n,r ≤ c n)
    (hc : ∀ n,0<c n) (hcm : StrictMono c)
    (hct : StrictMono (fun n => realTimeClamp (T := ⊤) (c n)))
    (hcut : ∀ n,realTimeClamp (T := ⊤) (c n)<⊤)
    (hcc : ∀ t : HalfClosedTime,t<⊤ → ∃ n,t<realTimeClamp (c n))
    (I : Fin (d+1) → progressiveEnergyRange B.F c (P.prod (volume.restrict (Ioi (0:ℝ)))) →ₗᵢ[ℝ] Lp ℝ 2 P)
    (L : PiLp 2 (fun _ : Fin (d+1) => progressiveEnergyRange B.F c (P.prod (volume.restrict (Ioi (0:ℝ))))) →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hL : ∀ x,L x=∑ i,I i (x i))
    (hI : ∀ i,∀ H : progressiveEnergyIntegrands B.F c (P.prod (volume.restrict (Ioi (0:ℝ)))),
      ∃ N : HalfClosedTime → Ω → ℝ,∃ hN : ContinuousM2Witness P B.F N,
        ItoCovarianceFormula P B.F (B.W i) H.val N ∧
        I i ⟨progressiveEnergyToLp B.F c _ H,LinearMap.mem_range_self _ H⟩ = (hN.moment ⊤).toLp (N ⊤))
    (Y : Lp ℝ 2 P) (m : ℝ)
    (ψ : PiLp 2 (fun _ : Fin (d+1) => progressiveEnergyRange B.F c (P.prod (volume.restrict (Ioi (0:ℝ))))))
    (hrep : Y = (memLp_const m : MemLp (fun _ : Ω => m) 2 P).toLp _+L ψ)
    (T : ℝ) (hT : 0 < T) [Fact (0 ≤ T)]
    (hgen : ∀ U : Lp ℝ 2 (P.trim (B.le (realTimeClamp T))),
      AEStronglyMeasurable[MeasurableSpace.comap
        (fun w (z : Σ _ : Fin (d+1),{r : ℝ // 0≤r ∧ (r:EReal)<⊤}) =>
          B.W z.1 (realTimeClamp z.2.val) w) inferInstance] (U : Ω → ℝ) P)
    (i : Fin (d+1))
    (H : progressiveEnergyIntegrands B.F c (P.prod (volume.restrict (Ioi (0:ℝ)))))
    (hH : progressiveEnergyToLp B.F c _ H = (ψ i).val) :
    let X := brownianTimeCoordinate P B T
    let R := P.trim (B.le (realTimeClamp T))
    let hΦ := (terminal_integrand_restriction P B.F B.mono B.le c hco H T hT.le).2
    letI := probability_trim P _ (B.le (realTimeClamp T))
    letI : MeasurableSpace Ω := B.F (realTimeClamp T)
    letI := finite_horizon_L2_nontrivial T hT
    ∀ (W : FiniteWienerHilbert d T →ₗᵢ[ℝ] Lp ℝ 2 R),
      ∀ hW : ∀ h,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) R,
      (∀ z,X z =ᵐ[R] (W (brownianTimeDirection z) : Ω → ℝ)) →
      (∀ (a : Icc (0:ℝ) T) (G : Ω → ℝ),Measurable[B.F (realTimeClamp a.val)] G →
        AEStronglyMeasurable[MeasurableSpace.comap
          (fun w (z : BrownianTimeCoordinates d a.val) =>
            X
              (z.1,⟨z.2.val,z.2.property.1,z.2.property.2.trans a.property.2⟩) w)
          inferInstance] G R) →
      ∀ (D : Lp ℝ 2 R →ₗ.[ℝ] Lp (FiniteWienerHilbert d T) 2 R),
        (D.graph : Set _) = closure (range (cylinderPair R W univ dense_univ (fun h _ => hW h) 2 (by simp))) →
      ∀ Y₀ : D.domain, (Y : Ω → ℝ) =ᵐ[P] (Y₀ : Lp ℝ 2 R) →
      ∀ᵐ t ∂compactTimeMeasure T hT.le,
        (fun w => hΦ.toLp _ (w,t)) =ᵐ[R]
          R[(fun w => brownianDerivativeTime R T hT.le (D Y₀) i (w,t))|B.F (realTimeClamp t.val)] := by
  have hclark := clark_projection_from_actual_ito P B c hco I L hL hI Y m ψ hrep T hT i H hH
  have hpoint := brownian_terminal_projection_pointwise P B c hc hcm hct hcut hcc hco T hT hgen
  let R := P.trim (B.le (realTimeClamp T))
  letI := probability_trim P _ (B.le (realTimeClamp T))
  letI : MeasurableSpace Ω := B.F (realTimeClamp T)
  letI := finite_horizon_L2_nontrivial T hT
  dsimp only
  intro W hW hX hnat D hD Y₀ hYeq
  have he := hclark W hW hX hnat D hD Y₀ hYeq
  have hp := hpoint (brownianDerivativeTime R T hT.le (D Y₀) i)
  rw [← he] at hp
  exact hp

end Asakura.Chapter12
