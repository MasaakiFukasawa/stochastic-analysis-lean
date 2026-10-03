import Chapter12ItoTerminalPairing
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
theorem clark_projection_from_actual_ito {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P (d+1))
    (c : ℕ → ℝ) (hco : ∀ r,∃ n,r ≤ c n)
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
    (T : ℝ) (hT : 0 < T) [Fact (0 ≤ T)] (i : Fin (d+1))
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
      hΦ.toLp _ = (condExpL2 ℝ ℝ
        (progressive_space_le_product
          (fun t : Icc (0:ℝ) T => B.F (realTimeClamp t.val))
          (fun t => B.mono (real_time_clamp_mono t.property.2)))
        (brownianDerivativeTime R T hT.le (D Y₀) i) : Lp ℝ 2 (R.prod (compactTimeMeasure T hT.le))) := by
  let X := brownianTimeCoordinate P B T
  let R := P.trim (B.le (realTimeClamp T))
  have hm := (terminal_integrand_restriction P B.F B.mono B.le c hco H T hT.le).1
  have hΦ := (terminal_integrand_restriction P B.F B.mono B.le c hco H T hT.le).2
  have hp := compact_progressive_restriction B.F c hco H.val H.property.2.1 T
  have hXm := brownian_time_coordinate_measurable P B T
  have hXc := brownian_time_coordinate_continuous P B T
  have hIto := actual_ito_terminal_increment_pairing P B c hco I L hL hI Y m ψ hrep T hT.le i
  letI := probability_trim P _ (B.le (realTimeClamp T))
  letI : MeasurableSpace Ω := B.F (realTimeClamp T)
  letI := finite_horizon_L2_nontrivial T hT
  dsimp only
  intro W hW hX hnat D hD Y₀ hYeq
  have hnull : ∀ (t : Icc (0:ℝ) T) N,MeasurableSet N → R N=0 →
      MeasurableSet[B.F (realTimeClamp t.val)] N := by
    intro t N hN hz
    have he : R N=P N := trim_measurableSet_eq (B.le _) hN
    exact B.null _ N (B.le _ N hN) (he.symm.trans hz)
  apply clark_projection_connected R T hT W hW X hXm hXc hX
    (fun t : Icc (0:ℝ) T => B.F (realTimeClamp t.val))
    (fun s t hst => B.mono (real_time_clamp_mono hst))
    (fun t => B.mono (real_time_clamp_mono t.property.2)) hnull hnat D hD Y₀ i
  · exact hp.aestronglyMeasurable.congr hΦ.coeFn_toLp.symm
  · intro a b hab G hGm hG
    have he := hIto a b hab G hGm hG H hH (Y₀ : Lp ℝ 2 R)
      (Lp.stronglyMeasurable _).measurable hYeq
    calc
      _ = ∫ z : Ω × Icc (0:ℝ) T,H.val (z.1,z.2.val)*
          (Ico a b).indicator (fun _ => G z.1) z.2 ∂R.prod (compactTimeMeasure T hT.le) := he.symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [hΦ.coeFn_toLp] with z hz
        rw [hz]

end Asakura.Chapter12
