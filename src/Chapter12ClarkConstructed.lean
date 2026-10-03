import Chapter12ClarkFiniteIntegrals
import Chapter12BrownianMalliavinOperator
import Chapter12ClarkActualConditional
import Chapter12RepresentedIntegrandsFinite
import Chapter12TerminalLpEmbedding
import Chapter12FiniteNaturalInformation
import Chapter12ProgressiveConditionalProjection
import Chapter12ConditionalTrim
import Chapter12VectorWienerGaussian
import Chapter12ConditionalProgressive
import Chapter12ItoIncrementPairing

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter4 Asakura.Chapter5
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

/-- The representation used in chapter 12 is obtained from the checked
chapter-5 construction for the same Brownian system. -/
theorem clark_ocone_constructed_brownian_operator {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P (d+1))
    (c : ℕ → ℝ) (hc : ∀ n,0<c n) (hcm : StrictMono c)
    (hct : StrictMono (fun n => realTimeClamp (T := ⊤) (c n)))
    (hcut : ∀ n,realTimeClamp (T := ⊤) (c n)<⊤)
    (hcc : ∀ t : HalfClosedTime,t<⊤ → ∃ n,t<realTimeClamp (c n))
    (hco : ∀ r : ℝ,∃ n,r≤c n)
    (T : ℝ) (hT : 0<T) [Fact (0≤T)]
    (hgen : ∀ U : Lp ℝ 2 (P.trim (B.le (realTimeClamp T))),
      AEStronglyMeasurable[MeasurableSpace.comap
        (fun w z => brownianTimeCoordinate P B T z w) inferInstance]
        (U : Ω → ℝ) (P.trim (B.le (realTimeClamp T))))
    (hnat : ∀ (a : Icc (0:ℝ) T) (G : Ω → ℝ),Measurable[B.F (realTimeClamp a.val)] G →
      AEStronglyMeasurable[MeasurableSpace.comap
        (fun w (z : BrownianTimeCoordinates d a.val) =>
          brownianTimeCoordinate P B T
            (z.1,⟨z.2.val,z.2.property.1,z.2.property.2.trans a.property.2⟩) w)
        inferInstance] G (P.trim (B.le (realTimeClamp T)))) :
    let X := brownianTimeCoordinate P B T
    let E := progressiveEnergyIntegrands B.F c (P.prod (volume.restrict (Ioi (0:ℝ))))
    let M2 := fun N => ContinuousM2Witness P B.F N
    let Ito := fun i (H : E) N => ItoCovarianceFormula P B.F (B.W i) H.val N
    let restrict := fun H : E =>
      ((terminal_integrand_restriction P B.F B.mono B.le c hco H T hT.le).2).toLp
        (fun z : Ω × Icc (0:ℝ) T => H.val (z.1,z.2.val))
    let R := P.trim (B.le (realTimeClamp T))
    letI := probability_trim P _ (B.le (realTimeClamp T))
    letI : MeasurableSpace Ω := B.F (realTimeClamp T)
    letI := finite_horizon_L2_nontrivial T hT
    ∃ W : FiniteWienerHilbert d T →ₗᵢ[ℝ] Lp ℝ 2 R,
    ∃ hW : ∀ h,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) R,
    ∃ D : Lp ℝ 2 R →ₗ.[ℝ] Lp (FiniteWienerHilbert d T) 2 R,
      D.IsClosed ∧
      (D.graph : Set _) = closure (range (cylinderPair R W univ dense_univ (fun h _ => hW h) 2 (by simp))) ∧
      ∀ Y₀ : D.domain,
      ∃ H : Fin (d+1) → E,∃ N : Fin (d+1) → HalfClosedTime → Ω → ℝ,
        (∀ i,M2 (N i)) ∧ (∀ i,Ito i (H i) (N i)) ∧
        (Y₀ : Lp ℝ 2 R) =ᵐ[P] (fun w => (∫ z,(Y₀ : Lp ℝ 2 R) z ∂R)+∑ i,N i (realTimeClamp T) w) ∧
        ∀ i,∀ᵐ t ∂compactTimeMeasure T hT.le,
          (fun w => restrict (H i) (w,t)) =ᵐ[R]
            R[(fun w => brownianDerivativeTime R T hT.le (D Y₀) i (w,t))|B.F (realTimeClamp t.val)] := by
  have hop := brownian_finite_malliavin_operator P B T hT 2 2 (by simp) (by simp) hgen
  have hclark := clark_ocone_actual_finite_integrals P B c hc hcm hct hcut hcc hco T hT hgen
  letI := probability_trim P _ (B.le (realTimeClamp T))
  letI : MeasurableSpace Ω := B.F (realTimeClamp T)
  letI := finite_horizon_L2_nontrivial T hT
  dsimp only at hop ⊢
  obtain ⟨W,hW,D,hclos,hclosed,hcomplete,hgraph,hgraphClosed,hdom,hX⟩ := hop
  refine ⟨W,hW,D.closure,hclosed,hgraphClosed,?_⟩
  exact hclark W hW hX hnat D.closure hgraphClosed

end Asakura.Chapter12
