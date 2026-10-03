import Chapter12BrownianRepresentation
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
theorem clark_ocone_actual_finite_integrals {Ω : Type*} [MeasurableSpace Ω]
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
        (U : Ω → ℝ) (P.trim (B.le (realTimeClamp T)))) :
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
    ∀ (W : FiniteWienerHilbert d T →ₗᵢ[ℝ] Lp ℝ 2 R),
      ∀ hW : ∀ h,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) R,
      (∀ z,X z =ᵐ[R] (W (brownianTimeDirection z) : Ω → ℝ)) →
      (∀ (a : Icc (0:ℝ) T) (G : Ω → ℝ),Measurable[B.F (realTimeClamp a.val)] G →
        AEStronglyMeasurable[MeasurableSpace.comap
          (fun w (z : BrownianTimeCoordinates d a.val) =>
            X (z.1,⟨z.2.val,z.2.property.1,z.2.property.2.trans a.property.2⟩) w)
          inferInstance] G R) →
      ∀ (D : Lp ℝ 2 R →ₗ.[ℝ] Lp (FiniteWienerHilbert d T) 2 R),
        (D.graph : Set _) = closure (range (cylinderPair R W univ dense_univ (fun h _ => hW h) 2 (by simp))) →
      ∀ Y₀ : D.domain,
      ∃ H : Fin (d+1) → E,∃ N : Fin (d+1) → HalfClosedTime → Ω → ℝ,
        (∀ i,M2 (N i)) ∧ (∀ i,Ito i (H i) (N i)) ∧
        (Y₀ : Lp ℝ 2 R) =ᵐ[P] (fun w => (∫ z,(Y₀ : Lp ℝ 2 R) z ∂R)+∑ i,N i (realTimeClamp T) w) ∧
        ∀ i,∀ᵐ t ∂compactTimeMeasure T hT.le,
          (fun w => restrict (H i) (w,t)) =ᵐ[R]
            R[(fun w => brownianDerivativeTime R T hT.le (D Y₀) i (w,t))|B.F (realTimeClamp t.val)] := by
  have hfull := fun U : Lp ℝ 2 (P.trim (B.le (realTimeClamp T))) => finite_brownian_natural_information P B T (U : Ω → ℝ) (hgen U)
  obtain ⟨I,L,hL,hI,hrep⟩ := brownian_system_representation P B c hc hcm hct hcut hcc hco
  let e := terminalLpEmbedding P (B.F (realTimeClamp T)) (B.le _)
  have hecoe := terminalLpEmbedding_coe P (B.F (realTimeClamp T)) (B.le _)
  have heint := terminalLpEmbedding_integral P (B.F (realTimeClamp T)) (B.le _)
  have hfinite := represented_integrands_at_finite_time P B c I L hL hI
  have hclark := clark_actual_time_conditional P B c hco hc hcm hct hcut hcc I L hL hI
  let R := P.trim (B.le (realTimeClamp T))
  letI := probability_trim P _ (B.le (realTimeClamp T))
  letI : MeasurableSpace Ω := B.F (realTimeClamp T)
  letI := finite_horizon_L2_nontrivial T hT
  dsimp only
  intro W hW hX hnat D hD Y₀
  let Y := e (Y₀ : Lp ℝ 2 R)
  have hYeq := hecoe (Y₀ : Lp ℝ 2 R)
  have hYn := (hfull (Y₀ : Lp ℝ 2 R)).congr hYeq.symm
  obtain ⟨ψ,hψ⟩ := hrep Y hYn
  have hmean : (∫ w,Y w ∂P)=∫ w,(Y₀ : Lp ℝ 2 R) w ∂R := heint _
  rw [hmean] at hψ
  obtain ⟨H,N,hHe,hN,hNI,hY⟩ := hfinite Y (∫ w,(Y₀ : Lp ℝ 2 R) w ∂R) ψ hψ
    (realTimeClamp T) (Y₀ : Lp ℝ 2 R) (Lp.stronglyMeasurable _).measurable hYeq
  refine ⟨H,N,hN,hNI,hY,?_⟩
  intro i
  exact hclark Y (∫ w,(Y₀ : Lp ℝ 2 R) w ∂R) ψ hψ T hT hfull i (H i) (hHe i)
    W hW hX hnat D hD Y₀ hYeq

end Asakura.Chapter12
