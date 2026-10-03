import Chapter12ClarkBoundedPastTest
import Chapter12BrownianDerivativeRealization
import Chapter12AdaptedProjectionTests

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology RealInnerProductSpace
namespace Asakura.Chapter12
open Asakura.Chapter2Complete Asakura.FullAudit
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- The analytic identification in the printed Clark--Ocone proof.
The only stochastic-integral input is the increment pairing furnished by
Ito isometry for the representing integrand; Gaussian IBP, approximation,
Fubini realization and adapted-step density are all derived above. -/
theorem clark_projection_connected {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (T : ℝ) (hT : 0 < T) [Fact (0 ≤ T)]
    (W : FiniteWienerHilbert d T →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hW : ∀ h, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (X : BrownianTimeCoordinates d T → Ω → ℝ)
    (hXm : ∀ z, Measurable (X z)) (hXc : ∀ w, Continuous (fun z => X z w))
    (hX : ∀ z, X z =ᵐ[P] (W (brownianTimeDirection z) : Ω → ℝ))
    (F : Icc (0:ℝ) T → MeasurableSpace Ω) (hF : Monotone F)
    (hle : ∀ t,F t ≤ ‹MeasurableSpace Ω›)
    (hnull : ∀ t N,MeasurableSet N → P N=0 → MeasurableSet[F t] N)
    (hnat : ∀ (a : Icc (0:ℝ) T) (G : Ω → ℝ), Measurable[F a] G →
      AEStronglyMeasurable[MeasurableSpace.comap
        (fun w (z : BrownianTimeCoordinates d a.val) =>
          X (z.1,⟨z.2.val,z.2.property.1,z.2.property.2.trans a.property.2⟩) w)
        inferInstance] G P) :
    letI := finite_horizon_L2_nontrivial T hT
    ∀ (D : Lp ℝ 2 P →ₗ.[ℝ] Lp (FiniteWienerHilbert d T) 2 P),
      (D.graph : Set _) = closure (range (cylinderPair P W univ dense_univ (fun h _ => hW h) 2 (by simp))) →
    ∀ (Y : D.domain) (i : Fin (d+1)) (ψ : Lp ℝ 2 (P.prod (compactTimeMeasure T hT.le))),
      AEStronglyMeasurable[progressiveSpace F] ψ (P.prod (compactTimeMeasure T hT.le)) →
      (∀ (a b : Icc (0:ℝ) T),a ≤ b → ∀ G : Ω → ℝ,Measurable[F a] G → MemLp G ∞ P →
        (∫ w,(Y : Lp ℝ 2 P) w*G w*(X (i,b) w-X (i,a) w) ∂P) =
          ∫ z,ψ z*(Ico a b).indicator (fun _ => G z.1) z.2 ∂P.prod (compactTimeMeasure T hT.le)) →
      ψ = (condExpL2 ℝ ℝ (progressive_space_le_product F hle)
        (brownianDerivativeTime P T hT.le (D Y) i) : Lp ℝ 2 (P.prod (compactTimeMeasure T hT.le))) := by
  letI := finite_horizon_L2_nontrivial T hT
  intro D hD Y i ψ hψ hIto
  apply adapted_projection_from_step_tests P T hT F hF hle hnull _ ψ hψ
  intro a b G hGm hG
  by_cases hab : a ≤ b
  · have htest := clark_bounded_past_increment_test P T hT W hW X hXm hXc hX D hD Y i
      a.val b.val a.property.1 hab b.property.2 G hG (hnat a G hGm)
    have ht := brownian_derivative_interval_test P T hT.le (D Y) i a b G
      (hG.mono_exponent le_top)
    exact ht.symm.trans (htest.trans (hIto a b hab G hGm hG))
  · have he : Ico a b = ∅ := Ico_eq_empty_of_le (le_of_not_ge hab)
    simp only [he,indicator_empty,mul_zero,integral_zero]

end Asakura.Chapter12
