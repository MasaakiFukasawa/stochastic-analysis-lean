import Chapter12AdaptedStepEmbedding
import Chapter12BoundedStepDivergence
import Chapter12DivergenceAdaptedExtension

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology
namespace Asakura.Chapter12
open Asakura.Chapter2Complete
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000

/-- The actual bounded-past Gaussian duality and the actual dense
progressive step space identify the divergence on every adapted L2 process. -/
theorem adapted_divergence_from_actual_steps {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (T : ℝ) (hT : 0<T) [Fact (0≤T)]
    (F : Icc (0:ℝ) T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet N → P N=0 → MeasurableSet[F t] N)
    (W : FiniteWienerHilbert d T →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hW : ∀ h,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (X : BrownianTimeCoordinates d T → Ω → ℝ)
    (hXm : ∀ z,Measurable (X z)) (hXc : ∀ w,Continuous (fun z => X z w))
    (hX : ∀ z,X z=ᵐ[P] (W (brownianTimeDirection z) : Ω → ℝ))
    (hnat : ∀ (a : Icc (0:ℝ) T) (G : Ω → ℝ),Measurable[F a] G →
      AEStronglyMeasurable[MeasurableSpace.comap
        (fun w (z : BrownianTimeCoordinates d a.val) =>
          X (z.1,⟨z.2.val,z.2.property.1,z.2.property.2.trans a.property.2⟩) w)
        inferInstance] G P) :
    letI := finite_horizon_L2_nontrivial T hT
    ∀ (D : Lp ℝ 2 P →ₗ.[ℝ] Lp (FiniteWienerHilbert d T) 2 P),
      (D.graph : Set _)=closure (range (cylinderPair P W univ dense_univ (fun h _ => hW h) 2 (by simp))) →
    letI : MeasurableSpace (Ω × Icc (0:ℝ) T) := progressiveSpace F
    ∀ (i : Fin (d+1))
      (I : Lp ℝ 2 ((P.prod (compactTimeMeasure T hT.le)).trim
        (progressive_space_le_product F hle)) →L[ℝ] Lp ℝ 2 P),
    (∀ (a b : Icc (0:ℝ) T),a≤b → ∀ (G : Ω → ℝ) (hG : Measurable[F a] G) (hg : MemLp G ∞ P),
      (I (timeElementaryLp P T hT F hF hle a b G hG hg) : Ω → ℝ)=ᵐ[P]
        (fun w => G w*(X (i,b) w-X (i,a) w))) →
    ∀ U,IsDivergence D (adaptedWienerEmbedding P T hT.le F hle (finitePiInjection i U)) (I U) := by
  letI := finite_horizon_L2_nontrivial T hT
  intro D hD i I hI
  let K := Lp ℝ 2 ((P.prod (compactTimeMeasure T hT.le)).trim (progressive_space_le_product F hle))
  let J : K →L[ℝ] Lp (FiniteWienerHilbert d T) 2 P :=
    (adaptedWienerEmbedding P T hT.le F hle).toContinuousLinearMap.comp (finitePiInjection i)
  let S : Set K := {U | ∃ (a b : Icc (0:ℝ) T) (G : Ω → ℝ)
    (hG : Measurable[F a] G) (hg : MemLp G ∞ P),
    (U : Ω × Icc (0:ℝ) T → ℝ)=ᵐ[((P.prod (compactTimeMeasure T hT.le)).trim
      (progressive_space_le_product F hle))]
      (fun z => (Ico a b).indicator (fun _ => G z.1) z.2)}
  have hdense : Dense (Submodule.span ℝ S : Set K) := time_elementary_span_dense P T hT F hF hle hnull
  apply divergence_from_adapted_step_core D J I S hdense
  rintro U ⟨a,b,G,hG,hg,he⟩
  have hU : U=timeElementaryLp P T hT F hF hle a b G hG hg :=
    Lp.ext (he.trans (time_elementary_memLp P T hT F hF hle a b G hG hg).coeFn_toLp.symm)
  rw [hU]
  by_cases hab : a≤b
  · obtain ⟨hu,hz,hd⟩ := bounded_past_step_divergence P T hT W hW X hXm hXc hX D hD
      i a b a.property.1 hab b.property.2 G hg (hnat a G hG)
    have hj := adapted_step_embedding P T hT F hF hle i a b G hG hg
    have hi : I (timeElementaryLp P T hT F hF hle a b G hG hg)=hz.toLp _ :=
      Lp.ext ((hI a b hab G hG hg).trans hz.coeFn_toLp.symm)
    change IsDivergence D (adaptedWienerEmbedding P T hT.le F hle
      (finitePiInjection i (timeElementaryLp P T hT F hF hle a b G hG hg))) _
    rw [hj,hi]
    exact hd
  · have hz : timeElementaryLp P T hT F hF hle a b G hG hg=0 := by
      apply Lp.ext
      have hh := (time_elementary_memLp P T hT F hF hle a b G hG hg).coeFn_toLp
      have hempty : Ico a b=∅ := Ico_eq_empty_of_le (le_of_not_ge hab)
      exact hh.trans ((Filter.EventuallyEq.of_eq (by funext z; simp [hempty])).trans
        (Lp.coeFn_zero ℝ 2 _).symm)
    rw [hz,map_zero,map_zero]
    intro f
    simp

end Asakura.Chapter12
