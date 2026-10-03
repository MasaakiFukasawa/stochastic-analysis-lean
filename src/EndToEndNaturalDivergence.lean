import Chapter12DivergenceItoConstructed
import Chapter12VectorNaturalInformation
import Chapter12BasketNaturalSelfFinancing

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology
namespace Asakura.EndToEnd
open Asakura.Chapter12 Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter4 Asakura.Chapter5
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000

/-- The closed divergence agrees with the actual vector Ito integral on the
completed natural Brownian filtration. Auxiliary exhaustion and information
generation data are derived internally. -/
theorem natural_brownian_divergence_ito {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P (d+1))
    (T : ℝ) (hT : 0<T) [Fact (0≤T)]
    (hnatural : ∀ a : Icc (0:ℝ) T,B.F (realTimeClamp a.val)=Asakura.nullAugmentation P
      (MeasurableSpace.comap (fun w z => brownianTimeCoordinate P B a.val z w) inferInstance)) :
    let Fc := fun t : Icc (0:ℝ) T => B.F (realTimeClamp t.val)
    let R := P.trim (B.le (realTimeClamp T))
    let hle := fun t : Icc (0:ℝ) T => B.mono (real_time_clamp_mono t.property.2)
    letI := probability_trim P _ (B.le (realTimeClamp T))
    letI : MeasurableSpace Ω := B.F (realTimeClamp T)
    letI := finite_horizon_L2_nontrivial T hT
    ∃ W : FiniteWienerHilbert d T →ₗᵢ[ℝ] Lp ℝ 2 R,
    ∃ hW : ∀ h,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) R,
    ∃ D : Lp ℝ 2 R →ₗ.[ℝ] Lp (FiniteWienerHilbert d T) 2 R,
      D.IsClosed ∧
      (D.graph : Set _) = closure (range (cylinderPair R W univ dense_univ (fun h _ => hW h) 2 (by simp))) ∧
    letI : MeasurableSpace (Ω × Icc (0:ℝ) T) := progressiveSpace Fc
    ∃ I : Fin (d+1) → Lp ℝ 2 ((R.prod (compactTimeMeasure T hT.le)).trim
      (progressive_space_le_product Fc hle)) →ₗᵢ[ℝ] Lp ℝ 2 R,
      (∀ i (a b : Icc (0:ℝ) T),a≤b → ∀ (G : Ω → ℝ)
        (hG : Measurable[Fc a] G) (hg : MemLp G ∞ R),
        (I i (timeElementaryLp R T hT Fc
          (B.mono.comp (real_time_clamp_mono.comp (Subtype.mono_coe _))) hle a b G hG hg) : Ω → ℝ)
          =ᵐ[R] (fun w => G w*(B.W i (realTimeClamp b.val) w-B.W i (realTimeClamp a.val) w))) ∧
      ∀ U : PiLp 2 (fun _ : Fin (d+1) => Lp ℝ 2 ((R.prod (compactTimeMeasure T hT.le)).trim
        (progressive_space_le_product Fc hle))),
        IsDivergence D (adaptedWienerEmbedding R T hT.le Fc hle U) (∑ i,I i (U i)) := by
  have hgen (U : Lp ℝ 2 (P.trim (B.le (realTimeClamp T)))) :=
    vector_natural_information_on_trim P B T T le_rfl (hnatural ⟨T,hT.le,le_rfl⟩) U
      (Lp.stronglyMeasurable U).measurable
  have hnat (a : Icc (0:ℝ) T) (G : Ω → ℝ)
      (hG : Measurable[B.F (realTimeClamp a.val)] G) :=
    vector_natural_information_on_trim P B T a.val a.property.2 (hnatural a) G hG
  obtain ⟨hc,hcm,hct,hcut,hcc,hco⟩ := canonical_clock_properties
  exact divergence_ito_constructed_brownian_operator P B canonicalClock hc hcm hct hcut hcc hco
    T hT hgen hnat

#print axioms natural_brownian_divergence_ito
end Asakura.EndToEnd
