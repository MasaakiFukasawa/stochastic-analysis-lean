import Chapter12BrownianMalliavinOperator
import Chapter12BrownianRepresentation
import Chapter12TerminalCompactIto
import Chapter12AdaptedVectorDivergence

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter4 Asakura.Chapter5
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000

theorem divergence_ito_constructed_brownian_operator {Ω : Type*} [MeasurableSpace Ω]
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
  have hop := brownian_finite_malliavin_operator P B T hT 2 2 (by simp) (by simp) hgen
  obtain ⟨I₀,L,hL,hI₀,hrep⟩ := brownian_system_representation P B c hc hcm hct hcut hcc hco
  have hi := fun i => terminal_compact_ito_exists P B i c (I₀ i) (hI₀ i) T hT
  have hXm := brownian_time_coordinate_measurable P B T
  have hXc := brownian_time_coordinate_continuous P B T
  have hnull (t : Icc (0:ℝ) T) (N : Set Ω)
      (hm : MeasurableSet[B.F (realTimeClamp T)] N)
      (hz : (P.trim (B.le (realTimeClamp T))) N=0) :
      MeasurableSet[B.F (realTimeClamp t.val)] N := by
    apply B.null _ N ((B.le _) N hm)
    rwa [trim_measurableSet_eq (B.le _) hm] at hz
  let R := P.trim (B.le (realTimeClamp T))
  let Fc := fun t : Icc (0:ℝ) T => B.F (realTimeClamp t.val)
  let hle := fun t : Icc (0:ℝ) T => B.mono (real_time_clamp_mono t.property.2)
  let hFc := B.mono.comp (real_time_clamp_mono.comp (Subtype.mono_coe (·∈Icc (0:ℝ) T)))
  letI := probability_trim P _ (B.le (realTimeClamp T))
  letI : MeasurableSpace Ω := B.F (realTimeClamp T)
  letI := finite_horizon_L2_nontrivial T hT
  dsimp only at hop hi ⊢
  obtain ⟨W,hW,D,hclos,hclosed,hcomplete,hgraph,hgraphClosed,hdom,hX⟩ := hop
  choose I hI using hi
  refine ⟨W,hW,D.closure,hclosed,hgraphClosed,I,hI,?_⟩
  apply adapted_vector_divergence R T hT.le Fc hle D.closure (fun i => (I i).toContinuousLinearMap)
  intro i
  exact adapted_divergence_from_actual_steps R T hT Fc hFc hle hnull W hW
    _ hXm hXc hX hnat D.closure hgraphClosed i (I i).toContinuousLinearMap (hI i)

end Asakura.Chapter12
