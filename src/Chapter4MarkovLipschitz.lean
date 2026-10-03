import Chapter4SDEInitialConditionalLaw
import Chapter4MarkovSmoothExtension
import Mathlib.Analysis.Calculus.ContDiff.RCLike

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- The full Markov assertion under the manuscript Lipschitz hypothesis.
There is no PDE assumption, prescribed transition kernel, independence of
a solution, or restart identity among the hypotheses. -/
theorem markov_from_lipschitz_coefficients
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] {dim noise : ℕ}
    (B : BrownianSystem P noise)
    (L : ℝ) (hL : 0≤L)
    (μ : Fin dim → (Fin dim → ℝ) → ℝ) (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (hLip : ∀ x y,(∑ i,(μ i x-μ i y)^2)+(∑ i,∑ j,(σ i j x-σ i j y)^2)≤L*∑ i,(x i-y i)^2)
    (ξ : Ω → Fin dim → ℝ) (hξ : MemLp ξ 2 P)
    (X : HalfClosedTime → Ω → Fin dim → ℝ) (hX : VectorSDESolution P B.F B.W μ σ ξ X)
    (Z : (Fin dim → ℝ) → HalfClosedTime → Ω → Fin dim → ℝ)
    (hZ : ∀ x,VectorSDESolution P B.F B.W μ σ (fun _ => x) (Z x))
    (s u : ℝ) (hs : 0≤s) (hu : 0≤u) :
    Measurable (fun x => @Measure.map Ω _ m _ (Z x (realTimeClamp u)) P) ∧
    ∀ f : (Fin dim → ℝ) → ℝ,Measurable f → ∀ K : ℝ,(∀ x,‖f x‖≤K) →
      P[(fun w => f (X (realTimeClamp (s+u)) w)) | B.F (realTimeClamp s)]=ᵐ[P]
        fun w => ∫ y,f y ∂@Measure.map Ω _ m _ (Z (X (realTimeClamp s) w) (realTimeClamp u)) P := by
  classical
  letI : MeasurableSpace Ω := m
  let ν := fun x => P.map (Z x (realTimeClamp u))
  letI (x : Fin dim → ℝ) : IsProbabilityMeasure (ν x) := by dsimp only [ν];infer_instance
  have hZm x : Measurable[m] (Z x (realTimeClamp u)) :=
    ((hZ x).adapted _ (real_time_below u hu (EReal.coe_lt_top u))).mono (B.le _) le_rfl
  obtain ⟨hμ,hσ,_,_⟩ := Vector.manuscript_lipschitz_coordinates μ σ L hL hLip
  have hclock j w (r : ℝ) hr (_ : (r:EReal)<⊤) := B.diagonal_clock j w r hr
  have hXi := (sde_finite_path_memLp P (EReal.coe_lt_top 0) rfl B.F B.mono B.le B.null
    B.W (fun j => B.C j j) B.martingale (fun j => B.cov j j) hclock L hL μ σ hLip ξ hξ X hX s hs (EReal.coe_lt_top s)).2.2
  let Y := fun t => X (deterministicTimeShift s hs t)
  have hY : VectorSDESolution P (B.shift s hs).F (B.shift s hs).W μ σ (X (realTimeClamp s)) Y := by
    have hh := vector_sde_deterministic_restart P B.F B.mono B.le B.null B.W (fun j => B.C j j)
      B.martingale (fun j => B.cov j j) B.diagonal_clock μ σ hμ hσ ξ X hX s hs
    simpa only [BrownianSystem.shift,deterministic_shift_bot] using hh
  have htest (f : (Fin dim → ℝ) → ℝ) (hf : ContDiff ℝ (⊤:ℕ∞) f) (hfc : HasCompactSupport f) :
      Measurable (fun x => ∫ y,f y ∂ν x) ∧
      P[(fun w => f (X (realTimeClamp (s+u)) w)) | B.F (realTimeClamp s)]=ᵐ[P]
        fun w => ∫ y,f y ∂ν (X (realTimeClamp s) w) := by
    obtain ⟨Lf,hLf⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hfc hf (by simp)
    obtain ⟨K,hK⟩ := hfc.exists_bound_of_continuous hf.continuous
    obtain ⟨hm,_,he⟩ := sde_initial_conditional_transition P (B.shift s hs) B L hL μ σ hLip
      (X (realTimeClamp s)) hXi Y hY Z hZ u hu f Lf hLf K hK
    have hmap x : (∫ y,f y ∂ν x)=∫ w,f (Z x (realTimeClamp u) w) ∂P :=
      integral_map (hZm x).aemeasurable hf.continuous.aestronglyMeasurable
    constructor
    · simpa only [hmap] using hm
    · simpa only [Y,BrownianSystem.shift,deterministic_shift_bot,
        deterministic_shift_real s hs u hu,hmap] using he
  exact markov_borel_of_smooth_compact_tests P (B.F (realTimeClamp s)) (B.le _)
    (X (realTimeClamp s)) (X (realTimeClamp (s+u)))
    (hX.adapted _ (real_time_below s hs (EReal.coe_lt_top s)))
    ((hX.adapted _ (real_time_below (s+u) (add_nonneg hs hu) (EReal.coe_lt_top _))).mono (B.le _) le_rfl)
    ν (fun f hf hfc => (htest f hf hfc).1) (fun f hf hfc => (htest f hf hfc).2)

end Asakura.Chapter4
