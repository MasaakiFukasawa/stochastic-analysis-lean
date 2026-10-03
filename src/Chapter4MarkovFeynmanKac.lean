import Chapter4ClassicalSolutionConditional
import Chapter4MarkovSmoothExtension

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false

/-- The manuscript's Markov theorem from classical solutions of the
backward equation. It starts with actual SDE solutions, derives all smooth
test identities by Feynman--Kac, constructs the measurable transition
kernel, and concludes for every bounded Borel test. -/
theorem markov_from_feynman_kac
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T) {dim noise : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W : Fin noise → ClosedTime T → Ω → ℝ)
    (B : Fin noise → Fin noise → ClosedTime T → Ω → ℝ)
    (hW : ∀ j,LocalMProcessWitness P F (W j))
    (hB : ∀ j k,LocalCovarianceWitness P F (W j) (W k) (B j k))
    (hclock : ∀ j k w (r : ℝ),0≤r → (r:EReal)<T → B j k (realTimeClamp r) w=if j=k then r else 0)
    (μ : Fin dim → (Fin dim → ℝ) → ℝ)
    (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (hμ : ∀ i,Continuous (μ i)) (hσ : ∀ i j,Continuous (σ i j))
    (ξ : Ω → Fin dim → ℝ) (X : ClosedTime T → Ω → Fin dim → ℝ)
    (hX : VectorSDESolution P F W μ σ ξ X)
    (Z : (Fin dim → ℝ) → ClosedTime T → Ω → Fin dim → ℝ)
    (hZ : ∀ x,VectorSDESolution P F W μ σ (fun _ => x) (Z x))
    (hclassical : ∀ f : (Fin dim → ℝ) → ℝ,ContDiff ℝ (⊤:ℕ∞) f → HasCompactSupport f →
      Nonempty (ClassicalForwardSolution μ σ f))
    (s t : ℝ) (htT : (t:EReal)<T) (hs : s∈Icc 0 t) :
    Measurable (fun x => P.map (Z x (realTimeClamp (t-s)))) ∧
    ∀ f : (Fin dim → ℝ) → ℝ,Measurable f → ∀ C : ℝ,(∀ x,‖f x‖≤C) →
      P[(fun w => f (X (realTimeClamp t) w)) | F (realTimeClamp s)]=ᵐ[P]
        fun w => ∫ y,f y ∂P.map (Z (X (realTimeClamp s) w) (realTimeClamp (t-s))) := by
  classical
  letI : MeasurableSpace Ω := m
  let ν := fun x => P.map (Z x (realTimeClamp (t-s)))
  have hu : 0≤t-s := sub_nonneg.mpr hs.2
  have huT : ((t-s):EReal)<T := (EReal.coe_le_coe (by linarith [hs.1] : t-s≤t)).trans_lt htT
  have hZm x : Measurable[m] (Z x (realTimeClamp (t-s))) :=
    ((hZ x).adapted _ (real_time_below (t-s) hu huT)).mono (hle _) le_rfl
  letI (x : Fin dim → ℝ) : IsProbabilityMeasure (ν x) :=
    (Measure.isProbabilityMeasure_map_iff (hZm x).aemeasurable).mpr inferInstance
  have htest (f : (Fin dim → ℝ) → ℝ) (hf : ContDiff ℝ (⊤:ℕ∞) f) (hfc : HasCompactSupport f) :
      Measurable (fun x => ∫ y,f y ∂ν x) ∧
      P[(fun w => f (X (realTimeClamp t) w)) | F (realTimeClamp s)]=ᵐ[P]
        fun w => ∫ y,f y ∂ν (X (realTimeClamp s) w) := by
    obtain ⟨v⟩ := hclassical f hf hfc
    have htrans x : v.value (t-s) x=∫ y,f y ∂ν x := by
      rw [show ν x=P.map (Z x (realTimeClamp (t-s))) from rfl,
        integral_map (hZm x).aemeasurable hf.continuous.aestronglyMeasurable]
      exact classical_solution_transition_expectation P hT F hF hle hnull W B hW hB hclock μ σ hμ hσ
        x (Z x) (hZ x) f v (t-s) hu huT
    have hvc : Continuous (v.value (t-s)) :=
      v.continuous.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => hu)
    refine ⟨?_,?_⟩
    · have heq : (fun x => ∫ y,f y ∂ν x)=v.value (t-s) := funext fun x => (htrans x).symm
      rw [heq]
      exact hvc.measurable
    · have hh := classical_solution_conditional P hT F hF hle hnull W B hW hB hclock μ σ hμ hσ
        ξ X hX f v s t htT hs
      simpa only [htrans] using hh
  exact markov_borel_of_smooth_compact_tests P (F (realTimeClamp s)) (hle _)
    (X (realTimeClamp s)) (X (realTimeClamp t))
    (hX.adapted _ (real_time_below s hs.1 ((EReal.coe_le_coe hs.2).trans_lt htT)))
    ((hX.adapted _ (real_time_below t (hs.1.trans hs.2) htT)).mono (hle _) le_rfl)
    ν (fun f hf hfc => (htest f hf hfc).1) (fun f hf hfc => (htest f hf hfc).2)

end Asakura.Chapter4
