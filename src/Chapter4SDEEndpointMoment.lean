import Chapter4EulerStrongManuscript
import Chapter4PathEvaluationMoment

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

theorem sde_finite_path_memLp
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T) (hTinf : T=⊤) {dim noise : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W C : Fin noise → ClosedTime T → Ω → ℝ)
    (hW : ∀ j,LocalMProcessWitness P F (W j))
    (hC : ∀ j,LocalCovarianceWitness P F (W j) (W j) (C j))
    (hclock : ∀ j w (r : ℝ),0≤r → (r:EReal)<T → C j (realTimeClamp r) w=r)
    (L : ℝ) (hL : 0≤L)
    (μ : Fin dim → (Fin dim → ℝ) → ℝ) (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (hLip : ∀ x y,(∑ i,(μ i x-μ i y)^2)+(∑ i,∑ j,(σ i j x-σ i j y)^2)≤L*∑ i,(x i-y i)^2)
    (ξ : Ω → Fin dim → ℝ) (hξ : MemLp ξ 2 P)
    (X : ClosedTime T → Ω → Fin dim → ℝ) (hX : VectorSDESolution P F W μ σ ξ X)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T) :
    Measurable[m] (Vector.realVectorPath X hX.path R hRT) ∧
    MemLp (Vector.realVectorPath X hX.path R hRT) 2 P ∧ MemLp (X (realTimeClamp R)) 2 P := by
  obtain ⟨hμc,hσc,hμ,hσ⟩ := Vector.manuscript_lipschitz_coordinates μ σ L hL hLip
  obtain ⟨K,hK,hμg,hσg⟩ := Vector.vector_lipschitz_growth μ σ (L*dim) (by positivity) hμ hσ
  let K' := K*(dim+1)
  have hK' : 0≤K' := by dsimp only [K'];positivity
  have hμg' i x : (μ i x)^2≤K'*(1+‖x‖^2) := vector_square_growth_norm x _ K hK (hμg i x)
  have hσg' i j x : (σ i j x)^2≤K'*(1+‖x‖^2) := vector_square_growth_norm x _ K hK (hσg i j x)
  obtain ⟨N,hN,hNI,hNe⟩ := hX.integrals
  let Y := Vector.realVectorPath X hX.path R hRT
  have hYm : Measurable[m] Y := ContinuousMap.measurable_iff_eval.mpr (fun r =>
    (hX.adapted _ (real_time_below r.val r.property.1 ((EReal.coe_le_coe r.property.2).trans_lt hRT))).mono (hle _) le_rfl)
  have hYi : MemLp Y 2 P := by
    simpa only [ENNReal.ofReal_ofNat] using
      Vector.global_sde_power_moment P hT hTinf F hF hle hnull W C hW hC hclock μ σ
        (fun i => (hμc i).measurable) (fun i j => (hσc i j).measurable) K' hK' hμg' hσg'
        2 (by norm_num) ξ (hX.initial_adapted.mono (hle ⊥) le_rfl) (by simpa using hξ)
        X hX.adapted hX.path N hN hNI hNe R hR hRT
  exact ⟨hYm,hYi,random_path_evaluation_memLp P Y hYm hYi ⟨R,right_mem_Icc.mpr hR⟩⟩

end Asakura.Chapter4
