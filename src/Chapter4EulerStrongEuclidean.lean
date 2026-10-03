import Chapter4EulerNormComparison

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- The final Euler theorem with the Euclidean squared maximum, as printed
in the manuscript. No approximation or error estimate is an input. -/
theorem euler_strong_rate_euclidean
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

    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T) :
    ∃ C : ℝ,0≤C ∧ ∀ (ξ : Ω → Fin dim → ℝ) (hξa : Measurable[F ⊥] ξ) (hξ : MemLp ξ 2 P)
      (X : ClosedTime T → Ω → Fin dim → ℝ) (hX : VectorSDESolution P F W μ σ ξ X)
      (n : ℕ),0<n → ∃ V : Ω → C(Icc (0:ℝ) R,Fin dim → ℝ),
      Measurable[m] V ∧ MemLp V 2 P ∧
      (∀ r,Measurable[F (realTimeClamp r.val)] (fun w => V w r)) ∧
      (∀ w r,V w r=eulerInterpolation μ σ (fun j r => W j (realTimeClamp r)) ξ (R/(n:ℝ)) n r.val w) ∧
      (∫ w,‖squaredEuclideanPath (Vector.realVectorPath X hX.path R hRT w-V w)‖ ∂P)≤C*(1+∫ w,(∑ i,(ξ w i)^2) ∂P)/(n:ℝ) ∧
      Real.sqrt (∫ w,‖squaredEuclideanPath (Vector.realVectorPath X hX.path R hRT w-V w)‖ ∂P)≤
        Real.sqrt (C*(1+∫ w,(∑ i,(ξ w i)^2) ∂P))/Real.sqrt (n:ℝ) := by
  obtain ⟨C0,hC0,hall⟩ := euler_strong_rate_manuscript P hT hTinf F hF hle hnull W C hW hC hclock L hL μ σ hLip R hR hRT
  refine ⟨(dim:ℝ)*C0,mul_nonneg (Nat.cast_nonneg dim) hC0,?_⟩
  intro ξ hξa hξ X hX n hn
  obtain ⟨V,hVm,hVi,hVa,hV,hb,_⟩ := hall ξ hξa hξ X hX n hn
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
        2 (by norm_num) ξ (hξa.mono (hle ⊥) le_rfl) (by simpa using hξ) X hX.adapted hX.path N hN hNI hNe R hR hRT
  have he := euler_euclidean_rate_transfer P (fun w => Y w-V w) (hYm.sub hVm) (hYi.sub hVi) ξ hξ C0 hC0 n hb
  refine ⟨V,hVm,hVi,hVa,hV,he,?_⟩
  exact euler_root_rate _ _ n (integral_nonneg (fun w => norm_nonneg _))
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg dim) hC0)
      (add_nonneg zero_le_one (integral_nonneg (fun w => Finset.sum_nonneg (fun _ _ => sq_nonneg _))))) he

end Asakura.Chapter4
