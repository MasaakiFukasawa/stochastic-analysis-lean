import Chapter4EulerFixedHorizon
import Chapter4VectorLipschitzGrowth
import Chapter4VectorPowerGrowth

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

/-- Manuscript Euler theorem: a single constant works for every L2 initial
value, every solution, and every positive subdivision count. The actual
Euler recursion is constructed and has the squared 1/n and root 1/sqrt(n)
rates. Finite-dimensional norm comparison only changes the constant. -/
theorem euler_strong_rate_manuscript
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
      (∫ w,‖Vector.realVectorPath X hX.path R hRT w-V w‖^2 ∂P)≤C*(1+∫ w,‖ξ w‖^2 ∂P)/(n:ℝ) ∧
      Real.sqrt (∫ w,‖Vector.realVectorPath X hX.path R hRT w-V w‖^2 ∂P)≤
        Real.sqrt (C*(1+∫ w,‖ξ w‖^2 ∂P))/Real.sqrt (n:ℝ) := by
  obtain ⟨hμc,hσc,hμ,hσ⟩ := Vector.manuscript_lipschitz_coordinates μ σ L hL hLip
  let L' := L*(dim:ℝ)
  have hL' : 0≤L' := by dsimp only [L'];positivity
  obtain ⟨K,hK,hμg,hσg⟩ := Vector.vector_lipschitz_growth μ σ L' hL' hμ hσ
  let K' := K*(dim+1)
  have hK' : 0≤K' := by dsimp only [K'];positivity
  have hμg' i x : (μ i x)^2≤K'*(1+‖x‖^2) := vector_square_growth_norm x _ K hK (hμg i x)
  have hσg' i j x : (σ i j x)^2≤K'*(1+‖x‖^2) := vector_square_growth_norm x _ K hK (hσg i j x)
  let C0 := eulerStrongStepConstant R L' K' dim noise
  have hC0 : 0≤C0 := euler_strong_step_constant_nonneg R L' K' hR hL' hK' dim noise
  refine ⟨C0*R,mul_nonneg hC0 hR,?_⟩
  intro ξ hξa hξ X hX n hn
  have hnn : (n:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have he : (n:ℝ)*(R/(n:ℝ))=R := by field_simp
  have hh : 0≤R/(n:ℝ) := div_nonneg hR (Nat.cast_nonneg n)
  have hnT : (((n:ℝ)*(R/(n:ℝ)) : ℝ):EReal)<T := by rw [he];exact hRT
  have hresult := euler_strong_error_fixed_horizon P hT hTinf F hF hle hnull W C hW hC hclock
    μ σ L' hL' hμ hσ ξ hξa hξ (R/(n:ℝ)) hh n R he hRT K' hK' hμg' hσg' X hX
  obtain ⟨V,hVm,hVi,hVa,hV,hb⟩ := hresult
  have hb' : (∫ w,‖Vector.realVectorPath X hX.path R hRT w-V w‖^2 ∂P)≤(C0*R)*(1+∫ w,‖ξ w‖^2 ∂P)/(n:ℝ) := by
    convert hb using 1 <;> dsimp only [C0] <;> ring
  refine ⟨V,hVm,hVi,hVa,hV,hb',?_⟩
  exact euler_root_rate _ _ n (integral_nonneg (fun w => sq_nonneg _))
    (mul_nonneg (mul_nonneg hC0 hR) (by positivity)) hb'

end Asakura.Chapter4
