import Chapter8SDECanonicalIdentification
import Chapter8TransitionDerivativeBounds

open MeasureTheory Set
open scoped NNReal
namespace Asakura.Chapter8
open Asakura.Chapter4 Asakura.Chapter3Complete Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- C2 regularity and uniform derivative bounds for the existing actual
SDE family, obtained by identifying it with the constructed smooth flow. -/
theorem actual_transition_regularity {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ}
    (B : BrownianSystem P n) (b : (Fin d → ℝ) → (Fin d → ℝ))
    (σ : Fin d → Fin n → ℝ)
    (D : (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
    (D₂ : (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
    (hD : ∀ z,HasFDerivAt b (D z) z) (hD₂ : ∀ z,HasFDerivAt D (D₂ z) z)
    (hcD₂ : Continuous D₂) (C L : ℝ≥0) (hDC : LipschitzWith C D)
    (hL : 0<L) (hDb : ∀ z,‖D z‖ ≤ (L:ℝ))
    (Z : (Fin d → ℝ) → HalfClosedTime → Ω → Fin d → ℝ)
    (hZ : ∀ x,VectorSDESolution P B.F B.W (fun i y => b y i) (fun i j _ => σ i j) (fun _ => x) (Z x))
    (T : ℝ) (hT : 0≤T)
    (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ 2 f)
    (B₀ B₁ B₂ : ℝ) (hB₁ : 0≤B₁) (hB₂ : 0≤B₂)
    (hfb : ∀ x,‖f x‖≤B₀) (hDfb : ∀ x,‖fderiv ℝ f x‖≤B₁)
    (hD₂fb : ∀ x,‖fderiv ℝ (fderiv ℝ f) x‖≤B₂) :
    ∃ A K : ℝ,0≤A ∧ 0≤K ∧ ∀ t : ℝ,t∈Icc 0 T →
      ContDiff ℝ 2 (fun x => ∫ w,f (Z x (realTimeClamp t) w) ∂P) ∧
      (∀ x,‖fderiv ℝ (fun y => ∫ w,f (Z y (realTimeClamp t) w) ∂P) x‖≤A) ∧
      (∀ x,‖fderiv ℝ (fderiv ℝ (fun y => ∫ w,f (Z y (realTimeClamp t) w) ∂P)) x‖≤K) := by
  have hLip : LipschitzWith L b := by
    apply lipschitzWith_of_nnnorm_fderiv_le (fun z => (hD z).differentiableAt)
    intro z
    rw [(hD z).fderiv]
    exact_mod_cast hDb z
  obtain ⟨V,hVm,hV⟩ := brownian_forcing_path P B σ T
  have hf1 : ContDiff ℝ 1 (fderiv ℝ f) := (contDiff_succ_iff_fderiv (n := 1)).mp hf |>.2.2
  obtain ⟨S,hSc,hS,hreg⟩ := constructed_transition_C2_bounds P b D D₂ hD hD₂ hcD₂ C L hDC hL hDb
    T hT V hVm f (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f))
    (fun z => (hf.differentiable (by norm_num)).differentiableAt.hasFDerivAt)
    (fun z => (hf1.differentiable (by norm_num)).differentiableAt.hasFDerivAt)
    (hf1.continuous_fderiv (by norm_num)) B₀ B₁ B₂ hB₁ hB₂ hfb hDfb hD₂fb
  refine ⟨B₁*Real.exp (((L:ℝ)+1)*T),
    B₁*((C:ℝ)*Real.exp (((L:ℝ)+1)*T)^2*T*Real.exp ((L:ℝ)*T))+B₂*Real.exp (((L:ℝ)+1)*T)^2,
    by positivity,by positivity,?_⟩
  intro t ht
  have he : (fun x => ∫ w,f (Z x (realTimeClamp t) w) ∂P)=
      fun x => ∫ w,f (S (x,V w) ⟨t,ht⟩) ∂P := by
    funext x
    apply integral_congr_ae
    exact (sde_canonical_identification P B b σ L hLip T hT V hV S hS x (Z x) (hZ x)).mono
      (fun w hw => congrArg f (hw ⟨t,ht⟩))
  rw [he]
  exact hreg ⟨t,ht⟩

end Asakura.Chapter8
