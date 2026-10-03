import Chapter8CoordinatePathContraction
import Chapter8SDECanonicalIdentification
import Chapter8AdditivePathMap

open MeasureTheory Set
open scoped NNReal RealInnerProductSpace
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter4 Asakura.Chapter3Complete
open Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Construct a jointly measurable SDE endpoint with a contraction bound
holding for every forcing path and every pair of initial states. -/
theorem canonical_sde_endpoint_contraction {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (e : (Fin d → ℝ) ≃L[ℝ] E) (g : (Fin d → ℝ) → (Fin d → ℝ))
    (K : ℝ≥0) (hg : LipschitzWith K g) (σ : Fin d → Fin n → ℝ)
    (κ : ℝ) (hm : ∀ x y,κ*‖e x-e y‖^2≤⟪e x-e y,e (g x)-e (g y)⟫)
    (Z : (Fin d → ℝ) → HalfClosedTime → Ω → Fin d → ℝ)
    (hZ : ∀ x,VectorSDESolution P B.F B.W (fun i y => -(g y i)) (fun i j _ => σ i j) (fun _ => x) (Z x))
    (T : ℝ) (hT : 0≤T) :
    ∃ F : (Fin d → ℝ) × Ω → (Fin d → ℝ),Measurable F ∧
      (∀ x,(fun w => F (x,w))=ᵐ[P] Z x (realTimeClamp T)) ∧
      ∀ w x y,‖e (F (x,w))-e (F (y,w))‖≤Real.exp (-κ*T)*‖e x-e y‖ := by
  let b := fun x => -g x
  have hb : LipschitzWith K b := hg.neg
  obtain ⟨V,hVm,hV⟩ := brownian_forcing_path P B σ T
  obtain ⟨S,hSc,hS⟩ := additive_path_map_exists b K hb T hT
  let F := fun p : (Fin d → ℝ) × Ω => S (p.1,V p.2) ⟨T,⟨hT,le_rfl⟩⟩
  have hFm : Measurable F := (ContinuousMap.measurable_iff_eval.mp
    (hSc.measurable.comp (measurable_fst.prodMk (hVm.comp measurable_snd)))) _
  have hFe x : (fun w => F (x,w))=ᵐ[P] Z x (realTimeClamp T) :=
    (sde_canonical_identification P B b σ K hb T hT V hV S hS x (Z x) (hZ x)).mono
      (fun w hw => (hw ⟨T,⟨hT,le_rfl⟩⟩).symm)
  refine ⟨F,hFm,hFe,?_⟩
  intro w x y
  let R := fun x r => S (x,V w) (projIcc 0 T hT r)
  let W := fun r => V w (projIcc 0 T hT r)
  have hc z : Continuous (R z) := (S (z,V w)).continuous.comp continuous_projIcc
  have he z r (hr : r∈Icc 0 T) : R z r=z-(∫ s in 0..r,g (R z s))+W r := by
    have hp : projIcc 0 T hT r=⟨r,hr⟩ := projIcc_of_mem hT hr
    change S (z,V w) (projIcc 0 T hT r)=_
    rw [hp,hS]
    simp only [b,R,W,hp,intervalIntegral.integral_neg,sub_eq_add_neg]
  have hh := coordinate_path_contraction e g hg.continuous κ T hT hm
    (R x) (R y) W x y (hc x) (hc y) (he x) (he y) T ⟨hT,le_rfl⟩
  simpa only [R,F,projIcc_of_mem hT (show T∈Icc 0 T from ⟨hT,le_rfl⟩)] using hh

end Asakura.Chapter8
