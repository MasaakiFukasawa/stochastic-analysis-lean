import UnitGaussianExists
import BrownianCube

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace Asakura
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- One continuous modification works for every exponent below one half. -/
theorem brownian_cube_common_modification (X : UnitCube 1 → Ω → ℝ)
    (hX : ∀ t, Measurable (X t)) (hG : IsGaussianProcess X P)
    (hm : ∀ t, (∫ ω, X t ω ∂P) = 0)
    (hc : ∀ s t, (∫ ω, X s ω * X t ω ∂P) = min (s.val 0) (t.val 0)) :
    ∃ Y : UnitCube 1 → Ω → ℝ,
      (∀ t, Measurable (Y t)) ∧ (∀ ω, Continuous (fun t => Y t ω)) ∧
      (∀ t, Y t =ᵐ[P] X t) ∧
      ∀ α : ℝ, 0 < α → α < 1/2 →
        ∀ᵐ ω ∂P, ∃ C : ℝ, 0 ≤ C ∧ ∀ s t,
          dist (Y s ω) (Y t ω) ≤ C * (dist s t)^α := by
  obtain ⟨Y,M,hYm,hYc,hYX,hMm,hM0,hYH⟩ :=
    brownian_cube_holder_modification X hX hG hm hc (1/4) (by norm_num) (by norm_num)
  refine ⟨Y,hYm,hYc,hYX,?_⟩
  intro α hα hαh
  obtain ⟨Z,N,hZm,hZc,hZX,hNm,hN0,hZH⟩ :=
    brownian_cube_holder_modification X hX hG hm hc α hα hαh
  have heq : ∀ᵐ ω ∂P, (fun t => Y t ω) = (fun t => Z t ω) :=
    continuous_modifications_agree P (DyadicSet 1) (dyadicSet_dense 1)
      (dyadicSet_countable 1) Y Z (Eventually.of_forall hYc) (Eventually.of_forall hZc)
      (fun t => (hYX t).trans (hZX t).symm)
  filter_upwards [heq] with ω hω
  refine ⟨N ω,hN0 ω,?_⟩
  intro s t
  simpa only [congrFun hω s, congrFun hω t] using hZH ω s t

/-- Brownian motion on the unit cube, including existence of the probability space,
Gaussian finite-dimensional distributions and all positive Holder exponents < 1/2. -/
theorem unit_brownian_exists :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω),
      IsProbabilityMeasure P ∧ ∃ Y : UnitCube 1 → Ω → ℝ,
      (∀ t, Measurable (Y t)) ∧ (∀ ω, Continuous (fun t => Y t ω)) ∧
      IsGaussianProcess Y P ∧ (∀ t, (∫ ω, Y t ω ∂P) = 0) ∧
      (∀ s t, (∫ ω, Y s ω * Y t ω ∂P) = min (s.val 0) (t.val 0)) ∧
      ∀ α : ℝ, 0 < α → α < 1/2 →
        ∀ᵐ ω ∂P, ∃ C : ℝ, 0 ≤ C ∧ ∀ s t,
          dist (Y s ω) (Y t ω) ≤ C * (dist s t)^α := by
  obtain ⟨Ω,mΩ,P,hP,X,hXm,hG,hm,hc⟩ := unit_gaussian_process_exists
  letI := mΩ
  letI := hP
  let Z : UnitCube 1 → Ω → ℝ := fun t => X (t.val 0)
  have hZg : IsGaussianProcess Z P := hG.comp_right (fun t : UnitCube 1 => t.val 0)
  have hZc (s t : UnitCube 1) : (∫ ω, Z s ω * Z t ω ∂P) = min (s.val 0) (t.val 0) :=
    hc _ (s.property 0) _ (t.property 0)
  obtain ⟨Y,hYm,hYc,hYZ,hYH⟩ := brownian_cube_common_modification Z
    (fun t => hXm _) hZg (fun t => hm _) hZc
  refine ⟨Ω,mΩ,P,hP,Y,hYm,hYc,hZg.congr (fun t => (hYZ t).symm),?_,?_,hYH⟩
  · intro t
    rw [integral_congr_ae (hYZ t)]
    exact hm _
  · intro s t
    exact (integral_congr_ae ((hYZ s).mul (hYZ t))).trans (hZc s t)
end Asakura
