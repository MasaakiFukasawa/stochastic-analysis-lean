import UnitBrownianExists
import AllHolderExponents
import ContinuousGluing

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace Asakura

theorem unit_brownian_zero_exists :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω),
      IsProbabilityMeasure P ∧ ∃ Y : UnitCube 1 → Ω → ℝ,
      (∀ t, Measurable (Y t)) ∧ (∀ ω, Continuous (fun t => Y t ω)) ∧
      (∀ ω, Y cubeZero ω = 0) ∧ IsGaussianProcess Y P ∧
      (∀ t, (∫ ω, Y t ω ∂P) = 0) ∧
      (∀ s t, (∫ ω, Y s ω * Y t ω ∂P) = min (s.val 0) (t.val 0)) ∧
      ∀ᵐ ω ∂P, ∀ α : ℝ, 0 ≤ α → α < 1/2 →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ s t,
          dist (Y s ω) (Y t ω) ≤ C * (dist s t)^α := by
  obtain ⟨Ω,mΩ,P,hP,Y,hYm,hYc,hG,hm,hc,hH⟩ := unit_brownian_exists
  letI := mΩ
  letI := hP
  have h0law : HasLaw (Y cubeZero) (gaussianReal 0 0) P := by
    refine ⟨(hYm _).aemeasurable, ?_⟩
    rw [(hG.hasGaussianLaw_eval cubeZero).map_eq_gaussianReal, hm,
      variance_eq_sub (hG.hasGaussianLaw_eval cubeZero).memLp_two, hm]
    have hcc := hc cubeZero cubeZero
    rw [min_self] at hcc
    change (∫ ω, Y cubeZero ω * Y cubeZero ω ∂P) = 0 at hcc
    simp only [pow_two, Pi.mul_apply] at *
    rw [hcc]
    simp
  have h0 : Y cubeZero =ᵐ[P] (fun _ => 0) := by
    rw [gaussianReal_zero_var] at h0law
    exact h0law.ae_eq_of_dirac
  let Z : UnitCube 1 → Ω → ℝ := fun t ω => Y t ω - Y cubeZero ω
  have he (t : UnitCube 1) : Z t =ᵐ[P] Y t := by
    filter_upwards [h0] with ω hω
    simp [Z,hω]
  refine ⟨Ω,mΩ,P,hP,Z,fun t => (hYm t).sub (hYm _),
    fun ω => (hYc ω).sub continuous_const, fun ω => sub_self _,
    hG.congr (fun t => (he t).symm),?_,?_,?_⟩
  · intro t
    exact (integral_congr_ae (he t)).trans (hm t)
  · intro s t
    exact (integral_congr_ae ((he s).mul (he t))).trans (hc s t)
  · have hall := holder_all_exponents_common_event P Y (1/2)
      (fun s t => cube_diameter 1 s.val t.val s.property t.property) hH
    filter_upwards [hall] with ω hω
    intro α hα hαh
    obtain ⟨C,hC,hbound⟩ := hω α hα hαh
    refine ⟨C,hC,?_⟩
    intro s t
    simpa [Z, Real.dist_eq] using hbound s t
end Asakura
