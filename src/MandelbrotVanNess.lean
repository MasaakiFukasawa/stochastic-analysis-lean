import MVNGaussian
import HalfLineModification
import FractionalHolder

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal
namespace Asakura

/-- Mandelbrot–Van Ness, using the explicit standard deterministic Itô-integral
interface. The theorem constructs a continuous modification of the L2-defined
integrals and proves the full covariance and simultaneous local Holder property.
Constructing the Chapter 2 Itô maps is not assumed to have been formalized here. -/
theorem mandelbrot_van_ness {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (I : IndependentWienerIntegrals P)
    (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1) :
    ∃ Y : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable (Y t)) ∧ (∀ ω, Continuous (fun t => Y t ω)) ∧
      (∀ t, Y t =ᵐ[P] (mvnProcessLp I H hH0 hH1 t : Ω → ℝ)) ∧
      IsGaussianProcess Y P ∧ (∀ t, (∫ ω, Y t ω ∂P) = 0) ∧
      (∀ s t, (∫ ω, Y s ω * Y t ω ∂P) =
        ((s:ℝ)^(2*H)+(t:ℝ)^(2*H)-|(s:ℝ)-(t:ℝ)|^(2*H))/2) ∧
      ∀ᵐ ω ∂P, ∀ α : ℝ, 0 ≤ α → α < H → ∀ N : ℕ,
        ∃ C : ℝ, 0 ≤ C ∧ ∀ s t : ℝ≥0, s ≤ N → t ≤ N →
          dist (Y s ω) (Y t ω) ≤ C * (dist s t)^α := by
  let X : ℝ≥0 → Ω → ℝ := fun t => mvnProcessLp I H hH0 hH1 t
  have hXm (t : ℝ≥0) : Measurable (X t) := (Lp.stronglyMeasurable _).measurable
  have hXg : IsGaussianProcess X P := mvn_process_gaussian I H hH0 hH1
  have hm (t : ℝ≥0) : (∫ ω, X t ω ∂P) = 0 := mvn_process_mean I H hH0 hH1 t
  have hc (s t : ℝ≥0) : (∫ ω, X s ω * X t ω ∂P) =
      ((s:ℝ)^(2*H)+(t:ℝ)^(2*H)-|(s:ℝ)-(t:ℝ)|^(2*H))/2 := mvn_process_covariance I H hH0 hH1 s t
  have hX0 : X 0 =ᵐ[P] (fun _ => 0) := by
    change (mvnProcessLp I H hH0 hH1 0 : Ω → ℝ) =ᵐ[P] (fun _ => 0)
    rw [mvn_process_zero]
    exact Lp.coeFn_zero ℝ 2 P
  have hb : ∀ p : ℝ≥0, 1 ≤ p → ∃ c : ℝ, 0 ≤ c ∧ ∀ s t,
      eLpNorm (X s-X t) p P ≤ ENNReal.ofReal (c*(dist s t)^H) := by
    intro p hp
    let C := eLpNorm id p (gaussianReal 0 1)
    have hC : C ≠ ∞ := (memLp_id_gaussianReal p).eLpNorm_ne_top
    refine ⟨C.toReal,ENNReal.toReal_nonneg,?_⟩
    intro s t
    rw [fractional_increment_norm X hXg (fun t => (t:ℝ)) H hH0 hm hc p s t]
    change ENNReal.ofReal (|(s:ℝ)-(t:ℝ)|^H)*C ≤
      ENNReal.ofReal (C.toReal*(dist (s:ℝ) (t:ℝ))^H)
    rw [Real.dist_eq,ENNReal.ofReal_mul ENNReal.toReal_nonneg,ENNReal.ofReal_toReal hC]
    exact le_of_eq (mul_comm _ _)
  obtain ⟨Y,hYm,hYc,hYX⟩ := half_line_power_modification P X hXm hX0 H hH0 hb
  have hYg := hXg.congr (fun t => (hYX t).symm)
  have hYm0 (t : ℝ≥0) : (∫ ω, Y t ω ∂P) = 0 := (integral_congr_ae (hYX t)).trans (hm t)
  have hYcov (s t : ℝ≥0) : (∫ ω, Y s ω * Y t ω ∂P) =
      ((s:ℝ)^(2*H)+(t:ℝ)^(2*H)-|(s:ℝ)-(t:ℝ)|^(2*H))/2 :=
    (integral_congr_ae ((hYX s).mul (hYX t))).trans (hc s t)
  exact ⟨Y,hYm,hYc,hYX,hYg,hYm0,hYcov,
    fractional_brownian_local_holder Y hYm hYc hYg H hH0 hYm0 hYcov⟩
end Asakura
