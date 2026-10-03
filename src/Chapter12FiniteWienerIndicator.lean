import Chapter12WienerIndicator
import Chapter12WienerCoordinatesExist
import Chapter12PiIsometry

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
namespace Asakura.Chapter12
open Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

noncomputable def finiteTimeIntervalVector (T a b : ℝ) :
    Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T)) :=
  indicatorConstLp 2 measurableSet_Ioc
    (ne_of_lt ((Measure.restrict_apply_le (Iic T) (Ioc a b)).trans_lt
      (lt_top_iff_ne_top.mpr (half_line_interval_measure_ne_top a b)))) (1:ℝ)

theorem zero_extension_interval (T a b : ℝ) (hb : b ≤ T) :
    L2ZeroExtension (volume.restrict (Ioi (0:ℝ))) (Iic T) measurableSet_Iic
      (finiteTimeIntervalVector T a b) = timeIntervalVector a b := by
  apply Lp.ext
  have hf : (finiteTimeIntervalVector T a b : ℝ → ℝ) =ᵐ[(volume.restrict (Ioi (0:ℝ))).restrict (Iic T)]
      (Ioc a b).indicator (fun _ => (1:ℝ)) := indicatorConstLp_coeFn
  have hh := (ae_eq_restrict_iff_indicator_ae_eq measurableSet_Iic).mp hf
  have hg : (timeIntervalVector a b : ℝ → ℝ) =ᵐ[volume.restrict (Ioi (0:ℝ))]
      (Ioc a b).indicator (fun _ => (1:ℝ)) := indicatorConstLp_coeFn
  filter_upwards [L2ZeroExtension_coe (volume.restrict (Ioi (0:ℝ))) (Iic T)
    measurableSet_Iic (finiteTimeIntervalVector T a b),hh,hg] with x hx hy hz
  rw [hx,hy,hz]
  by_cases h : x ∈ Ioc a b
  · have ht : x ∈ Iic T := h.2.trans hb
    simp [h,ht]
  · simp [h]

/-- The finite-horizon Wiener integral, built from the Ito integral, has
both its Gaussian law and the Brownian increment identities. -/
theorem finite_horizon_wiener_with_increments {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (B : BrownianSystem P (d+1)) (T : ℝ) :
    ∃ W : PiLp 2 (fun _ : Fin (d+1) =>
        Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T))) →ₗᵢ[ℝ] Lp ℝ 2 P,
      (∀ f, HasLaw (W f : Ω → ℝ) (gaussianReal 0 ⟨‖f‖^2,sq_nonneg _⟩) P) ∧
      (∀ (i : Fin (d+1)) (a b : ℝ), 0 ≤ a → a ≤ b → b ≤ T →
        (W (WithLp.toLp 2 (Pi.single i (finiteTimeIntervalVector T a b))) : Ω → ℝ) =ᵐ[P]
          fun w => B.W i (Asakura.FullAudit.realTimeClamp b) w -
            B.W i (Asakura.FullAudit.realTimeClamp a) w) := by
  classical
  obtain ⟨J,I,hI,hJ,hG⟩ := actual_wiener_coordinate_isometries_exists P B
  let E := L2ZeroExtension (E := ℝ) (volume.restrict (Ioi (0:ℝ))) (Iic T) measurableSet_Iic
  let V := finitePiIsometry (ι := Fin (d+1)) E
  refine ⟨I.comp V,?_,?_⟩
  · intro f
    change HasLaw (I (V f) : Ω → ℝ) _ P
    simpa only [V.norm_map] using hG (V f)
  · intro i a b ha hab hb
    have hv : V (WithLp.toLp 2 (Pi.single i (finiteTimeIntervalVector T a b))) =
        WithLp.toLp 2 (Pi.single i (timeIntervalVector a b)) := by
      apply PiLp.ext
      intro j
      change E ((Pi.single i (finiteTimeIntervalVector T a b) : Fin (d+1) → _) j) =
        (Pi.single i (timeIntervalVector a b) : Fin (d+1) → _) j
      by_cases hj : j = i
      · subst j
        simpa only [Pi.single_eq_same] using zero_extension_interval T a b hb
      · simp [Pi.single_eq_of_ne hj]
    change (I (V _) : Ω → ℝ) =ᵐ[P] _
    rw [hv,vector_wiener_single P J I hI]
    exact coordinate_wiener_indicator P B i (J i) (hJ i) a b ha hab

end Asakura.Chapter12
