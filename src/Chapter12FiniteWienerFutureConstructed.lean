import Chapter12VectorWienerFutureProcess
import Chapter12FiniteWienerIndicator
import Chapter12WienerTerminalMeasurable

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- The finite Wiener map is constructed on the ambient Brownian space,
with its terminal-information measurability proved from stopped integrals. -/
theorem finite_horizon_wiener_with_future_process {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (B : BrownianSystem P (d+1)) (T : ℝ) (hT : 0 ≤ T) :
    ∃ W : PiLp 2 (fun _ : Fin (d+1) =>
        Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T))) →ₗᵢ[ℝ] Lp ℝ 2 P,
      (∀ f, HasLaw (W f : Ω → ℝ) (gaussianReal 0 ⟨‖f‖^2,sq_nonneg _⟩) P) ∧
      (∀ f, AEStronglyMeasurable[B.F (realTimeClamp T)] (W f : Ω → ℝ) P) ∧
      (∀ (i : Fin (d+1)) (a b : ℝ), 0 ≤ a → a ≤ b → b ≤ T →
        (W (WithLp.toLp 2 (Pi.single i (finiteTimeIntervalVector T a b))) : Ω → ℝ) =ᵐ[P]
          fun w => B.W i (realTimeClamp b) w-B.W i (realTimeClamp a) w) ∧
      (∀ u,∃ N : HalfClosedTime → Ω → ℝ,ContinuousM2Witness P B.F N ∧
        (W u : Ω → ℝ)=ᵐ[P] N ⊤ ∧
        ∀ a,0≤a → (W (finiteFuturePart T a u) : Ω → ℝ)=ᵐ[P]
          fun w => N ⊤ w-N (realTimeClamp a) w) := by
  classical
  obtain ⟨J,I,hI,hJ,hG⟩ := actual_wiener_coordinate_isometries_exists P B
  let E := L2ZeroExtension (E := ℝ) (volume.restrict (Ioi (0:ℝ))) (Iic T) measurableSet_Iic
  let V := finitePiIsometry (ι := Fin (d+1)) E
  refine ⟨I.comp V,?_,?_,?_,?_⟩
  · intro f
    change HasLaw (I (V f) : Ω → ℝ) _ P
    simpa only [V.norm_map] using hG (V f)
  · intro f
    change AEStronglyMeasurable[B.F (realTimeClamp T)] (I (V f) : Ω → ℝ) P
    rw [hI]
    have hs : AEStronglyMeasurable[B.F (realTimeClamp T)]
        (fun w => ∑ i,J i (E (f i)) w) P := by
      have hh (s : Finset (Fin (d+1))) : AEStronglyMeasurable[B.F (realTimeClamp T)]
          (fun w => ∑ i ∈ s,J i (E (f i)) w) P := by
        induction s using Finset.induction_on with
        | empty => simpa using (aestronglyMeasurable_const (b := (0:ℝ)) (μ := P))
        | @insert i s hi ih =>
          simpa only [Finset.sum_insert hi,Pi.add_def,E] using
            (coordinate_wiener_terminal_measurable P B i (J i) (hJ i) T hT (f i)).add ih
      exact hh Finset.univ
    apply hs.congr
    filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i => J i (E (f i)))] with w hw
    simpa only [Finset.sum_apply,V,finitePiIsometry,LinearIsometry.coe_mk,LinearMap.coe_mk,AddHom.coe_mk,WithLp.ofLp_toLp] using hw.symm
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

  · intro u
    exact vector_wiener_future_process P B J I hI hJ T u

end Asakura.Chapter12

#print axioms Asakura.Chapter12.finite_horizon_wiener_with_future_process
