import Chapter6VariationScaling
import Chapter2ItoIntegrandEncoding
import Chapter3ScalarIto
import Chapter3ContinuousIntegralConstruction
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

lemma local_initial_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (Z : ClosedTime T → Ω → ℝ) (hZ : LocalMProcessWitness P F Z) : Z ⊥ =ᵐ[P] 0 := by
  obtain ⟨τ,_,_,_,_,hb⟩ := hZ.localizers
  simpa only [min_bot_right] using (hb 0).1.initial

/-- The exponential local martingale is derived from the scalar Ito formula.
Both integrals are constructed; the finite-variation terms cancel by the
proved scaling and associativity of signed Stieltjes integration. -/
theorem stochastic_exponential_constructed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (Z C : ClosedTime T → Ω → ℝ) (hZ : LocalMProcessWitness P F Z)
    (hC : LocalCovarianceWitness P F Z Z C) :
    LocalMProcessWitness P F (fun t w => Real.exp (Z t w-C t w/2)-1) ∧
    ItoCovarianceFormula P F Z
      (fun z => Real.exp (Z (realTimeClamp z.2) z.1-C (realTimeClamp z.2) z.1/2))
      (fun t w => Real.exp (Z t w-C t w/2)-1) := by
  have hCv := covariance_adapted_variation P F hF hle hZ hZ hC
  have hCc w t (ht : t < ⊤) : ContinuousAt (fun s => C s w) t := by
    have hh := ((hZ.path P F w t ht).mul (hZ.path P F w t ht)).sub
      (hC.defect.path P F w t ht)
    convert hh using 1
    funext s
    dsimp only [Pi.sub_apply,Pi.mul_apply]
    ring
  let A := fun t w => (-1/2:ℝ)*C t w
  let X := fun t w => A t w+Z t w
  have hX : SemimartingaleDecomposition P F X A Z :=
    ⟨hCv.smul (-1/2),hZ,fun w t ht => ((hCc w t ht).const_mul _).add (hZ.path P F w t ht),fun _ _ _ => rfl⟩
  have hXa t (ht : t < ⊤) : Measurable[F t] (X t) :=
    ((hCv.adapted t ht).const_mul _).add (hZ.adapted P F t ht)
  let H := fun t w => Real.exp (X t w)
  have hHa t ht : Measurable[F t] (H t) := Real.continuous_exp.measurable.comp (hXa t ht)
  have hHc w t ht : ContinuousAt (fun s => H s w) t :=
    Real.continuous_exp.continuousAt.comp (hX.continuous w t ht)
  obtain ⟨c,hc,hcm,hcT,_,_,hcc⟩ := positive_real_time_exhaustion hT
  have hreg := open_process_real_regularity F H hHa hHc
  obtain ⟨J,hJv,hJc,hJ⟩ := continuous_adapted_variation_exists P F hF hnull c
    (fun n => (hc n).le) hcm.monotone hcT hcc C hCv hCc
    (fun z => H (realTimeClamp z.2) z.1) hreg.1 hreg.2
  obtain ⟨I,hIv,hIc,hI,hIJ⟩ := variation_scaled_integrator_constructed P hT F hF hle hnull
    C hCv hCc _ hreg.1 hreg.2 c (fun n => (hc n).le) hcm.monotone hcT hcc J hJ (-1/2)
  obtain ⟨L,hL,hLI⟩ := continuous_adapted_ito_exists P hT F hF hle hnull Z hZ
    (fun z => H (realTimeClamp z.2) z.1) hreg.1 hreg.2
  have hIL : SemimartingaleDecomposition P F (fun t w => I t w+L t w) I L :=
    ⟨hIv,hL,fun w t ht => (hIc w t ht).add (hL.path P F w t ht),fun _ _ _ => rfl⟩
  have hIto := scalar_ito_formula P hT F hF hle hnull X A Z C (fun t w => I t w+L t w) J
    hX hC Real.exp Real.contDiff_exp c (fun n => (hc n).le) hcT hcc
    (by simpa only [Real.deriv_exp] using
      (show SemimartingaleIntegralFormula P F c (fun n => (hc n).le) A Z
        (fun z => H (realTimeClamp z.2) z.1) (fun t w => I t w+L t w) from ⟨I,L,hIL,hI,hLI⟩))
    (by simpa only [iteratedDeriv_eq_iterate,Real.iter_deriv_exp] using hJ)
  have hz := local_initial_zero P F Z hZ
  have hd := local_initial_zero P F _ hC.defect
  have he : ∀ᵐ w ∂P,∀ t,t < ⊤ → L t w = Real.exp (Z t w-C t w/2)-1 := by
    filter_upwards [hIto,hIJ,hz,hd] with w hi hij hz hd
    have hc0 : C ⊥ w = 0 := by
      change Z ⊥ w*Z ⊥ w-C ⊥ w = 0 at hd
      change Z ⊥ w = 0 at hz
      rw [hz] at hd
      linarith
    intro t ht
    have hi := hi t ht
    have hx0 : X ⊥ w = 0 := by simp [X,A,hz,hc0]
    have hxt : X t w = Z t w-C t w/2 := by dsimp [X,A]; ring
    rw [hx0,Real.exp_zero,hxt,hij t ht] at hi
    linarith
  have hfinal : LocalMProcessWitness P F (fun t w => Real.exp (Z t w-C t w/2)-1) := by
    apply Asakura.Chapter3Complete.LocalMProcessWitness.congr_ae_open P F hF hL _ _ he
    · intro t ht
      exact (Real.continuous_exp.measurable.comp ((hZ.adapted P F t ht).sub
        ((hCv.adapted t ht).div_const 2))).sub measurable_const
    · intro w t ht
      exact (Real.continuous_exp.continuousAt.comp ((hZ.path P F w t ht).sub
        ((hCc w t ht).div_const 2))).sub continuousAt_const
  refine ⟨hfinal,?_⟩
  have hsource := hLI.congr_on_time_domain P F Z L _
    (fun z => Real.exp (Z (realTimeClamp z.2) z.1-C (realTimeClamp z.2) z.1/2))
    (fun w r _ _ => by congr 1; dsimp [H,X,A]; ring)
  intro N D hN hD
  obtain ⟨V,hV,hform⟩ := hsource N D hN hD
  exact ⟨V,hV.congr_ae_processes P F hF hle hL hN hfinal hN he
    (.of_forall (fun _ _ _ => rfl)),hform⟩

theorem stochastic_exponential_local
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (Z C : ClosedTime T → Ω → ℝ) (hZ : LocalMProcessWitness P F Z)
    (hC : LocalCovarianceWitness P F Z Z C) :
    LocalMProcessWitness P F (fun t w => Real.exp (Z t w-C t w/2)-1) :=
  (stochastic_exponential_constructed P hT F hF hle hnull Z C hZ hC).1

end Asakura.Chapter6
