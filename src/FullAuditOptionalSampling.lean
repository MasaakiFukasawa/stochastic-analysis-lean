import FullAuditCountableStopping
import Chapter1WrittenL1

open MeasureTheory Set Filter Function
open scoped ENNReal Topology
namespace Asakura.FullAudit
open Asakura.Chapter1Written

/-- Countable closed-process optional sampling, with the manuscript's stopped
sigma algebra and its countable disjoint-fiber proof. No optional sampling
or stopped conditional-expectation theorem from Mathlib is invoked. -/
theorem closed_optional_sampling_written {Ω ι : Type*} {m : MeasurableSpace Ω}
    [LinearOrder ι] [Countable ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ι → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ i, F i ≤ m)
    (τ : Ω → ι) (hτ : ∀ i, MeasurableSet[F i] {ω | τ ω ≤ i})
    {Y : Ω → ℝ} (hY : Integrable Y P) :
    (fun ω => P[Y | F (τ ω)] ω) =ᵐ[P] P[Y | writtenStoppedSpace m F τ hτ] := by
  let Z : Ω → ℝ := fun ω => P[Y | F (τ ω)] ω
  let E : ι → Set Ω := fun i => {ω | τ ω = i}
  have hEi (i : ι) : MeasurableSet[F i] (E i) := countable_stopping_fiber F hF τ hτ i
  have hEm (i : ι) : MeasurableSet[m] (E i) := hle i _ (hEi i)
  have hEunion : (⋃ i, E i) = univ := by ext ω; simp [E]
  have hEd : Pairwise (Disjoint on E) := by
    intro i j hij
    exact disjoint_left.mpr fun ω hi hj => hij (hi.symm.trans hj)
  have hZm : Measurable[writtenStoppedSpace m F τ hτ] Z :=
    stopped_value_measurable_countable m F hF hle τ hτ (fun i => P[Y | F i])
      (fun i => stronglyMeasurable_condExp.measurable)
  have hG : writtenStoppedSpace m F τ hτ ≤ m := fun A hA => hA.1
  have hcell (i : ι) : ∫⁻ ω in E i, ‖Z ω‖ₑ ∂P ≤ ∫⁻ ω in E i, ‖Y ω‖ₑ ∂P := by
    have he : Z =ᵐ[P.restrict (E i)] P[Y | F i] :=
      (ae_restrict_mem (hEm i)).mono fun ω hω => by change τ ω = i at hω; simp only [Z,hω]
    have hen := he.fun_comp (fun x : ℝ => ‖x‖ₑ)
    simp only [Function.comp_def] at hen
    rw [lintegral_congr_ae hen,
      ← ofReal_integral_norm_eq_lintegral_enorm (integrable_condExp.integrableOn),
      ← ofReal_integral_norm_eq_lintegral_enorm hY.integrableOn]
    apply ENNReal.ofReal_le_ofReal
    have hj := conditional_jensen_written (hle i) abs_convex_written hY hY.abs
    calc
      _ = ∫ ω in E i, |P[Y | F i] ω| ∂P := by simp only [Real.norm_eq_abs]
      _ ≤ ∫ ω in E i, P[(fun ω => |Y ω|) | F i] ω ∂P :=
        integral_mono_ae integrable_condExp.abs.integrableOn integrable_condExp.integrableOn
          (ae_restrict_of_ae hj)
      _ = ∫ ω in E i, |Y ω| ∂P := setIntegral_condExp (hle i) hY.abs (hEi i)
      _ = _ := by simp only [Real.norm_eq_abs]
  have hnorm : ∫⁻ ω, ‖Z ω‖ₑ ∂P ≤ ∫⁻ ω, ‖Y ω‖ₑ ∂P := by
    have hz := lintegral_iUnion (μ := P) hEm hEd (fun ω => ‖Z ω‖ₑ)
    have hy := lintegral_iUnion (μ := P) hEm hEd (fun ω => ‖Y ω‖ₑ)
    rw [hEunion, Measure.restrict_univ] at hz hy
    rw [hz,hy]
    exact ENNReal.tsum_le_tsum hcell
  have hZi : Integrable Z P :=
    ⟨(hZm.mono hG le_rfl).aestronglyMeasurable, hnorm.trans_lt hY.2⟩
  apply ae_eq_condExp_of_forall_setIntegral_eq hG hY
    (fun _ _ _ => hZi.integrableOn) _ hZm.stronglyMeasurable.aestronglyMeasurable
  intro A hA _
  have hAFi (i : ι) : MeasurableSet[F i] (A ∩ E i) := stopped_event_fiber m F hF τ hτ hA i
  have hAFm (i : ι) : MeasurableSet[m] (A ∩ E i) := hle i _ (hAFi i)
  have hAFd : Pairwise (Disjoint on (fun i => A ∩ E i)) :=
    fun i j hij => (hEd hij).mono inter_subset_right inter_subset_right
  have hAu : (⋃ i, A ∩ E i) = A := by rw [← inter_iUnion,hEunion,inter_univ]
  rw [← hAu, integral_iUnion hAFm hAFd hZi.integrableOn,
    integral_iUnion hAFm hAFd hY.integrableOn]
  apply tsum_congr
  intro i
  have he : Z =ᵐ[P.restrict (A ∩ E i)] P[Y | F i] :=
    (ae_restrict_mem (hAFm i)).mono fun ω hω => by have ht : τ ω = i := hω.2; simp only [Z,ht]
  rw [integral_congr_ae he, setIntegral_condExp (hle i) hY (hAFi i)]

/-- Transfer from the canonical conditional-expectation representatives to the
arbitrary adapted representatives in the printed statement. Countability is
used to choose one common exceptional null set. -/
theorem optional_sampling_arbitrary_versions {Ω ι : Type*} {m : MeasurableSpace Ω}
    [LinearOrder ι] [Countable ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ι → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ i, F i ≤ m)
    (τ : Ω → ι) (hτ : ∀ i, MeasurableSet[F i] {ω | τ ω ≤ i})
    {Y : Ω → ℝ} (hY : Integrable Y P) (X : ι → Ω → ℝ)
    (hX : ∀ i, X i =ᵐ[P] P[Y | F i]) :
    (fun ω => X (τ ω) ω) =ᵐ[P] P[Y | writtenStoppedSpace m F τ hτ] := by
  have he : (fun ω => X (τ ω) ω) =ᵐ[P] (fun ω => P[Y | F (τ ω)] ω) := by
    filter_upwards [ae_all_iff.mpr hX] with ω hω
    exact hω (τ ω)
  exact he.trans (closed_optional_sampling_written P F hF hle τ hτ hY)

end Asakura.FullAudit
