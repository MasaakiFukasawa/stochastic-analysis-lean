import Chapter3BoundedItoMean
import Chapter3LocalItoFormula
import Chapter3RegularizedWeightRegularity

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Take expectations in the actual Ito formula. The martingale term's
zero mean and the finite-variation term's integrability are proved from bounds. -/
theorem bounded_C2_ito_expectation
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hA : LocalCovarianceWitness P F X X A)
    (hAm : ∀ ω, MonotoneOn (fun t => A t ω) (Iio ⊤))
    (hAc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => A s ω) t)
    (hA0 : ∀ ω, A ⊥ ω = 0)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (hf0 : f 0 = 0)
    (b : ClosedTime T) (hb : b < ⊤) (K L₁ L₂ : ℝ) (hK : 0 ≤ K) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hAb : ∀ᵐ ω ∂P, A b ω ≤ K)
    (hDb : ∀ᵐ ω ∂P, ∀ s, s ≤ b → |deriv f (X s ω)| ≤ L₁)
    (hDDb : ∀ᵐ ω ∂P, ∀ s, s ≤ b → |iteratedDeriv 2 f (X s ω)| ≤ L₂)
    (hfi : Integrable (fun ω => f (X b ω)) P) :
    ∃ J : ClosedTime T → Ω → ℝ,
      Integrable (J b) P ∧ (∫ ω, f (X b ω) ∂P) = (∫ ω, J b ω ∂P)/2 ∧
      (∀ᵐ ω ∂P, ∀ C : ℝ, 0 ≤ C →
        (∀ s, s ≤ b → |iteratedDeriv 2 f (X s ω)| ≤ C) → |J b ω| ≤ C*A b ω) := by
  have hd : Continuous (deriv f) := hf.continuous_deriv (by norm_num)
  have hdd : Continuous (iteratedDeriv 2 f) := hf.continuous_iteratedDeriv 2 le_rfl
  let H := fun t ω => deriv f (X t ω)
  let G := fun t ω => iteratedDeriv 2 f (X t ω)
  have hHa t (ht : t < ⊤) : Measurable[F t] (H t) := hd.measurable.comp (hX.adapted P F t ht)
  have hGa t (ht : t < ⊤) : Measurable[F t] (G t) := hdd.measurable.comp (hX.adapted P F t ht)
  have hHc ω t (ht : t < ⊤) : ContinuousAt (fun s => H s ω) t := hd.continuousAt.comp (hX.path P F ω t ht)
  have hGc ω t (ht : t < ⊤) : ContinuousAt (fun s => G s ω) t := hdd.continuousAt.comp (hX.path P F ω t ht)
  have hHr := open_process_real_regularity F H hHa hHc
  have hGr := open_process_real_regularity F G hGa hGc
  obtain ⟨Z,hZ,hz⟩ := continuous_adapted_ito_exists P hT F hF hle hnull X hX
    (fun z => H (realTimeClamp z.2) z.1) hHr.1 hHr.2
  have hmean := bounded_continuous_ito_mean_zero P hT F hF hle hnull X A H Z hX hA hAm hAc hA0
    hHa hHc hZ hz b hb K L₁ hK hL₁ hAb hDb
  have hAv := continuous_increasing_adapted_variation hT F hF A (hA.adapted P F hX hX) hAm hAc
  obtain ⟨c,hc,hcm,hcT,_,_,hcc⟩ := positive_real_time_exhaustion hT
  obtain ⟨J,hJv,hJc,hJ⟩ := continuous_adapted_variation_exists P F hF hnull c (fun n => (hc n).le)
    hcm.monotone hcT hcc A hAv hAc (fun z => G (realTimeClamp z.2) z.1) hGr.1 hGr.2
  have hJbound := increasing_variation_integral_bound P hT F hF hle A G J hAv hAm hGa hGc
    c (fun n => (hc n).le) hcT hcc hJ
  have hJb : ∀ᵐ ω ∂P, ∀ C : ℝ, 0 ≤ C →
      (∀ s, s ≤ b → |iteratedDeriv 2 f (X s ω)| ≤ C) → |J b ω| ≤ C*A b ω := by
    filter_upwards [hJbound] with ω hω
    intro C hC hbC
    simpa only [hA0 ω,sub_zero] using hω b hb C hC hbC
  have hJi : Integrable (J b) P := by
    apply (integrable_const (L₂*K)).mono'
      ((hJv.adapted b hb).mono (hle b) le_rfl).aestronglyMeasurable
    filter_upwards [hJb,hDDb,hAb] with ω hjω hdω haω
    rw [Real.norm_eq_abs]
    exact (hjω L₂ hL₂ hdω).trans (mul_le_mul_of_nonneg_left haω hL₂)
  have hformula := local_scalar_ito_formula P hT F hF hle hnull X A Z J hX hA f hf
    c (fun n => (hc n).le) hcT hcc hZ hz hJ
  have he : (fun ω => f (X b ω)) =ᵐ[P] (fun ω => Z b ω+J b ω/2) := by
    filter_upwards [hformula,hX.initial P F] with ω hω h0
    simpa only [h0,Pi.zero_apply,hf0,zero_add] using hω b hb
  have hZi : Integrable (Z b) P := by
    simpa only [min_top_right] using (hmean.1.moment ⊤).integrable (by norm_num)
  refine ⟨J,hJi,?_,hJb⟩
  rw [integral_congr_ae he,integral_add hZi (hJi.div_const 2),integral_div,hmean.2,zero_add]

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.bounded_C2_ito_expectation
