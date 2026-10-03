import Chapter3LocalItoFormula
import Chapter3ContinuousIntegralConstruction
import Chapter4Examples

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Apply the proved scalar Ito theorem and construct both integrals.
Only the original semimartingale and its covariance are supplied as inputs;
neither an Ito identity nor the existence of the derivative integrals is
assumed. The explicit derivatives allow direct comparison with the examples. -/
theorem constructed_scalar_ito
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A M C : ClosedTime T → Ω → ℝ)
    (hX : SemimartingaleDecomposition P F X A M)
    (hC : LocalCovarianceWitness P F M M C)
    (f f₁ f₂ : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (h₁ : ∀ x, HasDerivAt f (f₁ x) x) (h₂ : ∀ x, HasDerivAt f₁ (f₂ x) x)
    (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) (hcm : Monotone c)
    (hcT : ∀ k, (c k:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ k, t < realTimeClamp (T := T) (c k)) :
    ∃ Z J : ClosedTime T → Ω → ℝ,
      SemimartingaleIntegralFormula P F c hc A M
        (fun z => f₁ (X (realTimeClamp z.2) z.1)) Z ∧
      VariationIntegralFormula P c hc C
        (fun z => f₂ (X (realTimeClamp z.2) z.1)) J ∧
      ∀ᵐ ω ∂P, ∀ t, t < ⊤ →
        f (X t ω) = f (X ⊥ ω)+Z t ω+J t ω/2 := by
  have hd : deriv f = f₁ := funext (fun x => (h₁ x).deriv)
  have hdd : iteratedDeriv 2 f = f₂ := by
    rw [show (2:ℕ)=1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one,hd]
    exact funext (fun x => (h₂ x).deriv)
  have hfc : Continuous f₁ := hd ▸ hf.continuous_deriv (by norm_num)
  have hfcc : Continuous f₂ := hdd ▸ hf.continuous_iteratedDeriv 2 le_rfl
  have hXm t (ht : t < ⊤) : Measurable[F t] (X t) := by
    have he : X t = fun ω => A t ω+M t ω := funext (hX.decomposition t ht)
    rw [he]
    exact (hX.variation.adapted t ht).add (hX.martingale.adapted P F t ht)
  let H := fun t ω => f₁ (X t ω)
  let K := fun t ω => f₂ (X t ω)
  have hHm t ht : Measurable[F t] (H t) := hfc.measurable.comp (hXm t ht)
  have hHc ω t ht : ContinuousAt (fun s => H s ω) t :=
    hfc.continuousAt.comp (hX.continuous ω t ht)
  have hKm t ht : Measurable[F t] (K t) := hfcc.measurable.comp (hXm t ht)
  have hKc ω t ht : ContinuousAt (fun s => K s ω) t :=
    hfcc.continuousAt.comp (hX.continuous ω t ht)
  obtain ⟨I,N,hIN,hI,hN⟩ := continuous_semimartingale_integral_exists
    P hT F hF hle hnull X A M H hX hHm hHc c hc hcm hcT hcc
  have hCv := covariance_adapted_variation P F hF hle hX.martingale hX.martingale hC
  have hCc ω t (ht : t < ⊤) : ContinuousAt (fun s => C s ω) t := by
    have hh := ((hX.martingale.path P F ω t ht).mul
      (hX.martingale.path P F ω t ht)).sub (hC.defect.path P F ω t ht)
    convert hh using 1
    funext s
    simp only [Pi.sub_apply,Pi.mul_apply,sub_sub_cancel]
  obtain ⟨J,_,_,hJ⟩ := continuous_adapted_variation_exists P F hF hnull c hc hcm hcT hcc
    C hCv hCc (fun z => K (realTimeClamp z.2) z.1)
    (open_process_real_regularity F K hKm hKc).1
    (open_process_real_regularity F K hKm hKc).2
  have hZ : SemimartingaleIntegralFormula P F c hc A M
      (fun z => f₁ (X (realTimeClamp z.2) z.1)) (fun t ω => I t ω+N t ω) :=
    ⟨I,N,hIN,hI,hN⟩
  refine ⟨(fun t ω => I t ω+N t ω),J,hZ,hJ,?_⟩
  apply scalar_ito_formula P hT F hF hle hnull X A M C _ J hX hC f hf c hc hcT hcc
  · simpa only [hd] using hZ
  · simpa only [hdd] using hJ

/-- Local-martingale specialization with the zero variation integral
identified by uniqueness; the resulting integral itself is constructed. -/
theorem constructed_local_ito
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X C : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X)
    (hC : LocalCovarianceWitness P F X X C)
    (f f₁ f₂ : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (h₁ : ∀ x, HasDerivAt f (f₁ x) x) (h₂ : ∀ x, HasDerivAt f₁ (f₂ x) x)
    (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) (hcm : Monotone c)
    (hcT : ∀ k, (c k:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ k, t < realTimeClamp (T := T) (c k)) :
    ∃ Z J : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F Z ∧
      ItoCovarianceFormula P F X
        (fun z => f₁ (X (realTimeClamp z.2) z.1)) Z ∧
      VariationIntegralFormula P c hc C
        (fun z => f₂ (X (realTimeClamp z.2) z.1)) J ∧
      ∀ᵐ ω ∂P, ∀ t, t < ⊤ →
        f (X t ω) = f (X ⊥ ω)+Z t ω+J t ω/2 := by
  obtain ⟨Z,J,hZ,hJ,he⟩ := constructed_scalar_ito P hT F hF hle hnull
    X (fun _ _ => 0) X C
    (local_martingale_semimartingale_decomposition P hT F hF X hX) hC
    f f₁ f₂ hf h₁ h₂ c hc hcm hcT hcc
  obtain ⟨I,N,hIN,hI,hN⟩ := hZ
  have hzero := hI.unique P c hc hcc _ I (fun _ _ => 0) _
    (zero_variation_integral P c hc _)
  refine ⟨N,J,hIN.martingale,hN,hJ,?_⟩
  filter_upwards [he,hzero] with ω heω hzω
  intro t ht
  have hh := heω t ht
  rw [hIN.decomposition t ht ω,hzω t ht,zero_add] at hh
  exact hh

end Asakura.Chapter4
