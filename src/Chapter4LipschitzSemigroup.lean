import Chapter4DeterministicSDEFamily
import FullAuditMarkovSemigroup

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

section
variable {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] {dim noise : ℕ}
    (B : BrownianSystem P noise) (L : ℝ) (hL : 0≤L)
    (μ : Fin dim → (Fin dim → ℝ) → ℝ) (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (hLip : ∀ x y,(∑ i,(μ i x-μ i y)^2)+(∑ i,∑ j,(σ i j x-σ i j y)^2)≤L*∑ i,(x i-y i)^2)
    (Z : (Fin dim → ℝ) → HalfClosedTime → Ω → Fin dim → ℝ)
    (hZ : ∀ x,VectorSDESolution P B.F B.W μ σ (fun _ => x) (Z x))

include B L hL μ σ hLip hZ

lemma lipschitz_transition_conditional
    (f : (Fin dim → ℝ) → ℝ) (hf : Measurable f) (K : ℝ) (hb : ∀ x,‖f x‖≤K) (s t : ℝ≥0) :
    ∀ x,P[(fun w => f (Z x (realTimeClamp ((s+t:ℝ≥0):ℝ)) w)) | B.F (realTimeClamp (s:ℝ))]=ᵐ[P]
      fun w => transitionOperator P (fun x r => Z x (realTimeClamp (r:ℝ))) t f (Z x (realTimeClamp (s:ℝ)) w) := by
  intro x
  have he := (markov_from_lipschitz_coefficients P B L hL μ σ hLip
    (fun _ => x) (memLp_const x) (Z x) (hZ x) Z hZ s t s.coe_nonneg t.coe_nonneg).2 f hf K hb
  have hmap y : (∫ z,f z ∂@Measure.map Ω _ m _ (Z y (realTimeClamp (t:ℝ))) P)=
      transitionOperator P (fun x r => Z x (realTimeClamp (r:ℝ))) t f y :=
    integral_map (((hZ y).adapted _ (real_time_below t t.coe_nonneg (EReal.coe_lt_top t))).mono (B.le _) le_rfl).aemeasurable hf.aestronglyMeasurable
  simpa only [NNReal.coe_add,hmap] using he

/-- Chapman-Kolmogorov for the actual Lipschitz SDE transition operators,
using the Markov theorem just proved, not an assumed conditional identity. -/
theorem lipschitz_transition_semigroup
    (f : (Fin dim → ℝ) → ℝ) (hf : Measurable f) (K : ℝ) (hb : ∀ x,‖f x‖≤K) (s t : ℝ≥0) :
    transitionOperator P (fun x r => Z x (realTimeClamp (r:ℝ))) (s+t) f=
      transitionOperator P (fun x r => Z x (realTimeClamp (r:ℝ))) s
        (transitionOperator P (fun x r => Z x (realTimeClamp (r:ℝ))) t f) :=
  markov_transition_semigroup P (fun x r => Z x (realTimeClamp (r:ℝ)))
    (fun r => B.F (realTimeClamp (r:ℝ))) (fun r => B.le _) f s t
    (lipschitz_transition_conditional P B L hL μ σ hLip Z hZ f hf K hb s t)

theorem lipschitz_transition_zero (f : (Fin dim → ℝ) → ℝ) :
    transitionOperator P (fun x r => Z x (realTimeClamp (r:ℝ))) 0 f=f := by
  apply markov_transition_zero
  intro x
  have hz : realTimeClamp (T:=⊤) 0=⊥ := by
    apply Subtype.ext
    exact real_time_clamp_eq 0 le_rfl le_top
  simpa only [NNReal.coe_zero,hz] using (hZ x).initial_value P (EReal.coe_lt_top 0) B.F B.W μ σ (fun _ => x) (Z x)

theorem lipschitz_transition_kernel_composition
    (s t : ℝ≥0) (A : Set (Fin dim → ℝ)) (hA : MeasurableSet A) (x : Fin dim → ℝ) :
    (@Measure.map Ω _ m _ (Z x (realTimeClamp ((s+t:ℝ≥0):ℝ))) P).real A=
      ∫ y,(@Measure.map Ω _ m _ (Z y (realTimeClamp (t:ℝ))) P).real A
        ∂@Measure.map Ω _ m _ (Z x (realTimeClamp (s:ℝ))) P := by
  letI : MeasurableSpace Ω := m
  have hmeas := (markov_from_lipschitz_coefficients P B L hL μ σ hLip
    (fun _ => 0) (memLp_const 0) (Z 0) (hZ 0) Z hZ 0 t le_rfl t.coe_nonneg).1
  have hK : Measurable (fun y => (P.map (Z y (realTimeClamp (t:ℝ)))).real A) :=
    ((Measure.measurable_coe hA).comp hmeas).ennreal_toReal
  apply markov_transition_kernel_composition P (fun x r => Z x (realTimeClamp (r:ℝ)))
    (fun y r => ((hZ y).adapted _ (real_time_below r r.coe_nonneg (EReal.coe_lt_top r))).mono (B.le _) le_rfl)
    (fun r => B.F (realTimeClamp (r:ℝ))) (fun r => B.le _) s t A hA hK
    (lipschitz_transition_conditional P B L hL μ σ hLip Z hZ (A.indicator (fun _ => 1))
      (measurable_const.indicator hA) 1 (fun y => by by_cases hy : y∈A <;> simp [hy]) s t) x

end
end Asakura.Chapter4
