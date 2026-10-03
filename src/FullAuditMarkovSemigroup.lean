import FullAuditConditionalExercises
import Mathlib.Probability.HasLaw

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal
namespace Asakura.FullAudit
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

noncomputable def transitionOperator {Ω E : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : E → ℝ≥0 → Ω → E) (t : ℝ≥0) (f : E → ℝ) (x : E) : ℝ :=
  ∫ ω, f (X x t ω) ∂P

/-- The printed proof of the semigroup corollary: take expectations in the
 preceding Markov conditional identity. The operators are actual expectations
 of the supplied process, not abstract symbols with composition assumed. -/
theorem markov_transition_semigroup {Ω E : Type*} {m : MeasurableSpace Ω}
    [MeasurableSpace E] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : E → ℝ≥0 → Ω → E) (F : ℝ≥0 → MeasurableSpace Ω) (hle : ∀ t, F t ≤ m)
    (f : E → ℝ) (s t : ℝ≥0)
    (hM : ∀ x, P[(fun ω => f (X x (s+t) ω)) | F s] =ᵐ[P]
      (fun ω => transitionOperator P X t f (X x s ω))) :
    transitionOperator P X (s+t) f = transitionOperator P X s (transitionOperator P X t f) := by
  funext x
  have he := integral_congr_ae (hM x)
  rw [integral_condExp (hle s)] at he
  exact he

theorem markov_transition_zero {Ω E : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : E → ℝ≥0 → Ω → E)
    (h0 : ∀ x, X x 0 =ᵐ[P] (fun _ => x)) (f : E → ℝ) : transitionOperator P X 0 f = f := by
  funext x
  calc
    _ = ∫ _ : Ω, f x ∂P := integral_congr_ae ((h0 x).mono fun ω h => congrArg f h)
    _ = f x := by simp

/-- The transition measures are the actual pushforward laws. Their real
 masses satisfy the Chapman-Kolmogorov integral identity. Measurability of
 the transition probability in its initial state is a preceding kernel fact. -/
theorem markov_transition_kernel_composition {Ω E : Type*} {m : MeasurableSpace Ω}
    [MeasurableSpace E] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : E → ℝ≥0 → Ω → E) (hmX : ∀ x t, Measurable (X x t))
    (F : ℝ≥0 → MeasurableSpace Ω) (hle : ∀ t, F t ≤ m)
    (s t : ℝ≥0) (A : Set E) (hA : MeasurableSet A)
    (hK : Measurable (fun x => (P.map (X x t)).real A))
    (hM : ∀ x, P[(fun ω => A.indicator (fun _ => (1:ℝ)) (X x (s+t) ω)) | F s] =ᵐ[P]
      (fun ω => transitionOperator P X t (A.indicator (fun _ => 1)) (X x s ω))) (x : E) :
    (P.map (X x (s+t))).real A = ∫ y, (P.map (X y t)).real A ∂P.map (X x s) := by
  let f : E → ℝ := A.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hA
  have he (u : ℝ≥0) (y : E) : transitionOperator P X u f y = (P.map (X y u)).real A := by
    change (∫ ω, f (X y u ω) ∂P) = _
    rw [← integral_map (hmX y u).aemeasurable hf.aestronglyMeasurable]
    rw [integral_indicator hA,integral_const,smul_eq_mul,mul_one]
    rw [Measure.real,Measure.restrict_apply_univ]
    rfl
  have hsem := congrFun (markov_transition_semigroup P X F hle f s t hM) x
  rw [he (s+t) x] at hsem
  change (P.map (X x (s+t))).real A = ∫ ω, transitionOperator P X t f (X x s ω) ∂P at hsem
  simp only [he] at hsem
  rw [integral_map (hmX x s).aemeasurable hK.aestronglyMeasurable]
  exact hsem

end Asakura.FullAudit
