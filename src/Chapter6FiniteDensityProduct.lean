import Chapter6FiniteProductIntegrability

open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators
namespace Asakura.Chapter6
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- Finitely many mean-one conditional density increments form an integrable
martingale. No integrability of their product is assumed. -/
theorem finite_conditional_density_product {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℕ → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ n,F n ≤ m)
    (d : ℕ → Ω → ℝ≥0)
    (hd : ∀ n,Measurable[F (n+1)] (d n))
    (hi : ∀ n,Integrable (fun w => (d n w : ℝ)) P)
    (he : ∀ n,P[(fun w => (d n w : ℝ))|F n] =ᵐ[P] (fun _ => (1:ℝ))) :
    let X := fun n w => ∏ i ∈ Finset.range n,(d i w : ℝ)
    (∀ n,Integrable (X n) P) ∧
    (∀ s t,s ≤ t → P[X t|F s] =ᵐ[P] X s) ∧
    (∀ n,(∫ w,X n w ∂P) = 1) := by
  classical
  let X := fun n w => ∏ i ∈ Finset.range n,(d i w : ℝ)
  have ha n : Measurable[F n] (X n) := by
    apply Finset.measurable_prod
    intro i hi
    exact ((hd i).mono (hF (Nat.succ_le_of_lt (Finset.mem_range.mp hi))) le_rfl).coe_nnreal_real
  have hrec n : X (n+1) = fun w => X n w*(d n w : ℝ) := by
    funext w
    exact Finset.prod_range_succ _ n
  have hxi : ∀ n,Integrable (X n) P := by
    intro n
    induction n with
    | zero => simpa [X] using integrable_const (1:ℝ) (μ := P)
    | succ n ih =>
      rw [hrec]
      exact (conditional_unit_factor_product P (hle n) (d n)
        ((hd n).mono (hle (n+1)) le_rfl) (hi n) (he n) (X n) (ha n).stronglyMeasurable ih).1
  have hstep n : P[X (n+1)|F n] =ᵐ[P] X n := by
    rw [hrec]
    exact (conditional_unit_factor_product P (hle n) (d n)
      ((hd n).mono (hle (n+1)) le_rfl) (hi n) (he n) (X n) (ha n).stronglyMeasurable (hxi n)).2
  have hm s t (hst : s ≤ t) : P[X t|F s] =ᵐ[P] X s := by
    induction t,hst using Nat.le_induction with
    | base => exact Filter.EventuallyEq.of_eq (condExp_of_stronglyMeasurable (hle s) (ha s).stronglyMeasurable (hxi s))
    | succ t hst ih =>
      exact (condExp_condExp_of_le (hF hst) (hle t)).symm.trans
        ((condExp_congr_ae (m := F s) (hstep t)).trans ih)
  refine ⟨hxi,hm,?_⟩
  intro n
  have hh := integral_congr_ae (hm 0 n (Nat.zero_le _))
  rw [integral_condExp (hle 0)] at hh
  simpa [X] using hh

end Asakura.Chapter6
