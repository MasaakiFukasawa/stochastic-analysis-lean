import Chapter12GaussianLinearScoreLaw
import Chapter12GaussianExponentialLp
import Chapter12AllFiniteMoments

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- Finite collections of lognormal stocks have all finite moments; hence
so does every measurable payoff with polynomial growth. -/
theorem lognormal_polynomial_payoff_variance_moments {d : ℕ} (v : ℝ≥0)
    (x b : Fin d → ℝ) (A : Matrix (Fin d) (Fin d) ℝ)
    (h : (Fin d → ℝ) → ℝ) (hm : Measurable h)
    (C : ℝ) (n : ℕ) (hb : ∀ s,|h s|≤C*(1+‖s‖^n)) :
    AllFiniteMoments (Measure.pi (fun _ : Fin d => gaussianReal 0 v))
      (fun z => h (fun i => x i*Real.exp (b i+∑ j,A i j*z j))) := by
  classical
  let μ := Measure.pi (fun _ : Fin d => gaussianReal 0 v)
  let X : (Fin d → ℝ) → Fin d → ℝ := fun z i => x i*Real.exp (b i+∑ j,A i j*z j)
  have hXm : Measurable X := by fun_prop
  have he (a : Fin d → ℝ) : AllFiniteMoments μ (fun z => Real.exp (∑ j,a j*z j)) := by
    have hp (S : Finset (Fin d)) : AllFiniteMoments μ (fun z => ∏ j∈S,Real.exp (a j*z j)) := by
      classical
      induction S using Finset.induction_on with
      | empty => simpa using (AllFiniteMoments.const (P := μ) 1)
      | @insert j S hj ih =>
        have hjm : AllFiniteMoments μ (fun z => Real.exp (a j*z j)) := by
          intro p hpt
          exact ((gaussian_exponential_memLp (gaussianReal 0 v) id 0 v
            ⟨measurable_id.aemeasurable,Measure.map_id⟩ (a j) p hpt)).comp_measurePreserving
            (measurePreserving_eval (fun _ : Fin d => gaussianReal 0 v) j)
        simpa only [Finset.prod_insert hj] using hjm.mul ih
    simpa only [Real.exp_sum] using hp Finset.univ
  have hi (i : Fin d) : AllFiniteMoments μ (fun z => X z i) := by
    have hh := (he (A i)).const_mul (x i*Real.exp (b i))
    simpa only [X,Real.exp_add,mul_assoc] using hh
  have hnorm : AllFiniteMoments μ (fun z => ‖X z‖) := by
    intro p hp
    have hh := memLp_finsetSum Finset.univ (fun i _ => (hi i p hp).norm)
    apply hh.mono' hXm.aestronglyMeasurable.norm
    filter_upwards [] with z
    rw [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
    apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun i _ => norm_nonneg (X z i)))).mpr
    intro i
    exact Finset.single_le_sum (fun j _ => norm_nonneg (X z j)) (Finset.mem_univ i)
  have hpow : ∀ k : ℕ,AllFiniteMoments μ (fun z => ‖X z‖^k) := by
    intro k
    induction k with
    | zero => simpa using (AllFiniteMoments.const (P := μ) 1)
    | succ k hk => simpa only [pow_succ] using hk.mul hnorm
  have hdom := ((AllFiniteMoments.const (P := μ) 1).add (hpow n)).const_mul C
  intro p hp
  apply (hdom p hp).mono' (hm.comp hXm).aestronglyMeasurable
  exact ae_of_all _ (fun z => hb (X z))

end Asakura.Chapter12
