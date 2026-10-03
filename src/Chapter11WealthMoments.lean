import Chapter6ExponentialSecondMoment
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory Set Filter
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter6
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- All real moments of exponential wealth, including negative moments,
from the actual local martingale and a deterministic bracket bound. -/
theorem exponential_wealth_real_moment {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (Z C : ClosedTime T → Ω → ℝ) (hZ : LocalMProcessWitness P F Z)
    (hC : LocalCovarianceWitness P F Z Z C)
    (R : ClosedTime T) (hR : R<⊤)
    (A : Ω → ℝ) (hA : Measurable A) (L K x q : ℝ) (hx : 0<x)
    (hAb : ∀ᵐ w ∂P,|A w|≤L) (hCb : ∀ᵐ w ∂P,0≤C R w ∧ C R w≤K) :
    let V := fun w => x*Real.exp (A w+Z R w-C R w/2)
    Integrable (fun w => (V w)^q) P ∧
      (∫ w,(V w)^q ∂P)≤x^q*Real.exp (|q| *L+|q^2-q| *K/2) := by
  let V := fun w => x*Real.exp (A w+Z R w-C R w/2)
  have hCm : Measurable (C R) :=
    ((covariance_adapted_variation P F hF hle hZ hZ hC).adapted R hR).mono (hle R) le_rfl
  have hZm : Measurable (Z R) := (hZ.adapted P F R hR).mono (hle R) le_rfl
  have hτ t : MeasurableSet[F t] {w : Ω | R≤t} := by
    by_cases h : R≤t <;> simp [h]
  have hEi := exponential_integrable_of_upper_bound P (fun w => q^2*C R w)
    (hCm.const_mul _) (q^2*K) 1 (by norm_num)
    (hCb.mono (fun w hw => mul_le_mul_of_nonneg_left hw.2 (sq_nonneg q)))
  obtain ⟨hi,_,hmean,_⟩ := novikov_written P hT F hF hle hnull
    (fun t w => q*Z t w) (fun t w => q^2*C t w) (hZ.smul P F q)
    (scaled_self_covariance P F Z C hC q) (fun _ => R) hτ (fun _ => hR) 1 (by norm_num) hEi
  let E := fun w => Real.exp (q*Z R w-q^2*C R w/2)
  have hE : Integrable E P := by simpa only [min_top_right] using hi ⊤
  have hEm : (∫ w,E w ∂P)=1 := by simpa only [min_top_right] using hmean
  let D := x^q*Real.exp (|q| *L+|q^2-q| *K/2)
  have hVm : Measurable (fun w => (V w)^q) :=
    (((hA.add hZm).sub (hCm.div_const 2)).exp.const_mul x).pow_const q
  have hb : ∀ᵐ w ∂P,(V w)^q≤D*E w := by
    filter_upwards [hAb,hCb] with w ha hc
    dsimp only [V,D,E]
    rw [Real.mul_rpow hx.le (Real.exp_pos _).le,←Real.exp_mul,mul_assoc,←Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_pos_of_pos hx q).le
    apply Real.exp_le_exp.mpr
    have hqa : q*A w≤|q| *L := (le_abs_self _).trans (by
      rw [abs_mul];exact mul_le_mul_of_nonneg_left ha (abs_nonneg q))
    have hqc : (q^2-q)*C R w≤|q^2-q| *K :=
      (mul_le_mul_of_nonneg_right (le_abs_self _) hc.1).trans
        (mul_le_mul_of_nonneg_left hc.2 (abs_nonneg _))
    nlinarith
  have hVi : Integrable (fun w => (V w)^q) P :=
    (hE.const_mul D).mono' hVm.aestronglyMeasurable (hb.mono (fun w hw => by
      change ‖(V w)^q‖≤D*E w
      rw [Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos (show 0<V w from mul_pos hx (Real.exp_pos _)) q)]
      exact hw))
  refine ⟨hVi,?_⟩
  calc
    _ ≤ ∫ w,D*E w ∂P := integral_mono_ae hVi (hE.const_mul D) hb
    _ = D := by rw [integral_const_mul,hEm,mul_one]

end Asakura.Chapter11
