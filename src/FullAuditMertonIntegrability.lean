import FullAuditMertonCalculus

open MeasureTheory Set Filter
open scoped ENNReal
namespace Asakura.FullAudit
set_option maxHeartbeats 600000

/-- The moment estimate immediately preceding Merton's theorem controls the
 second moment of the power of wealth, also when 1-gamma is negative. -/
theorem merton_power_memLp {S : Type*} [MeasurableSpace S] (ν : Measure S)
    (V : S → ℝ) (γ : ℝ) (hV : Measurable V) (hpos : ∀ z, 0 < V z)
    (hmom : Integrable (fun z => (V z)^(2*(1-γ))) ν) :
    MemLp (fun z => (V z)^(1-γ)) 2 ν := by
  have hm : Measurable (fun z => (V z)^(1-γ)) := hV.pow_const _
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  convert hmom using 1
  funext z
  rw [show 2*(1-γ) = (1-γ)*(2:ℕ) by norm_num; ring,
    Real.rpow_mul_natCast (hpos z).le]

/-- The deterministic exponential factor is bounded on the time interval. -/
theorem merton_exponential_bound (A T t : ℝ) (ht : t ∈ Icc 0 T) :
    ‖Real.exp (A*(T-t))‖ ≤ Real.exp (|A| *T) := by
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    A*(T-t) ≤ |A| *(T-t) := mul_le_mul_of_nonneg_right (le_abs_self _) (sub_nonneg.mpr ht.2)
    _ ≤ |A| *T := mul_le_mul_of_nonneg_left (by linarith [ht.1]) (abs_nonneg _)

theorem merton_coefficients_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (V π : Ω × ℝ → ℝ)
    (A γ σ a T K : ℝ) (hV : Measurable V) (hπ : Measurable π)
    (hpos : ∀ z, 0 < V z) (hbound : ∀ z, ‖π z‖ ≤ K)
    (hmom : Integrable (fun z => (V z)^(2*(1-γ))) (P.prod (volume.restrict (Icc 0 T)))) :
    MemLp (fun z => Real.exp (A*(T-z.2))*σ*π z*(V z)^(1-γ)) 2
      (P.prod (volume.restrict (Icc 0 T))) ∧
    Integrable (fun z => Real.exp (A*(T-z.2))*(V z)^(1-γ)*(π z-a)^2)
      (P.prod (volume.restrict (Icc 0 T))) := by
  let ν := volume.restrict (Icc 0 T)
  have htime : ∀ᵐ z ∂P.prod ν, z.2 ∈ Icc 0 T := by
    apply (Measure.ae_prod_iff_ae_ae (measurable_snd (measurableSet_Icc))).mpr
    exact ae_of_all _ (fun _ => ae_restrict_mem measurableSet_Icc)
  have hE : MemLp (fun z : Ω × ℝ => Real.exp (A*(T-z.2))) ∞ (P.prod ν) := by
    apply MemLp.of_bound (by fun_prop) (Real.exp (|A| *T))
    filter_upwards [htime] with z hz
    exact merton_exponential_bound A T z.2 hz
  have hp : MemLp π ∞ (P.prod ν) := MemLp.of_bound hπ.aestronglyMeasurable K
    (ae_of_all _ hbound)
  have hv := merton_power_memLp (P.prod ν) V γ hV hpos hmom
  have hcoef : MemLp (fun z => Real.exp (A*(T-z.2))*σ*π z) ∞ (P.prod ν) :=
    (hE.mul_const σ).mul hp
  have hn : MemLp (fun z => Real.exp (A*(T-z.2))*σ*π z*(V z)^(1-γ)) 2 (P.prod ν) :=
    hcoef.mul hv
  have hdiff : MemLp (fun z => π z-a) ∞ (P.prod ν) := hp.sub (memLp_const a)
  have hsq : MemLp (fun z => (π z-a)^2) ∞ (P.prod ν) := by
    simpa only [pow_two] using hdiff.fun_mul hdiff
  have hc : MemLp (fun z => Real.exp (A*(T-z.2))*(π z-a)^2) ∞ (P.prod ν) := hE.mul hsq
  have hi : Integrable (fun z => Real.exp (A*(T-z.2))*(π z-a)^2*(V z)^(1-γ)) (P.prod ν) :=
    hc.integrable_mul (hv.mono_exponent (by norm_num : (1:ℝ≥0∞) ≤ 2))
  refine ⟨hn,?_⟩
  convert hi using 1
  funext z
  ring

end Asakura.FullAudit
