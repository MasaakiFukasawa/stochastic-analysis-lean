import Chapter2GlobalEnergyIdentity
import Chapter2L2FubiniMinkowski

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem measurable_real_l2_energy
    {S : Type*} [MeasurableSpace S] (ν : Measure S) (f : S → ℝ) (hf : Measurable f) :
    eLpNorm f 2 ν = (∫⁻ r, ENNReal.ofReal (f r^2) ∂ν)^(1/(2:ℝ)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf.aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat,ENNReal.rpow_two]
  congr 2
  funext r
  rw [← ofReal_norm,Real.norm_eq_abs,← ENNReal.ofReal_pow (abs_nonneg _),sq_abs]

/-- The analytic part of stochastic Fubini is instantiated on the actual
global Stieltjes measure. Its L2 norms are identified with the manuscript's
expected terminal energies, rather than assigned as abstract norms. -/
theorem actual_stieltjes_parameter_family
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure E) [SigmaFinite μ]
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hcm : Monotone c)
    (A : Ω → ℝ → ℝ)
    (hA : ∀ n ω, MonotoneOn (A ω) (Icc 0 (c n)))
    (hAc : ∀ n ω, ContinuousOn (A ω) (Icc 0 (c n)))
    (hm : ∀ t, Measurable (fun ω => A ω t)) :
    ∃ ν : Measure (Ω × ℝ), SigmaFinite ν ∧
      ∀ (H : E × (Ω × ℝ) → ℝ), Measurable H →
        (∀ x, eLpNorm (fun z => H (x,z)) 2 ν =
          (∫⁻ ω, ⨆ n, ∫⁻ r, ENNReal.ofReal (H (x,(ω,r))^2)
            ∂(intervalStieltjes 0 (c n) (hc n) (A ω) (hA n ω)
              (fun r hr => (hAc n ω r hr).mono inter_subset_left)).measure ∂P)^(1/(2:ℝ))) ∧
        ((∫⁻ x, (∫⁻ ω, ⨆ n, ∫⁻ r, ENNReal.ofReal (H (x,(ω,r))^2)
            ∂(intervalStieltjes 0 (c n) (hc n) (A ω) (hA n ω)
              (fun r hr => (hAc n ω r hr).mono inter_subset_left)).measure ∂P)^(1/(2:ℝ)) ∂μ) < ∞ →
          Integrable (l2Section ν H) μ ∧
          (((∫ x, l2Section ν H x ∂μ : Lp ℝ 2 ν) : (Ω × ℝ) → ℝ)
            =ᵐ[ν] (fun z => ∫ x, H (x,z) ∂μ)) ∧
          MemLp (fun z => ∫ x, H (x,z) ∂μ) 2 ν ∧
          (eLpNorm (fun z => ∫ x, H (x,z) ∂μ) 2 ν).toReal ≤
            ∫ x, (eLpNorm (fun z => H (x,z)) 2 ν).toReal ∂μ) := by
  obtain ⟨ν,hν,henergy⟩ := global_stieltjes_energy_identity P c hc hcm A hA hAc hm
  letI : SigmaFinite ν := hν
  refine ⟨ν,hν,?_⟩
  intro H hH
  have hn x := measurable_real_l2_energy ν (fun z => H (x,z)) (hH.comp measurable_prodMk_left)
  have he x := henergy (fun z => ENNReal.ofReal (H (x,z)^2))
    ((hH.comp measurable_prodMk_left).pow_const 2).ennreal_ofReal
  simp only [he] at hn
  refine ⟨hn,?_⟩
  intro hN
  have hN' : (∫⁻ x, eLpNorm (fun z => H (x,z)) 2 ν ∂μ) < ∞ := by
    simpa only [hn] using hN
  exact mixed_l1_l2_fubini_minkowski μ ν H hH hN'

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.actual_stieltjes_parameter_family
