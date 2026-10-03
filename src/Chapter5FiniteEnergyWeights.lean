import Chapter5FiniteEnergyNorm
import Chapter5PerturbationParameters

open MeasureTheory Set Filter Asymptotics
open scoped Topology ENNReal
namespace Asakura.Chapter5
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

lemma finiteEnergyNorm_weight_comparison
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R β γ : ℝ) (hR : 0≤R) (hβ : 0≤β) (hγ : 0≤γ)
    (H : Ω × ℝ → ℝ) (hHm : Measurable H) (hH : MemLp H 2 (P.prod (volume.restrict (Ioc 0 R)))) :
    finiteEnergyNorm P R β H≤Real.sqrt (Real.exp (|β-γ| *R))*finiteEnergyNorm P R γ H := by
  let ν := P.prod (volume.restrict (Ioc 0 R))
  have hs : ∀ᵐ z ∂ν,z.2∈Icc 0 R := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.preimage measurable_snd)).mpr
    exact ae_of_all _ fun _ => (ae_restrict_mem measurableSet_Ioc).mono (fun r hr => ⟨hr.1.le,hr.2⟩)
  have hiβ := (finite_time_weighted_energy P R hR β hβ H hHm hH).1
  have hiγ := (finite_time_weighted_energy P R hR γ hγ H hHm hH).1
  have hh := weighted_energy_comparison ν H β γ R hR hs hiβ hiγ
  dsimp only [ν] at hh
  rw [integral_prod _ hiβ,integral_prod _ hiγ] at hh
  simp only [← intervalIntegral.integral_of_le hR] at hh
  have hsq : (finiteEnergyNorm P R β H)^2≤
      (Real.sqrt (Real.exp (|β-γ| *R))*finiteEnergyNorm P R γ H)^2 := by
    rw [mul_pow,Real.sq_sqrt (Real.exp_pos _).le,finiteEnergyNorm_sq P R β hR,finiteEnergyNorm_sq P R γ hR]
    exact hh
  exact (sq_le_sq₀ (finiteEnergyNorm_nonneg _ _ _ _) (mul_nonneg (Real.sqrt_nonneg _) (finiteEnergyNorm_nonneg _ _ _ _))).mp hsq

lemma finite_energy_bigO_change_weight
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R β γ : ℝ) (hR : 0≤R) (hβ : 0≤β) (hγ : 0≤γ)
    (H : ℝ → Ω × ℝ → ℝ) (hHm : ∀ ε,Measurable (H ε))
    (hH : ∀ ε,MemLp (H ε) 2 (P.prod (volume.restrict (Ioc 0 R))))
    (k : ℕ) (he : (fun ε => finiteEnergyNorm P R γ (H ε)) =O[𝓝 0] (fun ε : ℝ => |ε|^k)) :
    (fun ε => finiteEnergyNorm P R β (H ε)) =O[𝓝 0] (fun ε : ℝ => |ε|^k) := by
  have hw : (fun ε => finiteEnergyNorm P R β (H ε)) =O[𝓝 0] (fun ε => finiteEnergyNorm P R γ (H ε)) := by
    apply IsBigO.of_bound (Real.sqrt (Real.exp (|β-γ| *R)))
    apply Eventually.of_forall
    intro ε
    simpa only [Real.norm_eq_abs,abs_of_nonneg (finiteEnergyNorm_nonneg _ _ _ _)] using
      finiteEnergyNorm_weight_comparison P R β γ hR hβ hγ (H ε) (hHm ε) (hH ε)
  exact hw.trans he

end Asakura.Chapter5
