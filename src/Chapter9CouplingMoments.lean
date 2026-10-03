import FullAuditTransportFlow
import Chapter8CenteredMoment

open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
namespace Asakura.Chapter9
open Asakura.FullAudit
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- The same-space coupling bounds the squared transport distance by the
actual mean squared displacement. -/
theorem transport_distance_sq_le_displacement {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → E) (hX : Measurable X) (hY : Measurable Y)
    (hi : Integrable (fun w => ‖X w-Y w‖^2) P) :
    transportDistance (P.map X) (P.map Y)^2≤∫ w,‖X w-Y w‖^2 ∂P := by
  let J := fun w => (X w,Y w)
  have hJ : Measurable J := hX.prodMk hY
  have hl : (P.map J).map Prod.fst=P.map X := by
    rw [Measure.map_map measurable_fst hJ]
    rfl
  have hr : (P.map J).map Prod.snd=P.map Y := by
    rw [Measure.map_map measurable_snd hJ]
    rfl
  have hf : Integrable (fun z : E × E => ‖z.1-z.2‖^2) (P.map J) :=
    (integrable_map_measure (by fun_prop) hJ.aemeasurable).mpr hi
  have hp : IsProbabilityMeasure (P.map J) :=
    (Measure.isProbabilityMeasure_map_iff hJ.aemeasurable).mpr inferInstance
  let c : QuadraticCoupling (P.map X) (P.map Y) := ⟨P.map J,hp,hl,hr,hf⟩
  letI : Nonempty (QuadraticCoupling (P.map X) (P.map Y)) := ⟨c⟩
  rw [transportDistance,Real.sq_sqrt (transport_energy_nonnegative _ _)]
  have hb := transport_energy_le_coupling c
  change _≤∫ z,‖z.1-z.2‖^2 ∂P.map J at hb
  rw [integral_map hJ.aemeasurable (by fun_prop)] at hb
  exact hb

/-- Independent centered noise contributes only its second moment to the
mean squared displacement. This supplies both coupling estimates in Ch.9. -/
theorem independent_affine_second_moment {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MemLp (fun x : E => x) 2 μ) (hν : MemLp (fun x : E => x) 2 ν)
    (hzero : (∫ y,y ∂ν)=0) (a b : ℝ) :
    (∫ z : E × E,‖a • z.1+b • z.2‖^2 ∂μ.prod ν)=
      a^2*(∫ x,‖x‖^2 ∂μ)+b^2*(∫ y,‖y‖^2 ∂ν) := by
  have hiμ := hμ.integrable (by norm_num)
  have hiν := hν.integrable (by norm_num)
  have hsμ := (memLp_two_iff_integrable_sq_norm hμ.aestronglyMeasurable).mp hμ
  have hsν := (memLp_two_iff_integrable_sq_norm hν.aestronglyMeasurable).mp hν
  have hcross : Integrable (fun z : E × E => ⟪z.1,z.2⟫) (μ.prod ν) := by
    apply (hiμ.norm.mul_prod hiν.norm).mono' (by fun_prop)
    exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using abs_real_inner_le_norm z.1 z.2)
  have hc : (∫ z : E × E,⟪z.1,z.2⟫ ∂μ.prod ν)=0 := by
    rw [integral_prod _ hcross]
    have he x : (∫ y,⟪x,y⟫ ∂ν)=0 := by
      have hh := (innerSL ℝ x).integral_comp_comm hiν
      simpa [hzero] using hh
    simp only [he,integral_zero]
  have hx : Integrable (fun z : E × E => ‖z.1‖^2) (μ.prod ν) := hsμ.comp_fst ν
  have hy : Integrable (fun z : E × E => ‖z.2‖^2) (μ.prod ν) := hsν.comp_snd μ
  have he (z : E × E) : ‖a • z.1+b • z.2‖^2=
      a^2*‖z.1‖^2+2*a*b*⟪z.1,z.2⟫+b^2*‖z.2‖^2 := by
    rw [norm_add_sq_real]
    simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,real_inner_smul_left,real_inner_smul_right]
    ring
  simp_rw [he]
  have hax : Integrable (fun z : E × E => a^2*‖z.1‖^2) (μ.prod ν) := hx.const_mul _
  have hab : Integrable (fun z : E × E => 2*a*b*⟪z.1,z.2⟫) (μ.prod ν) := hcross.const_mul _
  have hby : Integrable (fun z : E × E => b^2*‖z.2‖^2) (μ.prod ν) := hy.const_mul _
  have hs : Integrable (fun z : E × E => a^2*‖z.1‖^2+2*a*b*⟪z.1,z.2⟫) (μ.prod ν) := hax.add hab
  rw [integral_add hs hby,
    integral_add hax hab,integral_const_mul,
    integral_const_mul,integral_const_mul,hc]
  rw [integral_fun_fst (fun x : E => ‖x‖^2),integral_fun_snd (fun x : E => ‖x‖^2)]
  simp
end Asakura.Chapter9
