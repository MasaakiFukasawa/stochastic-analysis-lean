import FullAuditConditionalExercises
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

open MeasureTheory Set Filter
open scoped ENNReal
namespace Asakura.FullAudit
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

/-- Apply the preceding profit identity on [t,T], remove the zero terminal
 error, then use C5 to condition the future martingale increment on (V,P_t).
 In particular the information sigma algebra is constructed, not assumed
 equal to the insider's whole information. -/
theorem kyle_remaining_profit_exercise {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (F : MeasurableSpace Ω) (hF : F ≤ m)
    (V Pt PT Mt MT profit : Ω → ℝ) (ell σ t T : ℝ)
    (hV : Measurable[F] V) (hPt : Measurable[F] Pt)
    (hV2 : MemLp V 2 P) (hPt2 : MemLp Pt 2 P)
    (hMt : Integrable Mt P) (hMT : Integrable MT P)
    (hM : P[MT | F] =ᵐ[P] Mt) (hPT : PT =ᵐ[P] V)
    (hprofit : profit =ᵐ[P] (fun ω => ((V ω-Pt ω)^2-(V ω-PT ω)^2)/(2*ell)+
      ell*σ^2*(T-t)/2-σ*(MT ω-Mt ω))) :
    let G := MeasurableSpace.comap (fun ω => (V ω,Pt ω)) inferInstance
    P[profit | G] =ᵐ[P] (fun ω => (V ω-Pt ω)^2/(2*ell)+ell*σ^2*(T-t)/2) := by
  let G := MeasurableSpace.comap (fun ω => (V ω,Pt ω)) inferInstance
  letI : MeasurableSpace Ω := m
  have hGF : G ≤ F := (hV.prodMk hPt).comap_le
  have hG : G ≤ m := hGF.trans hF
  have hCE : P[MT | G] =ᵐ[P] P[Mt | G] :=
    (condExp_condExp_of_le hGF hF).symm.trans (condExp_congr_ae hM)
  have hinc : P[MT-Mt | G] =ᵐ[P] 0 := by
    have h := condExp_sub hMT hMt G
    filter_upwards [h,hCE] with ω hω he
    simp only [Pi.sub_apply,he,sub_self,Pi.zero_apply] at hω ⊢
    exact hω
  let A := fun ω => (V ω-Pt ω)^2/(2*ell)+ell*σ^2*(T-t)/2
  have hpair : Measurable[G] (fun ω => (V ω,Pt ω)) := Measurable.of_comap_le le_rfl
  have hAm : StronglyMeasurable[G] A :=
    (((hpair.fst.sub hpair.snd).pow_const 2).div_const _ |>.add_const _).stronglyMeasurable
  have hiA : Integrable A P :=
    (((memLp_two_iff_integrable_sq (hV2.sub hPt2).aestronglyMeasurable).mp (hV2.sub hPt2)).div_const _).add (integrable_const _)
  have he : profit =ᵐ[P] A-σ • (MT-Mt) := by
    filter_upwards [hprofit,hPT] with ω hp ht
    rw [hp,ht]
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,A,sub_self,zero_pow (by norm_num : (2:ℕ) ≠ 0),sub_zero]
  have hsub := condExp_sub hiA ((hMT.sub hMt).smul σ) G
  have hsm := condExp_smul σ (MT-Mt) G (μ := P)
  have hself := condExp_of_stronglyMeasurable hG hAm hiA
  have hcong := condExp_congr_ae (m := G) he
  filter_upwards [hsub,hsm,hinc,hcong] with ω hs hm hz he
  change P[profit | G] ω = A ω
  rw [he,hs]
  simp only [Pi.sub_apply,hself]
  rw [hm]
  simp only [Pi.smul_apply,smul_eq_mul,hz,Pi.zero_apply,mul_zero,sub_zero]

end Asakura.FullAudit
