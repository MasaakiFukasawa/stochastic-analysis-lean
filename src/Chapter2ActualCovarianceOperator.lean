import Chapter2M2ProcessRepresentatives
import Chapter2M2CovarianceL1Bound
import Chapter2LocalCovarianceAE
import Chapter2TimeExhaustion

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

/-- A concrete covariance operator on the manuscript's M2 space, evaluated
at a finite time. Its codomain is the actual L1 space. This permits the
printed covariance/Bochner-integral exchange to be checked at each time. -/
theorem actual_m2_covariance_operator
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (N : ClosedTime T → Ω → ℝ) (hN : ContinuousM2Witness P F N)
    (d : ClosedTime T) (hd : d < ⊤) :
    ∃ L : continuousM2Terminal P F →L[ℝ] Lp ℝ 1 P,
      (∀ v, ‖L v‖ ≤ ‖v‖ * ‖(hN.moment ⊤).toLp (N ⊤)‖) ∧
      ∀ v, ∃ C : ClosedTime T → Ω → ℝ,
        LocalCovarianceWitness P F (m2ProcessOfTerminal P F v) N C ∧
        ((L v : Lp ℝ 1 P) : Ω → ℝ) =ᵐ[P] C d := by
  classical
  obtain ⟨u,hu,hut,huc⟩ := exists_strict_time_exhaustion hT
  let X := m2ProcessOfTerminal P F
  have hX2 v := (m2_process_of_terminal_spec P F v).1
  have hXL v := continuous_m2_is_local P F hF hle u hu.monotone hut huc (X v) (hX2 v)
  have hNL := continuous_m2_is_local P F hF hle u hu.monotone hut huc N hN
  obtain ⟨B,hB⟩ := local_covariance_witness_exists P F hF hle hnull N N hNL hNL
  have hex v : ∃ C : ClosedTime T → Ω → ℝ,
      LocalCovarianceWitness P F (X v) N C ∧ Integrable (C d) P ∧
      (∫ ω, ‖C d ω‖ ∂P) ≤ ‖v‖ * ‖(hN.moment ⊤).toLp (N ⊤)‖ := by
    obtain ⟨C,hC⟩ := local_covariance_witness_exists P F hF hle hnull (X v) N (hXL v) hNL
    obtain ⟨A,hA⟩ := local_covariance_witness_exists P F hF hle hnull (X v) (X v) (hXL v) (hXL v)
    obtain ⟨hi,hb⟩ := m2_covariance_fixed_time_L1_bound P F hF hle hnull
      (X v) N A B C (hXL v) hNL (hX2 v) hN hA hB hC d hd
    have he' : ‖m2TerminalOfProcess P F (m2ProcessOfTerminal P F v) (m2_process_of_terminal_spec P F v).1‖ = ‖v‖ :=
      congrArg norm (m2_process_terminal_value P F v)
    have he : ‖((hX2 v).moment ⊤).toLp (X v ⊤)‖ = ‖v‖ := he' 
    exact ⟨C,hC,hi,by rw [he] at hb; exact hb⟩
  choose C hC hi hb using hex
  let J := fun v => (hi v).toL1 (C v d)
  have hbound v : ‖J v‖ ≤ ‖v‖ * ‖(hN.moment ⊤).toLp (N ⊤)‖ := by
    have he : ‖J v‖ = ∫ ω, ‖C v d ω‖ ∂P := by
      rw [L1.norm_eq_integral_norm]
      exact integral_congr_ae ((hi v).coeFn_toL1.fun_comp norm)
    rw [he]
    exact hb v
  have hlin (a : ℝ) (v w : continuousM2Terminal P F) : J (a • v+w) = a • J v+J w := by
    have hcomb := (hC v).bilinear P F hF hle (hC w) a
    have he := m2_process_representation_linear P F hF hle v w a
    have he' : ∀ᵐ ω ∂P, ∀ t, t < ⊤ → a*X v t ω+X w t ω = X (a • v+w) t ω :=
      he.mono (fun ω hω t _ => (hω t).symm)
    have hc := hcomb.congr_ae_processes P F hF hle
      (((hXL v).smul P F a).add P F hF hle (hXL w)) hNL (hXL (a • v+w)) hNL he'
      (ae_of_all _ (fun _ _ _ => rfl))
    have heC := (hC (a • v+w)).unique P F hF hle hc
    have heCd : C (a • v+w) d =ᵐ[P] (fun ω => a*C v d ω+C w d ω) :=
      heC.mono (fun ω hω => hω d hd)
    have hii := ((hi v).const_mul a).add (hi w)
    have hL1 := (Integrable.toL1_eq_toL1_iff _ _ (hi (a • v+w)) hii).mpr heCd
    exact hL1
  have hzero : J 0 = 0 := by
    apply norm_eq_zero.mp
    have h := hbound 0
    simp only [norm_zero,zero_mul] at h
    exact le_antisymm h (norm_nonneg _)
  let JL : continuousM2Terminal P F →ₗ[ℝ] Lp ℝ 1 P :=
    { toFun := J
      map_add' := fun v w => by simpa only [one_smul] using hlin 1 v w
      map_smul' := fun a v => by
        change J (a • v) = a • J v
        simpa only [add_zero,hzero] using hlin a v 0 }
  let L := JL.mkContinuous ‖(hN.moment ⊤).toLp (N ⊤)‖
    (fun v => (hbound v).trans_eq (mul_comm _ _))
  exact ⟨L,hbound,fun v => ⟨C v,hC v,(hi v).coeFn_toL1⟩⟩

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.actual_m2_covariance_operator
