import Chapter12ConditionalTensorProcess
import Chapter12ConditionalTimeClosed
import Chapter12FiberwiseSubspace
import Chapter12L2TensorDensity

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
open Asakura.Chapter2Complete
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- Constructing progressive conditional processes for scalar L2 variables
suffices for arbitrary joint L2 inputs. Separated functions are dense; their
conditional processes were constructed above, and the fiberwise identity is closed. -/
theorem progressive_projection_is_time_conditional {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ) (hT : 0<T) [Fact (0≤T)]
    (F : Icc (0:ℝ) T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet N → P N=0 → MeasurableSet[F t] N)
    (hex : ∀ U : Lp ℝ 2 P,∃ C : Ω × Icc (0:ℝ) T → ℝ,
      @Measurable _ _ (progressiveSpace F) inferInstance C ∧
      ∀ t,(fun w => C (w,t)) =ᵐ[P] P[(U : Ω → ℝ)|F t])
    (u : Lp ℝ 2 (P.prod (compactTimeMeasure T hT.le))) :
    let q : Lp ℝ 2 (P.prod (compactTimeMeasure T hT.le)) :=
      condExpL2 ℝ ℝ (progressive_space_le_product F hle) u
    ∀ᵐ t ∂compactTimeMeasure T hT.le,(fun w => q (w,t)) =ᵐ[P] P[(fun w => u (w,t))|F t] := by
  classical
  let ν := compactTimeMeasure T hT.le
  let R := lpMeas ℝ ℝ (progressiveSpace F) 2 (P.prod ν)
  let L := R.subtypeL.comp (condExpL2 ℝ ℝ (progressive_space_le_product F hle))
  let J := (randomSectionsIsometry P ν).toContinuousLinearMap
  let A : Icc (0:ℝ) T → Lp ℝ 2 P →L[ℝ] Lp ℝ 2 P := fun t =>
    (lpMeas ℝ ℝ (F t) 2 P).subtypeL.comp (condExpL2 ℝ ℝ (hle t))
  let V := fiberwiseIdentitySubmodule ν A J (J.comp L)
  have hv : u ∈ V := by
    apply joint_L2_tensor_induction P ν V (fiberwiseIdentitySubmodule_isClosed ν A J (J.comp L))
    intro h S hS hPS
    let U : Lp ℝ 2 P := indicatorConstLp 2 hS hPS.ne (1:ℝ)
    let f : Ω × Icc (0:ℝ) T → ℝ := (S ×ˢ univ).indicator (fun z => h z.2)
    have hf : MemLp f 2 (P.prod ν) := ((Lp.memLp h).comp_snd P).indicator (hS.prod .univ)
    have hU := indicatorConstLp_coeFn (p := 2) (hs := hS) (hμs := hPS.ne) (c := (1:ℝ))
    have huf : (hf.toLp f : Ω × Icc (0:ℝ) T → ℝ) =ᵐ[P.prod ν] (fun z => h z.2*U z.1) := by
      have huj := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := ν)).ae hU
      filter_upwards [hf.coeFn_toLp,huj] with z hz hu
      rw [hz]
      change f z=h z.2*(indicatorConstLp 2 hS hPS.ne (1:ℝ)) z.1
      rw [hu]
      by_cases hs : z.1 ∈ S <;> simp [f,hs]
    obtain ⟨C,hC,hCe⟩ := hex U
    obtain ⟨q,hqp,hqc⟩ := conditional_tensor_process P T hT F hle U h (hf.toLp f) huf C hC hCe
    have hqe : q=L (hf.toLp f) := conditional_time_projection P T hT F hF hle hnull
      (hf.toLp f) q hqp hqc
    change ∀ᵐ t ∂ν,J (L (hf.toLp f)) t=A t (J (hf.toLp f) t)
    filter_upwards [randomSectionsIsometry_coe P ν (hf.toLp f),
      randomSectionsIsometry_coe P ν q,hqc] with t hut hqt hct
    rw [← hqe]
    exact (conditional_L2_coe_iff P (F t) (hle t) _ _ _ _ hut hqt).mpr hct
  change ∀ᵐ t ∂ν,(fun w => L u (w,t)) =ᵐ[P] P[(fun w => u (w,t))|F t]
  filter_upwards [randomSectionsIsometry_coe P ν u,randomSectionsIsometry_coe P ν (L u),hv]
    with t hut hqt hvt
  exact (conditional_L2_coe_iff P (F t) (hle t) _ _ _ _ hut hqt).mp hvt

end Asakura.Chapter12
