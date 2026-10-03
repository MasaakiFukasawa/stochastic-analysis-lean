import Chapter10PathInformation
import Chapter10ActualProductIncrements
import Chapter4VectorLevyConstructed
import Chapter2TimeExhaustion
import Chapter3IncreasingAdaptedVariation

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter9
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- The proved innovation martingale and compensated-product identities give
actual local covariation witnesses on each finite interval. Gaussian moments
supply the harmless L2 localization of the product. -/
theorem finite_innovation_covariation {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {r : ℕ} (T : ℝ) (hT : 0<T)
    [Fact (0≤(T:EReal))]
    (X : Ω → C(Icc (0:ℝ) T,Fin r → ℝ))
    (F : Icc (0:ℝ) T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hm : ∀ t i,Measurable[F t] (fun w => X w t i))
    (hg : ∀ t i,HasGaussianLaw (fun w => X w t i) P)
    (hM : ∀ s t : Icc (0:ℝ) T,s≤t → ∀ i,P[(fun w => X w t i)|F s]=ᵐ[P] fun w => X w s i)
    (hQ : ∀ s t : Icc (0:ℝ) T,s≤t → ∀ i j,
      P[(fun w => X w t i*X w t j-(if i=j then t.val else 0))|F s]=ᵐ[P]
        fun w => X w s i*X w s j-(if i=j then s.val else 0))
    (h0 : ∀ i,(fun w => X w ⟨0,le_rfl,hT.le⟩ i)=ᵐ[P] 0) :
    let ρ := finitePrefixTime (T := (T:EReal)) T hT.le
    (∀ i,LocalMProcessWitness P (fun t => F (ρ t)) (fun t w => X w (ρ t) i)) ∧
      ∀ i j,LocalCovarianceWitness P (fun t => F (ρ t))
        (fun t w => X w (ρ t) i) (fun t w => X w (ρ t) j)
        (fun t _ => if i=j then (ρ t).val else 0) := by
  let ρ := finitePrefixTime (T := (T:EReal)) T hT.le
  have hρc : Continuous ρ := finite_prefix_time_continuous T hT.le
  have hρm : Monotone ρ := finite_prefix_time_mono T hT.le
  have hρ0 : ρ ⊥=⟨0,le_rfl,hT.le⟩ := Subtype.ext (finite_prefix_bot T hT.le)
  have hTe : (0:EReal)<T := by exact_mod_cast hT
  obtain ⟨u,hu,hut,huc⟩ := exists_strict_time_exhaustion hTe
  have hlocal i : LocalMProcessWitness P (fun t => F (ρ t)) (fun t w => X w (ρ t) i) := by
    apply continuous_m2_is_local P _ (hF.comp hρm) (fun t => hle _) u hu.monotone hut huc
    refine ⟨fun t => hm _ i,fun t => (hg _ i).memLp_two,?_,?_,?_⟩
    · intro w
      exact (continuous_apply i).comp ((X w).continuous.comp hρc)
    · intro s t hst
      exact hM _ _ (hρm hst) i
    · simpa only [hρ0] using h0 i
  refine ⟨hlocal,?_⟩
  intro i j
  have hprod : ContinuousM2Witness P (fun t => F (ρ t))
      (fun t w => X w (ρ t) i*X w (ρ t) j-(if i=j then (ρ t).val else 0)) := by
    refine ⟨fun t => ((hm _ i).mul (hm _ j)).sub measurable_const,?_,?_,?_,?_⟩
    · intro t
      have hi : MemLp (fun w => X w (ρ t) i) 4 P := (hg _ i).memLp (by norm_num)
      have hj : MemLp (fun w => X w (ρ t) j) 4 P := (hg _ j).memLp (by norm_num)
      letI : ENNReal.HolderTriple 4 4 2 := ⟨by
        apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)).mp
        norm_num [ENNReal.toReal_add]⟩
      exact (hi.mul hj : MemLp _ 2 P).sub (memLp_const _)
    · intro w
      have hi := (continuous_apply i).comp ((X w).continuous.comp hρc)
      have hj := (continuous_apply j).comp ((X w).continuous.comp hρc)
      by_cases hij : i=j
      · simpa only [hij,if_true] using! hi.mul hj |>.sub (continuous_subtype_val.comp hρc)
      · simpa only [hij,if_false] using! hi.mul hj |>.sub continuous_const
    · intro s t hst
      exact hQ _ _ (hρm hst) i j
    · filter_upwards [h0 i,h0 j] with w hi hj
      simp only [hρ0,hi,hj,Pi.zero_apply,zero_mul,ite_self,sub_zero]
  refine ⟨continuous_m2_is_local P _ (hF.comp hρm) (fun t => hle _) u hu.monotone hut huc _ hprod,?_⟩
  refine ⟨fun n _ => u n,?_,fun _ => hu.monotone,fun n _ => hut n,fun _ => huc,?_⟩
  · intro n t
    by_cases ht : u n≤t <;> simp [ht]
  · intro n w
    refine ⟨fun t => if i=j then (ρ (min (u n) t)).val else 0,fun _ => 0,?_,monotone_const,?_⟩
    · by_cases hij : i=j
      · simp only [hij,ite_true]
        exact fun s t hst => hρm (min_le_min_left _ hst)
      · simp only [hij,ite_false]
        exact monotone_const
    · intro t
      simp only [sub_zero]
      rfl

end Asakura.Chapter10
