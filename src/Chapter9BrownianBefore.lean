import Chapter9ReverseBrownianRegularity

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ContDiff
namespace Asakura.Chapter9
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Standard vector Brownian motion before a finite terminal time:
 continuous adapted paths, zero initial value, independent increments,
 and the Gaussian law of every linear projection. -/
structure BrownianBefore {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (F : ℝ → MeasurableSpace Ω) (W : ℝ → Ω → Fin d → ℝ) (T : ℝ) : Prop where
  initial : ∀ w,W 0 w=0
  adapted : ∀ s,0≤s → s<T → Measurable[F s] (W s)
  path : ∀ b,0≤b → b<T → ∀ w,ContinuousOn (fun s => W s w) (Icc 0 b)
  increments : ∀ s r,0≤s → (hsr : s≤r) → r<T →
    (∀ v : Fin d → ℝ,HasLaw (fun w => ∑ i,v i*(W r w i-W s w i))
      (gaussianReal 0 ⟨(r-s)*(∑ i,(v i)^2),
        mul_nonneg (sub_nonneg.mpr hsr) (Finset.sum_nonneg fun i _ => sq_nonneg (v i))⟩) P) ∧
    Indep (MeasurableSpace.comap (fun w i => W r w i-W s w i) inferInstance) (F s) P

 theorem reverse_brownian_is_brownian {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (X : ℝ → Ω → Fin d → ℝ) (hXm : ∀ r,Measurable (X r))
    (hXc : ∀ w,Continuous (fun r => X r w)) (T : ℝ)
    (hCE : ∀ a b,0≤a → a<b → b<T → ∀ g,IsBoundedBorel g →
      P[(fun w => g (X (T-b) w))|reversedNaturalInformation P X T a]=ᵐ[P]
        (fun w => ouReverseParamTransition μ T a (fun z => g z.2) (b,X (T-a) w))) :
    BrownianBefore P (reversedNaturalInformation P X T) (reverseBrownian μ X T) T := by
  refine ⟨reverse_brownian_zero μ X T,
    fun s hs hsT => reverse_brownian_adapted P μ X hXc T s hs hsT,
    fun b hb hbT w => reverse_brownian_continuous μ X hXc T b hb hbT w,?_⟩
  intro s r hs hsr hrT
  have hmr : Measurable (reverseBrownian μ X T r) :=
    (reverse_brownian_adapted P μ X hXc T r (hs.trans hsr) hrT).mono
      (reversed_information_le P X hXm T r) le_rfl
  have hms : Measurable (reverseBrownian μ X T s) :=
    (reverse_brownian_adapted P μ X hXc T s hs (hsr.trans_lt hrT)).mono
      (reversed_information_le P X hXm T s) le_rfl
  exact brownian_increment_law P (reversedNaturalInformation P X T s)
    (reversed_information_le P X hXm T s)
    (fun w i => reverseBrownian μ X T r w i-reverseBrownian μ X T s w i)
    (hmr.sub hms) (r-s) (sub_nonneg.mpr hsr)
    (fun v => reverse_brownian_characteristic P μ X hXm hXc T hCE r s hs hsr hrT v)
end Asakura.Chapter9
