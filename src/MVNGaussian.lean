import MVNProcess

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Asakura
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma mvn_process_gaussian (I : IndependentWienerIntegrals P) (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1) :
    IsGaussianProcess (fun t : ℝ≥0 => (mvnProcessLp I H hH0 hH1 t : Ω → ℝ)) P := by
  classical
  let Z : ℝ≥0 → Ω → ℝ := fun t ω => mvnNormalization H *
    ((I.first (mvnFutureLp H hH0 t)) ω + (I.second (mvnPastLp H hH0 hH1 t)) ω)
  have hZ : IsGaussianProcess Z P := by
    apply I.gaussian.of_isGaussianProcess
    intro t
    let u : Sum (Lp ℝ 2 (volume : Measure ℝ)) (Lp ℝ 2 (volume : Measure ℝ)) :=
      Sum.inl (mvnFutureLp H hH0 t)
    let v : Sum (Lp ℝ 2 (volume : Measure ℝ)) (Lp ℝ 2 (volume : Measure ℝ)) :=
      Sum.inr (mvnPastLp H hH0 hH1 t)
    refine ⟨{u,v},mvnNormalization H •
      (ContinuousLinearMap.proj ⟨u,by simp⟩ + ContinuousLinearMap.proj ⟨v,by simp⟩),?_⟩
    intro ω
    rfl
  apply hZ.congr
  intro t
  have hh := (Lp.coeFn_smul (mvnNormalization H)
    (I.first (mvnFutureLp H hH0 t)+I.second (mvnPastLp H hH0 hH1 t)))
  have ha := Lp.coeFn_add (I.first (mvnFutureLp H hH0 t)) (I.second (mvnPastLp H hH0 hH1 t))
  filter_upwards [hh,ha] with ω h₁ h₂
  symm
  change (mvnNormalization H • (I.first (mvnFutureLp H hH0 t)+
    I.second (mvnPastLp H hH0 hH1 t)) : Lp ℝ 2 P) ω = _
  rw [h₁]
  change mvnNormalization H * (I.first (mvnFutureLp H hH0 t)+
    I.second (mvnPastLp H hH0 hH1 t) : Lp ℝ 2 P) ω = _
  rw [h₂]
  rfl
end Asakura
