import Chapter9FrozenBracketCharacteristic
import Chapter4ConditionalCharacteristicLaw

open MeasureTheory Set ProbabilityTheory
namespace Asakura.Chapter9
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter4
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Division by sqrt(2) turns the identified bracket into the standard
 Brownian conditional characteristic function. -/
theorem frozen_brownian_characteristic {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (M : Fin d → HalfClosedTime → Ω → ℝ) (hM : ∀ i,LocalMProcessWitness P F (M i))
    (b : ℝ) (hb : 0≤b)
    (hC : ∀ i j,LocalCovarianceWitness P F (M i) (M j)
      (fun t _ => 2*(if i=j then 1 else 0)*(finitePrefixTime b hb t).val))
    (R s : ℝ) (hs : 0≤s) (hsR : s≤R) (hRb : R≤b) (v : Fin d → ℝ) :
    P[(fun w => Complex.exp (((∑ i,v i*((M i (realTimeClamp R) w-M i (realTimeClamp s) w)/Real.sqrt 2)):ℝ)*Complex.I))|
      F (realTimeClamp s)]=ᵐ[P] fun _ =>
        Complex.exp (-(((R-s)*(∑ i,(v i)^2):ℝ):ℂ)/2) := by
  have hh := frozen_bracket_vector_characteristic P F hF hle hnull M hM b hb 2 (by norm_num)
    hC R s hs hsR hRb (fun i => v i/Real.sqrt 2)
  have hsqrt : (Real.sqrt (2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have he : 2*(R-s)*(∑ i,(v i/Real.sqrt 2)^2)=(R-s)*(∑ i,(v i)^2) := by
    simp_rw [div_pow,hsqrt,← Finset.sum_div]
    ring
  have hfun w : (∑ i,(v i/Real.sqrt 2)*(M i (realTimeClamp R) w-M i (realTimeClamp s) w))=
      ∑ i,v i*((M i (realTimeClamp R) w-M i (realTimeClamp s) w)/Real.sqrt 2) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  simpa only [hfun,he] using hh
end Asakura.Chapter9
