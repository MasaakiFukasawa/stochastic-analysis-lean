import Chapter9ReverseCovariance
import Chapter9FrozenBrownianCharacteristic
import Chapter9BrownianIncrementLaw

open MeasureTheory Set ProbabilityTheory
open scoped ContDiff NNReal
namespace Asakura.Chapter9
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter5
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

noncomputable def reverseBrownian {Ω : Type*} {d : ℕ}
    (μ : Measure (Fin d → ℝ)) (X : ℝ → Ω → Fin d → ℝ) (T r : ℝ) (w : Ω) (i : Fin d) : ℝ :=
  (X (T-r) w i-X T w i-∫ u in 0..r,ouReverseDrift μ (T-u,X (T-u) w) i)/Real.sqrt 2

/-- The process defined by subtracting the displayed reverse drift has
 the standard vector Brownian conditional characteristic function. -/
theorem reverse_brownian_characteristic {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (X : ℝ → Ω → Fin d → ℝ) (hXm : ∀ r,Measurable (X r))
    (hXc : ∀ w,Continuous (fun r => X r w)) (T : ℝ)
    (hCE : ∀ a b,0≤a → a<b → b<T → ∀ g,IsBoundedBorel g →
      P[(fun w => g (X (T-b) w))|reversedNaturalInformation P X T a]=ᵐ[P]
        (fun w => ouReverseParamTransition μ T a (fun z => g z.2) (b,X (T-a) w)))
    (R s : ℝ) (hs : 0≤s) (hsR : s≤R) (hRT : R<T) (v : Fin d → ℝ) :
    P[(fun w => Complex.exp (((∑ i,v i*(reverseBrownian μ X T R w i-reverseBrownian μ X T s w i)):ℝ)*Complex.I))|
      reversedNaturalInformation P X T s]=ᵐ[P]
        fun _ => Complex.exp (-(((R-s)*(∑ i,(v i)^2):ℝ):ℂ)/2) := by
  have hR : 0≤R := hs.trans hsR
  let p := fun t : HalfClosedTime => (finitePrefixTime R hR t).val
  let F := fun t => reversedNaturalInformation P X T (p t)
  let M := fun (i : Fin d) (t : HalfClosedTime) w => X (T-p t) w i-X T w i-
    ∫ u in 0..p t,ouReverseDrift μ (T-u,X (T-u) w) i
  have hl q (hq : ContDiff ℝ ∞ q) := ou_reverse_local_smooth_test P μ X hXm hXc T hCE q hq R hR hRT
  have hM i : LocalMProcessWitness P F (M i) := by
    simpa only [reverseCompensated,reverse_generator_coordinate,sub_zero] using! hl (fun x => x i) (by fun_prop)
  have hC := reverse_coordinate_covariance P μ X hXm hXc T R hR hRT hl
  have hF : Monotone F := (reversed_information_monotone P X T).comp
    (fun s t hst => finite_prefix_time_mono R hR hst)
  have hle t : F t≤m := reversed_information_le P X hXm T (p t)
  have hnull t E (hE : MeasurableSet[m] E) (hPE : P E=0) : MeasurableSet[F t] E :=
    reversed_information_null P X T (p t) E hE hPE
  have hh := frozen_brownian_characteristic P F hF hle hnull M hM R hR hC R s hs hsR le_rfl v
  have hpR : p (realTimeClamp R)=R := by
    dsimp only [p]
    rw [finite_prefix_time_min R R hR hR le_top,min_self]
  have hps : p (realTimeClamp s)=s := by
    dsimp only [p]
    rw [finite_prefix_time_min R s hR hs le_top,min_eq_left hsR]
  have he w : (∑ i,v i*((M i (realTimeClamp R) w-M i (realTimeClamp s) w)/Real.sqrt 2))=
      ∑ i,v i*(reverseBrownian μ X T R w i-reverseBrownian μ X T s w i) := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [M,reverseBrownian]
    rw [hpR,hps,sub_div]
  simpa only [he,F,hps] using hh
end Asakura.Chapter9
