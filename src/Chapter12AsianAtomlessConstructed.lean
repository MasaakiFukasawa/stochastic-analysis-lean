import Chapter12BrownianPathInputs
import Chapter7NaturalBrownianSystem
import Chapter10DeterministicNoisePath
import Chapter11ConstantIntegral

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter7 Asakura.Chapter10 Asakura.Chapter11
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- The continuous Brownian path used in the bridge proof has its L2 moment
from Chapter 2's maximal estimate. Thus no Gaussian path law or maximum
moment is left as an extra assumption in the Asian no-atom argument. -/
theorem asian_average_atomless_from_brownian {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsPreBrownianReal W P) (hWm : ∀ t, Measurable (W t))
    (hWc : ∀ w, Continuous (fun t => W t w))
    (x σ r T : ℝ) (hx : 0 < x) (hσ : 0 < σ) (hT : 0 < T) (K : ℝ) :
    P {w | (∫ s in 0..T,x*Real.exp ((r-σ^2/2)*s+σ*W ⟨max s 0,le_max_right _ _⟩ w))/T = K} = 0 := by
  let B := naturalBrownianSystem P W hW hWm hWc
  have hI : ItoCovarianceFormula P B.F (B.W 0) (fun _ => 1) (B.W 0) := by
    simpa only [one_mul] using constant_ito_integral P (by simp : (0:EReal)<⊤)
      B.F B.mono B.le B.null (B.W 0) (B.martingale 0) 1
  obtain ⟨X,hXm,hXi,heX,_⟩ := deterministic_noise_path P B 0 (fun _ => 1)
    continuous_const (B.W 0) (B.martingale 0) hI T hT.le
  have he (w : Ω) (s : Icc (0:ℝ) T) : X w s = W ⟨s.val,s.property.1⟩ w := by
    rw [heX]
    change W (halfTimeReal (realTimeClamp s.val)) w = _
    congr 1
    exact Subtype.ext (changed_time_real s.val s.property.1)
  have hz := brownian_arithmetic_average_no_atom P W hW x σ r T hx hσ hT X hXm hXi he K
  have heq (w : Ω) :
      (∫ s in 0..T,x*Real.exp ((r-σ^2/2)*s+σ*X w (projIcc 0 T hT.le s))) =
      ∫ s in 0..T,x*Real.exp ((r-σ^2/2)*s+σ*W ⟨max s 0,le_max_right _ _⟩ w) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hT.le] at hs
    dsimp only
    rw [he]
    have hearg : (⟨(projIcc 0 T hT.le s).val,(projIcc 0 T hT.le s).property.1⟩ : ℝ≥0) =
        ⟨max s 0,le_max_right _ _⟩ := by
      apply Subtype.ext
      simp [projIcc,hs.1,hs.2,max_eq_left hs.1]
    rw [hearg]
  simpa only [heq] using hz

end Asakura.Chapter12
