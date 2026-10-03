import Chapter12AsianMomentsLp
import Chapter12AsianVegaEnvelopeTrim
import Chapter12StockEnvelopeTrim
import Chapter12BrownianPathMoments
import Chapter12AsianCompactIntegrals
import Chapter12ProbabilityTrim

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000

/-- The payoff times either printed Asian weight has all finite moments
on terminal information, in particular the asserted second moment. -/
theorem asian_payoff_weights_all_moments {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hc : ∀ w, Continuous (fun t => B t w)) (T : ℝ≥0) (hT : 0 < T)
    (mT : MeasurableSpace Ω) (hle : mT ≤ m)
    (X : Ω → C(Icc (0:ℝ) T,ℝ)) (hXm : Measurable[mT] X)
    (he : ∀ w (s : Icc (0:ℝ) T), X w s = B ⟨s.val,s.property.1⟩ w)
    (x σ r K : ℝ) (hx : 0 < x) :
    let I := fun j w => asianMoment T T.property x σ r j (X w)
    let J := fun j w => asianVegaMoment T T.property x σ r j (X w)
    AllFiniteMoments (P.trim hle) (fun w => max (I 0 w/T-K) 0*
      ((1/x)*(I 0 w*B T w/(σ*I 1 w)-1+I 0 w*I 2 w/(I 1 w)^2))) ∧
    AllFiniteMoments (P.trim hle) (fun w => max (I 0 w/T-K) 0*
      (J 0 w*B T w/(σ*I 1 w)-J 1 w/I 1 w-1/σ+J 0 w*I 2 w/(I 1 w)^2)) := by
  letI : MeasurableSpace Ω := m
  have hs (p : ℝ≥0∞) (hp : p ≠ ⊤) :=
    stock_path_envelope_on_trim P mT hle B hB hm hc T X hXm he x σ r p hp
  have hv (p : ℝ≥0∞) (hp : p ≠ ⊤) :=
    asian_vega_envelope_on_trim P B hB hm hc T mT hle X hXm he x σ r p hp
  have hi (p : ℝ≥0∞) (hp : p ≠ ⊤) :=
    asian_inverse_moments_on_trim P B hB hm hc T hT mT hle X hXm he x σ r hx p hp
  have hpath (p : ℝ≥0∞) (hp : p ≠ ⊤) : MemLp X p (P.trim hle) :=
    memLp_on_trim P mT hle X p hXm.stronglyMeasurable
      (brownian_path_memLp P B hB hm hc T X (hXm.mono hle le_rfl) he p hp)
  letI := probability_trim P mT hle
  letI : MeasurableSpace Ω := mT
  let I := fun j w => asianMoment T T.property x σ r j (X w)
  let J := fun j w => asianVegaMoment T T.property x σ r j (X w)
  have hI (j) : AllFiniteMoments (P.trim hle) (I j) := by
    intro p hp
    obtain ⟨G,hG,hb,_⟩ := hs p hp
    exact asian_moment_memLp (P.trim hle) p T T.property X hXm x σ r j G hG hb
  have hJ (j) : AllFiniteMoments (P.trim hle) (J j) := by
    intro p hp
    obtain ⟨G,hG,hb⟩ := hv p hp
    exact asian_vega_moment_memLp (P.trim hle) p T T.property X hXm x σ r j G hG hb
  have hIinv : AllFiniteMoments (P.trim hle) (fun w => (I 1 w)⁻¹) := by
    intro p hp
    have hIe (w : Ω) : I 1 w = asianFirstTimeMoment x σ r T T.property (X w) := by
      unfold I asianMoment
      rw [compact_asian_moment]
      unfold asianFirstTimeMoment
      simp only [pow_one,mul_assoc]
    simpa only [hIe] using hi p hp
  have hWT : AllFiniteMoments (P.trim hle) (B T) := by
    intro p hp
    have hXm' : Measurable (fun w => X w ⟨T,T.property,le_rfl⟩) :=
      (continuous_eval_const _).measurable.comp hXm
    have hh : MemLp (fun w => X w ⟨T,T.property,le_rfl⟩) p (P.trim hle) :=
      (hpath p hp).of_le hXm'.aestronglyMeasurable
        (ae_of_all (P.trim hle) fun w => (X w).norm_coe_le_norm _)
    have he' : (fun w => X w ⟨T,T.property,le_rfl⟩) = B T := funext fun w => he w _
    rwa [he'] at hh
  exact asian_weighted_payoffs_memLp (P.trim hle) (I 0) (I 1) (I 2) (J 0) (J 1) (B T)
    (hI 0) (hI 2) (hJ 0) (hJ 1) hWT hIinv x σ T K

end Asakura.Chapter12
