import Chapter10StateRealEquation

open MeasureTheory Set
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false

lemma LinearStateWitness.coordinate_memLp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
    (G : Fin d → Fin n → ℝ → ℝ) (ξ : Ω → Fin d → ℝ)
    (T : ℝ) (hT : 0≤T) (N : Fin d → Fin n → HalfClosedTime → Ω → ℝ)
    (X : Ω → C(Icc (0:ℝ) T,Fin d → ℝ))
    (h : LinearStateWitness P B A G ξ T hT N X) (s : Icc (0:ℝ) T) (i : Fin d) :
    MemLp (fun w => X w s i) 2 P := by
  apply h.moment.norm.of_le
    ((measurable_pi_apply i).comp ((continuous_eval_const _).measurable.comp h.measurable)).aestronglyMeasurable
  exact ae_of_all _ fun w => by simpa only [norm_norm,Function.comp_def] using!
    (norm_le_pi_norm (X w s) i).trans ((X w).norm_coe_le_norm s)

lemma LinearStateWitness.coordinate_adapted {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
    (G : Fin d → Fin n → ℝ → ℝ) (ξ : Ω → Fin d → ℝ)
    (T : ℝ) (hT : 0≤T) (N : Fin d → Fin n → HalfClosedTime → Ω → ℝ)
    (X : Ω → C(Icc (0:ℝ) T,Fin d → ℝ))
    (h : LinearStateWitness P B A G ξ T hT N X) (s : Icc (0:ℝ) T) (i : Fin d) :
    Measurable[B.F (realTimeClamp s.val)] (fun w => X w s i) := by
  let t := realTimeClamp (T := (⊤:EReal)) s.val
  have ht : t<⊤ := half_real_time_finite s.val
  have hh := h.decomposition i
  have ha := (hh.variation.adapted t ht).add (hh.martingale.adapted P B.F t ht)
  have he := funext (hh.decomposition t ht)
  have hp : finitePrefixTime T hT t=s := Subtype.ext (finite_prefix_time_of_real T s.val hT s.property le_top)
  have ha' : Measurable[B.F t] (fun w => X w (finitePrefixTime T hT t) i) := by
    rw [he]
    exact ha
  simpa only [hp] using ha' 

end Asakura.Chapter10
