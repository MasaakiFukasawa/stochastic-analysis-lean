import Chapter2RandomStieltjes

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- The random-measure construction needs measurable evaluations only on
the original interval, which is essential for adaptedness. -/
theorem random_stieltjes_measure_measurable_on
    {Ω : Type*} [MeasurableSpace Ω] (a b : ℝ) (hab : a ≤ b) (A : Ω → ℝ → ℝ)
    (hA : ∀ ω, MonotoneOn (A ω) (Icc a b))
    (hr : ∀ ω x, x ∈ Icc a b → ContinuousWithinAt (A ω) (Icc a b ∩ Ici x) x)
    (hm : ∀ r, r ∈ Icc a b → Measurable (fun ω => A ω r)) :
    Measurable (fun ω => (intervalStieltjes a b hab (A ω) (hA ω) (hr ω)).measure) := by
  letI (ω : Ω) : IsFiniteMeasure (intervalStieltjes a b hab (A ω) (hA ω) (hr ω)).measure :=
    intervalStieltjes_finite a b hab (A ω) (hA ω) (hr ω)
  apply Measurable.measure_of_isPiSystem (borel_eq_generateFrom_Iic ℝ) isPiSystem_Iic
  · rintro _ ⟨r,rfl⟩
    have he (ω) := (intervalStieltjes a b hab (A ω) (hA ω) (hr ω)).measure_Iic
      (interval_stieltjes_left_limit a b hab A hA hr ω) r
    simp only [he]
    exact ((hm _ (intervalClamp_mem a b hab r)).sub (hm a (left_mem_Icc.2 hab))).ennreal_ofReal
  · simp only [interval_stieltjes_total_mass a b hab A hA hr]
    exact ((hm b (right_mem_Icc.2 hab)).sub (hm a (left_mem_Icc.2 hab))).ennreal_ofReal

/-- Restricting a Stieltjes measure up to t agrees with constructing the
same measure on the shorter interval [a,t]. -/
theorem interval_stieltjes_restrict_Iic
    (a b t : ℝ) (hat : a ≤ t) (htb : t ≤ b) (A : ℝ → ℝ)
    (hA : MonotoneOn A (Icc a b))
    (hr : ∀ x, x ∈ Icc a b → ContinuousWithinAt A (Icc a b ∩ Ici x) x)
    (hAt : MonotoneOn A (Icc a t))
    (hrt : ∀ x, x ∈ Icc a t → ContinuousWithinAt A (Icc a t ∩ Ici x) x) :
    (intervalStieltjes a t hat A hAt hrt).measure =
      (intervalStieltjes a b (hat.trans htb) A hA hr).measure.restrict (Iic t) := by
  let α := (intervalStieltjes a b (hat.trans htb) A hA hr).measure
  let β := (intervalStieltjes a t hat A hAt hrt).measure
  letI : IsFiniteMeasure α := intervalStieltjes_finite a b (hat.trans htb) A hA hr
  letI : IsFiniteMeasure β := intervalStieltjes_finite a t hat A hAt hrt
  have hl := interval_stieltjes_left_limit a b (hat.trans htb) (fun _ : Unit => A)
    (fun _ => hA) (fun _ => hr) ()
  have hlt := interval_stieltjes_left_limit a t hat (fun _ : Unit => A)
    (fun _ => hAt) (fun _ => hrt) ()
  apply Measure.ext_of_Iic
  intro r
  rw [Measure.restrict_apply measurableSet_Iic,Iic_inter_Iic,
    StieltjesFunction.measure_Iic _ hlt,StieltjesFunction.measure_Iic _ hl]
  congr 1
  change A (intervalClamp a t hat r)-A a = A (intervalClamp a b (hat.trans htb) (min r t))-A a
  have he : intervalClamp a b (hat.trans htb) (min r t) = intervalClamp a t hat r := by
    change max a (min b (min r t)) = max a (min t r)
    rw [min_left_comm b r t,min_eq_right htb,min_comm r t]
  rw [he]

/-- The interval extension has no mass outside (a,b], including at a. -/
theorem interval_stieltjes_ae_mem_Ioc
    (a b : ℝ) (hab : a ≤ b) (A : ℝ → ℝ) (hA : MonotoneOn A (Icc a b))
    (hr : ∀ x, x ∈ Icc a b → ContinuousWithinAt A (Icc a b ∩ Ici x) x) :
    ∀ᵐ r ∂(intervalStieltjes a b hab A hA hr).measure, r ∈ Ioc a b := by
  let α := (intervalStieltjes a b hab A hA hr).measure
  letI : IsFiniteMeasure α := intervalStieltjes_finite a b hab A hA hr
  have hmass := interval_stieltjes_total_mass a b hab (fun _ : Unit => A)
    (fun _ => hA) (fun _ => hr) ()
  have hi : α (Ioc a b) = ENNReal.ofReal (A b-A a) := by
    rw [StieltjesFunction.measure_Ioc]
    change ENNReal.ofReal (A (intervalClamp a b hab b)-A (intervalClamp a b hab a)) = _
    rw [intervalClamp_eq a b hab (right_mem_Icc.2 hab),intervalClamp_eq a b hab (left_mem_Icc.2 hab)]
  rw [ae_iff]
  change α (Ioc a b)ᶜ = 0
  rw [measure_compl measurableSet_Ioc (measure_ne_top α _),hi]
  change (intervalStieltjes a b hab A hA hr).measure univ - _ = 0
  rw [hmass,tsub_self]

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.random_stieltjes_measure_measurable_on
#print axioms Asakura.Chapter2Complete.interval_stieltjes_restrict_Iic

#print axioms Asakura.Chapter2Complete.interval_stieltjes_ae_mem_Ioc
