import Chapter5BSDEDifference

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

/-- Actual process data of a BSDE's semimartingale decomposition.
All stochastic integrals are covariance-characterized, not formal symbols. -/
structure BSDECalculusData
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (F : ClosedTime T → MeasurableSpace Ω)
    (W : ClosedTime T → Ω → ℝ) (c : ℕ → ℝ) where
  Y : ClosedTime T → Ω → ℝ
  V : ClosedTime T → Ω → ℝ
  M : ClosedTime T → Ω → ℝ
  Z : Ω × ℝ → ℝ
  B : Ω × ℝ → ℝ
  decomposition : SemimartingaleDecomposition P F Y V M
  measurableZ : Measurable Z
  measurableB : Measurable B
  progressiveZ : ∀ n,@Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
    (fun z : Ω × Icc (0:ℝ) (c n) => Z (z.1,z.2.val))
  squareZ : ∀ n,∀ᵐ w ∂P,IntervalIntegrable (fun r => Z (w,r)^2) volume 0 (c n)
  integrableB : ∀ n,∀ᵐ w ∂P,IntervalIntegrable (fun r => B (w,r)) volume 0 (c n)
  drift : ∀ n,∀ᵐ w ∂P,∀ r∈Icc 0 (c n),V (realTimeClamp r) w=V ⊥ w+(∫ s in 0..r,B (w,s))
  integral : ItoCovarianceFormula P F W Z M

private theorem interval_square_sub
    (f g : ℝ → ℝ) (hf : Measurable f) (hg : Measurable g) (b : ℝ) (hb : 0≤b)
    (hi : IntervalIntegrable (fun r => f r^2) volume 0 b)
    (hj : IntervalIntegrable (fun r => g r^2) volume 0 b) :
    IntervalIntegrable (fun r => (f r-g r)^2) volume 0 b := by
  have hfi : MemLp f 2 (volume.restrict (Ioc 0 b)) :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hb).mp hi)
  have hgi : MemLp g 2 (volume.restrict (Ioc 0 b)) :=
    (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).mpr
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hb).mp hj)
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hb).mpr
    ((memLp_two_iff_integrable_sq (hf.sub hg).aestronglyMeasurable).mp (hfi.sub hgi))

/-- Subtraction constructs every analytic ingredient needed by the
weighted Ito estimate, including pathwise square integrability. -/
noncomputable def BSDECalculusData.sub
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t,F t≤m)
    (W : ClosedTime T → Ω → ℝ) (c : ℕ → ℝ) (hc : ∀ n,0≤c n)
    (u v : BSDECalculusData P F W c) : BSDECalculusData P F W c where
  Y := fun t w => u.Y t w-v.Y t w
  V := fun t w => u.V t w-v.V t w
  M := fun t w => u.M t w-v.M t w
  Z := fun z => u.Z z-v.Z z
  B := fun z => u.B z-v.B z
  decomposition := bsde_difference_decomposition P F hF hle _ _ _ _ _ _ u.decomposition v.decomposition
  measurableZ := u.measurableZ.sub v.measurableZ
  measurableB := u.measurableB.sub v.measurableB
  progressiveZ := fun n => (u.progressiveZ n).sub (v.progressiveZ n)
  squareZ := by
    intro n
    filter_upwards [u.squareZ n,v.squareZ n] with w hw hv
    exact interval_square_sub _ _ (u.measurableZ.comp measurable_prodMk_left)
      (v.measurableZ.comp measurable_prodMk_left) _ (hc n) hw hv
  integrableB := fun n => (u.integrableB n).and (v.integrableB n) |>.mono (fun _ hh => hh.1.sub hh.2)
  drift := fun n => bsde_difference_drift P u.V v.V u.B v.B (c n) (hc n) (u.drift n) (v.drift n)
    (u.integrableB n) (v.integrableB n)
  integral := bsde_difference_integral P F hF hle W u.M v.M u.Z v.Z u.integral v.integral

end Asakura.Chapter5
