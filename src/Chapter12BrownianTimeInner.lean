import Chapter12TimeRealizationIsometry

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- The Hilbert-valued derivative pairing is exactly the sum of the
coordinate time-space L2 pairings used in the Ito isometry. -/
theorem brownian_time_inner {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {d : ℕ} (T : ℝ) (hT : 0≤T)
    (U V : Lp (FiniteWienerHilbert d T) 2 P) :
    inner ℝ U V = ∑ i,inner ℝ (brownianDerivativeTime P T hT U i)
      (brownianDerivativeTime P T hT V i) := by
  simp only [brownianDerivativeTime,timeRealization_inner]
  let A := fun i => (brownianCoordinateProjection T i).compLp U
  let C := fun i => (brownianCoordinateProjection T i).compLp V
  have hi (i : Fin (d+1)) : Integrable (fun w => inner ℝ (A i w) (C i w)) P :=
    L2.integrable_inner (A i) (C i)
  simp only [L2.inner_def]
  change (∫ w,inner ℝ (U w) (V w) ∂P)=∑ i,∫ w,inner ℝ (A i w) (C i w) ∂P
  rw [←integral_finsetSum _ (fun i _ => hi i)]
  apply integral_congr_ae
  have hU := fun i => (brownianCoordinateProjection T i).coeFn_compLp U
  have hV := fun i => (brownianCoordinateProjection T i).coeFn_compLp V
  filter_upwards [ae_all_iff.mpr hU,ae_all_iff.mpr hV] with w hwU hwV
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [hwU i,hwV i]
  rfl

end Asakura.Chapter12
