import Chapter3StieltjesRiemann
import Chapter2StieltjesRestriction

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter2Complete
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Instantiate the Riemann error with the Stieltjes measure constructed in
chapter 2. Interval masses, total mass and support are proved from that
construction; none are assumed as a description of an unspecified measure. -/
theorem constructed_stieltjes_riemann_error
    (b : ℝ) (hb : 0 ≤ b) (Q H : ℝ → ℝ)
    (hQ : MonotoneOn Q (Icc 0 b))
    (hr : ∀ x, x ∈ Icc 0 b → ContinuousWithinAt Q (Icc 0 b ∩ Ici x) x)
    (hH : Measurable H) (u : ℕ → ℝ) (hu : Monotone u) (hu0 : u 0 = 0)
    (N : ℕ) (hN : b ≤ u N) (δ : ℝ) (hδ : 0 ≤ δ)
    (hosc : ∀ j ∈ Finset.range N, ∀ x ∈ Ioc (u j) (u (j+1)), |H (u j)-H x| ≤ δ) :
    let μ := (intervalStieltjes 0 b hb Q hQ hr).measure
    let Qc := fun x => Q (intervalClamp 0 b hb x)
    Integrable H μ ∧ ∀ t,
      |(∑ j ∈ Finset.range N, H (u j)*(Qc (min (u (j+1)) t)-Qc (min (u j) t)))-
        (∫ x in Iic t, H x ∂μ)| ≤ δ*(Q b-Q 0) := by
  intro μ Qc
  letI : IsFiniteMeasure μ := intervalStieltjes_finite 0 b hb Q hQ hr
  have hm (a c) (hac : a ≤ c) : μ.real (Ioc a c) = Qc c-Qc a :=
    intervalStieltjes_Ioc_real 0 b hb Q hQ hr a c hac
  have hs : ∀ᵐ x ∂μ, x ∈ Ioc (u 0) (u N) := by
    filter_upwards [interval_stieltjes_ae_mem_Ioc 0 b hb Q hQ hr] with x hx
    exact ⟨by simpa only [hu0] using hx.1,hx.2.trans hN⟩
  have ht : μ.real univ = Q b-Q 0 := by
    rw [Measure.real,interval_stieltjes_total_mass 0 b hb (fun _ : Unit => Q)
      (fun _ => hQ) (fun _ => hr) ()]
    exact ENNReal.toReal_ofReal (sub_nonneg.mpr (hQ (left_mem_Icc.mpr hb) (right_mem_Icc.mpr hb) hb))
  simpa only [ht] using stieltjes_riemann_error μ Qc H hm u hu N hs hH.aestronglyMeasurable δ hδ hosc

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.constructed_stieltjes_riemann_error
