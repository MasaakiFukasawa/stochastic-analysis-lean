import Chapter12ItoIndicatorIdentity
import Chapter12VectorWienerCoordinatesConstructed
import Chapter12LpZeroExtension

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

theorem half_line_interval_measure_ne_top (a b : ℝ) :
    (volume.restrict (Ioi (0:ℝ))) (Ioc a b) ≠ ⊤ := by
  apply ne_of_lt
  rw [Measure.restrict_apply measurableSet_Ioc]
  apply (measure_mono inter_subset_left).trans_lt
  rw [Real.volume_Ioc]
  exact ENNReal.ofReal_lt_top

noncomputable def timeIntervalVector (a b : ℝ) : Lp ℝ 2 (volume.restrict (Ioi (0:ℝ))) :=
  indicatorConstLp 2 measurableSet_Ioc (half_line_interval_measure_ne_top a b) (1:ℝ)

/-- Each constructed coordinate Wiener map sends an interval indicator to
the actual Brownian increment, including identification of the terminal limit. -/
theorem coordinate_wiener_indicator {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (i : Fin d) (J : Lp ℝ 2 (volume.restrict (Ioi (0:ℝ))) →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hJ : ∀ (f : ℝ → ℝ) (hm : Measurable f) (hi : MemLp f 2 (volume.restrict (Ioi (0:ℝ)))),
      ∃ N : HalfClosedTime → Ω → ℝ, ∃ hN : ContinuousM2Witness P B.F N,
        ItoCovarianceFormula P B.F (B.W i) (fun z => f z.2) N ∧
        J (hi.toLp f) = (hN.moment ⊤).toLp (N ⊤))
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    (J (timeIntervalVector a b) : Ω → ℝ) =ᵐ[P]
      fun w => B.W i (realTimeClamp b) w-B.W i (realTimeClamp a) w := by
  let hi := memLp_indicator_const (μ := volume.restrict (Ioi (0:ℝ))) 2 measurableSet_Ioc (1:ℝ)
    (Or.inr (half_line_interval_measure_ne_top a b))
  obtain ⟨N,hN,hNI,he⟩ := hJ ((Ioc a b).indicator (fun _ => (1:ℝ)))
    (measurable_const.indicator measurableSet_Ioc) hi
  change J (timeIntervalVector a b) = _ at he
  rw [he]
  exact (hN.moment ⊤).coeFn_toLp.trans (indicator_ito_terminal_identity P B i a b ha hab N hN hNI)

/-- In the vector integral, a single nonzero coordinate selects that
coordinate's Wiener integral. -/
theorem vector_wiener_single {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d : ℕ}
    (J : Fin d → Lp ℝ 2 (volume.restrict (Ioi (0:ℝ))) →ₗᵢ[ℝ] Lp ℝ 2 P)
    (W : PiLp 2 (fun _ : Fin d => Lp ℝ 2 (volume.restrict (Ioi (0:ℝ)))) →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hW : ∀ f, W f = ∑ i,J i (f i))
    (i : Fin d) (f : Lp ℝ 2 (volume.restrict (Ioi (0:ℝ)))) :
    W (WithLp.toLp 2 (Pi.single i f)) = J i f := by
  classical
  rw [hW]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · simp

end Asakura.Chapter12
