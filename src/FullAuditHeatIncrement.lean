import FullAuditCLTRows

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.FullAudit

noncomputable def heatIncrementR {Ω : Type*} (f : HeatTest) (W X : Ω → ℝ) (t v : ℝ) (ω : Ω) : ℝ :=
  heatAverage (f.F 0) (W ω+X ω) (t-v)-heatAverage (f.F 0) (W ω) t -
    (heatAverage (f.F 1) (W ω) t*X ω-(v/2)*heatAverage (f.F 2) (W ω) t+
      (1/2)*heatAverage (f.F 2) (W ω) t*X ω^2)

theorem HeatTest.average_measurable (f : HeatTest) (k : ℕ) (t : ℝ) :
    Measurable (fun x => heatAverage (f.F k) x t) :=
  ((heatAverage_continuous (f.continuous k) (f.C k) (f.bound k)).comp
    (show Continuous (fun x : ℝ => (x,t)) by fun_prop)).measurable

theorem HeatTest.average_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (f : HeatTest) (k : ℕ)
    (W : Ω → ℝ) (hW : Measurable W) (t : ℝ) :
    Integrable (fun ω => heatAverage (f.F k) (W ω) t) P :=
  Integrable.of_bound ((f.average_measurable k t).comp hW).aestronglyMeasurable (f.C k)
    (ae_of_all _ fun ω => heatAverage_bound (f.continuous k) (f.C k) (f.bound k) (W ω) t)

/-- The remainder defined by the actual process increment agrees with the
manuscript's Hessian integral, sample by sample. -/
theorem HeatTest.increment_remainder_eq {Ω : Type*} (f : HeatTest) (W X : Ω → ℝ)
    (t v : ℝ) (hv : 0 ≤ v) (hvt : v ≤ t) (ω : Ω) :
    heatIncrementR f W X t v ω = cltHessianRemainder
      (fun s => heatAverage (f.F 2) (W ω+s*X ω) (t-s*v))
      (fun s => (1/2)*heatAverage (f.F 3) (W ω+s*X ω) (t-s*v))
      (fun s => (1/4)*heatAverage (f.F 4) (W ω+s*X ω) (t-s*v)) (X ω) v := by
  have h := f.taylor_increment (W ω) t (X ω) v hv hvt
  dsimp [heatIncrementR]
  rw [h]
  ring

/-- All random terms used in the telescoping proof are integrable. -/
theorem HeatTest.increment_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (f : HeatTest) (W X : Ω → ℝ)
    (hW : Measurable W) (hmX : Measurable X) (hX : MemLp X 2 P) (t v : ℝ) :
    Integrable (heatIncrementR f W X t v) P := by
  have hi1 := f.average_integrable P 0 (W+X) (hW.add hmX) (t-v)
  have hi0 := f.average_integrable P 0 W hW t
  have hu : Integrable (fun ω => heatAverage (f.F 1) (W ω) t*X ω) P :=
    (hX.integrable (by norm_num)).bdd_mul ((f.average_measurable 1 t).comp hW).aestronglyMeasurable
      (ae_of_all _ fun ω => heatAverage_bound (f.continuous 1) (f.C 1) (f.bound 1) (W ω) t)
  have hv := f.average_integrable P 2 W hW t
  have hx2 := (memLp_two_iff_integrable_sq hX.aestronglyMeasurable).mp hX
  have hux2 : Integrable (fun ω => heatAverage (f.F 2) (W ω) t*X ω^2) P :=
    hx2.bdd_mul ((f.average_measurable 2 t).comp hW).aestronglyMeasurable
      (ae_of_all _ fun ω => heatAverage_bound (f.continuous 2) (f.C 2) (f.bound 2) (W ω) t)
  convert (hi1.sub hi0).sub ((hu.sub (hv.const_mul (v/2))).add (hux2.const_mul (1/2))) using 1
  ext ω
  simp only [heatIncrementR,Pi.add_apply,Pi.sub_apply]
  ring

/-- The actual heat increment has expected value equal to the expected remainder. -/
theorem HeatTest.increment_expectation {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (f : HeatTest) (W X : Ω → ℝ)
    (hW : Measurable W) (hmX : Measurable X) (hX : MemLp X 2 P)
    (hmean : ∫ ω, X ω ∂P = 0) (hind : IndepFun X W P) (t : ℝ) :
    (∫ ω, heatAverage (f.F 0) (W ω+X ω) (t-(∫ ω, X ω^2 ∂P))-
      heatAverage (f.F 0) (W ω) t ∂P) =
      ∫ ω, heatIncrementR f W X t (∫ ω, X ω^2 ∂P) ω ∂P := by
  let G := MeasurableSpace.comap W (borel ℝ)
  let H := MeasurableSpace.comap X (borel ℝ)
  have hG : G ≤ m := hW.comap_le
  have hH : H ≤ m := hmX.comap_le
  have hmWG : Measurable[G] W := measurable_iff_comap_le.mpr le_rfl
  have hmXH : StronglyMeasurable[H] X := (measurable_iff_comap_le.mpr le_rfl).stronglyMeasurable
  have hmU : StronglyMeasurable[G] (fun ω => heatAverage (f.F 1) (W ω) t) :=
    ((f.average_measurable 1 t).comp hmWG).stronglyMeasurable
  have hmV : StronglyMeasurable[G] (fun ω => heatAverage (f.F 2) (W ω) t) :=
    ((f.average_measurable 2 t).comp hmWG).stronglyMeasurable
  have hu : ∀ᵐ ω ∂P, ‖heatAverage (f.F 1) (W ω) t‖ ≤ f.C 1+f.C 2 := ae_of_all _ fun ω =>
    (heatAverage_bound (f.continuous 1) (f.C 1) (f.bound 1) (W ω) t).trans (le_add_of_nonneg_right (f.bound_nonneg 2))
  have hv : ∀ᵐ ω ∂P, ‖heatAverage (f.F 2) (W ω) t‖ ≤ f.C 1+f.C 2 := ae_of_all _ fun ω =>
    (heatAverage_bound (f.continuous 2) (f.C 2) (f.bound 2) (W ω) t).trans (le_add_of_nonneg_left (f.bound_nonneg 1))
  have hc := clt_heat_increment_cancellation P hG hH hmXH hX hmean hmU hmV _ hu hv hind
  letI : MeasurableSpace Ω := m
  have hiq : Integrable (fun ω => heatAverage (f.F 0) (W ω+X ω) (t-(∫ ω, X ω^2 ∂P))-
      heatAverage (f.F 0) (W ω) t) P :=
    (f.average_integrable P 0 (W+X) (hW.add hmX) _).sub (f.average_integrable P 0 W hW t)
  have hir := f.increment_integrable P W X hW hmX hX t (∫ ω, X ω^2 ∂P)
  have hil : Integrable (fun ω => heatAverage (f.F 1) (W ω) t*X ω -
      ((∫ ω, X ω^2 ∂P)/2)*heatAverage (f.F 2) (W ω) t+
      (1/2)*heatAverage (f.F 2) (W ω) t*X ω^2) P := by
    convert hiq.sub hir using 1
    ext ω
    simp only [Pi.sub_apply,heatIncrementR]
    ring
  change _ = ∫ ω, (heatAverage (f.F 0) (W ω+X ω) (t-(∫ ω, X ω^2 ∂P))-
    heatAverage (f.F 0) (W ω) t) - _ ∂P
  rw [integral_sub hiq hil,hc,sub_zero]

end Asakura.FullAudit
