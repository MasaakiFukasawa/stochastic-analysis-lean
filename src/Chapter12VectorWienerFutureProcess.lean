import Chapter12WienerFutureProcess
import Chapter12ZeroExtensionTruncation
import Chapter12FiniteWienerInformation
import Chapter12FutureDirections
import FullAuditMartingaleHilbert

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

theorem finite_continuous_m2_sum {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : HalfClosedTime → MeasurableSpace Ω)
    (N : ι → HalfClosedTime → Ω → ℝ) (hN : ∀ i,ContinuousM2Witness P F (N i)) :
    ContinuousM2Witness P F (fun t w => ∑ i,N i t w) := by
  classical
  have h (s : Finset ι) : ContinuousM2Witness P F (fun t w => ∑ i ∈ s,N i t w) := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty,Pi.zero_def] using ContinuousM2Witness.zero P F
    | @insert i s hi ih =>
      simpa only [Finset.sum_insert hi,Pi.add_def] using (hN i).add P F ih
  exact h Finset.univ

/-- The finite vector Wiener map has a single continuous adapted prefix
for every direction. Its future truncations are the increments to the terminal
value of that same process. -/
theorem vector_wiener_future_process {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P (d+1))
    (J : Fin (d+1) → Lp ℝ 2 (volume.restrict (Ioi (0:ℝ))) →ₗᵢ[ℝ] Lp ℝ 2 P)
    (I : PiLp 2 (fun _ : Fin (d+1) => Lp ℝ 2 (volume.restrict (Ioi (0:ℝ)))) →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hI : ∀ f,I f=∑ i,J i (f i))
    (hJ : ∀ i (f : ℝ → ℝ) (hm : Measurable f) (hi : MemLp f 2 (volume.restrict (Ioi (0:ℝ)))),
      ∃ N : HalfClosedTime → Ω → ℝ,∃ hN : ContinuousM2Witness P B.F N,
        ItoCovarianceFormula P B.F (B.W i) (fun z => f z.2) N ∧
        J i (hi.toLp f)=(hN.moment ⊤).toLp (N ⊤))
    (T : ℝ) (u : FiniteWienerHilbert d T) :
    let E := L2ZeroExtension (E := ℝ) (volume.restrict (Ioi (0:ℝ))) (Iic T) measurableSet_Iic
    let V := finitePiIsometry (ι := Fin (d+1)) E
    let W := I.comp V
    ∃ N : HalfClosedTime → Ω → ℝ,ContinuousM2Witness P B.F N ∧
      (W u : Ω → ℝ)=ᵐ[P] N ⊤ ∧
      ∀ a,0≤a → (W (finiteFuturePart T a u) : Ω → ℝ)=ᵐ[P]
        fun w => N ⊤ w-N (realTimeClamp a) w := by
  classical
  intro E V W
  choose N hN hNI hJN hfut using fun i => coordinate_wiener_future_process P B i (J i) (hJ i)
    (E (u i)) (Lp.stronglyMeasurable (E (u i))).measurable (Lp.memLp (E (u i)))
  have hjn i : J i (E (u i))=(hN i |>.moment ⊤).toLp (N i ⊤) := by
    simpa only [Lp.toLp_coeFn] using hJN i
  refine ⟨fun t w => ∑ i,N i t w,finite_continuous_m2_sum P B.F N hN,?_,?_⟩
  · change (I (V u) : Ω → ℝ)=ᵐ[P] _
    rw [hI]
    have he i : (J i (E (u i)) : Ω → ℝ)=ᵐ[P] N i ⊤ := by
      rw [hjn i]
      exact (hN i |>.moment ⊤).coeFn_toLp
    filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i => J i (E (u i))),
      ae_all_iff.mpr he] with w hw hn
    change (∑ i,J i (E (u i))) w=∑ i,N i ⊤ w
    rw [hw]
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl (fun i _ => hn i)
  · intro a ha
    have hcoord i : E (finiteFuturePart T a u i)=
        ((Lp.memLp (E (u i))).indicator measurableSet_Ioi).toLp ((Ioi a).indicator (E (u i) : ℝ → ℝ)) := by
      exact zero_extension_indicator _ _ _ measurableSet_Iic measurableSet_Ioi (u i)
    have he i : (J i (E (finiteFuturePart T a u i)) : Ω → ℝ)=ᵐ[P]
        fun w => N i ⊤ w-N i (realTimeClamp a) w := by
      rw [hcoord i]
      exact hfut i a ha
    change (I (V (finiteFuturePart T a u)) : Ω → ℝ)=ᵐ[P] _
    rw [hI]
    filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i => J i (E (finiteFuturePart T a u i))),
      ae_all_iff.mpr he] with w hw hn
    change (∑ i,J i (E (finiteFuturePart T a u i))) w=_
    rw [hw]
    simp only [Finset.sum_apply]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => hn i)

end Asakura.Chapter12
#print axioms Asakura.Chapter12.vector_wiener_future_process
