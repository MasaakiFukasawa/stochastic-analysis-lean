import Chapter4IndependentSquareMoment
import Chapter4LevyConstructed

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

lemma indepFun_of_independent_information {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] (P : Measure Ω) (F : MeasurableSpace Ω)
    (Z : Ω → ℝ) (Y : Ω → E)
    (hind : Indep (MeasurableSpace.comap Z inferInstance) F P)
    (hY : Measurable[F] Y) : IndepFun Z Y P := by
  apply indepFun_iff_measure_inter_preimage_eq_mul.2
  intro s t hs ht
  exact (hind.indepSet_of_measurableSet ⟨s,hs,rfl⟩ (hY ht)).measure_inter_eq_mul

/-- A square-integrable coefficient known at the left endpoint may multiply
the following Brownian increment; boundedness is unnecessary. -/
theorem predictable_brownian_increment_square_moment
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W A : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hA : LocalCovarianceWitness P F W W A)
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → A (realTimeClamp r) w=r)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T) (s : ℝ) (hs : s∈Icc 0 R)
    (G : Ω → ℝ) (hGa : Measurable[F (realTimeClamp s)] G) (hG : MemLp G 2 P) :
    MemLp (fun w => G w*(W (realTimeClamp R) w-W (realTimeClamp s) w)) 2 P ∧
    (∫ w,(G w*(W (realTimeClamp R) w-W (realTimeClamp s) w))^2 ∂P)=
      (R-s)*(∫ w,G w^2 ∂P) := by
  obtain ⟨hlaw,hind⟩ := levy_gaussian_increment_constructed P hT F hF hle hnull W A hW hA hclock R hR hRT s hs
  have hh := gaussian_weighted_increment_energy P G _ hG _ hlaw
    (indepFun_of_independent_information P _ _ G hind hGa).symm
  simpa only [NNReal.toReal] using hh

end Asakura.Chapter4
