import Chapter4FiniteSumPathMoment

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4.Vector
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

/-- Combining the actual coordinate drift and stochastic estimates. -/
theorem coordinate_estimates_assemble
    {Ω D : Type*} [MeasurableSpace Ω] [MetricSpace D] [CompactSpace D]
    [SecondCountableTopology D] (P : Measure Ω) {dim noise : ℕ}
    (V : Ω → C(D,Fin dim → ℝ)) (hv : Measurable V)
    (A : Fin dim → Ω → C(D,ℝ)) (Z : Fin dim → Fin noise → Ω → C(D,ℝ))
    (hai : ∀ i,MemLp (A i) 2 P) (hzi : ∀ i j,MemLp (Z i j) 2 P)
    (a b : ℝ) (ha : ∀ i,(∫ w,‖A i w‖^2 ∂P)≤a)
    (hb : ∀ i j,(∫ w,‖Z i j w‖^2 ∂P)≤b)
    (he : ∀ i,∀ᵐ w ∂P,coordinateRealPath (V w) i=A i w+∑ j,Z i j w) :
    MemLp V 2 P ∧ (∫ w,‖V w‖^2 ∂P)≤(dim:ℝ)*(2*a+2*(noise:ℝ)^2*b) := by
  classical
  let Q := fun i w => coordinateRealPath (V w) i
  have hqm i : Measurable (Q i) := coordinate_path_measurable V hv i
  have hqi i : MemLp (Q i) 2 P := by
    have hz := (finite_sum_path_moment P (Z i) (hzi i)).1
    have hs : MemLp (fun w => A i w+∑ j,Z i j w) 2 P :=
      MemLp.add (f := A i) (g := fun w => ∑ j,Z i j w) (hai i) hz
    exact (memLp_congr_ae (he i)).2 hs
  have hqb i : (∫ w,‖Q i w‖^2 ∂P)≤2*a+2*(noise:ℝ)^2*b := by
    obtain ⟨hz,hzb⟩ := finite_sum_path_moment P (Z i) (hzi i)
    have hsum : (∑ j,∫ w,‖Z i j w‖^2 ∂P)≤(noise:ℝ)*b := by
      simpa using Finset.sum_le_sum (s := Finset.univ) (fun j _ => hb i j)
    have hh := (path_sum_square_moment P (A i) (fun w => ∑ j,Z i j w) (hai i) hz).2
    have heq : (∫ w,‖Q i w‖^2 ∂P)=(∫ w,‖A i w+∑ j,Z i j w‖^2 ∂P) :=
      integral_congr_ae ((he i).mono (fun w hw => congrArg (fun x => ‖x‖^2) hw))
    rw [heq]
    have hzb' := hzb.trans (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg noise))
    nlinarith only [hh,ha i,hzb']
  have hbun : (fun w => bundleRealPaths (fun i => Q i w))=V := by
    funext w
    apply ContinuousMap.ext
    intro r
    rfl
  constructor
  · rw [← hbun]
    exact bundle_path_memLp P Q hqm hqi
  · have hh := bundle_path_second_moment P Q hqm hqi
    simp_rw [show ∀ w,bundleRealPaths (fun i => Q i w)=V w from fun w => congrFun hbun w] at hh
    exact hh.trans (by simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hqb i))

end Asakura.Chapter4.Vector
