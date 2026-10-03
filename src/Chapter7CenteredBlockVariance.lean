import Chapter7ConditionalOrthogonality
import Chapter7MeanSquareProbability

open MeasureTheory Finset
open scoped BigOperators
namespace Asakura.Chapter7
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

/-- Second moments of centered time blocks add. The individual centering
and orthogonality are supplied by conditional expectations of the actual
Brownian block integrals. -/
theorem centered_block_variance {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (U : Fin n → Ω → ℝ)
    (hU : ∀ k,MemLp (U k) 2 P) (F : Fin n → MeasurableSpace Ω)
    (hle : ∀ k,F k ≤ m)
    (hpast : ∀ i j : Fin n,i < j → StronglyMeasurable[F j] (U i))
    (hce : ∀ k,P[U k|F k] =ᵐ[P] fun _ => ∫ w,U k w ∂P) :
    (∫ w,(∑ k,(U k w-(∫ v,U k v ∂P)))^2 ∂P)=
      ∑ k,∫ w,(U k w-(∫ v,U k v ∂P))^2 ∂P := by
  letI : MeasurableSpace Ω := m
  classical
  let Z := fun k w => U k w-(∫ v,U k v ∂P)
  have hZ k : MemLp (Z k) 2 P := (hU k).sub (memLp_const _)
  have hz k : P[Z k|F k] =ᵐ[P] 0 := by
    have he := condExp_sub ((hU k).integrable (by norm_num)) (integrable_const (∫ v,U k v ∂P)) (F k)
    have hc : P[(fun _ => ∫ v,U k v ∂P)|F k] = fun _ => ∫ v,U k v ∂P :=
      condExp_of_stronglyMeasurable (hle k) stronglyMeasurable_const (integrable_const _)
    filter_upwards [he,hce k] with w hw hw'
    change P[Z k|F k] w = P[U k|F k] w-P[(fun _ => ∫ v,U k v ∂P)|F k] w at hw
    rw [hc,hw',sub_self] at hw
    exact hw
  have ho (i j : Fin n) (hij : i < j) : (∫ w,Z i w*Z j w ∂P)=0 := by
    exact conditional_centered_cross P (Z i) (Z j) (hZ i) (hZ j) (F j) (hle j)
      ((hpast i j hij).sub stronglyMeasurable_const) (hz j)
  apply orthogonal_square_sum P univ Z (fun k _ => hZ k)
  intro i _ j _ hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact ho i j h
  · simpa only [mul_comm] using ho j i h

end Asakura.Chapter7
