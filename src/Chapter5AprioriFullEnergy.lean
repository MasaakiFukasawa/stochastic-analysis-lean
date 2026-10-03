import Chapter5AprioriAtTime
import Chapter5IntegratedPointwiseEstimate

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- The two printed a priori bounds, including the uniform-in-time bound,
from the already constructed energy identity. All tail restrictions and
expectation/time interchanges are justified by the original L² data. -/
theorem apriori_full_energy_from_constructed_energy
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : ℝ) (hR : 0 ≤ R) (β C l m : ℝ)
    (hC : 0 ≤ C) (hl : C < l) (hm : 0 < m) (hβ : C*(2+l)+m ≤ β)
    (Y Z D F : Ω × ℝ → ℝ)
    (hYm : Measurable Y) (hZm : Measurable Z) (hDm : Measurable D) (hFm : Measurable F)
    (hY : MemLp Y 2 (P.prod (volume.restrict (Ioc 0 R))))
    (hZ : MemLp Z 2 (P.prod (volume.restrict (Ioc 0 R))))
    (hD : MemLp D 2 (P.prod (volume.restrict (Ioc 0 R))))
    (hξ : MemLp (fun w => Y (w,R)) 2 P)
    (hbound : ∀ w r, r ∈ Icc 0 R → |F (w,r)| ≤ C*(|Y (w,r)|+|Z (w,r)|)+|D (w,r)|)
    (hYt : ∀ t ∈ Icc 0 R, MemLp (fun w => Y (w,t)) 2 P)
    (N : ℝ → Ω → ℝ)
    (hNi : ∀ t ∈ Icc 0 R, Integrable (N t) P)
    (hN0 : ∀ t ∈ Icc 0 R, (∫ w,N t w ∂P) = 0)
    (he : ∀ t ∈ Icc 0 R, ∀ᵐ w ∂P,
      Real.exp (β*t)*Y (w,t)^2 + (∫ r in t..R,β*Real.exp (β*r)*Y (w,r)^2) +
      (∫ r in t..R,Real.exp (β*r)*Z (w,r)^2) =
      Real.exp (β*R)*Y (w,R)^2 + (∫ r in t..R,2*Real.exp (β*r)*Y (w,r)*F (w,r))-N t w) :
    let K := (∫ w,Real.exp (β*R)*Y (w,R)^2 ∂P)+(∫ w,(∫ r in 0..R,Real.exp (β*r)*D (w,r)^2) ∂P)/m
    (∀ t ∈ Icc 0 R, (∫ w,Real.exp (β*t)*Y (w,t)^2 ∂P) ≤ K) ∧
    (∫ w,(∫ r in 0..R,Real.exp (β*r)*Y (w,r)^2) ∂P) ≤ R*K ∧
    (∫ w,(∫ r in 0..R,Real.exp (β*r)*Z (w,r)^2) ∂P) ≤ l/(l-C)*K := by
  dsimp only
  have hl0 : 0 < l := hC.trans_lt hl
  have hβ0 : 0 ≤ β := (by positivity : 0 ≤ C*(2+l)+m).trans hβ
  obtain ⟨_,hDp,hDi,_⟩ := finite_time_weighted_energy P R hR β hβ0 D hDm hD
  have hat t ht := apriori_at_time_from_constructed_energy P R hR β C l m hC hl hm hβ
    Y Z D F hYm hZm hDm hFm hY hZ hD hξ hbound t ht (hYt t ht) (N t) (hNi t ht) (hN0 t ht) (he t ht)
  have hpoint t (ht : t ∈ Icc 0 R) : (∫ w,Real.exp (β*t)*Y (w,t)^2 ∂P) ≤
      (∫ w,Real.exp (β*R)*Y (w,R)^2 ∂P)+(∫ w,(∫ r in 0..R,Real.exp (β*r)*D (w,r)^2) ∂P)/m := by
    have htail := (finite_time_weighted_tail_energy P R hR β hβ0 D hDm hD t ht).2
    have hdle : (∫ w,(∫ r in t..R,Real.exp (β*r)*D (w,r)^2) ∂P) ≤
        ∫ w,(∫ r in 0..R,Real.exp (β*r)*D (w,r)^2) ∂P := by
      apply integral_mono_ae htail hDi
      filter_upwards [hDp] with w hw
      exact intervalIntegral.integral_mono_interval ht.1 ht.2 le_rfl
        (ae_of_all _ fun r => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)) hw
    have hddiv := div_le_div_of_nonneg_right hdle hm.le
    linarith [(hat t ht).1]
  refine ⟨hpoint,?_,(hat 0 ⟨le_rfl,hR⟩).2⟩
  exact integrated_pointwise_energy_bound P R hR β hβ0 Y hYm hY _
    (fun t ht => hpoint t ⟨ht.1.le,ht.2⟩)

end Asakura.Chapter5
