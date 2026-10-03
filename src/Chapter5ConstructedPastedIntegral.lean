import Chapter5LocalBrownianIntegral
import Chapter5PastedIntegralPrefix

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- The actual local integral of the manuscript's countable pasting is
constructed and identified with every finite sum of represented increments. -/
theorem ceil_pasted_integral_constructed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t E, MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    (W A : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hA : LocalCovarianceWitness P F W W A)
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (hcm : StrictMono c) (hcT : ∀ n, (c n:EReal) < T)
    (hct : StrictMono (fun n => realTimeClamp (T := T) (c n)))
    (hcut : ∀ n, realTimeClamp (T := T) (c n) < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hclock : ∀ n w r, r ∈ Icc 0 (c n) → A (realTimeClamp r) w = r)
    (H : ℕ → Ω × ℝ → ℝ) (hm : ∀ j,Measurable (H j))
    (hp : ∀ j l,@Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) (c l) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c l) => H j (z.1,z.2.val)))
    (hi : ∀ j,MemLp (H j) 2 (P.prod (volume.restrict (Ioi 0))))
    (M : ℕ → ClosedTime T → Ω → ℝ) (hM : ∀ j,LocalMProcessWitness P F (M j))
    (hI : ∀ (j : ℕ),ItoCovarianceFormula P F W
      (fun z => (Ioc (j:ℝ) (j+1)).indicator (fun r => H j (z.1,r)) z.2) (M j)) :
    let G := fun z : Ω × ℝ => H (Nat.ceil z.2-1) z
    ∃ J : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F J ∧ ItoCovarianceFormula P F W G J ∧
      (∀ R : ℝ,MemLp G 2 (P.prod (volume.restrict (Ioc 0 R)))) ∧
      (∀ᵐ w ∂P,∀ N : ℕ,∀ t,t<⊤ → J (min (realTimeClamp (N:ℝ)) t) w=∑ j∈Finset.range N,M j t w) := by
  dsimp only
  let G := fun z : Ω × ℝ => H (Nat.ceil z.2-1) z
  have hgm : Measurable G := by
    have hh : Measurable (fun p : (Ω × ℝ) × ℕ => H (p.2-1) p.1) :=
      measurable_from_prod_countable_left (fun j => hm (j-1))
    exact hh.comp (measurable_id.prodMk (Nat.measurable_ceil.comp measurable_snd))
  have hgp l := ceil_integrand_progressive (c l)
    (fun t : Icc (0:ℝ) (c l) => F (realTimeClamp t.val)) (fun j => H (j-1)) (fun j => hp (j-1) l)
  have hgl R := ceil_integrand_local_L2 P (fun j => H (j-1)) (fun j => hm (j-1)) (fun j => hi (j-1)) R
  obtain ⟨J,hJ,hJI⟩ := brownian_local_L2_integral_constructed P hT F hF hle hnull W A hW hA
    c hc hcm hcT hct hcut hcc hclock G hgm hgp (fun l => hgl (c l))
  refine ⟨J,hJ,hJI,hgl,?_⟩
  apply ae_all_iff.mpr
  intro N
  exact pasted_integral_prefix_identification P hT F hF hle hnull W J hW hJ H M hM hI
    (fun w => hgm.comp measurable_prodMk_left) hJI N

end Asakura.Chapter5
