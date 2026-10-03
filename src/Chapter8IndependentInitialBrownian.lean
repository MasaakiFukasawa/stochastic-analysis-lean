import Chapter7BrownianTail

open MeasureTheory Set
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter4 Asakura.Chapter7
open Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Adjoin an independent initial state, retaining the Brownian martingale
and cross-covariance structure in the completed product filtration. -/
theorem independent_initial_brownian {E Ω : Type*}
    [e : MeasurableSpace E] [m : MeasurableSpace Ω]
    (π : Measure E) (P : Measure Ω) [IsProbabilityMeasure π] [IsProbabilityMeasure P]
    {n : ℕ} (B : BrownianSystem P n) :
    ∃ B' : BrownianSystem (π.prod P) n,
      (∀ j t z,B'.W j t z=B.W j t z.2) ∧
      (∀ t,Measurable[B'.F t] (Prod.fst : E × Ω → E)) := by
  let F : HalfClosedTime → MeasurableSpace E := fun _ => e
  let H := fun t => productSigma e (B.F t)
  let G := independentProductFiltration π P F B.F
  have hHl t : H t≤productSigma e m := product_sigma_mono le_rfl (B.le t)
  have hGm : Monotone G := fun s t hst => null_augmentation_mono (π.prod P)
    (product_sigma_mono le_rfl (B.mono hst))
  have hGl t : G t≤productSigma e m := fun _ he => he.1
  have hGn t N (hN : MeasurableSet[productSigma e m] N) (hz : (π.prod P) N=0) :
      MeasurableSet[G t] N := null_augmentation_null (π.prod P) (H t) N hN hz
  have hW j := local_null_augmentation (π.prod P) H hHl _
    (local_product_snd π P F B.F (fun _ => le_rfl) B.le (B.W j) (B.martingale j))
  have hC j k := covariance_null_augmentation (π.prod P) H hHl _ _ _
    (covariance_product_snd π P F B.F (fun _ => le_rfl) B.le
      (B.W j) (B.W k) (B.C j k) (B.cov j k))
  let B' : BrownianSystem (π.prod P) n := {
    F := G, mono := hGm, le := hGl, null := hGn
    W := fun j t z => B.W j t z.2
    C := fun j k t z => B.C j k t z.2
    martingale := hW, cov := hC
    clock := fun j k z r hr => B.clock j k z.2 r hr }
  refine ⟨B',fun _ _ _ => rfl,?_⟩
  intro t
  apply (show Measurable[H t] (Prod.fst : E × Ω → E) from measurable_fst).mono _ le_rfl
  exact sigma_le_null_augmentation (π.prod P) (H t) (hHl t)

end Asakura.Chapter8
