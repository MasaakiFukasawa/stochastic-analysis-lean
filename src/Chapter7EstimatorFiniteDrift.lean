import Chapter7OriginalEstimatorMatrixCLT
import Chapter7OriginalEstimatorConsistency

open MeasureTheory ProbabilityTheory Matrix Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

lemma realized_entry_finite_congr {Ω : Type*} (X X' Y Y' : ℝ → Ω → ℝ) (T : ℝ) (hT : 0<T)
    (hX : ∀ t∈Icc 0 T,∀ w,X t w=X' t w) (hY : ∀ t∈Icc 0 T,∀ w,Y t w=Y' t w) (n : ℕ) :
    realizedProcessEntry X Y T (n+1)=realizedProcessEntry X' Y' T (n+1) := by
  funext w
  dsimp only [realizedProcessEntry]
  congr 1
  apply sum_congr rfl
  intro k _
  have hs := grid_left_in_interval T hT.le n k
  have he := grid_right_in_interval T hT n k
  simp only [Nat.cast_add,Nat.cast_one,hX _ hs,hX _ he,hY _ hs,hY _ he]

lemma drifted_projection_finite_extension {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (u : Fin d → ℝ) (b : ℝ → Ω → ℝ) (x : Ω → ℝ) (T t : ℝ) (ht : t∈Icc 0 T) (w : Ω) :
    driftedProjectionProcess B u (finiteDriftExtension b T) x t w=driftedProjectionProcess B u b x t w := by
  dsimp only [driftedProjectionProcess]
  rw [finite_drift_integral b T t ht.1 ht.2]

theorem finite_interval_estimator_matrix_clt {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {d : ℕ} (B : BrownianSystem P d) (Baux : BrownianSystem Q 1)
    (S : Matrix (Fin d) (Fin d) ℝ)
    (T K : ℝ) (hT : 0<T) (hK : 0≤K) (b : Fin d → ℝ → Ω → ℝ) (x : Fin d → Ω → ℝ)
    (hbc : ∀ i w,ContinuousOn (fun r => b i r w) (Icc 0 T))
    (hba : ∀ i r,r∈Icc 0 T → Measurable[B.F (realTimeClamp r)] (b i r))
    (hbb : ∀ i r,r∈Icc 0 T → ∀ w,|b i r w|≤K) (hx : ∀ i,Measurable (x i)) :
    TendstoInDistribution (fun n => normalizedEstimatorMatrix
      (fun i => driftedProjectionProcess B (S i) (b i) (x i)) S T (n+1)) atTop
      id (fun _ => P) (estimatorGaussianLaw S) := by
  let c := fun i => finiteDriftExtension (b i) T
  have hc i := finite_drift_extension (b i) T hT.le (hbc i)
  have hca i r (hr : r∈Icc 0 T) : Measurable[B.F (realTimeClamp r)] (c i r) := by
    have he : c i r=b i r := funext ((hc i).2 r hr)
    rw [he]
    exact hba i r hr
  have hcb i r (hr : r∈Icc 0 T) w : |c i r w|≤K := by
    change |finiteDriftExtension (b i) T r w|≤K
    rw [(hc i).2 r hr w]
    exact hbb i r hr w
  have hd := original_estimator_matrix_clt P Q B Baux S T K hT hK c x
    (fun i => (hc i).1) hca hcb hx
  apply hd.congr _ (ae_of_all _ (fun _ => rfl))
  intro n
  apply ae_of_all
  intro w
  ext p
  change Real.sqrt ((n+1:ℕ):ℝ)*(_-_)=Real.sqrt ((n+1:ℕ):ℝ)*(_-_)
  have he := realized_entry_finite_congr
    (driftedProjectionProcess B (S p.1) (c p.1) (x p.1))
    (driftedProjectionProcess B (S p.1) (b p.1) (x p.1))
    (driftedProjectionProcess B (S p.2) (c p.2) (x p.2))
    (driftedProjectionProcess B (S p.2) (b p.2) (x p.2)) T hT
    (fun t ht w => drifted_projection_finite_extension B (S p.1) (b p.1) (x p.1) T t ht w)
    (fun t ht w => drifted_projection_finite_extension B (S p.2) (b p.2) (x p.2) T t ht w) n
  rw [he]

theorem finite_interval_estimator_entry_consistency {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (u v : Fin d → ℝ) (T K : ℝ) (hT : 0<T) (hK : 0≤K) (b c : ℝ → Ω → ℝ) (x y : Ω → ℝ)
    (hbc : ∀ w,ContinuousOn (fun r => b r w) (Icc 0 T))
    (hcc : ∀ w,ContinuousOn (fun r => c r w) (Icc 0 T))
    (hba : ∀ r∈Icc 0 T,Measurable[B.F (realTimeClamp r)] (b r))
    (hca : ∀ r∈Icc 0 T,Measurable[B.F (realTimeClamp r)] (c r))
    (hbb : ∀ r∈Icc 0 T,∀ w,|b r w|≤K) (hcb : ∀ r∈Icc 0 T,∀ w,|c r w|≤K) :
    TendstoInMeasure P (fun n => realizedProcessEntry (driftedProjectionProcess B u b x)
      (driftedProjectionProcess B v c y) T (n+1)) atTop (fun _ => ∑ j,u j*v j) := by
  have hb := finite_drift_extension b T hT.le hbc
  have hc := finite_drift_extension c T hT.le hcc
  have hbe r (hr : r∈Icc 0 T) : finiteDriftExtension b T r=b r := funext (hb.2 r hr)
  have hce r (hr : r∈Icc 0 T) : finiteDriftExtension c T r=c r := funext (hc.2 r hr)
  have hd := original_estimator_entry_consistency P B u v T K hT hK
    (finiteDriftExtension b T) (finiteDriftExtension c T) x y hb.1 hc.1
    (fun r hr => by rw [hbe r hr]; exact hba r hr)
    (fun r hr => by rw [hce r hr]; exact hca r hr)
    (fun r hr w => by rw [hbe r hr]; exact hbb r hr w)
    (fun r hr w => by rw [hce r hr]; exact hcb r hr w)
  apply hd.congr_left
  intro n
  have he := realized_entry_finite_congr
    (driftedProjectionProcess B u (finiteDriftExtension b T) x) (driftedProjectionProcess B u b x)
    (driftedProjectionProcess B v (finiteDriftExtension c T) y) (driftedProjectionProcess B v c y) T hT
    (fun t ht w => drifted_projection_finite_extension B u b x T t ht w)
    (fun t ht w => drifted_projection_finite_extension B v c y T t ht w) n
  exact ae_of_all P (fun w => congrFun he w)

end Asakura.Chapter7
