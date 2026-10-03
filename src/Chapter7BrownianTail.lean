import Chapter7AugmentedMartingale
import Chapter7ConcatenatedCovariance
import Chapter7ClockHalfTime
import Chapter4BrownianSystem

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

noncomputable def independentProductFiltration
    {Ω Γ : Type*} [m : MeasurableSpace Ω] [n : MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ)
    (F : HalfClosedTime → MeasurableSpace Ω) (H : HalfClosedTime → MeasurableSpace Γ)
    (t : HalfClosedTime) : MeasurableSpace (Ω × Γ) :=
  Asakura.nullAugmentation (m := productSigma m n) (P.prod Q) (productSigma (F t) (H t))

/-- The independent Brownian-tail extension used in the written CLT:
actual local martingales and covariance are constructed on the product
probability space. The extension agrees on the original prefix and its
bracket diverges at infinity for every path. -/
theorem independent_brownian_tail
    {Ω Γ : Type*} [m : MeasurableSpace Ω] [n : MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (M C : HalfClosedTime → Ω → ℝ) (hM : LocalMProcessWitness P F M)
    (hC : LocalCovarianceWitness P F M M C) (B : BrownianSystem Q 1)
    (a : ℝ) (ha : 0 ≤ a) :
    let G := independentProductFiltration P Q F B.F
    let Z := fun t (z : Ω × Γ) => M (min (realTimeClamp a) t) z.1+
      (B.W 0 t z.2-B.W 0 (min (realTimeClamp a) t) z.2)
    let A := fun t (z : Ω × Γ) => C (min (realTimeClamp a) t) z.1+
      (B.C 0 0 t z.2-B.C 0 0 (min (realTimeClamp a) t) z.2)
    Monotone G ∧ (∀ t,G t ≤ productSigma m n) ∧
    (∀ t N,MeasurableSet[productSigma m n] N → (P.prod Q) N = 0 → MeasurableSet[G t] N) ∧
    LocalMProcessWitness (P.prod Q) G Z ∧ LocalCovarianceWitness (P.prod Q) G Z Z A ∧
    (∀ r,0 ≤ r → ∀ z,A (realTimeClamp r) z = C (realTimeClamp (min a r)) z.1+max 0 (r-a)) ∧
    (∀ r,r ∈ Icc 0 a → ∀ z,Z (realTimeClamp r) z = M (realTimeClamp r) z.1) ∧
    (∀ z r,∃ t,t < ⊤ ∧ r < A t z) := by
  letI : MeasurableSpace Ω := m
  letI : MeasurableSpace Γ := n
  let H := fun t => productSigma (F t) (B.F t)
  let G := independentProductFiltration P Q F B.F
  have hHl t : H t ≤ productSigma m n := product_sigma_mono (hle t) (B.le t)
  have hGm : Monotone G := fun s t hst => null_augmentation_mono (P.prod Q)
    (product_sigma_mono (hF hst) (B.mono hst))
  have hGl t : G t ≤ productSigma m n := fun _ he => he.1
  have hGn t N (hmN : MeasurableSet[productSigma m n] N) (hzN : (P.prod Q) N = 0) :
      MeasurableSet[G t] N := null_augmentation_null (P.prod Q) (H t) N hmN hzN
  have hMl := local_null_augmentation (P.prod Q) H hHl _ (local_product_fst P Q F B.F hle B.le M hM)
  have hBl := local_null_augmentation (P.prod Q) H hHl _ (local_product_snd P Q F B.F hle B.le (B.W 0) (B.martingale 0))
  have hCl := covariance_null_augmentation (P.prod Q) H hHl _ _ _
    (covariance_product_fst P Q F B.F hle B.le M M C hC)
  have hDl := covariance_null_augmentation (P.prod Q) H hHl _ _ _
    (covariance_product_snd P Q F B.F hle B.le (B.W 0) (B.W 0) (B.C 0 0) (B.cov 0 0))
  have hσ t : MeasurableSet[G t] {z : Ω × Γ | realTimeClamp a ≤ t} := by
    by_cases ht : realTimeClamp a ≤ t <;> simp [ht]
  obtain ⟨hZ,hA⟩ := concatenated_local_covariance (P.prod Q) G hGm hGl hGn
    (fun t z => M t z.1) (fun t z => B.W 0 t z.2)
    (fun t z => C t z.1) (fun t z => B.C 0 0 t z.2) hMl hBl hCl hDl (fun _ => realTimeClamp a) hσ
  have he r (hr : 0 ≤ r) (z : Ω × Γ) :
      C (min (realTimeClamp a) (realTimeClamp r)) z.1+
        (B.C 0 0 (realTimeClamp r) z.2-B.C 0 0 (min (realTimeClamp a) (realTimeClamp r)) z.2) =
      C (realTimeClamp (min a r)) z.1+max 0 (r-a) := by
    rw [← real_time_clamp_mono.map_min,B.diagonal_clock 0 z.2 r hr,
      B.diagonal_clock 0 z.2 (min a r) (le_min ha hr)]
    congr 1
    by_cases har : a ≤ r
    · rw [min_eq_left har,max_eq_right (sub_nonneg.mpr har)]
    · rw [min_eq_right (le_of_not_ge har),max_eq_left (sub_nonpos.mpr (le_of_not_ge har)),sub_self]
  refine ⟨hGm,hGl,hGn,hZ,hA,he,?_,?_⟩
  · intro r hr z
    dsimp only
    rw [min_eq_right (real_time_clamp_mono hr.2),sub_self,add_zero]
  · intro z r
    let b := max a (max 0 (r-C (realTimeClamp a) z.1+a))+1
    have hb : 0 ≤ b := by dsimp [b]; positivity
    have hab : a ≤ b := by dsimp [b]; linarith [le_max_left a (max 0 (r-C (realTimeClamp a) z.1+a))]
    refine ⟨realTimeClamp b,changed_time_finite b hb,?_⟩
    dsimp only
    rw [he b hb z,min_eq_left hab,max_eq_right (sub_nonneg.mpr hab)]
    dsimp only [b]
    have hh := le_trans (le_max_right 0 (r-C (realTimeClamp a) z.1+a))
      (le_max_right a (max 0 (r-C (realTimeClamp a) z.1+a)))
    linarith

end Asakura.Chapter7
