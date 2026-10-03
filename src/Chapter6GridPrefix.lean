import Chapter6BrownianGridLinearMoments

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped Topology ENNReal NNReal BigOperators
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

noncomputable def gridPrefix {n d : ℕ} (k : ℕ) (j : Fin d) : (Fin n → Fin d → ℝ) →L[ℝ] ℝ :=
  ∑ a : Fin n,if a.val<k then (ContinuousLinearMap.proj j : (Fin d → ℝ) →L[ℝ] ℝ).comp (ContinuousLinearMap.proj a : (Fin n → Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) else 0

lemma gridPrefix_apply {n d : ℕ} (k : ℕ) (j : Fin d) (z : Fin n → Fin d → ℝ) :
    gridPrefix k j z=∑ a : Fin n,if a.val<k then z a j else 0 := by
  simp only [gridPrefix,ContinuousLinearMap.sum_apply]
  apply sum_congr rfl
  intro a _
  by_cases ha : a.val<k <;> simp [ha]

lemma gridPrefix_basis {n d : ℕ} (k : ℕ) (j : Fin d) (a : Fin n) (b : Fin d) :
    gridPrefix k j (Pi.single a (Pi.single b 1))=if a.val<k ∧ b=j then 1 else 0 := by
  classical
  rw [gridPrefix_apply]
  rw [Finset.sum_eq_single a]
  · by_cases h : a.val<k <;> by_cases he : b=j <;> simp [Pi.single_apply,h,he,eq_comm]
  · intro a' _ hne
    simp [Pi.single_apply,hne]
  · simp

lemma finite_prefix_count {n k : ℕ} (hk : k≤n) :
    (∑ a : Fin n,if a.val<k then (1:ℝ) else 0)=k := by
  rw [Fin.sum_univ_eq_sum_range (fun a : ℕ => if a<k then (1:ℝ) else 0)]
  have he : (Finset.range n).filter (fun a => a<k)=Finset.range k := by
    ext a
    simp only [Finset.mem_filter,Finset.mem_range]
    exact ⟨fun h => h.2,fun h => ⟨h.trans_le hk,h⟩⟩
  rw [← Finset.sum_filter,he]
  simp

lemma gridPrefix_covariance_sum {n d : ℕ} (k l : ℕ) (hk : k≤n) (hl : l≤n) (i j : Fin d) :
    (∑ a : Fin n,∑ b : Fin d,gridPrefix k i (Pi.single a (Pi.single b 1))*gridPrefix l j (Pi.single a (Pi.single b 1)))=
      if i=j then ((min k l:ℕ):ℝ) else 0 := by
  classical
  simp only [gridPrefix_basis]
  have hi (a : Fin n) : (∑ b : Fin d,(if a.val<k ∧ b=i then (1:ℝ) else 0)*(if a.val<l ∧ b=j then 1 else 0))=
      if i=j ∧ a.val<min k l then 1 else 0 := by
    by_cases ha : a.val<k <;> by_cases hb : a.val<l <;> by_cases he : i=j <;> simp [ha,hb,he,lt_min_iff,eq_comm]
  simp_rw [hi]
  by_cases hij : i=j
  · simp only [hij,true_and,ite_true]
    exact finite_prefix_count ((min_le_left k l).trans hk)
  · simp [hij]

/-- Prefixes of the actual increment grid recover Brownian samples on
one common full-measure set, by telescoping and W_0=0. -/
theorem gridPrefix_brownian_sample {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P d)
    (h : ℝ) (k : ℕ) (hk : k≤n) (j : Fin d) :
    (fun w => gridPrefix k j (finiteNoiseGrid (fun i r => B.W i (realTimeClamp r)) h n w))=ᵐ[P]
      B.W j (realTimeClamp ((k:ℝ)*h)) := by
  classical
  filter_upwards [(B.martingale j).initial P B.F] with w hw
  rw [gridPrefix_apply]
  dsimp only [finiteNoiseGrid]
  rw [Fin.sum_univ_eq_sum_range (fun a : ℕ => if a<k then B.W j (realTimeClamp (((a:ℝ)+1)*h)) w-B.W j (realTimeClamp ((a:ℝ)*h)) w else 0)]
  have he : (Finset.range n).filter (fun a => a<k)=Finset.range k := by
    ext a
    simp only [Finset.mem_filter,Finset.mem_range]
    exact ⟨fun h => h.2,fun h => ⟨h.trans_le hk,h⟩⟩
  rw [← Finset.sum_filter,he]
  have hz : realTimeClamp (T := ⊤) 0=⊥ := by apply Subtype.ext; simp [realTimeClamp]
  have ht := Finset.sum_range_sub (fun a : ℕ => B.W j (realTimeClamp ((a:ℝ)*h)) w) k
  simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_zero,zero_mul,hz,hw,Pi.zero_apply,sub_zero] using ht

end Asakura.Chapter6
