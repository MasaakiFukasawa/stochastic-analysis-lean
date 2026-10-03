import Chapter12AffineForcingArray
import Mathlib.Analysis.Calculus.ContDiff.Operations

open scoped Topology ContDiff
namespace Asakura.Chapter12
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem affine_forcing_array_difference {n : ℕ} {K E : Type*}
    [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L M : (Fin n → ℝ) →L[ℝ] C(K,E)) (a b : C(K,E))
    (B ε : ℝ) (hB : 0≤B) (hε : 0≤ε)
    (hb : ∀t,Real.sqrt (∑i,‖L (Pi.single i 1) t-M (Pi.single i 1) t‖^2)≤B*ε)
    (k : ℕ) (hk : 1≤k) (z : Fin n → ℝ) (t : K) :
    Real.sqrt (∑i : Fin k → Fin n,
      ‖(iteratedFDeriv ℝ k (fun y => a+L y) z (fun j => Pi.single (i j) 1)) t-
        (iteratedFDeriv ℝ k (fun y => b+M y) z (fun j => Pi.single (i j) 1)) t‖^2)≤
      (if k=1 then B else 0)*ε := by
  have he : (fun y => a+L y)-(fun y => b+M y)=(fun y => (a-b)+(L-M) y) := by
    funext y
    simp only [Pi.sub_apply,ContinuousLinearMap.sub_apply]
    abel
  have hd := iteratedFDeriv_sub_apply
    ((contDiff_const.add L.contDiff : ContDiff ℝ (k:ℕ∞ω) (fun y => a+L y))).contDiffAt
    ((contDiff_const.add M.contDiff : ContDiff ℝ (k:ℕ∞ω) (fun y => b+M y))).contDiffAt (x:=z)
  rw [he] at hd
  have hp := affine_forcing_array_bounds (L-M) (a-b) (B*ε) (mul_nonneg hB hε)
    (fun s => by simpa only [ContinuousLinearMap.sub_apply,ContinuousMap.sub_apply] using hb s) k hk z t
  rw [hd] at hp
  simpa only [ContinuousMultilinearMap.sub_apply,ContinuousMap.sub_apply,ite_mul,zero_mul] using hp
end Asakura.Chapter12
#print axioms Asakura.Chapter12.affine_forcing_array_difference
