import Chapter4PositiveTimeExtension

open Set Filter Function
open scoped Topology
namespace Asakura.Chapter11
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- A smooth retraction into an open interval, identical near a prescribed
compact subinterval. It localizes C1,2 functions without asking for second
time derivatives. -/
theorem interval_smooth_retraction (a l u b : ℝ) (hal : a<l) (hlu : l≤u) (hub : u<b) :
    ∃ ρ : ℝ → ℝ,ContDiff ℝ 2 ρ ∧ (∀ x,ρ x∈Ioo a b) ∧
      ∀ x∈Icc l u,ρ =ᶠ[𝓝 x] id := by
  have hab : a<b := hal.trans_le hlu |>.trans hub
  obtain ⟨χ,hχ,hχb,hsupp,hone⟩ := exists_contDiff_support_eq_eq_one_iff
    (n:=(2:ℕ∞)) (s:=Ioo a b) (t:=Icc ((a+l)/2) ((u+b)/2)) isOpen_Ioo isClosed_Icc
    (by intro x hx;constructor <;> linarith [hx.1,hx.2])
  let c := (a+b)/2
  have hc : c∈Ioo a b := by dsimp only [c];constructor <;> linarith
  let ρ := fun x => χ x*x+(1-χ x)*c
  refine ⟨ρ,(hχ.mul contDiff_id).add ((contDiff_const.sub hχ).mul contDiff_const),?_,?_⟩
  · intro x
    have hχx := hχb (mem_range_self x)
    by_cases hx : x∈Ioo a b
    · simpa only [smul_eq_mul] using (convex_Ioo a b) hx hc hχx.1 (sub_nonneg.mpr hχx.2) (by ring : χ x+(1-χ x)=1)
    · have hz : χ x=0 := notMem_support.mp (by rwa [hsupp])
      simpa only [ρ,hz,zero_mul,sub_zero,one_mul,zero_add] using hc
  · intro x hx
    have hxi : x∈Ioo ((a+l)/2) ((u+b)/2) := by constructor <;> linarith [hx.1,hx.2]
    filter_upwards [isOpen_Ioo.mem_nhds hxi] with y hy
    have hy1 := (hone y).mp ⟨hy.1.le,hy.2.le⟩
    simp only [ρ,hy1,one_mul,sub_self,zero_mul,add_zero,id_eq]

end Asakura.Chapter11
