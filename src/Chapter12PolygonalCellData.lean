import Chapter12UniformMeshCells

open Set
namespace Asakura.Chapter12
set_option maxHeartbeats 1800000

/-- Each value of the constructed finite-sum path is a convex combination
of two original values at distance at most the mesh size. -/
theorem polygonal_cell_data {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (T h : ℝ) (hh : 0<h) (n : ℕ) (hn : 0<n)
    (hT : (n:ℝ)*h=T) (t : Icc (0:ℝ) T) :
    ∃ l r : Icc (0:ℝ) T,∃ a : ℝ,0≤a ∧ a≤1 ∧
      (l:ℝ)≤t ∧ (t:ℝ)≤r ∧ (r:ℝ)-l≤h ∧
      polygonalPath f h n t=(1-a) • f l+a • f r := by
  obtain ⟨k,hk,hkt⟩ := exists_uniform_mesh_cell h hh n hn t (by simpa [hT] using t.property)
  have hk0 : 0≤(k:ℝ)*h := mul_nonneg (Nat.cast_nonneg k) hh.le
  have hk1 : ((k:ℝ)+1)*h≤T := by
    rw [← hT]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hh.le
  have hkl : (k:ℝ)*h≤((k:ℝ)+1)*h := by nlinarith
  let l : Icc (0:ℝ) T := ⟨(k:ℝ)*h,hk0,hkl.trans hk1⟩
  let r : Icc (0:ℝ) T := ⟨((k:ℝ)+1)*h,hk0.trans hkl,hk1⟩
  refine ⟨l,r,(t-(k:ℝ)*h)/h,div_nonneg (sub_nonneg.mpr hkt.1) hh.le,?_,hkt.1,hkt.2,?_,?_⟩
  · apply (div_le_one hh).mpr
    linarith [hkt.2]
  · change ((k:ℝ)+1)*h-(k:ℝ)*h≤h
    ring_nf
    rfl
  · exact polygonalPath_on_cell f h hh n k hk t hkt

end Asakura.Chapter12
