import Chapter12PolygonalMesh

open Set
namespace Asakura.Chapter12
set_option maxHeartbeats 1800000

noncomputable def polygonalPath {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (h : ℝ) (n : ℕ) (t : ℝ) : E :=
  f 0+∑ k∈Finset.range n,
    ((min (((k:ℝ)+1)*h) t-min ((k:ℝ)*h) t)/h) • (f (((k:ℝ)+1)*h)-f ((k:ℝ)*h))

theorem polygonalPath_continuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (h : ℝ) (n : ℕ) : Continuous (polygonalPath f h n) := by
  unfold polygonalPath
  fun_prop

theorem polygonalPath_past {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (h : ℝ) (hh : 0≤h) (k n : ℕ) (hkn : k≤n)
    (t : ℝ) (ht : t≤(k:ℝ)*h) : polygonalPath f h n t=polygonalPath f h k t := by
  induction n,hkn using Nat.le_induction with
  | base => rfl
  | succ n hkn ih =>
    have hn : t≤(n:ℝ)*h := ht.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hkn) hh)
    have hn1 : t≤((n:ℝ)+1)*h := by nlinarith
    simpa only [polygonalPath,Finset.sum_range_succ,min_eq_right hn,min_eq_right hn1,
      sub_self,zero_div,zero_smul,add_zero] using ih

theorem polygonalPath_after {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (h : ℝ) (hh : 0<h) (n : ℕ)
    (t : ℝ) (ht : (n:ℝ)*h≤t) : polygonalPath f h n t=f ((n:ℝ)*h) := by
  induction n with
  | zero => simp [polygonalPath]
  | succ n ih =>
    have hn : (n:ℝ)*h≤t := by push_cast at ht; nlinarith
    have hn1 : ((n:ℝ)+1)*h≤t := by simpa using ht
    have hd : (((n:ℝ)+1)*h-(n:ℝ)*h)/h=1 := by field_simp; ring
    have hi := ih hn
    simp only [polygonalPath] at hi ⊢
    rw [Finset.sum_range_succ,min_eq_left hn,min_eq_left hn1,hd,one_smul]
    rw [← add_assoc,hi]
    simp only [Nat.cast_add,Nat.cast_one]
    abel

theorem polygonalPath_on_cell {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (h : ℝ) (hh : 0<h) (n k : ℕ) (hk : k<n)
    (t : ℝ) (ht : t∈Icc ((k:ℝ)*h) (((k:ℝ)+1)*h)) :
    polygonalPath f h n t=
      (1-(t-(k:ℝ)*h)/h) • f ((k:ℝ)*h)+
      ((t-(k:ℝ)*h)/h) • f (((k:ℝ)+1)*h) := by
  rw [polygonalPath_past f h hh.le (k+1) n hk t (by simpa using ht.2)]
  have he := polygonalPath_after f h hh k t ht.1
  simp only [polygonalPath] at he ⊢
  rw [Finset.sum_range_succ,min_eq_right ht.2,min_eq_left ht.1,← add_assoc,he]
  module

end Asakura.Chapter12
