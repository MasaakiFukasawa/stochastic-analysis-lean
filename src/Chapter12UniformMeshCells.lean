import Chapter12PolygonalConstruction

open Set
namespace Asakura.Chapter12
set_option maxHeartbeats 1200000

theorem exists_uniform_mesh_cell (h : ℝ) (hh : 0<h) (n : ℕ) (hn : 0<n)
    (t : ℝ) (ht : t∈Icc (0:ℝ) ((n:ℝ)*h)) :
    ∃ k : ℕ,k<n ∧ t∈Icc ((k:ℝ)*h) (((k:ℝ)+1)*h) := by
  induction n generalizing t with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n=0
    · subst n
      refine ⟨0,by omega,?_⟩
      simpa using ht
    · by_cases htn : t≤(n:ℝ)*h
      · obtain ⟨k,hk,hkt⟩ := ih (by omega) t ⟨ht.1,htn⟩
        exact ⟨k,by omega,hkt⟩
      · exact ⟨n,by omega,⟨(lt_of_not_ge htn).le,by simpa using ht.2⟩⟩

end Asakura.Chapter12
