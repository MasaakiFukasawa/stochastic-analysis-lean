import Chapter13PrimitiveProducts

open MeasureTheory Set
namespace Asakura.Chapter13
set_option maxHeartbeats 2000000

theorem cheyette_state_kernel {n:ℕ} (A:Fin n → Fin n → ℝ → ℝ)
    (g:Fin n → ℝ → ℝ) (v K N:Fin n → ℝ) (a t:ℝ)
    (hA:∀i j,IntervalIntegrable (A i j) volume a t)
    (hg:∀j,IntervalIntegrable (g j) volume a t) :
    (∑i,v i*((∑j,∫u in a..t,A i j u*(K j-∫s in a..u,g j s))+N i))=
      (∑i,∑j,v i*(∫u in a..t,A i j u)*(K j-∫s in a..t,g j s))+
      ∑i,v i*((∑j,∫u in a..t,(∫s in a..u,A i j s)*g j u)+N i) := by
  simp_rw [cheyette_primitive_kernel _ _ _ _ _ (hA _ _) (hg _)]
  simp only [Finset.sum_add_distrib,mul_add,Finset.mul_sum]
  ring_nf

/-- In particular the forward curve on its diagonal is the short rate. -/
theorem cheyette_short_rate {n:ℕ} (f:ℝ) (g G X:Fin n → ℝ) (Y:Fin n → Fin n → ℝ) :
    f+(∑i,∑j,g i*Y i j*(G j-G j))+(∑i,g i*X i)=f+∑i,g i*X i := by simp

end Asakura.Chapter13
#print axioms Asakura.Chapter13.cheyette_state_kernel
#print axioms Asakura.Chapter13.cheyette_short_rate
