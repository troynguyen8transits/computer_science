import Downstream.LogCost

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! A fixed native host polynomial preserves a uniform sublinear domain
exponent, while keeping input-length factors polynomial. This lemma is purely
quantitative and is applied to the actual native machine separately. -/

namespace CSPConsequence.NativeAbsorption

theorem add_exp {x y C D R : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hR : 1 ≤ R)
    (hx : x ≤ Real.exp (C*R)) (hy : y ≤ Real.exp (D*R)) :
    x+y ≤ Real.exp ((C+D+Real.log 2)*R) := by
  have hc : 1 ≤ Real.exp (C*R) := Real.one_le_exp_iff.mpr (by positivity)
  have hd : 1 ≤ Real.exp (D*R) := Real.one_le_exp_iff.mpr (by positivity)
  have h1 := le_mul_of_one_le_right (Real.exp_nonneg (C*R)) hd
  have h2 := le_mul_of_one_le_left (Real.exp_nonneg (D*R)) hc
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  calc
    _ ≤ Real.exp (C*R)+Real.exp (D*R) := add_le_add hx hy
    _ ≤ 2*Real.exp (C*R)*Real.exp (D*R) := by linarith
    _ = Real.exp (Real.log 2+(C+D)*R) := by
      rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2),add_mul,Real.exp_add]
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hR hlog2])

theorem mul_exp {x y C D R : ℝ} (hy0 : 0 ≤ y)
    (hx : x ≤ Real.exp (C*R)) (hy : y ≤ Real.exp (D*R)) :
    x*y ≤ Real.exp ((C+D)*R) := by
  calc
    _ ≤ Real.exp (C*R)*Real.exp (D*R) := mul_le_mul hx hy hy0 (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add,add_mul]

theorem pow_exp {x C R : ℝ} (n : ℕ) (hx0 : 0 ≤ x) (hx : x ≤ Real.exp (C*R)) :
    x^n ≤ Real.exp ((n:ℝ)*C*R) := by
  calc
    _ ≤ (Real.exp (C*R))^n := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul,mul_assoc]

theorem host_bound {T S L A Cₜ Cₛ R : ℝ} (a q : ℕ)
    (ha : 1 ≤ a) (hL : 1 ≤ L) (hA : 0 ≤ A) (hT0 : 0 ≤ T) (hS0 : 0 ≤ S)
    (hCt : 0 ≤ Cₜ) (hCs : 0 ≤ Cₛ) (hR : 0 ≤ R)
    (hT : T ≤ Real.exp (Cₜ*R))
    (hS : S ≤ A*L^a+Real.exp (Cₛ*R)) :
    (q:ℝ)*(3*T+1)*(L+S+1)^q ≤
      (4*q*(A+3)^q)*L^(a*q)*Real.exp ((Cₜ+q*Cₛ)*R) := by
  have hEt : 1 ≤ Real.exp (Cₜ*R) := Real.one_le_exp_iff.mpr (mul_nonneg hCt hR)
  have hEs : 1 ≤ Real.exp (Cₛ*R) := Real.one_le_exp_iff.mpr (mul_nonneg hCs hR)
  have hLa : L ≤ L^a := le_self_pow₀ hL (by omega)
  have hLa1 : 1 ≤ L^a := one_le_pow₀ hL
  have harg : L+S+1 ≤ (A+3)*L^a*Real.exp (Cₛ*R) := by
    calc
      _ ≤ (A+2)*L^a+Real.exp (Cₛ*R) := by nlinarith
      _ ≤ (A+2)*L^a*Real.exp (Cₛ*R)+L^a*Real.exp (Cₛ*R) := by
        exact add_le_add
          (le_mul_of_one_le_right (by positivity) hEs)
          (le_mul_of_one_le_left (Real.exp_nonneg _) hLa1)
      _ = _ := by ring
  have ht : 3*T+1 ≤ 4*Real.exp (Cₜ*R) := by linarith
  have hexp : Real.exp (Cₜ*R)*(Real.exp (Cₛ*R))^q =
      Real.exp ((Cₜ+q*Cₛ)*R) := by
    rw [← Real.exp_nat_mul,← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ (q:ℝ)*(4*Real.exp (Cₜ*R))*((A+3)*L^a*Real.exp (Cₛ*R))^q := by
      gcongr
    _ = (4*q*(A+3)^q)*L^(a*q)*(Real.exp (Cₜ*R)*(Real.exp (Cₛ*R))^q) := by
      rw [mul_pow,mul_pow,← pow_mul]
      ring
    _ = _ := by rw [hexp]

theorem host_bound_with_input {T S L A B Cₜ Cₛ R : ℝ} (a d q : ℕ)
    (ha : 1 ≤ a) (hL : 1 ≤ L) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hT0 : 0 ≤ T) (hS0 : 0 ≤ S) (hCt : 0 ≤ Cₜ) (hCs : 0 ≤ Cₛ) (hR : 0 ≤ R)
    (hT : T ≤ B*L^d*Real.exp (Cₜ*R))
    (hS : S ≤ A*L^a+Real.exp (Cₛ*R)) :
    (q:ℝ)*(3*T+1)*(L+S+1)^q ≤
      (q*(3*B+1)*(A+3)^q)*L^(d+a*q)*Real.exp ((Cₜ+q*Cₛ)*R) := by
  have hEt : 1 ≤ Real.exp (Cₜ*R) := Real.one_le_exp_iff.mpr (mul_nonneg hCt hR)
  have hEs : 1 ≤ Real.exp (Cₛ*R) := Real.one_le_exp_iff.mpr (mul_nonneg hCs hR)
  have hLa : L ≤ L^a := le_self_pow₀ hL (by omega)
  have hLa1 : 1 ≤ L^a := one_le_pow₀ hL
  have hLd : 1 ≤ L^d := one_le_pow₀ hL
  have harg : L+S+1 ≤ (A+3)*L^a*Real.exp (Cₛ*R) := by
    calc
      _ ≤ (A+2)*L^a+Real.exp (Cₛ*R) := by nlinarith
      _ ≤ (A+2)*L^a*Real.exp (Cₛ*R)+L^a*Real.exp (Cₛ*R) :=
        add_le_add (le_mul_of_one_le_right (by positivity) hEs)
          (le_mul_of_one_le_left (Real.exp_nonneg _) hLa1)
      _ = _ := by ring
  have ht : 3*T+1 ≤ (3*B+1)*L^d*Real.exp (Cₜ*R) := by
    have hh : 1 ≤ L^d*Real.exp (Cₜ*R) := by nlinarith
    nlinarith
  have hexp : Real.exp (Cₜ*R)*(Real.exp (Cₛ*R))^q = Real.exp ((Cₜ+q*Cₛ)*R) := by
    rw [← Real.exp_nat_mul,← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ (q:ℝ)*((3*B+1)*L^d*Real.exp (Cₜ*R))*((A+3)*L^a*Real.exp (Cₛ*R))^q := by
      gcongr
    _ = (q*(3*B+1)*(A+3)^q)*L^(d+a*q)*
        (Real.exp (Cₜ*R)*(Real.exp (Cₛ*R))^q) := by
      rw [mul_pow,mul_pow,← pow_mul,pow_add]
      ring
    _ = _ := by rw [hexp]

#print axioms host_bound
#print axioms add_exp
#print axioms host_bound_with_input

end CSPConsequence.NativeAbsorption
