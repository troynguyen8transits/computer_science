import Downstream.SelectedBounds
import Downstream.LogCost
import Downstream.CounterExistence

set_option autoImplicit false
set_option maxHeartbeats 3000000

/-! Uniform exponential bound on the actual imported clique budget at the
actual CSP network parameters, including its natural ceiling and integer B'. -/

namespace CSPConsequence.CliqueBudget

noncomputable def rateA {Δ : ℕ} (c : CounterExistence.Counter Δ) : ℝ := max c.A 0+1

noncomputable def coefficient {Δ : ℕ} (c : CounterExistence.Counter Δ) : ℝ :=
  90*rateA c*Δ*Real.log 2+5796*c.C₀*LogCost.polyCoefficient Δ+Real.log 2

theorem coefficient_nonneg {Δ : ℕ} (c : CounterExistence.Counter Δ) (hΔ : 1 ≤ Δ) :
    0 ≤ coefficient c := by
  have ha : 0 ≤ rateA c := by unfold rateA; have := le_max_right c.A 0; linarith
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogΔ : 0 ≤ Real.log (Δ:ℝ) := Real.log_nonneg (by exact_mod_cast hΔ)
  have hlog17 : 0 ≤ Real.log 17 := Real.log_nonneg (by norm_num)
  unfold coefficient LogCost.polyCoefficient
  positivity

theorem actual {Δ k D g : ℕ} (c : CounterExistence.Counter Δ)
    (I : Instance k D) (b l : ℕ) (hg : 0 < g) (hpos : 0 < D)
    (hb : 1 ≤ b) (hD : D ≤ 2^b) (hΔ : 1 ≤ Δ) (hdeg : ∀ a, I.degree a ≤ Δ)
    (hsize : (c.K l)^32 ≤ k) (hu : k ≤ (c.K l)^320) (hgK : g = 3*(c.K l)^8) :
    (LevelCounter.budget (c.e l) c.C₀ (c.K l) g (Δ*b*(k/g+1))
      ((k/g+1)+(k/g+1)*(k/g+1)+1)
      (BitNetwork.data I ⟨0,hpos⟩ b (balanced hg)).U : ℝ) ≤
        Real.exp (coefficient c*LogCost.scale k b) := by
  let K := c.K l
  let N := BitNetwork.data I ⟨0,hpos⟩ b (balanced hg)
  let P := Δ*b*(k/g+1)
  let B := (k/g+1)+(k/g+1)*(k/g+1)+1
  let L := AppRunningTime.Lof K g ((1:ℝ)/(2*K)) P N.U
  let B' := AppRunningTime.B'of K g P B
  have hK : 2 ≤ K := c.levels.K_two l
  have bounds : SelectedBounds.Bounds K k g P B N.U Δ b L B' :=
    SelectedBounds.actual I b Δ K hg hpos hb hD hΔ hdeg hK hsize hgK
  have hn : N.Is P B := BitNetwork.is_valid I ⟨0,hpos⟩ hg hb hD hΔ hdeg
  have hg2 : 2 ≤ g := by
    have hp : 1 ≤ K^8 := one_le_pow₀ (by omega : 1 ≤ K)
    change g = 3*K^8 at hgK
    omega
  have hL : 1 ≤ L := (LevelCounter.parameters_pos K N P B hK hg2 hn).1
  have ha : 0 ≤ rateA c := by unfold rateA; have := le_max_right c.A 0; linarith
  have hlogK : 0 < Real.logb 2 (K:ℝ) := Real.logb_pos (by norm_num) (by exact_mod_cast hK)
  have he0 : 0 ≤ c.e l := by
    have hh : (0:ℝ) ≤ 1/(Real.logb 2 (K:ℝ))^c.C₀ := by positivity
    exact hh.trans (c.levels.e_ge l)
  have hA : c.A ≤ rateA c := by unfold rateA; have := le_max_left c.A 0; linarith
  have he : c.e l ≤ rateA c/Real.sqrt (Real.logb 2 (K:ℝ)) :=
    (c.rate l).trans (div_le_div_of_nonneg_right hA (Real.sqrt_nonneg _))
  have harg : (K:ℝ)*(L+B') ≤ 17*(Δ:ℝ)*b*k^5 := by exact_mod_cast bounds.argument
  have hlog := LogCost.bound_log_le K c.C₀ L B' hK hL
    (by exact_mod_cast bounds.k_two) (by exact_mod_cast hb) (by exact_mod_cast hΔ)
    (by exact_mod_cast hsize) (by exact_mod_cast hu) ha he0 he bounds.scaled harg
  have hceil := LogCost.ceil_log (LogCost.bound_one_le K c.C₀ L B' (by omega) hL he0)
    hlog (by exact_mod_cast bounds.k_two) (by exact_mod_cast hb)
  simpa only [LevelCounter.budget,coefficient] using Real.le_exp_of_log_le hceil

#print axioms coefficient_nonneg
#print axioms actual

end CSPConsequence.CliqueBudget
