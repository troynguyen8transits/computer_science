import Downstream.OperationBound
import Downstream.RuntimeMetadata
import Downstream.BitInputSizes

set_option autoImplicit false
set_option maxHeartbeats 3000000

/-! Actual counter runs with uniform exponential time and polynomial-plus-
exponential state bounds. These are the inputs to the fixed native host bound. -/

namespace CSPConsequence.CoreRuntime

open Groundwork Printed NodeRefinement QuerySizes

def timeFactor {Δ : ℕ} (c : CounterExistence.Counter Δ) : ℕ := (2*Δ+7)^c.C₁
def stateFactor {Δ : ℕ} (c : CounterExistence.Counter Δ) : ℕ := (8*Δ+45)+(2*Δ+12)^c.C₁
def timeDegree {Δ : ℕ} (c : CounterExistence.Counter Δ) : ℕ := 3*c.C₁
def stateDegree {Δ : ℕ} (c : CounterExistence.Counter Δ) : ℕ := 3*c.C₁+2

theorem actual {Δ k D g : ℕ} (c : CounterExistence.Counter Δ)
    (I : Instance k D) (b l : ℕ) (hg : 0 < g) (hpos : 0 < D)
    (hb : 1 ≤ b) (hD : D ≤ 2^b) (hΔ : 1 ≤ Δ) (hdeg : ∀ a, I.degree a ≤ Δ)
    (hsize : (c.K l)^32 ≤ k) (hu : k ≤ (c.K l)^320) (hgK : g = 3*(c.K l)^8) :
    let E := (BitInputCodec.encode (paramsOf I g b,unary (c.K l))).length
    ∃ T S : ℕ,
      c.machine.Runs (paramsOf I g b,unary (c.K l)) (3*T) S (I.count:ℤ) ∧
      (T:ℝ) ≤ (timeFactor c:ℝ)*(E:ℝ)^(timeDegree c)*
        Real.exp (OperationBound.coefficient c*LogCost.scale k b) ∧
      (S:ℝ) ≤ (stateFactor c:ℝ)*(E:ℝ)^(stateDegree c)+
        Real.exp (CliqueBudget.coefficient c*LogCost.scale k b) := by
  intro E
  let K := c.K l
  let ctx := paramsOf I g b
  let P := Δ*b*(k/g+1)
  let B := (k/g+1)+(k/g+1)*(k/g+1)+1
  let N := BitNetwork.data I ⟨0,hpos⟩ b (balanced hg)
  let 𝒯 := LevelCounter.budget (c.e l) c.C₀ K g P B N.U
  have hK : 2 ≤ K := c.levels.K_two l
  have bounds : SelectedBounds.Bounds K k g P B N.U Δ b
      (AppRunningTime.Lof K g ((1:ℝ)/(2*K)) P N.U) (AppRunningTime.B'of K g P B) :=
    SelectedBounds.actual I b Δ K hg hpos hb hD hΔ hdeg hK hsize hgK
  have hg2 : 2 ≤ g := by
    have hp : 1 ≤ K^8 := one_le_pow₀ (by omega : 1 ≤ K)
    change g = 3*K^8 at hgK
    omega
  obtain ⟨T,hr,hT⟩ := c.correct I b l hg hpos hb hD hΔ hdeg hg2 hgK
  let S := size ctx+(𝒯+(g*(P+B)+size (1,2*K))^c.C₁)+room ctx g P B+4
  have hrun : c.machine.Runs (ctx,unary K) (3*T) S (I.count:ℤ) := hr
  have hE : E = k+D+g+b+K+5+k^2+k^2*D^2 := BitInputCodec.encode_paramsOf_length I g b K
  have hE1 : 1 ≤ E := by omega
  have hk : 1 ≤ k := by have := bounds.k_two; omega
  have hkE : k ≤ E := by omega
  have hgE : g ≤ E := by omega
  have hbE : b ≤ E := by omega
  have hKE : K ≤ E := by omega
  have hctx : size ctx ≤ 10*E := BitInputCodec.paramsOf_size_le_encode I g b K
  have hmeta := RuntimeMetadata.metadata hk hE1 hkE hgE hbE hKE (Δ := Δ)
  have hV : g*(P+B) ≤ (2*Δ+7)*E^3 := hmeta.2.2.1
  have hbudget : (𝒯:ℝ) ≤ Real.exp (CliqueBudget.coefficient c*LogCost.scale k b) :=
    CliqueBudget.actual c I b l hg hpos hb hD hΔ hdeg hsize hu hgK
  have htime := OperationBound.grouping_bound c hΔ hK bounds.k_two hb hsize hu hgK
    bounds.volume hbudget hV (C₁ := c.C₁)
  have ht : (T:ℝ) ≤ (timeFactor c:ℝ)*(E:ℝ)^(timeDegree c)*
      Real.exp (OperationBound.coefficient c*LogCost.scale k b) := by
    have hh := hT.trans htime
    simpa only [timeFactor,timeDegree,Nat.cast_pow,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hh
  have hstate := RuntimeMetadata.state_bound ctx k g b Δ K c.C₁ 𝒯 E
    hk hE1 hkE hgE hbE hKE hctx
  have hs : (S:ℝ) ≤ (stateFactor c:ℝ)*(E:ℝ)^(stateDegree c)+
      Real.exp (CliqueBudget.coefficient c*LogCost.scale k b) := by
    have hh : (S:ℝ) ≤ (stateFactor c:ℝ)*(E:ℝ)^(stateDegree c)+(𝒯:ℝ) := by
      exact_mod_cast hstate
    linarith
  exact ⟨T,S,hrun,ht,hs⟩

#print axioms actual

end CSPConsequence.CoreRuntime
