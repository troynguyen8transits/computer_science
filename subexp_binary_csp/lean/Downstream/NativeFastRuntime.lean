import Downstream.CoreRuntime
import Downstream.TotalCounter

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! One globally correct native counter, with its uniform fast bound on large
bounded-degree CSPs. Runtime is measured on the original canonical bit input;
the three unused advice headers are zero and parameters are computed internally.
-/

namespace CSPConsequence.NativeFastRuntime

open Groundwork Printed Turing NodeRefinement

def polynomialDegree {Δ : ℕ} (c : CounterExistence.Counter Δ) (q : ℕ) : ℕ :=
  CoreRuntime.timeDegree c+CoreRuntime.stateDegree c*q

noncomputable def exponentialCoefficient {Δ : ℕ} (c : CounterExistence.Counter Δ) (q : ℕ) : ℝ :=
  OperationBound.coefficient c+q*CliqueBudget.coefficient c

noncomputable def polynomialCoefficient {Δ : ℕ} (c : CounterExistence.Counter Δ) (q : ℕ) : ℝ :=
  (q*(3*(CoreRuntime.timeFactor c:ℝ)+1)*((CoreRuntime.stateFactor c:ℝ)+4)^q)*
    4^(polynomialDegree c q)

def Correct (N : TM2ComputableAux Bool Bool) : Prop :=
  ∀ {k D : ℕ} (I : Instance k D), ∃ t,
    Nonempty (TM2OutputsInTime N.tm
      ((AutomaticCounter.canonicalInput I).map N.inputAlphabet.invFun)
      (some ((Nat.bits I.count).map N.outputAlphabet.invFun)) t)

def FastBound {Δ : ℕ} (c : CounterExistence.Counter Δ)
    (N : TM2ComputableAux Bool Bool) (q : ℕ) : Prop :=
  ∀ {k D : ℕ} (I : Instance k D), c.K 0^32 ≤ k → 2 ≤ D → (∀ a, I.degree a ≤ Δ) →
    ∃ t, Nonempty (TM2OutputsInTime N.tm
      ((AutomaticCounter.canonicalInput I).map N.inputAlphabet.invFun)
      (some ((Nat.bits I.count).map N.outputAlphabet.invFun)) t) ∧
      (t:ℝ) ≤ polynomialCoefficient c q*
        ((AutomaticCounter.canonicalInput I).length:ℝ)^(polynomialDegree c q)*
        Real.exp (exponentialCoefficient c q*LogCost.scale k (Nat.size D))

theorem for_counter {Δ : ℕ} (c : CounterExistence.Counter Δ) (hΔ : 1 ≤ Δ) :
    ∃ (N : TM2ComputableAux Bool Bool) (q : ℕ), (∀ i, Finite (N.tm.Γ i)) ∧
      Correct N ∧ FastBound c N q := by
  obtain ⟨N,q,hfin,hhost⟩ := TotalCounter.native_from_runs c
  refine ⟨N,q,hfin,?_,?_⟩
  · intro k D I
    obtain ⟨T,S,hr⟩ := TotalCounter.correct c hΔ I
    exact ⟨_,hhost I T S hr⟩
  · intro k D I hlarge hD hdeg
    let l := LevelSelection.select c.K k
    let K := c.K l
    let g := 3*K^8
    let b := Nat.size D
    let E := (BitInputCodec.encode (paramsOf I g b,unary K)).length
    let L := (AutomaticCounter.canonicalInput I).length
    have hK : 2 ≤ K := c.levels.K_two l
    have hpos : 0 < D := by omega
    have hb : 1 ≤ b := FinitePreparation.bitWidth_pos hpos
    have hg : 0 < g := by dsimp [g]; positivity
    have hselected := LevelSelection.selected_bounds c.K k (c.levels.K_two 0)
      c.levels.K_lt c.growth10 hlarge
    have hsize : K^32 ≤ k := hselected.1
    have hu : k ≤ K^320 := hselected.2.le
    have hKk : K ≤ k := (le_self_pow (by omega : 1 ≤ K) (by decide : 32 ≠ 0)).trans hsize
    have hk : 2 ≤ k := by omega
    have hgk : g ≤ k := LevelSelection.grouping_fits hK hsize
    have hbD : b ≤ D := Nat.size_le.mpr Nat.lt_two_pow_self
    have hEform : E = k+D+g+b+K+5+k^2+k^2*D^2 := BitInputCodec.encode_paramsOf_length I g b K
    have hLform : L = k+D+5+k^2+k^2*D^2 := by
      simpa only [L,AutomaticCounter.canonicalInput,add_zero] using BitInputCodec.encode_paramsOf_length I 0 0 0
    have hE1 : 1 ≤ E := by omega
    have hLE : L ≤ E := by omega
    have hEL : E ≤ 4*L := by omega
    obtain ⟨T,S,hr,ht,hs⟩ := CoreRuntime.actual c I b l hg hpos hb
      FinitePreparation.bitWidth_capacity hΔ hdeg hsize hu rfl
    have hnative := hhost I (3*T) (S+1)
      (TotalCounter.fast_branch_runs c I hlarge hD hdeg hr)
    let t := q*(3*T+1)*(L+(S+1)+1)^q
    have hnative' : Nonempty (TM2OutputsInTime N.tm
        ((AutomaticCounter.canonicalInput I).map N.inputAlphabet.invFun)
        (some ((Nat.bits I.count).map N.outputAlphabet.invFun)) t) := hnative
    have hEr : (1:ℝ) ≤ E := by exact_mod_cast hE1
    have hR : 0 ≤ LogCost.scale k b :=
      (LogCost.scale_pos (by exact_mod_cast hk) (by exact_mod_cast hb)).le
    have hs' : ((S+1:ℕ):ℝ) ≤ ((CoreRuntime.stateFactor c:ℝ)+1)*(E:ℝ)^(CoreRuntime.stateDegree c)+
        Real.exp (CliqueBudget.coefficient c*LogCost.scale k b) := by
      have hp : (1:ℝ) ≤ (E:ℝ)^(CoreRuntime.stateDegree c) := one_le_pow₀ hEr
      push_cast
      nlinarith
    have hh := NativeAbsorption.host_bound_with_input
      (CoreRuntime.stateDegree c) (CoreRuntime.timeDegree c) q
      (by unfold CoreRuntime.stateDegree; omega) hEr (by positivity) (by positivity)
      (by positivity : (0:ℝ)≤T) (by positivity : (0:ℝ)≤(S+1:ℕ))
      (OperationBound.coefficient_nonneg c hΔ) (CliqueBudget.coefficient_nonneg c hΔ) hR ht hs'
    have hAeq : ((CoreRuntime.stateFactor c:ℝ)+1)+3 = (CoreRuntime.stateFactor c:ℝ)+4 := by ring
    rw [hAeq] at hh
    let F : ℝ := q*(3*(CoreRuntime.timeFactor c:ℝ)+1)*((CoreRuntime.stateFactor c:ℝ)+4)^q
    have hF : 0 ≤ F := by dsimp [F]; positivity
    have htimeE : (t:ℝ) ≤ F*(E:ℝ)^(polynomialDegree c q)*
        Real.exp (exponentialCoefficient c q*LogCost.scale k b) := by
      calc
        _ ≤ (q:ℝ)*(3*(T:ℝ)+1)*((E:ℝ)+(S+1:ℕ)+1)^q := by
          dsimp [t]
          push_cast
          gcongr <;> exact_mod_cast hLE
        _ ≤ _ := hh
    refine ⟨t,hnative',?_⟩
    calc
      _ ≤ F*(E:ℝ)^(polynomialDegree c q)*
          Real.exp (exponentialCoefficient c q*LogCost.scale k b) := htimeE
      _ ≤ F*(4*(L:ℝ))^(polynomialDegree c q)*
          Real.exp (exponentialCoefficient c q*LogCost.scale k b) := by
        gcongr <;> exact_mod_cast hEL
      _ = _ := by
        rw [mul_pow]
        unfold polynomialCoefficient
        dsimp [F,L]
        ring

theorem exists_native (Δ : ℕ) (hΔ : 1 ≤ Δ) :
    ∃ (c : CounterExistence.Counter Δ) (N : TM2ComputableAux Bool Bool) (q : ℕ),
      (∀ i, Finite (N.tm.Γ i)) ∧ Correct N ∧ FastBound c N q := by
  obtain ⟨c⟩ := CounterExistence.exists_counter Δ
  obtain ⟨N,q,hfin,hcorrect,hfast⟩ := for_counter c hΔ
  exact ⟨c,N,q,hfin,hcorrect,hfast⟩

#print axioms for_counter
#print axioms exists_native

end CSPConsequence.NativeFastRuntime
