import Downstream.ProviderGive
import Printed.GroupingProcs
import Printed.HandOver
import ExplicitCost.GroupingDefs

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! Preparation of the grouping input with the group count supplied in unary.
Unlike Printed.inputOf_polyT's fixed-g interface, the certificate below uses
one polynomial for every group count. The inputOf correctness lemma is imported
directly from Anthropic's Printed.GroupingProcs. -/

namespace CSPConsequence.DynamicPreparation

open Groundwork Printed ProviderParameters ProviderMetadata NodeRefinement

def networkInput (Δ : ℕ) (c : Params) : NetInput :=
  inputOf (groupCount c) ((procs Δ).P c) ((procs Δ).B c)
    ((procs Δ).len c) ((procs Δ).cap c)

theorem networkInput_polyT (Δ : ℕ) : PolyT (networkInput Δ) := by
  have hP : PolyT (fun c : Params => List.replicate ((procs Δ).P c) ()) := boundP_unary Δ
  have hB : PolyT (fun c : Params => List.replicate ((procs Δ).B c) ()) := boundB_unary
  have hl : PolyT (fun p : Params × ℕ => List.replicate ((procs Δ).len p.1 p.2) ()) :=
    nodeLength_unary
  have hc : PolyT (fun p : (Params × ℕ) × ℕ =>
      List.replicate ((procs Δ).cap p.1.1 p.1.2 p.2) ()) :=
    PolyT.comp (g := fun p : (Params × ℕ) × ℕ => (p.1.1,p.1.2,p.2))
      edgeCapacity_unary (by fun_prop)
  have hg : Unary groupCount := Unary.of_length (by fun_prop)
  unfold networkInput inputOf unary
  fun_prop

abbrev PreparedInput := Params × List Unit

def groupingInput (Δ : ℕ) (p : PreparedInput) : ExplicitCost.GroupingInput :=
  ((1,2*p.2.length), ((p.2, p.1.2.1), networkInput Δ p.1))

theorem groupingInput_polyT (Δ : ℕ) : PolyT (groupingInput Δ) := by
  have hn := networkInput_polyT Δ
  unfold groupingInput
  fun_prop

theorem networkInput_of {k D g : ℕ} (I : Instance k D) (b Δ : ℕ) (hg : 0 < g)
    (hpos : 0 < D) (hb : 1 ≤ b) (hD : D ≤ 2^b) (hΔ : 1 ≤ Δ)
    (hdeg : ∀ a, I.degree a ≤ Δ) :
    networkInput Δ (paramsOf I g b) =
      netInput (BitNetwork.data I ⟨0,hpos⟩ b (balanced hg))
        (Δ*b*(k/g+1)) ((k/g+1)+(k/g+1)*(k/g+1)+1) := by
  have h := ProviderGive.gives I b Δ hg hpos hb hD hΔ hdeg
  unfold networkInput
  have hgroup : groupCount (paramsOf I g b) = g := by simp [groupCount,paramsOf]
  rw [hgroup, h.P_eq,h.B_eq]
  exact inputOf_eq _ _ _ _ _ h.len_eq h.cap_eq

theorem groupingInput_of {k D g : ℕ} (I : Instance k D) (b Δ K : ℕ) (hg : 0 < g)
    (hpos : 0 < D) (hb : 1 ≤ b) (hD : D ≤ 2^b) (hΔ : 1 ≤ Δ)
    (hdeg : ∀ a, I.degree a ≤ Δ) :
    groupingInput Δ (paramsOf I g b,unary K) =
      ExplicitCost.groupingInput 1 (2*K) K
        (BitNetwork.data I ⟨0,hpos⟩ b (balanced hg))
        (Δ*b*(k/g+1)) ((k/g+1)+(k/g+1)*(k/g+1)+1) := by
  unfold groupingInput ExplicitCost.groupingInput ExplicitCost.dataInput
  rw [networkInput_of I b Δ hg hpos hb hD hΔ hdeg]
  simp [paramsOf,unary]

#print axioms networkInput_polyT
#print axioms groupingInput_polyT
#print axioms networkInput_of
#print axioms groupingInput_of

end CSPConsequence.DynamicPreparation
