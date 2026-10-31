import Downstream.LabelRefinement
import Downstream.TableRefinement

set_option autoImplicit false

/-! Correctness of the concrete factor query against the actual bit network.
No label-table oracle is assumed; all data are read from the finite input.
-/

namespace CSPConsequence.FactorRefinement

open Finset Groundwork DomainCodec FiniteInput ProviderParameters NodeRefinement
  ProviderTables PairDecoder ProviderLabels LabelRefinement

def term (p : InteractionInput) (a v : ℕ) : Bool :=
  if edgeAt p.1.1 a v then
    let z := nodeValue (p.1,p.2.1.1,p.2.2.1,a)
    let key := if p.2.1.1 < p.2.1.2 then (a,v) else (v,a)
    let y := labelValue (p.1,p.2.1,p.2.2.2,key)
    if a < v then decide (z = y) else relationAt p.1.1 v a y z
  else true

theorem factorBit_eq (p : InteractionInput) : factorBit p =
    if labelLegal (p.1,p.2.1,p.2.2.2) then
      (nodeMembers (p.1,p.2.1.1)).all fun a =>
        (nodeMembers (p.1,p.2.1.2)).all fun v => term p a v
    else false := rfl

variable {k D g : ℕ} (I : Instance k D) (b : ℕ) (hg : 0 < g) (hD : 0 < D)

theorem originalFactor_of (G H : Fin g) (w θ : List Bool) (a v : Fin k) :
    (I.network ⟨0,hD⟩ b).f a v
      (decode ⟨0,hD⟩ b (EncodedSettings.members (balanced hg) G) w a)
      (decode ⟨0,hD⟩ b (BitNetwork.labels I (balanced hg) G H) θ
        (if G < H then (a,v) else (v,a))) =
      if term (paramsOf I g b,(G.val,H.val),(w,θ)) a.val v.val then (1 : ℤ) else 0 := by
  have hp : (paramsOf I g b).1 = tabulate I := rfl
  have hreadAV : labelValue (paramsOf I g b,(G.val,H.val),θ,(a.val,v.val)) =
      (decode ⟨0,hD⟩ b (BitNetwork.labels I (balanced hg) G H) θ (a,v)).val :=
    labelValue_of I b hg hD G H θ (a,v)
  have hreadVA : labelValue (paramsOf I g b,(G.val,H.val),θ,(v.val,a.val)) =
      (decode ⟨0,hD⟩ b (BitNetwork.labels I (balanced hg) G H) θ (v,a)).val :=
    labelValue_of I b hg hD G H θ (v,a)
  by_cases hgroup : G < H <;> by_cases hvertex : a < v <;>
    by_cases hedge : I.edge a v = true <;>
    simp [term, Instance.network, hp, hedge, hgroup, hvertex,
      nodeValue_of I b hg hD G w,
      hreadAV, hreadVA, edgeAt_tabulate, relationAt_tabulate, Fin.ext_iff] <;>
    split_ifs <;> rfl

theorem factorValue_of (G H : Fin g) (w θ : List Bool) :
    factorValue (paramsOf I g b,(G.val,H.val),(w,θ)) =
      (BitNetwork.data I ⟨0,hD⟩ b (balanced hg)).f G H w θ := by
  let χ := balanced (k := k) hg
  let raw := (paramsOf I g b,(G.val,H.val),(w,θ))
  have hbit : ((nodeMembers (paramsOf I g b,G.val)).all fun a =>
      (nodeMembers (paramsOf I g b,H.val)).all fun v => term raw a v) = true ↔
      ∀ p ∈ univ.filter (fun p : Fin k × Fin k => χ p.1 = G ∧ χ p.2 = H),
        term raw p.1.val p.2.val = true := by
    simp only [nodeMembers_of I b hg G, nodeMembers_of I b hg H,
      List.all_map, List.all_eq_true, EncodedSettings.mem_members,
      mem_filter, mem_univ, true_and, Prod.forall, and_imp, Function.comp_def]
    constructor
    · intro h a v ha hv
      exact h a ha v hv
    · intro h a ha v hv
      exact h a v ha hv
  unfold factorValue
  rw [factorBit_eq, labelLegal_of I b hg G H θ]
  change (if (if BitNetwork.legalLabel (D := D) b (BitNetwork.labels I χ G H) θ then
      (nodeMembers (paramsOf I g b,G.val)).all fun a =>
        (nodeMembers (paramsOf I g b,H.val)).all fun v => term raw a v
      else false) then (1 : ℤ) else 0) =
    if BitNetwork.legalLabel (D := D) b (BitNetwork.labels I χ G H) θ then
      ∏ p ∈ univ.filter (fun p : Fin k × Fin k => χ p.1 = G ∧ χ p.2 = H),
        (I.network ⟨0,hD⟩ b).f p.1 p.2
          (decode ⟨0,hD⟩ b (EncodedSettings.members χ G) w p.1)
          (decode ⟨0,hD⟩ b (BitNetwork.labels I χ G H) θ
            (if G < H then p else p.swap))
    else 0
  by_cases hlegal : BitNetwork.legalLabel (D := D) b (BitNetwork.labels I χ G H) θ = true
  · simp only [if_pos hlegal]
    have ht (p : Fin k × Fin k) :
        (I.network ⟨0,hD⟩ b).f p.1 p.2
          (decode ⟨0,hD⟩ b (EncodedSettings.members χ G) w p.1)
          (decode ⟨0,hD⟩ b (BitNetwork.labels I χ G H) θ
            (if G < H then p else p.swap)) =
          if term raw p.1.val p.2.val then (1 : ℤ) else 0 :=
      originalFactor_of I b hg hD G H w θ p.1 p.2
    simp_rw [ht]
    rw [Finset.prod_boole]
    simp only [hbit]
    split_ifs <;> rfl
  · simp [hlegal]

def factorMachine : Stepped InteractionInput ℤ := Stepped.ofFun factorValue

@[instance_reducible] def factorMachine_polyT : IsPolyT factorMachine :=
  IsPolyT.ofFun factorValue_polyT

theorem factorMachine_correct (G H : Fin g) (w θ : List Bool) :
    factorMachine.Runs (paramsOf I g b,(G.val,H.val),(w,θ)) 1
      (max (size (paramsOf I g b,(G.val,H.val),(w,θ)))
        (size ((BitNetwork.data I ⟨0,hD⟩ b (balanced hg)).f G H w θ)) + 1)
      ((BitNetwork.data I ⟨0,hD⟩ b (balanced hg)).f G H w θ) := by
  simpa only [factorMachine, factorValue_of I b hg hD G H w θ] using
    Stepped.ofFun_runs factorValue (paramsOf I g b,(G.val,H.val),(w,θ))

#print axioms factorValue_of
#print axioms factorMachine_polyT
#print axioms factorMachine_correct

end CSPConsequence.FactorRefinement
