import Downstream.ProviderGive
import Printed.GroupingProcs
import Printed.HandOver

set_option autoImplicit false

/-! A single concrete machine replaces all legal network queries by the CSP
provider. Imported composition lemmas are from Anthropic's Printed.GroupingProcs
and QueryMachines.Runs/Poly; no oracle is retained by the resulting machine. -/

namespace CSPConsequence.OracleElimination

open Groundwork Printed QueryMachines QueryMachines.QueryMachine
  ProviderParameters ProviderMetadata NodeRefinement QuerySizes

variable {α β : Type}

def machine (Δ : ℕ) (M : QueryMachine NetQuery ℤ α β) : Stepped (Params × α) β :=
  M.plug (answerOf (procs Δ))

theorem machine_poly [Enc α] [Enc β] (Δ : ℕ)
    (M : QueryMachine NetQuery ℤ α β) (hM : M.PolyTimeSteps) :
    Nonempty (IsPolyT (machine Δ M)) := by
  obtain ⟨hM⟩ := hM
  have hk := procs_keeps Δ
  obtain ⟨hA⟩ := answerOf_poly (procs Δ) hk.mem hk.W hk.Ψ hk.f
  exact ⟨QueryMachine.plug_isPolyT M (answerOf (procs Δ))⟩

theorem runs {g : ℕ} (Δ : ℕ) (M : QueryMachine NetQuery ℤ α β)
    (c : Params) (N : Eight.SecNetworks.Net g) (P B S₀ : ℕ)
    (hgive : (procs Δ).Give c N P B 1 S₀)
    (a : α) (v : β) (T S : ℕ)
    (h : M.Within (netOracle N) unitCost a T S v) :
    (machine Δ M).Runs (c,a) (3*T) (size c+S+S₀+4) v := by
  obtain ⟨own,L,hr,hle⟩ := h
  have hp := stPlug NetQuery ℤ Params α β M (answerOf (procs Δ))
    (netOracle N) c a own S (S₀+3) L v (fun _ => 1) hr
    (fun x _ w hw => answerOf_runs hgive hw)
  rw [sum_map_unitCost] at hle
  rw [sum_map_const] at hp
  exact hp.mono (by omega) (by omega)

theorem csp_runs {k D g : ℕ} (I : Instance k D) (b Δ : ℕ) (hg : 0 < g)
    (hpos : 0 < D) (hb : 1 ≤ b) (hD : D ≤ 2^b) (hΔ : 1 ≤ Δ)
    (hdeg : ∀ a, I.degree a ≤ Δ)
    (M : QueryMachine NetQuery ℤ α β) (a : α) (v : β) (T S : ℕ)
    (h : M.Within (netOracle (BitNetwork.data I ⟨0,hpos⟩ b (balanced hg)))
      unitCost a T S v) :
    (machine Δ M).Runs (paramsOf I g b,a) (3*T)
      (size (paramsOf I g b)+S+
        room (paramsOf I g b) g (Δ*b*(k/g+1)) ((k/g+1)+(k/g+1)*(k/g+1)+1)+4) v :=
  runs Δ M _ _ _ _ _ (ProviderGive.gives I b Δ hg hpos hb hD hΔ hdeg) a v T S h

#print axioms machine_poly
#print axioms runs
#print axioms csp_runs

end CSPConsequence.OracleElimination
