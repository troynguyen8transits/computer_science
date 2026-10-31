import Downstream.BruteCSPSemantics
import ToTuring.Poly.Range
import ToTuring.Poly.Comb
import StepMachines.Prog.SideBasics

set_option autoImplicit false
set_option maxHeartbeats 3000000

/-! A uniform fallback on explicit CSP tables, including the empty domain.
Every leaf and loop part has an actual polynomial-time TM certificate.
The abstract enumeration runs for at most 2*2^(b*k) steps with polynomial
state size. Native simulation is available through BitInputMachine.machine.
This fallback has no degree restriction or clique-algorithm assumption. -/
namespace CSPConsequence.BruteCSP
open Finset Groundwork FiniteInput ProviderParameters NodeRefinement
open Groundwork.Stepped

def leafMachine : Stepped (Params × Nat) Int := ofFun leaf
def enumerate : Stepped Params Int := sumRange bound leafMachine

def leafMachine_poly : IsPolyT leafMachine := IsPolyT.ofFun leaf_polyT
def enumerate_poly : IsPolyT enumerate := by
  letI := leafMachine_poly
  unfold enumerate
  exact IsPolyT.sumRange bound_polyT

theorem enumerate_runs (p : Params) :
    enumerate.Runs p (2*bound p) (2*size p+3*width p+9)
      (∑ y ∈ range (bound p), leaf (p,y)) := by
  let Sm := size p+width p+4
  have hleaf : ∀ y < bound p, leafMachine.Runs (p,y) 1 Sm (leaf (p,y)) := by
    intro y hy
    have hsize : Nat.size y ≤ width p := Nat.size_le.mpr hy
    have hv := leaf_size (p,y)
    have hh := ofFun_runs leaf (p,y)
    have hi : size (p,y) ≤ size p+width p+1 := by
      change size p+(Nat.size y+1) ≤ size p+width p+1
      omega
    have hm : max (size (p,y)) (size (leaf (p,y)))+1 ≤ Sm := by
      dsimp only [Sm]
      omega
    exact hh.mono le_rfl hm
  have hh := sumRange_runs (N := bound) (M := leafMachine) (a := p)
    (fun _ => 1) (fun y => leaf (p,y)) 1 Sm hleaf (fun y hy => leaf_natAbs (p,y))
  change (sumRange bound leafMachine).Runs p _ _ _
  apply hh.mono
  · simp only [sum_const,card_range,smul_eq_mul]
    omega
  · simp only [bound,mul_one,size_nat,Nat.size_pow]
    dsimp [Sm]
    omega

theorem enumerate_correct {k D : Nat} (I : Instance k D) (g b : Nat)
    (hpos : 0 < D) (hD : D ≤ 2^b) :
    enumerate.Runs (paramsOf I g b) (2*bound (paramsOf I g b))
      (2*size (paramsOf I g b)+3*width (paramsOf I g b)+9) (I.count : Int) := by
  have h := enumerate_runs (paramsOf I g b)
  rwa [sum_leaf_eq_count I g b hpos hD] at h

def emptyValue (p : Params) : Int := if vertices p.1 = 0 then 1 else 0
def machine : Stepped Params Int :=
  ite (fun p => decide (domain p.1 = 0)) (ofFun emptyValue) enumerate

@[fun_prop] theorem emptyValue_polyT : PolyT emptyValue := by unfold emptyValue vertices; fun_prop

def machine_poly : IsPolyT machine := by
  letI := enumerate_poly
  letI : IsPolyT (ofFun emptyValue) := IsPolyT.ofFun emptyValue_polyT
  unfold machine
  exact IsPolyT.ite (by unfold domain; fun_prop)

/-- All domains, including D=0, and all graph degrees. The supplied block width
must represent the domain; the outer preparation computes such a width. -/
theorem machine_correct {k D : Nat} (I : Instance k D) (g b : Nat) (hD : D ≤ 2^b) :
    machine.Runs (paramsOf I g b) (2*bound (paramsOf I g b))
      (2*size (paramsOf I g b)+3*width (paramsOf I g b)+12) (I.count : Int) := by
  by_cases hpos : 0 < D
  · have hh := ite_runs_false
      (p := fun p : Params => decide (domain p.1 = 0)) (M := ofFun emptyValue)
      (by simp [paramsOf,domain_tabulate,Nat.ne_of_gt hpos])
      (enumerate_correct I g b hpos hD)
    apply hh.mono (by omega)
    omega
  · have hz : D = 0 := Nat.eq_zero_of_not_pos hpos
    subst D
    have hv : emptyValue (paramsOf I g b) = (I.count : Int) := by
      rw [count_empty_domain]
      simp only [emptyValue,paramsOf,vertices_tabulate]
      split_ifs <;> rfl
    have hs : size (emptyValue (paramsOf I g b)) ≤ 2 := by
      unfold emptyValue
      split_ifs <;> decide
    have hh := ite_runs_true
      (p := fun p : Params => decide (domain p.1 = 0)) (N := enumerate)
      (by simp [paramsOf,domain_tabulate]) (ofFun_runs emptyValue (paramsOf I g b))
    rw [hv] at hh
    apply hh.mono
    · have hp : 1 ≤ bound (paramsOf I g b) := Nat.one_le_two_pow
      omega
    · rw [hv] at hs
      omega

#print axioms enumerate_poly
#print axioms enumerate_correct
#print axioms machine_poly
#print axioms machine_correct
end CSPConsequence.BruteCSP
