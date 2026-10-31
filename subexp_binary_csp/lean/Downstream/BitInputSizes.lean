import Downstream.BitInputRoundtrip

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! Relate the actual typed context/state size to the canonical bit input.
These bounds use complete rectangular tables; sparse normalization is separate. -/
namespace CSPConsequence.BitInputCodec
open Groundwork Printed FiniteInput ProviderParameters DynamicPreparation NodeRefinement

theorem paramsOf_size {k D : Nat} (I : Instance k D) (g b : Nat) :
    size (paramsOf I g b) = 2*k^2*D^2+2*k^2*D+4*k^2+6*k+2*D+2*g+2*b+6 := by
  simp only [paramsOf,tabulate,size_prod,size_list,List.map_ofFn,Function.comp_def,
    size_bool,size_unit,List.sum_ofFn,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    smul_eq_mul,List.map_replicate,List.sum_replicate]
  ring

theorem prepared_size {k D : Nat} (I : Instance k D) (g b K : Nat) :
    size (paramsOf I g b,unary K) =
      2*k^2*D^2+2*k^2*D+4*k^2+6*k+2*D+2*g+2*b+2*K+7 := by
  rw [size_prod,paramsOf_size]
  simp only [unary,size_list,List.map_replicate,size_unit,List.sum_replicate,smul_eq_mul]
  ring

theorem prepared_size_le_encode {k D : Nat} (I : Instance k D) (g b K : Nat) :
    size (paramsOf I g b,unary K) ≤ 10*(encode (paramsOf I g b,unary K)).length := by
  rw [prepared_size,encode_paramsOf_length]
  have hD : D ≤ D^2 := by
    cases D with
    | zero => simp
    | succ D => nlinarith
  have hmix := Nat.mul_le_mul_left (k^2) hD
  nlinarith

theorem paramsOf_size_le_encode {k D : Nat} (I : Instance k D) (g b K : Nat) :
    size (paramsOf I g b) ≤ 10*(encode (paramsOf I g b,unary K)).length := by
  have hp := prepared_size_le_encode I g b K
  rw [size_prod] at hp
  change size (paramsOf I g b)+size (unary K) ≤
    10*(encode (paramsOf I g b,unary K)).length at hp
  omega

#print axioms paramsOf_size
#print axioms prepared_size_le_encode
#print axioms paramsOf_size_le_encode
end CSPConsequence.BitInputCodec
