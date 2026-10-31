import Downstream.DynamicPreparation
import Downstream.OracleElimination
import Downstream.UniformClique
import ExplicitCost.GroupingLemma

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! The concrete counting machine: finite input preparation, uniform grouping,
and all four query procedures are composed here. Anthropic's explicit grouping
cost theorem is imported directly; native simulation and final asymptotic
absorption are separate remaining obligations. -/

namespace CSPConsequence.ConcreteSolver

open Groundwork Printed QueryMachines ExplicitCost ProviderParameters
  ProviderMetadata NodeRefinement QuerySizes

def machine (Δ : ℕ) (E : QueryMachine TableQuery ℤ UniformClique.Input ℤ)
    (kf : UniformClique.U × UniformClique.U → Option UniformClique.U) :
    Stepped DynamicPreparation.PreparedInput ℤ :=
  Stepped.mapIn (fun p => (p.1,DynamicPreparation.groupingInput Δ p))
    (OracleElimination.machine Δ (groupingData E (UniformClique.arg kf)))

theorem machine_poly (Δ : ℕ) (E : QueryMachine TableQuery ℤ UniformClique.Input ℤ)
    (kf : UniformClique.U × UniformClique.U → Option UniformClique.U)
    (hE : E.PolyTimeSteps) (hKF : PolyT kf) : Nonempty (IsPolyT (machine Δ E kf)) := by
  obtain ⟨hM⟩ := OracleElimination.machine_poly Δ _ (UniformClique.grouping_poly E kf hE hKF)
  have hp := DynamicPreparation.groupingInput_polyT Δ
  exact ⟨IsPolyT.mapIn (M := OracleElimination.machine Δ (groupingData E (UniformClique.arg kf)))
    (by fun_prop)⟩

theorem explicit_cost : ∃ C₁ : ℕ,
    ∀ {k D g : ℕ} (I : Instance k D) (b Δ K : ℕ) (hg : 0 < g)
      (hpos : 0 < D) (hb : 1 ≤ b) (hD : D ≤ 2^b) (hΔ : 1 ≤ Δ)
      (hdeg : ∀ a, I.degree a ≤ Δ)
      (E : QueryMachine TableQuery ℤ UniformClique.Input ℤ)
      (kf : UniformClique.U × UniformClique.U → Option UniformClique.U)
      (𝒯 SE : ℕ),
    let N := BitNetwork.data I ⟨0,hpos⟩ b (balanced hg)
    let P := Δ*b*(k/g+1)
    let B := (k/g+1)+(k/g+1)*(k/g+1)+1
    let L := AppRunningTime.Lof K g ((1:ℝ)/(2*K)) P N.U
    let B' := AppRunningTime.B'of K g P B
    2 ≤ K → 2 ≤ g → g = 3*K^8 →
    SolvesCliques E (UniformClique.arg kf (unary K,unary L,unary B')) K L B' 𝒯 SE →
    ∃ T : ℕ,
      (machine Δ E kf).Runs (paramsOf I g b,unary K) (3*T)
        (size (paramsOf I g b) + (SE+(g*(P+B)+size (1,2*K))^C₁) +
          room (paramsOf I g b) g P B+4) (I.count : ℤ) ∧
      (T : ℝ) ≤ ((K:ℝ)^g + 𝒯*(2:ℝ)^(2*(g:ℝ)*P/K)) * ((g:ℝ)*(P+B))^C₁ := by
  obtain ⟨C₁,hC⟩ := groupingExplicit
  refine ⟨C₁, ?_⟩
  intro k D g I b Δ K hg hpos hb hD hΔ hdeg E kf 𝒯 SE N P B L B' hK hg2 hgK hEC
  have hn : N.Is P B := BitNetwork.is_valid I ⟨0,hpos⟩ hg hb hD hΔ hdeg
  have hz : (1:ℝ)/(↑(2*K):ℝ) = (1:ℝ)/(2*K) := by norm_cast
  have hc : AppRunningTime.Cases K g ((1:ℝ)/(↑(2*K):ℝ)) P N.c :=
    Or.inl ⟨hgK,hz⟩
  have hec : SolvesCliques E (UniformClique.arg kf
      (unary K,unary (AppRunningTime.Lof K g ((1:ℝ)/↑(2*K)) P N.U),unary B'))
      K (AppRunningTime.Lof K g ((1:ℝ)/↑(2*K)) P N.U) B' 𝒯 SE := by
    simpa only [hz] using hEC
  obtain ⟨T,hr,hT⟩ := hC _ E (UniformClique.arg kf) 1 (2*K) K g N P B 1 𝒯 SE
    hK hg2 (by omega) (by omega) hn (by omega)
    (by simpa only [Nat.cast_one] using hc) (by simpa only [Nat.cast_one] using hec)
  have hp := OracleElimination.csp_runs I b Δ hg hpos hb hD hΔ hdeg
    (groupingData E (UniformClique.arg kf)) (ExplicitCost.groupingInput 1 (2*K) K N P B)
    N.value T (SE+(g*(P+B)+size (1,2*K))^C₁) hr
  have hin := DynamicPreparation.groupingInput_of I b Δ K hg hpos hb hD hΔ hdeg
  have hout : N.value = (I.count:ℤ) := BitNetwork.value_eq_count I ⟨0,hpos⟩ b (balanced hg) hD
  refine ⟨T,?_,?_⟩
  · unfold machine
    apply Stepped.mapIn_runs
    rw [hin]
    rw [hout] at hp
    exact hp
  · simpa only [Nat.cast_one,mul_one] using hT

#print axioms machine_poly
#print axioms explicit_cost

end CSPConsequence.ConcreteSolver
