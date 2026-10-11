import LehnerEdges
import Lean.Util.CollectAxioms

/-! Check all declarations by their originating project module. This includes
helper definitions and generated declarations, and follows transitive proof
and type dependencies into both external libraries and Mathlib. -/

open Lean in
run_cmd do
  let env ← getEnv
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (decl, _) in env.constants.toList do
    if let some modIdx := env.getModuleIdxFor? decl then
      let origin := env.header.moduleNames[modIdx.toNat]!
      if (`LehnerEdges).isPrefixOf origin then
        checked := checked + 1
        for axiomName in (← Lean.collectAxioms decl) do
          if !permitted.contains axiomName then
            throwError "Axiom audit failed: {decl} depends on {axiomName}"
  if checked == 0 then
    throwError "Axiom audit selected no declarations"
  logInfo m!"PASS: recursively audited {checked} project declarations; only propext, Classical.choice, Quot.sound permitted."

#print axioms LehnerEdges.two_fiber_stiefel_increment
#print axioms LehnerEdges.traceNorm_eq_sup_contractions
#print axioms LehnerEdges.weighted_trace_amgm
#print axioms LehnerEdges.densityFunctional_le_rhoPlus
#print axioms LehnerEdges.rhoMinus_eq_neg_rhoPlus
#print axioms LehnerEdges.rhoMinus_le_densityFunctional
#print axioms LehnerEdges.pointwise_comparison_bound
#print axioms LehnerEdges.finite_density_stiefel_comparison
#print axioms LehnerEdges.finite_spectral_process_concentration
#print axioms LehnerEdges.gue_pair_law
#print axioms LehnerEdges.complex_gaussian_matrix_norm_concentration
#print axioms LehnerEdges.finite_block_process_bound
#print axioms LehnerEdges.opNorm_eq_max_edges
#print axioms sudakov_fernique_drift
#print axioms LogSobolev.gaussian_hasSubgaussianMGF
#print axioms LehnerEdges.purification_increment
#print axioms LehnerEdges.separable_linear_gaussian_comparison
#print axioms LehnerEdges.full_purification_comparison
#print axioms LehnerEdges.full_signed_purification_comparison
#print axioms LehnerEdges.stdGaussian_integral_norm_contraction_le
#print axioms LehnerEdges.real_gaussian_matrix_norm_mean_le
#print axioms LehnerEdges.stdGaussian_integral_positive_centered_le_one
#print axioms LehnerEdges.complexGaussianMatrix_norm_le_realStack
#print axioms LehnerEdges.gaussian_wishart_positive_excess_le_three
#print axioms LehnerEdges.gaussian_purification_edge_bound_six
#print axioms LehnerEdges.opNorm_eq_signed_rayleigh_sup
