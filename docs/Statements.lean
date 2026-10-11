import LehnerEdges

-- Exact exported theorem types, including implicit arguments.
set_option format.width 110
set_option pp.universes false

-- LehnerEdges/BlockComparison.lean
#check @LehnerEdges.blockRow_mul_blockColumn
#check @LehnerEdges.blockRow_mul_adjoint
#check @LehnerEdges.compressed_block_energy
#check @LehnerEdges.compressed_block_traceNorm
#check @LehnerEdges.pointwise_comparison_bound

-- LehnerEdges/DensityBounds.lean
#check @LehnerEdges.frobeniusSq_sqrt
#check @LehnerEdges.density_trace_le_norm
#check @LehnerEdges.squareFunction_posSemidef
#check @LehnerEdges.trace_covariance
#check @LehnerEdges.traceNorm_sqrt_mul_sqrt
#check @LehnerEdges.fidelity_bound
#check @LehnerEdges.density_energy_bound
#check @LehnerEdges.comparison_block_bound

-- LehnerEdges/FiniteBlockBound.lean
#check @LehnerEdges.stiefel_norm_le_one
#check @LehnerEdges.stiefel_pair_le_traceNorm
#check @LehnerEdges.finite_block_process_bound

-- LehnerEdges/GaussianComparison.lean
#check @LehnerEdges.processMap_apply
#check @LehnerEdges.linear_gaussian_comparison
#check @LehnerEdges.familyVector_norm_sq
#check @LehnerEdges.familyVector_sub
#check @LehnerEdges.coefficient_increment
#check @LehnerEdges.finite_density_stiefel_comparison

-- LehnerEdges/GaussianConcentration.lean
#check @LehnerEdges.standardGaussian_eq_stdGaussian
#check @LehnerEdges.stdGaussian_integrable_of_lipschitz
#check @LehnerEdges.stdGaussian_hasSubgaussianMGF
#check @LehnerEdges.stdGaussian_measure_ge_le

-- LehnerEdges/GaussianMatrices.lean
#check @LehnerEdges.euclidean_real_inner_eq_re
#check @LehnerEdges.matrixVector_matrixOfVector
#check @LehnerEdges.gueProjection_hermitian
#check @LehnerEdges.gueProjection_pair
#check @LehnerEdges.gue_pair_eq_innerSL
#check @LehnerEdges.gue_variance_pair
#check @LehnerEdges.gue_mean_pair
#check @LehnerEdges.gue_pair_law
#check @LehnerEdges.matrixOfVector_norm_lipschitz
#check @LehnerEdges.gaussian_matrix_norm_concentration

-- LehnerEdges/LeftVariational.lean
#check @LehnerEdges.posDef_inv_neg
#check @LehnerEdges.lehnerMatrix_neg_parameter
#check @LehnerEdges.lambdaMin_lehner_neg
#check @LehnerEdges.rhoMinus_eq_neg_rhoPlus
#check @LehnerEdges.rhoStar_eq_max_rhoPlus
#check @LehnerEdges.rhoMinus_le_densityFunctional

-- LehnerEdges/MatrixBasics.lean
#check @LehnerEdges.covariance_one
#check @LehnerEdges.compressed_posSemidef
#check @LehnerEdges.energy_eq_sum_sq
#check @LehnerEdges.covariance_posSemidef
#check @LehnerEdges.energy_posSemidef
#check @LehnerEdges.frobeniusSq_nonneg
#check @LehnerEdges.re_trace_mul_nonneg
#check @LehnerEdges.re_trace_conjTranspose
#check @LehnerEdges.frobeniusSq_sub
#check @LehnerEdges.frobeniusSq_eq_sum
#check @LehnerEdges.matrixVector_norm_sq
#check @LehnerEdges.matrixVector_inner
#check @LehnerEdges.trace_cauchy_schwarz_sq

-- LehnerEdges/ProcessLipschitz.lean
#check @LehnerEdges.sum_frobeniusSq_mul
#check @LehnerEdges.sum_compressed_frobeniusSq_le
#check @LehnerEdges.gueCoefficient_norm_le
#check @LehnerEdges.finite_process_lipschitz
#check @LehnerEdges.finite_spectral_process_lipschitz
#check @LehnerEdges.finite_spectral_process_concentration

-- LehnerEdges/Stiefel.lean
#check @LehnerEdges.frobeniusSq_mul_coisometry
#check @LehnerEdges.frobeniusSq_coisometry_adjoint_mul
#check @LehnerEdges.re_trace_cross
#check @LehnerEdges.positive_cross_bound
#check @LehnerEdges.stiefel_pair_right
#check @LehnerEdges.stiefel_pair_compressed
#check @LehnerEdges.two_fiber_stiefel_increment
#check @LehnerEdges.compressed_increment

-- LehnerEdges/TraceAMGM.lean
#check @LehnerEdges.trace_amgm
#check @LehnerEdges.weighted_trace_amgm

-- LehnerEdges/TraceDuality.lean
#check @LehnerEdges.polarContraction_factorization
#check @LehnerEdges.abs_re_trace_pos_mul_le
#check @LehnerEdges.abs_frobeniusPair_le_traceNorm
#check @LehnerEdges.polarContraction_pair
#check @LehnerEdges.traceNorm_eq_sup_contractions

-- LehnerEdges/TraceNorm.lean
#check @LehnerEdges.re_trace_mono
#check @LehnerEdges.traceNorm_nonneg
#check @LehnerEdges.mul_adjoint_le
#check @LehnerEdges.adjoint_mul_le
#check @LehnerEdges.conjugate_mono
#check @LehnerEdges.sqrt_smul_sq
#check @LehnerEdges.traceNorm_mul_le
#check @LehnerEdges.frobeniusSq_adjoint
#check @LehnerEdges.frobeniusSq_mul_le
#check @LehnerEdges.opNorm_le_frobenius
#check @LehnerEdges.opNorm_sq_le_frobeniusSq
#check @LehnerEdges.inverseSqrt_hermitian
#check @LehnerEdges.inverseSqrt_mul
#check @LehnerEdges.polarContraction_mul_adjoint
#check @LehnerEdges.sqrt_eq_real_cfc
#check @LehnerEdges.polarContraction_norm_le
#check @LehnerEdges.traceNorm_mul_le_frobenius

-- LehnerEdges/Variational.lean
#check @LehnerEdges.lambdaMax_le_iff
#check @LehnerEdges.le_lambdaMin_iff
#check @LehnerEdges.density_trace_le_lambdaMax
#check @LehnerEdges.lambdaMax_sub_le
#check @LehnerEdges.abs_lambdaMax_sub_le
#check @LehnerEdges.lambdaMax_neg
#check @LehnerEdges.lambdaMin_neg
#check @LehnerEdges.abs_lambdaMin_sub_le
#check @LehnerEdges.opNorm_eq_max_edges
#check @LehnerEdges.lehnerMatrix_hermitian
#check @LehnerEdges.densityFunctional_le_lehnerMatrix
#check @LehnerEdges.densityFunctional_le_rhoPlus

-- LehnerEdges/Wishart.lean
#check @LehnerEdges.complexGaussianMatrix_norm_lipschitz
#check @LehnerEdges.complex_gaussian_matrix_norm_concentration
#check @LehnerEdges.wishartMatrix_posSemidef
#check @LehnerEdges.wishart_sqrt_norm
