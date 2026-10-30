# Lean verification of the qubit PPT manuscript

The full qubit-anywhere PPT-composition theorem is proved in Lean.
For complex-linear maps S from M_m to M_n and T from M_n to M_d, if
both maps are PPT and at least one of m, n, d equals two, then T composed
with S is entanglement breaking. The other dimensions are arbitrary and
independent. There are no trace-preserving, unital, or rank assumptions.
The result includes zero maps and singular marginals.

For two PPT operators on systems A:B and C:D, every positive joint
measurement effect on B:C produces a separable conditional operator on
A:D whenever any of the four systems is a qubit. The intermediate
systems may have different dimensions, and zero effects are included.

Every composition of two PPT maps and its Hilbert–Schmidt adjoint are
2-entanglement breaking in arbitrary dimensions. Every input of Schmidt
number at most two therefore has separable output under the composition.
For arbitrary finite dimensions, every PPT pair decreases the Schmidt-number
bound by one down to one. Arbitrary-length chains satisfy the Schmidt-number
iteration and the rectangular endpoint bound in the manuscript. For a PPT
self-map on M_d with d ≥ 2, the entanglement-breaking index is at most 2(d-1).
A measurement effect of Schmidt number at most two also produces separable
swapping output for arbitrary local dimensions.

These statements concern the [manuscript at commit 06b9b4e](https://github.com/GLiuax/ppt-composition-conjecture/blob/06b9b4ed69a5074148a5a9b7deab6e8b2f34ec82/A%20Qubit%20Forbids%20Entanglement%20Swapping%20between%20PPT%20Links.tex).
The source examined on 29 October 2026 has SHA-256 digest
e8fb279e8c65cc742185806cbc208e0c6a1332a5549a8ae376b3f6ffd6ce7bb3.

## Precise formal statements

The complete main theorem and middle-qubit branch are in
[MiddleQubit.lean](PPTQubit/MiddleQubit.lean). The endpoint results and
2-EB consequence are in [Endpoints.lean](PPTQubit/Endpoints.lean). The
measurement statement is in [Swapping.lean](PPTQubit/Swapping.lean).

| Theorem | Verified conclusion |
| --- | --- |
| swapping_positive_effect_separable | Every positive joint measurement on the intermediate systems yields a separable conditional operator whenever any of the four original systems is a qubit. |
| swappingOutcome_partial_trace | The indexed outcome is exactly the partial trace of the product of the two input operators and the lifted measurement effect. |
| ppt_pair_adjoint_two_eb | A PPT pair and its Hilbert–Schmidt adjoint are both 2-EB. |
| ppt_pair_schmidt_number_two | Every Schmidt-number-at-most-two input becomes separable after any two PPT maps. |
| ppt_pair_numeric_easy_ranges | An arbitrary PPT pair decreases Schmidt number by one in the ranges SN at most two or output dimension below the input SN. |
| pt_invariant_schmidt_bound | A positive operator invariant under partial transpose on a reference of dimension at least two has Schmidt number at most one below that dimension. |
| maximal_block_structure_rank_one | The maximal block-structure conclusion holds for positive operators of matrix rank at most one. |
| kpositive_iff_choi_kblock | For Hermitian Choi operators, k-positivity is equivalent to nonnegativity on Schmidt-rank-at-most-k vectors. |
| kblock_iff_schmidt_pairing_nonnegative | k-block positivity is equivalent to nonnegative trace pairing with every positive operator of Schmidt number at most k. |
| choi_decomposition_list | A k-positive map with Hermitian Choi matrix admits the iterated completely positive pivot decomposition, including singular pivots. |
| schmidt_witness_of_closed_cone | A closed Schmidt-number cone yields a Hermitian k-block-positive separating witness. |
| block_structure_from_schmidt_witness | The maximal-Schmidt principal-block criterion follows from Schmidt witness completeness. |
| schmidt_rank_closed | Schmidt-rank-at-most-k vectors form a closed set in all finite dimensions. |
| schmidt_unit_projectors_compact | Unit-norm Schmidt-rank-at-most-k pure projectors form a compact set. |
| schmidt_number_normalized_expansion | Every bounded-Schmidt-number operator has a finite nonnegative expansion using unit-norm bounded-rank projectors, with zero terms allowed. |
| schmidtCone_zero_closed | The Schmidt-number-zero cone is the singleton zero and is closed. |
| schmidtCone_closed | Every finite-dimensional Schmidt-number cone is closed. |
| maximal_schmidt_block_criterion | Separable two-dimensional principal blocks imply Schmidt number at most n-1 under the stated dimension hypotheses. |
| principal_block_structure | The general principal-block Schmidt-number structure, including every admissible block size. |
| swapping_schmidt_number_two_effect | Every effect of Schmidt number at most two produces separable swapping output for arbitrary local dimensions. |
| PPTChain.entanglement_breaking_rectangular | A chain of N PPT maps is EB when 2(min(p,q)-1) ≤ N, including odd N and arbitrary intermediate dimensions. |
| ppt_pair_trimming | Every pair of PPT maps decreases Schmidt number by one down to one. |
| PPTPairChain.schmidt_iteration | A chain of l arbitrary PPT pairs decreases an input bound k to max(k-l,1). |
| PPTPairChain.entanglement_breaking | Such a chain is entanglement breaking when its input dimension p satisfies p ≤ l+1. |
| PPTPairChain.ancilla_bound | A chain of l PPT pairs is (l+1)-entanglement breaking. |
| ppt_power_entanglement_breaking | A PPT map on M_d has an entanglement-breaking 2(d-1)-th power for d ≥ 2. |
| ppt_index_bound | The entanglement-breaking index is at most 2(d-1) for d ≥ 2. |
| completely_positive_preserves_schmidt_number | A completely positive map acting locally does not increase the Schmidt-number bound. |
| ppt_qubit_index_bound | A PPT map on M_2 has an entanglement-breaking index at most two. |
| TrimChain.schmidt_number_decay | The numerical decay formula for a chain of maps, each satisfying the explicit SchmidtTrimming premise. |
| square_index_bound_of_trimming | The index bound 2(d-1), conditional on the explicit SchmidtTrimming premise for the squared map. |
| ppt_composition_qubit_anywhere | A two-map PPT composition is entanglement breaking if its input, intermediate, or output dimension equals two. |
| ppt_composition_qubit_middle | The intermediate-qubit case, with both endpoints unrestricted. |
| qubitLink_ppt_separable | Two arbitrary PPT operators sharing a qubit have a separable link product. |
| qubit_ppt_state_endpoint | A PPT map sends every qubit-reference PPT operator to a separable operator. |
| ppt_composition_qubit_input | A two-map PPT composition with input dimension two is entanglement breaking. |
| ppt_composition_qubit_output | A two-map PPT composition with output dimension two is entanglement breaking. |
| ppt_composition_endpoint | Either endpoint dimension equal to two suffices. |
| ppt_composition_two_entanglement_breaking | Every two-map PPT composition is 2-EB, with arbitrary map dimensions. |

All matrix maps are complex-linear. IsPPTMap is defined by positivity of the
Choi matrix and its partial transpose. The theorem
ppt_map_iff_complete_ppt proves that this is equivalent to producing PPT
outputs from every positive bipartite input in every finite ancillary
dimension. The formal convention transposes the first factor. Full
transposition and factor exchange identities handle the other convention.

IsSeparable means a finite sum of positive product rank-one operators,
without trace normalization. IsEntanglementBreaking quantifies over every
finite ancillary dimension and every positive bipartite input. It is not
defined merely as a condition on the Choi matrix. The equivalence with
Choi separability is proved in entanglementBreaking_iff_choi_separable.
IsTwoEntanglementBreaking uses the same input-output definition with a
qubit reference. Complete positivity is a separate predicate, proved for the
PPT maps to which the 2-EB conclusions apply. The audit also proves the
PPT-map definition equivalent to complete positivity of both T and its
output-transposed map.

## Proof route and checked ingredients

The formal endpoint proof constructs separable decompositions through the
auxiliary qutrit operator.

1. Every qubit PPT operator R has a positive auxiliary Q fixed by qutrit
   partial transpose, with R recovered by the fixed local congruence V.
   The construction includes singular blocks through a positive generalized
   inverse and proved support identities.
2. Q has exactly rank Q nonzero pure terms, each supported in a real
   two-dimensional qutrit subspace. Explicit injective real 3-by-2 matrices
   give the restrictions and commute with partial-transpose symmetrization.
3. Applying a PPT map to the other factor gives a PPT operator for each
   restricted qubit term. Its symmetrization is positive and fixed by
   qubit partial transpose, hence separable by the proved product-state
   decomposition theorem. Local real congruences and summation reconstruct
   the full separable output. Congruence by V recovers the qubit endpoint.
4. Choi composition gives the input endpoint. A proved transpose-dual
   composition identity and factor exchange give the output endpoint.
   Choi separability then gives entanglement breaking for every reference
   dimension. Applying the state theorem after one PPT map gives 2-EB.

This is a direct separable-decomposition proof of the endpoint result.
The manuscript's standalone bilinear-positivity lemma and its full
PPT/decomposable-cone duality argument have not been separately encoded.
Neither is assumed by the endpoint theorems.

The middle-qubit proof implements the manuscript's independent Pauli and
Hermitian row-contraction argument directly on Choi blocks.

1. Spectral calculus proves positivity of $A-A^2$ for positive
   contractions, constructs Hermitian absolute parts, and supplies square
   roots and generalized inverse square roots of arbitrary positive
   marginals.
2. A qubit PPT operator is normalized on the marginal support. A positive
   product term completes the kernel to give identity marginal on the full
   space. The inverse local filter annihilates this extra term and restores
   the original operator exactly, including the zero-marginal case.
3. The qubit reduction identity gives positivity of I - R for a normalized
   PPT operator R. An exact Pauli block identity then proves the Hermitian
   row-contraction bound.
4. The row-contraction operator has an explicit separable decomposition.
   In particular, each squared tensor difference is a positive weighted
   sum of product spectral projectors. The Choi link product is one half
   of this row-contraction operator, with the second Pauli component's sign
   accounted for explicitly.
5. Local filters recover the arbitrary PPT link product. The matrix-unit
   Choi composition identity proves the middle-qubit branch, which is
   combined with both endpoint cases into the main theorem.

The swapping proof expands an arbitrary positive effect into rank-one
projectors. Either of two rectangular filters expresses each contribution
as the Choi matrix of a pair of PPT maps, using the first or second
intermediate dimension according to where the qubit occurs. Summing the
separable contributions proves the result. A separate identity identifies
the indexed construction with the partial trace in the manuscript.

The Schmidt formalization defines the pure-state rank by product-vector
decomposition and proves its equivalence to the coefficient matrix rank.
The least such bound for a positive operator is its Schmidt number, with
zero assigned to the zero operator. It proves preservation under local
completely positive maps, identifies Schmidt number at most one with
separability, and establishes the two-PPT-map conclusion for inputs of
Schmidt number at most two. A verified Hilbert–Schmidt pairing identifies
the adjoint, whose preservation of PPT gives the adjoint 2-EB conclusion.

For a chain whose maps each satisfy SchmidtTrimming, Lean proves Schmidt
number decay and the associated entanglement-breaking bounds. The hypothesis
is now proved for every pair of PPT maps, so the results for arbitrary PPT
pairs are unconditional. This formalization follows the descent and block
structure strategy of [Christandl, Müller-Hermes, and Wolf](https://arxiv.org/abs/1807.01266).

[StructuredTrimming](PPTQubit/StructuredTrimming.lean) derives trimming
from the maximal-Schmidt principal-block criterion. That criterion is now
proved without a witness or closedness premise. The more general published
block-structure assertion, represented by PrincipalBlockStructure in
[BlockStructure](PPTQubit/BlockStructure.lean), is proved in
[GeneralBlock](PPTQubit/GeneralBlock.lean). Its proof uses Schmidt-number
witness separation and iterated Choi decomposition on the complement of an
arbitrary principal block.

[PureBlockStructure](PPTQubit/PureBlockStructure.lean) proves the
principal-block conclusion for positive matrices of rank at most one;
[InvariantSchmidt](PPTQubit/InvariantSchmidt.lean) proves the Schmidt
number bound for arbitrary positive partial-transpose-invariant operators.
[KPositive](PPTQubit/KPositive.lean) connects k-positive maps with
Schmidt-rank-k block positivity for Hermitian Choi operators and proves
the direct algebraic dual pairing. [ChoiPivot](PPTQubit/ChoiPivot.lean),
[ChoiDecomposition](PPTQubit/ChoiDecomposition.lean), and
[ChoiIterated](PPTQubit/ChoiIterated.lean) establish the iterated Choi
decomposition, including singular pivots, for Hermitian Choi matrices.
[BlockWitness](PPTQubit/BlockWitness.lean) proves the maximal-Schmidt
block criterion from the existence of Schmidt-number separating witnesses.
[SchmidtCone](PPTQubit/SchmidtCone.lean) proves the cone is convex and
establishes strict separation for a closed convex cone;
[RealDualWitness](PPTQubit/RealDualWitness.lean) represents the separating
functional by a Hermitian matrix. [WitnessClosed](PPTQubit/WitnessClosed.lean)
combines these steps to derive the witness, trimming, and index bound from
closedness of every Schmidt-number cone. [SchmidtCompact](PPTQubit/SchmidtCompact.lean)
proves compactness of the normalized bounded-rank projectors and a normalized
finite expansion. The norm here is the finite-function supremum norm, so
these projectors need not have unit trace. The real trace is bounded below
by one on the normalized generators, which is sufficient for the closedness
argument. [FiniteConic](PPTQubit/FiniteConic.lean) proves closedness
of a finite-dimensional conic hull using Carathéodory compression and a
positive normalizing functional. [SchmidtFiniteCone](PPTQubit/SchmidtFiniteCone.lean)
connects this result to Schmidt-number cones. Finally,
[Unconditional](PPTQubit/Unconditional.lean) proves the cone closedness,
the required block criterion, PPT-pair trimming, iteration, and index bound
without additional hypotheses.

| Files | Checked content |
| --- | --- |
| [StructuredTrimming](PPTQubit/StructuredTrimming.lean), [BlockStructure](PPTQubit/BlockStructure.lean) | Unconditional easy ranges and explicit reduction of the general index bound to the published block-structure proposition. |
| [PureBlockStructure](PPTQubit/PureBlockStructure.lean), [InvariantSchmidt](PPTQubit/InvariantSchmidt.lean), [KPositive](PPTQubit/KPositive.lean) | Pure/rank-one block structure, the partial-transpose-invariant Schmidt bound, and k-positive Choi and trace-pairing identities. |
| [ChoiPivot](PPTQubit/ChoiPivot.lean), [ChoiDecomposition](PPTQubit/ChoiDecomposition.lean), [ChoiIterated](PPTQubit/ChoiIterated.lean) | Completely positive pivot terms and iterated k-positive residuals, including singular pivots. |
| [SchmidtCone](PPTQubit/SchmidtCone.lean), [RealDualWitness](PPTQubit/RealDualWitness.lean), [BlockWitness](PPTQubit/BlockWitness.lean), [WitnessClosed](PPTQubit/WitnessClosed.lean) | Convexity and separation, Hermitian witnesses, and the reduction of general trimming and the index bound to Schmidt-cone closedness. |
| [SchmidtCompact](PPTQubit/SchmidtCompact.lean), [FiniteConic](PPTQubit/FiniteConic.lean), [SchmidtFiniteCone](PPTQubit/SchmidtFiniteCone.lean), [Unconditional](PPTQubit/Unconditional.lean) | Compact normalized generators, closed Schmidt-number cones, and unconditional PPT-pair trimming, iteration and index results. |
| [Swapping](PPTQubit/Swapping.lean), [LowSchmidtEffect](PPTQubit/LowSchmidtEffect.lean) | Arbitrary positive effects with a qubit, Schmidt-number-at-most-two effects without a qubit assumption, rectangular filters and the partial-trace formula. |
| [GeneralBlock](PPTQubit/GeneralBlock.lean), [RectangularChain](PPTQubit/RectangularChain.lean) | General principal-block structure and the full rectangular bound for arbitrary-length PPT chains. |
| [Schmidt](PPTQubit/Schmidt.lean), [SchmidtRank](PPTQubit/SchmidtRank.lean), [SchmidtNumber](PPTQubit/SchmidtNumber.lean) | Schmidt decomposition bounds, equivalence with matrix rank, separability at Schmidt number one, and monotonicity under local completely positive maps. |
| [SchmidtIteration](PPTQubit/SchmidtIteration.lean), [SchmidtConsequences](PPTQubit/SchmidtConsequences.lean) | General iteration and index implications with an explicit one-step premise, plus unconditional qubit-index and Schmidt-number-two results. |
| [Adjoint](PPTQubit/Adjoint.lean) | Hilbert–Schmidt pairing and adjoint composition, PPT preservation, and the 2-EB conclusion for adjoint PPT pairs. |
| [SpectralTools](PPTQubit/SpectralTools.lean), [SpectralSeparability](PPTQubit/SpectralSeparability.lean), [RowContraction](PPTQubit/RowContraction.lean) | Spectral calculus and the general Hermitian row-contraction separability theorem. |
| [SupportSquareRoots](PPTQubit/SupportSquareRoots.lean), [SecondOperations](PPTQubit/SecondOperations.lean), [QubitNormalization](PPTQubit/QubitNormalization.lean) | Exact support normalization and restoration for every qubit PPT operator. |
| [QubitRowContraction](PPTQubit/QubitRowContraction.lean), [QubitLink](PPTQubit/QubitLink.lean), [MiddleQubit](PPTQubit/MiddleQubit.lean) | Qubit reduction, Pauli block identities, separable PPT link products, and the complete qubit-anywhere composition theorem. |
| [MinorRank](PPTQubit/MinorRank.lean), [RealCombination](PPTQubit/RealCombination.lean) | General rank/minor equivalence over any field and full-column-rank real combinations in arbitrary finite complex dimensions. |
| [HermitianExtension](PPTQubit/HermitianExtension.lean), [SingularSupport](PPTQubit/SingularSupport.lean), [SingularDecomposition](PPTQubit/SingularDecomposition.lean) | Explicit Hermitian extension, including singular Gram matrices, and the spectral real-annihilator construction. |
| [SupportCompression](PPTQubit/SupportCompression.lean), [MinimalGram](PPTQubit/MinimalGram.lean), [GeneralDecomposition](PPTQubit/GeneralDecomposition.lean) | Lossless support projection, strict marginal positivity on its range, and the general real-hyperplane decomposition with the minimum number rank Q of nonzero terms. The zero operator has an empty decomposition. |
| [Auxiliary](PPTQubit/Auxiliary.lean), [AuxiliaryInterface](PPTQubit/AuxiliaryInterface.lean) | Singular auxiliary-qutrit construction and its interface for arbitrary product-indexed qubit PPT operators. |
| [RealPlanes](PPTQubit/RealPlanes.lean), [MatrixMaps](PPTQubit/MatrixMaps.lean), [LocalOperations](PPTQubit/LocalOperations.lean) | Explicit real subspaces, positive and transpose-invariant restrictions, local filtering, and preservation of PPT and separability. |
| [ChoiTensor](PPTQubit/ChoiTensor.lean), [ChoiCorrespondence](PPTQubit/ChoiCorrespondence.lean) | Positive maps give block-positive Choi matrices. Choi inversion, tensor action, the complete PPT criterion, composition identities, and the EB criterion are proved. |
| [QubitSeparability](PPTQubit/QubitSeparability.lean), [QutritPPTAction](PPTQubit/QutritPPTAction.lean) | Qubit PT-invariant separability and separable output after a PPT map acts on a qutrit PT-invariant positive input. |
| [PPTPairing](PPTQubit/PPTPairing.lean), [QubitPairing](PPTQubit/QubitPairing.lean) | Nonnegative pairing of PPT operators with decomposable witnesses, and with qubit PT-invariant block-positive witnesses. |

The main theorem and its dependencies are checked with Lean's
print-axioms command. They depend only on the standard Lean principles
propext, Classical.choice and Quot.sound. There are no project axioms,
sorry placeholders, or admitted proof steps.

## Remaining scope

The main theorem, both swapping formulations, the general principal-block
structure, the one-step Schmidt-number decrease and its iteration, the full
rectangular endpoint bound, and the index bound 2(d-1) have Lean proofs.
The manuscript's standalone bilinear-positivity lemma and the explicit
orthonormal-basis formulation of the real qutrit plane are not separately
encoded. The verified endpoint proof uses the corresponding direct
separable-decomposition and injective real-basis arguments.
The earlier conditional and positive-marginal lemmas remain available, but
the general real-hyperplane and endpoint theorems have no such premises.
The formal files use the designated transposed factor first when applying
the real-hyperplane decomposition.

## Reproducing the check

The project pins Lean 4.29.1 and mathlib commit
5e932f97dd25535344f80f9dd8da3aab83df0fe6. With network access, initialize
the pinned dependency and check the project from this directory.

~~~sh
lake update
lake exe cache get
lake build
~~~

For the local check, the compiled Mathlib cache is at
/private/tmp/ppt-lean-mathlib. While it remains available, run

~~~sh
bash verify-cached.sh
~~~

Set PPT_MATHLIB_CACHE to another restored cache root if needed. The script
compiles every module in dependency order in a fresh temporary directory,
then checks the combined PPTQubit.lean entry point. It does not use stale
project build artifacts. This checks the same source as the project build
but does not test dependency installation. The local check completed
successfully. The audit downloaded the pinned Mathlib source and its locked
dependency sources, recomputed cache keys using that version's hashing code,
and compared all 10,232 required compiled artifacts against the selected
2,558 archives. All matched. Dependency installation through Lake has not
been tested in this audit.

For the additional audit of this exact dependency snapshot, run

~~~sh
bash audit.sh
~~~

This checks the dependency hashes, rebuilds all 58 project modules in a
fresh directory, compiles the definition and boundary checks, rejects any
nonstandard axiom in project declarations, and runs `leanchecker --fresh`
on the combined project. The checker replays the imported and project
constants into an empty environment using the same Lean kernel. It is not
an independent implementation of Lean.

See the [original audit report](audit/REPORT.md), [coverage update](audit/COVERAGE-UPDATE.md), [run log](audit/latest-run.log),
[definition checks](audit/Semantics.lean), and
[dependency provenance](audit/dependency-audit.json). The report distinguishes
proved results from manuscript claims not yet fully formalized.

## License

The Lean formalization and its verification scripts are licensed under the
[Apache License 2.0](LICENSE). This license applies to this directory.
