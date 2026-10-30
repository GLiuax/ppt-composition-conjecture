import PPTQubit
import audit.Coverage
import Lean.Util.CollectAxioms

/-! Audit the full project environment and print the public theorem signatures.
This file adds no mathematical assumptions to the project. -/
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let names := env.constants.toList.filter fun (n, _) =>
    (`PPTQubit).isPrefixOf n || (`PPTAudit).isPrefixOf n ||
      n.toString.startsWith "_private.PPTQubit." || n.toString.startsWith "_private.audit."
  if names.isEmpty then
    throwError "Audit found no project declarations"
  let (_, state) := ((names.forM fun (n, _) => CollectAxioms.collect n).run env).run {}
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  for ax in state.axioms do
    unless permitted.contains ax do
      throwError "Unexpected axiom in project dependency closure: {ax}"
  let theoremCount := names.filter fun (_, c) => match c with
    | .thmInfo _ => true
    | _ => false
  let axiomCount := names.filter fun (_, c) => match c with
    | .axiomInfo _ => true
    | _ => false
  unless axiomCount.isEmpty do
    throwError "Project declares {axiomCount.length} axioms"
  logInfo m!"AUDIT PASS: {names.length} project declarations, {theoremCount.length} theorem declarations (including generated declarations)."
  logInfo m!"Transitive axioms: {state.axioms.qsort Name.lt}"

#print sig PPTQubit.ppt_composition_qubit_anywhere
#print sig PPTQubit.swapping_positive_effect_separable
#print sig PPTQubit.swappingOutcome_partial_trace
#print sig PPTQubit.ppt_pair_adjoint_two_eb
#print sig PPTQubit.pt_invariant_real_hyperplane_decomposition
#print sig PPTQubit.schmidtCone_closed
#print sig PPTQubit.maximal_schmidt_block_criterion
#print sig PPTQubit.ppt_pair_trimming
#print sig PPTQubit.PPTPairChain.schmidt_number_decay
#print sig PPTQubit.PPTPairChain.entanglement_breaking
#print sig PPTQubit.ppt_power_entanglement_breaking
#print sig PPTQubit.ppt_index_bound
#print sig PPTQubit.swapping_schmidt_number_two_effect
#print sig PPTQubit.principal_block_structure
#print sig PPTQubit.PPTChain.entanglement_breaking_rectangular

#print PPTQubit.MatrixMap
#print PPTQubit.IsPPT
#print PPTQubit.IsPPTMap
#print PPTQubit.IsSeparable
#print PPTQubit.IsEntanglementBreaking
#print PPTQubit.SchmidtRankAtMost
#print PPTQubit.SchmidtNumberAtMost
#print PPTQubit.SchmidtTrimming
#print PPTQubit.PrincipalBlockStructure
