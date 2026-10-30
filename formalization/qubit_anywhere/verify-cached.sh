#!/usr/bin/env bash
set -eu

cd -- "$(dirname -- "$0")"
ppt_cache="$(printenv PPT_MATHLIB_CACHE || true)"
if [ -z "$ppt_cache" ]; then
  ppt_cache="/private/tmp/ppt-lean-mathlib"
fi
ppt_mathlib="$ppt_cache/.lake/build/lib/lean"

if [ ! -d "$ppt_mathlib/Mathlib" ]; then
  printf '%s\n' "Mathlib cache not found at $ppt_mathlib." >&2
  printf '%s\n' "Set PPT_MATHLIB_CACHE or follow the Lake instructions in README.md." >&2
  exit 1
fi

ppt_lean_path="$ppt_mathlib"
for ppt_package in "$ppt_cache"/.lake/packages/*; do
  if [ -d "$ppt_package/.lake/build/lib/lean" ]; then
    ppt_lean_path="$ppt_lean_path:$ppt_package/.lake/build/lib/lean"
  fi
done

ppt_build="$(mktemp -d /tmp/ppt-lean-check.XXXXXX)"
trap 'rm -rf -- "$ppt_build"' EXIT
mkdir -p "$ppt_build/PPTQubit"
ppt_lean_path="$ppt_build:$ppt_lean_path"

LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/Auxiliary.olean" PPTQubit/Auxiliary.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/HermitianExtension.olean" PPTQubit/HermitianExtension.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/MinorRank.olean" PPTQubit/MinorRank.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/RealCombination.olean" PPTQubit/RealCombination.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/GramDecomposition.olean" PPTQubit/GramDecomposition.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/PPTPairing.olean" PPTQubit/PPTPairing.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/InvariantDecomposition.olean" PPTQubit/InvariantDecomposition.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/SingularSupport.olean" PPTQubit/SingularSupport.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/SingularDecomposition.olean" PPTQubit/SingularDecomposition.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/MinimalGram.olean" PPTQubit/MinimalGram.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/SupportCompression.olean" PPTQubit/SupportCompression.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/GeneralDecomposition.olean" PPTQubit/GeneralDecomposition.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/QubitSeparability.olean" PPTQubit/QubitSeparability.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/QubitPairing.olean" PPTQubit/QubitPairing.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/MatrixMaps.olean" PPTQubit/MatrixMaps.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/RealPlanes.olean" PPTQubit/RealPlanes.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/LocalOperations.olean" PPTQubit/LocalOperations.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/ChoiTensor.olean" PPTQubit/ChoiTensor.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/ChoiCorrespondence.olean" PPTQubit/ChoiCorrespondence.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/QutritPPTAction.olean" PPTQubit/QutritPPTAction.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/AuxiliaryInterface.olean" PPTQubit/AuxiliaryInterface.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/Endpoints.olean" PPTQubit/Endpoints.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/SpectralTools.olean" PPTQubit/SpectralTools.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/SeparableTensor.olean" PPTQubit/SeparableTensor.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/SpectralSeparability.olean" PPTQubit/SpectralSeparability.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/SupportSquareRoots.olean" PPTQubit/SupportSquareRoots.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/SecondOperations.olean" PPTQubit/SecondOperations.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/RowContraction.olean" PPTQubit/RowContraction.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/QubitRowContraction.olean" PPTQubit/QubitRowContraction.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/QubitNormalization.olean" PPTQubit/QubitNormalization.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/QubitLink.olean" PPTQubit/QubitLink.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/MiddleQubit.olean" PPTQubit/MiddleQubit.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/Swapping.olean" PPTQubit/Swapping.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/Schmidt.olean" PPTQubit/Schmidt.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/SchmidtRank.olean" PPTQubit/SchmidtRank.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/SchmidtNumber.olean" PPTQubit/SchmidtNumber.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/SchmidtIteration.olean" PPTQubit/SchmidtIteration.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/SchmidtConsequences.olean" PPTQubit/SchmidtConsequences.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/Adjoint.olean" PPTQubit/Adjoint.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/StructuredTrimming.olean" PPTQubit/StructuredTrimming.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/InvariantSchmidt.olean" PPTQubit/InvariantSchmidt.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/PureBlockStructure.olean" PPTQubit/PureBlockStructure.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/BlockStructure.olean" PPTQubit/BlockStructure.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/KPositive.olean" PPTQubit/KPositive.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/ChoiPivot.olean" PPTQubit/ChoiPivot.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/ChoiDecomposition.olean" PPTQubit/ChoiDecomposition.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/ChoiIterated.olean" PPTQubit/ChoiIterated.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/SchmidtCone.olean" PPTQubit/SchmidtCone.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/RealDualWitness.olean" PPTQubit/RealDualWitness.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/BlockWitness.olean" PPTQubit/BlockWitness.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/WitnessClosed.olean" PPTQubit/WitnessClosed.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/SchmidtCompact.olean" PPTQubit/SchmidtCompact.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/FiniteConic.olean" PPTQubit/FiniteConic.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/SchmidtFiniteCone.olean" PPTQubit/SchmidtFiniteCone.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/Unconditional.olean" PPTQubit/Unconditional.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/LowSchmidtEffect.olean" PPTQubit/LowSchmidtEffect.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/GeneralBlock.olean" PPTQubit/GeneralBlock.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit/RectangularChain.olean" PPTQubit/RectangularChain.lean
LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/PPTQubit.olean" PPTQubit.lean

if [ "${PPT_AUDIT:-0}" = "1" ]; then
  mkdir -p "$ppt_build/audit"
  LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/audit/Semantics.olean" audit/Semantics.lean
  LEAN_PATH="$ppt_lean_path" lean -o "$ppt_build/audit/Coverage.olean" audit/Coverage.lean
  LEAN_PATH="$ppt_lean_path" lean audit/Check.lean
  ppt_toolchain="$(lean --print-prefix)"
  printf '%s\n' 'Replaying the complete project and imported declarations in a fresh Lean kernel environment.'
  LEAN_PATH="$ppt_lean_path" "$ppt_toolchain/bin/leanchecker" --fresh PPTQubit
  printf '%s\n' 'Kernel replay passed.'
fi
