# PPT Map Composition with a Qubit

Research manuscript by Ao-Xiang Liu and Cong-Feng Qiao.

## Result

Two compatible maps that are completely positive and completely copositive
compose to an entanglement-breaking map whenever the input, intermediate, or
output system is a qubit. The other dimensions are arbitrary and independent.
Trace preservation, unitality, and full rank are not assumed.

In the state formulation, every selected measurement outcome on the
intermediate systems of two independent states with positive partial
transpose (PPT) leaves the end systems separable whenever any one of the
four original local systems is a qubit. The intermediate dimensions may
differ.

For arbitrary dimensions, every composition of two compatible PPT maps,
and its adjoint, breaks entanglement with every qubit reference. This
2-entanglement-breaking property gives a uniform bound. Any `2(d-1)` PPT
maps on the algebra of complex `d x d` matrices compose to an
entanglement-breaking map, even when the maps differ at every step.

## Problem and significance

The problem originates in
[Open Quantum Problem 38, The PPT-squared conjecture](https://oqp.iqoqi.oeaw.ac.at/the-ppt-squared-conjecture).
The conjecture asked whether composing two PPT maps always destroys
entanglement with every reference system. Through the Choi correspondence,
the same question concerns the ability of independent PPT links to
distribute entanglement by entanglement swapping.

PPT states can be entangled, and a PPT map is not necessarily entanglement
breaking. A restriction on their composition therefore constrains both
repeated quantum noise and the connection of noisy quantum links. The
qubit endpoint case is not a consequence of the low-dimensional
separability criterion, because a qubit can be PPT entangled with a
sufficiently large system.

[High-dimensional counterexamples](https://github.com/openai/math/blob/main/preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/paper.pdf)
rule out the unrestricted two-map conjecture. The results here identify a
dimensional condition that still forces two-step entanglement breaking and
bound the number of steps required without that condition. The linear
bound is uniform over the maps, but is not optimal in every dimension.
For qutrit maps, two steps already suffice.

## Proof and related work

The endpoint proof uses an auxiliary operator invariant under partial
transpose on a qutrit factor. Its decomposition over real two-dimensional
subspaces, together with symmetrization, makes the relevant restrictions
of positive maps decomposable.
An independent argument using Pauli matrices treats the intermediate
qubit case, previously established by
[Henry](https://doi.org/10.5281/zenodo.21866485).

The conditional route from a qubit endpoint to a uniform composition
bound, and the Schmidt-number iteration used to obtain it, are due to
[Christandl, Müller-Hermes, and Wolf](https://doi.org/10.1007/s00023-019-00774-7).
[Turturean and Bao](https://github.com/physical-superintelligence/oqp-batch-2026/tree/7049357c42a8fe85262da08fdc10d57b4d9e67a0/ppt-composition-bound)
also prove the endpoint statement and the same `2(d-1)` bound, using a
different proof based on Schur complements, singular-value decomposition,
and separability of positive operators with equal diagonal blocks.

## Manuscript and reproduction

- [Manuscript PDF](<A Qubit Forbids Entanglement Swapping between PPT Links.pdf>).
- [LaTeX source](<A Qubit Forbids Entanglement Swapping between PPT Links.tex>),
  including the bibliography and complete Supplemental Material.

From this directory, compile with

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error "A Qubit Forbids Entanglement Swapping between PPT Links.tex"
```

References are embedded in the source. No separate bibliography database
or BibTeX run is required. The analytical proofs are included in the
Supplemental Material.

## Versions and citation

An [earlier repository version](https://github.com/GLiuax/ppt-composition-conjecture/tree/16b85dfc26888dc1dac812a6d633463b29dcba61)
already states the qubit endpoint result, the 2-entanglement-breaking
consequence, and the `2(d-1)` bound. Its commit is dated September 19,
2026 UTC. The files linked above are the current manuscript and
are not identical to that snapshot. Identify the version used when citing
or comparing the work.

The current manuscript may be cited as Ao-Xiang Liu and Cong-Feng Qiao,
*A Qubit Forbids Entanglement Swapping between PPT Links*, research
manuscript (2026). Include the repository version when referring to the
earlier snapshot.
