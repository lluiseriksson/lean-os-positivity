# lean-os-positivity

Lean 4 / Mathlib satellite repository for the THE-ERIKSSON-PROGRAMME.

This repository formalizes the **definition layer** for lattice reflection
positivity and the operatorial Osterwalder-Schrader target used by the mother
Yang-Mills repository.  It currently provides:

- finite-volume reflection positivity for complex observables on a finite
  lattice configuration space;
- an explicit positive-time observable interface;
- transfer-matrix certificate interfaces for the Ising and Gaussian-chain M1
  targets;
- OS/GNS reconstruction data interfaces;
- the operatorial mass-gap predicate for a positive Hamiltonian;
- the Wilson lattice gauge reflection-positivity interface consumed downstream.

## What this is not

This is **not** a proof of the Clay Yang-Mills problem, not a continuum limit,
and not a formalization of the full Euclidean OS axioms on `R^d`.

The repository intentionally carries unproved analytic/model-specific inputs as
explicit certificate fields or theorem arguments.  No project axiom is used to
stand in for a missing proof.

## Toolchain

The toolchain and Mathlib pin match `github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME`:

- Lean: `leanprover/lean4:v4.29.0-rc6`
- Mathlib: `07642720480157414db592fa85b626dafb71355b`

## Build

```bash
lake build OSPositivity
```

Current local verification:

```text
Build completed successfully (1905 jobs).
```

## Public Interface

Downstream repositories should import the root contract:

```lean
import Interfaces
```

See `INTERFACES.md` for the public declarations and breaking-change policy.
Implementation modules live under `OSPositivity/`; they are not the mother
repository contract.

## Honesty Ledger

Read `HYPOTHESIS_FRONTIER.md` before citing this repository.  The current main
line has zero Lean `sorry` and zero project axioms; the unproved content is
visible as explicit certificates such as `TransferMatrixReflectionCertificate`,
`GNSReconstruction`, and `WilsonRPCertificate`.
