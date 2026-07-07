# Satellite status

Last updated: 2026-07-07.

## Default branch

- Default branch: `main`
- Checked HEAD: `5380502fa26e0f4b2d0f29bfe9e44c598ad10cc4`
- Latest remote checks on that HEAD: `CI` success and `heartbeat` success
- Open PRs at this check: none
- Open coordination issue: `agent-task` #10

## Mother-facing surface

Downstream code should import the root contract:

```lean
import Interfaces
```

The current compile-time consumer oracle is
`OSPositivity/MotherOracle.lean`.  The safe mirror order remains:

1. `PairingFormAlgebraOracle`
2. `PairingFormInequalityOracle`
3. `LatticeReflectionSpanOracle`
4. `IsingBondTrueSideOracle`
5. `ReflectionNullContextOracle`

The first downstream copy target should be the
`PairingFormAlgebraOracle` section, especially these public names:

- `WeightFunction.reflectionForm_eq_pairingForm`
- `WeightFunction.pairingForm_add_left`
- `WeightFunction.pairingForm_add_right`
- `WeightFunction.pairingForm_smul_left`
- `WeightFunction.pairingForm_smul_right`
- `WeightFunction.pairingForm_conj_symm`

## Boundaries

This repository currently provides finite, certificate-explicit interfaces and
oracles.  This status file does not claim quotient construction,
`GNSReconstruction`, OS/Wightman reconstruction, continuum Yang-Mills, source
construction, `hRpoly`, raw activity, a mass gap theorem, or a Clay result.

## Exact next step

In `THE-ERIKSSON-PROGRAMME`, choose the Lean API smoke-test file, then mirror
`PairingFormAlgebraOracle` from `OSPositivity/MotherOracle.lean` using only
`import Interfaces`.
