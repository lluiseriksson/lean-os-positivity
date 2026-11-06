# Satellite status

Last updated: 2026-07-08 23:55 CEST.

## Default branch

- Default branch: `main`
- Checked HEAD: `2ea7692fb7a60cac1b8f1deac5b1446c12557218`
- Latest remote checks on that HEAD: `CI` success
  ([run 28844970068](https://github.com/lluiseriksson/lean-os-positivity/actions/runs/28844970068))
  and `heartbeat` success
  ([run 28973984529](https://github.com/lluiseriksson/lean-os-positivity/actions/runs/28973984529))
- Open PRs at this check: none
- Most recent satellite PR: #61, merged into `main`
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

The first downstream copy target remains the
`PairingFormAlgebraOracle` section of `OSPositivity/MotherOracle.lean`,
cross-checking the hypothesis/order details against
`MOTHER_CONSUMPTION_CHECKLIST.md`.  The exact public names are:

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
`import Interfaces`; use `MOTHER_CONSUMPTION_CHECKLIST.md` as the copy checklist
and stop before quotient or `GNSReconstruction` construction.
