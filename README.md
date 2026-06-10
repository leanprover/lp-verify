# LPVerify

[![Lean](https://img.shields.io/badge/Lean-4.31.0--rc1-blue.svg)](./lean-toolchain)
[![License](https://img.shields.io/github/license/leanprover/lp-verify.svg)](./LICENSE)

> **New here? Start at [`leanprover/lp`](https://github.com/leanprover/lp)** — the entry
> point for the `lp` / `maximize` tactics and the verified LP solver. This repository is one
> package of that family: the pure-Lean certificate checker.

Pure-Lean checker for linear programming certificates produced by
SoPlex (or any solver that emits the [`leanprover/lp-core`](https://github.com/leanprover/lp-core)
`Certificate` shape). No native dependencies — depending on
`lp-verify` does **not** pull in the SoPlex C++ build.

This is the package that delivers the standalone goal of
[`leanprover/lp#50`](https://github.com/leanprover/lp/issues/50):
*verify externally-produced certificates without building SoPlex*.
Use it when you have an LP solution generated elsewhere (a CI
artifact, a Python harness driving HiGHS via `lp-backend-soplex-json`,
a remote service that produces SoPlex JSON output) and want a
checked-in-Lean proof that the certificate is sound.

If instead you want `by lp` end-to-end (the tactic that calls SoPlex
itself and reconstructs Lean proof terms), depend on the meta-package
[`leanprover/lp`](https://github.com/leanprover/lp). That pulls in
`lp-verify` plus `lp-tactic` plus the SoPlex FFI backend.

## Quickstart

Add `LPVerify` to your `lakefile.lean`:

```lean
require LPVerify from git "https://github.com/leanprover/lp-verify" @ "main"
```

Construct (or deserialise) a `Problem` and a `Certificate`, then
hand them to `verifyOutcome`:

```lean
import LPVerify
open LP LP.Verify

-- An infeasible LP: the row says x ≥ 1, the column bound says x ≤ 0.
def lp : Problem 1 1 :=
  { c         := #v[0]
    a         := #[(0, 0, 1)]
    rowBounds := #v[(some 1, none)]
    colBounds := #v[(none, some 0)] }

-- Farkas certificate: multiplier 1 on the row lower bound and 1 on
-- the column upper bound combine to the contradiction 0 ≥ 1.
def cert : Certificate 1 1 :=
  { primal := none
    dual   := some { rowLower := #v[1], rowUpper := #v[0]
                     colLower := #v[0], colUpper := #v[1] }
    ray    := none }

#eval match verifyOutcome {} none lp
    { status := .infeasible, objective := none, certificate := cert, log := "" } with
  | .infeasible _ => "infeasible (with Lean proof)"
  | _             => "certificate rejected"
```

`Problem` and `Certificate` are the
[`leanprover/lp-core`](https://github.com/leanprover/lp-core) types (re-exported
under `LP`). `verifyOutcome` returns a `Verified` value whose
constructors (`.optimal`, `.infeasible`, `.unbounded`, `.unchecked`)
carry real Lean soundness proofs over the original `Problem`, not just
a status label — here `.infeasible h` carries `h : IsInfeasible lp`.
For end-to-end examples that produce and check certificates with a
real solver, see the meta-package
[`leanprover/lp`](https://github.com/leanprover/lp); `lp-verify` itself
stays solver-free.

## Trust model

Pure Lean. The verifier itself adds no trust assumptions beyond
the Lean kernel — every `Certificate` is independently checked
before any proof is constructed, and certificates that fail
checking are surfaced as `Verified.unchecked` rather than silently
accepted.

The serialisation layer between this checker and whichever external
tool produced the certificate is the user's responsibility. If you
want a known-good JSON wire format, see
[`leanprover/lp-backend-soplex-json`](https://github.com/leanprover/lp-backend-soplex-json).

## Layout

```
LPVerify.lean              # top-level import (aggregates submodules)
LPVerify/Driver.lean       # `verifyOutcome`, the `Verified` inductive
LPVerify/Sound.lean        # soundness lemmas for each Verified constructor
LPVerify/Prop.lean         # Prop-level statement of validity
LPVerify/Bool.lean         # decidable Bool-level checker
LPVerify/Arith.lean        # rational arithmetic over Problem rows
LPVerify/Budget.lean       # numerator/denominator bit-length budget
```

All declarations live in `namespace LP.Verify`, matching the
namespace used before the split. A consumer that writes
`LP.Verify.verifyOutcome` resolves the same way whether they
imported `LP.Verify` (from `leanprover/lp`) or `LPVerify`
directly.

## Licence

`LPVerify` is licensed under the [Apache License 2.0](./LICENSE),
matching the rest of the `leanprover/lp` family.
