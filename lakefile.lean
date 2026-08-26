import Lake
open Lake DSL

/-! # `LPVerify` build configuration

  Pure-Lean LP certificate checker. No native dependencies, no
  `moreLinkArgs`. Built on top of `leanprover/lp-core` (`LPCore.Types`
  and `LPCore.Validate`).

  This is the package that fulfils the verifier-only goal of
  issue #50: any consumer that just wants to verify an
  externally-produced certificate can depend on `lp-verify` (which
  pulls in `lp-core`) without ever touching the SoPlex C++ build.
-/

require LPCore from git "https://github.com/leanprover/lp-core" @ "46c14aba1b4f3c5f7d865e187119a72775bee81b"

package LPVerify

@[default_target]
lean_lib LPVerify where
  roots := #[`LPVerify]
  globs := #[`LPVerify, `LPVerify.Arith, `LPVerify.Bool, `LPVerify.Budget,
             `LPVerify.Driver, `LPVerify.Prop, `LPVerify.Sound]

/-- `lake test` entry point: certificate accept/reject behavioral
    tests against hand-constructed fixtures. -/
@[test_driver]
lean_exe «verify-tests» where
  root := `LPVerifyTest.Verify

/-- `lake exe verify-bench [N] [iters]`: hot-path timing on a
    synthetic mid-size optimality certificate (issue #4). -/
lean_exe «verify-bench» where
  root := `LPVerifyTest.Bench
