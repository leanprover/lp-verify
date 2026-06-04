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

require LPCore from git "https://github.com/leanprover/lp-core" @
  "70ca150585f8439a830374b5bec602d391addbc9"

package LPVerify

@[default_target]
lean_lib LPVerify where
  roots := #[`LPVerify]
  globs := #[`LPVerify, `LPVerify.Arith, `LPVerify.Bool, `LPVerify.Budget,
             `LPVerify.Driver, `LPVerify.Prop, `LPVerify.Sound]
