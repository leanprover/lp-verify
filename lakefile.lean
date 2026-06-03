import Lake
open Lake DSL

/-! # `LPVerify` build configuration

  Pure-Lean LP certificate checker. No native dependencies, no
  `moreLinkArgs`. Built on top of `kim-em/lp-core` (`LPCore.Types`
  and `LPCore.Validate`).

  This is the package that fulfils the verifier-only goal of
  issue #50: any consumer that just wants to verify an
  externally-produced certificate can depend on `lp-verify` (which
  pulls in `lp-core`) without ever touching the SoPlex C++ build.
-/

require LPCore from git "https://github.com/kim-em/lp-core" @
  "8b694db5f88c65b06714de5488edefd238185f60"

package LPVerify

@[default_target]
lean_lib LPVerify where
  roots := #[`LPVerify]
  globs := #[`LPVerify, `LPVerify.Arith, `LPVerify.Bool, `LPVerify.Budget,
             `LPVerify.Driver, `LPVerify.Prop, `LPVerify.Sound]
