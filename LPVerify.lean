/-
  Top-level entry point for `LPVerify` — the pure-Lean LP certificate
  checker.

  Re-exported by `leanprover/lp` through `LP.Verify` so existing
  callers writing `import LP.Verify` keep working unchanged.
-/
module

public import LPVerify.Arith
public import LPVerify.Bool
public import LPVerify.Budget
public import LPVerify.Driver
public import LPVerify.Prop
public import LPVerify.Sound

@[expose] public section
