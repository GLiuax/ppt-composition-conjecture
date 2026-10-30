import Lake
open Lake DSL

package pptQubitVerification

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "5e932f97dd25535344f80f9dd8da3aab83df0fe6"

@[default_target]
lean_lib PPTQubit
