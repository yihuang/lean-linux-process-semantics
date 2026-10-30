/-
  * Examples.FuzzTlv.Statements — the theorem statements about the fuzz target

  EVERY INPUT means every process input the model accepts: argv, the environment,
  the files, and standard input, which is where this driver reads the bytes from.
  So these say: whatever bytes arrive, of any length and split into any reads, every
  execution ends in `exit_group` with status 0 or 2.  They are about the compiled
  instructions, not the C source.
-/
import LinuxSem.OssVerify.Shapes

set_option autoImplicit false

open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.OssVerify

namespace LinuxSem.Examples.FuzzTlv.Statements

/-- When the environment refuses nothing it is not forced to, on every input within
    16 GiB. -/
def halts (img : Image) : Prop :=
  Shapes.halts_within_budget Shapes.budgets.lim_source Shapes.ok_or_refused img

/-- Whatever the environment refuses, with no budget premise. -/
def halts_may_fail (img : Image) : Prop :=
  Shapes.halts_may_fail Shapes.ok_or_refused img

end LinuxSem.Examples.FuzzTlv.Statements
