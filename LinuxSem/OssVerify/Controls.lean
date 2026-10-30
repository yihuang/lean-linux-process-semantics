/-
  * OssVerify.Controls — the statement layer's controls

  QA on `Shapes` and `Images`, on the model's own fixtures.  `Examples.FuzzTlv`
  meets and refuses the halting shapes on a compiled program; these cover the rest:
  the agreement shape can be met, and `image_wf` refuses malformed images.
-/
import LinuxSem.Checks.BudgetPremise
import LinuxSem.OssVerify.Images
import LinuxSem.OssVerify.Shapes

set_option autoImplicit false
set_option maxRecDepth 100000

open LinuxSem.Checks.Examples
open LinuxSem.Checks.Cases.Prelude
open LinuxSem.OssVerify.Images
open LinuxSem.OssVerify.Shapes

namespace LinuxSem.OssVerify.Controls

theorem exit0_agrees : agrees budgets.lim_source budgets.lim_target exit0_image exit0_image :=
  LinuxSem.Checks.BudgetPremise.exit0_strong_universal_error_free_budgets _ _

/-- An entry point nothing maps. -/
theorem entry_outside_not_wf : ¬ image_wf ⟨exit0_segments, 0x200000, demo_phdrs⟩ :=
  fun H => absurd (image_wf_b_complete _ H) (by decide)

/-- A program-header table in unmapped memory. -/
theorem phdrs_outside_not_wf : ¬ image_wf ⟨exit0_segments, 0x100, ⟨0x300000, 56, 1⟩⟩ :=
  fun H => absurd (image_wf_b_complete _ H) (by decide)

end LinuxSem.OssVerify.Controls
