/-
  * OssVerify.Images — well-formed images

  TRUST BOUNDARY: part of the statement layer.

  The three computable checks of `Equivalence.IMAGE_WF`.  Without them, an image
  malformed enough to have no valid entry, or to fault on its first instruction,
  would satisfy every "on every run" statement for no reason.  `image_wf_b` decides
  them, so `decide` proves `image_wf` of a concrete image through `image_wf_b_sound`.
-/
import LinuxSem.EquivalenceDefinition.Equivalence

set_option autoImplicit false

namespace LinuxSem.OssVerify.Images

open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.EquivalenceDefinition.Equivalence

/-- The entry point holds a fetchable instruction, the program-header table lies
    inside one readable loaded segment, and there is room above the segments for
    a program break. -/
def image_wf (i : Image) : Prop :=
  image_entry_fetchable i.img_segments i.img_init_pc = true
  ∧ image_phdrs_readable i.img_segments i.img_phdrs = true
  ∧ image_brk_satisfiable i.img_segments = true

def image_wf_b (i : Image) : Bool :=
  image_entry_fetchable i.img_segments i.img_init_pc
  && image_phdrs_readable i.img_segments i.img_phdrs
  && image_brk_satisfiable i.img_segments

theorem image_wf_b_sound (i : Image) (H : image_wf_b i = true) : image_wf i := by
  simp only [image_wf_b, Bool.and_eq_true] at H
  exact ⟨H.1.1, H.1.2, H.2⟩

theorem image_wf_b_complete (i : Image) (H : image_wf i) : image_wf_b i = true := by
  obtain ⟨H1, H2, H3⟩ := H
  simp only [image_wf_b, H1, H2, H3, Bool.and_self]

/-- The whole image of a loader snapshot. -/
def of_mem_image (m : MemImage) : Image :=
  ⟨m.loaded_segments, m.init_pc, m.phdrs⟩

end LinuxSem.OssVerify.Images
