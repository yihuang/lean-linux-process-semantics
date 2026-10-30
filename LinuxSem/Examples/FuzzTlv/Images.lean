/-
  * Examples.FuzzTlv.Images — the two builds of the fuzz target

  `plain` is `source/fuzz_tlv.c` with `-DFIXED`, `buggy` without it.  The ELF is the
  artifact: `embedElf%` reads it at elaboration and refuses a binary the model cannot
  faithfully run.
-/
import LinuxSem.Common.EmbedElf
import LinuxSem.OssVerify.Images

set_option autoImplicit false
set_option maxRecDepth 400000
set_option maxHeartbeats 4000000

open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.OssVerify.Images

namespace LinuxSem.Examples.FuzzTlv.Images

def plain_mem : MemImage := embedElf% "program.fixed.elf"
def buggy_mem : MemImage := embedElf% "program.buggy.elf"

def plain : Image := of_mem_image plain_mem
def buggy : Image := of_mem_image buggy_mem

def plain_segs : List Segment := plain_mem.loaded_segments
def buggy_segs : List Segment := buggy_mem.loaded_segments

theorem plain_wf : image_wf plain := image_wf_b_sound _ (by decide)
theorem buggy_wf : image_wf buggy := image_wf_b_sound _ (by decide)

/-- The layout the proofs are written against: the writable page ends the image. -/
example : plain_mem.init_pc = 0x100121c := by decide
example : plain_mem.phdrs = ⟨0x1000040, 56, 6⟩ := by decide
example : plain_segs.map (fun s => (s.seg_base, s.seg_size, s.seg_perms))
    = [(0x1000000, 0x1000, "r--"), (0x1001000, 0x1000, "r-x"), (0x1003000, 0x1000, "rw-")] := by
  decide

end LinuxSem.Examples.FuzzTlv.Images
