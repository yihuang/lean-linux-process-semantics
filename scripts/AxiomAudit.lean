/-
A soundness audit: the theorems below must depend only on Lean's three
standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

A tactic that silently *drops* a goal (e.g. an `elab` that clears the goal
list on failure — see PORTING.md §5.3) would leave a `sorryAx` in the proof
term while `scripts/check.sh`'s token grep would stay clean.  Checking the
axioms catches that class of hole.

## The second half is the index of the headline claims

Every claim the README advertises appears below by fully-qualified name: the
headline theorems plus the witness objects that make them bite.  A `#print
axioms` on a name that no longer resolves FAILS, so a rename cannot silently
drop a claim from the surface while the tree stays green.  That pin is the
reason the list lives here instead of in a module of its own: a module of
`#check`s re-exports nothing (its olean holds no declarations), and `#check`
cannot see a *weakened* statement — adding a premise to a headline theorem
leaves it green.  This file at least fails on a hole in the term.

(The list came from `LinuxSem/Checks/Capstone.lean`, deleted in favour of
this section.  Its two `by decide` sanity checks were already discharged
inside `LinuxProcessSem/Specs.lean` — `modeled_sysnos.length = 90` — and
inside `Checks/Examples.lean`, where `exit0_image_must_exit_zero` closes the
concrete `exits_c` walk by `decide`.  Nothing was lost by folding it in.)
-/
import LinuxSem

open LinuxSem

/- ## Soundness of the symbolic-execution tower and the simulators -/

#print axioms Common.ShapeAlg.alloc_mmap_strong_equiv_alg
#print axioms Common.SymExec.sym_exec_sound
#print axioms Common.FileSim.fout_strong_equiv
#print axioms Common.DrainSim.drain_strong_equiv
#print axioms Common.StreamSim.stream_strong_equiv
#print axioms Common.AllocSim.alloc_strong_equiv
#print axioms Common.WallSim.wall_strong_equiv
#print axioms Common.MmapSim.mmap_strong_equiv_te
#print axioms Common.MuslCall.musl_write_frame
#print axioms Common.MuslStrlen.HZ.mstr_argv_ptr_bounds
#print axioms Common.AxSymExec3Sound.erange_f_sound
#print axioms Common.AxSymExec3Sound.evalS_eq
#print axioms Common.AxSymExec3Sound.mkOr_denot
#print axioms Common.AxSymExec3Sound.sym_exec_ex
#print axioms Common.AxSymExec3Sound.sym_execT_ex
#print axioms Common.AxSymRun3.run_sound
#print axioms Common.AxSymRun3.runTX_sound
#print axioms Common.AxSymRun3.carry_after
#print axioms Common.AxSymExec3Sound.carry_sound
#print axioms EquivalenceDefinition.MeasureLib.full_support_base_mass_lower_certificate
#print axioms EquivalenceDefinition.MeasureLib.calibrated_mixture_mass_lower_certificate
#print axioms Common.AxSymExec3B.carryK0_eq
#print axioms Common.AsanPlanCore.run_block_eq
#print axioms Common.AsanPopFree.popfree_spec_of_code
#print axioms Checks.ExecutableSpecs.check_syscall_for_run

/- ## Headline claims

1. The abort refutation is fired, not stated: the witness image exists and
   its run really dies by signal at every limit. -/

#print axioms Checks.AbortWitness.abrt_image
#print axioms Checks.AbortWitness.abrt_refutes_error_free_abort
#print axioms Checks.AbortWitness.abrt_dies_by_signal
#print axioms Checks.AbortWitness.demo_entry_valid_abrt
#print axioms Checks.AbortWitness.abrt_input_valid

/- 2. The dispatched syscall surface is exact, in both directions, and the
   list it ranges over is duplicate-free. -/

#print axioms Checks.DispatchSurface.modeled_sysnos_exact
#print axioms Checks.DispatchSurface.syscall_spec_number_modeled
#print axioms Checks.DispatchSurface.modeled_sysnos_dispatched
#print axioms Checks.DispatchSurface.modeled_sysnos_nodup

/- 3. Omni and coexec are the same judgment. -/

#print axioms Checks.Omni.coexec_progress_iff
#print axioms Checks.Omni.coexec_coexec_progress
#print axioms Checks.Omni.sstep_receptive

/- 4. The exit route is realizable and bounded, and the walk carries a trace
   (which is what lets omni statements be discharged). -/

#print axioms Checks.Examples.exits_c_must_exit_at
#print axioms Checks.Omni.exits_c_exec
#print axioms Checks.Examples.exit0_image_must_exit_zero

/- 5. The budget mark's reading, with its four backing-metadata hypotheses
   explicit. -/

#print axioms Checks.BudgetPremise.mremap_budget_refused_refuses_inplace
#print axioms Checks.BudgetPremise.mremap_budget_refused_refuses_move
#print axioms Checks.BudgetPremise.mark_is_never_spurious

/- 6. Page-granularity of the mapping ledger survives the syscall surface,
   `brk` included.  The chain is unconditional: an unmodelled sysno makes the
   hypothesis impossible, so there is no coverage premise. -/

#print axioms Checks.VmMapsDisjoint.brk_grant_wf
#print axioms Checks.VmMapsDisjoint.brk_model_next_wf
#print axioms Checks.VmMapsDisjoint.check_brk_preserves
#print axioms Checks.VmMapsDisjoint.checked_table_preserves_vm
#print axioms Checks.VmMapsDisjoint.check_syscall_preserves_vm_wf
#print axioms Checks.VmMapsDisjoint.syscall_spec_preserves_vm_wf
#print axioms Checks.VmMapsDisjoint.base_unique_after_syscall
#print axioms Checks.VmMapsDisjoint.base_entry_unique
#print axioms Checks.VmMapsDisjoint.munmap_returns_matched_bytes

/- 7. The ASan plan checker is sound against the abstract semantics. -/

#print axioms Common.AsanPlanSound.check_sound

/- 8. The two equivalence demos are inhabited, not merely interfaced. -/

#print axioms Examples.PatchClassifyDemo.Sealed.DemoSealed
#print axioms Examples.PatchClassifyDemo.Sealed.demo_b1_reads_as_one
#print axioms Examples.RwxFlagNs.omni_strong_universal
#print axioms Examples.RwxFlagNs.strong_universal

/- 9. The accept/reject gate is decided on the exit-0 and exit-1 images. -/

#print axioms Checks.GatedSize.gate_exit0_accepts
#print axioms Checks.GatedSize.gate_exit1_rejects

/- 10. The classifier surface needs no spurious-failure or halting allowance. -/

#print axioms Checks.ErrorFreeInput.exit0_must_exit_zero_at_source_budget
#print axioms Checks.HaltsAllowed.exit1_must_exit_reject

/- 11. The ledger invariants hold of every reachable state, and the two new
       ones are carried along a whole run. -/

#print axioms Checks.MapsFit.check_syscall_preserves_vm_fit
#print axioms Checks.MapsFit.syscall_spec_preserves_vm_fit
#print axioms Checks.NoaccessOwned.check_syscall_preserves_sys_inv
#print axioms Checks.NoaccessOwned.syscall_spec_preserves_sys_inv
#print axioms Checks.NoaccessOwned.checked_table_preserves_na
#print axioms Checks.NoaccessOwned.sys_inv_noaccess_pages_owned
#print axioms Checks.NoaccessOwned.star_preserves_sys_inv
#print axioms Checks.NoaccessOwned.star_cfg_preserves_sys_inv
#print axioms Checks.NoaccessOwned.init_config_star_sys_inv

/- 12. The mremap budget mark reads "no placement fits", and on a state that
       keeps the ledger invariants a marked request has no non-errno
       resolution. -/

#print axioms Checks.BudgetPremise.mremap_budget_refused_iff
#print axioms Checks.BudgetPremise.mremap_budget_refused_refuses_inplace
#print axioms Checks.BudgetPremise.mremap_budget_refused_refuses_move
#print axioms Checks.BudgetPremiseInv.mremap_move_budget_admits_fresh
#print axioms Checks.BudgetPremiseInv.mremap_fresh_b_intro_sys_inv
#print axioms Checks.BudgetPremiseMremap.mremap_budget_refused_is_refusal_sys_inv

/- 13. A successful mmap, mremap or brk keeps the run going and touches no user
       memory, and a partial munmap's 0 answer leaves exactly the bytes and the
       pages outside the range. -/

#print axioms Checks.MmStepFrame.mm_ok_step
#print axioms Checks.MmStepFrame.mm_ok_no_accesses
#print axioms Checks.MunmapCut.check_munmap_zero_owned
#print axioms Checks.MunmapCut.check_munmap_zero_pages
#print axioms Checks.MunmapCut.check_munmap_unmap_backing

/- 14. A request whose charge alone exceeds the budget is no longer excused by
       the budget premise, and the finer premise is refutable on a run. -/

#print axioms EquivalenceDefinition.Equivalence.strong_universal_error_free_T_budgets_only_subsumes
#print axioms Checks.OversizeReachable.mm_errors
#print axioms Checks.OversizeReachable.mm_refutes_budgets_only
#print axioms Checks.OversizeReachable.cm_run_budget_only_refused

/- 15. The mmap-base band is exactly the set of bases Linux gives. -/

#print axioms Checks.Cases.MmapBase.sv48_band_is_linux_set
#print axioms Checks.Cases.MmapBase.sv39_band_is_linux_set
#print axioms Checks.Cases.MmapBase.rnd_bits_25_and_a_huge_guard_go_below_the_floor
#print axioms Checks.Cases.MmapBase.floor_guard_max_is_tight

/- 16. The fuzz-target statements: each shape is the model's definition, and a
       compiled binary meets it while the same source without its fixes does not. -/

#print axioms OssVerify.Shapes.agrees_is_lps
#print axioms OssVerify.Shapes.halts_within_budget_is_lps
#print axioms OssVerify.Shapes.halts_may_fail_is_lps
#print axioms OssVerify.Controls.exit0_agrees
#print axioms Examples.FuzzTlv.FixedProof.plain_halts_holds
#print axioms Examples.FuzzTlv.FixedProof.plain_halts_may_fail_holds
#print axioms Examples.FuzzTlv.BuggyRefutation.buggy_halts_refuted
#print axioms Examples.FuzzTlv.BuggyRefutation.buggy_halts_may_fail_refuted
