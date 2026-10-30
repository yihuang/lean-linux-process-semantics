/-
  * LinuxProcessSem.Checks.Sys.Fs.ReadWrite — the read (63), write (64),
    pread64 (67), pwrite64 (68), writev (66), readv (65), lseek (62)
    checkers, and their proofs

  Answers to Linux [fs/read_write.c]: this file holds the checkers for the
  syscalls defined there, and no others.

  [Checks/ExecutableSpecs.lean] keeps the dispatcher and the four top-level
  theorems and re-exports this module.  The checkers here are executable,
  and their proofs relate them to the relational specs in the matching
  [Sys] module.

  A word is read UNSIGNED (`(w.toNat : Int)`); a `Bool` comparison is `==`
  or `decide (· < ·)` / `decide (· ≤ ·)`; list operations are
  `List.length` / `List.take` / `List.drop` / `List.flatten`; and
  `CheckOk` / `CheckReject` / `CheckUnmodeled` are the constructors of
  `check_result` (`Checks.Sys.Prelude`).

  Lean's `match` has no or-pattern, so `Some (FdFile p _)` and
  `Some (FdFileRW p _)` are two arms with one body each; the bodies are the
  same text.

  One declaration below is PUBLIC and is this file's own: the theorem
  [check_readv_imported_frame], stated beside [check_readv_imported] itself
  because [Checks/VmMapsDisjoint.lean] has to name it (the same reason
  `Checks/Sys/Fs/Open.lean` states [check_ftruncate_file_arm_frame] beside
  its checker).  Its proof is the checker side of
  [check_readv_imported_sound_ok] (`ReadWrite/Vec.lean`) with the spec
  dropped.

  This file holds `readv_heap_gap_no_ok` and the `check_read`,
  `check_read_urandom`, `check_lseek`, `check_pread64` and `check_pwrite64`
  quadruples; the `check_write`, `check_writev`, `check_readv_imported` and
  `check_readv` quadruples live in `ReadWrite/Write.lean`,
  `ReadWrite/Vec.lean` and `ReadWrite/Readv.lean`.  The recipe those proofs
  follow (`check_pwrite64_*` is the smallest complete example):

  (1) PROLOGUE.  Peel `bind inputSpec ;; bind getModelSpec` with
      `bind_ok0` (accepted outcomes) or `bind_unmodeled2` (declines); in
      the completeness directions rewrite it away instead with
      `simp only [inputSpec, getModelSpec, bind_input_spec, bind_getModel] at Hs`
      — [bind_input_spec] is what makes that possible (a
      `(bind_input_model_iff ?_ …).mp Hs` leaves the continuation's
      metavariable unsolved: the unification happens under the bind).
  (2) FD DISPATCH.  `generalize hq : fd_lookup (m_fds m) fd = q at H ⊢`
      then `cases q` (and `cases e` for the `some e` branch), and in every
      arm `try dsimp only at H ⊢` before anything else: `simp` alone leaves
      an already-`some`/`none`-headed `match` unreduced, which is the file
      kinds' `match some (FdEntry.FdFile p off) with …`.
  (3) EFFECT INVERSION.  After `obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff`
      the acceptor's `match eff with | ⟨ret,[(a,bs)],[],[],[],[]⟩ => …`
      still does NOT reduce: `ws` must be decomposed one level further
      (`cases ws with | nil => … | cons hd tl => obtain ⟨a,bs⟩ := hd;
      cases tl <;> cases zs <;> cases us <;> cases cs <;> cases ks`), and
      then `dsimp only at H` in the live branch reduces the match to the
      leaf `if`.  The first goal after the `cases` cascade is the live one;
      the rest are dead and are closed by
      `all_goals (try dsimp only at H); all_goals (try contradiction)`.
      `exact nomatch H` is NOT usable for those dead shapes when `H` is an
      unreduced `if … = .CheckOk …`: its "Missing cases: _" error is not
      backtrackable, so `try`/`first` do not skip it.  `contradiction` is.
  (4) SCRUTINEE EQUATIONS.  `cases h : e` only generalises the TARGET, so
      a hypothesis mentioning `e` keeps an unreduced `match`; use
      `generalize h : e = x at H ⊢` + `cases x` (as [check_pread64_*] does
      for `Fs.file_read` and `write_source`), or add `simp only [h] at H ⊢`
      in every branch (as [check_read_urandom_*] does).
  (5) LEAVES.  `check_ret_only` accepts exactly the spec's `ret_only` /
      `err_ret` leaf ([ret_only_ok_spec] below, one step); a ledger leaf
      inverts with `check_ret_only_copyins_ok_iff` and rebuilds with
      `record_copyins_ok_empty`; a `seqSpec (set_fs …) (record_copyins …)`
      leaf inverts with [seqSpec_set_fs_record_ret_only_ok_inv] and
      declines with [seqSpec_set_fs_unmodeled_inv].  In the completeness
      directions invert the spec side with `seqSpec_modify_pure_ok_inv` /
      [seqSpec_set_fs_record_ret_only_ok_inv] or `cases Hs`, and finish
      with `simp [check_ret_only, bv_eqb_refl]` (or
      `check_ret_only_copyins_refl`).  Wrap completion leaves as
      `cases Hs` + `try simp […]` / `try rfl`: a plain `simp`/`rfl` after a
      `cases` that already closed the goal is a "No goals to be solved"
      error.
  (6) MACROS.  The leaves must be THEOREMS, not tactic macros: Lean's
      macro hygiene renames `H`, `eff`, `m`, `m'`, `evs` inside a
      quotation (`H✝`), so a macro cannot refer to the caller's
      hypotheses.
  (7) SIX MORE FOOTGUNS, found on the `check_read` pair:

      (a) `ok_zsplit` / `ok_zsplit_c` below split `check_access_ok_zero`
          against `access_ok_zero` at one `access_okb` verdict.
          [Checks.Sys.Uaccess.ok_zero_cases] does NOT work: it `cases`es
          the scrutinee, which generalises only the target, so the
          hypothesis keeps its `if` (footgun (4)).  The `_c` form is the
          completeness direction's, where the checker is the GOAL and the
          spec the hypothesis.
      (b) DO NOT `subst` the equalities a passing checker test encodes.
          `ha : bv_eqb a buf = true` has to become `a = buf` first, and
          `subst` then eliminates whichever side it likes — for the read
          arms it eliminated the PARAMETER `buf` and not the pattern
          variable, exactly the footgun the recipe's item (4) warns about.
          `rw [ha', hret']` on the goal is what works.
      (c) `SocketState`/`NetStep` are the tree's shapes: `NetStep.cons`
          takes ONE byte (a `NetStream` is `Nat → NetStep`), so
          `cases rx 0` has the single arm `| cons b0 =>` and the tail is
          `rx` itself.
      (d) The two `err_ret`s (`Sys.Syscall` and `Sys.Uaccess`) are both open
          in this file, so a bare `err_ret` in a NEW statement is
          ambiguous; qualify it.
      (e) A checker leaf under `check_access_ok_zero` is still an `if`
          after the effect cases: `unfold check_socket_pending_error at H`
          (and `unfold socket_pending_error` on the spec side) is what lets
          the split see it.
      (f) In the completeness direction the effect has to be reduced out of
          the checker's `match eff with | ⟨ret, [(a, bs)], …⟩` before the
          delivered-prefix guard can be rewritten: `simp only [mkEffect]`
          after substituting the spec's effect, since `dsimp` alone does not
          unfold `mkEffect` inside a match scrutinee.

  (8) `lseek`'s spec tests `SEEK_MAX < bv_unsigned whence` as a PROP, while
      the checker tests `decide (…) = true` as a BOOL: rewrite the spec side
      with `ite_eq_left (of_decide_eq_true hw)` / `ite_eq_right (fun hP => hw
      (decide_eq_true hP))` and the checker side with `ite_eq_left hw`.

  (9) THE `check_read` COMPLETENESS PAIR, and three things it needed that
      are worth carrying to the other quadruples:

      (a) A COMPLETENESS LEAF IS INVERTED, NOT `cases`d.  `cases Hs` only
          does the job when the spec's leaf is a `pure` (then `Hs` is an
          `Outcome.ok … = .unmodeled` clash, or substitutes the three
          unknowns); a `seqSpec (set_fds …) (pure e)` leaf needs
          [seqSpec_set_fds_pure_ok_inv] (ditto set_pipes / set_stdin /
          set_fs / record_copyins), and the RST / ETIMEDOUT arm needs
          [seqSpec_set_fds_err_ret_ok_inv].  `cases Hs` on a `bind` /
          `seqSpec` chain leaves `∃ …` goals behind — that is the failure
          mode to watch for, and "No goals to be solved" at the *next*
          tactic is the other one (a `dsimp only at Hs ⊢` can already close
          a leaf whose checker arm is literally `.CheckUnmodeled`, because
          `dsimp` discharges an `X = X`).
      (b) `check_access_ok_zero` IS POSITIVE, `access_ok_zero` IS NEGATIVE
          only in /dev/null's arm: everywhere else `ok_zsplit_c Hs buf
          count` splits both sides at one verdict.  /dev/null's spec spells
          the test `if !access_okb … then -EFAULT`, so it needs the manual
          `by_cases hok : access_okb … = true` pair
          (`rw [ite_eq_right (by simp [hok])] at Hs` beside `rw [ite_eq_left hok]`)
          that [check_read_sound_ok] already uses in the other direction.
      (c) THE NO-DECLINE TOOLKIT ([pure_no_unmodeled],
          [emit_no_unmodeled], [choose_no_unmodeled],
          [modifySpec_no_unmodeled], [bind_no_unmodeled],
          [seqSpec_no_unmodeled], [modifySeq_no_unmodeled],
          [emitSeq_no_unmodeled], [deliverSeq_no_unmodeled],
          [choose_bind_no_unmodeled], [seqSpec_pure_no_unmodeled],
          [access_ok_zero_unmodeled_iff]) is what refutes the branches
          where the spec CANNOT decline: in the completeness-unmodeled
          direction those branches are `absurd Hs (…)`, never an effect
          cascade — the cascade is the SOUND direction's problem.
          `set_fs` / `set_fds` / `set_pipes` / `set_stdin` are all
          `modifySpec (with_… …)`, so `modifySeq_no_unmodeled` states them
          all.

  (10) THE `check_write_*` SHAPE.  `write_spec` is `write_range_gate buf
      count` (an `if !modeled_rw_range … then unmodeled else k`, so a
      `by_cases hmr` per file arm, with `exact nomatch H` / `rfl` on the
      gate-true side) wrapped round either `access_ok_zero` or
      `write_file_tail i.in_mem buf count place`.  `write_file_tail` binds
      `bs` to `write_source …`, answers -EFAULT when `!w_is0 count &&
      (bs.length == 0)`, builds `deliver` from `place bs` (`none` giving
      `unmodeled`, `some upd` giving `upd (write_ledger buf count bs)`), and
      closes with `access_ok_zero buf count deliver` when `e_is0 count` and
      `deliver` otherwise.  The order to walk is: gate →
      `generalize hbs : write_source … = bs` → the
      -EFAULT `if` → `place` (`cases hfs : Fs.fs_lookup …`, then the
      `modeled_file_gap` `if` where the arm has one) → `w_is0 count` (which
      picks `write_ledger`'s `ret_only` / `record_copyins` leaf and takes
      the `access_ok_zero` with it).  The CHANNEL arm has no gate-free
      `place`: after `bs.length == 0`, its leaf is
      `bind (choose (fun ds => 1 ≤ ds.length ∧ ds.length ≤ rw_count_clamp
      count ∧ ds = bs.take ds.length)) (fun ds => seqSpec (emit (ds.map
      (WriteEv ch))) (record_copyins [(buf, ds.length)] (ret_only (len_word
      ds))))`, so `check_write_sound_ok` must build it at `ds` chosen as
      `bs.take ret.toNat`, out of the checker's `1 ≤ ret.toNat &&
      ret.toNat ≤ bs.length` and `copyins = [(buf, ret.toNat)]`, and needs
      three facts:

        · `(bs.take ret.toNat).length = ret.toNat`
          (`List.length_take` + `Nat.min_eq_left (Int.ofNat_le.mp h)`);
        · `(bs.take ret.toNat).length ≤ rw_count_clamp count`
          (`Uaccess.write_source_length_le` at `hbs`);
        · `len_word (bs.take ret.toNat) = ret` — the checker never says the
          RETURN is `len_word` of the prefix, only that its `toNat` matches
          the ledger, so this is `BitVec.ofNat 64 ret.toNat = ret`
          (`BitVec.eq_of_toNat_eq` + `BitVec.toNat_ofNat` +
          `Nat.mod_eq_of_lt ret.isLt`).  `bitvec` does NOT give it
          definitionally; that is the one genuinely new ingredient the write
          CHANNEL arm adds over the read one.
      The three FILE arms and /dev/null then reuse `access_ok_zero` /
      `write_range_gate` splits and the two `write_ledger` leaves, and the
      PIPE arm walks `pipe_end_live` → `pipe_lookup` → `pipe_write_room` →
      `bs.length == word_to_nat count` before its
      `check_ret_only_copyins` leaf.

  The proofs `cases` the effect's six fields and close the dead shapes with
  `exact nomatch H` (footgun (d)).  A function-typed `if` whose test narrows
  a word is split with the `generalize hP : … = Q at *` pattern of footgun
  (a) wherever `by_cases` would loop.
-/
import LinuxSem.Checks.Sys.Prelude
import LinuxSem.Checks.Sys.Uaccess
import LinuxSem.LinuxProcessSem.RiscvSemantics
import LinuxSem.LinuxProcessSem.Sys.Fs.ReadWrite

namespace LinuxSem.Checks.Sys.Fs.ReadWrite

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Uaccess
open LinuxSem.LinuxProcessSem.Sys.Fs.ReadWrite
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Sys.Uaccess

/- =========================================================================
   Shared acceptors
   ========================================================================= -/

/-- [ReadWrite.socket_pending_error] as an acceptor: the read that reports
    the peer's RST or timeout also consumes it, so the accepted model is
    the one whose connection has moved to [SkReset].  No byte moves, so
    the range verdict is all that is left in front of it. -/
def check_socket_pending_error (e : Int) (fd : word) (peer : PeerAddr)
    (ch : word) (buf count : word) (_i : SyscallInput) (eff : SyscallEffect)
    (m : Model) : check_result :=
  check_access_ok_zero buf count eff m
    (check_ret_only eff (errno_ret e)
       (with_fds (fd_insert (m_fds m) fd
          (FdEntry.FdSocket (SockState.SkReset peer ch))) m) [])

/-- [ReadWrite.read_urandom] as an acceptor, branch for branch: the zero
    count, the first-byte verdict, the stream's length test, the
    whole-delivery verdict, and then ONE delivery — exactly the clamped
    count off the front of [m_urandom] at [buf], the stream advanced past
    them, no event.  Nothing is chosen, so the accepted effect is computed
    rather than matched against a predicate. -/
def check_read_urandom (i : SyscallInput) (buf count : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if w_is0 count then check_ret_only eff (BitVec.ofInt 64 0) m []
  else
    match read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) with
    | none => check_ret_only eff (errno_ret EFAULT) m []
    | some _ =>
        let r := stream_take_z (m_urandom m) (rw_count_clamp count)
        if !(((r.1.length : Int) == rw_count_clamp count))
        then .CheckUnmodeled
        else
          match read_bytes_map i.in_wmem buf (len_word r.1) with
          | none => .CheckUnmodeled
          | some _ =>
              match eff with
              | ⟨ret, [(a, bs)], [], [], [], []⟩ =>
                  if bv_eqb a buf && bv_eqb ret (len_word r.1)
                     && listN_eqb bs r.1
                  then .CheckOk (with_urandom r.2 m) []
                  else .CheckReject
              | _ => .CheckReject

/- =========================================================================
   read (63)
   ========================================================================= -/

/-- `[ReadWrite.read_spec]`'s acceptor, arm for arm.  The fd kinds are
    dispatched first (a closed fd, a write-only or append fd, a channel
    opened for writing: -EBADF), then the two range/gate tests Linux makes
    inside `[vfs_read]` (`[access_ok]`, then the zero count), then the
    per-kind protocol.  Every kernel citation lives on `[read_spec]`. -/
def check_read (i : SyscallInput) (fd buf count : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match fd_lookup (m_fds m) fd with
  | none => check_ret_only eff (errno_ret EBADF) m []
  | some (FdEntry.FdFileW _ _) => check_ret_only eff (errno_ret EBADF) m []
  | some (FdEntry.FdFileA _ _) => check_ret_only eff (errno_ret EBADF) m []
  | some (FdEntry.FdChannel ch) =>
      if !(w_is0 ch) then check_ret_only eff (errno_ret EBADF) m []
      else
      if !(access_okb buf (count.toNat : Int))
      then check_ret_only eff (errno_ret EFAULT) m []
        -- vfs_read's access_ok, fs/read_write.c at v6.18.46
      else
      if w_is0 count then check_ret_only eff (BitVec.ofInt 64 0) m []
      else
        match m_stdin m 0 with
        | none => check_ret_only eff (BitVec.ofInt 64 0) m []
          -- end of input (sticky)
        | some _ =>
            match read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) with
            | none => check_ret_only eff (errno_ret EFAULT) m []
              -- no byte can land: -EFAULT
            | some _ =>
            match read_bytes_map i.in_wmem buf
                    (len_word (stream_take_z (m_stdin m) (rw_count_clamp count)).1) with
            | none => .CheckUnmodeled
              -- partially writable destination: fail closed
            | some _ =>
                match eff with
                | ⟨ret, [(a, bs)], [], [], [], []⟩ =>
                    if bv_eqb a buf
                       && bv_eqb ret (len_word bs)
                       && decide (1 ≤ (bs.length : Int))
                       && decide ((bs.length : Int) ≤ rw_count_clamp count)
                       && listN_eqb (stream_take (m_stdin m) bs.length).1 bs
                       && wmem_ok i buf (len_word bs)
                       -- delivered prefix writable
                    then .CheckOk
                           (with_stdin (stream_take (m_stdin m) bs.length).2 m)
                           (bs.map (event.ReadEv ch))
                    else .CheckReject
                | _ => .CheckReject
  | some FdEntry.FdDir =>
      if !(access_okb buf (count.toNat : Int))
      then check_ret_only eff (errno_ret EFAULT) m []
      else check_ret_only eff (errno_ret EISDIR) m []
  | some (FdEntry.FdSocket sk) =>
      if !(modeled_rw_range buf count) then .CheckUnmodeled
      else
      if w_is0 count then
        check_access_ok_zero buf count eff m
          (check_ret_only eff (BitVec.ofInt 64 0) m [])
          -- [read(fd, buf, 0)] short-circuits before the protocol on ANY
          -- socket, so this precedes the state dispatch below
      else
      match sk with
      | .SkConnected peer ch rx =>
          match rx 0 with
          | .fin =>
              check_access_ok_zero buf count eff m
                (check_ret_only eff (BitVec.ofInt 64 0) m [])
          | .rst =>
              check_socket_pending_error ECONNRESET fd peer ch buf count i eff m
          | .timedOut =>
              check_socket_pending_error ETIMEDOUT fd peer ch buf count i eff m
          | .cons _ =>
              match read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) with
              | none => check_ret_only eff (errno_ret EFAULT) m []
              | some _ =>
              match read_bytes_map i.in_wmem buf
                      (len_word (net_take_z rx (rw_count_clamp count)).1) with
              | none => .CheckUnmodeled
                -- partially writable destination: fail closed
              | some _ =>
                  -- the delivered bytes are a nonempty prefix of what the
                  -- peer has left to say, and the script advances past
                  -- exactly them -- the channel rule, on [net_take]
                  match eff with
                  | ⟨ret, [(a, bs)], [], [], [], []⟩ =>
                      if bv_eqb a buf
                         && bv_eqb ret (len_word bs)
                         && decide (1 ≤ (bs.length : Int))
                         && decide ((bs.length : Int) ≤ rw_count_clamp count)
                         && listN_eqb (net_take rx bs.length).1 bs
                         && wmem_ok i buf (len_word bs)
                      then .CheckOk
                             (with_fds
                                (fd_insert (m_fds m) fd
                                   (FdEntry.FdSocket
                                      (SockState.SkConnected peer ch
                                         (net_take rx bs.length).2))) m)
                             (bs.map (event.ReadEv ch))
                      else .CheckReject
                  | _ => .CheckReject
      | .SkReset _ _ =>
          check_access_ok_zero buf count eff m
            (check_ret_only eff (BitVec.ofInt 64 0) m [])
          -- the peer's error was reported once and RCV_SHUTDOWN is set:
          -- 0, NOT the -ENOTCONN the socket's TCP_CLOSE state suggests
      | _ =>
          check_access_ok_zero buf count eff m
            (check_ret_only eff (errno_ret ENOTCONN) m [])
          -- fresh, bound or listening: never TCP_ESTABLISHED
  | some (FdEntry.FdFile p off) =>
      if !(access_okb buf (count.toNat : Int))
      then check_ret_only eff (errno_ret EFAULT) m []
      else
      match Fs.fs_lookup (m_fs m) p with
      | none => .CheckUnmodeled
      | some data =>
          let bs := Fs.file_read data off (BitVec.ofInt 64 (rw_count_clamp count))
          match read_bytes_map i.in_wmem buf (len_word bs) with
          | none =>
              -- the DELIVERED prefix is not fully writable
              match read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) with
              | none => check_ret_only eff (errno_ret EFAULT) m []
                -- not even the first delivered byte: -EFAULT
              | some _ => .CheckUnmodeled
                -- partially writable: fail closed
          | some _ =>
              let m' := with_fds
                          (fd_insert (m_fds m) fd
                             (FdEntry.FdFile p (off + len_word bs))) m
              match bs, eff with
              -- zero-byte read (EOF / count = 0): canonical empty-writes
              -- shape, same as a zero-byte channel read
              | [], _ => check_ret_only eff (BitVec.ofInt 64 0) m' []
              | _ :: _, ⟨ret, [(a, bs')], [], [], [], []⟩ =>
                  if bv_eqb a buf && listN_eqb bs' bs
                     && bv_eqb ret (len_word bs)
                  then .CheckOk m' []
                  else .CheckReject
              | _, _ => .CheckReject
  | some (FdEntry.FdFileRW p off) =>
      -- the [FdFile] arm above, on the O_RDWR kind
      if !(access_okb buf (count.toNat : Int))
      then check_ret_only eff (errno_ret EFAULT) m []
      else
      match Fs.fs_lookup (m_fs m) p with
      | none => .CheckUnmodeled
      | some data =>
          let bs := Fs.file_read data off (BitVec.ofInt 64 (rw_count_clamp count))
          match read_bytes_map i.in_wmem buf (len_word bs) with
          | none =>
              match read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) with
              | none => check_ret_only eff (errno_ret EFAULT) m []
              | some _ => .CheckUnmodeled
          | some _ =>
              let m' := with_fds
                          (fd_insert (m_fds m) fd
                             (FdEntry.FdFileRW p (off + len_word bs))) m
              match bs, eff with
              | [], _ => check_ret_only eff (BitVec.ofInt 64 0) m' []
              | _ :: _, ⟨ret, [(a, bs')], [], [], [], []⟩ =>
                  if bv_eqb a buf && listN_eqb bs' bs
                     && bv_eqb ret (len_word bs)
                  then .CheckOk m' []
                  else .CheckReject
              | _, _ => .CheckReject
  | some (FdEntry.FdDevNull rd _) =>
      if !rd then check_ret_only eff (errno_ret EBADF) m []
      else check_access_ok_zero buf count eff m
             (check_ret_only eff (BitVec.ofInt 64 0) m [])
             -- [read_null]: 0
  | some FdEntry.FdUrandom =>
      if !(access_okb buf (count.toNat : Int))
      then check_ret_only eff (errno_ret EFAULT) m []
      else check_read_urandom i buf count eff m
        -- the declared stream
  | some (FdEntry.FdPipe id w) =>
      if w then check_ret_only eff (errno_ret EBADF) m []
        -- write end: -EBADF
      else
      if !(modeled_rw_range buf count) then .CheckUnmodeled
      else
      if w_is0 count then
        check_access_ok_zero buf count eff m
          (check_ret_only eff (BitVec.ofInt 64 0) m [])
          -- "Null read succeeds"
      else
      match pipe_lookup (m_pipes m) id with
      | none => .CheckUnmodeled
      | some ([], _) =>
          if pipe_end_live (m_fds m) id true then .CheckUnmodeled
            -- would block
          else check_access_ok_zero buf count eff m
                 (check_ret_only eff (BitVec.ofInt 64 0) m [])
                 -- end of file
      | some (q@(_ :: _), used) =>
          let del := pipe_take q (rw_count_clamp count)
          match read_bytes_map i.in_wmem buf (len_word del) with
          | none =>
              match read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) with
              | none => check_ret_only eff (errno_ret EFAULT) m []
              | some _ => .CheckUnmodeled
                -- partially writable: fail closed
          | some _ =>
              let m' := with_pipes
                          (pipe_insert (m_pipes m) id
                             (pipe_consume (q, used) del.length)) m
              match eff with
              | ⟨ret, ws, [], [], [], []⟩ =>
                  if writes_eqb ws (delivered_writes buf del)
                     && bv_eqb ret (len_word del)
                  then .CheckOk m' []
                  else .CheckReject
              | _ => .CheckReject

/- =========================================================================
   write (64)
   ========================================================================= -/

/-- `[ReadWrite.write_spec]`'s acceptor, arm for arm.  The fd dispatch is
    first (a closed fd, a file opened `O_RDONLY`, a channel opened for
    reading: -EBADF), then `[modeled_rw_range]` — the count gate the write
    side needs because it reads user memory — then the per-kind protocol.
    Every kernel citation lives on `[write_spec]`. -/
def check_write (i : SyscallInput) (fd buf count : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match fd_lookup (m_fds m) fd with
  | none => check_ret_only eff (errno_ret EBADF) m []
  | some (FdEntry.FdFile _ _) => check_ret_only eff (errno_ret EBADF) m []
  | some (FdEntry.FdChannel ch) =>
      if w_is0 ch then check_ret_only eff (errno_ret EBADF) m []
      else
      if !(modeled_rw_range buf count) then .CheckUnmodeled
      else
      if w_is0 count
      then check_access_ok_zero buf count eff m
             (check_ret_only eff (BitVec.ofInt 64 0) m [])
             -- [count = 0] moves no byte, so only the range verdict is
             -- left — see [Uaccess.access_ok_zero]
      else
      let bs := write_source i.in_mem buf count
      if bs.length == 0
      then check_ret_only eff (errno_ret EFAULT) m []
      else
        -- the claimed return determines the delivered prefix: any
        -- nonempty prefix of the readable prefix is admissible.
        --
        -- The ledger test is a nested [if] under the range test, not a
        -- third [&&]: [andb] is an ordinary application and [vm_compute]
        -- is call by value, so every operand is evaluated, and this one
        -- converts [ret] to a unary [nat] -- about 2^64 constructors for
        -- an errno-encoded return, which does not terminate (36 GB
        -- resident and climbing, measured).  Under the range test the
        -- conversion is bounded by [length bs].  Extraction is not
        -- affected: ExtrOcamlBasic inlines [andb] as OCaml's lazy [(&&)].
        -- [check_writev]'s channel arm and
        -- [Net.Socket.check_send_on_socket] have the same shape for the
        -- same reason; [check_read] never puts [ret] inside a [Z.to_nat],
        -- since every length it tests comes from the delivered bytes.
        -- [write_channel_eintr_rejected] and [write_channel_epipe_rejected]
        -- in `Checks/Cases/Fs/ReadWrite.lean` pin by evaluation that this
        -- path is reachable, though neither example sits in this file. -/
        match eff with
        | ⟨ret, [], [], [], [], copyins⟩ =>
            if decide (1 ≤ (ret.toNat : Int))
               && decide ((ret.toNat : Int) ≤ (bs.length : Int))
            then
              if access_ranges_eqb copyins [(buf, ret.toNat)]
              then .CheckOk m (bs.take ret.toNat |>.map (event.WriteEv ch))
              else .CheckReject
            else .CheckReject
        | _ => .CheckReject
  | some FdEntry.FdDir => check_ret_only eff (errno_ret EBADF) m []
  | some (FdEntry.FdSocket _) => .CheckUnmodeled
    -- writing a socket is unmodeled permanently -- a write that would
    -- raise SIGPIPE has no encoding; see [ReadWrite.write_spec]
  | some (FdEntry.FdFileW p off) =>
      if !(modeled_rw_range buf count) then .CheckUnmodeled
      else
      let bs := write_source i.in_mem buf count
      if !(w_is0 count) && (bs.length == 0)
      then check_ret_only eff (errno_ret EFAULT) m []
      else
        let k :=
          match Fs.fs_lookup (m_fs m) p with
          | none => .CheckUnmodeled
          | some data =>
              if !(modeled_file_gap data off bs) then .CheckUnmodeled
              else
              let m' :=
                with_fds (fd_insert (m_fds m) fd
                            (FdEntry.FdFileW p (off + len_word bs)))
                  (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data off bs)) m)
              if w_is0 count
              then check_ret_only eff (len_word bs) m' []
              else check_ret_only_copyins [(buf, bs.length)] eff (len_word bs) m' []
        if w_is0 count then check_access_ok_zero buf count eff m k else k
  | some (FdEntry.FdFileRW p off) =>
      -- the [FdFileW] arm above, on the O_RDWR kind
      if !(modeled_rw_range buf count) then .CheckUnmodeled
      else
      let bs := write_source i.in_mem buf count
      if !(w_is0 count) && (bs.length == 0)
      then check_ret_only eff (errno_ret EFAULT) m []
      else
        let k :=
          match Fs.fs_lookup (m_fs m) p with
          | none => .CheckUnmodeled
          | some data =>
              if !(modeled_file_gap data off bs) then .CheckUnmodeled
              else
              let m' :=
                with_fds (fd_insert (m_fds m) fd
                            (FdEntry.FdFileRW p (off + len_word bs)))
                  (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data off bs)) m)
              if w_is0 count
              then check_ret_only eff (len_word bs) m' []
              else check_ret_only_copyins [(buf, bs.length)] eff (len_word bs) m' []
        if w_is0 count then check_access_ok_zero buf count eff m k else k
  | some (FdEntry.FdFileA p off) =>
      -- the arm above with the destination moved to end-of-file, the
      -- [modeled_file_gap] guard dropped, and [rw_verify_area]'s test
      -- kept on the fd's real position; see [ReadWrite.write_spec].  The
      -- count gate is the arm above's, [modeled_rw_range], and it does
      -- not subsume the [access_ok] below it -- that argument is in
      -- [ReadWrite.write_spec]'s [FdFileA] arm
      if !(modeled_rw_range buf count) then .CheckUnmodeled
      else if !(access_okb buf (count.toNat : Int))
      then check_ret_only eff (errno_ret EFAULT) m []
      else if rw_pos_einvalb off (count.toNat : Int)
      then check_ret_only eff (errno_ret EINVAL) m []
      else
      let bs := write_source i.in_mem buf count
      if !(w_is0 count) && (bs.length == 0)
      then check_ret_only eff (errno_ret EFAULT) m []
      else
        let k :=
          match Fs.fs_lookup (m_fs m) p with
          | none => .CheckUnmodeled
          | some data =>
              let m' :=
                with_fds (fd_insert (m_fds m) fd
                            (FdEntry.FdFileA p (append_new_pos data bs off)))
                  (with_fs (Fs.fs_set (m_fs m) p
                              (Fs.file_write data (len_word data) bs)) m)
              if w_is0 count
              then check_ret_only eff (len_word bs) m' []
              else check_ret_only_copyins [(buf, bs.length)] eff (len_word bs) m' []
        if w_is0 count then check_access_ok_zero buf count eff m k else k
  | some FdEntry.FdUrandom => check_ret_only eff (errno_ret EBADF) m []
    -- read-only
  | some (FdEntry.FdDevNull _ wr) =>
      if !wr then check_ret_only eff (errno_ret EBADF) m []
      else
      if !(modeled_rw_range buf count) then .CheckUnmodeled
      else check_access_ok_zero buf count eff m
             (check_ret_only eff (BitVec.ofInt 64 (rw_count_clamp count)) m [])
             -- [write_null]: the clamped count, no copy-in
  | some (FdEntry.FdPipe id w) =>
      if !w then check_ret_only eff (errno_ret EBADF) m []
        -- read end: -EBADF
      else
      if !(modeled_rw_range buf count) then .CheckUnmodeled
      else
      if w_is0 count
      then check_access_ok_zero buf count eff m
             (check_ret_only eff (BitVec.ofInt 64 0) m [])
             -- "Null write succeeds"
      else
      if !(pipe_end_live (m_fds m) id false) then .CheckUnmodeled
        -- SIGPIPE
      else
      match pipe_lookup (m_pipes m) id with
      | none => .CheckUnmodeled
      | some st =>
          if !(pipe_write_room st (count.toNat : Int)) then .CheckUnmodeled
          else
          let bs := write_source i.in_mem buf count
          if !(bs.length == word_to_nat count) then .CheckUnmodeled
          else check_ret_only_copyins [(buf, bs.length)] eff count
                 (with_pipes (pipe_insert (m_pipes m) id (pipe_append st bs)) m) []

/- =========================================================================
   pread64 (67) and pwrite64 (68)
   ========================================================================= -/

/-- `[ReadWrite.pread64_spec]`'s acceptor.  The position test comes first
    (`[ppos_einvalb]`, before the descriptor is resolved), then the fd
    kinds that answer -ESPIPE, then the range and position verdicts, and
    finally the file's bytes at `[pos]` — with the model left alone, since
    a pread advances no offset. -/
def check_pread64 (i : SyscallInput) (fd buf count pos : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if ppos_einvalb pos then check_ret_only eff (errno_ret EINVAL) m []
  else
  match fd_lookup (m_fds m) fd with
  | none => check_ret_only eff (errno_ret EBADF) m []
  | some (FdEntry.FdChannel _) => check_ret_only eff (errno_ret ESPIPE) m []
  | some (FdEntry.FdPipe _ _) => check_ret_only eff (errno_ret ESPIPE) m []
  | some (FdEntry.FdSocket _) => check_ret_only eff (errno_ret ESPIPE) m []
  | some (FdEntry.FdFileW _ _) => check_ret_only eff (errno_ret EBADF) m []
  | some (FdEntry.FdFileA _ _) => check_ret_only eff (errno_ret EBADF) m []
  | some (FdEntry.FdDevNull rd _) =>
      if !rd then check_ret_only eff (errno_ret EBADF) m []
      else if !(access_okb buf (count.toNat : Int))
      then check_ret_only eff (errno_ret EFAULT) m []
      else if rw_pos_einvalb pos (count.toNat : Int)
      then check_ret_only eff (errno_ret EINVAL) m []
      else check_ret_only eff (BitVec.ofInt 64 0) m []
  | some FdEntry.FdUrandom =>
      if !(access_okb buf (count.toNat : Int))
      then check_ret_only eff (errno_ret EFAULT) m []
      else if rw_pos_einvalb pos (count.toNat : Int)
      then check_ret_only eff (errno_ret EINVAL) m []
      else check_read_urandom i buf count eff m
  | some FdEntry.FdDir =>
      if !(access_okb buf (count.toNat : Int))
      then check_ret_only eff (errno_ret EFAULT) m []
      else if rw_pos_einvalb pos (count.toNat : Int)
      then check_ret_only eff (errno_ret EINVAL) m []
      else check_ret_only eff (errno_ret EISDIR) m []
  | some (FdEntry.FdFile p _) =>
      if !(access_okb buf (count.toNat : Int))
      then check_ret_only eff (errno_ret EFAULT) m []
      else if rw_pos_einvalb pos (count.toNat : Int)
      then check_ret_only eff (errno_ret EINVAL) m []
      else
      match Fs.fs_lookup (m_fs m) p with
      | none => .CheckUnmodeled
      | some data =>
          let bs := Fs.file_read data pos (BitVec.ofInt 64 (rw_count_clamp count))
          match read_bytes_map i.in_wmem buf (len_word bs) with
          | none =>
              match read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) with
              | none => check_ret_only eff (errno_ret EFAULT) m []
              | some _ => .CheckUnmodeled
                -- partially writable: fail closed
          | some _ =>
              -- the model does not move: a pread advances no offset
              match bs, eff with
              | [], _ => check_ret_only eff (BitVec.ofInt 64 0) m []
              | _ :: _, ⟨ret, [(a, bs')], [], [], [], []⟩ =>
                  if bv_eqb a buf && listN_eqb bs' bs
                     && bv_eqb ret (len_word bs)
                  then .CheckOk m []
                  else .CheckReject
              | _, _ => .CheckReject
  | some (FdEntry.FdFileRW p _) =>
      -- the [FdFile] arm above, on the O_RDWR kind
      if !(access_okb buf (count.toNat : Int))
      then check_ret_only eff (errno_ret EFAULT) m []
      else if rw_pos_einvalb pos (count.toNat : Int)
      then check_ret_only eff (errno_ret EINVAL) m []
      else
      match Fs.fs_lookup (m_fs m) p with
      | none => .CheckUnmodeled
      | some data =>
          let bs := Fs.file_read data pos (BitVec.ofInt 64 (rw_count_clamp count))
          match read_bytes_map i.in_wmem buf (len_word bs) with
          | none =>
              match read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) with
              | none => check_ret_only eff (errno_ret EFAULT) m []
              | some _ => .CheckUnmodeled
          | some _ =>
              match bs, eff with
              | [], _ => check_ret_only eff (BitVec.ofInt 64 0) m []
              | _ :: _, ⟨ret, [(a, bs')], [], [], [], []⟩ =>
                  if bv_eqb a buf && listN_eqb bs' bs
                     && bv_eqb ret (len_word bs)
                  then .CheckOk m []
                  else .CheckReject
              | _, _ => .CheckReject

/-- `[ReadWrite.pwrite64_spec]`'s acceptor: the positional write, which
    reads `[pos]` instead of the descriptor's offset and moves neither.
    An append fd is the one kind whose answer is not the write-only arm's,
    so it declines — see `[ReadWrite.pwrite64_spec]`. -/
def check_pwrite64 (i : SyscallInput) (fd buf count pos : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if ppos_einvalb pos then check_ret_only eff (errno_ret EINVAL) m []
  else
  match fd_lookup (m_fds m) fd with
  | none => check_ret_only eff (errno_ret EBADF) m []
  | some (FdEntry.FdChannel _) => check_ret_only eff (errno_ret ESPIPE) m []
  | some (FdEntry.FdPipe _ _) => check_ret_only eff (errno_ret ESPIPE) m []
  | some (FdEntry.FdSocket _) => check_ret_only eff (errno_ret ESPIPE) m []
  | some (FdEntry.FdFile _ _) => check_ret_only eff (errno_ret EBADF) m []
  | some FdEntry.FdDir => check_ret_only eff (errno_ret EBADF) m []
  | some (FdEntry.FdFileA _ _) => .CheckUnmodeled
    -- see [ReadWrite.pwrite64_spec]
  | some FdEntry.FdUrandom => check_ret_only eff (errno_ret EBADF) m []
    -- read-only
  | some (FdEntry.FdDevNull _ wr) =>
      if !wr then check_ret_only eff (errno_ret EBADF) m []
      else if !(access_okb buf (count.toNat : Int))
      then check_ret_only eff (errno_ret EFAULT) m []
      else if rw_pos_einvalb pos (count.toNat : Int)
      then check_ret_only eff (errno_ret EINVAL) m []
      else check_ret_only eff (BitVec.ofInt 64 (rw_count_clamp count)) m []
  | some (FdEntry.FdFileW p _) =>
      if !(access_okb buf (count.toNat : Int))
      then check_ret_only eff (errno_ret EFAULT) m []
      else if rw_pos_einvalb pos (count.toNat : Int)
      then check_ret_only eff (errno_ret EINVAL) m []
      else
      let bs := write_source i.in_mem buf count
        -- no count gate: see [ReadWrite.pwrite64_spec]
      if !(w_is0 count) && (bs.length == 0)
      then check_ret_only eff (errno_ret EFAULT) m []
      else
      match Fs.fs_lookup (m_fs m) p with
      | none => .CheckUnmodeled
      | some data =>
          if !(modeled_file_gap data pos bs) then .CheckUnmodeled
          else
          let m' := with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data pos bs)) m
          if w_is0 count
          then check_ret_only eff (len_word bs) m' []
          else check_ret_only_copyins [(buf, bs.length)] eff (len_word bs) m' []
  | some (FdEntry.FdFileRW p _) =>
      -- the [FdFileW] arm above, on the O_RDWR kind
      if !(access_okb buf (count.toNat : Int))
      then check_ret_only eff (errno_ret EFAULT) m []
      else if rw_pos_einvalb pos (count.toNat : Int)
      then check_ret_only eff (errno_ret EINVAL) m []
      else
      let bs := write_source i.in_mem buf count
      if !(w_is0 count) && (bs.length == 0)
      then check_ret_only eff (errno_ret EFAULT) m []
      else
      match Fs.fs_lookup (m_fs m) p with
      | none => .CheckUnmodeled
      | some data =>
          if !(modeled_file_gap data pos bs) then .CheckUnmodeled
          else
          let m' := with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data pos bs)) m
          if w_is0 count
          then check_ret_only eff (len_word bs) m' []
          else check_ret_only_copyins [(buf, bs.length)] eff (len_word bs) m' []

/- =========================================================================
   writev (66)
   ========================================================================= -/

/-- `[ReadWrite.writev_spec]`'s acceptor.  The iovec array is imported and
    its descriptors are the copy-in ledger on every arm — including the
    errno arms, which is why they use `[check_ret_only_copyins]` rather
    than `[check_ret_only]`.  The channel arm then takes a (possibly
    short) nonempty prefix of the gathered bytes; the file arms transfer
    the whole gathering at the descriptor's offset (or at end-of-file for
    an append fd). -/
def check_writev (i : SyscallInput) (fd iov iovcnt : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match fd_lookup (m_fds m) fd with
  | none => check_ret_only eff (errno_ret EBADF) m []
  | some (FdEntry.FdFile _ _) => check_ret_only eff (errno_ret EBADF) m []
  | some FdEntry.FdDir => check_ret_only eff (errno_ret EBADF) m []
  | some (FdEntry.FdSocket _) => .CheckUnmodeled
  | some (FdEntry.FdChannel ch) =>
      if w_is0 ch then check_ret_only eff (errno_ret EBADF) m []
      else
        match import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
        | .ImpFault => check_ret_only_copyins
            (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
            eff (errno_ret EFAULT) m []
        | .ImpInval => check_ret_only_copyins
            (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
            eff (errno_ret EINVAL) m []
        | .ImpOk iovs0 =>
            let total := iovs_total (cap_iovecs iovs0)
            let bs := writev_gathered i.in_mem iovs0
            if total == 0
            then check_ret_only_copyins
              (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
              eff (BitVec.ofInt 64 0) m []
            else if bs.length == 0
            then check_ret_only_copyins
              (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
              eff (errno_ret EFAULT) m []
            else if addr_is_error_b (len_word bs) then .CheckUnmodeled
            else
              -- as for [check_write]: the claimed return picks the
              -- delivered (possibly short) prefix; an error-encoded
              -- return is never a delivered length
              match eff with
              | ⟨ret, [], [], [], [], copyins⟩ =>
                  if decide (1 ≤ (ret.toNat : Int))
                     && decide ((ret.toNat : Int) ≤ (bs.length : Int))
                     && !(addr_is_error_b ret)
                  then
                    -- a nested [if] rather than a fourth [&&]: [vm_compute]
                    -- evaluates every operand of [andb], and this operand
                    -- converts [ret] to a unary numeral -- bounded by
                    -- [length bs] once the range test has passed, and by
                    -- nothing for an errno-encoded return
                    if access_ranges_eqb copyins
                         (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt) ++
                          iov_prefix_accesses (cap_iovecs iovs0) ret.toNat)
                    then .CheckOk m (bs.take ret.toNat |>.map (event.WriteEv ch))
                    else .CheckReject
                  else .CheckReject
              | _ => .CheckReject
  | some (FdEntry.FdFileW p off) =>
      match import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
      | .ImpFault => check_ret_only_copyins
          (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
          eff (errno_ret EFAULT) m []
      | .ImpInval => check_ret_only_copyins
          (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
          eff (errno_ret EINVAL) m []
      | .ImpOk iovs0 =>
          let total := iovs_total (cap_iovecs iovs0)
          let bs := writev_gathered i.in_mem iovs0
          if total == 0
          then check_ret_only_copyins
            (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
            eff (BitVec.ofInt 64 0) m []
          else if rw_pos_einvalb off total
          then check_ret_only_copyins
            (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
            eff (errno_ret EINVAL) m []
          else if bs.length == 0
          then check_ret_only_copyins
            (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
            eff (errno_ret EFAULT) m []
          else
            match Fs.fs_lookup (m_fs m) p with
            | none => .CheckUnmodeled
            | some data =>
                if !(modeled_file_gap data off bs) then .CheckUnmodeled
                else if addr_is_error_b (len_word bs) then .CheckUnmodeled
                else check_ret_only_copyins
                  (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt) ++
                   iov_prefix_accesses (cap_iovecs iovs0) bs.length)
                  eff (len_word bs)
                  (with_fds (fd_insert (m_fds m) fd
                               (FdEntry.FdFileW p (off + len_word bs)))
                     (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data off bs)) m))
                  []
  | some (FdEntry.FdFileRW p off) =>
      -- the [FdFileW] arm above, on the O_RDWR kind
      match import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
      | .ImpFault => check_ret_only_copyins
          (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
          eff (errno_ret EFAULT) m []
      | .ImpInval => check_ret_only_copyins
          (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
          eff (errno_ret EINVAL) m []
      | .ImpOk iovs0 =>
          let total := iovs_total (cap_iovecs iovs0)
          let bs := writev_gathered i.in_mem iovs0
          if total == 0
          then check_ret_only_copyins
            (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
            eff (BitVec.ofInt 64 0) m []
          else if rw_pos_einvalb off total
          then check_ret_only_copyins
            (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
            eff (errno_ret EINVAL) m []
          else if bs.length == 0
          then check_ret_only_copyins
            (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
            eff (errno_ret EFAULT) m []
          else
            match Fs.fs_lookup (m_fs m) p with
            | none => .CheckUnmodeled
            | some data =>
                if !(modeled_file_gap data off bs) then .CheckUnmodeled
                else if addr_is_error_b (len_word bs) then .CheckUnmodeled
                else check_ret_only_copyins
                  (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt) ++
                   iov_prefix_accesses (cap_iovecs iovs0) bs.length)
                  eff (len_word bs)
                  (with_fds (fd_insert (m_fds m) fd
                               (FdEntry.FdFileRW p (off + len_word bs)))
                     (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data off bs)) m))
                  []
  | some (FdEntry.FdFileA p off) =>
      -- [rw_pos_einvalb] still reads [off], the fd's real position; only
      -- the destination moves.  See [ReadWrite.writev_spec]'s [FdFileA] arm
      match import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
      | .ImpFault => check_ret_only_copyins
          (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
          eff (errno_ret EFAULT) m []
      | .ImpInval => check_ret_only_copyins
          (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
          eff (errno_ret EINVAL) m []
      | .ImpOk iovs0 =>
          let total := iovs_total (cap_iovecs iovs0)
          let bs := writev_gathered i.in_mem iovs0
          if total == 0
          then check_ret_only_copyins
            (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
            eff (BitVec.ofInt 64 0) m []
          else if rw_pos_einvalb off total
          then check_ret_only_copyins
            (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
            eff (errno_ret EINVAL) m []
          else if bs.length == 0
          then check_ret_only_copyins
            (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
            eff (errno_ret EFAULT) m []
          else
            match Fs.fs_lookup (m_fs m) p with
            | none => .CheckUnmodeled
            | some data =>
                if addr_is_error_b (len_word bs) then .CheckUnmodeled
                else check_ret_only_copyins
                  (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt) ++
                   iov_prefix_accesses (cap_iovecs iovs0) bs.length)
                  eff (len_word bs)
                  (with_fds (fd_insert (m_fds m) fd
                               (FdEntry.FdFileA p (append_new_pos data bs off)))
                     (with_fs (Fs.fs_set (m_fs m) p
                                 (Fs.file_write data (len_word data) bs)) m))
                  []
  | some (FdEntry.FdPipe _ w) =>
      if !w then check_ret_only eff (errno_ret EBADF) m []
        -- read end: -EBADF
      else
        match import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
        | .ImpFault => check_ret_only_copyins
            (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
            eff (errno_ret EFAULT) m []
        | .ImpInval => check_ret_only_copyins
            (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
            eff (errno_ret EINVAL) m []
        | .ImpOk iovs0 =>
            if (iovs_total (cap_iovecs iovs0)) == 0
            then check_ret_only_copyins
              (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
              eff (BitVec.ofInt 64 0) m []
            else .CheckUnmodeled
              -- vectored pipe writes are unmodeled
  | some FdEntry.FdUrandom => check_ret_only eff (errno_ret EBADF) m []
    -- read-only
  | some (FdEntry.FdDevNull _ wr) =>
      if !wr then check_ret_only eff (errno_ret EBADF) m []
      else
        match import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
        | .ImpFault => check_ret_only_copyins
            (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
            eff (errno_ret EFAULT) m []
        | .ImpInval => check_ret_only_copyins
            (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
            eff (errno_ret EINVAL) m []
        | .ImpOk iovs0 =>
            check_ret_only_copyins
              (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
              eff (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs0))) m []
              -- [write_iter_null]: the capped aggregate, the iovec array
              -- the only copy-in

/- =========================================================================
   readv (65)
   ========================================================================= -/

/-- The checker-side spelling of a readv fail-closed gap: a plain
    decline.  See [ReadWrite.readv_buf_gap]. -/
def check_readv_gap : check_result := .CheckUnmodeled

/-- `[ReadWrite.readv_imported]`'s acceptor: the descriptor kind has
    already passed `[readable_fd]`, and the iovec array has already been
    imported.  Every arm either computes the exactly-determined delivery
    (a channel or socket takes a nonempty prefix of its script; a file
    takes its whole readable range and does NOT move the descriptor's
    offset in the effect, only in the returned model) or declines. -/
def check_readv_imported (i : SyscallInput) (fd : word)
    (r : ReadableFd) (iovs0 : List (word × word))
    (eff : SyscallEffect) (m : Model) : check_result :=
  let iovs := cap_iovecs iovs0
  let total := iovs_total iovs
  if total == 0 then check_ret_only eff (BitVec.ofInt 64 0) m []
  else
  match r with
  | .RdChannel ch =>
      match m_stdin m 0 with
      | none => check_ret_only eff (BitVec.ofInt 64 0) m []
      | some _ =>
          match scatter_iovecs i.in_wmem iovs [BitVec.ofInt 8 0] with
          | none => check_ret_only eff (errno_ret EFAULT) m []
          | some _ =>
              match scatter_iovecs i.in_wmem iovs
                      (stream_take_z (m_stdin m) total).1 with
              | none => check_readv_gap
                -- partially writable destination
              | some _ =>
                  match eff with
                  | ⟨ret, writes, [], [], [], []⟩ =>
                      let bs := (writes.map Prod.snd).flatten
                      match scatter_iovecs i.in_wmem iovs bs with
                      | none => .CheckReject
                      | some expected =>
                          if bv_eqb ret (len_word bs)
                             && writes_eqb writes expected
                             && decide (1 ≤ (bs.length : Int))
                             && decide ((bs.length : Int) ≤ total)
                             && listN_eqb (stream_take (m_stdin m) bs.length).1 bs
                          then .CheckOk
                                 (with_stdin
                                    (stream_take (m_stdin m) bs.length).2 m)
                                 (bs.map (event.ReadEv ch))
                          else .CheckReject
                  | _ => .CheckReject
  | .RdSocket sk =>
      match sk with
      | .SkConnected peer ch rx =>
          match rx 0 with
          | .fin => check_ret_only eff (BitVec.ofInt 64 0) m []
          | .rst =>
              check_ret_only eff (errno_ret ECONNRESET)
                (with_fds (fd_insert (m_fds m) fd
                             (FdEntry.FdSocket (SockState.SkReset peer ch))) m) []
          | .timedOut =>
              check_ret_only eff (errno_ret ETIMEDOUT)
                (with_fds (fd_insert (m_fds m) fd
                             (FdEntry.FdSocket (SockState.SkReset peer ch))) m) []
          | .cons _ =>
              match scatter_iovecs i.in_wmem iovs [BitVec.ofInt 8 0] with
              | none => check_ret_only eff (errno_ret EFAULT) m []
              | some _ =>
                  match scatter_iovecs i.in_wmem iovs
                          (net_take_z rx total).1 with
                  | none => check_readv_gap
                    -- partially writable destination
                  | some _ =>
                      -- exactly the channel shape, on the connection's
                      -- script: the ledger is the canonical scatter of the
                      -- delivered bytes, so the writes determine them
                      match eff with
                      | ⟨ret, writes, [], [], [], []⟩ =>
                          let bs := (writes.map Prod.snd).flatten
                          match scatter_iovecs i.in_wmem iovs bs with
                          | none => .CheckReject
                          | some expected =>
                              if bv_eqb ret (len_word bs)
                                 && writes_eqb writes expected
                                 && decide (1 ≤ (bs.length : Int))
                                 && decide ((bs.length : Int) ≤ total)
                                 && listN_eqb (net_take rx bs.length).1 bs
                              then .CheckOk
                                     (with_fds
                                        (fd_insert (m_fds m) fd
                                           (FdEntry.FdSocket
                                              (SockState.SkConnected peer ch
                                                 (net_take rx bs.length).2))) m)
                                     (bs.map (event.ReadEv ch))
                              else .CheckReject
                      | _ => .CheckReject
      | .SkReset _ _ => check_ret_only eff (BitVec.ofInt 64 0) m []
      | _ => check_ret_only eff (errno_ret ENOTCONN) m []
  | .RdPipe _ => check_readv_gap
    -- vectored pipe reads are unmodeled
  | .RdDevNull => check_ret_only eff (BitVec.ofInt 64 0) m []
    -- [read_iter_null]: 0
  | .RdUrandom => check_readv_gap
    -- vectored device reads decline: [ReadWrite.readv_imported]
  | .RdDir => check_ret_only eff (errno_ret EISDIR) m []
  | .RdFile p off =>
      match Fs.fs_lookup (m_fs m) p with
      | none => check_readv_gap
      | some data =>
          if rw_pos_einvalb off total then check_ret_only eff (errno_ret EINVAL) m []
          else
          let bs := Fs.file_read data off (BitVec.ofInt 64 total)
          match scatter_iovecs i.in_wmem iovs bs with
          | some writes =>
              if addr_is_error_b (len_word bs) then check_readv_gap
              else
              match eff with
              | ⟨ret, writes', [], [], [], []⟩ =>
                  if bv_eqb ret (len_word bs) && writes_eqb writes' writes
                  then .CheckOk
                         (with_fds (fd_insert (m_fds m) fd
                                      (FdEntry.FdFile p (off + len_word bs))) m) []
                  else .CheckReject
              | _ => .CheckReject
          | none =>
              match scatter_iovecs i.in_wmem iovs [BitVec.ofInt 8 0] with
              | none => check_ret_only eff (errno_ret EFAULT) m []
              | some _ => check_readv_gap
  | .RdFileRW p off =>
      -- the [RdFile] arm above, on the O_RDWR kind
      match Fs.fs_lookup (m_fs m) p with
      | none => check_readv_gap
      | some data =>
          if rw_pos_einvalb off total then check_ret_only eff (errno_ret EINVAL) m []
          else
          let bs := Fs.file_read data off (BitVec.ofInt 64 total)
          match scatter_iovecs i.in_wmem iovs bs with
          | some writes =>
              if addr_is_error_b (len_word bs) then check_readv_gap
              else
              match eff with
              | ⟨ret, writes', [], [], [], []⟩ =>
                  if bv_eqb ret (len_word bs) && writes_eqb writes' writes
                  then .CheckOk
                         (with_fds (fd_insert (m_fds m) fd
                                      (FdEntry.FdFileRW p (off + len_word bs))) m) []
                  else .CheckReject
              | _ => .CheckReject
          | none =>
              match scatter_iovecs i.in_wmem iovs [BitVec.ofInt 8 0] with
              | none => check_ret_only eff (errno_ret EFAULT) m []
              | some _ => check_readv_gap

/-- `[ReadWrite.readv_spec]`'s acceptor: the `[FMODE_READ]` gate
    (`[readable_fd]`), then the heap-backed count band, then the iovec
    import — whose descriptors are the copy-in ledger — and finally the
    imported-vector body on the effect with that ledger stripped. -/
def check_readv (i : SyscallInput) (fd iov iovcnt : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match fd_lookup (m_fds m) fd with
  | none => check_ret_only eff (errno_ret EBADF) m []
  | some e =>
      match readable_fd e with
      | none => check_ret_only eff (errno_ret EBADF) m []
        -- the read end has a [RdPipe]; only the O_WRONLY write end
        -- reaches this arm, where -EBADF is the kernel's own answer
      | some r =>
          if readv_heap_iovecb iovcnt then check_readv_gap
          else
            match import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
            | .ImpFault => check_ret_only_copyins
                (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
                eff (errno_ret EFAULT) m []
            | .ImpInval => check_ret_only_copyins
                (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
                eff (errno_ret EINVAL) m []
            | .ImpOk iovs0 =>
                check_copyin_prefix
                  (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt)) eff
                  (check_readv_imported i fd r iovs0
                     (strip_copyin_prefix
                        (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
                        eff) m)

/- -------------------------------------------------------------------------
   `check_readv_imported`'s `m_vmmaps` frame (PUBLIC)

   [Checks/VmMapsDisjoint.lean] must show that each checker leaves
   [m_vmmaps] alone.  Its `vm_frame` loop does that by unfolding the
   checker and casing the result hypothesis, and the imported-vector body
   is where that loop needs the fact stated, so it is stated HERE, next to
   the checker it is about, exactly as `Checks/Sys/Fs/Open.lean`'s
   `check_ftruncate_file_arm_frame` and `Checks/Sys/Fs/Namei.lean`'s
   `check_unlinkat_body_frame` are stated next to theirs.

   Why it cannot come from the `*_sound_ok` next door, and why the wrapper
   lemmas do not substitute for it: `check_copyin_prefix_model` (like
   every other `*_model` inversion) returns an equality of the INNER
   result, not `m' = m`, so it hands the outer frame nothing at this call
   site — the model equality has to be produced by walking the body.

   The walk is the checker side of [check_readv_imported_sound_ok]
   (`ReadWrite/Vec.lean`), with the spec dropped: every accepting branch
   hands back either the caller's model or a `with_stdin`/`with_fds` update
   of it, and a projection of a structure update is the old projection by
   `rfl`.  The two model-state tests (`m_stdin m 0`, `Fs.fs_lookup
   (m_fs m) p`) and the three `scatter_iovecs` imports are `generalize`d,
   never `split`: `split` generalises the stuck `if` under them.
   ------------------------------------------------------------------------- -/

/-- The imported-vector body of `readv` leaves [m_vmmaps] alone: no branch
    of it writes to `m_vm`, and the three that rebuild the model rebuild
    `m_stdin` or `m_fds` only.  Public because
    [Checks/VmMapsDisjoint.lean] cites it as a term. -/
theorem check_readv_imported_frame (i : SyscallInput) (fd : word)
    (e : ReadableFd) (iovs0 : List (word × word)) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (H : check_readv_imported i fd e iovs0 eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold check_readv_imported at H
  try dsimp only at H
  by_cases hz : (iovs_total (cap_iovecs iovs0) == 0) = true
  · rw [ite_eq_left hz] at H
    exact check_ret_only_frame eff (BitVec.ofInt 64 0) m m' evs H
  · rw [ite_eq_right hz] at H
    try dsimp only at H
    cases e with
    | RdChannel ch =>
      try dsimp only at H
      generalize hs : m_stdin m 0 = st at H
      cases st with
      | none => exact check_ret_only_frame eff (BitVec.ofInt 64 0) m m' evs H
      | some b0 =>
        try dsimp only at H
        generalize hone : scatter_iovecs i.in_wmem (cap_iovecs iovs0)
          [BitVec.ofInt 8 0] = one at H
        cases one with
        | none => exact check_ret_only_frame eff (errno_ret EFAULT) m m' evs H
        | some one =>
          try dsimp only at H
          generalize hneed : scatter_iovecs i.in_wmem (cap_iovecs iovs0)
            (stream_take_z (m_stdin m) (iovs_total (cap_iovecs iovs0))).1 = need at H
          cases need with
          | none =>
            try dsimp only at H
            unfold check_readv_gap at H
            exact nomatch H
          | some need =>
            try dsimp only at H
            obtain ⟨ret, writes, zs, us, cs, copyins⟩ := eff
            cases zs <;> cases us <;> cases cs <;> cases copyins
            case nil.nil.nil.nil =>
              try dsimp only at H
              generalize hbs : (writes.map Prod.snd).flatten = bs at H
              try dsimp only at H
              generalize hsc : scatter_iovecs i.in_wmem (cap_iovecs iovs0) bs = sc at H
              cases sc with
              | none =>
                try dsimp only at H
                exact nomatch H
              | some expected =>
                try dsimp only at H
                by_cases hgood : (bv_eqb ret (len_word bs)
                    && writes_eqb writes expected
                    && decide (1 ≤ (bs.length : Int))
                    && decide ((bs.length : Int) ≤ iovs_total (cap_iovecs iovs0))
                    && listN_eqb (stream_take (m_stdin m) bs.length).1 bs) = true
                · rw [ite_eq_left hgood] at H
                  cases H
                  rfl
                · rw [ite_eq_right hgood] at H
                  exact nomatch H
            all_goals (try dsimp only at H); all_goals (try exact nomatch H)
    | RdSocket sk =>
      try dsimp only at H
      cases sk with
      | SkFresh => exact check_ret_only_frame eff (errno_ret ENOTCONN) m m' evs H
      | SkBound => exact check_ret_only_frame eff (errno_ret ENOTCONN) m m' evs H
      | SkListening => exact check_ret_only_frame eff (errno_ret ENOTCONN) m m' evs H
      | SkReset peer ch => exact check_ret_only_frame eff (BitVec.ofInt 64 0) m m' evs H
      | SkConnected peer ch rx =>
        try dsimp only at H
        generalize hrx : rx 0 = st at H
        cases st with
        | fin => exact check_ret_only_frame eff (BitVec.ofInt 64 0) m m' evs H
        | rst =>
          exact check_ret_only_frame eff (errno_ret ECONNRESET)
            (with_fds (fd_insert (m_fds m) fd
              (FdEntry.FdSocket (SockState.SkReset peer ch))) m) m' evs H
        | timedOut =>
          exact check_ret_only_frame eff (errno_ret ETIMEDOUT)
            (with_fds (fd_insert (m_fds m) fd
              (FdEntry.FdSocket (SockState.SkReset peer ch))) m) m' evs H
        | cons b0 =>
          try dsimp only at H
          generalize hone : scatter_iovecs i.in_wmem (cap_iovecs iovs0)
            [BitVec.ofInt 8 0] = one at H
          cases one with
          | none => exact check_ret_only_frame eff (errno_ret EFAULT) m m' evs H
          | some one =>
            try dsimp only at H
            generalize hneed : scatter_iovecs i.in_wmem (cap_iovecs iovs0)
              (net_take_z rx (iovs_total (cap_iovecs iovs0))).1 = need at H
            cases need with
            | none =>
              try dsimp only at H
              unfold check_readv_gap at H
              exact nomatch H
            | some need =>
              try dsimp only at H
              obtain ⟨ret, writes, zs, us, cs, copyins⟩ := eff
              cases zs <;> cases us <;> cases cs <;> cases copyins
              case nil.nil.nil.nil =>
                try dsimp only at H
                generalize hbs : (writes.map Prod.snd).flatten = bs at H
                try dsimp only at H
                generalize hsc : scatter_iovecs i.in_wmem (cap_iovecs iovs0) bs = sc at H
                cases sc with
                | none =>
                  try dsimp only at H
                  exact nomatch H
                | some expected =>
                  try dsimp only at H
                  by_cases hgood : (bv_eqb ret (len_word bs)
                      && writes_eqb writes expected
                      && decide (1 ≤ (bs.length : Int))
                      && decide ((bs.length : Int) ≤ iovs_total (cap_iovecs iovs0))
                      && listN_eqb (net_take rx bs.length).1 bs) = true
                  · rw [ite_eq_left hgood] at H
                    cases H
                    rfl
                  · rw [ite_eq_right hgood] at H
                    exact nomatch H
              all_goals (try dsimp only at H); all_goals (try exact nomatch H)
    | RdPipe id =>
      try dsimp only at H
      unfold check_readv_gap at H
      exact nomatch H
    | RdDevNull => exact check_ret_only_frame eff (BitVec.ofInt 64 0) m m' evs H
    | RdUrandom =>
      try dsimp only at H
      unfold check_readv_gap at H
      exact nomatch H
    | RdDir => exact check_ret_only_frame eff (errno_ret EISDIR) m m' evs H
    | RdFile p off =>
      try dsimp only at H
      generalize hfs : Fs.fs_lookup (m_fs m) p = lk at H
      cases lk with
      | none =>
        try dsimp only at H
        unfold check_readv_gap at H
        exact nomatch H
      | some data =>
        try dsimp only at H
        by_cases hpos : rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = true
        · rw [ite_eq_left hpos] at H
          exact check_ret_only_frame eff (errno_ret EINVAL) m m' evs H
        · rw [ite_eq_right hpos] at H
          try dsimp only at H
          generalize hsc : scatter_iovecs i.in_wmem (cap_iovecs iovs0)
            (Fs.file_read data off (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs0)))) = sc
            at H
          cases sc with
          | some writes =>
            try dsimp only at H
            by_cases hae : addr_is_error_b (len_word (Fs.file_read data off
                (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs0))))) = true
            · rw [ite_eq_left hae] at H
              unfold check_readv_gap at H
              exact nomatch H
            · rw [ite_eq_right hae] at H
              try dsimp only at H
              obtain ⟨ret, writes', zs, us, cs, copyins⟩ := eff
              cases zs <;> cases us <;> cases cs <;> cases copyins
              case nil.nil.nil.nil =>
                try dsimp only at H
                by_cases hgood : (bv_eqb ret (len_word (Fs.file_read data off
                    (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs0)))))
                    && writes_eqb writes' writes) = true
                · rw [ite_eq_left hgood] at H
                  cases H
                  rfl
                · rw [ite_eq_right hgood] at H
                  exact nomatch H
              all_goals (try dsimp only at H); all_goals (try exact nomatch H)
          | none =>
            try dsimp only at H
            generalize hone : scatter_iovecs i.in_wmem (cap_iovecs iovs0)
              [BitVec.ofInt 8 0] = one at H
            cases one with
            | none => exact check_ret_only_frame eff (errno_ret EFAULT) m m' evs H
            | some one =>
              try dsimp only at H
              unfold check_readv_gap at H
              exact nomatch H
    | RdFileRW p off =>
      try dsimp only at H
      generalize hfs : Fs.fs_lookup (m_fs m) p = lk at H
      cases lk with
      | none =>
        try dsimp only at H
        unfold check_readv_gap at H
        exact nomatch H
      | some data =>
        try dsimp only at H
        by_cases hpos : rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = true
        · rw [ite_eq_left hpos] at H
          exact check_ret_only_frame eff (errno_ret EINVAL) m m' evs H
        · rw [ite_eq_right hpos] at H
          try dsimp only at H
          generalize hsc : scatter_iovecs i.in_wmem (cap_iovecs iovs0)
            (Fs.file_read data off (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs0)))) = sc
            at H
          cases sc with
          | some writes =>
            try dsimp only at H
            by_cases hae : addr_is_error_b (len_word (Fs.file_read data off
                (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs0))))) = true
            · rw [ite_eq_left hae] at H
              unfold check_readv_gap at H
              exact nomatch H
            · rw [ite_eq_right hae] at H
              try dsimp only at H
              obtain ⟨ret, writes', zs, us, cs, copyins⟩ := eff
              cases zs <;> cases us <;> cases cs <;> cases copyins
              case nil.nil.nil.nil =>
                try dsimp only at H
                by_cases hgood : (bv_eqb ret (len_word (Fs.file_read data off
                    (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs0)))))
                    && writes_eqb writes' writes) = true
                · rw [ite_eq_left hgood] at H
                  cases H
                  rfl
                · rw [ite_eq_right hgood] at H
                  exact nomatch H
              all_goals (try dsimp only at H); all_goals (try exact nomatch H)
          | none =>
            try dsimp only at H
            generalize hone : scatter_iovecs i.in_wmem (cap_iovecs iovs0)
              [BitVec.ofInt 8 0] = one at H
            cases one with
            | none => exact check_ret_only_frame eff (errno_ret EFAULT) m m' evs H
            | some one =>
              try dsimp only at H
              unfold check_readv_gap at H
              exact nomatch H

/- The `vm_compute` examples: the copy-in ledger a readv/writev reports,
   on concrete memories. -/

/-- The ledger a two-descriptor readv reports, for a memory whose iovec
    descriptors are readable: two 16-byte ranges, 0x2000 and 0x2010. -/
theorem readv_copyin_reports_the_iovec_table :
    ((import_iovecs_accesses (fun _ => some (0 : byte)) (0x2000 : word) 2).map
      (fun p => ((p.1.toNat : Int), p.2)))
      = [((0x2000 : Int), 16), ((0x2010 : Int), 16)] := by decide

/-- A memory image holding one iovec descriptor at 0x2000: base 0x3000,
    length 2.  Test scaffolding for the two checks below. -/
def one_iovec_mem : word → Option byte :=
  LinuxSem.LinuxProcessSem.RiscvSemantics.write_to_mem (fun _ => some 0) 0x2000
    (Z_to_le_bytes 8 0x3000 ++ Z_to_le_bytes 8 2)

/-- The writev ledger: the descriptor range for the array, then the
    delivered data's range. -/
theorem writev_copyin_reports_table_and_delivered_data :
    ((copy_iovecs_accesses one_iovec_mem 0x2000 1 ++
      iov_prefix_accesses [(0x3000, 2)] 2).map
      (fun p => ((p.1.toNat : Int), p.2)))
      = [((0x2000 : Int), 16), ((0x3000 : Int), 2)] := by decide

/-- A memory image whose first iovec descriptor names an unreadable base
    and an impossible length.  Test scaffolding, as above. -/
def invalid_first_iovec_mem : word → Option byte :=
  LinuxSem.LinuxProcessSem.RiscvSemantics.write_to_mem (fun _ => some 0) 0x2000
    (Z_to_le_bytes 8 0x3000 ++ Z_to_le_bytes 8 (2 ^ 63))

/-- Only the attempted descriptor is charged. -/
theorem invalid_iovec_charges_only_the_attempted_descriptor :
    copy_iovecs_accesses invalid_first_iovec_mem 0x2000 2
      = [((0x2000 : word), 16)] := by decide

/- =========================================================================
   lseek (62)
   ========================================================================= -/

/-- `[ReadWrite.lseek_spec]`'s acceptor.  `ksys_lseek` decides the fd and
    the `[whence ≤ SEEK_MAX]` test before it reaches any `[.llseek]`, so a
    bad `[whence]` is -EINVAL whatever the descriptor is; the four file
    kinds then move the offset through `[lseek_base]`/`[lseek_dest]`, and
    an out-of-range result is -EINVAL (`[lseek_dest]`'s `none`).
    SEEK_DATA/SEEK_HOLE decline (`[lseek_base]`'s `none`), and so does a
    directory. -/
def check_lseek (fd off whence : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  match fd_lookup (m_fds m) fd with
  | none => check_ret_only eff (errno_ret EBADF) m []
  | some e =>
      if decide (SEEK_MAX < (whence.toNat : Int))
      then check_ret_only eff (errno_ret EINVAL) m []
        -- before the fd's kind: see [ReadWrite.lseek_spec]
      else
      match e with
      | .FdChannel _ => check_ret_only eff (errno_ret ESPIPE) m []
      | .FdSocket _ => check_ret_only eff (errno_ret ESPIPE) m []
        -- a socket file has no [.llseek] and never gets FMODE_LSEEK, so
        -- [vfs_llseek] is -ESPIPE -- after the -EINVAL above, which
        -- [ksys_lseek] decides first
      | .FdPipe _ _ => check_ret_only eff (errno_ret ESPIPE) m []
      | .FdDevNull _ _ => check_ret_only eff (BitVec.ofInt 64 0) m []
        -- [null_lseek]: 0
      | .FdUrandom => check_ret_only eff (BitVec.ofInt 64 0) m []
        -- [noop_llseek]: the pinned 0
      | .FdDir => .CheckUnmodeled
        -- unmodeled: see [ReadWrite.lseek_spec]
      | .FdFile p cur =>
          match Fs.fs_lookup (m_fs m) p with
          | none => .CheckUnmodeled
          | some data =>
              match lseek_base whence cur (len_word data) with
              | none => .CheckUnmodeled
                -- SEEK_DATA/SEEK_HOLE: unmodeled
              | some base =>
                  match lseek_dest base off with
                  | none => check_ret_only eff (errno_ret EINVAL) m []
                  | some r =>
                      check_ret_only eff r
                        (with_fds (fd_insert (m_fds m) fd (FdEntry.FdFile p r)) m) []
      | .FdFileW p cur =>
          match Fs.fs_lookup (m_fs m) p with
          | none => .CheckUnmodeled
          | some data =>
              match lseek_base whence cur (len_word data) with
              | none => .CheckUnmodeled
              | some base =>
                  match lseek_dest base off with
                  | none => check_ret_only eff (errno_ret EINVAL) m []
                  | some r =>
                      check_ret_only eff r
                        (with_fds (fd_insert (m_fds m) fd (FdEntry.FdFileW p r)) m) []
      | .FdFileRW p cur =>
          -- the [FdFileW] arm above, on the O_RDWR kind
          match Fs.fs_lookup (m_fs m) p with
          | none => .CheckUnmodeled
          | some data =>
              match lseek_base whence cur (len_word data) with
              | none => .CheckUnmodeled
              | some base =>
                  match lseek_dest base off with
                  | none => check_ret_only eff (errno_ret EINVAL) m []
                  | some r =>
                      check_ret_only eff r
                        (with_fds (fd_insert (m_fds m) fd (FdEntry.FdFileRW p r)) m) []
      | .FdFileA p cur =>
          match Fs.fs_lookup (m_fs m) p with
          | none => .CheckUnmodeled
          | some data =>
              match lseek_base whence cur (len_word data) with
              | none => .CheckUnmodeled
              | some base =>
                  match lseek_dest base off with
                  | none => check_ret_only eff (errno_ret EINVAL) m []
                  | some r =>
                      check_ret_only eff r
                        (with_fds (fd_insert (m_fds m) fd (FdEntry.FdFileA p r)) m) []

theorem readv_heap_gap_no_ok (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (m' : Model) (evs : List event)
    (H : readv_heap_gap i m (.ok eff m' evs)) : False := by
  unfold readv_heap_gap readv_buf_gap unmodeled at H
  exact nomatch H

/- =========================================================================
   read_urandom (the acceptor of [ReadWrite.read_urandom])
   ========================================================================= -/

/-- Invert one `seqSpec (modifySpec f) (pure x)` step into its three
    consequents. -/
theorem seqSpec_modify_pure_ok_inv (f : Model → Model) (x : SyscallEffect)
    (i : SyscallInput) (m : Model) (y : SyscallEffect) (m' : Model)
    (evs : List event)
    (H : seqSpec (modifySpec f) (pure x) i m (.ok y m' evs)) :
    y = x ∧ m' = f m ∧ evs = [] := by
  obtain ⟨u, m1, evs1, evs2, hm, hp, hevs⟩ := H
  cases hm
  cases hp
  simp only [List.nil_append] at hevs
  subst hevs
  exact ⟨rfl, rfl, rfl⟩

/-- The same step never declines.  Stated here, as above. -/
theorem seqSpec_modify_pure_unmodeled_false (f : Model → Model) (x : SyscallEffect)
    (i : SyscallInput) (m : Model) :
    ¬ seqSpec (modifySpec f) (pure x) i m .unmodeled := by
  intro H
  simp only [seqSpec, LinuxSem.LinuxProcessSem.bind,
    LinuxSem.LinuxProcessSem.pure] at H
  rcases H with hm | ⟨u, m1, evs1, hm, hp⟩
  · exact nomatch hm
  · exact nomatch hp

theorem check_read_urandom_sound_ok (i : SyscallInput) (buf count : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_read_urandom i buf count eff m = .CheckOk m' evs) :
    read_urandom buf count i m i m (.ok eff m' evs) := by
  unfold read_urandom
  simp only [check_read_urandom] at H
  by_cases h0 : w_is0 count = true
  · rw [ite_eq_left h0] at H ⊢
    obtain ⟨rfl, rfl, rfl⟩ :=
      (check_ret_only_ok_iff eff (BitVec.ofInt 64 0) m [] m' evs).mp H
    simp only [LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only,
      LinuxSem.LinuxProcessSem.pure]
  · rw [ite_eq_right h0] at H ⊢
    cases hw : read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) with
    | none =>
      simp only [hw] at H ⊢
      obtain ⟨rfl, rfl, rfl⟩ :=
        (check_ret_only_ok_iff eff (errno_ret EFAULT) m [] m' evs).mp H
      simp only [LinuxSem.LinuxProcessSem.Sys.Syscall.err_ret,
        LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only,
        LinuxSem.LinuxProcessSem.pure]
    | some w1 =>
      simp only [hw] at H ⊢
      generalize hr : (stream_take_z (m_urandom m) (rw_count_clamp count)) = r
        at H ⊢
      by_cases hlen : (!(((r.1).length : Int) == rw_count_clamp count)) = true
      · rw [ite_eq_left hlen] at H
        exact nomatch H
      · rw [ite_eq_right hlen] at H ⊢
        cases hw2 : read_bytes_map i.in_wmem buf (len_word r.1) with
        | none =>
          simp only [hw2] at H
          exact nomatch H
        | some w2 =>
          simp only [hw2] at H ⊢
          obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
          cases ws with
          | nil => dsimp only at H; exact nomatch H
          | cons hd tl =>
            obtain ⟨a, bs⟩ := hd
            cases tl <;> cases zs <;> cases us <;> cases cs <;> cases ks
            · dsimp only at H
              by_cases hc : (bv_eqb a buf && bv_eqb ret (len_word r.1)
                  && listN_eqb bs r.1) = true
              · rw [ite_eq_left hc] at H
                cases H
                have h1 : bv_eqb a buf = true
                    ∧ bv_eqb ret (len_word r.1) = true
                    ∧ listN_eqb bs r.1 = true := by
                  simpa [Bool.and_eq_true, and_assoc] using hc
                obtain ⟨ha, hret, hbs⟩ := h1
                have ha' : a = buf := (Fs.bv_eqb_eq a buf).mp ha
                have hret' : ret = len_word r.1 := (Fs.bv_eqb_eq ret _).mp hret
                have hbs' : bs = r.1 := (listN_eqb_eq bs r.1).mp hbs
                rw [ha', hret', hbs']
                simp only [set_urandom, seqSpec]
                exact bind_ok (modifySpec (with_urandom r.2))
                  (fun _ =>
                    LinuxSem.LinuxProcessSem.pure
                      (mkEffect (len_word r.1) [(buf, r.1)] []))
                  i m () _ [] _ _ [] rfl rfl
              · rw [ite_eq_right hc] at H
                exact nomatch H
            all_goals (try dsimp only at H)
            all_goals (try contradiction)

theorem check_read_urandom_sound_unmodeled (i : SyscallInput) (buf count : word)
    (eff : SyscallEffect) (m : Model)
    (H : check_read_urandom i buf count eff m = .CheckUnmodeled) :
    read_urandom buf count i m i m .unmodeled := by
  unfold read_urandom
  simp only [check_read_urandom] at H
  by_cases h0 : w_is0 count = true
  · rw [ite_eq_left h0] at H
    exact absurd H (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])
  · rw [ite_eq_right h0] at H ⊢
    cases hw : read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) with
    | none =>
      simp only [hw] at H
      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
    | some w1 =>
      simp only [hw] at H ⊢
      generalize hr : (stream_take_z (m_urandom m) (rw_count_clamp count)) = r
        at H ⊢
      by_cases hlen : (!(((r.1).length : Int) == rw_count_clamp count)) = true
      · rw [ite_eq_left hlen] at H ⊢
        rfl
      · rw [ite_eq_right hlen] at H ⊢
        cases hw2 : read_bytes_map i.in_wmem buf (len_word r.1) with
        | none =>
          simp only [hw2] at H ⊢
          rfl
        | some w2 =>
          simp only [hw2] at H ⊢
          obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
          cases ws with
          | nil => dsimp only at H; exact nomatch H
          | cons hd tl =>
            obtain ⟨a, bs⟩ := hd
            cases tl <;> cases zs <;> cases us <;> cases cs <;> cases ks
            · dsimp only at H
              by_cases hc : (bv_eqb a buf && bv_eqb ret (len_word r.1)
                  && listN_eqb bs r.1) = true
              · rw [ite_eq_left hc] at H
                exact nomatch H
              · rw [ite_eq_right hc] at H
                exact nomatch H
            all_goals (try dsimp only at H)
            all_goals (try contradiction)

theorem check_read_urandom_complete_ok (i : SyscallInput) (buf count : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : read_urandom buf count i m i m (.ok eff m' evs)) :
    check_read_urandom i buf count eff m = .CheckOk m' evs := by
  unfold read_urandom at H
  simp only [check_read_urandom]
  by_cases h0 : w_is0 count = true
  · rw [ite_eq_left h0] at H ⊢
    cases H
    simp [check_ret_only, bv_eqb_refl]
  · rw [ite_eq_right h0] at H ⊢
    cases hw : read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) with
    | none =>
      simp only [hw] at H ⊢
      cases H
      simp [check_ret_only, bv_eqb_refl]
    | some w1 =>
      simp only [hw] at H ⊢
      generalize hr : (stream_take_z (m_urandom m) (rw_count_clamp count)) = r
        at H ⊢
      by_cases hlen : (!(((r.1).length : Int) == rw_count_clamp count)) = true
      · rw [ite_eq_left hlen] at H
        cases H
      · rw [ite_eq_right hlen] at H ⊢
        cases hw2 : read_bytes_map i.in_wmem buf (len_word r.1) with
        | none =>
          simp only [hw2] at H
          cases H
        | some w2 =>
          simp only [hw2] at H ⊢
          simp only [set_urandom] at H
          obtain ⟨heff, hm', hevs⟩ := seqSpec_modify_pure_ok_inv
            (with_urandom r.2) (mkEffect (len_word r.1) [(buf, r.1)] [])
            i m eff m' evs H
          subst heff
          subst hm'
          subst hevs
          dsimp only
          rw [ite_eq_left (by
            rw [bv_eqb_refl, bv_eqb_refl, (listN_eqb_eq r.1 r.1).mpr rfl]
            rfl)]

theorem check_read_urandom_complete_unmodeled (i : SyscallInput) (buf count : word)
    (m : Model) (eff : SyscallEffect)
    (H : read_urandom buf count i m i m .unmodeled) :
    check_read_urandom i buf count eff m = .CheckUnmodeled := by
  unfold read_urandom at H
  simp only [check_read_urandom]
  by_cases h0 : w_is0 count = true
  · rw [ite_eq_left h0] at H
    cases H
  · rw [ite_eq_right h0] at H ⊢
    cases hw : read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) with
    | none =>
      simp only [hw] at H
      cases H
    | some w1 =>
      simp only [hw] at H ⊢
      generalize hr : (stream_take_z (m_urandom m) (rw_count_clamp count)) = r
        at H ⊢
      by_cases hlen : (!(((r.1).length : Int) == rw_count_clamp count)) = true
      · rw [ite_eq_left hlen] at H ⊢
      · rw [ite_eq_right hlen] at H ⊢
        cases hw2 : read_bytes_map i.in_wmem buf (len_word r.1) with
        | none =>
          simp only [hw2] at H ⊢
        | some w2 =>
          simp only [hw2] at H
          simp only [set_urandom] at H
          exact absurd H (seqSpec_modify_pure_unmodeled_false
            (with_urandom r.2) (mkEffect (len_word r.1) [(buf, r.1)] []) i m)

theorem check_read_urandom_delivery_clamped (i : SyscallInput) (buf count : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event) (a : word)
    (bs : List byte)
    (H : check_read_urandom i buf count eff m = .CheckOk m' evs)
    (Hws : eff.eff_writes = [(a, bs)]) :
    (bs.length : Int) ≤ MAX_RW_COUNT := by
  simp only [check_read_urandom] at H
  by_cases h0 : w_is0 count = true
  · rw [ite_eq_left h0] at H
    obtain ⟨heff, -, -⟩ :=
      (check_ret_only_ok_iff eff (BitVec.ofInt 64 0) m [] m' evs).mp H
    rw [heff] at Hws
    simp at Hws
  · rw [ite_eq_right h0] at H
    cases hw : read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) with
    | none =>
      simp only [hw] at H
      obtain ⟨heff, -, -⟩ :=
        (check_ret_only_ok_iff eff (errno_ret EFAULT) m [] m' evs).mp H
      rw [heff] at Hws
      simp at Hws
    | some w1 =>
      simp only [hw] at H
      generalize hr : (stream_take_z (m_urandom m) (rw_count_clamp count)) = r
        at H
      by_cases hlen : (!(((r.1).length : Int) == rw_count_clamp count)) = true
      · rw [ite_eq_left hlen] at H
        exact nomatch H
      · rw [ite_eq_right hlen] at H
        cases hw2 : read_bytes_map i.in_wmem buf (len_word r.1) with
        | none => simp only [hw2] at H; exact nomatch H
        | some w2 =>
          simp only [hw2] at H
          obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
          cases ws with
          | nil => dsimp only at H; exact nomatch H
          | cons hd tl =>
            obtain ⟨a0, bs0⟩ := hd
            cases tl <;> cases zs <;> cases us <;> cases cs <;> cases ks
            · dsimp only at H
              by_cases hc : (bv_eqb a0 buf && bv_eqb ret (len_word r.1)
                  && listN_eqb bs0 r.1) = true
              · rw [ite_eq_left hc] at H
                cases H
                have h1 : bv_eqb a0 buf = true
                    ∧ bv_eqb ret (len_word r.1) = true
                    ∧ listN_eqb bs0 r.1 = true := by
                  simpa [Bool.and_eq_true, and_assoc] using hc
                obtain ⟨-, -, hbs_loc⟩ := h1
                have hb : (((r.1).length : Int) == rw_count_clamp count) = true := by
                  cases h : (((r.1).length : Int) == rw_count_clamp count) with
                  | false => rw [h] at hlen; exact absurd rfl hlen
                  | true => rfl
                have heq : (r.1.length : Int) = rw_count_clamp count :=
                  beq_iff_eq.mp hb
                have hbs : bs = r.1 := by
                  have h1 : (a0, bs0) = (a, bs) := by simpa using Hws
                  have hbs0 : bs0 = bs := congrArg Prod.snd h1
                  rw [← hbs0]
                  exact (listN_eqb_eq bs0 r.1).mp hbs_loc
                rw [hbs, heq]
                exact (rw_count_clamp_range count).2
              · rw [ite_eq_right hc] at H
                exact nomatch H
            all_goals (try dsimp only at H)
            all_goals (try contradiction)

/-- THE SAME STREAM READS THE SAME BYTES: two models that agree on
    [m_urandom] — the source and the target of an equivalence pair, seeded
    from one [in_urandom] — hand the same bytes to the same request and
    leave the same remainder, whatever else they differ in.  Nothing is
    chosen on the way, so this is by computation rather than by a relation
    between choices.  The result below stands on its own. -/
theorem check_read_urandom_same_stream (i : SyscallInput) (buf count : word)
    (eff1 eff2 : SyscallEffect) (m1 m2 m1' m2' : Model)
    (evs1 evs2 : List event)
    (Hu : m_urandom m1 = m_urandom m2)
    (H1 : check_read_urandom i buf count eff1 m1 = .CheckOk m1' evs1)
    (H2 : check_read_urandom i buf count eff2 m2 = .CheckOk m2' evs2) :
    eff1.eff_writes = eff2.eff_writes ∧ eff1.eff_ret = eff2.eff_ret
      ∧ m_urandom m1' = m_urandom m2' := by
  simp only [check_read_urandom] at H1 H2
  rw [Hu] at H1
  by_cases h0 : w_is0 count = true
  · rw [ite_eq_left h0] at H1 H2
    obtain ⟨rfl, rfl, rfl⟩ :=
      (check_ret_only_ok_iff eff1 (BitVec.ofInt 64 0) m1 [] m1' evs1).mp H1
    obtain ⟨rfl, rfl, rfl⟩ :=
      (check_ret_only_ok_iff eff2 (BitVec.ofInt 64 0) m2 [] m2' evs2).mp H2
    exact ⟨rfl, rfl, Hu⟩
  · rw [ite_eq_right h0] at H1 H2
    cases hw : read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) with
    | none =>
      simp only [hw] at H1 H2
      obtain ⟨rfl, rfl, rfl⟩ :=
        (check_ret_only_ok_iff eff1 (errno_ret EFAULT) m1 [] m1' evs1).mp H1
      obtain ⟨rfl, rfl, rfl⟩ :=
        (check_ret_only_ok_iff eff2 (errno_ret EFAULT) m2 [] m2' evs2).mp H2
      exact ⟨rfl, rfl, Hu⟩
    | some w1 =>
      simp only [hw] at H1 H2
      generalize hr : (stream_take_z (m_urandom m2) (rw_count_clamp count)) = r
        at H1 H2
      by_cases hlen : (!(((r.1).length : Int) == rw_count_clamp count)) = true
      · rw [ite_eq_left hlen] at H1
        exact nomatch H1
      · rw [ite_eq_right hlen] at H1 H2
        cases hw2 : read_bytes_map i.in_wmem buf (len_word r.1) with
        | none =>
          simp only [hw2] at H1
          exact nomatch H1
        | some w2 =>
          simp only [hw2] at H1 H2
          obtain ⟨ret1, ws1, zs1, us1, cs1, ks1⟩ := eff1
          obtain ⟨ret2, ws2, zs2, us2, cs2, ks2⟩ := eff2
          cases ws1 with
          | nil => dsimp only at H1; exact nomatch H1
          | cons hd1 tl1 =>
            obtain ⟨a1, bs1⟩ := hd1
            cases tl1 <;> cases zs1 <;> cases us1 <;> cases cs1 <;> cases ks1
            · dsimp only at H1
              cases ws2 with
              | nil => dsimp only at H2; exact nomatch H2
              | cons hd2 tl2 =>
                obtain ⟨a2, bs2⟩ := hd2
                cases tl2 <;> cases zs2 <;> cases us2 <;> cases cs2 <;> cases ks2
                · dsimp only at H2
                  by_cases hc1 : (bv_eqb a1 buf && bv_eqb ret1 (len_word r.1)
                      && listN_eqb bs1 r.1) = true
                  · rw [ite_eq_left hc1] at H1
                    cases H1
                    by_cases hc2 : (bv_eqb a2 buf && bv_eqb ret2 (len_word r.1)
                        && listN_eqb bs2 r.1) = true
                    · rw [ite_eq_left hc2] at H2
                      cases H2
                      have e1 : bv_eqb a1 buf = true
                          ∧ bv_eqb ret1 (len_word r.1) = true
                          ∧ listN_eqb bs1 r.1 = true := by
                        simpa [Bool.and_eq_true, and_assoc] using hc1
                      have e2 : bv_eqb a2 buf = true
                          ∧ bv_eqb ret2 (len_word r.1) = true
                          ∧ listN_eqb bs2 r.1 = true := by
                        simpa [Bool.and_eq_true, and_assoc] using hc2
                      obtain ⟨ha1, hr1, hb1⟩ := e1
                      obtain ⟨ha2, hr2, hb2⟩ := e2
                      rw [(Fs.bv_eqb_eq a1 buf).mp ha1,
                        (Fs.bv_eqb_eq ret1 _).mp hr1,
                        (listN_eqb_eq bs1 r.1).mp hb1,
                        (Fs.bv_eqb_eq a2 buf).mp ha2,
                        (Fs.bv_eqb_eq ret2 _).mp hr2,
                        (listN_eqb_eq bs2 r.1).mp hb2]
                      exact ⟨rfl, rfl, by simp⟩
                    · rw [ite_eq_right hc2] at H2
                      exact nomatch H2
                  · rw [ite_eq_right hc1] at H1
                    exact nomatch H1
                all_goals (try dsimp only at H2)
                all_goals (try contradiction)
            all_goals (try dsimp only at H1)
            all_goals (try contradiction)

/- =========================================================================
   lseek (62)
   ========================================================================= -/

theorem check_lseek_sound_ok (fd off whence : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : check_lseek fd off whence eff m = .CheckOk m' evs) :
    lseek_spec fd off whence i m (.ok eff m' evs) := by
  simp only [lseek_spec, getModelSpec, bind_getModel]
  simp only [check_lseek] at H
  cases hfd : fd_lookup (m_fds m) fd with
  | none =>
    simp only [hfd] at H ⊢
    obtain ⟨rfl, rfl, rfl⟩ :=
      (check_ret_only_ok_iff eff (errno_ret EBADF) m [] m' evs).mp H
    simp only [LinuxSem.LinuxProcessSem.Sys.Syscall.err_ret,
      LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only,
      LinuxSem.LinuxProcessSem.pure]
  | some e =>
    simp only [hfd] at H ⊢
    by_cases hw : decide (SEEK_MAX < (whence.toNat : Int)) = true
    · rw [ite_eq_left hw] at H
      rw [ite_eq_left (of_decide_eq_true hw)]
      obtain ⟨rfl, rfl, rfl⟩ :=
        (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
      simp only [LinuxSem.LinuxProcessSem.Sys.Syscall.err_ret,
        LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only,
        LinuxSem.LinuxProcessSem.pure]
    · rw [ite_eq_right hw] at H
      rw [ite_eq_right (fun hP => hw (decide_eq_true hP))]
      cases e with
      | FdChannel _ =>
        simp only
        obtain ⟨rfl, rfl, rfl⟩ :=
          (check_ret_only_ok_iff eff (errno_ret ESPIPE) m [] m' evs).mp H
        simp only [LinuxSem.LinuxProcessSem.Sys.Syscall.err_ret,
          LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only,
          LinuxSem.LinuxProcessSem.pure]
      | FdSocket _ =>
        simp only
        obtain ⟨rfl, rfl, rfl⟩ :=
          (check_ret_only_ok_iff eff (errno_ret ESPIPE) m [] m' evs).mp H
        simp only [LinuxSem.LinuxProcessSem.Sys.Syscall.err_ret,
          LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only,
          LinuxSem.LinuxProcessSem.pure]
      | FdPipe _ _ =>
        simp only
        obtain ⟨rfl, rfl, rfl⟩ :=
          (check_ret_only_ok_iff eff (errno_ret ESPIPE) m [] m' evs).mp H
        simp only [LinuxSem.LinuxProcessSem.Sys.Syscall.err_ret,
          LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only,
          LinuxSem.LinuxProcessSem.pure]
      | FdDevNull _ _ =>
        simp only
        obtain ⟨rfl, rfl, rfl⟩ :=
          (check_ret_only_ok_iff eff (BitVec.ofInt 64 0) m [] m' evs).mp H
        simp only [LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only,
          LinuxSem.LinuxProcessSem.pure]
      | FdUrandom =>
        simp only
        obtain ⟨rfl, rfl, rfl⟩ :=
          (check_ret_only_ok_iff eff (BitVec.ofInt 64 0) m [] m' evs).mp H
        simp only [LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only,
          LinuxSem.LinuxProcessSem.pure]
      | FdDir =>
        simp only at H
        exact nomatch H
      | FdFile p cur =>
        simp only
        cases hfs : Fs.fs_lookup (m_fs m) p with
        | none => simp only [hfs] at H; exact nomatch H
        | some data =>
          simp only [hfs] at H ⊢
          cases hb : lseek_base whence cur (len_word data) with
          | none => simp only [hb] at H; exact nomatch H
          | some base =>
            simp only [hb] at H ⊢
            cases hd : lseek_dest base off with
            | none =>
              simp only [hd] at H ⊢
              obtain ⟨rfl, rfl, rfl⟩ :=
                (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
              simp only [LinuxSem.LinuxProcessSem.Sys.Syscall.err_ret,
                LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only,
                LinuxSem.LinuxProcessSem.pure]
            | some r =>
              simp only [hd] at H ⊢
              obtain ⟨rfl, rfl, rfl⟩ :=
                (check_ret_only_ok_iff eff r
                  (with_fds (fd_insert (m_fds m) fd (FdEntry.FdFile p r)) m) []
                  m' evs).mp H
              simp only [set_fds, seqSpec]
              exact bind_ok
                (modifySpec (with_fds (fd_insert (m_fds m) fd (FdEntry.FdFile p r))))
                (fun _ => LinuxSem.LinuxProcessSem.pure
                  (mkEffect r [] []))
                i m () _ [] _ _ [] rfl rfl
      | FdFileW p cur =>
        simp only
        cases hfs : Fs.fs_lookup (m_fs m) p with
        | none => simp only [hfs] at H; exact nomatch H
        | some data =>
          simp only [hfs] at H ⊢
          cases hb : lseek_base whence cur (len_word data) with
          | none => simp only [hb] at H; exact nomatch H
          | some base =>
            simp only [hb] at H ⊢
            cases hd : lseek_dest base off with
            | none =>
              simp only [hd] at H ⊢
              obtain ⟨rfl, rfl, rfl⟩ :=
                (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
              simp only [LinuxSem.LinuxProcessSem.Sys.Syscall.err_ret,
                LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only,
                LinuxSem.LinuxProcessSem.pure]
            | some r =>
              simp only [hd] at H ⊢
              obtain ⟨rfl, rfl, rfl⟩ :=
                (check_ret_only_ok_iff eff r
                  (with_fds (fd_insert (m_fds m) fd (FdEntry.FdFileW p r)) m) []
                  m' evs).mp H
              simp only [set_fds, seqSpec]
              exact bind_ok
                (modifySpec (with_fds (fd_insert (m_fds m) fd (FdEntry.FdFileW p r))))
                (fun _ => LinuxSem.LinuxProcessSem.pure
                  (mkEffect r [] []))
                i m () _ [] _ _ [] rfl rfl
      | FdFileRW p cur =>
        simp only
        cases hfs : Fs.fs_lookup (m_fs m) p with
        | none => simp only [hfs] at H; exact nomatch H
        | some data =>
          simp only [hfs] at H ⊢
          cases hb : lseek_base whence cur (len_word data) with
          | none => simp only [hb] at H; exact nomatch H
          | some base =>
            simp only [hb] at H ⊢
            cases hd : lseek_dest base off with
            | none =>
              simp only [hd] at H ⊢
              obtain ⟨rfl, rfl, rfl⟩ :=
                (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
              simp only [LinuxSem.LinuxProcessSem.Sys.Syscall.err_ret,
                LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only,
                LinuxSem.LinuxProcessSem.pure]
            | some r =>
              simp only [hd] at H ⊢
              obtain ⟨rfl, rfl, rfl⟩ :=
                (check_ret_only_ok_iff eff r
                  (with_fds (fd_insert (m_fds m) fd (FdEntry.FdFileRW p r)) m) []
                  m' evs).mp H
              simp only [set_fds, seqSpec]
              exact bind_ok
                (modifySpec (with_fds (fd_insert (m_fds m) fd (FdEntry.FdFileRW p r))))
                (fun _ => LinuxSem.LinuxProcessSem.pure
                  (mkEffect r [] []))
                i m () _ [] _ _ [] rfl rfl
      | FdFileA p cur =>
        simp only
        cases hfs : Fs.fs_lookup (m_fs m) p with
        | none => simp only [hfs] at H; exact nomatch H
        | some data =>
          simp only [hfs] at H ⊢
          cases hb : lseek_base whence cur (len_word data) with
          | none => simp only [hb] at H; exact nomatch H
          | some base =>
            simp only [hb] at H ⊢
            cases hd : lseek_dest base off with
            | none =>
              simp only [hd] at H ⊢
              obtain ⟨rfl, rfl, rfl⟩ :=
                (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
              simp only [LinuxSem.LinuxProcessSem.Sys.Syscall.err_ret,
                LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only,
                LinuxSem.LinuxProcessSem.pure]
            | some r =>
              simp only [hd] at H ⊢
              obtain ⟨rfl, rfl, rfl⟩ :=
                (check_ret_only_ok_iff eff r
                  (with_fds (fd_insert (m_fds m) fd (FdEntry.FdFileA p r)) m) []
                  m' evs).mp H
              simp only [set_fds, seqSpec]
              exact bind_ok
                (modifySpec (with_fds (fd_insert (m_fds m) fd (FdEntry.FdFileA p r))))
                (fun _ => LinuxSem.LinuxProcessSem.pure
                  (mkEffect r [] []))
                i m () _ [] _ _ [] rfl rfl

theorem check_lseek_sound_unmodeled (fd off whence : word) (eff : SyscallEffect)
    (m : Model) (i : SyscallInput)
    (H : check_lseek fd off whence eff m = .CheckUnmodeled) :
    lseek_spec fd off whence i m .unmodeled := by
  simp only [lseek_spec, getModelSpec, bind_getModel]
  simp only [check_lseek] at H
  cases hfd : fd_lookup (m_fds m) fd with
  | none =>
    simp only [hfd] at H
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])
  | some e =>
    simp only [hfd] at H ⊢
    by_cases hw : decide (SEEK_MAX < (whence.toNat : Int)) = true
    · rw [ite_eq_left hw] at H
      rw [ite_eq_left (of_decide_eq_true hw)]
      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
    · rw [ite_eq_right hw] at H
      rw [ite_eq_right (fun hP => hw (decide_eq_true hP))]
      cases e with
      | FdChannel _ =>
        simp only
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ESPIPE) m [])
      | FdSocket _ =>
        simp only
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ESPIPE) m [])
      | FdPipe _ _ =>
        simp only
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ESPIPE) m [])
      | FdDevNull _ _ =>
        simp only
        exact absurd H (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])
      | FdUrandom =>
        simp only
        exact absurd H (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])
      | FdDir =>
        simp only at H ⊢
        rfl
      | FdFile p cur =>
        simp only
        cases hfs : Fs.fs_lookup (m_fs m) p with
        | none => simp only [hfs] at H ⊢; rfl
        | some data =>
          simp only [hfs] at H ⊢
          cases hb : lseek_base whence cur (len_word data) with
          | none => simp only [hb] at H ⊢; rfl
          | some base =>
            simp only [hb] at H ⊢
            cases hd : lseek_dest base off with
            | none =>
              simp only [hd] at H
              exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
            | some r =>
              simp only [hd] at H
              exact absurd H (check_ret_only_no_unmodeled eff r
                (with_fds (fd_insert (m_fds m) fd (FdEntry.FdFile p r)) m) [])
      | FdFileW p cur =>
        simp only
        cases hfs : Fs.fs_lookup (m_fs m) p with
        | none => simp only [hfs] at H ⊢; rfl
        | some data =>
          simp only [hfs] at H ⊢
          cases hb : lseek_base whence cur (len_word data) with
          | none => simp only [hb] at H ⊢; rfl
          | some base =>
            simp only [hb] at H ⊢
            cases hd : lseek_dest base off with
            | none =>
              simp only [hd] at H
              exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
            | some r =>
              simp only [hd] at H
              exact absurd H (check_ret_only_no_unmodeled eff r
                (with_fds (fd_insert (m_fds m) fd (FdEntry.FdFileW p r)) m) [])
      | FdFileRW p cur =>
        simp only
        cases hfs : Fs.fs_lookup (m_fs m) p with
        | none => simp only [hfs] at H ⊢; rfl
        | some data =>
          simp only [hfs] at H ⊢
          cases hb : lseek_base whence cur (len_word data) with
          | none => simp only [hb] at H ⊢; rfl
          | some base =>
            simp only [hb] at H ⊢
            cases hd : lseek_dest base off with
            | none =>
              simp only [hd] at H
              exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
            | some r =>
              simp only [hd] at H
              exact absurd H (check_ret_only_no_unmodeled eff r
                (with_fds (fd_insert (m_fds m) fd (FdEntry.FdFileRW p r)) m) [])
      | FdFileA p cur =>
        simp only
        cases hfs : Fs.fs_lookup (m_fs m) p with
        | none => simp only [hfs] at H ⊢; rfl
        | some data =>
          simp only [hfs] at H ⊢
          cases hb : lseek_base whence cur (len_word data) with
          | none => simp only [hb] at H ⊢; rfl
          | some base =>
            simp only [hb] at H ⊢
            cases hd : lseek_dest base off with
            | none =>
              simp only [hd] at H
              exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
            | some r =>
              simp only [hd] at H
              exact absurd H (check_ret_only_no_unmodeled eff r
                (with_fds (fd_insert (m_fds m) fd (FdEntry.FdFileA p r)) m) [])

theorem check_lseek_complete_ok (fd off whence : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : lseek_spec fd off whence i m (.ok eff m' evs)) :
    check_lseek fd off whence eff m = .CheckOk m' evs := by
  simp only [lseek_spec, getModelSpec, bind_getModel] at H
  simp only [check_lseek]
  cases hfd : fd_lookup (m_fds m) fd with
  | none =>
    simp only [hfd] at H ⊢
    cases H
    simp [check_ret_only, bv_eqb_refl]
  | some e =>
    simp only [hfd] at H ⊢
    by_cases hw : decide (SEEK_MAX < (whence.toNat : Int)) = true
    · rw [ite_eq_left (of_decide_eq_true hw)] at H
      rw [ite_eq_left hw]
      cases H
      simp [check_ret_only, bv_eqb_refl]
    · rw [ite_eq_right (fun hP => hw (decide_eq_true hP))] at H
      rw [ite_eq_right hw]
      cases e with
      | FdChannel _ =>
        simp only
        cases H
        simp [check_ret_only, bv_eqb_refl]
      | FdSocket _ =>
        simp only
        cases H
        simp [check_ret_only, bv_eqb_refl]
      | FdPipe _ _ =>
        simp only
        cases H
        simp [check_ret_only, bv_eqb_refl]
      | FdDevNull _ _ =>
        simp only
        cases H
        simp [check_ret_only, bv_eqb_refl]
      | FdUrandom =>
        simp only
        cases H
        simp [check_ret_only, bv_eqb_refl]
      | FdDir =>
        simp only at H
        cases H
      | FdFile p cur =>
        simp only
        cases hfs : Fs.fs_lookup (m_fs m) p with
        | none =>
          simp only [hfs] at H
          cases H
        | some data =>
          simp only [hfs] at H ⊢
          cases hb : lseek_base whence cur (len_word data) with
          | none =>
            simp only [hb] at H
            cases H
          | some base =>
            simp only [hb] at H ⊢
            cases hd : lseek_dest base off with
            | none =>
              simp only [hd] at H ⊢
              cases H
              simp [check_ret_only, bv_eqb_refl]
            | some r =>
              simp only [hd] at H ⊢
              simp only [set_fds] at H
              obtain ⟨heff, hm', hevs⟩ := seqSpec_modify_pure_ok_inv
                (with_fds (fd_insert (m_fds m) fd (FdEntry.FdFile p r)))
                (mkEffect r [] []) i m eff m' evs H
              subst heff
              subst hm'
              subst hevs
              simp [check_ret_only, bv_eqb_refl]
      | FdFileW p cur =>
        simp only
        cases hfs : Fs.fs_lookup (m_fs m) p with
        | none =>
          simp only [hfs] at H
          cases H
        | some data =>
          simp only [hfs] at H ⊢
          cases hb : lseek_base whence cur (len_word data) with
          | none =>
            simp only [hb] at H
            cases H
          | some base =>
            simp only [hb] at H ⊢
            cases hd : lseek_dest base off with
            | none =>
              simp only [hd] at H ⊢
              cases H
              simp [check_ret_only, bv_eqb_refl]
            | some r =>
              simp only [hd] at H ⊢
              simp only [set_fds] at H
              obtain ⟨heff, hm', hevs⟩ := seqSpec_modify_pure_ok_inv
                (with_fds (fd_insert (m_fds m) fd (FdEntry.FdFileW p r)))
                (mkEffect r [] []) i m eff m' evs H
              subst heff
              subst hm'
              subst hevs
              simp [check_ret_only, bv_eqb_refl]
      | FdFileRW p cur =>
        simp only
        cases hfs : Fs.fs_lookup (m_fs m) p with
        | none =>
          simp only [hfs] at H
          cases H
        | some data =>
          simp only [hfs] at H ⊢
          cases hb : lseek_base whence cur (len_word data) with
          | none =>
            simp only [hb] at H
            cases H
          | some base =>
            simp only [hb] at H ⊢
            cases hd : lseek_dest base off with
            | none =>
              simp only [hd] at H ⊢
              cases H
              simp [check_ret_only, bv_eqb_refl]
            | some r =>
              simp only [hd] at H ⊢
              simp only [set_fds] at H
              obtain ⟨heff, hm', hevs⟩ := seqSpec_modify_pure_ok_inv
                (with_fds (fd_insert (m_fds m) fd (FdEntry.FdFileRW p r)))
                (mkEffect r [] []) i m eff m' evs H
              subst heff
              subst hm'
              subst hevs
              simp [check_ret_only, bv_eqb_refl]
      | FdFileA p cur =>
        simp only
        cases hfs : Fs.fs_lookup (m_fs m) p with
        | none =>
          simp only [hfs] at H
          cases H
        | some data =>
          simp only [hfs] at H ⊢
          cases hb : lseek_base whence cur (len_word data) with
          | none =>
            simp only [hb] at H
            cases H
          | some base =>
            simp only [hb] at H ⊢
            cases hd : lseek_dest base off with
            | none =>
              simp only [hd] at H ⊢
              cases H
              simp [check_ret_only, bv_eqb_refl]
            | some r =>
              simp only [hd] at H ⊢
              simp only [set_fds] at H
              obtain ⟨heff, hm', hevs⟩ := seqSpec_modify_pure_ok_inv
                (with_fds (fd_insert (m_fds m) fd (FdEntry.FdFileA p r)))
                (mkEffect r [] []) i m eff m' evs H
              subst heff
              subst hm'
              subst hevs
              simp [check_ret_only, bv_eqb_refl]

theorem check_lseek_complete_unmodeled (fd off whence : word) (m : Model)
    (i : SyscallInput) (eff : SyscallEffect)
    (H : lseek_spec fd off whence i m .unmodeled) :
    check_lseek fd off whence eff m = .CheckUnmodeled := by
  simp only [lseek_spec, getModelSpec, bind_getModel] at H
  simp only [check_lseek]
  cases hfd : fd_lookup (m_fds m) fd with
  | none =>
    simp only [hfd] at H
    cases H
  | some e =>
    simp only [hfd] at H ⊢
    by_cases hw : decide (SEEK_MAX < (whence.toNat : Int)) = true
    · rw [ite_eq_left (of_decide_eq_true hw)] at H
      rw [ite_eq_left hw]
      cases H
    · rw [ite_eq_right (fun hP => hw (decide_eq_true hP))] at H
      rw [ite_eq_right hw]
      cases e with
      | FdChannel _ =>
        simp only at H ⊢
        cases H
      | FdSocket _ =>
        simp only at H ⊢
        cases H
      | FdPipe _ _ =>
        simp only at H ⊢
        cases H
      | FdDevNull _ _ =>
        simp only at H ⊢
        cases H
      | FdUrandom =>
        simp only at H ⊢
        cases H
      | FdDir =>
        simp only at H ⊢
      | FdFile p cur =>
        simp only
        cases hfs : Fs.fs_lookup (m_fs m) p with
        | none => simp only [hfs] at H ⊢
        | some data =>
          simp only [hfs] at H ⊢
          cases hb : lseek_base whence cur (len_word data) with
          | none => simp only [hb] at H ⊢
          | some base =>
            simp only [hb] at H ⊢
            cases hd : lseek_dest base off with
            | none =>
              simp only [hd] at H
              cases H
            | some r =>
              simp only [hd] at H
              simp only [set_fds] at H
              exact absurd H (seqSpec_modify_pure_unmodeled_false
                (with_fds (fd_insert (m_fds m) fd (FdEntry.FdFile p r)))
                (mkEffect r [] []) i m)
      | FdFileW p cur =>
        simp only
        cases hfs : Fs.fs_lookup (m_fs m) p with
        | none => simp only [hfs] at H ⊢
        | some data =>
          simp only [hfs] at H ⊢
          cases hb : lseek_base whence cur (len_word data) with
          | none => simp only [hb] at H ⊢
          | some base =>
            simp only [hb] at H ⊢
            cases hd : lseek_dest base off with
            | none =>
              simp only [hd] at H
              cases H
            | some r =>
              simp only [hd] at H
              simp only [set_fds] at H
              exact absurd H (seqSpec_modify_pure_unmodeled_false
                (with_fds (fd_insert (m_fds m) fd (FdEntry.FdFileW p r)))
                (mkEffect r [] []) i m)
      | FdFileRW p cur =>
        simp only
        cases hfs : Fs.fs_lookup (m_fs m) p with
        | none => simp only [hfs] at H ⊢
        | some data =>
          simp only [hfs] at H ⊢
          cases hb : lseek_base whence cur (len_word data) with
          | none => simp only [hb] at H ⊢
          | some base =>
            simp only [hb] at H ⊢
            cases hd : lseek_dest base off with
            | none =>
              simp only [hd] at H
              cases H
            | some r =>
              simp only [hd] at H
              simp only [set_fds] at H
              exact absurd H (seqSpec_modify_pure_unmodeled_false
                (with_fds (fd_insert (m_fds m) fd (FdEntry.FdFileRW p r)))
                (mkEffect r [] []) i m)
      | FdFileA p cur =>
        simp only
        cases hfs : Fs.fs_lookup (m_fs m) p with
        | none => simp only [hfs] at H ⊢
        | some data =>
          simp only [hfs] at H ⊢
          cases hb : lseek_base whence cur (len_word data) with
          | none => simp only [hb] at H ⊢
          | some base =>
            simp only [hb] at H ⊢
            cases hd : lseek_dest base off with
            | none =>
              simp only [hd] at H
              cases H
            | some r =>
              simp only [hd] at H
              simp only [set_fds] at H
              exact absurd H (seqSpec_modify_pure_unmodeled_false
                (with_fds (fd_insert (m_fds m) fd (FdEntry.FdFileA p r)))
                (mkEffect r [] []) i m)
/- The `bind input ;; bind getModel` prologue of every spec in this
   family, as an IFF: the body admits exactly the program's outcomes. -/

theorem spec_input_model_intro {A : Type} (k : SyscallInput → Model → SysSpec A)
    (i : SyscallInput) (m : Model) (o : Outcome A Model event)
    (H : k i m i m o) :
    bind input (fun i0 => bind getModel (fun m0 => k i0 m0)) i m o := by
  cases o with
  | ok x m' evs =>
    exact bind_ok0 input (fun i0 => bind getModel (fun m0 => k i0 m0)) i m i m
      x m' evs (input_ok i m)
      (bind_ok0 getModel (fun m0 => k i m0) i m m m x m' evs rfl H)
  | unmodeled =>
    exact Or.inr ⟨i, m, [], input_ok i m, Or.inr ⟨m, m, [], rfl, H⟩⟩

theorem bind_input_model_iff {A : Type} (k : SyscallInput → Model → SysSpec A)
    (i : SyscallInput) (m : Model) (o : Outcome A Model event) :
    bind input (fun i0 => bind getModel (fun m0 => k i0 m0)) i m o
      ↔ k i m i m o := by
  constructor
  · intro H
    exact bind_input_model_inv k i m o H
  · intro H
    exact spec_input_model_intro k i m o H


/- =========================================================================
   The shared recipe

   Every quadruple below walks the checker and
   its spec arm for arm, in the order the two definitions make their
   tests, so no test ever has to be commuted:

   (1) the `bind inputSpec ;; bind getModelSpec` prologue is peeled with
       `bind_ok0` (accepted outcomes) or `bind_unmodeled2` (declines);
       in the completeness directions the same prologue is inverted with
       the two bridges above ([bind_input_model_iff] /
       [bind_input_model_inv]) instead;
   (2) the fd dispatch is generalised (`generalize hq : fd_lookup … = q
       at H ⊢`) and then `cases`d, because the checker and the spec
       mention the SAME lookup under DIFFERENT nested constructor
       patterns, and `dsimp only` — not `simp` — is what reduces an
       already-`some`/`none`-headed `match` (the file kinds in particular
       leave an unreduced `match some (FdEntry.FdFile p off) with …`);
   (3) the effect is decomposed (`obtain ⟨ret, ws, zs, us, cs, ks⟩ :=
       eff`, then `ws` to `hd :: tl` and `hd` to `(a, bs)`, then the
       `cases tl <;> cases zs <;> …` cascade); the first goal after the
       cascade is the live shape, the rest are dead and fall to
       `all_goals (try dsimp only at H); all_goals (try contradiction)`
       (`contradiction`, not `nomatch`: an unreduced `if`-shaped `H` is
       not a constructor clash);
   (4) the leaves are [ret_only_ok_spec] (and plain `pure_ok` /
       `unmodeled_intro`), and the equalities a passing checker test
       encodes are extracted with `(Fs.bv_eqb_eq _ _).mp` /
       `(listN_eqb_eq _ _).mp` and rewritten on the GOAL (never `subst`,
       which would eliminate the parameter rather than the pattern
       variable).
   ========================================================================= -/

/-- `bind input k` at a fixed input.  The reader binds the
    input it was handed and changes nothing, so the chain is the
    continuation at that same input — the completeness directions below
    peel the `bind inputSpec ;; bind getModelSpec` prologue with this and
    [bind_getModel] instead of naming the continuation. -/
theorem bind_input_spec {A : Type} (k : SyscallInput → SysSpec A) (i : SyscallInput)
    (m : Model) (o : Outcome A Model event) :
    bind input k i m o ↔ k i i m o := by
  cases o with
  | ok x m2 evs =>
    simp only [LinuxSem.LinuxProcessSem.bind,
      LinuxSem.LinuxProcessSem.input]
    constructor
    · rintro ⟨x0, m1, evs1, evs2, h1, h2, h3⟩
      simp only [Outcome.ok.injEq] at h1
      obtain ⟨rfl, rfl, rfl⟩ := h1
      simp at h3
      subst h3
      exact h2
    · intro h
      exact ⟨i, m, [], evs, rfl, h, rfl⟩
  | unmodeled =>
    simp only [LinuxSem.LinuxProcessSem.bind,
      LinuxSem.LinuxProcessSem.input]
    constructor
    · rintro (h | ⟨x0, m1, evs1, h1, h2⟩)
      · exact absurd h (by simp)
      · obtain ⟨rfl, rfl, rfl⟩ := h1
        exact h2
    · intro h
      exact Or.inr ⟨i, m, [], rfl, h⟩

/-- The accepted fixed-return leaf of a checker-to-spec proof: the
    checker's `check_ret_only` said yes, so the spec's `ret_only` /
    `err_ret` leaf is the same `pure` (the two are definitionally equal,
    `err_ret e` being `ret_only (errno_ret e)`).  One step per leaf. -/
theorem ret_only_ok_spec {r : word} {eff : SyscallEffect} {m m' : Model}
    {evs : List event} (H : check_ret_only eff r m [] = .CheckOk m' evs)
    (i : SyscallInput) :
    LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only r i m (.ok eff m' evs) := by
  obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff eff r m [] m' evs).mp H
  simp only [LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only,
    LinuxSem.LinuxProcessSem.pure]

/- =========================================================================
   pread64 (67)
   ========================================================================= -/

theorem check_pread64_sound_ok (i : SyscallInput) (fd buf count pos : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_pread64 i fd buf count pos eff m = .CheckOk m' evs) :
    pread64_spec fd buf count pos i m (.ok eff m' evs) := by
  unfold pread64_spec
  simp only [check_pread64] at H
  by_cases hp : ppos_einvalb pos = true
  · rw [ite_eq_left hp] at H ⊢
    exact ret_only_ok_spec H i
  · rw [ite_eq_right hp] at H ⊢
    refine bind_ok0 (c := inputSpec) ?_ i m i m eff m' evs (input_ok i m) ?_
    try dsimp only
    refine bind_ok0 (c := getModelSpec) ?_ i m m m eff m' evs rfl ?_
    try dsimp only
    generalize hq : fd_lookup (m_fds m) fd = q at H ⊢
    cases q with
    | none =>
      try dsimp only at H ⊢
      exact ret_only_ok_spec H i
    | some e =>
      cases e with
      | FdChannel ch =>
        try dsimp only at H ⊢
        exact ret_only_ok_spec H i
      | FdFile p off =>
        try dsimp only at H ⊢
        by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
        · rw [ite_eq_left hak] at H ⊢
          exact ret_only_ok_spec H i
        · rw [ite_eq_right hak] at H ⊢
          by_cases hrp : rw_pos_einvalb pos (count.toNat : Int) = true
          · rw [ite_eq_left hrp] at H ⊢
            exact ret_only_ok_spec H i
          · rw [ite_eq_right hrp] at H ⊢
            cases hfs : Fs.fs_lookup (m_fs m) p with
            | none =>
              simp only [hfs] at H
              exact nomatch H
            | some data =>
              simp only [hfs] at H ⊢
              try dsimp only at H ⊢
              generalize hbs :
                Fs.file_read data pos (BitVec.ofInt 64 (rw_count_clamp count)) = bs
                at H ⊢
              generalize hw : read_bytes_map i.in_wmem buf (len_word bs) = w
                at H ⊢
              try dsimp only at H ⊢
              cases w with
              | none =>
                try dsimp only at H ⊢
                generalize hw1 : read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) = w1
                  at H ⊢
                try dsimp only at H ⊢
                cases w1 with
                | none =>
                  try dsimp only at H ⊢
                  exact ret_only_ok_spec H i
                | some w1 =>
                  try dsimp only at H ⊢
                  exact nomatch H
              | some w =>
                try dsimp only at H ⊢
                cases bs with
                | nil =>
                  try dsimp only at H ⊢
                  simp only [len_word] at H ⊢
                  try dsimp only at H ⊢
                  exact ret_only_ok_spec H i
                | cons b bsr =>
                  try dsimp only at H ⊢
                  obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
                  cases ws with
                  | nil => dsimp only at H; exact nomatch H
                  | cons hd tl =>
                    obtain ⟨a, bs'⟩ := hd
                    cases tl <;> cases zs <;> cases us <;> cases cs <;> cases ks
                    · dsimp only at H
                      by_cases hc : (bv_eqb a buf && listN_eqb bs' (b :: bsr)
                          && bv_eqb ret (len_word (b :: bsr))) = true
                      · rw [ite_eq_left hc] at H
                        cases H
                        have h1 : bv_eqb a buf = true ∧ listN_eqb bs' (b :: bsr) = true
                            ∧ bv_eqb ret (len_word (b :: bsr)) = true := by
                          simpa [Bool.and_eq_true, and_assoc] using hc
                        obtain ⟨ha, hbs', hret⟩ := h1
                        rw [(Fs.bv_eqb_eq a buf).mp ha,
                          (listN_eqb_eq bs' (b :: bsr)).mp hbs',
                          (Fs.bv_eqb_eq ret _).mp hret]
                        exact pure_ok _ i m
                      · rw [ite_eq_right hc] at H
                        exact nomatch H
                    all_goals (try dsimp only at H)
                    all_goals (try contradiction)
      | FdFileW p off =>
        try dsimp only at H ⊢
        exact ret_only_ok_spec H i
      | FdFileA p off =>
        try dsimp only at H ⊢
        exact ret_only_ok_spec H i
      | FdFileRW p off =>
        try dsimp only at H ⊢
        by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
        · rw [ite_eq_left hak] at H ⊢
          exact ret_only_ok_spec H i
        · rw [ite_eq_right hak] at H ⊢
          by_cases hrp : rw_pos_einvalb pos (count.toNat : Int) = true
          · rw [ite_eq_left hrp] at H ⊢
            exact ret_only_ok_spec H i
          · rw [ite_eq_right hrp] at H ⊢
            cases hfs : Fs.fs_lookup (m_fs m) p with
            | none =>
              simp only [hfs] at H
              exact nomatch H
            | some data =>
              simp only [hfs] at H ⊢
              try dsimp only at H ⊢
              generalize hbs :
                Fs.file_read data pos (BitVec.ofInt 64 (rw_count_clamp count)) = bs
                at H ⊢
              generalize hw : read_bytes_map i.in_wmem buf (len_word bs) = w
                at H ⊢
              try dsimp only at H ⊢
              cases w with
              | none =>
                try dsimp only at H ⊢
                generalize hw1 : read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) = w1
                  at H ⊢
                try dsimp only at H ⊢
                cases w1 with
                | none =>
                  try dsimp only at H ⊢
                  exact ret_only_ok_spec H i
                | some w1 =>
                  try dsimp only at H ⊢
                  exact nomatch H
              | some w =>
                try dsimp only at H ⊢
                cases bs with
                | nil =>
                  try dsimp only at H ⊢
                  simp only [len_word] at H ⊢
                  try dsimp only at H ⊢
                  exact ret_only_ok_spec H i
                | cons b bsr =>
                  try dsimp only at H ⊢
                  obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
                  cases ws with
                  | nil => dsimp only at H; exact nomatch H
                  | cons hd tl =>
                    obtain ⟨a, bs'⟩ := hd
                    cases tl <;> cases zs <;> cases us <;> cases cs <;> cases ks
                    · dsimp only at H
                      by_cases hc : (bv_eqb a buf && listN_eqb bs' (b :: bsr)
                          && bv_eqb ret (len_word (b :: bsr))) = true
                      · rw [ite_eq_left hc] at H
                        cases H
                        have h1 : bv_eqb a buf = true ∧ listN_eqb bs' (b :: bsr) = true
                            ∧ bv_eqb ret (len_word (b :: bsr)) = true := by
                          simpa [Bool.and_eq_true, and_assoc] using hc
                        obtain ⟨ha, hbs', hret⟩ := h1
                        rw [(Fs.bv_eqb_eq a buf).mp ha,
                          (listN_eqb_eq bs' (b :: bsr)).mp hbs',
                          (Fs.bv_eqb_eq ret _).mp hret]
                        exact pure_ok _ i m
                      · rw [ite_eq_right hc] at H
                        exact nomatch H
                    all_goals (try dsimp only at H)
                    all_goals (try contradiction)
      | FdDir =>
        try dsimp only at H ⊢
        by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
        · rw [ite_eq_left hak] at H ⊢
          exact ret_only_ok_spec H i
        · rw [ite_eq_right hak] at H ⊢
          by_cases hrp : rw_pos_einvalb pos (count.toNat : Int) = true
          · rw [ite_eq_left hrp] at H ⊢
            exact ret_only_ok_spec H i
          · rw [ite_eq_right hrp] at H ⊢
            exact ret_only_ok_spec H i
      | FdSocket sk =>
        try dsimp only at H ⊢
        exact ret_only_ok_spec H i
      | FdPipe id w =>
        try dsimp only at H ⊢
        exact ret_only_ok_spec H i
      | FdDevNull rd wr =>
        try dsimp only at H ⊢
        by_cases hrd : (!rd) = true
        · rw [ite_eq_left hrd] at H ⊢
          exact ret_only_ok_spec H i
        · rw [ite_eq_right hrd] at H ⊢
          by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
          · rw [ite_eq_left hak] at H ⊢
            exact ret_only_ok_spec H i
          · rw [ite_eq_right hak] at H ⊢
            by_cases hrp : rw_pos_einvalb pos (count.toNat : Int) = true
            · rw [ite_eq_left hrp] at H ⊢
              exact ret_only_ok_spec H i
            · rw [ite_eq_right hrp] at H ⊢
              exact ret_only_ok_spec H i
      | FdUrandom =>
        try dsimp only at H ⊢
        by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
        · rw [ite_eq_left hak] at H ⊢
          exact ret_only_ok_spec H i
        · rw [ite_eq_right hak] at H ⊢
          by_cases hrp : rw_pos_einvalb pos (count.toNat : Int) = true
          · rw [ite_eq_left hrp] at H ⊢
            exact ret_only_ok_spec H i
          · rw [ite_eq_right hrp] at H ⊢
            exact check_read_urandom_sound_ok i buf count eff m m' evs H

theorem check_pread64_sound_unmodeled (i : SyscallInput) (fd buf count pos : word)
    (eff : SyscallEffect) (m : Model)
    (H : check_pread64 i fd buf count pos eff m = .CheckUnmodeled) :
    pread64_spec fd buf count pos i m .unmodeled := by
  unfold pread64_spec
  simp only [check_pread64] at H
  by_cases hp : ppos_einvalb pos = true
  · rw [ite_eq_left hp] at H
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
  · rw [ite_eq_right hp] at H ⊢
    refine bind_unmodeled2 (c := inputSpec) ?_ i m i m [] (input_ok i m) ?_
    try dsimp only
    refine bind_unmodeled2 (c := getModelSpec) ?_ i m m m [] rfl ?_
    try dsimp only
    generalize hq : fd_lookup (m_fds m) fd = q at H ⊢
    cases q with
    | none =>
      try dsimp only at H
      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])
    | some e =>
      cases e with
      | FdChannel ch =>
        try dsimp only at H
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ESPIPE) m [])
      | FdFile p off =>
        try dsimp only at H ⊢
        by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
        · rw [ite_eq_left hak] at H
          exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
        · rw [ite_eq_right hak] at H ⊢
          by_cases hrp : rw_pos_einvalb pos (count.toNat : Int) = true
          · rw [ite_eq_left hrp] at H
            exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
          · rw [ite_eq_right hrp] at H ⊢
            cases hfs : Fs.fs_lookup (m_fs m) p with
            | none =>
              simp only [hfs] at H ⊢
              rfl
            | some data =>
              simp only [hfs] at H ⊢
              try dsimp only at H ⊢
              generalize hbs :
                Fs.file_read data pos (BitVec.ofInt 64 (rw_count_clamp count)) = bs
                at H ⊢
              generalize hw : read_bytes_map i.in_wmem buf (len_word bs) = w
                at H ⊢
              try dsimp only at H ⊢
              cases w with
              | none =>
                try dsimp only at H ⊢
                generalize hw1 : read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) = w1
                  at H ⊢
                try dsimp only at H ⊢
                cases w1 with
                | none =>
                  try dsimp only at H
                  exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
                | some w1 =>
                  rfl
              | some w =>
                try dsimp only at H ⊢
                cases bs with
                | nil =>
                  try dsimp only at H
                  exact absurd H
                    (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])
                | cons b bsr =>
                  try dsimp only at H ⊢
                  obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
                  cases ws with
                  | nil => dsimp only at H; exact nomatch H
                  | cons hd tl =>
                    obtain ⟨a, bs'⟩ := hd
                    cases tl <;> cases zs <;> cases us <;> cases cs <;> cases ks
                    · dsimp only at H
                      by_cases hc : (bv_eqb a buf && listN_eqb bs' (b :: bsr)
                          && bv_eqb ret (len_word (b :: bsr))) = true
                      · rw [ite_eq_left hc] at H
                        exact nomatch H
                      · rw [ite_eq_right hc] at H
                        exact nomatch H
                    all_goals (try dsimp only at H)
                    all_goals (try contradiction)
      | FdFileW p off =>
        try dsimp only at H
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])
      | FdFileA p off =>
        try dsimp only at H
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])
      | FdFileRW p off =>
        try dsimp only at H ⊢
        by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
        · rw [ite_eq_left hak] at H
          exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
        · rw [ite_eq_right hak] at H ⊢
          by_cases hrp : rw_pos_einvalb pos (count.toNat : Int) = true
          · rw [ite_eq_left hrp] at H
            exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
          · rw [ite_eq_right hrp] at H ⊢
            cases hfs : Fs.fs_lookup (m_fs m) p with
            | none =>
              simp only [hfs] at H ⊢
              rfl
            | some data =>
              simp only [hfs] at H ⊢
              try dsimp only at H ⊢
              generalize hbs :
                Fs.file_read data pos (BitVec.ofInt 64 (rw_count_clamp count)) = bs
                at H ⊢
              generalize hw : read_bytes_map i.in_wmem buf (len_word bs) = w
                at H ⊢
              try dsimp only at H ⊢
              cases w with
              | none =>
                try dsimp only at H ⊢
                generalize hw1 : read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) = w1
                  at H ⊢
                try dsimp only at H ⊢
                cases w1 with
                | none =>
                  try dsimp only at H
                  exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
                | some w1 =>
                  rfl
              | some w =>
                try dsimp only at H ⊢
                cases bs with
                | nil =>
                  try dsimp only at H
                  exact absurd H
                    (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])
                | cons b bsr =>
                  try dsimp only at H ⊢
                  obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
                  cases ws with
                  | nil => dsimp only at H; exact nomatch H
                  | cons hd tl =>
                    obtain ⟨a, bs'⟩ := hd
                    cases tl <;> cases zs <;> cases us <;> cases cs <;> cases ks
                    · dsimp only at H
                      by_cases hc : (bv_eqb a buf && listN_eqb bs' (b :: bsr)
                          && bv_eqb ret (len_word (b :: bsr))) = true
                      · rw [ite_eq_left hc] at H
                        exact nomatch H
                      · rw [ite_eq_right hc] at H
                        exact nomatch H
                    all_goals (try dsimp only at H)
                    all_goals (try contradiction)
      | FdDir =>
        try dsimp only at H
        by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
        · rw [ite_eq_left hak] at H
          exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
        · rw [ite_eq_right hak] at H
          by_cases hrp : rw_pos_einvalb pos (count.toNat : Int) = true
          · rw [ite_eq_left hrp] at H
            exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
          · rw [ite_eq_right hrp] at H
            exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EISDIR) m [])
      | FdSocket sk =>
        try dsimp only at H
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ESPIPE) m [])
      | FdPipe id w =>
        try dsimp only at H
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ESPIPE) m [])
      | FdDevNull rd wr =>
        try dsimp only at H
        by_cases hrd : (!rd) = true
        · rw [ite_eq_left hrd] at H
          exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])
        · rw [ite_eq_right hrd] at H
          by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
          · rw [ite_eq_left hak] at H
            exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
          · rw [ite_eq_right hak] at H
            by_cases hrp : rw_pos_einvalb pos (count.toNat : Int) = true
            · rw [ite_eq_left hrp] at H
              exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
            · rw [ite_eq_right hrp] at H
              exact absurd H
                (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])
      | FdUrandom =>
        try dsimp only at H ⊢
        by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
        · rw [ite_eq_left hak] at H
          exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
        · rw [ite_eq_right hak] at H ⊢
          by_cases hrp : rw_pos_einvalb pos (count.toNat : Int) = true
          · rw [ite_eq_left hrp] at H
            exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
          · rw [ite_eq_right hrp] at H ⊢
            exact check_read_urandom_sound_unmodeled i buf count eff m H

theorem check_pread64_complete_ok (i : SyscallInput) (fd buf count pos : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (Hs : pread64_spec fd buf count pos i m (.ok eff m' evs)) :
    check_pread64 i fd buf count pos eff m = .CheckOk m' evs := by
  unfold pread64_spec at Hs
  simp only [check_pread64]
  by_cases hp : ppos_einvalb pos = true
  · rw [ite_eq_left hp] at Hs ⊢
    cases Hs
    try simp [check_ret_only, bv_eqb_refl]
  · rw [ite_eq_right hp] at Hs ⊢
    simp only [inputSpec, getModelSpec, bind_input_spec, bind_getModel] at Hs
    generalize hq : fd_lookup (m_fds m) fd = q at Hs ⊢
    cases q with
    | none =>
      try dsimp only at Hs ⊢
      cases Hs
      try simp [check_ret_only, bv_eqb_refl]
    | some e =>
      cases e with
      | FdChannel ch =>
        try dsimp only at Hs ⊢
        cases Hs
        try simp [check_ret_only, bv_eqb_refl]
      | FdFile p off =>
        try dsimp only at Hs ⊢
        by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
        · rw [ite_eq_left hak] at Hs ⊢
          cases Hs
          try simp [check_ret_only, bv_eqb_refl]
        · rw [ite_eq_right hak] at Hs ⊢
          by_cases hrp : rw_pos_einvalb pos (count.toNat : Int) = true
          · rw [ite_eq_left hrp] at Hs ⊢
            cases Hs
            try simp [check_ret_only, bv_eqb_refl]
          · rw [ite_eq_right hrp] at Hs ⊢
            cases hfs : Fs.fs_lookup (m_fs m) p with
            | none =>
              simp only [hfs] at Hs
              cases Hs
            | some data =>
              simp only [hfs] at Hs ⊢
              try dsimp only at Hs ⊢
              generalize hbs : Fs.file_read data pos (BitVec.ofInt 64 (rw_count_clamp count)) = bs at Hs ⊢
              generalize hw : read_bytes_map i.in_wmem buf (len_word bs) = w at Hs ⊢
              try dsimp only at Hs ⊢
              cases w with
              | none =>
                try dsimp only at Hs ⊢
                generalize hw1 : read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) = w1 at Hs ⊢
                try dsimp only at Hs ⊢
                cases w1 with
                | none =>
                  try dsimp only at Hs ⊢
                  cases Hs
                  try simp [check_ret_only, bv_eqb_refl]
                | some w1 =>
                  try dsimp only at Hs ⊢
                  cases Hs
              | some w =>
                try dsimp only at Hs ⊢
                cases bs with
                | nil =>
                  try dsimp only at Hs ⊢
                  cases Hs
                  try simp [check_ret_only, bv_eqb_refl, delivered_writes, len_word]
                | cons b bsr =>
                  try dsimp only at Hs ⊢
                  cases Hs
                  try simp [bv_eqb_refl, listN_eqb_eq, delivered_writes, len_word]
      | FdFileW p off =>
        try dsimp only at Hs ⊢
        cases Hs
        try simp [check_ret_only, bv_eqb_refl]
      | FdFileA p off =>
        try dsimp only at Hs ⊢
        cases Hs
        try simp [check_ret_only, bv_eqb_refl]
      | FdFileRW p off =>
        try dsimp only at Hs ⊢
        by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
        · rw [ite_eq_left hak] at Hs ⊢
          cases Hs
          try simp [check_ret_only, bv_eqb_refl]
        · rw [ite_eq_right hak] at Hs ⊢
          by_cases hrp : rw_pos_einvalb pos (count.toNat : Int) = true
          · rw [ite_eq_left hrp] at Hs ⊢
            cases Hs
            try simp [check_ret_only, bv_eqb_refl]
          · rw [ite_eq_right hrp] at Hs ⊢
            cases hfs : Fs.fs_lookup (m_fs m) p with
            | none =>
              simp only [hfs] at Hs
              cases Hs
            | some data =>
              simp only [hfs] at Hs ⊢
              try dsimp only at Hs ⊢
              generalize hbs : Fs.file_read data pos (BitVec.ofInt 64 (rw_count_clamp count)) = bs at Hs ⊢
              generalize hw : read_bytes_map i.in_wmem buf (len_word bs) = w at Hs ⊢
              try dsimp only at Hs ⊢
              cases w with
              | none =>
                try dsimp only at Hs ⊢
                generalize hw1 : read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) = w1 at Hs ⊢
                try dsimp only at Hs ⊢
                cases w1 with
                | none =>
                  try dsimp only at Hs ⊢
                  cases Hs
                  try simp [check_ret_only, bv_eqb_refl]
                | some w1 =>
                  try dsimp only at Hs ⊢
                  cases Hs
              | some w =>
                try dsimp only at Hs ⊢
                cases bs with
                | nil =>
                  try dsimp only at Hs ⊢
                  cases Hs
                  try simp [check_ret_only, bv_eqb_refl, delivered_writes, len_word]
                | cons b bsr =>
                  try dsimp only at Hs ⊢
                  cases Hs
                  try simp [bv_eqb_refl, listN_eqb_eq, delivered_writes, len_word]
      | FdDir =>
        try dsimp only at Hs ⊢
        by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
        · rw [ite_eq_left hak] at Hs ⊢
          cases Hs
          try simp [check_ret_only, bv_eqb_refl]
        · rw [ite_eq_right hak] at Hs ⊢
          by_cases hrp : rw_pos_einvalb pos (count.toNat : Int) = true
          · rw [ite_eq_left hrp] at Hs ⊢
            cases Hs
            try simp [check_ret_only, bv_eqb_refl]
          · rw [ite_eq_right hrp] at Hs ⊢
            cases Hs
            try simp [check_ret_only, bv_eqb_refl]
      | FdSocket sk =>
        try dsimp only at Hs ⊢
        cases Hs
        try simp [check_ret_only, bv_eqb_refl]
      | FdPipe id w =>
        try dsimp only at Hs ⊢
        cases Hs
        try simp [check_ret_only, bv_eqb_refl]
      | FdDevNull rd wr =>
        try dsimp only at Hs ⊢
        by_cases hrd : (!rd) = true
        · rw [ite_eq_left hrd] at Hs ⊢
          cases Hs
          try simp [check_ret_only, bv_eqb_refl]
        · rw [ite_eq_right hrd] at Hs ⊢
          by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
          · rw [ite_eq_left hak] at Hs ⊢
            cases Hs
            try simp [check_ret_only, bv_eqb_refl]
          · rw [ite_eq_right hak] at Hs ⊢
            by_cases hrp : rw_pos_einvalb pos (count.toNat : Int) = true
            · rw [ite_eq_left hrp] at Hs ⊢
              cases Hs
              try simp [check_ret_only, bv_eqb_refl]
            · rw [ite_eq_right hrp] at Hs ⊢
              cases Hs
              try simp [check_ret_only, bv_eqb_refl]
      | FdUrandom =>
        try dsimp only at Hs ⊢
        by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
        · rw [ite_eq_left hak] at Hs ⊢
          cases Hs
          try simp [check_ret_only, bv_eqb_refl]
        · rw [ite_eq_right hak] at Hs ⊢
          by_cases hrp : rw_pos_einvalb pos (count.toNat : Int) = true
          · rw [ite_eq_left hrp] at Hs ⊢
            cases Hs
            try simp [check_ret_only, bv_eqb_refl]
          · rw [ite_eq_right hrp] at Hs ⊢
            exact check_read_urandom_complete_ok i buf count eff m m' evs Hs

theorem check_pread64_complete_unmodeled (i : SyscallInput) (fd buf count pos : word)
    (m : Model) (eff : SyscallEffect)
    (Hs : pread64_spec fd buf count pos i m .unmodeled) :
    check_pread64 i fd buf count pos eff m = .CheckUnmodeled := by
  unfold pread64_spec at Hs
  simp only [check_pread64]
  by_cases hp : ppos_einvalb pos = true
  · rw [ite_eq_left hp] at Hs ⊢
    cases Hs
  · rw [ite_eq_right hp] at Hs ⊢
    simp only [inputSpec, getModelSpec, bind_input_spec, bind_getModel] at Hs
    generalize hq : fd_lookup (m_fds m) fd = q at Hs ⊢
    cases q with
    | none =>
      try dsimp only at Hs ⊢
      cases Hs
    | some e =>
      cases e with
      | FdChannel ch =>
        try dsimp only at Hs ⊢
        cases Hs
      | FdFile p off =>
        try dsimp only at Hs ⊢
        by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
        · rw [ite_eq_left hak] at Hs ⊢
          cases Hs
        · rw [ite_eq_right hak] at Hs ⊢
          by_cases hrp : rw_pos_einvalb pos (count.toNat : Int) = true
          · rw [ite_eq_left hrp] at Hs ⊢
            cases Hs
          · rw [ite_eq_right hrp] at Hs ⊢
            cases hfs : Fs.fs_lookup (m_fs m) p with
            | none =>
              simp only [hfs] at Hs ⊢
              try rfl
            | some data =>
              simp only [hfs] at Hs ⊢
              try dsimp only at Hs ⊢
              generalize hbs : Fs.file_read data pos (BitVec.ofInt 64 (rw_count_clamp count)) = bs at Hs ⊢
              generalize hw : read_bytes_map i.in_wmem buf (len_word bs) = w at Hs ⊢
              try dsimp only at Hs ⊢
              cases w with
              | none =>
                try dsimp only at Hs ⊢
                generalize hw1 : read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) = w1 at Hs ⊢
                try dsimp only at Hs ⊢
                cases w1 with
                | none =>
                  try dsimp only at Hs ⊢
                  cases Hs
                | some w1 =>
                  try dsimp only at Hs ⊢
                  try rfl
              | some w =>
                try dsimp only at Hs ⊢
                cases bs with
                | nil =>
                  try dsimp only at Hs ⊢
                  cases Hs
                | cons b bsr =>
                  try dsimp only at Hs ⊢
                  cases Hs
      | FdFileW p off =>
        try dsimp only at Hs ⊢
        cases Hs
      | FdFileA p off =>
        try dsimp only at Hs ⊢
        cases Hs
      | FdFileRW p off =>
        try dsimp only at Hs ⊢
        by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
        · rw [ite_eq_left hak] at Hs ⊢
          cases Hs
        · rw [ite_eq_right hak] at Hs ⊢
          by_cases hrp : rw_pos_einvalb pos (count.toNat : Int) = true
          · rw [ite_eq_left hrp] at Hs ⊢
            cases Hs
          · rw [ite_eq_right hrp] at Hs ⊢
            cases hfs : Fs.fs_lookup (m_fs m) p with
            | none =>
              simp only [hfs] at Hs ⊢
              try rfl
            | some data =>
              simp only [hfs] at Hs ⊢
              try dsimp only at Hs ⊢
              generalize hbs : Fs.file_read data pos (BitVec.ofInt 64 (rw_count_clamp count)) = bs at Hs ⊢
              generalize hw : read_bytes_map i.in_wmem buf (len_word bs) = w at Hs ⊢
              try dsimp only at Hs ⊢
              cases w with
              | none =>
                try dsimp only at Hs ⊢
                generalize hw1 : read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) = w1 at Hs ⊢
                try dsimp only at Hs ⊢
                cases w1 with
                | none =>
                  try dsimp only at Hs ⊢
                  cases Hs
                | some w1 =>
                  try dsimp only at Hs ⊢
                  try rfl
              | some w =>
                try dsimp only at Hs ⊢
                cases bs with
                | nil =>
                  try dsimp only at Hs ⊢
                  cases Hs
                | cons b bsr =>
                  try dsimp only at Hs ⊢
                  cases Hs
      | FdDir =>
        try dsimp only at Hs ⊢
        by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
        · rw [ite_eq_left hak] at Hs ⊢
          cases Hs
        · rw [ite_eq_right hak] at Hs ⊢
          by_cases hrp : rw_pos_einvalb pos (count.toNat : Int) = true
          · rw [ite_eq_left hrp] at Hs ⊢
            cases Hs
          · rw [ite_eq_right hrp] at Hs ⊢
            cases Hs
      | FdSocket sk =>
        try dsimp only at Hs ⊢
        cases Hs
      | FdPipe id w =>
        try dsimp only at Hs ⊢
        cases Hs
      | FdDevNull rd wr =>
        try dsimp only at Hs ⊢
        by_cases hrd : (!rd) = true
        · rw [ite_eq_left hrd] at Hs ⊢
          cases Hs
        · rw [ite_eq_right hrd] at Hs ⊢
          by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
          · rw [ite_eq_left hak] at Hs ⊢
            cases Hs
          · rw [ite_eq_right hak] at Hs ⊢
            by_cases hrp : rw_pos_einvalb pos (count.toNat : Int) = true
            · rw [ite_eq_left hrp] at Hs ⊢
              cases Hs
            · rw [ite_eq_right hrp] at Hs ⊢
              cases Hs
      | FdUrandom =>
        try dsimp only at Hs ⊢
        by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
        · rw [ite_eq_left hak] at Hs ⊢
          cases Hs
        · rw [ite_eq_right hak] at Hs ⊢
          by_cases hrp : rw_pos_einvalb pos (count.toNat : Int) = true
          · rw [ite_eq_left hrp] at Hs ⊢
            cases Hs
          · rw [ite_eq_right hrp] at Hs ⊢
            exact check_read_urandom_complete_unmodeled i buf count m eff Hs

/-- Invert the `seqSpec (set_fs …) (record_copyins … (ret_only …))`
    stage of `pwrite64_spec`'s file arm: the accepted effect is the
    recorded ledger wrapped round the fixed return, the model is the file
    system update, and nothing was emitted. -/
theorem seqSpec_set_fs_record_ret_only_ok_inv (fs' : Fs.Fs) (reads : List (word × Nat))
    (r : word) (i : SyscallInput) (m : Model) (eff : SyscallEffect) (m' : Model)
    (evs : List event)
    (H : seqSpec (set_fs fs') (record_copyins reads (LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only r)) i m (.ok eff m' evs)) :
    eff = with_copyins reads (mkEffect r [] []) ∧ m' = with_fs fs' m ∧ evs = [] := by
  obtain ⟨u, m1, evs1, evs2, hm, hp, hevs⟩ := H
  simp only [set_fs, modifySpec, LinuxSem.LinuxProcessSem.modify] at hm
  cases hm
  obtain ⟨core, hcore, heff⟩ :=
    record_copyins_ok_inv reads (LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only r) i (with_fs fs' m) eff m' evs2 hp
  cases hcore
  simp only [List.append_nil] at heff
  simp only [List.nil_append] at hevs
  exact ⟨heff, rfl, hevs⟩

theorem check_pwrite64_sound_ok (i : SyscallInput) (fd buf count pos : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_pwrite64 i fd buf count pos eff m = .CheckOk m' evs) :
    pwrite64_spec fd buf count pos i m (.ok eff m' evs) := by
  unfold pwrite64_spec
  simp only [check_pwrite64] at H
  by_cases hp : ppos_einvalb pos = true
  · rw [ite_eq_left hp] at H ⊢
    exact ret_only_ok_spec H i
  · rw [ite_eq_right hp] at H ⊢
    refine bind_ok0 (c := inputSpec) ?_ i m i m eff m' evs (input_ok i m) ?_
    try dsimp only
    refine bind_ok0 (c := getModelSpec) ?_ i m m m eff m' evs rfl ?_
    try dsimp only
    generalize hq : fd_lookup (m_fds m) fd = q at H ⊢
    cases q with
    | none =>
      try dsimp only at H ⊢
      exact ret_only_ok_spec H i
    | some e =>
      cases e with
      | FdChannel ch =>
        try dsimp only at H ⊢
        exact ret_only_ok_spec H i
      | FdFile p off =>
        try dsimp only at H ⊢
        exact ret_only_ok_spec H i
      | FdFileW p off =>
        try dsimp only at H ⊢
        by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
        · rw [ite_eq_left hak] at H ⊢
          exact ret_only_ok_spec H i
        · rw [ite_eq_right hak] at H ⊢
          by_cases hrp : rw_pos_einvalb pos (count.toNat : Int) = true
          · rw [ite_eq_left hrp] at H ⊢
            exact ret_only_ok_spec H i
          · rw [ite_eq_right hrp] at H ⊢
            generalize hbs : write_source i.in_mem buf count = bs at H ⊢
            by_cases hz : (!(w_is0 count) && (bs.length == 0)) = true
            · rw [ite_eq_left hz] at H ⊢
              exact ret_only_ok_spec H i
            · rw [ite_eq_right hz] at H ⊢
              cases hfs : Fs.fs_lookup (m_fs m) p with
              | none =>
                simp only [hfs] at H
                exact nomatch H
              | some data =>
                simp only [hfs] at H ⊢
                try dsimp only at H ⊢
                by_cases hmg : (!(modeled_file_gap data pos bs)) = true
                · rw [ite_eq_left hmg] at H ⊢
                  exact nomatch H
                · rw [ite_eq_right hmg] at H ⊢
                  try dsimp only at H ⊢
                  by_cases hw : w_is0 count = true
                  · rw [ite_eq_left hw] at H ⊢
                    obtain ⟨rfl, rfl, rfl⟩ :=
                      (check_ret_only_ok_iff eff (len_word bs)
                        (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data pos bs)) m)
                        [] m' evs).mp H
                    simp only [set_fs, seqSpec]
                    exact bind_ok
                      (modifySpec (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data pos bs))))
                      (fun _ => LinuxSem.LinuxProcessSem.pure
                        (mkEffect (len_word bs) [] []))
                      i m () _ [] _ _ [] rfl rfl
                  · rw [ite_eq_right hw] at H ⊢
                    obtain ⟨heff, hm', hevs⟩ :=
                      (check_ret_only_copyins_ok_iff [(buf, bs.length)] eff (len_word bs)
                        (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data pos bs)) m)
                        [] m' evs).mp H
                    subst heff
                    subst hm'
                    subst hevs
                    simp only [set_fs, seqSpec]
                    try dsimp only
                    refine bind_ok
                      (modifySpec (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data pos bs))))
                      (fun _ => record_copyins [(buf, bs.length)] (LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only (len_word bs)))
                      i m () (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data pos bs)) m)
                      [] _ (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data pos bs)) m) []
                      rfl ?_
                    exact record_copyins_ok_empty (reads := [(buf, bs.length)]) rfl
                      (pure_ok _ i _)
      | FdFileA p off =>
        try dsimp only at H ⊢
        exact nomatch H
      | FdFileRW p off =>
        try dsimp only at H ⊢
        by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
        · rw [ite_eq_left hak] at H ⊢
          exact ret_only_ok_spec H i
        · rw [ite_eq_right hak] at H ⊢
          by_cases hrp : rw_pos_einvalb pos (count.toNat : Int) = true
          · rw [ite_eq_left hrp] at H ⊢
            exact ret_only_ok_spec H i
          · rw [ite_eq_right hrp] at H ⊢
            generalize hbs : write_source i.in_mem buf count = bs at H ⊢
            by_cases hz : (!(w_is0 count) && (bs.length == 0)) = true
            · rw [ite_eq_left hz] at H ⊢
              exact ret_only_ok_spec H i
            · rw [ite_eq_right hz] at H ⊢
              cases hfs : Fs.fs_lookup (m_fs m) p with
              | none =>
                simp only [hfs] at H
                exact nomatch H
              | some data =>
                simp only [hfs] at H ⊢
                try dsimp only at H ⊢
                by_cases hmg : (!(modeled_file_gap data pos bs)) = true
                · rw [ite_eq_left hmg] at H ⊢
                  exact nomatch H
                · rw [ite_eq_right hmg] at H ⊢
                  try dsimp only at H ⊢
                  by_cases hw : w_is0 count = true
                  · rw [ite_eq_left hw] at H ⊢
                    obtain ⟨rfl, rfl, rfl⟩ :=
                      (check_ret_only_ok_iff eff (len_word bs)
                        (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data pos bs)) m)
                        [] m' evs).mp H
                    simp only [set_fs, seqSpec]
                    exact bind_ok
                      (modifySpec (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data pos bs))))
                      (fun _ => LinuxSem.LinuxProcessSem.pure
                        (mkEffect (len_word bs) [] []))
                      i m () _ [] _ _ [] rfl rfl
                  · rw [ite_eq_right hw] at H ⊢
                    obtain ⟨heff, hm', hevs⟩ :=
                      (check_ret_only_copyins_ok_iff [(buf, bs.length)] eff (len_word bs)
                        (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data pos bs)) m)
                        [] m' evs).mp H
                    subst heff
                    subst hm'
                    subst hevs
                    simp only [set_fs, seqSpec]
                    try dsimp only
                    refine bind_ok
                      (modifySpec (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data pos bs))))
                      (fun _ => record_copyins [(buf, bs.length)] (LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only (len_word bs)))
                      i m () (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data pos bs)) m)
                      [] _ (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data pos bs)) m) []
                      rfl ?_
                    exact record_copyins_ok_empty (reads := [(buf, bs.length)]) rfl
                      (pure_ok _ i _)
      | FdDir =>
        try dsimp only at H ⊢
        exact ret_only_ok_spec H i
      | FdSocket sk =>
        try dsimp only at H ⊢
        exact ret_only_ok_spec H i
      | FdPipe id w =>
        try dsimp only at H ⊢
        exact ret_only_ok_spec H i
      | FdDevNull rd wr =>
        try dsimp only at H ⊢
        by_cases hwr : (!wr) = true
        · rw [ite_eq_left hwr] at H ⊢
          exact ret_only_ok_spec H i
        · rw [ite_eq_right hwr] at H ⊢
          by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
          · rw [ite_eq_left hak] at H ⊢
            exact ret_only_ok_spec H i
          · rw [ite_eq_right hak] at H ⊢
            by_cases hrp : rw_pos_einvalb pos (count.toNat : Int) = true
            · rw [ite_eq_left hrp] at H ⊢
              exact ret_only_ok_spec H i
            · rw [ite_eq_right hrp] at H ⊢
              exact ret_only_ok_spec H i
      | FdUrandom =>
        try dsimp only at H ⊢
        exact ret_only_ok_spec H i

/-- The first stage of `seqSpec (set_fs …) k` cannot decline —
    `set_fs` is a `modifySpec` — so a `seqSpec` decline is the second
    stage's, at the model the update left. -/
theorem seqSpec_set_fs_unmodeled_inv {A : Type} (fs' : Fs.Fs) (k : SysSpec A)
    (i : SyscallInput) (m : Model)
    (H : seqSpec (set_fs fs') k i m .unmodeled) : k i (with_fs fs' m) .unmodeled := by
  unfold seqSpec set_fs modifySpec LinuxSem.LinuxProcessSem.modify
    LinuxSem.LinuxProcessSem.bind at H
  rcases H with h | ⟨u, m1, evs1, h1, h2⟩
  · exact absurd h (by simp)
  · simp only [Outcome.ok.injEq] at h1
    obtain ⟨-, hm, -⟩ := h1
    subst hm
    simpa using h2

theorem check_pwrite64_sound_unmodeled (i : SyscallInput) (fd buf count pos : word)
    (eff : SyscallEffect) (m : Model)
    (H : check_pwrite64 i fd buf count pos eff m = .CheckUnmodeled) :
    pwrite64_spec fd buf count pos i m .unmodeled := by
  unfold pwrite64_spec
  simp only [check_pwrite64] at H
  by_cases hp : ppos_einvalb pos = true
  · rw [ite_eq_left hp] at H
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
  · rw [ite_eq_right hp] at H ⊢
    refine bind_unmodeled2 (c := inputSpec) ?_ i m i m [] (input_ok i m) ?_
    try dsimp only
    refine bind_unmodeled2 (c := getModelSpec) ?_ i m m m [] rfl ?_
    try dsimp only
    generalize hq : fd_lookup (m_fds m) fd = q at H ⊢
    cases q with
    | none =>
      try dsimp only at H
      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])
    | some e =>
      cases e with
      | FdChannel ch =>
        try dsimp only at H
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ESPIPE) m [])
      | FdFile p off =>
        try dsimp only at H
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])
      | FdFileW p off =>
        try dsimp only at H ⊢
        by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
        · rw [ite_eq_left hak] at H
          exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
        · rw [ite_eq_right hak] at H ⊢
          by_cases hrp : rw_pos_einvalb pos (count.toNat : Int) = true
          · rw [ite_eq_left hrp] at H
            exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
          · rw [ite_eq_right hrp] at H ⊢
            generalize hbs : write_source i.in_mem buf count = bs at H ⊢
            by_cases hz : (!(w_is0 count) && (bs.length == 0)) = true
            · rw [ite_eq_left hz] at H
              exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
            · rw [ite_eq_right hz] at H ⊢
              cases hfs : Fs.fs_lookup (m_fs m) p with
              | none =>
                simp only [hfs] at H ⊢
                try rfl
              | some data =>
                simp only [hfs] at H ⊢
                try dsimp only at H ⊢
                by_cases hmg : (!(modeled_file_gap data pos bs)) = true
                · rw [ite_eq_left hmg] at H ⊢
                  try rfl
                · rw [ite_eq_right hmg] at H ⊢
                  try dsimp only at H ⊢
                  by_cases hw : w_is0 count = true
                  · rw [ite_eq_left hw] at H
                    exact absurd H (check_ret_only_no_unmodeled eff (len_word bs)
                      (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data pos bs)) m) [])
                  · rw [ite_eq_right hw] at H
                    exact absurd H (check_ret_only_copyins_no_unmodeled [(buf, bs.length)]
                      eff (len_word bs)
                      (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data pos bs)) m) [])
      | FdFileA p off =>
        try dsimp only at H ⊢
        try rfl
      | FdFileRW p off =>
        try dsimp only at H ⊢
        by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
        · rw [ite_eq_left hak] at H
          exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
        · rw [ite_eq_right hak] at H ⊢
          by_cases hrp : rw_pos_einvalb pos (count.toNat : Int) = true
          · rw [ite_eq_left hrp] at H
            exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
          · rw [ite_eq_right hrp] at H ⊢
            generalize hbs : write_source i.in_mem buf count = bs at H ⊢
            by_cases hz : (!(w_is0 count) && (bs.length == 0)) = true
            · rw [ite_eq_left hz] at H
              exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
            · rw [ite_eq_right hz] at H ⊢
              cases hfs : Fs.fs_lookup (m_fs m) p with
              | none =>
                simp only [hfs] at H ⊢
                try rfl
              | some data =>
                simp only [hfs] at H ⊢
                try dsimp only at H ⊢
                by_cases hmg : (!(modeled_file_gap data pos bs)) = true
                · rw [ite_eq_left hmg] at H ⊢
                  try rfl
                · rw [ite_eq_right hmg] at H ⊢
                  try dsimp only at H ⊢
                  by_cases hw : w_is0 count = true
                  · rw [ite_eq_left hw] at H
                    exact absurd H (check_ret_only_no_unmodeled eff (len_word bs)
                      (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data pos bs)) m) [])
                  · rw [ite_eq_right hw] at H
                    exact absurd H (check_ret_only_copyins_no_unmodeled [(buf, bs.length)]
                      eff (len_word bs)
                      (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data pos bs)) m) [])
      | FdDir =>
        try dsimp only at H
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])
      | FdSocket sk =>
        try dsimp only at H
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ESPIPE) m [])
      | FdPipe id w =>
        try dsimp only at H
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ESPIPE) m [])
      | FdDevNull rd wr =>
        try dsimp only at H
        by_cases hwr : (!wr) = true
        · rw [ite_eq_left hwr] at H
          exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])
        · rw [ite_eq_right hwr] at H
          by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
          · rw [ite_eq_left hak] at H
            exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
          · rw [ite_eq_right hak] at H
            by_cases hrp : rw_pos_einvalb pos (count.toNat : Int) = true
            · rw [ite_eq_left hrp] at H
              exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
            · rw [ite_eq_right hrp] at H
              exact absurd H (check_ret_only_no_unmodeled eff
                (BitVec.ofInt 64 (rw_count_clamp count)) m [])
      | FdUrandom =>
        try dsimp only at H
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])

theorem check_pwrite64_complete_ok (i : SyscallInput) (fd buf count pos : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (Hs : pwrite64_spec fd buf count pos i m (.ok eff m' evs)) :
    check_pwrite64 i fd buf count pos eff m = .CheckOk m' evs := by
  unfold pwrite64_spec at Hs
  simp only [check_pwrite64]
  by_cases hp : ppos_einvalb pos = true
  · rw [ite_eq_left hp] at Hs ⊢
    cases Hs
    try simp [check_ret_only, bv_eqb_refl]
  · rw [ite_eq_right hp] at Hs ⊢
    simp only [inputSpec, getModelSpec, bind_input_spec, bind_getModel] at Hs
    generalize hq : fd_lookup (m_fds m) fd = q at Hs ⊢
    cases q with
    | none =>
      try dsimp only at Hs ⊢
      cases Hs
      try simp [check_ret_only, bv_eqb_refl]
    | some e =>
      cases e with
      | FdChannel ch =>
        try dsimp only at Hs ⊢
        cases Hs
        try simp [check_ret_only, bv_eqb_refl]
      | FdFile p off =>
        try dsimp only at Hs ⊢
        cases Hs
        try simp [check_ret_only, bv_eqb_refl]
      | FdFileW p off =>
        try dsimp only at Hs ⊢
        by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
        · rw [ite_eq_left hak] at Hs ⊢
          cases Hs
          try simp [check_ret_only, bv_eqb_refl]
        · rw [ite_eq_right hak] at Hs ⊢
          by_cases hrp : rw_pos_einvalb pos (count.toNat : Int) = true
          · rw [ite_eq_left hrp] at Hs ⊢
            cases Hs
            try simp [check_ret_only, bv_eqb_refl]
          · rw [ite_eq_right hrp] at Hs ⊢
            generalize hbs : write_source i.in_mem buf count = bs at Hs ⊢
            by_cases hz : (!(w_is0 count) && (bs.length == 0)) = true
            · rw [ite_eq_left hz] at Hs ⊢
              cases Hs
              try simp [check_ret_only, bv_eqb_refl]
            · rw [ite_eq_right hz] at Hs ⊢
              cases hfs : Fs.fs_lookup (m_fs m) p with
              | none =>
                simp only [hfs] at Hs
                cases Hs
              | some data =>
                simp only [hfs] at Hs ⊢
                try dsimp only at Hs ⊢
                by_cases hmg : (!(modeled_file_gap data pos bs)) = true
                · rw [ite_eq_left hmg] at Hs ⊢
                  cases Hs
                · rw [ite_eq_right hmg] at Hs ⊢
                  try dsimp only at Hs ⊢
                  by_cases hw : w_is0 count = true
                  · rw [ite_eq_left hw] at Hs ⊢
                    obtain ⟨heff, hm', hevs⟩ :=
                      seqSpec_modify_pure_ok_inv
                        (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data pos bs)))
                        (mkEffect (len_word bs) [] []) i m eff m' evs Hs
                    subst heff
                    subst hm'
                    subst hevs
                    try simp [check_ret_only, bv_eqb_refl]
                  · rw [ite_eq_right hw] at Hs ⊢
                    obtain ⟨heff, hm', hevs⟩ :=
                      seqSpec_set_fs_record_ret_only_ok_inv
                        (Fs.fs_set (m_fs m) p (Fs.file_write data pos bs))
                        [(buf, bs.length)] (len_word bs) i m eff m' evs Hs
                    subst heff
                    subst hm'
                    subst hevs
                    exact check_ret_only_copyins_refl [(buf, bs.length)] (len_word bs)
                      (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data pos bs)) m) []
      | FdFileA p off =>
        try dsimp only at Hs ⊢
        cases Hs
      | FdFileRW p off =>
        try dsimp only at Hs ⊢
        by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
        · rw [ite_eq_left hak] at Hs ⊢
          cases Hs
          try simp [check_ret_only, bv_eqb_refl]
        · rw [ite_eq_right hak] at Hs ⊢
          by_cases hrp : rw_pos_einvalb pos (count.toNat : Int) = true
          · rw [ite_eq_left hrp] at Hs ⊢
            cases Hs
            try simp [check_ret_only, bv_eqb_refl]
          · rw [ite_eq_right hrp] at Hs ⊢
            generalize hbs : write_source i.in_mem buf count = bs at Hs ⊢
            by_cases hz : (!(w_is0 count) && (bs.length == 0)) = true
            · rw [ite_eq_left hz] at Hs ⊢
              cases Hs
              try simp [check_ret_only, bv_eqb_refl]
            · rw [ite_eq_right hz] at Hs ⊢
              cases hfs : Fs.fs_lookup (m_fs m) p with
              | none =>
                simp only [hfs] at Hs
                cases Hs
              | some data =>
                simp only [hfs] at Hs ⊢
                try dsimp only at Hs ⊢
                by_cases hmg : (!(modeled_file_gap data pos bs)) = true
                · rw [ite_eq_left hmg] at Hs ⊢
                  cases Hs
                · rw [ite_eq_right hmg] at Hs ⊢
                  try dsimp only at Hs ⊢
                  by_cases hw : w_is0 count = true
                  · rw [ite_eq_left hw] at Hs ⊢
                    obtain ⟨heff, hm', hevs⟩ :=
                      seqSpec_modify_pure_ok_inv
                        (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data pos bs)))
                        (mkEffect (len_word bs) [] []) i m eff m' evs Hs
                    subst heff
                    subst hm'
                    subst hevs
                    try simp [check_ret_only, bv_eqb_refl]
                  · rw [ite_eq_right hw] at Hs ⊢
                    obtain ⟨heff, hm', hevs⟩ :=
                      seqSpec_set_fs_record_ret_only_ok_inv
                        (Fs.fs_set (m_fs m) p (Fs.file_write data pos bs))
                        [(buf, bs.length)] (len_word bs) i m eff m' evs Hs
                    subst heff
                    subst hm'
                    subst hevs
                    exact check_ret_only_copyins_refl [(buf, bs.length)] (len_word bs)
                      (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data pos bs)) m) []
      | FdDir =>
        try dsimp only at Hs ⊢
        cases Hs
        try simp [check_ret_only, bv_eqb_refl]
      | FdSocket sk =>
        try dsimp only at Hs ⊢
        cases Hs
        try simp [check_ret_only, bv_eqb_refl]
      | FdPipe id w =>
        try dsimp only at Hs ⊢
        cases Hs
        try simp [check_ret_only, bv_eqb_refl]
      | FdDevNull rd wr =>
        try dsimp only at Hs ⊢
        by_cases hwr : (!wr) = true
        · rw [ite_eq_left hwr] at Hs ⊢
          cases Hs
          try simp [check_ret_only, bv_eqb_refl]
        · rw [ite_eq_right hwr] at Hs ⊢
          by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
          · rw [ite_eq_left hak] at Hs ⊢
            cases Hs
            try simp [check_ret_only, bv_eqb_refl]
          · rw [ite_eq_right hak] at Hs ⊢
            by_cases hrp : rw_pos_einvalb pos (count.toNat : Int) = true
            · rw [ite_eq_left hrp] at Hs ⊢
              cases Hs
              try simp [check_ret_only, bv_eqb_refl]
            · rw [ite_eq_right hrp] at Hs ⊢
              cases Hs
              try simp [check_ret_only, bv_eqb_refl]
      | FdUrandom =>
        try dsimp only at Hs ⊢
        cases Hs
        try simp [check_ret_only, bv_eqb_refl]

theorem check_pwrite64_complete_unmodeled (i : SyscallInput) (fd buf count pos : word)
    (m : Model) (eff : SyscallEffect)
    (Hs : pwrite64_spec fd buf count pos i m .unmodeled) :
    check_pwrite64 i fd buf count pos eff m = .CheckUnmodeled := by
  unfold pwrite64_spec at Hs
  simp only [check_pwrite64]
  by_cases hp : ppos_einvalb pos = true
  · rw [ite_eq_left hp] at Hs ⊢
    cases Hs
  · rw [ite_eq_right hp] at Hs ⊢
    simp only [inputSpec, getModelSpec, bind_input_spec, bind_getModel] at Hs
    generalize hq : fd_lookup (m_fds m) fd = q at Hs ⊢
    cases q with
    | none =>
      try dsimp only at Hs ⊢
      cases Hs
    | some e =>
      cases e with
      | FdChannel ch =>
        try dsimp only at Hs ⊢
        cases Hs
      | FdFile p off =>
        try dsimp only at Hs ⊢
        cases Hs
      | FdFileW p off =>
        try dsimp only at Hs ⊢
        by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
        · rw [ite_eq_left hak] at Hs ⊢
          cases Hs
        · rw [ite_eq_right hak] at Hs ⊢
          by_cases hrp : rw_pos_einvalb pos (count.toNat : Int) = true
          · rw [ite_eq_left hrp] at Hs ⊢
            cases Hs
          · rw [ite_eq_right hrp] at Hs ⊢
            generalize hbs : write_source i.in_mem buf count = bs at Hs ⊢
            by_cases hz : (!(w_is0 count) && (bs.length == 0)) = true
            · rw [ite_eq_left hz] at Hs ⊢
              cases Hs
            · rw [ite_eq_right hz] at Hs ⊢
              cases hfs : Fs.fs_lookup (m_fs m) p with
              | none =>
                simp only [hfs] at Hs ⊢
                try rfl
              | some data =>
                simp only [hfs] at Hs ⊢
                try dsimp only at Hs ⊢
                by_cases hmg : (!(modeled_file_gap data pos bs)) = true
                · rw [ite_eq_left hmg] at Hs ⊢
                  try rfl
                · rw [ite_eq_right hmg] at Hs ⊢
                  try dsimp only at Hs ⊢
                  by_cases hw : w_is0 count = true
                  · rw [ite_eq_left hw] at Hs ⊢
                    exact absurd Hs (seqSpec_modify_pure_unmodeled_false
                      (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data pos bs)))
                      (mkEffect (len_word bs) [] []) i m)
                  · rw [ite_eq_right hw] at Hs ⊢
                    have hbad := seqSpec_set_fs_unmodeled_inv
                      (Fs.fs_set (m_fs m) p (Fs.file_write data pos bs))
                      (record_copyins [(buf, bs.length)]
                        (LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only
                          (len_word bs))) i m Hs
                    obtain hbad2 := record_copyins_unmodeled_inv [(buf, bs.length)]
                      (LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only
                        (len_word bs)) i _ hbad
                    simp only [LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only,
                      LinuxSem.LinuxProcessSem.pure] at hbad2
                    exact nomatch hbad2
      | FdFileA p off =>
        try dsimp only at Hs ⊢
        try rfl
      | FdFileRW p off =>
        try dsimp only at Hs ⊢
        by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
        · rw [ite_eq_left hak] at Hs ⊢
          cases Hs
        · rw [ite_eq_right hak] at Hs ⊢
          by_cases hrp : rw_pos_einvalb pos (count.toNat : Int) = true
          · rw [ite_eq_left hrp] at Hs ⊢
            cases Hs
          · rw [ite_eq_right hrp] at Hs ⊢
            generalize hbs : write_source i.in_mem buf count = bs at Hs ⊢
            by_cases hz : (!(w_is0 count) && (bs.length == 0)) = true
            · rw [ite_eq_left hz] at Hs ⊢
              cases Hs
            · rw [ite_eq_right hz] at Hs ⊢
              cases hfs : Fs.fs_lookup (m_fs m) p with
              | none =>
                simp only [hfs] at Hs ⊢
                try rfl
              | some data =>
                simp only [hfs] at Hs ⊢
                try dsimp only at Hs ⊢
                by_cases hmg : (!(modeled_file_gap data pos bs)) = true
                · rw [ite_eq_left hmg] at Hs ⊢
                  try rfl
                · rw [ite_eq_right hmg] at Hs ⊢
                  try dsimp only at Hs ⊢
                  by_cases hw : w_is0 count = true
                  · rw [ite_eq_left hw] at Hs ⊢
                    exact absurd Hs (seqSpec_modify_pure_unmodeled_false
                      (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data pos bs)))
                      (mkEffect (len_word bs) [] []) i m)
                  · rw [ite_eq_right hw] at Hs ⊢
                    have hbad := seqSpec_set_fs_unmodeled_inv
                      (Fs.fs_set (m_fs m) p (Fs.file_write data pos bs))
                      (record_copyins [(buf, bs.length)]
                        (LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only
                          (len_word bs))) i m Hs
                    obtain hbad2 := record_copyins_unmodeled_inv [(buf, bs.length)]
                      (LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only
                        (len_word bs)) i _ hbad
                    simp only [LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only,
                      LinuxSem.LinuxProcessSem.pure] at hbad2
                    exact nomatch hbad2
      | FdDir =>
        try dsimp only at Hs ⊢
        cases Hs
      | FdSocket sk =>
        try dsimp only at Hs ⊢
        cases Hs
      | FdPipe id w =>
        try dsimp only at Hs ⊢
        cases Hs
      | FdDevNull rd wr =>
        try dsimp only at Hs ⊢
        by_cases hwr : (!wr) = true
        · rw [ite_eq_left hwr] at Hs ⊢
          cases Hs
        · rw [ite_eq_right hwr] at Hs ⊢
          by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
          · rw [ite_eq_left hak] at Hs ⊢
            cases Hs
          · rw [ite_eq_right hak] at Hs ⊢
            by_cases hrp : rw_pos_einvalb pos (count.toNat : Int) = true
            · rw [ite_eq_left hrp] at Hs ⊢
              cases Hs
            · rw [ite_eq_right hrp] at Hs ⊢
              cases Hs
      | FdUrandom =>
        try dsimp only at Hs ⊢
        cases Hs


/- =========================================================================
   read (63)

   The four `check_read_*` lemmas below follow the header's recipe, with
   two bridges carrying the shape an inline `eapply bind_ok0` would:

   - [seqSpec_set_*_pure_ok] build a `seqSpec (set_X …) (pure e)` stage at
     its own accepted outcome (the update changes one component of the
     model and emits nothing);
   - [seqSpec_set_*_deliver_ok] build a read's delivery stage — advance
     the stream or the socket script, record one event per delivered
     byte, return the fixed effect — at its own accepted outcome.

   They are stated as OUTCOME CONSTRUCTORS rather than as inversions
   because every direction but the completeness one builds the spec's
   outcome, and the completeness one inverts the checker's leaf with
   [check_ret_only_ok_iff] / [check_ret_only_copyins_ok_iff] anyway.
   ========================================================================= -/

/-- `seqSpec (set_fds fds) (pure e)` at its own accepted
    outcome: the update moves the descriptor table and emits nothing. -/
theorem seqSpec_set_fds_pure_ok (fds : List (word × FdEntry)) (e : SyscallEffect)
    (i : SyscallInput) (m : Model) :
    seqSpec (set_fds fds) (pure e) i m (.ok e (with_fds fds m) []) :=
  ⟨(), with_fds fds m, [], [], rfl, rfl, rfl⟩

/-- The same for `set_pipes`. -/
theorem seqSpec_set_pipes_pure_ok (ps : List (word × PipeBuf)) (e : SyscallEffect)
    (i : SyscallInput) (m : Model) :
    seqSpec (set_pipes ps) (pure e) i m (.ok e (with_pipes ps m) []) :=
  ⟨(), with_pipes ps m, [], [], rfl, rfl, rfl⟩

/-- The RST / ETIMEDOUT arm's outcome — the socket's entry moves
    to `SkReset`, and the pending error is reported. -/
theorem seqSpec_set_fds_err_ret_ok (fds : List (word × FdEntry)) (e : Int)
    (i : SyscallInput) (m : Model) :
    seqSpec (set_fds fds)
      (LinuxSem.LinuxProcessSem.Sys.Uaccess.err_ret e) i m
      (.ok (mkEffect (errno_ret e) [] []) (with_fds fds m) []) :=
  ⟨(), with_fds fds m, [], [], rfl, rfl, rfl⟩

/-- The delivery stage of a channel read: advance the stream
    past the delivered bytes, record one `ReadEv` per byte, and return the
    fixed effect. -/
theorem seqSpec_set_stdin_deliver_ok (stdin : InputStream) (ch : word) (buf : word)
    (bs : List byte) (i : SyscallInput) (m : Model) :
    seqSpec (set_stdin stdin)
      (seqSpec (emit (bs.map (event.ReadEv ch)))
        (pure (mkEffect (len_word bs) [(buf, bs)] []))) i m
      (.ok (mkEffect (len_word bs) [(buf, bs)] [])
        (with_stdin stdin m) (bs.map (event.ReadEv ch))) := by
  refine ⟨(), with_stdin stdin m, [], bs.map (event.ReadEv ch), rfl, ?_, rfl⟩
  refine ⟨(), with_stdin stdin m, bs.map (event.ReadEv ch), [], rfl, rfl, ?_⟩
  simp

/-- The same delivery stage on a socket: the connection's script
    advances instead of the stream, and the descriptor is written back. -/
theorem seqSpec_set_fds_deliver_ok (fds : List (word × FdEntry)) (ch : word)
    (buf : word) (bs : List byte) (i : SyscallInput) (m : Model) :
    seqSpec (set_fds fds)
      (seqSpec (emit (bs.map (event.ReadEv ch)))
        (pure (mkEffect (len_word bs) [(buf, bs)] []))) i m
      (.ok (mkEffect (len_word bs) [(buf, bs)] []) (with_fds fds m)
        (bs.map (event.ReadEv ch))) := by
  refine ⟨(), with_fds fds m, [], bs.map (event.ReadEv ch), rfl, ?_, rfl⟩
  refine ⟨(), with_fds fds m, bs.map (event.ReadEv ch), [], rfl, rfl, ?_⟩
  simp

/-- Split `check_access_ok_zero` / `access_ok_zero` at the range
    verdict, in the checker's hypothesis and the spec's goal at once.
    ([Checks.Sys.Uaccess.ok_zero_cases] generalises only the goal, so the
    hypothesis keeps its `if`.) -/
macro "ok_zsplit " H:ident b:ident c:ident : tactic =>
  `(tactic| (try simp only [check_access_ok_zero] at $H:ident
             try simp only [LinuxSem.LinuxProcessSem.Sys.Uaccess.access_ok_zero]
             by_cases hok : access_okb $b (($c).toNat : Int) = true
             all_goals (first
               | rw [ite_eq_left hok] at $H:ident ⊢
               | rw [ite_eq_right hok] at $H:ident ⊢)))

theorem check_read_sound_ok (i : SyscallInput) (fd buf count : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_read i fd buf count eff m = .CheckOk m' evs) :
    read_spec fd buf count i m (.ok eff m' evs) := by
  unfold read_spec
  simp only [check_read] at H
  refine bind_ok0 (c := inputSpec) ?_ i m i m eff m' evs (input_ok i m) ?_
  try dsimp only
  refine bind_ok0 (c := getModelSpec) ?_ i m m m eff m' evs rfl ?_
  try dsimp only
  generalize hq : fd_lookup (m_fds m) fd = q at H ⊢
  cases q with
  | none =>
    try dsimp only at H ⊢
    exact ret_only_ok_spec H i
  | some e =>
    cases e with
    | FdChannel ch =>
      try dsimp only at H ⊢
      by_cases hw : (!(w_is0 ch)) = true
      · rw [ite_eq_left hw] at H ⊢
        exact ret_only_ok_spec H i
      · rw [ite_eq_right hw] at H ⊢
        by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
        · rw [ite_eq_left hak] at H ⊢
          exact ret_only_ok_spec H i
        · rw [ite_eq_right hak] at H ⊢
          by_cases hc : w_is0 count = true
          · rw [ite_eq_left hc] at H ⊢
            exact ret_only_ok_spec H i
          · rw [ite_eq_right hc] at H ⊢
            generalize hs : m_stdin m 0 = st at H ⊢
            cases st with
            | none =>
              try dsimp only at H ⊢
              exact ret_only_ok_spec H i
            | some b0 =>
              try dsimp only at H ⊢
              generalize hw1 : read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) = w1
                at H ⊢
              cases w1 with
              | none =>
                try dsimp only at H ⊢
                exact ret_only_ok_spec H i
              | some w1 =>
                try dsimp only at H ⊢
                generalize hwn : read_bytes_map i.in_wmem buf
                  (len_word (stream_take_z (m_stdin m) (rw_count_clamp count)).1) = wn
                  at H ⊢
                cases wn with
                | none => try dsimp only at H; exact nomatch H
                | some wn =>
                  try dsimp only at H ⊢
                  obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
                  cases ws with
                  | nil => dsimp only at H; exact nomatch H
                  | cons hd tl =>
                    obtain ⟨a, bs⟩ := hd
                    cases tl <;> cases zs <;> cases us <;> cases cs <;> cases ks
                    · dsimp only at H
                      by_cases hg : (bv_eqb a buf && bv_eqb ret (len_word bs)
                          && decide (1 ≤ (bs.length : Int))
                          && decide ((bs.length : Int) ≤ rw_count_clamp count)
                          && listN_eqb (stream_take (m_stdin m) bs.length).1 bs
                          && wmem_ok i buf (len_word bs)) = true
                      · rw [ite_eq_left hg] at H
                        cases H
                        have hg' : bv_eqb a buf = true
                            ∧ bv_eqb ret (len_word bs) = true
                            ∧ decide (1 ≤ (bs.length : Int)) = true
                            ∧ decide ((bs.length : Int) ≤ rw_count_clamp count) = true
                            ∧ listN_eqb (stream_take (m_stdin m) bs.length).1 bs = true
                            ∧ wmem_ok i buf (len_word bs) = true := by
                          simpa [Bool.and_eq_true, and_assoc] using hg
                        obtain ⟨ha, hret, hle1, hle2, htake, hw⟩ := hg'
                        have ha' : a = buf := (Fs.bv_eqb_eq a buf).mp ha
                        have hret' : ret = len_word bs := (Fs.bv_eqb_eq ret (len_word bs)).mp hret
                        rw [ha', hret']
                        refine ⟨bs, m, [], bs.map (event.ReadEv ch),
                          choose_ok _ bs i m ⟨?_, ?_, ?_, ?_⟩, ?_, rfl⟩
                        · exact of_decide_eq_true hle1
                        · exact of_decide_eq_true hle2
                        · exact (listN_eqb_eq _ _).mp htake
                        · exact (wmem_ok_true i buf (len_word bs)).mp hw
                        · exact seqSpec_set_stdin_deliver_ok _ ch buf bs i m
                      · rw [ite_eq_right hg] at H
                        exact nomatch H
                    all_goals (try dsimp only at H)
                    all_goals (try contradiction)
    | FdFile p off =>
      try dsimp only at H ⊢
      by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
      · rw [ite_eq_left hak] at H ⊢
        exact ret_only_ok_spec H i
      · rw [ite_eq_right hak] at H ⊢
        cases hfs : Fs.fs_lookup (m_fs m) p with
        | none =>
          simp only [hfs] at H
          exact nomatch H
        | some data =>
          simp only [hfs] at H ⊢
          try dsimp only at H ⊢
          generalize hbs : Fs.file_read data off (BitVec.ofInt 64 (rw_count_clamp count)) = bs
            at H ⊢
          generalize hw : read_bytes_map i.in_wmem buf (len_word bs) = w at H ⊢
          try dsimp only at H ⊢
          cases w with
          | none =>
            try dsimp only at H ⊢
            generalize hw1 : read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) = w1
              at H ⊢
            try dsimp only at H ⊢
            cases w1 with
            | none =>
              try dsimp only at H ⊢
              exact ret_only_ok_spec H i
            | some w1 =>
              try dsimp only at H ⊢
              exact nomatch H
          | some w =>
            try dsimp only at H ⊢
            cases bs with
            | nil =>
              try dsimp only at H ⊢
              obtain ⟨rfl, rfl, rfl⟩ :=
                (check_ret_only_ok_iff eff (BitVec.ofInt 64 0)
                  (with_fds (fd_insert (m_fds m) fd
                    (FdEntry.FdFile p (off + len_word []))) m) [] m' evs).mp H
              exact seqSpec_set_fds_pure_ok _ (mkEffect (BitVec.ofInt 64 0) [] []) i m
            | cons b bsr =>
              try dsimp only at H ⊢
              obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
              cases ws with
              | nil => dsimp only at H; exact nomatch H
              | cons hd tl =>
                obtain ⟨a, bs'⟩ := hd
                cases tl <;> cases zs <;> cases us <;> cases cs <;> cases ks
                · dsimp only at H
                  by_cases hc : (bv_eqb a buf && listN_eqb bs' (b :: bsr)
                      && bv_eqb ret (len_word (b :: bsr))) = true
                  · rw [ite_eq_left hc] at H
                    cases H
                    have hc' : bv_eqb a buf = true ∧ listN_eqb bs' (b :: bsr) = true
                        ∧ bv_eqb ret (len_word (b :: bsr)) = true := by
                      simpa [Bool.and_eq_true, and_assoc] using hc
                    obtain ⟨ha, hbs', hret⟩ := hc'
                    have ha' : a = buf := (Fs.bv_eqb_eq a buf).mp ha
                    have hbs'' : bs' = (b :: bsr) := (listN_eqb_eq bs' (b :: bsr)).mp hbs'
                    have hret' : ret = len_word (b :: bsr) :=
                      (Fs.bv_eqb_eq ret (len_word (b :: bsr))).mp hret
                    rw [ha', hbs'', hret']
                    exact seqSpec_set_fds_pure_ok _
                      (mkEffect (len_word (b :: bsr)) (delivered_writes buf (b :: bsr)) []) i m
                  · rw [ite_eq_right hc] at H
                    exact nomatch H
                all_goals (try dsimp only at H)
                all_goals (try contradiction)
    | FdFileW p off =>
      try dsimp only at H ⊢
      exact ret_only_ok_spec H i
    | FdFileA p off =>
      try dsimp only at H ⊢
      exact ret_only_ok_spec H i
    | FdFileRW p off =>
      try dsimp only at H ⊢
      by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
      · rw [ite_eq_left hak] at H ⊢
        exact ret_only_ok_spec H i
      · rw [ite_eq_right hak] at H ⊢
        cases hfs : Fs.fs_lookup (m_fs m) p with
        | none =>
          simp only [hfs] at H
          exact nomatch H
        | some data =>
          simp only [hfs] at H ⊢
          try dsimp only at H ⊢
          generalize hbs : Fs.file_read data off (BitVec.ofInt 64 (rw_count_clamp count)) = bs
            at H ⊢
          generalize hw : read_bytes_map i.in_wmem buf (len_word bs) = w at H ⊢
          try dsimp only at H ⊢
          cases w with
          | none =>
            try dsimp only at H ⊢
            generalize hw1 : read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) = w1
              at H ⊢
            try dsimp only at H ⊢
            cases w1 with
            | none =>
              try dsimp only at H ⊢
              exact ret_only_ok_spec H i
            | some w1 =>
              try dsimp only at H ⊢
              exact nomatch H
          | some w =>
            try dsimp only at H ⊢
            cases bs with
            | nil =>
              try dsimp only at H ⊢
              obtain ⟨rfl, rfl, rfl⟩ :=
                (check_ret_only_ok_iff eff (BitVec.ofInt 64 0)
                  (with_fds (fd_insert (m_fds m) fd
                    (FdEntry.FdFileRW p (off + len_word []))) m) [] m' evs).mp H
              exact seqSpec_set_fds_pure_ok _ (mkEffect (BitVec.ofInt 64 0) [] []) i m
            | cons b bsr =>
              try dsimp only at H ⊢
              obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
              cases ws with
              | nil => dsimp only at H; exact nomatch H
              | cons hd tl =>
                obtain ⟨a, bs'⟩ := hd
                cases tl <;> cases zs <;> cases us <;> cases cs <;> cases ks
                · dsimp only at H
                  by_cases hc : (bv_eqb a buf && listN_eqb bs' (b :: bsr)
                      && bv_eqb ret (len_word (b :: bsr))) = true
                  · rw [ite_eq_left hc] at H
                    cases H
                    have hc' : bv_eqb a buf = true ∧ listN_eqb bs' (b :: bsr) = true
                        ∧ bv_eqb ret (len_word (b :: bsr)) = true := by
                      simpa [Bool.and_eq_true, and_assoc] using hc
                    obtain ⟨ha, hbs', hret⟩ := hc'
                    have ha' : a = buf := (Fs.bv_eqb_eq a buf).mp ha
                    have hbs'' : bs' = (b :: bsr) := (listN_eqb_eq bs' (b :: bsr)).mp hbs'
                    have hret' : ret = len_word (b :: bsr) :=
                      (Fs.bv_eqb_eq ret (len_word (b :: bsr))).mp hret
                    rw [ha', hbs'', hret']
                    exact seqSpec_set_fds_pure_ok _
                      (mkEffect (len_word (b :: bsr)) (delivered_writes buf (b :: bsr)) []) i m
                  · rw [ite_eq_right hc] at H
                    exact nomatch H
                all_goals (try dsimp only at H)
                all_goals (try contradiction)
    | FdDir =>
      try dsimp only at H ⊢
      by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
      · rw [ite_eq_left hak] at H ⊢
        exact ret_only_ok_spec H i
      · rw [ite_eq_right hak] at H ⊢
        exact ret_only_ok_spec H i
    | FdSocket sk =>
      try dsimp only at H ⊢
      by_cases hmr : (!(modeled_rw_range buf count)) = true
      · rw [ite_eq_left hmr] at H
        exact nomatch H
      · rw [ite_eq_right hmr] at H ⊢
        by_cases hz : w_is0 count = true
        · rw [ite_eq_left hz] at H ⊢
          ok_zsplit H buf count
          · exact ret_only_ok_spec H i
          · exact ret_only_ok_spec H i
        · rw [ite_eq_right hz] at H ⊢
          cases sk with
          | SkFresh =>
            try dsimp only at H ⊢
            ok_zsplit H buf count
            · exact ret_only_ok_spec H i
            · exact ret_only_ok_spec H i
          | SkBound =>
            try dsimp only at H ⊢
            ok_zsplit H buf count
            · exact ret_only_ok_spec H i
            · exact ret_only_ok_spec H i
          | SkListening =>
            try dsimp only at H ⊢
            ok_zsplit H buf count
            · exact ret_only_ok_spec H i
            · exact ret_only_ok_spec H i
          | SkConnected peer ch rx =>
            try dsimp only at H ⊢
            generalize hrx : rx 0 = nx at H ⊢
            cases nx with
            | fin =>
              try dsimp only at H ⊢
              ok_zsplit H buf count
              · exact ret_only_ok_spec H i
              · exact ret_only_ok_spec H i
            | rst =>
              unfold check_socket_pending_error at H
              unfold socket_pending_error
              try dsimp only at H ⊢
              ok_zsplit H buf count
              · obtain ⟨rfl, rfl, rfl⟩ :=
                  (check_ret_only_ok_iff eff (errno_ret ECONNRESET)
                    (with_fds (fd_insert (m_fds m) fd
                      (FdEntry.FdSocket (SockState.SkReset peer ch))) m) [] m' evs).mp H
                exact seqSpec_set_fds_err_ret_ok _ ECONNRESET i m
              · exact ret_only_ok_spec H i
            | timedOut =>
              unfold check_socket_pending_error at H
              unfold socket_pending_error
              try dsimp only at H ⊢
              ok_zsplit H buf count
              · obtain ⟨rfl, rfl, rfl⟩ :=
                  (check_ret_only_ok_iff eff (errno_ret ETIMEDOUT)
                    (with_fds (fd_insert (m_fds m) fd
                      (FdEntry.FdSocket (SockState.SkReset peer ch))) m) [] m' evs).mp H
                exact seqSpec_set_fds_err_ret_ok _ ETIMEDOUT i m
              · exact ret_only_ok_spec H i
            | cons b0 =>
              try dsimp only at H ⊢
              generalize hw1 : read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) = w1
                at H ⊢
              cases w1 with
              | none =>
                try dsimp only at H ⊢
                exact ret_only_ok_spec H i
              | some w1 =>
                try dsimp only at H ⊢
                generalize hwn : read_bytes_map i.in_wmem buf
                  (len_word (net_take_z rx (rw_count_clamp count)).1) = wn at H ⊢
                cases wn with
                | none => try dsimp only at H; exact nomatch H
                | some wn =>
                  try dsimp only at H ⊢
                  obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
                  cases ws with
                  | nil => dsimp only at H; exact nomatch H
                  | cons hd tl =>
                    obtain ⟨a, bs⟩ := hd
                    cases tl <;> cases zs <;> cases us <;> cases cs <;> cases ks
                    · dsimp only at H
                      by_cases hg : (bv_eqb a buf && bv_eqb ret (len_word bs)
                          && decide (1 ≤ (bs.length : Int))
                          && decide ((bs.length : Int) ≤ rw_count_clamp count)
                          && listN_eqb (net_take rx bs.length).1 bs
                          && wmem_ok i buf (len_word bs)) = true
                      · rw [ite_eq_left hg] at H
                        cases H
                        have hg' : bv_eqb a buf = true
                            ∧ bv_eqb ret (len_word bs) = true
                            ∧ decide (1 ≤ (bs.length : Int)) = true
                            ∧ decide ((bs.length : Int) ≤ rw_count_clamp count) = true
                            ∧ listN_eqb (net_take rx bs.length).1 bs = true
                            ∧ wmem_ok i buf (len_word bs) = true := by
                          simpa [Bool.and_eq_true, and_assoc] using hg
                        obtain ⟨ha, hret, hle1, hle2, htake, hw⟩ := hg'
                        have ha' : a = buf := (Fs.bv_eqb_eq a buf).mp ha
                        have hret' : ret = len_word bs := (Fs.bv_eqb_eq ret (len_word bs)).mp hret
                        rw [ha', hret']
                        refine ⟨bs, m, [], bs.map (event.ReadEv ch),
                          choose_ok _ bs i m ⟨?_, ?_, ?_, ?_⟩, ?_, rfl⟩
                        · exact of_decide_eq_true hle1
                        · exact of_decide_eq_true hle2
                        · exact (listN_eqb_eq _ _).mp htake
                        · exact (wmem_ok_true i buf (len_word bs)).mp hw
                        · exact seqSpec_set_fds_deliver_ok _ ch buf bs i m
                      · rw [ite_eq_right hg] at H
                        exact nomatch H
                    all_goals (try dsimp only at H)
                    all_goals (try contradiction)
          | SkReset _ _ =>
            try dsimp only at H ⊢
            ok_zsplit H buf count
            · exact ret_only_ok_spec H i
            · exact ret_only_ok_spec H i
    | FdPipe id w =>
      try dsimp only at H ⊢
      by_cases hw : w = true
      · rw [ite_eq_left hw] at H ⊢
        exact ret_only_ok_spec H i
      · rw [ite_eq_right hw] at H ⊢
        by_cases hmr : (!(modeled_rw_range buf count)) = true
        · rw [ite_eq_left hmr] at H
          exact nomatch H
        · rw [ite_eq_right hmr] at H ⊢
          by_cases hz : w_is0 count = true
          · rw [ite_eq_left hz] at H ⊢
            ok_zsplit H buf count
            · exact ret_only_ok_spec H i
            · exact ret_only_ok_spec H i
          · rw [ite_eq_right hz] at H ⊢
            generalize hp : pipe_lookup (m_pipes m) id = p at H ⊢
            cases p with
            | none =>
              try dsimp only at H
              exact nomatch H
            | some qu =>
              obtain ⟨q, used⟩ := qu
              cases q with
              | nil =>
                try dsimp only at H ⊢
                by_cases hlv : pipe_end_live (m_fds m) id true = true
                · rw [ite_eq_left hlv] at H
                  exact nomatch H
                · rw [ite_eq_right hlv] at H ⊢
                  ok_zsplit H buf count
                  · exact ret_only_ok_spec H i
                  · exact ret_only_ok_spec H i
              | cons b bs0 =>
                try dsimp only at H ⊢
                generalize hw2 : read_bytes_map i.in_wmem buf
                  (len_word (pipe_take (b :: bs0) (rw_count_clamp count))) = w2 at H ⊢
                cases w2 with
                | none =>
                  try dsimp only at H ⊢
                  generalize hw1 : read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) = w1
                    at H ⊢
                  try dsimp only at H ⊢
                  cases w1 with
                  | none =>
                    try dsimp only at H ⊢
                    exact ret_only_ok_spec H i
                  | some w1 =>
                    try dsimp only at H ⊢
                    exact nomatch H
                | some w2 =>
                  try dsimp only at H ⊢
                  obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
                  cases zs <;> cases us <;> cases cs <;> cases ks
                  · dsimp only at H
                    by_cases hc : (writes_eqb ws
                        (delivered_writes buf (pipe_take (b :: bs0) (rw_count_clamp count)))
                        && bv_eqb ret
                          (len_word (pipe_take (b :: bs0) (rw_count_clamp count)))) = true
                    · rw [ite_eq_left hc] at H
                      cases H
                      have hc' : writes_eqb ws
                          (delivered_writes buf (pipe_take (b :: bs0) (rw_count_clamp count))) = true
                          ∧ bv_eqb ret
                            (len_word (pipe_take (b :: bs0) (rw_count_clamp count))) = true := by
                        simpa [Bool.and_eq_true, and_assoc] using hc
                      obtain ⟨hws, hret⟩ := hc'
                      rw [(writes_eqb_eq _ _).mp hws, (Fs.bv_eqb_eq ret _).mp hret]
                      exact seqSpec_set_pipes_pure_ok _
                        (mkEffect (len_word (pipe_take (b :: bs0) (rw_count_clamp count)))
                          (delivered_writes buf (pipe_take (b :: bs0) (rw_count_clamp count))) [])
                        i m
                    · rw [ite_eq_right hc] at H
                      exact nomatch H
                  all_goals (try dsimp only at H)
                  all_goals (try contradiction)
    | FdDevNull rd wr =>
      try dsimp only at H ⊢
      by_cases hrd : (!rd) = true
      · rw [ite_eq_left hrd] at H ⊢
        exact ret_only_ok_spec H i
      · rw [ite_eq_right hrd] at H ⊢
        simp only [check_access_ok_zero] at H
        by_cases hok : access_okb buf (count.toNat : Int) = true
        · rw [ite_eq_left hok] at H
          rw [ite_eq_right (by simp [hok])]
          exact ret_only_ok_spec H i
        · rw [ite_eq_right hok] at H
          rw [ite_eq_left (by simp [hok])]
          exact ret_only_ok_spec H i
    | FdUrandom =>
      try dsimp only at H ⊢
      by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
      · rw [ite_eq_left hak] at H ⊢
        exact ret_only_ok_spec H i
      · rw [ite_eq_right hak] at H ⊢
        exact check_read_urandom_sound_ok i buf count eff m m' evs H

/-! ### Inverting the delivery stages

  The other direction of the two builders above: the completeness
  directions have the SPEC's outcome in hand and need the effect, the model
  and the trace back out of it. -/

theorem seqSpec_set_fds_pure_ok_inv (fds : List (word × FdEntry)) (e : SyscallEffect)
    (i : SyscallInput) (m : Model) (eff : SyscallEffect) (m' : Model) (evs : List event)
    (H : seqSpec (set_fds fds) (pure e) i m (.ok eff m' evs)) :
    eff = e ∧ m' = with_fds fds m ∧ evs = [] := by
  obtain ⟨u, m1, ev1, ev2, h1, h2, h3⟩ := H
  simp only [set_fds, modifySpec, LinuxSem.LinuxProcessSem.modify] at h1
  cases h1
  cases h2
  simp only [List.nil_append] at h3
  cases h3
  exact ⟨rfl, rfl, rfl⟩

theorem seqSpec_set_pipes_pure_ok_inv (ps : List (word × PipeBuf)) (e : SyscallEffect)
    (i : SyscallInput) (m : Model) (eff : SyscallEffect) (m' : Model) (evs : List event)
    (H : seqSpec (set_pipes ps) (pure e) i m (.ok eff m' evs)) :
    eff = e ∧ m' = with_pipes ps m ∧ evs = [] := by
  obtain ⟨u, m1, ev1, ev2, h1, h2, h3⟩ := H
  simp only [set_pipes, modifySpec, LinuxSem.LinuxProcessSem.modify] at h1
  cases h1
  cases h2
  simp only [List.nil_append] at h3
  cases h3
  exact ⟨rfl, rfl, rfl⟩

theorem seqSpec_set_stdin_deliver_ok_inv (stdin : InputStream) (ch : word) (buf : word)
    (bs : List byte) (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (m' : Model) (evs : List event)
    (H : seqSpec (set_stdin stdin)
      (seqSpec (emit (bs.map (event.ReadEv ch)))
        (pure (mkEffect (len_word bs) [(buf, bs)] []))) i m (.ok eff m' evs)) :
    eff = mkEffect (len_word bs) [(buf, bs)] []
      ∧ m' = with_stdin stdin m ∧ evs = bs.map (event.ReadEv ch) := by
  obtain ⟨u, m1, ev1, ev2, h1, h2, h3⟩ := H
  simp only [set_stdin, modifySpec, LinuxSem.LinuxProcessSem.modify] at h1
  cases h1
  obtain ⟨y, m2, ev3, ev4, h4, h5, h6⟩ := h2
  cases h4
  cases h5
  simp only [List.nil_append, List.append_nil] at h3 h6
  cases h6
  cases h3
  exact ⟨rfl, rfl, rfl⟩

theorem seqSpec_set_fds_deliver_ok_inv (fds : List (word × FdEntry)) (ch : word)
    (buf : word) (bs : List byte) (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (m' : Model) (evs : List event)
    (H : seqSpec (set_fds fds)
      (seqSpec (emit (bs.map (event.ReadEv ch)))
        (pure (mkEffect (len_word bs) [(buf, bs)] []))) i m (.ok eff m' evs)) :
    eff = mkEffect (len_word bs) [(buf, bs)] []
      ∧ m' = with_fds fds m ∧ evs = bs.map (event.ReadEv ch) := by
  obtain ⟨u, m1, ev1, ev2, h1, h2, h3⟩ := H
  simp only [set_fds, modifySpec, LinuxSem.LinuxProcessSem.modify] at h1
  cases h1
  obtain ⟨y, m2, ev3, ev4, h4, h5, h6⟩ := h2
  cases h4
  cases h5
  simp only [List.nil_append, List.append_nil] at h3 h6
  cases h6
  cases h3
  exact ⟨rfl, rfl, rfl⟩

/- A `bind` whose first stage is a `choose` hands back the chosen value and
   the choice's premise: [LinuxSem.Checks.Sys.Prelude.choose_bind_ok_inv],
   in scope here through the [open LinuxSem.Checks.Sys.Prelude] above.  The
   claim is stated once, in the shared `Checks` prelude, and is not
   restated in this file. -/

/-- The channel read's delivered-prefix guard, evaluated at the
    spec's `choose` witness (`a = buf`, `ret = len_word bs`). -/
theorem read_channel_guard_true (i : SyscallInput) (m : Model) (count buf : word)
    (bs : List byte)
    (h1 : 1 ≤ (bs.length : Int))
    (h2 : (bs.length : Int) ≤ rw_count_clamp count)
    (htake : (stream_take (m_stdin m) bs.length).1 = bs)
    (hw : read_bytes_map i.in_wmem buf (len_word bs) ≠ none) :
    (bv_eqb buf buf && bv_eqb (len_word bs) (len_word bs)
      && decide (1 ≤ (bs.length : Int))
      && decide ((bs.length : Int) ≤ rw_count_clamp count)
      && listN_eqb (stream_take (m_stdin m) bs.length).1 bs
      && wmem_ok i buf (len_word bs)) = true := by
  simp only [bv_eqb_refl, decide_eq_true h1, decide_eq_true h2,
    (listN_eqb_eq _ _).mpr htake, (wmem_ok_true i buf (len_word bs)).mpr hw,
    Bool.and_true]

/-- The same guard on a socket, over the connection's script. -/
theorem read_socket_guard_true (i : SyscallInput) (count buf : word)
    (rx : NetStream) (bs : List byte)
    (h1 : 1 ≤ (bs.length : Int))
    (h2 : (bs.length : Int) ≤ rw_count_clamp count)
    (htake : (net_take rx bs.length).1 = bs)
    (hw : read_bytes_map i.in_wmem buf (len_word bs) ≠ none) :
    (bv_eqb buf buf && bv_eqb (len_word bs) (len_word bs)
      && decide (1 ≤ (bs.length : Int))
      && decide ((bs.length : Int) ≤ rw_count_clamp count)
      && listN_eqb (net_take rx bs.length).1 bs
      && wmem_ok i buf (len_word bs)) = true := by
  simp only [bv_eqb_refl, decide_eq_true h1, decide_eq_true h2,
    (listN_eqb_eq _ _).mpr htake, (wmem_ok_true i buf (len_word bs)).mpr hw,
    Bool.and_true]

theorem check_read_sound_unmodeled (i : SyscallInput) (fd buf count : word)
    (eff : SyscallEffect) (m : Model)
    (H : check_read i fd buf count eff m = .CheckUnmodeled) :
    read_spec fd buf count i m .unmodeled := by
  unfold read_spec
  simp only [check_read] at H
  refine bind_unmodeled2 (c := inputSpec) ?_ i m i m [] (input_ok i m) ?_
  try dsimp only
  refine bind_unmodeled2 (c := getModelSpec) ?_ i m m m [] rfl ?_
  try dsimp only
  generalize hq : fd_lookup (m_fds m) fd = q at H ⊢
  cases q with
  | none =>
    try dsimp only at H
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])
  | some e =>
    cases e with
    | FdChannel ch =>
      try dsimp only at H ⊢
      by_cases hw : (!(w_is0 ch)) = true
      · rw [ite_eq_left hw] at H
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])
      · rw [ite_eq_right hw] at H ⊢
        by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
        · rw [ite_eq_left hak] at H
          exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
        · rw [ite_eq_right hak] at H ⊢
          by_cases hc : w_is0 count = true
          · rw [ite_eq_left hc] at H
            exact absurd H
              (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])
          · rw [ite_eq_right hc] at H ⊢
            generalize hs : m_stdin m 0 = st at H ⊢
            cases st with
            | none =>
              try dsimp only at H
              exact absurd H
                (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])
            | some b0 =>
              try dsimp only at H ⊢
              generalize hw1 : read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) = w1
                at H ⊢
              cases w1 with
              | none =>
                try dsimp only at H
                exact absurd H
                  (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
              | some w1 =>
                try dsimp only at H ⊢
                generalize hwn : read_bytes_map i.in_wmem buf
                  (len_word (stream_take_z (m_stdin m) (rw_count_clamp count)).1) = wn
                  at H ⊢
                cases wn with
                | none => try dsimp only at H ⊢; rfl
                | some wn =>
                  try dsimp only at H ⊢
                  obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
                  cases ws with
                  | nil => dsimp only at H; exact nomatch H
                  | cons hd tl =>
                    obtain ⟨a, bs⟩ := hd
                    cases tl <;> cases zs <;> cases us <;> cases cs <;> cases ks
                    · dsimp only at H
                      by_cases hg : (bv_eqb a buf && bv_eqb ret (len_word bs)
                          && decide (1 ≤ (bs.length : Int))
                          && decide ((bs.length : Int) ≤ rw_count_clamp count)
                          && listN_eqb (stream_take (m_stdin m) bs.length).1 bs
                          && wmem_ok i buf (len_word bs)) = true
                      · rw [ite_eq_left hg] at H
                        exact nomatch H
                      · rw [ite_eq_right hg] at H
                        exact nomatch H
                    all_goals (try dsimp only at H)
                    all_goals (try contradiction)
    | FdFile p off =>
      try dsimp only at H ⊢
      by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
      · rw [ite_eq_left hak] at H
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
      · rw [ite_eq_right hak] at H ⊢
        cases hfs : Fs.fs_lookup (m_fs m) p with
        | none => simp only [hfs] at H ⊢; rfl
        | some data =>
          simp only [hfs] at H ⊢
          try dsimp only at H ⊢
          generalize hbs : Fs.file_read data off (BitVec.ofInt 64 (rw_count_clamp count)) = bs
            at H ⊢
          generalize hw : read_bytes_map i.in_wmem buf (len_word bs) = w at H ⊢
          try dsimp only at H ⊢
          cases w with
          | none =>
            try dsimp only at H ⊢
            generalize hw1 : read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) = w1
              at H ⊢
            try dsimp only at H ⊢
            cases w1 with
            | none =>
              try dsimp only at H
              exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
            | some w1 => try dsimp only at H ⊢; rfl
          | some w =>
            try dsimp only at H ⊢
            cases bs with
            | nil =>
              try dsimp only at H
              exact absurd H
                (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0)
                  (with_fds (fd_insert (m_fds m) fd
                    (FdEntry.FdFile p (off + len_word []))) m) [])
            | cons b bsr =>
              try dsimp only at H ⊢
              obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
              cases ws with
              | nil => dsimp only at H; exact nomatch H
              | cons hd tl =>
                obtain ⟨a, bs'⟩ := hd
                cases tl <;> cases zs <;> cases us <;> cases cs <;> cases ks
                · dsimp only at H
                  by_cases hc : (bv_eqb a buf && listN_eqb bs' (b :: bsr)
                      && bv_eqb ret (len_word (b :: bsr))) = true
                  · rw [ite_eq_left hc] at H
                    exact nomatch H
                  · rw [ite_eq_right hc] at H
                    exact nomatch H
                all_goals (try dsimp only at H)
                all_goals (try contradiction)
    | FdFileW p off =>
      try dsimp only at H
      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])
    | FdFileA p off =>
      try dsimp only at H
      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])
    | FdFileRW p off =>
      try dsimp only at H ⊢
      by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
      · rw [ite_eq_left hak] at H
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
      · rw [ite_eq_right hak] at H ⊢
        cases hfs : Fs.fs_lookup (m_fs m) p with
        | none => simp only [hfs] at H ⊢; rfl
        | some data =>
          simp only [hfs] at H ⊢
          try dsimp only at H ⊢
          generalize hbs : Fs.file_read data off (BitVec.ofInt 64 (rw_count_clamp count)) = bs
            at H ⊢
          generalize hw : read_bytes_map i.in_wmem buf (len_word bs) = w at H ⊢
          try dsimp only at H ⊢
          cases w with
          | none =>
            try dsimp only at H ⊢
            generalize hw1 : read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) = w1
              at H ⊢
            try dsimp only at H ⊢
            cases w1 with
            | none =>
              try dsimp only at H
              exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
            | some w1 => try dsimp only at H ⊢; rfl
          | some w =>
            try dsimp only at H ⊢
            cases bs with
            | nil =>
              try dsimp only at H
              exact absurd H
                (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0)
                  (with_fds (fd_insert (m_fds m) fd
                    (FdEntry.FdFileRW p (off + len_word []))) m) [])
            | cons b bsr =>
              try dsimp only at H ⊢
              obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
              cases ws with
              | nil => dsimp only at H; exact nomatch H
              | cons hd tl =>
                obtain ⟨a, bs'⟩ := hd
                cases tl <;> cases zs <;> cases us <;> cases cs <;> cases ks
                · dsimp only at H
                  by_cases hc : (bv_eqb a buf && listN_eqb bs' (b :: bsr)
                      && bv_eqb ret (len_word (b :: bsr))) = true
                  · rw [ite_eq_left hc] at H
                    exact nomatch H
                  · rw [ite_eq_right hc] at H
                    exact nomatch H
                all_goals (try dsimp only at H)
                all_goals (try contradiction)
    | FdDir =>
      try dsimp only at H ⊢
      by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
      · rw [ite_eq_left hak] at H
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
      · rw [ite_eq_right hak] at H
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EISDIR) m [])
    | FdSocket sk =>
      try dsimp only at H ⊢
      by_cases hmr : (!(modeled_rw_range buf count)) = true
      · rw [ite_eq_left hmr] at H ⊢
        rfl
      · rw [ite_eq_right hmr] at H ⊢
        by_cases hz : w_is0 count = true
        · rw [ite_eq_left hz] at H ⊢
          ok_zsplit H buf count
          · exact absurd H (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])
          · exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
        · rw [ite_eq_right hz] at H ⊢
          cases sk with
          | SkFresh =>
            try dsimp only at H ⊢
            ok_zsplit H buf count
            · exact absurd H
                (check_ret_only_no_unmodeled eff (errno_ret ENOTCONN) m [])
            · exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
          | SkBound =>
            try dsimp only at H ⊢
            ok_zsplit H buf count
            · exact absurd H
                (check_ret_only_no_unmodeled eff (errno_ret ENOTCONN) m [])
            · exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
          | SkListening =>
            try dsimp only at H ⊢
            ok_zsplit H buf count
            · exact absurd H
                (check_ret_only_no_unmodeled eff (errno_ret ENOTCONN) m [])
            · exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
          | SkConnected peer ch rx =>
            try dsimp only at H ⊢
            generalize hrx : rx 0 = nx at H ⊢
            cases nx with
            | fin =>
              try dsimp only at H ⊢
              ok_zsplit H buf count
              · exact absurd H
                  (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])
              · exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
            | rst =>
              unfold check_socket_pending_error at H
              unfold socket_pending_error
              try dsimp only at H ⊢
              ok_zsplit H buf count
              · exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ECONNRESET)
                  (with_fds (fd_insert (m_fds m) fd
                    (FdEntry.FdSocket (SockState.SkReset peer ch))) m) [])
              · exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
            | timedOut =>
              unfold check_socket_pending_error at H
              unfold socket_pending_error
              try dsimp only at H ⊢
              ok_zsplit H buf count
              · exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ETIMEDOUT)
                  (with_fds (fd_insert (m_fds m) fd
                    (FdEntry.FdSocket (SockState.SkReset peer ch))) m) [])
              · exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
            | cons b0 =>
              try dsimp only at H ⊢
              generalize hw1 : read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) = w1
                at H ⊢
              cases w1 with
              | none =>
                try dsimp only at H
                exact absurd H
                  (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
              | some w1 =>
                try dsimp only at H ⊢
                generalize hwn : read_bytes_map i.in_wmem buf
                  (len_word (net_take_z rx (rw_count_clamp count)).1) = wn at H ⊢
                cases wn with
                | none => try dsimp only at H ⊢; rfl
                | some wn =>
                  try dsimp only at H ⊢
                  obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
                  cases ws with
                  | nil => dsimp only at H; exact nomatch H
                  | cons hd tl =>
                    obtain ⟨a, bs⟩ := hd
                    cases tl <;> cases zs <;> cases us <;> cases cs <;> cases ks
                    · dsimp only at H
                      by_cases hg : (bv_eqb a buf && bv_eqb ret (len_word bs)
                          && decide (1 ≤ (bs.length : Int))
                          && decide ((bs.length : Int) ≤ rw_count_clamp count)
                          && listN_eqb (net_take rx bs.length).1 bs
                          && wmem_ok i buf (len_word bs)) = true
                      · rw [ite_eq_left hg] at H
                        exact nomatch H
                      · rw [ite_eq_right hg] at H
                        exact nomatch H
                    all_goals (try dsimp only at H)
                    all_goals (try contradiction)
          | SkReset _ _ =>
            try dsimp only at H ⊢
            ok_zsplit H buf count
            · exact absurd H
                (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])
            · exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
    | FdPipe id w =>
      try dsimp only at H ⊢
      by_cases hw : w = true
      · rw [ite_eq_left hw] at H
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])
      · rw [ite_eq_right hw] at H ⊢
        by_cases hmr : (!(modeled_rw_range buf count)) = true
        · rw [ite_eq_left hmr] at H ⊢
          rfl
        · rw [ite_eq_right hmr] at H ⊢
          by_cases hz : w_is0 count = true
          · rw [ite_eq_left hz] at H ⊢
            ok_zsplit H buf count
            · exact absurd H (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])
            · exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
          · rw [ite_eq_right hz] at H ⊢
            generalize hp : pipe_lookup (m_pipes m) id = p at H ⊢
            cases p with
            | none => try dsimp only at H ⊢; rfl
            | some qu =>
              obtain ⟨q, used⟩ := qu
              cases q with
              | nil =>
                try dsimp only at H ⊢
                by_cases hlv : pipe_end_live (m_fds m) id true = true
                · rw [ite_eq_left hlv] at H ⊢
                  rfl
                · rw [ite_eq_right hlv] at H ⊢
                  ok_zsplit H buf count
                  · exact absurd H
                      (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])
                  · exact absurd H
                      (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
              | cons b bs0 =>
                try dsimp only at H ⊢
                generalize hw2 : read_bytes_map i.in_wmem buf
                  (len_word (pipe_take (b :: bs0) (rw_count_clamp count))) = w2 at H ⊢
                cases w2 with
                | none =>
                  try dsimp only at H ⊢
                  generalize hw1 : read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) = w1
                    at H ⊢
                  try dsimp only at H ⊢
                  cases w1 with
                  | none =>
                    try dsimp only at H
                    exact absurd H
                      (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
                  | some w1 => try dsimp only at H ⊢; rfl
                | some w2 =>
                  try dsimp only at H ⊢
                  obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
                  cases zs <;> cases us <;> cases cs <;> cases ks
                  · dsimp only at H
                    by_cases hc : (writes_eqb ws
                        (delivered_writes buf (pipe_take (b :: bs0) (rw_count_clamp count)))
                        && bv_eqb ret
                          (len_word (pipe_take (b :: bs0) (rw_count_clamp count)))) = true
                    · rw [ite_eq_left hc] at H
                      exact nomatch H
                    · rw [ite_eq_right hc] at H
                      exact nomatch H
                  all_goals (try dsimp only at H)
                  all_goals (try contradiction)
    | FdDevNull rd wr =>
      try dsimp only at H ⊢
      by_cases hrd : (!rd) = true
      · rw [ite_eq_left hrd] at H
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])
      · rw [ite_eq_right hrd] at H ⊢
        simp only [check_access_ok_zero] at H
        by_cases hok : access_okb buf (count.toNat : Int) = true
        · rw [ite_eq_left hok] at H
          rw [ite_eq_right (by simp [hok])]
          exact absurd H (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])
        · rw [ite_eq_right hok] at H
          rw [ite_eq_left (by simp [hok])]
          exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
    | FdUrandom =>
      try dsimp only at H ⊢
      by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
      · rw [ite_eq_left hak] at H
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
      · rw [ite_eq_right hak] at H ⊢
        exact check_read_urandom_sound_unmodeled i buf count eff m H

/-! ### Building the checker's leaf from the spec's

  The guard lemmas the completeness direction rewrites with,
  once the spec's outcome has fixed the delivered prefix (`a = buf`,
  `ret = len_word bs`). -/

theorem read_file_guard_true (buf : word) (bs : List byte) :
    (bv_eqb buf buf && listN_eqb bs bs && bv_eqb (len_word bs) (len_word bs))
      = true := by
  simp only [bv_eqb_refl, (listN_eqb_eq bs bs).mpr rfl, Bool.and_true]

theorem read_pipe_guard_true (buf : word) (del : List byte) :
    (writes_eqb (delivered_writes buf del) (delivered_writes buf del)
      && bv_eqb (len_word del) (len_word del)) = true := by
  simp only [(writes_eqb_eq _ _).mpr rfl, bv_eqb_refl, Bool.and_true]

theorem seqSpec_set_fds_err_ret_ok_inv (fds : List (word × FdEntry)) (e : Int)
    (i : SyscallInput) (m : Model) (eff : SyscallEffect) (m' : Model) (evs : List event)
    (H : seqSpec (set_fds fds)
      (LinuxSem.LinuxProcessSem.Sys.Uaccess.err_ret e) i m (.ok eff m' evs)) :
    eff = mkEffect (errno_ret e) [] [] ∧ m' = with_fds fds m ∧ evs = [] := by
  obtain ⟨u, m1, ev1, ev2, h1, h2, h3⟩ := H
  simp only [set_fds, modifySpec, LinuxSem.LinuxProcessSem.modify] at h1
  cases h1
  simp only [LinuxSem.LinuxProcessSem.Sys.Uaccess.err_ret,
    LinuxSem.LinuxProcessSem.Sys.Uaccess.ret_only] at h2
  cases h2
  simp only [List.nil_append] at h3
  cases h3
  exact ⟨rfl, rfl, rfl⟩

macro "ok_zsplit_c " H:ident b:ident c:ident : tactic =>
  `(tactic| (try simp only [LinuxSem.LinuxProcessSem.Sys.Uaccess.access_ok_zero] at $H:ident
             try simp only [check_access_ok_zero]
             by_cases hok : access_okb $b (($c).toNat : Int) = true
             all_goals (first
               | rw [ite_eq_left hok] at $H:ident ⊢
               | rw [ite_eq_right hok] at $H:ident ⊢)))


/- =========================================================================
   read (63) — the completeness directions

   The sound directions above build the spec's outcome from the checker's;
   these invert the spec's outcome instead.  The prologue is
   peeled with [bind_input_spec] / [bind_getModel] (footgun (1) of the
   recipe), the leaves are inverted with [seqSpec_set_*_ok_inv], and the
   delivered-prefix guard is then closed by rewriting with the guard
   lemmas ([read_channel_guard_true] / [read_socket_guard_true] /
   [read_file_guard_true] / [read_pipe_guard_true]).
   ========================================================================= -/

theorem check_read_complete_ok (i : SyscallInput) (fd buf count : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (Hs : read_spec fd buf count i m (.ok eff m' evs)) :
    check_read i fd buf count eff m = .CheckOk m' evs := by
  unfold read_spec at Hs
  simp only [check_read]
  simp only [inputSpec, getModelSpec, bind_input_spec, bind_getModel] at Hs
  generalize hq : fd_lookup (m_fds m) fd = q at Hs ⊢
  cases q with
  | none =>
    try dsimp only at Hs ⊢
    cases Hs
    try simp [check_ret_only, bv_eqb_refl]
  | some e =>
    cases e with
    | FdChannel ch =>
      try dsimp only at Hs ⊢
      by_cases hw : (!(w_is0 ch)) = true
      · rw [ite_eq_left hw] at Hs ⊢
        cases Hs
        try simp [check_ret_only, bv_eqb_refl]
      · rw [ite_eq_right hw] at Hs ⊢
        by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
        · rw [ite_eq_left hak] at Hs ⊢
          cases Hs
          try simp [check_ret_only, bv_eqb_refl]
        · rw [ite_eq_right hak] at Hs ⊢
          by_cases hc : w_is0 count = true
          · rw [ite_eq_left hc] at Hs ⊢
            cases Hs
            try simp [check_ret_only, bv_eqb_refl]
          · rw [ite_eq_right hc] at Hs ⊢
            generalize hs : m_stdin m 0 = st at Hs ⊢
            cases st with
            | none =>
              try dsimp only at Hs ⊢
              cases Hs
              try simp [check_ret_only, bv_eqb_refl]
            | some b0 =>
              try dsimp only at Hs ⊢
              generalize hw1 : read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) = w1
                at Hs ⊢
              cases w1 with
              | none =>
                try dsimp only at Hs ⊢
                cases Hs
                try simp [check_ret_only, bv_eqb_refl]
              | some w1 =>
                try dsimp only at Hs ⊢
                generalize hwn : read_bytes_map i.in_wmem buf
                  (len_word (stream_take_z (m_stdin m) (rw_count_clamp count)).1) = wn
                  at Hs ⊢
                cases wn with
                | none =>
                  try dsimp only at Hs ⊢
                  cases Hs
                | some wn =>
                  try dsimp only at Hs ⊢
                  obtain ⟨bs, hP, Hk⟩ := choose_bind_ok_inv _ _ i m eff m' evs Hs
                  obtain ⟨h1, h2, htake, hwmem⟩ := hP
                  obtain ⟨heff, hm', hevs⟩ :=
                    seqSpec_set_stdin_deliver_ok_inv _ ch buf bs i m eff m' evs Hk
                  subst heff
                  subst hm'
                  subst hevs
                  try dsimp only
                  rw [read_channel_guard_true i m count buf bs h1 h2 htake hwmem]
                  try simp
    | FdFile p off =>
      try dsimp only at Hs ⊢
      by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
      · rw [ite_eq_left hak] at Hs ⊢
        cases Hs
        try simp [check_ret_only, bv_eqb_refl]
      · rw [ite_eq_right hak] at Hs ⊢
        cases hfs : Fs.fs_lookup (m_fs m) p with
        | none =>
          simp only [hfs] at Hs
          cases Hs
        | some data =>
          simp only [hfs] at Hs ⊢
          try dsimp only at Hs ⊢
          generalize hbs : Fs.file_read data off (BitVec.ofInt 64 (rw_count_clamp count)) = bs
            at Hs ⊢
          generalize hw : read_bytes_map i.in_wmem buf (len_word bs) = w at Hs ⊢
          try dsimp only at Hs ⊢
          cases w with
          | none =>
            try dsimp only at Hs ⊢
            generalize hw1 : read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) = w1
              at Hs ⊢
            try dsimp only at Hs ⊢
            cases w1 with
            | none =>
              try dsimp only at Hs ⊢
              cases Hs
              try simp [check_ret_only, bv_eqb_refl]
            | some w1 =>
              try dsimp only at Hs ⊢
              cases Hs
          | some w =>
            try dsimp only at Hs ⊢
            cases bs with
            | nil =>
              try dsimp only at Hs ⊢
              obtain ⟨heff, hm', hevs⟩ :=
                seqSpec_set_fds_pure_ok_inv _
                  (mkEffect (len_word []) (delivered_writes buf []) []) i m eff m' evs Hs
              subst heff
              subst hm'
              subst hevs
              try simp [check_ret_only, bv_eqb_refl, delivered_writes, len_word, mkEffect]
            | cons b bsr =>
              try dsimp only at Hs ⊢
              obtain ⟨heff, hm', hevs⟩ :=
                seqSpec_set_fds_pure_ok_inv _
                  (mkEffect (len_word (b :: bsr)) (delivered_writes buf (b :: bsr)) [])
                  i m eff m' evs Hs
              subst heff
              subst hm'
              subst hevs
              simp only [mkEffect, delivered_writes]
              try dsimp only
              rw [read_file_guard_true buf (b :: bsr)]
              try simp
    | FdFileW p off =>
      try dsimp only at Hs ⊢
      cases Hs
      try simp [check_ret_only, bv_eqb_refl]
    | FdFileA p off =>
      try dsimp only at Hs ⊢
      cases Hs
      try simp [check_ret_only, bv_eqb_refl]
    | FdFileRW p off =>
      try dsimp only at Hs ⊢
      by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
      · rw [ite_eq_left hak] at Hs ⊢
        cases Hs
        try simp [check_ret_only, bv_eqb_refl]
      · rw [ite_eq_right hak] at Hs ⊢
        cases hfs : Fs.fs_lookup (m_fs m) p with
        | none =>
          simp only [hfs] at Hs
          cases Hs
        | some data =>
          simp only [hfs] at Hs ⊢
          try dsimp only at Hs ⊢
          generalize hbs : Fs.file_read data off (BitVec.ofInt 64 (rw_count_clamp count)) = bs
            at Hs ⊢
          generalize hw : read_bytes_map i.in_wmem buf (len_word bs) = w at Hs ⊢
          try dsimp only at Hs ⊢
          cases w with
          | none =>
            try dsimp only at Hs ⊢
            generalize hw1 : read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) = w1
              at Hs ⊢
            try dsimp only at Hs ⊢
            cases w1 with
            | none =>
              try dsimp only at Hs ⊢
              cases Hs
              try simp [check_ret_only, bv_eqb_refl]
            | some w1 =>
              try dsimp only at Hs ⊢
              cases Hs
          | some w =>
            try dsimp only at Hs ⊢
            cases bs with
            | nil =>
              try dsimp only at Hs ⊢
              obtain ⟨heff, hm', hevs⟩ :=
                seqSpec_set_fds_pure_ok_inv _
                  (mkEffect (len_word []) (delivered_writes buf []) []) i m eff m' evs Hs
              subst heff
              subst hm'
              subst hevs
              try simp [check_ret_only, bv_eqb_refl, delivered_writes, len_word, mkEffect]
            | cons b bsr =>
              try dsimp only at Hs ⊢
              obtain ⟨heff, hm', hevs⟩ :=
                seqSpec_set_fds_pure_ok_inv _
                  (mkEffect (len_word (b :: bsr)) (delivered_writes buf (b :: bsr)) [])
                  i m eff m' evs Hs
              subst heff
              subst hm'
              subst hevs
              simp only [mkEffect, delivered_writes]
              try dsimp only
              rw [read_file_guard_true buf (b :: bsr)]
              try simp
    | FdDir =>
      try dsimp only at Hs ⊢
      by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
      · rw [ite_eq_left hak] at Hs ⊢
        cases Hs
        try simp [check_ret_only, bv_eqb_refl]
      · rw [ite_eq_right hak] at Hs ⊢
        cases Hs
        try simp [check_ret_only, bv_eqb_refl]
    | FdSocket sk =>
      try dsimp only at Hs ⊢
      by_cases hmr : (!(modeled_rw_range buf count)) = true
      · rw [ite_eq_left hmr] at Hs ⊢
        cases Hs
      · rw [ite_eq_right hmr] at Hs ⊢
        by_cases hz : w_is0 count = true
        · rw [ite_eq_left hz] at Hs ⊢
          ok_zsplit_c Hs buf count
          · cases Hs
            try simp [check_ret_only, bv_eqb_refl]
          · cases Hs
            try simp [check_ret_only, bv_eqb_refl]
        · rw [ite_eq_right hz] at Hs ⊢
          cases sk with
          | SkFresh =>
            try dsimp only at Hs ⊢
            ok_zsplit_c Hs buf count
            · cases Hs
              try simp [check_ret_only, bv_eqb_refl]
            · cases Hs
              try simp [check_ret_only, bv_eqb_refl]
          | SkBound =>
            try dsimp only at Hs ⊢
            ok_zsplit_c Hs buf count
            · cases Hs
              try simp [check_ret_only, bv_eqb_refl]
            · cases Hs
              try simp [check_ret_only, bv_eqb_refl]
          | SkListening =>
            try dsimp only at Hs ⊢
            ok_zsplit_c Hs buf count
            · cases Hs
              try simp [check_ret_only, bv_eqb_refl]
            · cases Hs
              try simp [check_ret_only, bv_eqb_refl]
          | SkConnected peer ch rx =>
            try dsimp only at Hs ⊢
            generalize hrx : rx 0 = nx at Hs ⊢
            cases nx with
            | fin =>
              try dsimp only at Hs ⊢
              ok_zsplit_c Hs buf count
              · cases Hs
                try simp [check_ret_only, bv_eqb_refl]
              · cases Hs
                try simp [check_ret_only, bv_eqb_refl]
            | rst =>
              unfold check_socket_pending_error
              unfold socket_pending_error at Hs
              try dsimp only at Hs ⊢
              ok_zsplit_c Hs buf count
              · obtain ⟨heff, hm', hevs⟩ :=
                  seqSpec_set_fds_err_ret_ok_inv _ ECONNRESET i m eff m' evs Hs
                subst heff
                subst hm'
                subst hevs
                simp only [mkEffect]
                try dsimp only
                try simp [check_ret_only, bv_eqb_refl]
              · cases Hs
                try simp [check_ret_only, bv_eqb_refl]
            | timedOut =>
              unfold check_socket_pending_error
              unfold socket_pending_error at Hs
              try dsimp only at Hs ⊢
              ok_zsplit_c Hs buf count
              · obtain ⟨heff, hm', hevs⟩ :=
                  seqSpec_set_fds_err_ret_ok_inv _ ETIMEDOUT i m eff m' evs Hs
                subst heff
                subst hm'
                subst hevs
                simp only [mkEffect]
                try dsimp only
                try simp [check_ret_only, bv_eqb_refl]
              · cases Hs
                try simp [check_ret_only, bv_eqb_refl]
            | cons b0 =>
              try dsimp only at Hs ⊢
              generalize hw1 : read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) = w1
                at Hs ⊢
              cases w1 with
              | none =>
                try dsimp only at Hs ⊢
                cases Hs
                try simp [check_ret_only, bv_eqb_refl]
              | some w1 =>
                try dsimp only at Hs ⊢
                generalize hwn : read_bytes_map i.in_wmem buf
                  (len_word (net_take_z rx (rw_count_clamp count)).1) = wn at Hs ⊢
                cases wn with
                | none =>
                  try dsimp only at Hs ⊢
                  cases Hs
                | some wn =>
                  try dsimp only at Hs ⊢
                  obtain ⟨bs, hP, Hk⟩ := choose_bind_ok_inv _ _ i m eff m' evs Hs
                  obtain ⟨h1, h2, htake, hwmem⟩ := hP
                  obtain ⟨heff, hm', hevs⟩ :=
                    seqSpec_set_fds_deliver_ok_inv _ ch buf bs i m eff m' evs Hk
                  subst heff
                  subst hm'
                  subst hevs
                  try dsimp only
                  rw [read_socket_guard_true i count buf rx bs h1 h2 htake hwmem]
                  try simp
          | SkReset _ _ =>
            try dsimp only at Hs ⊢
            ok_zsplit_c Hs buf count
            · cases Hs
              try simp [check_ret_only, bv_eqb_refl]
            · cases Hs
              try simp [check_ret_only, bv_eqb_refl]
    | FdPipe id w =>
      try dsimp only at Hs ⊢
      by_cases hw : w = true
      · rw [ite_eq_left hw] at Hs ⊢
        cases Hs
        try simp [check_ret_only, bv_eqb_refl]
      · rw [ite_eq_right hw] at Hs ⊢
        by_cases hmr : (!(modeled_rw_range buf count)) = true
        · rw [ite_eq_left hmr] at Hs ⊢
          cases Hs
        · rw [ite_eq_right hmr] at Hs ⊢
          by_cases hz : w_is0 count = true
          · rw [ite_eq_left hz] at Hs ⊢
            ok_zsplit_c Hs buf count
            · cases Hs
              try simp [check_ret_only, bv_eqb_refl]
            · cases Hs
              try simp [check_ret_only, bv_eqb_refl]
          · rw [ite_eq_right hz] at Hs ⊢
            generalize hp : pipe_lookup (m_pipes m) id = p at Hs ⊢
            cases p with
            | none =>
              try dsimp only at Hs ⊢
              cases Hs
            | some qu =>
              obtain ⟨q, used⟩ := qu
              cases q with
              | nil =>
                try dsimp only at Hs ⊢
                by_cases hlv : pipe_end_live (m_fds m) id true = true
                · rw [ite_eq_left hlv] at Hs ⊢
                  cases Hs
                · rw [ite_eq_right hlv] at Hs ⊢
                  ok_zsplit_c Hs buf count
                  · cases Hs
                    try simp [check_ret_only, bv_eqb_refl]
                  · cases Hs
                    try simp [check_ret_only, bv_eqb_refl]
              | cons b bs0 =>
                try dsimp only at Hs ⊢
                generalize hw2 : read_bytes_map i.in_wmem buf
                  (len_word (pipe_take (b :: bs0) (rw_count_clamp count))) = w2 at Hs ⊢
                cases w2 with
                | none =>
                  try dsimp only at Hs ⊢
                  generalize hw1 : read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) = w1
                    at Hs ⊢
                  try dsimp only at Hs ⊢
                  cases w1 with
                  | none =>
                    try dsimp only at Hs ⊢
                    cases Hs
                    try simp [check_ret_only, bv_eqb_refl]
                  | some w1 =>
                    try dsimp only at Hs ⊢
                    cases Hs
                | some w2 =>
                  try dsimp only at Hs ⊢
                  obtain ⟨heff, hm', hevs⟩ :=
                    seqSpec_set_pipes_pure_ok_inv _
                      (mkEffect (len_word (pipe_take (b :: bs0) (rw_count_clamp count)))
                        (delivered_writes buf (pipe_take (b :: bs0) (rw_count_clamp count))) [])
                      i m eff m' evs Hs
                  subst heff
                  subst hm'
                  subst hevs
                  try dsimp only
                  rw [read_pipe_guard_true buf (pipe_take (b :: bs0) (rw_count_clamp count))]
                  try simp
    | FdDevNull rd wr =>
      try dsimp only at Hs ⊢
      by_cases hrd : (!rd) = true
      · rw [ite_eq_left hrd] at Hs ⊢
        cases Hs
        try simp [check_ret_only, bv_eqb_refl]
      · rw [ite_eq_right hrd] at Hs ⊢
        -- the spec writes this arm's range test NEGATED (`if !access_okb …
        -- then -EFAULT`), the checker's `check_access_ok_zero` positively,
        -- so the split has to pick its polarity per side
        simp only [check_access_ok_zero]
        by_cases hok : access_okb buf (count.toNat : Int) = true
        · rw [ite_eq_right (by simp [hok])] at Hs
          rw [ite_eq_left hok]
          cases Hs
          try simp [check_ret_only, bv_eqb_refl]
        · rw [ite_eq_left (by simp [hok])] at Hs
          rw [ite_eq_right hok]
          cases Hs
          try simp [check_ret_only, bv_eqb_refl]
    | FdUrandom =>
      try dsimp only at Hs ⊢
      by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
      · rw [ite_eq_left hak] at Hs ⊢
        cases Hs
        try simp [check_ret_only, bv_eqb_refl]
      · rw [ite_eq_right hak] at Hs ⊢
        exact check_read_urandom_complete_ok i buf count eff m m' evs Hs


/-! ### A spec stage that cannot decline

  The completeness directions invert a spec's `.unmodeled` outcome, and
  every leaf but the one the arm means to decline at is a stage that CANNOT
  decline: `pure`, `emit`, `choose`, `modifySpec`, and
  the `seqSpec` / `bind` chains built out of them.  The lemmas below say
  so once each, so the completeness proofs can knock those branches out
  with `absurd Hs (…)` instead of re-deriving it per arm. -/

theorem pure_no_unmodeled {A : Type} (x : A) (i : SyscallInput) (m : Model) :
    ¬ (pure x : SysSpec A) i m .unmodeled := by
  intro h
  exact nomatch h

theorem emit_no_unmodeled (evs : List event) (i : SyscallInput) (m : Model) :
    ¬ emit evs i m .unmodeled := by
  intro h
  exact nomatch h

theorem choose_no_unmodeled {A : Type} (P : A → Prop) (i : SyscallInput) (m : Model) :
    ¬ (choose P : SysSpec A) i m .unmodeled := by
  rintro ⟨x, -, h⟩
  exact nomatch h

theorem bind_no_unmodeled {A B : Type} (c : SysSpec A) (k : A → SysSpec B)
    (i : SyscallInput) (m : Model)
    (hc : ¬ c i m .unmodeled)
    (hk : ∀ (a : A) (m1 : Model) (evs1 : List event),
      c i m (.ok a m1 evs1) → ¬ k a i m1 .unmodeled) :
    ¬ bind c k i m .unmodeled := by
  intro H
  simp only [LinuxSem.LinuxProcessSem.bind] at H
  rcases H with h | ⟨a, m1, evs1, h1, h2⟩
  · exact hc h
  · exact hk a m1 evs1 h1 h2

theorem seqSpec_no_unmodeled {A : Type} (c : SysSpec Unit) (k : SysSpec A)
    (i : SyscallInput) (m : Model)
    (hc : ¬ c i m .unmodeled)
    (hk : ∀ (u : Unit) (m1 : Model) (evs1 : List event),
      c i m (.ok u m1 evs1) → ¬ k i m1 .unmodeled) :
    ¬ seqSpec c k i m .unmodeled := by
  intro H
  simp only [seqSpec, LinuxSem.LinuxProcessSem.bind] at H
  rcases H with h | ⟨u, m1, evs1, h1, h2⟩
  · exact hc h
  · exact hk u m1 evs1 h1 h2

/-- `modifySpec f ;; k` cannot decline: the update always succeeds and the
    continuation runs at the updated model. -/
theorem modifySeq_no_unmodeled {A : Type} (f : Model → Model) (k : SysSpec A)
    (i : SyscallInput) (m : Model) (hk : ¬ k i (f m) .unmodeled) :
    ¬ seqSpec (modifySpec f) k i m .unmodeled := by
  refine seqSpec_no_unmodeled (modifySpec f) k i m (modifySpec_no_unmodeled f i m) ?_
  intro u m1 evs1 h
  simp only [modifySpec, LinuxSem.LinuxProcessSem.modify,
    Outcome.ok.injEq] at h
  obtain ⟨-, hm, -⟩ := h
  subst hm
  exact hk

/-- `emit evs ;; k` cannot decline, and changes nothing. -/
theorem emitSeq_no_unmodeled {A : Type} (evs : List event) (k : SysSpec A)
    (i : SyscallInput) (m : Model) (hk : ¬ k i m .unmodeled) :
    ¬ seqSpec (emit evs) k i m .unmodeled := by
  refine seqSpec_no_unmodeled (emit evs) k i m (emit_no_unmodeled evs i m) ?_
  intro u m1 evs1 h
  simp only [emit, Outcome.ok.injEq] at h
  obtain ⟨-, hm, -⟩ := h
  subst hm
  exact hk

/-- The read delivery stage of a channel or a socket: cannot decline. -/
theorem deliverSeq_no_unmodeled (f : Model → Model) (evs : List event)
    (e : SyscallEffect) (i : SyscallInput) (m : Model) :
    ¬ seqSpec (modifySpec f) (seqSpec (emit evs) (pure e)) i m .unmodeled :=
  modifySeq_no_unmodeled f _ i m (emitSeq_no_unmodeled evs _ i (f m) (pure_no_unmodeled e i (f m)))

/-- `choose P ;; k` cannot decline when `k` cannot, at any chosen value
    (`choose` leaves the model alone). -/
theorem choose_bind_no_unmodeled {B : Type} (P : List byte → Prop)
    (k : List byte → SysSpec B) (i : SyscallInput) (m : Model)
    (hk : ∀ a, ¬ k a i m .unmodeled) :
    ¬ bind (choose P) k i m .unmodeled := by
  refine bind_no_unmodeled (choose P) k i m (choose_no_unmodeled P i m) ?_
  intro a m1 evs1 h
  obtain ⟨x, -, ho⟩ := h
  simp only [Outcome.ok.injEq] at ho
  obtain ⟨-, hm, -⟩ := ho
  subst hm
  exact hk a

/-- A `seqSpec` whose continuation is a plain `pure` cannot decline. -/
theorem seqSpec_pure_no_unmodeled {A : Type} (c : SysSpec Unit) (e : A)
    (i : SyscallInput) (m : Model) (hc : ¬ c i m .unmodeled) :
    ¬ seqSpec c (pure e) i m .unmodeled :=
  seqSpec_no_unmodeled c _ i m hc (fun _ m1 _ _ => pure_no_unmodeled e i m1)

/-- `access_ok_zero` declines exactly when its range test fails. -/
theorem access_ok_zero_unmodeled_iff (buf count : word) (k : SysSpec SyscallEffect)
    (i : SyscallInput) (m : Model) :
    access_ok_zero buf count k i m .unmodeled
      ↔ (access_okb buf (count.toNat : Int) = true ∧ k i m .unmodeled) := by
  unfold access_ok_zero
  by_cases h : access_okb buf (count.toNat : Int) = true
  · rw [ite_eq_left h]
    exact ⟨fun hk => ⟨h, hk⟩, fun hk => hk.2⟩
  · rw [ite_eq_right h]
    constructor
    · intro hh
      exact absurd hh (pure_no_unmodeled _ i m)
    · rintro ⟨hh, -⟩
      exact absurd hh h


/-- The two `access_ok_zero` shapes of a socket's non-delivering
    arms, both of which the arm's own leaf cannot decline. -/
theorem access_ok_zero_false_of_unmodeled (buf count : word) (k : SysSpec SyscallEffect)
    (i : SyscallInput) (m : Model) (Hk : ¬ k i m .unmodeled)
    (Hs : access_ok_zero buf count k i m .unmodeled) : False := by
  rw [access_ok_zero_unmodeled_iff] at Hs
  exact absurd Hs.2 Hk

theorem check_read_complete_unmodeled (i : SyscallInput) (fd buf count : word)
    (m : Model) (eff : SyscallEffect)
    (Hs : read_spec fd buf count i m .unmodeled) :
    check_read i fd buf count eff m = .CheckUnmodeled := by
  unfold read_spec at Hs
  simp only [check_read]
  simp only [inputSpec, getModelSpec, bind_input_spec, bind_getModel] at Hs
  generalize hq : fd_lookup (m_fds m) fd = q at Hs ⊢
  cases q with
  | none =>
    try dsimp only at Hs ⊢
    cases Hs
  | some e =>
    cases e with
    | FdChannel ch =>
      try dsimp only at Hs ⊢
      by_cases hw : (!(w_is0 ch)) = true
      · rw [ite_eq_left hw] at Hs ⊢
        cases Hs
      · rw [ite_eq_right hw] at Hs ⊢
        by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
        · rw [ite_eq_left hak] at Hs ⊢
          cases Hs
        · rw [ite_eq_right hak] at Hs ⊢
          by_cases hc : w_is0 count = true
          · rw [ite_eq_left hc] at Hs ⊢
            cases Hs
          · rw [ite_eq_right hc] at Hs ⊢
            generalize hs : m_stdin m 0 = st at Hs ⊢
            cases st with
            | none =>
              try dsimp only at Hs ⊢
              cases Hs
            | some b0 =>
              try dsimp only at Hs ⊢
              generalize hw1 : read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) = w1
                at Hs ⊢
              cases w1 with
              | none =>
                try dsimp only at Hs ⊢
                cases Hs
              | some w1 =>
                try dsimp only at Hs ⊢
                generalize hwn : read_bytes_map i.in_wmem buf
                  (len_word (stream_take_z (m_stdin m) (rw_count_clamp count)).1) = wn
                  at Hs ⊢
                cases wn with
                | none =>
                  try dsimp only at Hs ⊢
                  try rfl
                | some wn =>
                  try dsimp only at Hs ⊢
                  refine absurd Hs (choose_bind_no_unmodeled _ _ i m ?_)
                  intro bs
                  exact deliverSeq_no_unmodeled _ _ _ i m
    | FdFile p off =>
      try dsimp only at Hs ⊢
      by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
      · rw [ite_eq_left hak] at Hs ⊢
        cases Hs
      · rw [ite_eq_right hak] at Hs ⊢
        cases hfs : Fs.fs_lookup (m_fs m) p with
        | none =>
          simp only [hfs] at Hs ⊢
          try rfl
        | some data =>
          simp only [hfs] at Hs ⊢
          try dsimp only at Hs ⊢
          generalize hbs : Fs.file_read data off (BitVec.ofInt 64 (rw_count_clamp count)) = bs
            at Hs ⊢
          generalize hw : read_bytes_map i.in_wmem buf (len_word bs) = w at Hs ⊢
          try dsimp only at Hs ⊢
          cases w with
          | none =>
            try dsimp only at Hs ⊢
            generalize hw1 : read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) = w1
              at Hs ⊢
            try dsimp only at Hs ⊢
            cases w1 with
            | none =>
              try dsimp only at Hs ⊢
              cases Hs
            | some w1 =>
              try dsimp only at Hs ⊢
              try rfl
          | some w =>
            try dsimp only at Hs ⊢
            cases bs with
            | nil =>
              try dsimp only at Hs ⊢
              exact absurd Hs
                (seqSpec_pure_no_unmodeled _ (mkEffect (len_word []) (delivered_writes buf []) [])
                  i m (modifySpec_no_unmodeled _ i m))
            | cons b bsr =>
              try dsimp only at Hs ⊢
              exact absurd Hs
                (seqSpec_pure_no_unmodeled _
                  (mkEffect (len_word (b :: bsr)) (delivered_writes buf (b :: bsr)) [])
                  i m (modifySpec_no_unmodeled _ i m))
    | FdFileW p off =>
      try dsimp only at Hs ⊢
      cases Hs
    | FdFileA p off =>
      try dsimp only at Hs ⊢
      cases Hs
    | FdFileRW p off =>
      try dsimp only at Hs ⊢
      by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
      · rw [ite_eq_left hak] at Hs ⊢
        cases Hs
      · rw [ite_eq_right hak] at Hs ⊢
        cases hfs : Fs.fs_lookup (m_fs m) p with
        | none =>
          simp only [hfs] at Hs ⊢
          try rfl
        | some data =>
          simp only [hfs] at Hs ⊢
          try dsimp only at Hs ⊢
          generalize hbs : Fs.file_read data off (BitVec.ofInt 64 (rw_count_clamp count)) = bs
            at Hs ⊢
          generalize hw : read_bytes_map i.in_wmem buf (len_word bs) = w at Hs ⊢
          try dsimp only at Hs ⊢
          cases w with
          | none =>
            try dsimp only at Hs ⊢
            generalize hw1 : read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) = w1
              at Hs ⊢
            try dsimp only at Hs ⊢
            cases w1 with
            | none =>
              try dsimp only at Hs ⊢
              cases Hs
            | some w1 =>
              try dsimp only at Hs ⊢
              try rfl
          | some w =>
            try dsimp only at Hs ⊢
            cases bs with
            | nil =>
              try dsimp only at Hs ⊢
              exact absurd Hs
                (seqSpec_pure_no_unmodeled _ (mkEffect (len_word []) (delivered_writes buf []) [])
                  i m (modifySpec_no_unmodeled _ i m))
            | cons b bsr =>
              try dsimp only at Hs ⊢
              exact absurd Hs
                (seqSpec_pure_no_unmodeled _
                  (mkEffect (len_word (b :: bsr)) (delivered_writes buf (b :: bsr)) [])
                  i m (modifySpec_no_unmodeled _ i m))
    | FdDir =>
      try dsimp only at Hs ⊢
      by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
      · rw [ite_eq_left hak] at Hs ⊢
        cases Hs
      · rw [ite_eq_right hak] at Hs ⊢
        cases Hs
    | FdSocket sk =>
      try dsimp only at Hs ⊢
      by_cases hmr : (!(modeled_rw_range buf count)) = true
      · rw [ite_eq_left hmr] at Hs ⊢
        try rfl
      · rw [ite_eq_right hmr] at Hs ⊢
        by_cases hz : w_is0 count = true
        · rw [ite_eq_left hz] at Hs ⊢
          rw [access_ok_zero_unmodeled_iff] at Hs
          simp only [check_access_ok_zero]
          rw [ite_eq_left Hs.1]
          exact absurd Hs.2 (pure_no_unmodeled _ i m)
        · rw [ite_eq_right hz] at Hs ⊢
          cases sk with
          | SkFresh =>
            try dsimp only at Hs ⊢
            rw [access_ok_zero_unmodeled_iff] at Hs
            simp only [check_access_ok_zero]
            rw [ite_eq_left Hs.1]
            exact absurd Hs.2 (pure_no_unmodeled _ i m)
          | SkBound =>
            try dsimp only at Hs ⊢
            rw [access_ok_zero_unmodeled_iff] at Hs
            simp only [check_access_ok_zero]
            rw [ite_eq_left Hs.1]
            exact absurd Hs.2 (pure_no_unmodeled _ i m)
          | SkListening =>
            try dsimp only at Hs ⊢
            rw [access_ok_zero_unmodeled_iff] at Hs
            simp only [check_access_ok_zero]
            rw [ite_eq_left Hs.1]
            exact absurd Hs.2 (pure_no_unmodeled _ i m)
          | SkConnected peer ch rx =>
            try dsimp only at Hs ⊢
            generalize hrx : rx 0 = nx at Hs ⊢
            cases nx with
            | fin =>
              try dsimp only at Hs ⊢
              rw [access_ok_zero_unmodeled_iff] at Hs
              simp only [check_access_ok_zero]
              rw [ite_eq_left Hs.1]
              exact absurd Hs.2 (pure_no_unmodeled _ i m)
            | rst =>
              unfold check_socket_pending_error
              unfold socket_pending_error at Hs
              try dsimp only at Hs ⊢
              rw [access_ok_zero_unmodeled_iff] at Hs
              simp only [check_access_ok_zero]
              rw [ite_eq_left Hs.1]
              exact absurd Hs.2
                (seqSpec_pure_no_unmodeled _ _ i m (modifySpec_no_unmodeled _ i m))
            | timedOut =>
              unfold check_socket_pending_error
              unfold socket_pending_error at Hs
              try dsimp only at Hs ⊢
              rw [access_ok_zero_unmodeled_iff] at Hs
              simp only [check_access_ok_zero]
              rw [ite_eq_left Hs.1]
              exact absurd Hs.2
                (seqSpec_pure_no_unmodeled _ _ i m (modifySpec_no_unmodeled _ i m))
            | cons b0 =>
              try dsimp only at Hs ⊢
              generalize hw1 : read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) = w1
                at Hs ⊢
              cases w1 with
              | none =>
                try dsimp only at Hs ⊢
                cases Hs
              | some w1 =>
                try dsimp only at Hs ⊢
                generalize hwn : read_bytes_map i.in_wmem buf
                  (len_word (net_take_z rx (rw_count_clamp count)).1) = wn at Hs ⊢
                cases wn with
                | none =>
                  try dsimp only at Hs ⊢
                  try rfl
                | some wn =>
                  try dsimp only at Hs ⊢
                  refine absurd Hs (choose_bind_no_unmodeled _ _ i m ?_)
                  intro bs
                  exact deliverSeq_no_unmodeled _ _ _ i m
          | SkReset _ _ =>
            try dsimp only at Hs ⊢
            rw [access_ok_zero_unmodeled_iff] at Hs
            simp only [check_access_ok_zero]
            rw [ite_eq_left Hs.1]
            exact absurd Hs.2 (pure_no_unmodeled _ i m)
    | FdPipe id w =>
      try dsimp only at Hs ⊢
      by_cases hw : w = true
      · rw [ite_eq_left hw] at Hs ⊢
        cases Hs
      · rw [ite_eq_right hw] at Hs ⊢
        by_cases hmr : (!(modeled_rw_range buf count)) = true
        · rw [ite_eq_left hmr] at Hs ⊢
          try rfl
        · rw [ite_eq_right hmr] at Hs ⊢
          by_cases hz : w_is0 count = true
          · rw [ite_eq_left hz] at Hs ⊢
            rw [access_ok_zero_unmodeled_iff] at Hs
            simp only [check_access_ok_zero]
            rw [ite_eq_left Hs.1]
            exact absurd Hs.2 (pure_no_unmodeled _ i m)
          · rw [ite_eq_right hz] at Hs ⊢
            generalize hp : pipe_lookup (m_pipes m) id = p at Hs ⊢
            cases p with
            | none =>
              try dsimp only at Hs ⊢
              try rfl
            | some qu =>
              obtain ⟨q, used⟩ := qu
              cases q with
              | nil =>
                try dsimp only at Hs ⊢
                by_cases hlv : pipe_end_live (m_fds m) id true = true
                · rw [ite_eq_left hlv] at Hs ⊢
                  try rfl
                · rw [ite_eq_right hlv] at Hs ⊢
                  rw [access_ok_zero_unmodeled_iff] at Hs
                  simp only [check_access_ok_zero]
                  rw [ite_eq_left Hs.1]
                  exact absurd Hs.2 (pure_no_unmodeled _ i m)
              | cons b bs0 =>
                try dsimp only at Hs ⊢
                generalize hw2 : read_bytes_map i.in_wmem buf
                  (len_word (pipe_take (b :: bs0) (rw_count_clamp count))) = w2 at Hs ⊢
                cases w2 with
                | none =>
                  try dsimp only at Hs ⊢
                  generalize hw1 : read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) = w1
                    at Hs ⊢
                  try dsimp only at Hs ⊢
                  cases w1 with
                  | none =>
                    try dsimp only at Hs ⊢
                    cases Hs
                  | some w1 =>
                    try dsimp only at Hs ⊢
                    try rfl
                | some w2 =>
                  try dsimp only at Hs ⊢
                  exact absurd Hs
                    (seqSpec_pure_no_unmodeled _
                      (mkEffect (len_word (pipe_take (b :: bs0) (rw_count_clamp count)))
                        (delivered_writes buf
                          (pipe_take (b :: bs0) (rw_count_clamp count))) [])
                      i m (modifySpec_no_unmodeled _ i m))
    | FdDevNull rd wr =>
      try dsimp only at Hs ⊢
      by_cases hrd : (!rd) = true
      · rw [ite_eq_left hrd] at Hs ⊢
        cases Hs
      · rw [ite_eq_right hrd] at Hs ⊢
        -- the spec spells this arm's range test NEGATED
        by_cases hok : access_okb buf (count.toNat : Int) = true
        · rw [ite_eq_right (by simp [hok])] at Hs
          cases Hs
        · rw [ite_eq_left (by simp [hok])] at Hs
          cases Hs
    | FdUrandom =>
      try dsimp only at Hs ⊢
      by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
      · rw [ite_eq_left hak] at Hs ⊢
        cases Hs
      · rw [ite_eq_right hak] at Hs ⊢
        exact check_read_urandom_complete_unmodeled i buf count m eff Hs


/-- Invert the channel delivery stage of a vectored read. -/
theorem wv_stdin_deliver_writes_inv (stdin : InputStream) (ch : word)
    (writes : List (word × List byte)) (bs : List byte) (i : SyscallInput)
    (m : Model) (eff : SyscallEffect) (m' : Model) (evs : List event)
    (H : seqSpec (set_stdin stdin)
      (seqSpec (emit (bs.map (event.ReadEv ch)))
        (pure (mkEffect (len_word bs) writes []))) i m (.ok eff m' evs)) :
    eff = mkEffect (len_word bs) writes [] ∧ m' = with_stdin stdin m ∧
      evs = bs.map (event.ReadEv ch) := by
  obtain ⟨u, m1, ev1, ev2, h1, h2, h3⟩ := H
  simp only [set_stdin, modifySpec, LinuxSem.LinuxProcessSem.modify] at h1
  cases h1
  obtain ⟨y, m2, ev3, ev4, h4, h5, h6⟩ := h2
  cases h4
  cases h5
  simp only [List.nil_append, List.append_nil] at h3 h6
  cases h6
  cases h3
  exact ⟨rfl, rfl, rfl⟩


/-- The same on a socket's descriptor table. -/
theorem wv_fds_deliver_writes_inv (fds : List (word × FdEntry)) (ch : word)
    (writes : List (word × List byte)) (bs : List byte) (i : SyscallInput)
    (m : Model) (eff : SyscallEffect) (m' : Model) (evs : List event)
    (H : seqSpec (set_fds fds)
      (seqSpec (emit (bs.map (event.ReadEv ch)))
        (pure (mkEffect (len_word bs) writes []))) i m (.ok eff m' evs)) :
    eff = mkEffect (len_word bs) writes [] ∧ m' = with_fds fds m ∧
      evs = bs.map (event.ReadEv ch) := by
  obtain ⟨u, m1, ev1, ev2, h1, h2, h3⟩ := H
  simp only [set_fds, modifySpec, LinuxSem.LinuxProcessSem.modify] at h1
  cases h1
  obtain ⟨y, m2, ev3, ev4, h4, h5, h6⟩ := h2
  cases h4
  cases h5
  simp only [List.nil_append, List.append_nil] at h3 h6
  cases h6
  cases h3
  exact ⟨rfl, rfl, rfl⟩


/-- The channel readv's delivery stage, with the vectored ledger
    (`set_stdin` + per-byte events + the arbitrary write list). -/
theorem seqSpec_set_stdin_deliver_writes (stdin : InputStream) (ch : word)
    (writes : List (word × List byte)) (bs : List byte) (i : SyscallInput)
    (m : Model) :
    seqSpec (set_stdin stdin)
      (seqSpec (emit (bs.map (event.ReadEv ch)))
        (pure (mkEffect (len_word bs) writes []))) i m
      (.ok (mkEffect (len_word bs) writes []) (with_stdin stdin m)
        (bs.map (event.ReadEv ch))) := by
  refine ⟨(), with_stdin stdin m, [], bs.map (event.ReadEv ch), rfl, ?_, rfl⟩
  refine ⟨(), with_stdin stdin m, bs.map (event.ReadEv ch), [], rfl, rfl, by simp⟩


/-- The same on a socket's descriptor table. -/
theorem seqSpec_set_fds_deliver_writes (fds : List (word × FdEntry))
    (ch : word) (writes : List (word × List byte)) (bs : List byte)
    (i : SyscallInput) (m : Model) :
    seqSpec (set_fds fds)
      (seqSpec (emit (bs.map (event.ReadEv ch)))
        (pure (mkEffect (len_word bs) writes []))) i m
      (.ok (mkEffect (len_word bs) writes []) (with_fds fds m)
        (bs.map (event.ReadEv ch))) := by
  refine ⟨(), with_fds fds m, [], bs.map (event.ReadEv ch), rfl, ?_, rfl⟩
  refine ⟨(), with_fds fds m, bs.map (event.ReadEv ch), [], rfl, rfl, by simp⟩

end LinuxSem.Checks.Sys.Fs.ReadWrite
