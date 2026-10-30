# Working conventions (for humans and agents)

Read [README.md](README.md) for the layout.

## Ground rules

1. **One module per file**, at the path that mirrors its namespace.  Keep the
   namespace `LinuxSem.<path>` (e.g.
   `LinuxSem.Riscv.Decode`,
   `LinuxSem.LinuxProcessSem.Fs`).
2. **The comments are part of the artifact.** They carry the design rationale,
   the kernel citations, and the measurements behind non-obvious choices. Do not
   strip them, and do not add commentary that depends on another codebase.
3. **No `sorry`, `admit`, `axiom`, or `unsafe` in the library.** If a
   proof is out of reach, stop and report it rather than leave a hole.
4. **Keep the file compiling.** Add definitions first (they typecheck
   quickly), then lemmas.  Never leave the tree broken at the end of a
   work session.
5. **Only touch your assigned file(s).** Do not edit `lakefile.toml`,
   `lean-toolchain`, the root module, `Prelude.lean`, or another agent's
   file.  The integrator wires files into the root module and runs the
   full build.
6. **Verify with** `lake env lean <path/to/YourFile.lean>` (typecheck only,
   no build-directory writes).  Do not run `lake build` concurrently with
   other work.

## Conventions

| type | Lean |
| --- | --- |
| `word`, `reg`, `byte` | `BitVec 64`, `BitVec 5`, `BitVec 8` (from `Riscv.Prelude`) |
| integers | `Int` |
| naturals | `Nat` |
| records | `structure` (with `deriving DecidableEq, Repr` where useful) |
| decidable propositions | `decide P` |

Module-qualified names: open the namespace
(`namespace LinuxSem.LinuxProcessSem.Fs`) and the short name
`Fs.path` resolves.

## Definition of done for a module

- the module's definitions and lemmas are complete, or what is missing is
  reported;
- `lake env lean <your file>` is silent;
- any decidable definition has at least a couple of `by decide` sanity checks;
- a short report: what is complete, what is missing and why.

## Word hygiene in comments

`scripts/check.sh` greps the whole tree for `\b(sorry|axiom)\b`, so do **not**
write those two words in prose either — say "no proof hole", "no extra
postulate", "no `admit`" instead.  Honest notes about the no-hole discipline
must not name the tokens, or CI fails.
