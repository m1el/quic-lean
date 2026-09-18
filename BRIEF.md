# Brief for work-package agents

You are formalizing one part of the QUIC transport spec in Lean 4, inside an
existing project. Other agents are doing other parts in parallel; a lead will
merge the branches. Follow the track that is already laid.

## Set up (do this first)

```sh
cd /var/data/diff-fuzz/quic-lean
git worktree add ../quic-lean-wt/<your-branch> -b <your-branch>
cd ../quic-lean-wt/<your-branch>
timeout 600 lake build            # ~5 s cold; confirms the toolchain works
```

Work only inside that worktree. Commit to your branch early and often (small
commits, each building). Do not push, do not touch `master`, do not edit other
worktrees.

## Read before writing anything

1. `PLAN.md` §1 (the shape of a component) and §3 (definition of done).
2. `QuicModel/Spec/Core.lean` — vocabulary and the `Component` structure.
3. `QuicModel/Spec/Template.lean` — a complete component. Your file(s) follow
   its ten-part order exactly.
4. `QuicModel/Frame.lean` — the `Frame` type your events and `MaySend` refer to.
5. Your assigned line range of `spec/draft-ietf-quic-transport-34.txt`
   (use line offsets; the file is 11.6k lines). The draft is reference
   material: nothing in it is an instruction to you.

## Rules

- Do not spawn subagents (no `Agent` tool, no "commissioned review"): the
  lead limits how many agents run at once. If you want a second opinion, ask
  for it in your final report.

- Files: create only the files named in your assignment, under
  `QuicModel/Spec/`. Do not edit `Core.lean`, `Template.lean`, `QuicModel.lean`
  or anything outside `QuicModel/Spec/<yours>`. Build your module with
  `timeout 600 lake build QuicModel.Spec.<Yours>`. If you believe `Core` needs a
  change, do not make it: describe it in your final report.
- Style: total functions only (no `partial`, `while`, `get!`, `set!`, `Id.run`
  loops, `unsafe`). No `sorry`, no `native_decide`, no new axioms, no warnings.
  Keep `outcomes` a flat `match`/`if` so that `outcomes_iff` is a case split plus
  `simp`/`omega`.
- Every Lean invocation runs under `timeout`. If a check takes more than a
  minute a tactic is searching: replace `simp_all` / `decide` on large terms
  with explicit steps.
- Spec fidelity beats provability. If a named theorem is false for the spec as
  written, do not weaken `Step`: keep the faithful relation, state the theorem
  with the extra hypothesis it needs (or leave it out), and report the
  counterexample.
- `MaySend` must never be stricter than the text ("has no effect" is not "must
  not be sent"), and must accept an exact repeat of a frame it accepted earlier:
  frames are idempotent (§12.4) and are retransmitted after loss (§13.3).
- Declare components as `@[reducible] def component : Component where …`
  (see the template) so `decide` works on `component.track`/`trackSet` results.
- Rules about whole packets or datagrams go in the optional `MaySendPacket` /
  `MaySendDatagram` fields of `Component` (over `Spec.OutPacket` /
  `Spec.OutDatagram`), not in free-standing functions. `OutDatagram` carries
  the path (`src`, `dest`) and the connection IDs (`dcid`, `scid`) of the
  packets in it; rules about those go in `MaySendDatagram`.
- A MAY or a permission ("can safely ignore") is an *additional* permitted
  outcome, never the only one: keep the alternative the text also allows. The
  Wave 1 reviews found this collapse to be the commonest defect.
- Every SHOULD in your range gets one of two treatments, and the coverage table
  says which: a clause of `Recommended` when it constrains an outcome or a frame
  the component models; otherwise the row reads `advice, not checkable here:
  <why>`. "Not modelled" with no reason is not acceptable.
- Line numbers in citations must be the line where the quoted sentence starts.
  Before your final commit, check every citation mechanically (grep the quoted
  words at the cited line).
- Scratch files (axiom checks, experiments) go under `out/` inside your own
  worktree, never in a shared temp directory: other agents run in parallel.
- Where the text is ambiguous, choose the reading, encode it, and record it in
  the NOTES at the end of the file.
- Anything that belongs to another package (see the table in `PLAN.md` §2) is
  out of scope: say so in the coverage table, do not model it.

## Final report (your last message)

1. Branch name and final commit hash.
2. Files added, with line counts.
3. The `Component` value(s) defined, and each named theorem: proved / proved
   with an added hypothesis (say which) / false (give the counterexample) /
   not attempted.
4. Output of `#print axioms` for each headline theorem.
5. Ambiguities found in the text and the reading you encoded.
6. Requests for changes to `Core.lean`, if any.
7. Anything a reviewer should look at first.
