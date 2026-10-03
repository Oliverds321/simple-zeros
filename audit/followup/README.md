# audit/followup: build logs and censuses of the follow-up release

This folder holds the evidence for the release `v1.0`: the logs of the clean build of the release commit and
the axiom censuses run on it. The logs and censuses of the clean build are added here by the person who runs it; the
release notes (`RELEASE_NOTES.md`) name the commit they were taken on.

## Files

| file | what it is |
|---|---|
| `printaxioms_replay_2026-10-01.out` | output of `comparator/PrintAxioms/FollowUpReplay.lean` on 1 October 2026, checked against the build products of the kernel replay of 28 September 2026 (commit bb7223b; the `ZetaS/` of this release differs from bb7223b's only in two doc-strings of `ZetaS/ChallengeZetaS.lean`) |
| `printaxioms_shell_2026-10-01.out` | output of `comparator/PrintAxioms/FollowUpShell.lean` on 1 October 2026, checked against a build of commit 5c4c62d, whose `ZetaShell/` is the one this release started from |

Both were produced before the clean build of the release commit, as a check that the two files compile and print what
they should; the census of the release commit itself replaces them as the evidence of record. Each ends with the
summary line of the project's job runner (`exit`, elapsed time, peak memory, file); the file path in that line is given
relative to the repository root.

## What a reader runs

The commands and their expected output are in the top-level `README.md`, section "How to verify". Every
`#print axioms` line must read `depends on axioms: [propext, Classical.choice, Quot.sound]`.
