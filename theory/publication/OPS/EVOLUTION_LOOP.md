# Continuous Evolution Loop

This file defines the outer loop for the publication workspace.

The publication workspace is not a graveyard of split drafts.
It is the execution layer for a continuously evolving research program.

## Core principle

Every result should be able to move through this loop:

`source -> track -> paper wave -> formalization feedback -> upstream backport -> sequel or revision wave`

No track ends simply because a submission pack exists.

## Valid source types

Any new track may start from one or more of the following:

- a main-theory section or subsection
- a theorem cluster already isolated in `SOURCE_MAP.md`
- a Lean gap or formalization cluster
- a reproducible experiment or generated table family
- referee or editorial feedback on an existing paper
- a stable side branch that should become its own sequel track

## Long-lived track states

Use these as the real lifecycle, above the local `P0`--`P7` stage labels:

1. `seed`
   a source unit is identified and bounded
2. `active`
   the track is being pushed through manuscript stages
3. `waiting-human-input`
   only author metadata, funding statements, or submission-system data remain
4. `submitted`
   the manuscript has left the local pipeline
5. `revision`
   external feedback has reopened the track
6. `split`
   one child track has been spawned from the paper
7. `archived`
   the track is frozen and no longer active

## Mandatory side effects of each wave

Every accepted wave must do at least one of the following:

- improve the manuscript itself
- improve the formalization target list
- improve the upstream main-theory source
- create or sharpen a sequel / split decision

If a wave only creates diagnostics and none of the above happens, the wave
does not count as real progress.

## Required records

These records make the loop durable:

- paper-local `TRACK_BOARD.md`
- paper-local `SOURCE_MAP.md`
- paper-local `THEOREM_LIST.md`
- paper-local `LEAN_SYNC_NOTE_YYYY-MM-DD.md` once `P6` is touched
- paper-local `UPSTREAM_SYNC_NOTE_YYYY-MM-DD.md` once `P5` changes theorem
  packaging, scope, or source interpretation
- global `OPS/UPSTREAM_BOARD.md`
- global `OPS/FORMALIZATION_BOARD.md`

## Transition rules

### From source to track

Before a new track is active, record:

- source chapter or file roots
- target journal or provisional genre
- why the track is not redundant with an existing one
- what downstream track it could eventually feed

### From paper wave to upstream

After any `P5` integration that changes theorem order, scope, cuts, or
motivation:

- create/update a paper-local `UPSTREAM_SYNC_NOTE_YYYY-MM-DD.md`
- update `OPS/UPSTREAM_BOARD.md`
- state exactly what should be backported to the main theory source

### From paper wave to Lean

After any `P6` pass:

- update the paper-local `LEAN_SYNC_NOTE_YYYY-MM-DD.md`
- update `OPS/FORMALIZATION_BOARD.md`
- classify each active claim set as `verified`, `partial`, `backlog`, or
  `paper-external`

### From paper to sequel

When a stable side branch appears:

- do not bury it inside a review note
- register it in `OPS/UPSTREAM_BOARD.md`
- state whether it should become a new publication track, a future appendix,
  or a main-paper-only branch

## Human-only blockers

The following do not invalidate the technical track state:

- final author list
- affiliation and funding declarations
- cover-letter personalization
- submission-system-only fields

Mark them clearly, but do not let them freeze unrelated mathematical or
formalization work on other tracks.
