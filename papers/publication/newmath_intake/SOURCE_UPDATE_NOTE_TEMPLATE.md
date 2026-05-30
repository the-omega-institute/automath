# Source Update Note Template

Use this template when a newmath-derived seed or promoted paper needs to move
from one `D:/omega/newmath` source commit to another.  Do not silently edit a
source map to point at a newer branch tip.

## Update Identity

- automath path:
- source repo: `D:/omega/newmath`
- previous source ref:
- previous source commit:
- new source ref:
- new source commit:
- update date:
- reviewer:

## Reason For Update

State why the source update is needed.  Examples:

- newly added packaging theorem;
- regenerated Rule110 artifact suite;
- corrected source path or declaration name;
- venue-specific narrowing of the evidence set.

## Changed Source Paths

| Path | Previous role | New role | Required manuscript change |
|---|---|---|---|
|  |  |  |  |

## Changed Claims

| Claim | Status after update | Evidence |
|---|---|---|
|  | unchanged / strengthened / weakened / removed |  |

## Required Rechecks

- [ ] source paths exist at the new commit;
- [ ] theorem or artifact inventory updated;
- [ ] risk register updated if any claim weakened;
- [ ] venue ladder updated if route changed;
- [ ] intake guard passes if this is still a seed;
- [ ] active pipeline gate rerun if this is already promoted.

## Decision

Record the final update decision:

- adopt new source commit;
- keep previous source commit;
- park until source-side work is complete.
