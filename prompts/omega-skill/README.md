# omega-skill

Claude Code plugin packaging the **Omega Reasoning Protocol** as a single skill.

The protocol enforces three principles on the model's reasoning:

- **FORCING** — separate structurally inevitable conclusions from chosen ones.
- **MINIMIZE** — strip every assumption that has no failure mode.
- **AUDIT** — every non-trivial conclusion must be traceable to its premises.

It also knows how to look up structural correspondences in the Omega derivation
chain at `github.com/the-omega-institute/automath`.

## Install

```text
/plugin marketplace add the-omega-institute/automath
/plugin install omega-skill@omega
```

To enable automatic updates, open `/plugin > Marketplaces` and toggle
auto-update for the `omega` marketplace, or set
`FORCE_AUTOUPDATE_PLUGINS=1` in the environment.

## Use

Once installed the skill auto-activates on triggers such as `/omega`,
"think deeply", "first principles", or any task that benefits from
distinguishing forced from chosen.

## Versioning

Versions follow calver `YYYY.MM.DD.N`, where `N` is the number of commits
on that UTC day touching `prompts/omega-skill/`. The version is bumped
automatically by `.github/workflows/sync-plugin-version.yml` whenever the
plugin tree changes.
