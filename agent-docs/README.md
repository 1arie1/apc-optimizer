# Agent-maintained documentation

These notes are written and maintained by the AI agents that develop this optimizer (see
[`AGENTS.md`](../AGENTS.md) and the `autoopt` skill), not by human authors. They are working
documents — not part of the audited surface, and not a substitute for it.

- [`architecture.md`](architecture.md) — how the optimizer is built: the spec, the verified-pass
  framework, `BusFacts`, and the pipeline. The map an agent reads before extending the optimizer.
- [`ideas.md`](ideas.md) — a ranked shortlist of future optimization ideas. Agents add ideas that
  don't fit the current session and remove ones that have been implemented.
- [`log.md`](log.md) — an append-only history of optimizer changes: each entry records the idea,
  whether it worked, and its effect on effectiveness. Earlier entries describe superseded designs.
- [`runtime-scaling.md`](runtime-scaling.md) — why the optimizer's wall time is superlinear in
  circuit size (~N^1.5–1.8 against Rust's ~N^1.0), with the measurements, the per-pass attribution,
  and the quadratic code sites. Read before working on runtime.

For humans, the entry points are the top-level [`README.md`](../README.md) (which defines the
auditing surface) and [`AGENTS.md`](../AGENTS.md) (the agent instructions).
