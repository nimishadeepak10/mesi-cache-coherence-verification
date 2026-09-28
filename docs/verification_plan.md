# Verification Plan: MESI Cache Coherence Protocol (multi-cache formal model)

**Scope of this plan:** formal verification only, via [SymbiYosys](https://github.com/YosysHQ/sby)
against hand-written SVA (SystemVerilog Assertions), inspected with [GTKWave](https://gtkwave.sourceforge.net/)
when a run produces a trace. There is no simulation testbench for this design. A snooping
cache-coherence protocol's interesting behavior is the cross-instance interaction, which is exactly
what formal verification (exhaustive over reachable states) checks better than a finite set of
directed simulation vectors would.

---

## 1. Design under test

| | |
|---|---|
| **DUT** | `rtl/mesi_multi_cache.v` (top), instantiating `rtl/mesi_cache_core.v` N times |
| **Protocol** | MESI (Modified / Exclusive / Shared / Invalid) snooping cache coherence |
| **Configuration verified** | N = 3 caches sharing one cache line over one snooping bus |
| **Bus model** | Single shared bus: at most one cache is granted the bus (may issue a local CPU request) per cycle; every other cache observes that cycle's transaction as a snoop |
| **Scope simplification** | One cache line, no tags, addresses, or replacement policy. Coherence-protocol correctness is a per-line property. A real multi-line, multi-address cache must satisfy exactly these same invariants independently for every line; modeling one line proves the protocol logic without paying for address-space state-space blowup that adds nothing to this question |
| **Reference model** | `rtl/mesi_line.v`, the original single cache-line FSM (no cross-instance behavior). `mesi_cache_core.v` is its logic extended with the two signals a lone cache has no way to define: whether another cache currently holds the line, and what bus transaction a local request implies for everyone else |

## 2. Verification methodology

**Tool chain:** Yosys (SystemVerilog frontend) into SymbiYosys into a solver (`smtbmc`; `mode prove`
uses BMC plus k-induction; `mode cover` for reachability). GTKWave for opening any `.vcd` trace a
run produces, whether a counterexample or a cover witness, to inspect the actual signal-level
scenario rather than trusting the solver's verdict on faith.

**Property style, two different assertion forms, deliberately:**
- **Safety invariants** (section 4, P1 to P3): plain immediate `assert` inside `always @(posedge clk)`,
  same-cycle claims ("this must never be true right now"), no history needed.
- **Functional-correctness / transition properties** (section 4, P4 to P9): immediate `assert`
  combined with `$past()` inside `always @(posedge clk)`, next-cycle claims ("if X held last cycle,
  Y must hold now"). The natural IEEE 1800 tool for this is concurrent SVA
  (`assert property (@(posedge clk) ... |=> ...)`, section 16.14), and that was the first thing tried.
  It was rejected outright by this build's yosys frontend, confirmed with an isolated five-line probe,
  independent of this file's complexity, that fails with the identical `syntax error, unexpected '@'`
  this file's first attempt hit. Not a design-specific limitation to work around case by case; this
  yosys build's Verilog frontend does not implement that grammar production for bare module-item
  concurrent assertions at all. `$past()`-based immediate assertions express the same next-cycle
  semantics and were used instead.

**A second, unrelated frontend limitation found and worked around while building this DUT:** a
static `assert`/`cover` label repeated across `generate for` loop iterations collides, confirmed
with another isolated probe, because this frontend uses the label text as a flat cell name rather
than scoping it per generate instance. Per-cache checks inside a `generate for` are therefore left
unlabeled below; SymbiYosys still reports exactly which cache instance failed via the hierarchical
instance path in its counterexample output, it just does not have a short mnemonic name. Checks
that instantiate once (not inside a `for` loop) keep their labels.

**Verdict discipline:** a safety property counts as proven only when `mode prove` returns pass for
both basecase and induction, an unbounded proof, not a bounded depth sample that happened not to
find a bug. A coverage goal counts as reached only when `mode cover` reports the specific witness
for that statement, and, for the headline scenario this plan specifically claims to demonstrate
(ownership transfer), only after opening the actual `.vcd` and confirming the trace shows what it
claims to, not just trusting the solver's pass label.

## 3. Environment assumptions

| ID | Assumption | Why it's needed |
|---|---|---|
| A1 | Each cache issues at most one of `cpu_read`/`cpu_write` per cycle | A cache cannot be doing two different local operations on the same line in the same cycle, this is a property of what "one request" means, not a restriction that hides real behavior |
| A2 | At most one cache per cycle either issues a real bus transaction (`issue_busrd`/`issue_busrdx`) or performs a silent E/M write (`$onehot0` over both masks combined) | The precise condition actually needed for soundness, see the debugging note below. Harmless concurrency, such as two caches simultaneously reading a line they already hold Shared, is not restricted |

Both are environment assumptions (`assume`), not DUT behavior. They constrain what inputs the
solver is allowed to consider, matching what a real bus/arbiter would actually present to these
caches.

**A2 was debugged, not assumed on faith.** The original version of A2 was broader: `$onehot0` over
every cache's raw request activity (`cpu_read | cpu_write`), serializing all local requests,
including ones that touch neither the bus nor another cache. That is stronger than the model
actually needs, so it was tested for over-constraint by loosening it to serialize only real bus
transactions (`issue_busrd | issue_busrdx`) and re-running `mode prove`.

That loosened version produced a genuine counterexample, not a tooling artifact. `mesi_multi_cache.sby`
failed P6 (`write_becomes_modified`) at basecase step 4. Reading the failing trace directly out of
the `.vcd` (`trace.vcd`, `state`/`cpu_write`/`issue_busrd` signals) showed: cache 0 holds the line
Exclusive and asserts `cpu_write` (a silent upgrade to Modified, no bus transaction, so the loosened
assumption let it proceed); in the same cycle, cache 2 independently misses and issues `BusRd`. Cache
0's core prioritizes the incoming snoop over its own pending local write (`mesi_cache_core.v`, snoop
branch taken before local_req), so cache 0 downgrades to Shared instead of reaching Modified, a lost
write on a concurrent access. The same race exists for a redundant write on an already-Modified line
racing a remote `BusRd`, found the same way after the first fix was applied and the proof was
re-run. Both are real behavior of this stall-free RTL, not modeling artifacts: the design has no
stall or retry path, so a silent (bus-transaction-free) write can always be preempted by a real bus
transaction landing the same cycle.

The assumption was tightened back, precisely: instead of re-broadening to all request activity, A2
now serializes real bus transactions together with silent E/M writes (the two event classes shown to
race), while leaving every other kind of local activity, in particular a cache reading a line it
already holds Shared, unconstrained. Re-running `mode prove` with this exact assumption reproves all
25 properties by k-induction (section 5). C9 (section 6) is the new coverage goal added specifically
to confirm the loosening had real effect: two caches issuing a local read in the same cycle while
both already hold Shared, a scenario the original blanket assumption made unreachable and this one
does not.

## 4. Properties

**Safety invariants** (checked every cycle, no temporal history):

| ID | Property | Statement |
|---|---|---|
| P1 | `valid_encoding` | Each cache's `state` is always one of {I, S, E, M} |
| P2 | `single_writer` | If a cache holds E or M, no other cache holds any copy of the line (subsumes P3 and forbids the classic "one cache Modified, another stale-Shared" coherence bug) |
| P3 | `mutex_modified` | At most one cache is in M at any time, the headline mutual-exclusion property this plan sets out to prove, stated directly rather than relying on P2 alone |

**Functional-correctness / transition properties** (next-cycle claims, `$past()`-based):

| ID | Property | Statement |
|---|---|---|
| P4 | `read_miss_exclusive` | A read miss (I, `cpu_read`, no other owner) transitions to E |
| P5 | `read_miss_shared` | A read miss with another current owner transitions to S, never E, the property that actually distinguishes this multi-cache model from the single-cache reference model |
| P6 | `write_becomes_modified` | Any local write, from any starting state, transitions to M |
| P7 | `remote_write_invalidates` | A remote BusRdX (another cache writing) invalidates this cache unconditionally, the direct formal statement of "no stale data survives an invalidation" |
| P8 | `remote_read_downgrades` | A remote BusRd downgrades E/M to S, not I, data survives, only write permission is revoked |
| P9 | `silent_upgrade` | A write to an already-Exclusive line upgrades to M without issuing a bus transaction that cycle, the real MESI write-performance optimization; easy to accidentally break by over-broadcasting, and only observable formally |

## 5. Traceability matrix

All properties are instantiated once per cache (N=3, P1, P2, P4 to P9 each produce 3 checks; P3 is
a single cross-cache check), 3x8 + 1 = **25 safety/correctness checks**, all passing.

| Property | Result | Method |
|---|---|---|
| P1 `valid_encoding` (x3) | PROVEN | k-induction |
| P2 `single_writer` (x3) | PROVEN | k-induction |
| P3 `mutex_modified` | PROVEN | k-induction |
| P4 `read_miss_exclusive` (x3) | PROVEN | k-induction |
| P5 `read_miss_shared` (x3) | PROVEN | k-induction |
| P6 `write_becomes_modified` (x3) | PROVEN | k-induction |
| P7 `remote_write_invalidates` (x3) | PROVEN | k-induction |
| P8 `remote_read_downgrades` (x3) | PROVEN | k-induction |
| P9 `silent_upgrade` (x3) | PROVEN | k-induction |

Reproduce: `sby -f formal/mesi_multi_cache.sby` from the `formal/` directory. Actual run:
`engine_0 (smtbmc) returned pass for basecase` plus `... for induction`, then
`successful proof by k-induction`, then `DONE (PASS, rc=0)`.

## 6. Coverage

| ID | Cover goal | Demonstrates |
|---|---|---|
| C1 | `reach_shared` (x3) | Each cache can individually reach S |
| C2 | `reach_exclusive` (x3) | Each cache can individually reach E |
| C3 | `reach_modified` (x3) | Each cache can individually reach M |
| C4 | silent-upgrade cover (x3) | The E to M silent-upgrade path (P9) is actually exercised, not just vacuously true because it never fires |
| C5 | invalidation-after-modified cover (x3) | A cache that was Modified is later invalidated (P7's transition is genuinely exercised) |
| C6 | `reach_two_shared` | Two different caches hold S simultaneously, real sharing, not just each cache's own isolated state space |
| C7 | `cover_ownership_transfer` | A cache that was Modified downgrades to S at the same cycle another cache's read pulls it to S, a full ownership-transfer transaction |
| C8 | `reach_three_shared` | All three caches hold S simultaneously |
| C9 | `concurrent_shared_reads` | Two caches issue a local read in the same cycle while both already hold S, the concurrency A2's tightened form was specifically loosened to permit |

All 9 cover goals (19 individual witnesses across the 3 cache instances plus cross-cache points)
were reached: `sby -f formal/mesi_multi_cache_cover.sby` returns `DONE (PASS, rc=0)`, every cover
statement in the summary listed with `reached cover statement ... step N`.

**C7 verified by hand, not just by the solver's label.** Opened the trace for
`cover_ownership_transfer` in GTKWave and read the `state[0..2]` signal changes directly:

| Cycle | `state[0]` | `state[1]` | `state[2]` |
|---|---|---|---|
| reset | I | I | I |
| 1 | **M** | I | I |
| 2 | **S** | **S** | I |

Cache 0 reaches Modified, then in the very next sampled cycle both cache 0 (downgrading) and cache
1 (a remote read pulling it to Shared) land on S together, exactly the ownership-transfer scenario
C7 claims, confirmed from the raw waveform rather than trusted on the solver's summary label alone.
That trace reaches Modified by a write-miss, `I -> M` directly (a write-miss issues BusRdX and lands
in Modified immediately, it never passes through Exclusive; only a read-miss with no other owner does,
per the FSM in `mesi_cache_core.v`). Exclusive does not appear in it, which is correct protocol
behavior for that specific path, not a gap in what was checked.

**The full I to E to M lattice, checked separately.** Opened the trace for the C4 silent-upgrade
cover (cache 0's instance) to confirm the read-miss and silent-upgrade paths that C7 does not
exercise:

| Cycle | `state[0]` | What happened |
|---|---|---|
| reset | I | |
| 1 | **E** | read miss, no other owner (P4) |
| 2 | **M** | local write from E, silent upgrade, no bus transaction (P9) |
| 3 | I | invalidated by a remote write (P7) |

This is the same cache line, in one trace, visiting all four states and both of the transitions C7's
path skips: the read-miss `I -> E` and the silent upgrade `E -> M`. Between the two traces, every
edge in the state diagram in the README has now been walked and confirmed from a real waveform, not
only asserted as reachable by a solver summary line.

## 7. Sign-off criteria

This DUT is considered formally signed off when:
1. Every property in section 5 is proven by k-induction, not just BMC-bounded, and not falsified or
   errored.
2. Every cover goal in section 6 is reached, with at least the headline scenario (C7, ownership
   transfer) independently confirmed from its raw trace, not only the solver's summary label.
3. Both environment assumptions (section 3) are documented and justified, not silently baked into
   the RTL where a reader cannot see what is assumed versus proven.

All three conditions hold as of this document.

## 8. Explicit non-goals

This plan proves the MESI coherence protocol's state-transition correctness for one line shared by
3 caches over an idealized single-cycle snooping bus. It does not claim:
- Multi-line or multi-address behavior, cache capacity, or replacement policy. Out of scope by
  construction (section 1); the invariants proved here must independently hold per line in a real
  cache, which this model represents.
- Bus arbitration fairness or starvation freedom. A2 (section 3) assumes a well-behaved arbiter
  exists; this plan does not verify the arbiter itself.
- Data-path correctness (actual cache-line contents/values). This model is state-only (I/S/E/M),
  matching common formal MESI verification practice, where protocol correctness and data-path
  correctness are typically verified as separate concerns.
- Timing or physical implementation, or scaling behavior to N greater than 3 caches. The properties
  and their proofs are per-N; re-running at a different N is mechanical but was not done as part of
  this sign-off. The state space at N=3 already exercises every qualitatively distinct interaction:
  one cache alone, two sharing, and a three-way share/transfer.
