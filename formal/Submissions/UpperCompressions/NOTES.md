# Candidate 92: weighted minimum selection over disclosure cuts

This construction has a Lean-checked verifier bound of 92 hash compressions on
every raw input and every oracle-answer path, together with the exact contract's
raw-signature admissibility and strong-security theorems. The existing record
is 100; official verification and publication of 92 are pending. An isolated
mathematical check does not replace the hosted verdict or establish a new record.

The construction combines a compact disclosure forest with an uneven
distribution over its admissible cuts. Signing searches for a low-tier cut;
verification recomputes only the path from that cut to the public key.

## Where the eight compressions come from

The graph has 54 tagged chains of length 18, grouped into 18 ternary hashes and
one root. Each disclosed value has 129 bits. A signature reveals six group
values and one value on each of the other 36 chains, for 42 values total.
The remaining chain lengths sum to 74. Verification therefore costs

```
74 chain compressions + 12 group compressions + 5 root compressions
  + 1 message/nonce index compression = 92.
```

Key generation costs `54*18 + 18 + 5 = 995` compressions. The wire format uses
an 86-bit nonce and `42*129` disclosure bits, exactly the 5504-bit limit. The
cost theorem quantifies over arbitrary raw signatures, including rejecting
inputs. All pure computation follows the compression track's cost model; this
is not a cycle-count claim.

## Weighted classes and the exact sampler

The cut family is large enough for 770731564938763476110450815401984 distinct
classes. The decoder places them in 72 tiers. Tier `j` has `19*2^(104-j)` classes
for `j<71`, with `91*2^33` classes in the last tier. Each class in tier `j`
receives `2^(j+1)` accepted aliases in the low 129 bits of the hash output.
The total accepted mass is exactly `45/524288`.

Signing makes all `L=2^20` independent 86-bit nonce draws, with replacement,
and queries the same memoized random oracle on each message/nonce pair. It
returns the first occurrence in the lowest accepted tier, or fails if none is
accepted. Repeated nonces keep their cached answers. The availability proof
handles those repetitions and gives failure at most `2^-129`, inside the
required `2^-128` limit.

The unequal alias multiplicities let the finite cut family support a spread of
class probabilities. Searching all trials for the lowest tier changes the
chosen-class distribution. This is the statistical part of the improvement:
the proof accounts for that selection rule exactly, rather than treating the
winner as an ordinary accepted sample.

## The proof mechanism

Fix the entire finite nonce table for one message. Let `A` be the fraction of
entries with no accepted tier below `j`, and `B` the fraction with no accepted
tier at most `j`. For a particular nonce in tier `j`, its probability of being
selected is

```
K_L(A,B)/N,  where N = 2^86
K_L(A,B) = sum_{t=0}^{L-1} B^t A^(L-1-t).
```

This polynomial includes equal-tier ties and duplicate draws. Its monotonicity
provides the posterior bound when a previously unexposed public coordinate is
resampled. A finite eager-table coupling carries that argument back to the
actual lazy random oracle. The rest of the oracle remains the same shared
cache, including graph queries and the signer's private nonwinning queries.
Public exposure is tracked separately from implementation-cache membership.

The final analysis divides a successful forgery into graph authentication,
replay through the public cache before signing, and a newly exposed index
input. All three charges use the same actual execution budget. Distinct public
index queries, other paid queries, and the post-sign remaining budget are
accounted for together.

For small budgets, exact stopped first and second moments control the replay
term. For large budgets, a clipped hazard process and an exponential bound
control every message row at once. Empirical good events stay inside joint
expectations; the proof does not condition the posterior argument on them.
A separate completion tower averages the conditional bad-table error after
the adversary's adaptive first stage. The small-budget branch is checked at
`(243337/245000)*κ*B`, and the large-budget branch at `0.991*κ*B`, both strictly
below `κ*B`, with `κ=2^-127`.

## What required care

An early-exit signing argument does not apply here: the all-trial signer keeps
private accepted nonwinners in the cache. Charging only implementation-cache
misses would miss later public queries to those inputs. The proof instead
retains the full private cache and charges first public exposures.

A fixed observed transcript can have an atypical completion distribution.
The small bad-table probability is proved after averaging over the actual
adaptive execution, not as a uniform pointwise promise for every transcript.
Likewise, the signing continuation budget is used only for supported outputs;
an arbitrary fixed cache need not support every syntactically possible class.

## Export and validation status

`WideHonest.admissible`, `WideWire.cost`, and `WideSecure.raw_secure` are checked
on the exact raw scheme, with only `propext`, `Classical.choice`, and `Quot.sound`.
`WideBudgetEndpoints.raw_secure_of_typed` supplies the canonical encoding
transfer for strong security, including same-message alternate signatures.
`Solution.lean` exports these exact declarations under the contract's names.

The full staged root must still pass the official import policy, file limit,
axiom audit, statement comparison, and kernel replay. The mathematical result
is checked; the official submission result and any new record remain pending.

Further improvements should search the weighted tier schedule and the
disclosure-family geometry together, then reuse the exact first-minimum kernel
and the common-budget proof. A promising numerical schedule still needs its
finite class embedding, all-input resource bound, and actual-game security
connection checked before it can support another claim.
