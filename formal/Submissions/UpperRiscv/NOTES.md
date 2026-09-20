# upper-riscv: 696 cycles

## Idea

The scored cycle count is

```
cycles = 71 (index phase) + Σ_chains (9 + 2·nibble) + 23 (root + decision)
       = 94 + 9·C + 2·N + rootCompressions,   C = 32 chains, N = Σ nibbles.
```

`N` is the `target` of `Valid.lean`: an index is accepted iff its 32 nibbles sum to `target`, and
verification hashes `nibble k` times in chain `k`, so **every unit of `target` costs exactly two
cycles**. Lowering `target` is therefore the cheapest available saving, and it is bounded only by
signing availability: the signer draws nonces until the index is accepted, and

```
failure = (1 - comp(32, target) / 2^128) ^ (2^20)  ≤  2^-128.
```

The previous submission used `target = 160`. That value is not forced by the availability
*requirement* — it is forced by the availability *proof*. `Availability.lean` bounds repeated
failure with the rational Bernoulli inequality

```
(1 - p)^k ≤ 1 / (1 + k·p)        (`bernoulli_reciprocal`)
```

applied once to a block of `8192` trials, giving `miss^8192 ≤ 1/2` and then `miss^(2^20) ≤ 2^-128`
from 128 such blocks. Used this way the bound needs `2^20·p ≥ 128`, i.e. `p ≥ 2^-13`, i.e.
`comp(32, target) ≥ 2^115`; the smallest such target is exactly 160. But the truth is
`(1-p)^{1/p} ≤ e^{-1}`, not `1/2`, so the one-shot reciprocal bound throws away a factor of
`ln 2 ≈ 1.4427` in the exponent.

The fix is to keep the compounding instead of recovering `e` analytically: apply the *same*
rational lemma to a short run of 128 trials and then raise to the 64th power.

```
miss^8192 = (miss^128)^64 ≤ (1/(1 + 128·p))^64 = (8388608/8481920)^64 ≤ 1/2,
```

the last step because `(8481920/8388608)^64 ≈ 2.0298 > 2` — a 260-digit `norm_num` check. This
needs only `p ≥ 729/2^23`, i.e. `comp(32, target) ≥ 729·2^105 ≈ 2^114.53`.

## Result

**`target = 157`, claim `702 → 696`.** `comp 32 157 = 30465700825049557482282408820464096`
(kernel-checked through the existing `compTable` dynamic program), which is `≈ 2^114.55` and clears
the `729·2^105` threshold with about 3% to spare. 157 is the exact minimum: `comp 32 156 ≈ 2^114.37`
gives failure `≈ 2^-119`, above the `2^-128` allowance. True failure at 157 is about `2^-135`.

Nothing structural changed: same graph, same 32 chains of length 15, same 1337-instruction image,
same signature format (4224 bits), same security proof. The diff is `target`, its kernel-computed
count, the two availability lemmas, the machine's sum-check immediate (`XORI x27, x27, 1280` →
`1256`, since the lane sum carries `8·Σ`), and the cost bookkeeping (`608 → 602` chain cycles,
`172 → 169` and `173 → 170` compressions, `cycleBound 702 → 696`).

Reducing `target` only *helps* security: `RowHyp` needs `2 ≤ numValid` and `2·numValid ≤ 2^128`,
both monotone the right way, so `Potentials.lean` needed one literal updated and no new argument.

Official verifier: `python3 .contract/verifier/verify.py upper-riscv --source .` →
`verified: track=upper-riscv claim=696` in 248 s.

## What did not work, and what the remaining fat is

Measured decomposition of the 696 cycles: **382 instruction cycles vs 314 hash cycles** (157 chain
hashes + 1 index + 12 root). The instruction overhead dominates, so the scheme is far from the
compression-optimal shape; these are the levers I costed out and did not take:

- **Fewer or longer chains.** Minimising `94 + 9·C + 2·N` over `C` with 4-bit nibbles and
  `comp(C,16,N) ≥ 729·2^105` gives `C = 32` as the optimum; `C = 31` needs `N = 176` (725 cycles)
  and `C ≤ 30` cannot reach the availability threshold at all with 4-bit nibbles (the whole
  `[0,15]^30` space is `2^120`, and its largest sum-slice is only `≈ 2^114.0`). The index carries
  `C·log2(w) ≤ 128` bits, so wider nibbles buy fewer chains but longer ones. `C = 32, N = 157` is
  the optimum of this family — the 6 cycles above are all that parameter tuning yields.
- **The per-chain prologue (9 instructions × 32 = 288 cycles).** The clear target. Instruction 2,
  `ADDI x10, x12, -8`, exists only to hand the HASH its input address, because the header value
  stored by instruction 7 (`SD x12, x12, -8`) is the *slot* address `slotAddr k`, not the header
  address. Re-tweaking the scheme to `slotAddr k - 8` and rebasing the block on `x10` would remove
  it: `SD x10, x10, 0` stores the header, `SD x10, x26, 8/16` the value, `SH x10, tag, 6` the level
  tag. `hdrNat_injective` only needs injectivity, so the security proof survives, but every
  address offset in `ChainPrologue/ChainBlock/MachineMemory/Layout/Rows` shifts. **Worth 32 cycles
  (→ 664).** I did not attempt it here to avoid risking the verified 696.
- **The root hash (12 compressions).** The root input is 6080 bits = 32 values × 128 bits + 31
  interleaved 64-bit headers; 1984 of those bits are headers. Hashing only the values would be
  `⌈4096/512⌉ = 8` compressions, saving 4 cycles, but gathering them contiguously costs 32 copies
  (128 instructions). A narrower header would help both this and nothing else: a 32-bit header
  gives `⌈5088/512⌉ = 10`, saving 2 — but the header must hold a ~21-bit address and a 16-bit tag.
  Not worth it at the current header format.
- **`levelSetup` (8 cycles).** Already near-minimal: 7 of the 15 level tags are chosen to be values
  already sitting in registers after the index phase (`1, 192, 64, 120, 4224, jumpBase0,
  jumpBase1`) and level 14's tag is `0` (`x0`). The other 7 need one `ADDI` each and the tags must
  stay pairwise distinct for `levVal_injective`.
- **`lanes` (39 cycles).** Eight lane words × ~5 instructions, extracting 32 nibbles four at a time
  into 16-bit lanes and accumulating the sum in one `MUL`. I found no cheaper SWAR encoding.
- **Dropping the per-step level tag** would remove the `SH` from every chain step and save 157
  cycles outright, but it changes the hashed inputs and so invalidates the whole security
  development (`Values/Resample/StageB/RowPotential`). Not a parameter change.

## Next

1. The prologue rebase onto `x10` with header tweak `slotAddr k - 8`: 32 cycles, no new
   mathematics, purely refinement-proof surgery. This is the next thing I would do.
2. Then re-run the `(C, w, N)` optimisation for 5-bit nibbles (`C ≤ 25`) once the per-chain
   overhead drops to 8, since the optimum shifts toward fewer, longer chains as `9·C` shrinks.
3. Anyone touching availability should note that the two-stage reciprocal trick above is generic:
   it recovers the `ln 2` factor in any `(1-p)^n` bound without leaving ℚ, and it is what makes
   the last few units of `target` reachable.
