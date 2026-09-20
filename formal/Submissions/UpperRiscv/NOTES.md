# upper-riscv: 694 cycles

## Idea

The scored cycle count is

```
cycles = 71 (index phase) + Σ_chains (9 + 2·nibble) + 23 (root + decision)   [at 702/696]
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

## Second step: 696 → 694, two instructions out of the root and decision

- **Root length in one instruction.** The root hash needs `x11 = 6080`, previously `LUI x11, 1;
  ADDI x11, x11, 1984`. On the accepting path `x13` still holds the checked signature length 4224
  (nothing writes it after the loader, and it doubles as level tag 4), and `6080 − 4224 = 1856`
  fits a 12-bit immediate, so `ADDI x11, x13, 1856` does it. The chain-phase context `Ctx` only
  carried the low 16 bits of the tag registers; it now also carries `x13 = 4224` (`Ctx.sigLen`),
  which `Ctx.frame` preserves for free since `x13` is already a `CtxReg`. No other register is
  usable: every other fully-known register (`x5 = 1`, `x11 = 192`, `x9`, the broadcast words,
  the stack top) is more than 2047 away from 6080.
- **Decision by branches.** `LD; XOR; LD; XOR; OR; SLTIU; ADDI x5; ECALL` (8) becomes
  `LD x26; BNE x26,x30,+24; LD x28; BNE x28,x31,+16; ADDI x10,x0,1; ADDI x5,x0,0; ECALL`
  followed by the 3-instruction `reject` stub: 7 cycles accepting, 5 or 7 rejecting. `Refines`
  bounds cycles from above, so unequal path costs are fine. A trick that folds the verdict into
  `x5` does *not* work: the HALT syscall traps unless `x5 ∈ {0}` at the final ECALL and
  `x5 = 1` would issue a HASH, so `x5` must be zeroed explicitly on every path.

Claim `694`: `71 + 602 + 21`. `verifier_length` is 1338 (the reject stub adds three instructions
and the root loses one). Verified locally with the official verifier.

## What did not work, and where the remaining fat is

Measured decomposition of the 694 cycles: **380 instruction cycles vs 314 hash cycles** (157 chain
hashes + 1 index + 12 root). The instruction overhead dominates. What I costed out:

- **Fewer or longer chains.** Minimising `94 + 9·C + 2·N` over `C` with 4-bit nibbles and
  `comp(C,16,N) ≥ 729·2^105` gives `C = 32` as the optimum; `C = 31` needs `N = 176` (725 cycles)
  and `C ≤ 30` cannot reach the availability threshold at all with 4-bit nibbles (the whole
  `[0,15]^30` space is `2^120` and its largest sum-slice is only `≈ 2^114.0`). The index carries
  `C·log2(w) ≤ 128` bits, so wider nibbles buy fewer but longer chains. `C = 32, N = 157` is the
  optimum of this family — the 6 cycles above are all that parameter tuning yields.

- **The per-chain prologue (9 instructions × 32 = 288 cycles) is not reducible by rebasing.**
  I first thought `ADDI x10, x12, -8` was removable by keeping a single pointer. It is not.
  `RiscvMachine.lean` fixes the HASH ABI: the input is `x11` bits at `x10`, and `writeHash`
  stores **four 64-bit words — 32 bytes — at `x12`**. A chain step hashes `header ‖ value`
  (192 bits at `slotAddr k - 8`) and must land the new value back at `slotAddr k`, so
  `x10 = x12 - 8` is forced, and `ChainSteps.ChainInv` carries exactly that (`slot`, `input`).
  Making input and output coincide needs the value first, but then the 32-byte write covers
  `value ‖ 16 more bytes` and destroys whatever tweak follows it.

- **Pre-loading the 32 headers into the data image** would drop `SD x12, x12, -8` from every
  prologue (another 32 cycles), and the header's address part never changes. It fails for the same
  overspill reason: chain `k`'s output covers `slotAddr k … +31`, and with stride 24 header `k+1`
  sits at `slotAddr k + 16`, inside that range. Protecting it needs stride ≥ 40, which inflates the
  root input from 6080 to 10048 bits (+8 compressions) and puts machine garbage into the hashed
  root input — net worse *and* a scheme change.

- **The root hash (12 compressions).** 6080 bits = 32 values × 128 + 31 interleaved 64-bit headers.
  Hashing only the values is `⌈4096/512⌉ = 8`, saving 4, but gathering them contiguously costs 32
  copies (128 instructions). A 32-bit header gives `⌈5088/512⌉ = 10`, saving 2, but the header must
  hold a ~21-bit address and a 16-bit tag.

- **`levelSetup` (8 cycles) is already minimal.** Eight of the fifteen level tags are chosen to be
  values that happen to sit in registers after the index phase — `x5 = 1`, `x11 = 192`,
  `x9 = 64` (low half of the payload cursor), `x22 = 120`, `x13 = 4224` (the checked signature
  length), `x24 = 5730`, `x25 = 8226` (the two jump bases) and `x0 = 0`. Only levels 7–13 cost an
  `ADDI` each, and `levVal_injective` forbids sharing.

- **`lanes` (39 cycles).** Eight lane words × 5 instructions (shift, AND, ADD to the accumulator,
  SUB from the broadcast jump base, SD), minus one ADD on the first. The `(~src >> s) & 0x78`
  trick computes `120 - 8·nibble` in one AND and would save one instruction per lane word, but the
  halfword the prologue loads has to be `jumpBase - 8·nibble`: the `JALR` immediate is 12-bit
  signed and `tableEnd k` is ~4400 + 156k, so the base must ride in the loaded value. Adding the
  base back costs exactly the instruction the trick saved.

- **`lengthCheck` (3 cycles) can become 2** by keeping 4224 in the data image and loading it with
  one `LD` (`x12` is already `dataBase` there). It is one cycle, and it shifts `indexLength`
  77 → 76, hence every `tableEnd k`, hence both `jumpBase` constants — which are *also* level tags
  in `levList` and words in `dataImage` — plus `verifier_length` and the fuel. Not worth the ripple.

## Next

1. **Drop the per-step level tag: worth 157 cycles (→ ~537). It is the only big prize left, and
   it is *not* proof surgery.**
   Each chain step is `SH x12, tag, -2` then `ECALL`; the `SH` exists only to put `levVal t` in the
   header's top halfword. Iterating `v ↦ H(hdr_k ‖ v)` with a chain-only tweak is still one-time
   secure — the constant-sum index set already forbids any `n' ≤ n` with `Σn' = Σn` other than `n`
   — so this is a proof problem, not a scheme problem. The obstacle is `Names.lean`: `decodeHdr`
   inverts `hdrNat` to recover `(k, t)` from a header, and `hdrNat_injective` is what makes that a
   function. Without level tags a header only identifies the chain, and the level would have to be
   recovered from the value, so the query→node map that `Values/Events/Resample/StageB` are built
   on has to be restructured. Worse, the *analysis* has no room for it: `Main.lean` ends at
   `probTrue ≤ (B − 492)/2^127 < B/2^127`, i.e. the per-query constant is exactly the target.
   Without level tags a chain-`k` query can hit any of that chain's 15 honest values, so the
   union bound behind `Spr` loses a factor 15, which is fatal at zero slack. Recovering it needs
   a genuinely sharper argument (a forgery needs *both* a chain preimage and an index hit, and
   the current proof charges only one), not a re-plumbing of `decodeHdr`. Budget accordingly.
2. If that lands, redo the `(C, w, N)` optimisation: with the per-step cost halved the balance
   shifts back toward longer chains, and 5-bit nibbles (`C ≤ 25`) become competitive.
3. The two-stage reciprocal trick used above is generic: it recovers the `ln 2` that a one-shot
   `(1-p)^k ≤ 1/(1+kp)` throws away, without leaving ℚ. Anyone tightening an availability bound in
   this competition probably wants it.
