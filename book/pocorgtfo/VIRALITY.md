# Pick Two — Go-Viral-But-Correct Playbook

Synthesis of ten parallel research passes. The through-line of every one of them:
**this book spreads on honesty, not hype.** The audiences that can make it go
viral (hackers, formal-methods people, alignment researchers) also punish
overclaiming harder than anyone. Lead with the caveats and they become
amplifiers; bury them and they become the dunk.

## 0. The three non-negotiable caveats (put them on every artifact)

1. **The math is Lawvere, 1969.** The contribution is the *reduction/unification*
   and the machine-checking, not new mathematics. Say so first.
2. **It is existence, not frequency.** It proves a bad point *exists* under the
   premises; it says nothing about how often a real model hits it.
3. **The force rests on modeling premises** (reflectivity / continuity / exact
   calibration), graded free → defensible → strong. Inviting people to reject a
   premise is the honest escape — make it a feature.

## 1. The single strongest asset: the `rfl` collapse

The most screenshot-able, debate-generating, true object is:

> Three separately-published AI-safety "trilemmata" are the **same proof term** —
> equal by `rfl` in Lean 4. The kernel sees one theorem where the literature saw
> three.

It is concrete, checkable, non-accusatory (it does *not* claim the authors erred),
and falsifiable (open the file, run it). This is the hook for HN, X, LessWrong,
and the Lean community at once.

## 2. The artifacts to ship (before any post)

- **Public GitHub repo**, toolchain pinned, with a **one-command build**
  (`lake exe cache get && lake build`) and a **`#print axioms` target** that prints
  the audit (combinatorial core axiom-free; analytic parts use the 3 standard
  axioms). A green CI badge + a `grep -r sorry` gate that proves sorry-free.
- **A standalone gist**: the ~5-line `lawvere` proof, and the three trilemmata
  reduced to one term by `rfl`, compiling against pinned Mathlib.
- **A live.lean-lang.org link** so a skeptic verifies the kernel check in 30s with
  no install.
- **Zenodo DOI** for the repo snapshot + the free book PDF; **a short companion
  paper on arXiv** (cs.LO primary; cross-list cs.AI, cs.LG, math.CT). Paper is the
  citable entry point, book is the depth, repo is the trust anchor; each links the
  other two.
- **The free PDF**, ungated. Sell the print as the artifact, never gate the PoC.
- **(Stretch) a polyglot PDF** that is also a zip of the Lean sources — a real
  *PoC‖GTFO* issue is a polyglot, and this crowd treats anything less as cosplay.
  `unzip book.pdf && lake build` reproducing the sorry-free check is the flex.

## 3. Channel-by-channel

**Hacker News** — biggest reach, highest flame risk. `Show HN:` framed as an
artifact, author present in-thread from minute one, caveat #1 in the first comment.
Post ~8–10am ET weekday.

**lobste.rs** — best cultural fit; needs a member to submit under `formalmethods`/
`compsci`. Expect (welcome) a proof-checker.

**Lean Zulip (#general / #announce)** + **math/types Mastodon (mathstodon, types.pl)**
— lead with the artifact, cite the Mathlib lemmas you build on so authors feel
cited not recruited. No cold DMs for RTs; post where they already read.

**LessWrong + Alignment Forum** (cross-post, request AF promotion) — open with an
epistemic-status box stating your own weak points. Reframe the coupling theorem as
**"a frontier map for probing, not a refutation"** — that converts the
interpretability/ELK crowd. A 3–4 post distillation sequence beats one 421-page
drop.

**X / Bluesky** — the launch thread: hook → the collapse → name Lawvere → the `rfl`
screenshot → the honest caveats (this beat earns the RT) → why it still matters →
the ask ("tell me where the premises are wrong"). Carry image = the `rfl` shot;
quote-bait = an animated diagonal GIF.

**r/netsec, r/ProgrammingLanguages, r/types, r/math** — frame as "a surprising
unification, here's the proof," repo first, book second. r/math and r/netsec remove
anything that smells promotional.

**tmp.0ut / Phrack / DEF CON / CCC** — native habitat for the homage. Contribute the
artifact (polyglot), submit a lightning talk ("Three AI impossibility results are
one 1969 theorem, machine-checked"). CCC especially rewards formal proof + anti-hype.

## 4. Short-form video (the ideas, not the book)

Five honest concepts: (a) "I broke this chatbot with one sentence" → the liar/
self-reference; (b) "Pick two" animated triangle (faithful/calibrated/covering);
(c) "the prompt that eats its own safety" ouroboros; (d) "Cantor, Gödel, the liar,
halting — same trick" card-flip; (e) "I didn't trust the proof, so a machine checked
it." The one visualization to hand an explainer channel (3Blue1Brown/Veritasim/
Welch Labs type): **the Diagonal Mirror** — grid of bots × questions, flip the
diagonal, collapse to one bot asked about itself, reveal the same motion under
Cantor/Gödel/halting. Honest one-liner: *"Some things we want from AI aren't hard —
they're impossible, and a 1969 paradox proves it"* (true: existence, under stated
premises).

## 5. Distribution / earned media

- **Newsletters** (tailored angle each, no blast): The Gradient (long-form),
  tl;dr sec (security), Import AI (lead with existence-not-frequency), The Batch,
  CAIS/ML-Safety newsletters, n-Category Café (Lawvere-adjacent), Hillel Wayne,
  Quanta tip line.
- **Podcasts**: AXRP (ideal — alignment theory), MLST, The Inside View, Security
  Cryptography Whatever, Type Theory Forall, Darknet Diaries (zine-culture angle).
- **Academic**: companion paper to ITP/CPP/CAV (formal methods), SATML / NeurIPS
  & ICML safety workshops, USENIX/S&P position tracks; Topos Institute colloquium
  (category theory ∩ safety — strong fit); artifact-evaluation badge (CAV/CPP/
  USENIX) advertising the one-command sorry-free build.
- **The "Break My Premises" bounty** — since the math is settled, invite attacks on
  the *modeling premises*. Recognition/small bounty for the strongest critique.
  Keeps the honest caveat central and turns critics into contributors.

## 6. The honest two-week launch sequence

- **D1 (Tue):** push repo, tag v1.0, cut Zenodo DOI, finalize free PDF.
- **D2:** email top-3 newsletters under embargo with tailored angles; line up a podcast.
- **D3–4:** submit artifact for AE badge; post arXiv companion (DOI-linked).
- **D5 (Fri):** soft-announce to Lean Zulip + category-theory community (fixes first).
- **Weekend:** fold in corrections; cut v1.0.1 if needed.
- **D8 (Mon, launch):** Show HN + LessWrong (caveats first) + measured X thread;
  newsletter embargo lifts same morning.
- **D9:** open the "break my premises" bounty; answer every thread personally.
- **D10–11:** record podcast(s); pitch second-tier newsletters citing traction.
- **D12–14:** publish a "what the critiques got right" follow-up; submit talk CFPs.

Throughout: one DOI'd artifact underpins every channel; caveats lead every post;
no outlet gets a duplicate blast.

## 7. Lines NOT to cross (catchy but false — never ship these)

- "AI chatbots are mathematically proven to fail." (frequency claim — false)
- "We proved AI is unsafe / doomed." (not the argument)
- "Prompt injection can never be stopped." (bars *completeness*, not mitigation)
- "We discovered a new theorem." (it's Lawvere 1969)
- "Interpretability is impossible." (only *exact* probing, under one premise)
- "These researchers wasted the field's time." (`rfl` does not imply error)
- "This holds regardless of assumptions." (premise-dependent by design)

## 8. Copy bank (honest, reusable)

**Catchphrases:** Three corners and no fourth. · PoC, or GTFO. ·
Kernel-checked or GTFO. · Pick two — the third is a fixed point. · No universal
verdict. · You can't patch a theorem. · Sorry-free or it didn't happen. · Same
diagonal, different corner.

**KDP SEO subtitle (metadata):** *How AI-Safety Impossibility Results Reduce to One
1969 Theorem — Machine-Checked in Lean 4.*
(Cover keeps the gospel subtitle; the SEO line is for the Amazon metadata field.)

**KDP backend keywords:** formal verification Lean 4 theorem prover · AI safety
impossibility results alignment · Lawvere fixed point diagonal argument ·
machine-checked proofs mathematical logic · category theory computer science
security · intermediate value theorem topology proofs · hacker zine security
research writeups.

**KDP categories:** Computers/AI (COM004000) · Mathematics/Logic (MAT018000) ·
Computers/Security (COM053000); then request up to 10 browse nodes via KDP support,
aiming at small niches for a #1 flag.
