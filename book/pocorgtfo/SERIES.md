# Pick Two — The Series

## Manifesto

Every field that touches AI has a folklore of "you can't do that" results, and
almost all of them are stated in English, argued by analogy, and believed on
reputation. **Pick Two** refuses folklore. Each issue takes one genuinely
load-bearing theorem at the intersection of AI, security, and mathematics and
ships it as a *machine-checked Proof of Concept* — Lean 4, sorry-free — or else
marks it, in the open, **Not formalized**. The editorial standard is singular and
non-negotiable: a claim is proven in the artifact, cited to a real published proof,
or confessed. **Prove it or confess it. PoC, or GTFO.**

## Format bible (every issue)

- **The Sermon** — numbered continuously across the series; the Pastor's anti-hype
  homily framing the issue's heresy.
- **The Statement** — the theorem in plain English, then in Lean type signatures.
- **PoC boxes** — self-contained, kernel-checked Lean, each ending green.
- **The Axiom Audit** — a mandatory `#print axioms` dump listing exactly what the
  proof trusts.
- **The "Not Formalized" Confession** — an honest ledger of every prose-only claim
  and why.
- **Exercises & Open Problems** — graded; some seed the next issue.
- **Colophon** — reproducibility: toolchain, build hash, one-command verification.

## The slate

| Issue | Title | Thesis (one line) | Core result to formalize | Audience |
|------|-------|-------------------|--------------------------|----------|
| 0x01 | **Issue 0x01** (this book) | Several AI-safety impossibilities are one 1969 theorem. | Lawvere fixed-point + IVT; the three trilemmata as one `rfl`. | AI safety, formal methods, hackers |
| 0x02 | **No Free Privacy** | Accuracy, privacy, generality — the trade-off is a theorem. | (ε,δ)-DP composition; reconstruction / Hardt–Talwar lower bounds. | Privacy engineers (OpenDP, Tumult) |
| 0x03 | **Two Generals, One Ledger** | No deterministic async consensus with one faulty node. | FLP (Fischer–Lynch–Paterson 1985); contrast CAP (Gilbert–Lynch). | Distributed systems, consensus/chains |
| 0x04 | **The Adversary Always Exists** | Adversarial examples are geometric inevitability, not a bug. | Concentration-of-measure robustness bounds (Gilmer, Shafahi et al.). | ML-security / robustness |
| 0x05 | **Knowledge Without Leakage** | Prove you know a secret while revealing nothing — precisely. | Zero-knowledge for 3-COL / QR (Goldwasser–Micali–Rackoff); simulator. | Cryptographers, ZK/SNARK builders |
| 0x06 | **Crypto-Agility or Death** | PQ migration is a correctness problem; verified impls are the hedge. | Functional-correctness + constant-time (HACL*/fiat-crypto) on an ML-KEM kernel. | Applied crypto, TLS/libs |
| 0x07 | **The Watermark That Washes Out** | Honest accounting of what watermarking can and cannot guarantee. | Detectability (Kirchenbauer et al.) + undetectable WM (Christ–Gunn–Zamir); paraphrase impossibility. | Provenance, governance |
| 0x08 | **Escape Is a Theorem** | A sandbox is only as sound as its proof. | Verified SFI soundness (RockSalt-style); CompCert semantic preservation as the positive case. | Systems security, compilers |
| 0x09 | **Learning Has a Price** | What is learnable is bounded — and some learnability is *undecidable*. | No-Free-Lunch (Wolpert) + EMX / CH-independence (Ben-David et al. 2019). | Learning theory, ML foundations |

Every proposed result is a real, correctly-attributed theorem. An issue ships only
when its `lake build` is green and its axiom audit is clean — **rigor gates the
date, never the reverse.**

## Cross-volume flywheel

- **One repo, one namespace** (`AIPoCGTFO.Vol0xNN`) with shared lower-bound/diagonal
  libraries; Vol 1's Lawvere core becomes an imported dependency for later issues.
- **Running mascot & motto:** the Diagonal Serpent eating its own tail; *"Prove it
  or confess it."*
- **Numbered sermons** carry a continuing argument across issues (collectors' hook).
- **The Challenge:** each issue ships one unproven lemma as a community bounty;
  solvers are credited and seed the next issue.

## Business & governance

- **Cadence:** ~2 issues/year, gated on a green build and a clean audit.
- **Model:** free canonical PDF + public CI-verified repo; revenue from print
  per-issue editions and a hardcover omnibus. The PDF is the funnel; print is the
  artifact.
- **CFP:** open call per issue — submit a theorem + draft Lean artifact; accepted
  authors co-sign.
- **Governance:** two-reviewer rule (one math-fidelity, one Lean-soundness), a
  mandatory axiom audit, and a public errata/retraction log. A silent `sorry` or an
  undisclosed axiom is a retractable offense. **PoC, or GTFO.**
