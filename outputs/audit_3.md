# Audit 3 — §2 Related Work, Table 1, and §2/Table 1 bibliography

**Auditor:** Agent 3 of 10
**Scope:** `/Users/mbhatt/stuff/paper2_v3.tex`, §2 Related Work (lines 211-245) and any Table 1 positioning / empirical-correspondence table, plus bibitems referenced from those.
**Mode:** READ-ONLY.
**Web tools:** `WebFetch` and `WebSearch` are both denied in this session (permission errors). Arxiv IDs are therefore checked only for format/year plausibility, not against live arxiv titles.

---

## 0. Orientation — what §2 and "Table 1" actually contain

§2 Related Work is a short two-paragraph section (lines 211-245). It cites exactly 19 keys:

```
szegedy2013intriguing, goodfellow2014explaining, carlini2017evaluating,
madry2018towards, tsipras2018robustness, fawzi2018adversarial,
cohen2019certified, katz2017reluplex, singh2019abstract, huang2017safety,
bagnall2019certifying, naitzat2020topology, zou2023universal,
chao2024jailbreaking, mehrotra2024tree, greshake2023indirect,
mouret2015illuminating, samvelyan2024rainbow, wolpert1997no
```

**There is no "Table 1" anywhere in `paper2_v3.tex`.** I enumerated every `\begin{table}` in the file (see lines 809, 872, 1066, 1083, 1106, 1130, 1609, 1722, 1908, 1931, 1944, 1955, 1969, 1979, 1989, 1999, 2027, 2066, 2126, 2151) — all are later empirical/experimental tables (`tab:multi-turn`, `tab:stochastic`, `tab:three-target`, `tab:llamaguard-demo`, `tab:forced-collapse`, `tab:paraphrase-unsafe`, `tab:pipeline`, `tab:counterexample-ablation`, `tab:smoketests`, `tab:continuous-sweep`, `tab:gp-sensitivity`, `tab:resolution`, `tab:higher-dim-lipschitz`, `tab:seed-replication`, `tab:independent-dataset`, `tab:ci`, `tab:live-sweep`, `tab:judge-robustness`, `tab:judge-committee`, `tab:pair-baseline`). **None is a §2-positioning or "empirical correspondence" table; no table contains a "MART [24] confirms diminishing safety returns"–style row.**

The bibliography has a telltale comment at line 1384:

```
% --- New references for comparison table ---
```

…followed by 17 bibitems (`ge2024mart`, `hubinger2024sleeper`, `anil2024many`, `kim2025manyshot`, `zhan2024injecagent`, `zhang2024asb`, `yuan2025instability`, `skoltech2025quant`, `eth2025gguf`, `hammoud2024merging`, `liu2026whackamole`, `iris2025`, `zhao2025weak`, `huang2025safetytax`, `huang2026formal`, `slingshot2026`, plus `munshi2026manifold` earlier). A full-text `\cite{…}` grep shows **none of these 16 "comparison-table" bibitems is cited anywhere in the body** (only `munshi2026manifold` is cited, from §Experiments, lines 910 and 973).

So the intended Table 1 is missing: the bibitems provisioned for it sit orphaned in the bibliography. This is the dominant finding of this audit.

---

## 1. Per-item audit table

Legend: `C` = cited in §2 text, `B` = bibitem exists, `PL` = arxiv-ID / venue / year plausibility.

### 1a. Bibitems cited from §2 Related Work

| Key | C§2? | Bibitem? | ID / venue | Year sanity | PL | Verdict |
|---|---|---|---|---|---|---|
| `szegedy2013intriguing` | yes | line 1363 | ICLR 2014 | yes (famous 2013 arxiv → ICLR'14) | OK | ✅ |
| `goodfellow2014explaining` | yes | line 1284 | ICLR 2015 | yes (FGSM paper) | OK | ✅ |
| `carlini2017evaluating` | yes | line 1302 | IEEE S&P 2017 | yes (C&W attack) | OK | ✅ |
| `madry2018towards` | yes | line 1329 | ICLR 2018 | yes (PGD paper) | OK | ✅ |
| `tsipras2018robustness` | yes (×2) | line 1368 | ICLR 2019 | yes (Tsipras et al.) | OK | ✅ |
| `fawzi2018adversarial` | yes | line 1313 | NeurIPS 31 (2018) | yes | OK | ✅ |
| `cohen2019certified` | yes | line 1279 | ICML 2019 | yes (randomized smoothing) | OK | ✅ |
| `katz2017reluplex` | yes | line 1295 | CAV 2017 | yes (Reluplex) | OK | ✅ |
| `singh2019abstract` | yes | line 1358 | POPL 2019 | yes (DeepPoly/ELINA) | OK | ✅ |
| `huang2017safety` | yes | line 1324 | CAV 2017 | yes | OK | ✅ |
| `bagnall2019certifying` | yes | line 1261 | AAAI 2019 | plausible; the Coq-verified-generalization paper from Bagnall/Stewart is real | OK | ✅ |
| `naitzat2020topology` | yes | line 1339 | JMLR 21(184), 2020 | yes | OK | ✅ |
| `zou2023universal` | yes | line 1378 | arXiv 2307.15043, 2023 | yes (GCG attack) | OK | ✅ |
| `chao2024jailbreaking` | yes (×2, one as `\cite{chao2024jailbreaking}` at 224 and one at 2142) | line 1273 | arXiv 2310.08419, 2024 | yes (PAIR) | OK | ✅ |
| `mehrotra2024tree` | yes | line 1307 | NeurIPS 37, 2024 | yes (TAP) | OK | ✅ |
| `greshake2023indirect` | yes | line 1318 | AISec 2023 | yes (indirect prompt injection seminal paper) | OK | ✅ |
| `mouret2015illuminating` | yes | line 1334 | arXiv 1504.04909, 2015 | yes (MAP-Elites) | OK | ✅ |
| `samvelyan2024rainbow` | yes | line 1351 | NeurIPS 37, 2024 | yes (Rainbow Teaming) | OK | ✅ |
| `wolpert1997no` | yes | line 1373 | IEEE TEvC 1(1):67–82, 1997 | yes — matches the canonical Wolpert & Macready NFL paper exactly | OK | ✅ |

All 19 §2 citations resolve to bibitems. (Item 3 of scope: ✅.)

### 1b. "Comparison-table" bibitems (provisioned, uncited)

These are listed under the `% --- New references for comparison table ---` banner but never cited from any `\cite{…}` call. They are the bibitems that Item 1/2 of the scope was asking us to cross-check against "Table 1".

| Key | Referenced from §2/Table 1? | Bibitem line | ID / venue | Year sanity | Verdict |
|---|---|---|---|---|---|
| `ge2024mart` | **no (Table 1 missing)** | 1386 | NAACL 2024; authors `K. Ge et al.` | MART is the Meta 2023 paper by Ge et al. ("MART: Improving LLM Safety with Multi-round Automatic Red-Teaming", arXiv 2311.07689); reposting it as NAACL 2024 is plausible | ⚠️ orphan + lead author initial unverifiable without web |
| `hubinger2024sleeper` | no | 1392 | arXiv 2401.05566, 2024 | yes, real Anthropic paper | ⚠️ orphan |
| `anil2024many` | no | 1398 | NeurIPS 37, 2024 | many-shot jailbreaking (Anthropic) is a real 2024 paper | ⚠️ orphan |
| `kim2025manyshot` | no | 1403 | ACL 2025 | plausible follow-up venue/year; unverifiable | ⚠️ orphan, unverified |
| `zhan2024injecagent` | no | 1408 | Findings of ACL 2024 | InjecAgent is a real 2024 paper by Zhan et al. (arXiv 2403.02691) | ⚠️ orphan |
| `zhang2024asb` | no | 1414 | arXiv 2410.02644, 2024 | Agent Security Bench (ASB) is a real 2024 paper; 2410.x fits Oct 2024 | ⚠️ orphan |
| `yuan2025instability` | no | 1420 | arXiv **2512.12066**, 2025 | 2512.xxxxx ⇒ Dec 2025 — arxiv does reach 25YY in December of that year; numerically valid (arxiv IDs run to 2512.xxxxx by end of 2025) | ⚠️ orphan, plausible "future" arxiv ID |
| `skoltech2025quant` | no | 1425 | arXiv 2502.15799, 2025 | Feb 2025; valid | ⚠️ orphan |
| `eth2025gguf` | no | 1431 | ICML 2025 | plausible | ⚠️ orphan |
| `hammoud2024merging` | no | 1437 | Findings of EMNLP 2024 | "Model Merging and Safety Alignment" by Hammoud et al. is real | ⚠️ orphan |
| `liu2026whackamole` | no | 1443 | arXiv **2603.20957**, 2026 | 2603.x ⇒ March 2026; consistent with paper's 2026 framing | ⚠️ orphan, future-dated |
| `iris2025` | no | 1448 | NAACL 2025 | plausible | ⚠️ orphan |
| `zhao2025weak` | no | 1453 | ICML 2025 | "Weak-to-Strong Jailbreaking" (Zhao et al.) is a real paper, originally late 2024 | ⚠️ orphan |
| `huang2025safetytax` | no | 1458 | arXiv 2503.00555, 2025 | Mar 2025; valid | ⚠️ orphan |
| `huang2026formal` | no | 1463 | arXiv **2603.00047**, 2026 | Mar 2026; future-dated but paper is positioned as 2026 | ⚠️ orphan, future-dated |
| `slingshot2026` | no | 1468 | arXiv **2602.02395**, 2026 | Feb 2026; future-dated but paper is 2026 | ⚠️ orphan, future-dated |
| `munshi2026manifold` | cited from §Experiments (not §2), line 1344 | — | arXiv **2602.22291v2**, 2026 | Feb 2026. **Format concern:** arxiv daily submission counters typically do not reach `.22291` — most months land around `.1xxxx`–`.19xxx`. `.22291` is higher than typical monthly submission counts, so this ID is borderline implausible even for a heavy-volume month | ⚠️ cited (but not in §2), ID suspicious |

**Spot-check summary (Item 2, per instructions):** I was asked to spot-check 5 entries online. Because `WebFetch` and `WebSearch` are both blocked in this session, I fell back to arxiv-ID format sanity + year sanity + author-prior-knowledge checks. No entry is obviously fabricated (e.g., no arxiv `3000.xxxxx`), but also no entry is positively confirmed against live arxiv. The most suspicious formatting item is `munshi2026manifold`'s `2602.22291v2` (abnormally high within-month counter).

---

## 2. Item-by-item scope responses

### Item 1 — Every paper cited in §2 or Table 1 has a `\bibitem`

- Every one of the 19 §2 `\cite{…}` keys resolves (see table 1a).
- Table 1 **does not exist**, so the question is vacuous for Table 1. See §0.

Verdict: ✅ for §2; ⚠️ N/A for Table 1 (cannot audit a table that isn't present).

### Item 2 — "MART [24] confirms diminishing safety returns"–type mappings

- No such mappings appear in the paper. No row of any table in `paper2_v3.tex` matches the form "MART [24] confirms …". The §2 prose does not name MART, sleeper agents, or many-shot jailbreaking either.
- The comparison-table bibitems (ge2024mart, hubinger2024sleeper, anil2024many, kim2025manyshot, zhan2024injecagent, zhang2024asb, …) are orphaned — staged for a table that was removed or never added. This is the single largest issue in my scope.
- Online spot-checks of 5 arxiv IDs: **not performed** — WebFetch/WebSearch both denied with permission errors (exact error: "Permission to use WebFetch has been denied"). Fall-back format/year sanity was applied to every arxiv ID; all pass except the high-counter `2602.22291v2` (`munshi2026manifold`), which is flagged ⚠️.

Verdict: ❌ (mappings absent) / ⚠️ (one suspicious arxiv ID, many orphan bibitems).

### Item 3 — Every `\cite{foo}` in §2 resolves to a bibitem

All 19 resolve. ✅.

### Item 4 — "Closest precedent is the no-free-lunch framework [22]" → `wolpert1997no`

- Text (line 231-233): *"The closest conceptual precedent is the no-free-lunch framework~\cite{wolpert1997no}"* — matches scope-item wording exactly.
- Bibitem `wolpert1997no` at line 1373: `D. H. Wolpert and W. G. Macready. No free lunch theorems for optimization. IEEE Trans. Evol. Comput., 1(1):67–82, 1997.` This is the canonical NFL paper (authors, title, venue, volume/issue/pages, and year are all exactly correct to my prior knowledge, not confirmed online in this session).
- The paper is also referred to as [22] in any `numbers`-style render, but I cannot independently verify that `wolpert1997no` is literally entry 22 in the printed `plain` bibliography ordering without compiling; `\bibitem{wolpert1997no}` is the 22nd `\bibitem` if we ignore the late "comparison-table" block — counting from `alon2023detecting` (1), ..., `wolpert1997no` is bibitem #22 in the list. That matches.

Verdict: ✅.

### Item 5 — Future-dated arxiv IDs

Paper is positioned as 2026, so 26XX.xxxxx IDs are expected. Flags:

| Key | ID | Comment |
|---|---|---|
| `munshi2026manifold` | 2602.22291v2 | ⚠️ within-month counter `.22291` is unusually high. Possibly real for Feb 2026 if arxiv volume has grown; flag for author confirmation. |
| `liu2026whackamole` | 2603.20957 | ⚠️ Mar 2026, `.20957` also high but less extreme. |
| `huang2026formal` | 2603.00047 | OK — very early-March 2026 submission. |
| `slingshot2026` | 2602.02395 | OK — early-Feb 2026. |
| `yuan2025instability` | 2512.12066 | OK — Dec 2025, plausible volume. |

No ID matches the scope's "obviously wrong" pattern (e.g., `3000.xxx`, `9999.xxx`). Two IDs (`2602.22291v2`, `2603.20957`) have high within-month counters that deserve manual verification but are not definitionally impossible.

Verdict: ⚠️ (two borderline IDs to verify; none clearly wrong).

---

## 3. Summary table

| # | Scope item | Status |
|---|---|---|
| 1 | Every §2 / Table 1 citation has a bibitem | ✅ (§2 all resolved); ⚠️ N/A for Table 1 (table absent) |
| 2 | Table 1 MART-style mappings exist + spot-check 5 arxiv IDs | ❌ Table 1 missing; comparison-table bibitems are orphaned. Online spot-checks not possible (WebFetch/WebSearch denied). |
| 3 | Every `\cite{foo}` in §2 resolves | ✅ 19/19 |
| 4 | "[22] = wolpert1997no" = real NFL paper | ✅ |
| 5 | Future-dated arxiv IDs look plausible | ⚠️ all 2026 IDs are in-band; `2602.22291v2` (munshi2026manifold) and `2603.20957` (liu2026whackamole) have high within-month counters worth confirming |

---

## 4. Key findings / recommendations

1. **Missing Table 1.** The bibliography clearly was prepared for a comparison / empirical-correspondence table ("`--- New references for comparison table ---`" at line 1384). That table is not present in the source, and 16 of the 17 "new" bibitems (`ge2024mart`, `hubinger2024sleeper`, `anil2024many`, `kim2025manyshot`, `zhan2024injecagent`, `zhang2024asb`, `yuan2025instability`, `skoltech2025quant`, `eth2025gguf`, `hammoud2024merging`, `liu2026whackamole`, `iris2025`, `zhao2025weak`, `huang2025safetytax`, `huang2026formal`, `slingshot2026`) are **never cited**. These will produce LaTeX warnings and — more importantly — the §2 → Table 1 narrative arc promised by scope is absent in the paper. Either add the table (preferred) or delete the orphan bibitems.
2. **§2 Related Work coverage is clean.** All 19 citations resolve; `wolpert1997no` is accurately described as the no-free-lunch precedent.
3. **Arxiv ID watch.** `munshi2026manifold`'s `2602.22291v2` has an unusually high intra-month counter; worth a manual confirmation that the ID is exactly as assigned by arxiv. Two 2603.* IDs (`liu2026whackamole`: `2603.20957`; `huang2026formal`: `2603.00047`) are consistent with the paper's 2026 framing. None are obviously wrong.
4. **Web verification could not be performed** for 5-entry spot-checks because both `WebFetch` and `WebSearch` returned "Permission … denied." I noted this as an audit limitation rather than attempting a workaround.

---

## 5. Files referenced

- `/Users/mbhatt/stuff/paper2_v3.tex` — entire file (§2 at lines 211-245; bibliography at lines 1254-1473).
