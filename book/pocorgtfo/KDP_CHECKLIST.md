# KDP Publishing Checklist — Pick Two, Issue 0x01

## Files to upload
- **Interior:** `aipocorgtfo-book.pdf` — 420 pp, trim 6×9in (432×648 pt), all fonts
  embedded, no Type 3 fonts, no bleed (text interior), no crop marks.
- **Cover:** `cover.pdf` — full wrap 13.1958×9.25in (back + spine + front, 0.125in
  bleed), spine 0.9458in sized for 420 pp on white paper.

## Interior specs (already met)
- Trim **6×9in**. Inside/gutter margin **0.9in** (KDP minimum for 351–500 pp is
  0.875in). Outside/top/bottom **0.6–0.8in** (min 0.25in). ✔
- Fonts fully embedded (Palatino + Inconsolata + math), no Type 3. ✔
- Zero overfull lines >15pt; code wraps inside the measure. ✔
- Page numbers present; chapter openings start recto (`openright`). ✔

## If the page count changes, re-lock the spine
Spine width (white paper) = `pages × 0.002252 in`. Full cover width =
`0.25 + 12 + spine`. Height = `9.25`. Edit the four constants at the top of
`cover.tex` (and the `7.0641 / 13.0641 / 10.0641 / 6.595` panel coordinates) then
rebuild. `build.sh` prints the current numbers.

## KDP metadata (paste into the portal)
- **Title:** `Pick Two`
- **Subtitle (SEO):** `How AI-Safety Impossibility Results Reduce to One 1969
  Theorem — Machine-Checked in Lean 4`
  (The cover uses the gospel subtitle; the SEO line goes in the metadata field.)
- **Series:** `Pick Two`, Issue 0x01.
- **Author / contributors:** credit **Manish Bhatt** as the author (this is a homage edition).
- **Publisher:** set the KDP "Publisher" field to **Shrewd Research**.
- **Description:** see `VIRALITY.md` §8 (the ~185-word back-cover text).
- **Categories:** Computers/Artificial Intelligence (COM004000);
  Mathematics/Logic (MAT018000); Computers/Security (COM053000). After publishing,
  email KDP support with the ASIN to add up to 10 browse nodes (aim at small nodes
  for a "#1" flag).
- **7 backend keywords:** see `VIRALITY.md` §8.
- **Price:** paperback $24.99–$29.99; hardcover $39.99–$49.99; optional low-priced
  eBook. The free PDF is the funnel — say so in the description ("full text free as
  a PDF; buy print to own the artifact").

## Compliance (do not skip)
- **AI-content disclosure:** answer KDP's prompt honestly. Lean proofs are
  machine-*checked*, not AI-generated; if any prose was AI-assisted, disclose
  "AI-assisted."
- **Homage / trademark:** the copyright page already states this is an independent
  homage, not affiliated with or endorsed by the *International Journal of Proof of
  Concept or Get the Fuck Out*, and borrows no trade dress. Keep that line.
- **Attribution:** the copyright page credits Manish Bhatt as author and
  states the proofs are Lean-checked and sorry-free. Keep it.
- **No metadata violations:** no price/"bestseller" in title; the `||` renders fine;
  the SEO subtitle carries the real keywords.
- **Barcode:** leave the white box at the back-cover bottom-right; KDP drops the
  barcode there (or provide your own ISBN).

## Build
```sh
./build.sh          # builds interior + cover, prints page count + spine
```
Outputs `aipocorgtfo-book.pdf` and `cover.pdf`. Regenerate the interior source from
the book's own Verso chapters with `python3 convert.py` (done by `build.sh`).

## Technical compliance (verified on the built files)
| Check | Interior | Cover |
|-------|----------|-------|
| Trim / size | 6×9 exactly (432×648 pt) ✔ | 13.1958×9.25 in (6×9 + 0.125" bleed + 0.939" spine) ✔ |
| Encrypted | no ✔ | no ✔ |
| Fonts embedded | all ✔ (0 non-embedded, 0 Type 3) | all ✔ |
| Page rotation | 0 ✔ | n/a |
| Overfull/clipping | 0 overfull boxes ✔ | within safe margins ✔ |

PDF version 1.5 (KDP accepts standard, unencrypted PDF with embedded fonts). These
files are ready to upload as-is.

## Exact submission walkthrough (the part that needs your account)
1. Sign in at kdp.amazon.com → **Create** → **Paperback**.
2. **Paperback Details:** Language English; Title `Pick Two`; Subtitle
   (paste the SEO subtitle above); Series `Pick Two`, number 1; Author
   Manish Bhatt. Choose the free KDP ISBN (or enter your own)
   — this is the step that replaces the placeholder.
3. **Paperback Content:** Print ISBN = KDP-assigned; Publication date = today;
   Interior = Black & white on white paper; Trim = 6×9 in; Bleed = No; Cover finish
   = your choice. Upload `aipocorgtfo-book.pdf` as the manuscript and `cover.pdf` as
   the cover. Run KDP's Print Previewer; it should flag nothing (margins/spine are
   already within spec).
4. **Pricing:** set territories and price (see pricing guidance above).
5. (Optional) repeat **Create → Hardcover** with the same interior; KDP recomputes
   the hardcover spine, so regenerate `cover.pdf` with the hardcover spine width it
   shows (edit the constants in `cover.tex`, rebuild).
6. Submit for review. KDP validates the files on upload; the checks in the table
   above are exactly what it verifies.

After publishing, email KDP support with the ASIN to add the extra browse
categories listed above.
