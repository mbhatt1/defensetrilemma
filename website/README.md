# Defense Trilemma — Documentation Site

A VitePress site that walks through the [Defense Trilemma](https://github.com/mbhatt1/stuff/blob/main/paper2_neurips.pdf) paper diagrammatically. One page per visualization, all 11 covered.

## Pages

1. **The Trilemma + 1D cross-section** (`/`) — landing page with the headline diagram
2. **2D Prompt Space** (`/prompt-space`) — geometric setup with safe/unsafe/boundary
3. **Boundary Fixation Proof** (`/boundary-proof`) — five-step proof as two converging chains
4. **Three-Level Hierarchy** (`/hierarchy`) — how each theorem strengthens the previous
5. **The K Dilemma** (`/dilemma`) — why no choice of K escapes both failure modes
6. **Discrete Dilemma** (`/discrete`) — injectivity vs completeness, no topology
7. **Extensions** (`/extensions`) — multi-turn, stochastic, pipeline failure modes
8. **Empirical Surfaces** (`/empirical`) — Llama mesa, GPT-OSS mosaic, Mini flat
9. **Counterexamples** (`/counterexamples`) — each hypothesis is necessary
10. **Engineering Prescription** (`/engineering`) — four strategies ordered by actionability
11. **Lean Artifact Map** (`/lean-artifact`) — 45-file mechanically verified proof

## Diagrams

All diagrams are inline SVG (no extra build dependencies). They respect light/dark theme via CSS variables in `docs/.vitepress/theme/custom.css`.

## Local development

```bash
pnpm install
pnpm run docs:dev      # serves on http://localhost:5173
pnpm run docs:build    # builds to docs/.vitepress/dist
pnpm run docs:preview  # preview the production build
```

## Stack

- VitePress 1.6 — markdown-driven static site
- Inline SVG for all diagrams
- Built-in math via markdown-it-mathjax3
- KaTeX styling via CDN
