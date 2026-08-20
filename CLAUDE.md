# Working notes for Claude

This repository is a single mathematics writing project. Read this file at
the start of every session. It is the source of truth for how we work together;
the flavor-specific conventions (notation, prose, citations) are in the second
half of this file.

## The core workflow: dialogue -> paragraphs

The point of this repo is that **discussions become paper text**, so nothing has
to be reconstructed later. Concretely:

1. We think out loud in `dialogue/dialogue.md`. This is the messy thread:
   conjectures, failed attempts, objections, "what about this case." It is
   version-controlled but is **not** the manuscript.
2. When an argument settles, I (the author) say something like *"promote this"*
   or *"this is ready for the paper."* You then take the settled idea and write
   it as finished prose into the relevant file under `sections/`, in the house
   style below.
3. Promotion is a rewrite, not a copy-paste. Dialogue prose is exploratory and
   first-person; paper prose is declarative, claim-before-support, and free of
   the scaffolding ("as we said", "let's try", "I think").
4. After promoting, leave a one-line pointer in `dialogue.md` noting which
   section now contains the settled version, so the thread stays navigable.

When I ask a question in chat that produces something worth keeping, **offer to
record it**, either as a dialogue entry or, if it is ready, as paper text. Do
not let good arguments evaporate into the chat scrollback.

## Standing instructions on content

- Treat every argument or derivation you generate as a **provisional draft**,
  not settled work. Flag the load-bearing step explicitly: the premise that is
  doing the work, the inference an objection would target, the "it follows that"
  that hides real work. I would rather see "the weak joint is here" than a
  confident wrong argument.
- When you see a weak joint, say so even if I did not ask. Acting as a hostile
  referee is a feature, not rudeness.
- Do not silently invent citations. If a reference is needed and you are not
  certain of it, write `\cite{NEEDS-REF:ShortKey}` (no spaces in the key, so it
  is findable by grep) rather than fabricating one.

## How I want you to work

- **No em-dashes.** Never use em-dashes (the long dash, or `---`/`--`) in paper
  text, LaTeX, or chat. Rephrase, or use a colon, comma, or parentheses.
- **Neutral tone.** Avoid hyperbole and editorializing (no "genuinely",
  "elegant", "crucial", "profound", "beautiful"). Keep a plain, declarative
  register.
- **Apply edits directly.** Default to making the edit and rebuilding, not
  proposing and waiting. I read the compiled output and can roll back with git.
- **Build with `make`.** Never run bare `latexmk -pdf`; use `make` (which keeps
  SyncTeX wired). When you edit a `.tex` file, run the build, read the log, and
  fix errors before telling me you are done. Never leave the tree in a
  non-compiling state across a hand-off.

## Build

- Build with `make` (runs `latexmk -pdf -synctex=1 main.tex`). `make clean`
  removes auxiliary files; `make watch` rebuilds on save.
- The compiled `main.pdf` is what I read in the LaTeX Workshop preview pane, so
  keep it building at all times.

## Memory

You have a persistent per-project memory (a `memory/` directory under this
repo's Claude project folder). Use it for facts that are not derivable from the
files or git history: standing preferences, decisions and their rationale,
pointers to external sources. Do not record what the repo already captures.

---

# Mathematics flavor: house style

## Document class and spacing

- `\documentclass[12pt,reqno]{amsart}`. `reqno` puts equation numbers on the right.
- `\linespread{1.1}`, `\allowdisplaybreaks`, and equations numbered within
  subsections: `\numberwithin{equation}{subsection}`.

## Notation

- All macros live in `macros.tex`. Use them; do not reinvent notation inline.
  If you need a symbol with no macro yet, add it to `macros.tex` with a brief
  comment rather than defining it inline in a section.

## Theorem environments

- A **section-numbered** family sharing one counter keyed to `thm`: `thm`, `lem`,
  `cor`, `prop`, `definition`, `rem`, `example`, `nota`, `claim`, `ques`.
- A **letter-numbered** family for main results stated in the introduction:
  `letterthm` (-> Theorem A, B, ...), `lettercor`, `letterconj`.
- Unnumbered: `mainthm`, `question`, `opr` (open problem).
- Step environments (`step`) structure long proofs: label them **Step 1**,
  **Step 2**, set in bold with the statement in italic.

## Theorem and proof style

- Hypotheses before conclusion, always; hypotheses separated by commas, the
  conclusion after "Then".
- Cited results carry the citation in brackets after the environment opening:
  `\begin{thm}[\cite{key}]`.
- Do not open a proof with "Proof." (amsthm supplies it). Open with "First we
  show ..." when the proof has phases.
- Estimates go in align/equation environments, not inline. Use `\leqslant`,
  `\geqslant`. Use `\varepsilon` (macro `\eps`). Do not add manual `\qed`.

## Citations

- `\cite{key}` or `\cite[Theorem X.Y]{key}`; page/line as `\cite[p.~9, line~-2]{key}`.
- Author names in running text are surname only.
- `\bibliographystyle{amsalpha}` with `bibtex`.
- Uncertain reference: `\cite{NEEDS-REF:ShortKey}`.

## American spelling

- "fiber" not "fibre", "center" not "centre".
