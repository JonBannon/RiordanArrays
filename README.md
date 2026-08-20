# Riordan Arrays

A single-paper LaTeX repository (mathematics), scaffolded from
`paper-templates` on 2026-08-19.

See `CLAUDE.md` for house style and the dialogue -> paragraph workflow; see
`dialogue/dialogue.md` for the development thread.

## Layout

- `main.tex` - master file; inputs everything.
- `sections/` - the manuscript, one file per section.
- `dialogue/dialogue.md` - the working thread (not the paper). Settled
  arguments get promoted into `sections/`.
- `refs.bib` - bibliography.
- `CLAUDE.md` - read first; house style + how the dialogue -> paragraph loop works.

## Build

    make          # build main.pdf
    make watch    # rebuild on save
    make clean

## Reading the typeset output in VSCode

Install the **LaTeX Workshop** extension (publisher: James Yu) for a live PDF
preview pane and SyncTeX (click a source line to jump to the PDF and back;
this requires `-synctex=1`, already wired into the `Makefile`).
