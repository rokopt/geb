# Vendored geb-mathlib provenance

- Source: https://github.com/rokopt/geb-mathlib.git
- Source commit: 37d8590716954a02c96e8f06caa30b0c62aec6ec
- Back-port patch: scripts/geb-mathlib-backport.patch (sha256 bd9087325bf7416c6516de32a81e9f1c0210cc9278a7fb854e9223622fd204ad)
- Excluded modules: Geb.Prototypes.Computability.TreeScanner. Each is dropped along with its submodules and every import of it; see scripts/refresh-geb-mathlib.sh.
- `GebMeta` is not vendored: every import of it is dropped, each `{cite}` docstring role it supplies is rewritten to its escaped bracketed key, and each `{name}` role naming one of its declarations is rewritten to `{lit}`; see scripts/refresh-geb-mathlib.sh.
- The files under `Geb/` are an unmodified mirror of the source commit except where the back-port patch changes them and where the exclusion above removes them; modified files carry a change notice in their header comment.
