# Vendored geb-mathlib provenance

- Source: https://github.com/rokopt/geb-mathlib.git
- Source commit: caf42eed39714f96794bed4135330c7dbf2bf2a2
- Back-port patch: scripts/geb-mathlib-backport.patch (sha256 5e8e0ce34854825cadd7c58fc8fa58f41ce53615b73ce5fbbef1a07e2b244b67)
- Excluded modules: Geb.Prototypes.Computability.TreeScanner. Each is dropped along with its submodules and every import of it; see scripts/refresh-geb-mathlib.sh.
- The files under `Geb/` are an unmodified mirror of the source commit except where the back-port patch changes them and where the exclusion above removes them; modified files carry a change notice in their header comment.
