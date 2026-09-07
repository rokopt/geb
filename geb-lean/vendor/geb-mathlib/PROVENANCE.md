# Vendored geb-mathlib provenance

- Source: https://github.com/rokopt/geb-mathlib.git
- Source commit: 673cfcaf782f1668c54193bf5ae532df547cf4aa
- Back-port patch: scripts/geb-mathlib-backport.patch (sha256 b3ed5fe2ba40fff470aecbf99618781590d8f00e68599d3b612d024de5bb1de2)
- Excluded modules: Geb.Prototypes.Computability.TreeScanner. Each is dropped along with its submodules and every import of it; see scripts/refresh-geb-mathlib.sh.
- `GebMeta` is not vendored: every import of it is dropped and each `{cite}` docstring role it supplies is rewritten to its escaped bracketed key; see scripts/refresh-geb-mathlib.sh.
- The files under `Geb/` are an unmodified mirror of the source commit except where the back-port patch changes them and where the exclusion above removes them; modified files carry a change notice in their header comment.
