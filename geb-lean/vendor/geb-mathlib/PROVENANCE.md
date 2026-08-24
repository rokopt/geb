# Vendored geb-mathlib provenance

- Source: https://github.com/rokopt/geb-mathlib.git
- Source commit: c8fe7b98706bb288a67ad46162534d27fd11a0cc
- Back-port patch: scripts/geb-mathlib-backport.patch (sha256 db914016f36be3bf71797f55815980d2e04ad7541d10eec88f33b94f721e8b09)
- Excluded modules: Geb.Prototypes.Computability.TreeScanner. Each is dropped along with its submodules and every import of it; see scripts/refresh-geb-mathlib.sh.
- The files under `Geb/` are an unmodified mirror of the source commit except where the back-port patch changes them and where the exclusion above removes them; modified files carry a change notice in their header comment.
