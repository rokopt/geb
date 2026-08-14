# Vendored geb-mathlib provenance

- Source: https://github.com/rokopt/geb-mathlib.git
- Source commit: a3e78987794b27e82f0c6047dd5f8457ecb5ba32
- Back-port patch: scripts/geb-mathlib-backport.patch (sha256 02e9b21570d91c0c04a917b12ba6d53d89ded5c46e9c827344cbe0fa4616f82d)
- Excluded modules: Geb.Internal.Computability.TreeScanner. Each is dropped along with its submodules and every import of it; see scripts/refresh-geb-mathlib.sh.
- The files under `Geb/` are an unmodified mirror of the source commit except where the back-port patch changes them and where the exclusion above removes them; modified files carry a change notice in their header comment.
