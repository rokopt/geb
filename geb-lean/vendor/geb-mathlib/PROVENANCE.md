# Vendored geb-mathlib provenance

- Source: https://github.com/rokopt/geb-mathlib.git
- Source commit: 133ff2aef3dd97f07e07c991f13431f8fa650d96
- Back-port patch: scripts/geb-mathlib-backport.patch (sha256 b376b2147dfa91fc2a8734a5d9eef881547ba8c383a2294c6fe96592e6636df3)
- Excluded modules: Geb.Internal.Computability.TreeScanner. Each is dropped along with its submodules and every import of it; see scripts/refresh-geb-mathlib.sh.
- The files under `Geb/` are an unmodified mirror of the source commit except where the back-port patch changes them and where the exclusion above removes them; modified files carry a change notice in their header comment.
