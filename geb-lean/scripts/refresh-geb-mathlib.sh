#!/usr/bin/env bash
# Refresh vendor/geb-mathlib from upstream and re-apply the back-port patch.
# Usage: scripts/refresh-geb-mathlib.sh [<source-rev>]   (default: main)
set -euo pipefail

REPO_URL="https://github.com/rokopt/geb-mathlib.git"
SRC_REV="${1:-main}"

# Modules dropped from the vendored copy, each with its submodules and
# every import of it. A module qualifies when it depends on a definition
# absent from the pinned toolchain's dependencies and no patch hunk can
# supply it. See docs/geb-mathlib-backport-notes.md § Module exclusion.
#
# Name the narrowest module that carries the dependency, so that a
# sibling added upstream later is ingested rather than silently dropped.
#
# Geb.Internal.Computability.TreeScanner: imports
# Cslib.Computability.Machines.Turing.MultiTape.{Deterministic,TapeLemmas},
# added to cslib after the pinned v4.29.0-rc6 revision.
EXCLUDED_MODULES=(Geb.Internal.Computability.TreeScanner)
ROOT="$(cd "$(dirname "$0")/.." && pwd)"   # geb-lean package root
VENDOR="$ROOT/vendor/geb-mathlib"
PATCH="$ROOT/scripts/geb-mathlib-backport.patch"

# Fail immediately if the back-port patch is missing.
[ -f "$PATCH" ] || { echo "error: back-port patch not found: $PATCH" >&2; exit 1; }

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
git clone --quiet "$REPO_URL" "$TMP/gm"
git -C "$TMP/gm" checkout --quiet "$SRC_REV"
# A content checksum, not a commit hash: the commit that last touched
# the patch is unavailable in a shallow CI checkout and cannot name
# itself when the patch and PROVENANCE.md change in the same commit.
SRC_SHA="$(git -C "$TMP/gm" rev-parse HEAD)"
PATCH_SHA256="$(sha256sum "$PATCH" | cut -d' ' -f1)"
EXCLUDED_RENDERED="${EXCLUDED_MODULES[*]:-(none)}"

# Complete overwrite of the Geb namespace (no orphaned files).
rm -f "$VENDOR/Geb.lean"; rm -rf "$VENDOR/Geb"
cp "$TMP/gm/Geb.lean" "$VENDOR/Geb.lean"
cp -R "$TMP/gm/Geb" "$VENDOR/Geb"
cp "$TMP/gm/LICENSE" "$VENDOR/LICENSE"

cat > "$VENDOR/PROVENANCE.md" <<EOF
# Vendored geb-mathlib provenance

- Source: $REPO_URL
- Source commit: $SRC_SHA
- Back-port patch: scripts/geb-mathlib-backport.patch (sha256 $PATCH_SHA256)
- Excluded modules: $EXCLUDED_RENDERED. Each is dropped along with its submodules and every import of it; see scripts/refresh-geb-mathlib.sh.
- The files under \`Geb/\` are an unmodified mirror of the source commit except where the back-port patch changes them and where the exclusion above removes them; modified files carry a change notice in their header comment.
EOF

# Apply the back-port patch; a rejection is a hard, reportable failure.
# git apply resolves paths from the git repository root, not from a
# subdirectory; use --directory so the patch paths (vendor/geb-mathlib/...)
# resolve correctly when geb-lean is a subdirectory of a monorepo.
GIT_ROOT="$(git -C "$ROOT" rev-parse --show-toplevel)"
REL="$(realpath --relative-to="$GIT_ROOT" "$ROOT")"
( cd "$GIT_ROOT" && git apply -p1 --directory="$REL" "$PATCH" )

# Drop excluded modules after patching, so every hunk still anchors
# against the pristine upstream text it was generated from.
for mod in "${EXCLUDED_MODULES[@]}"; do
  rm -f "$VENDOR/${mod//.//}.lean"
  rm -rf "$VENDOR/${mod//.//}"
  # An import of an excluded module or of any of its submodules would
  # leave the surviving tree with a bad import.
  find "$VENDOR" -name '*.lean' -exec \
    sed -i -E "/^(public )?import ${mod}(\.|\$)/d" {} +
done

# A refresh that changes no vendored content (an upstream revision
# touching none of the mirrored files) leaves at most PROVENANCE.md
# modified. Restore it in that case so the tree is byte-clean and the
# CI workflow's create-pull-request step opens no pull request.
if ! git -C "$GIT_ROOT" status --porcelain -- "$REL/vendor/geb-mathlib" \
    | grep -qv 'PROVENANCE\.md$'; then
  git -C "$GIT_ROOT" checkout -- "$REL/vendor/geb-mathlib/PROVENANCE.md"
  echo "No vendored content changed; refresh is a no-op."
else
  echo "Refreshed vendor/geb-mathlib to $SRC_SHA and applied back-port patch."
fi
