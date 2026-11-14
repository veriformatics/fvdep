#!/usr/bin/env bash
# Re-pins one tool in tools/tools.lock to a release: its linux-x86_64 asset (the current asset's
# file name with the old version replaced by the new one, so each tool keeps its scheme: static
# musl builds, raw binaries) + the sha256 digest GitHub records for it (vflab + GitHub's runners
# are linux-x86_64). A Renovate PR bumps the version column alone; this rewrites the line.
# Usage: tools/pin-tool.sh <name> <version>
set -euo pipefail

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
lock="$root/tools/tools.lock"
name="${1:?usage: pin-tool.sh <name> <version>}"
version="${2:?usage: pin-tool.sh <name> <version>}"

read -r old_version old_url < <(awk -v n="$name" '$1 == n && $3 == "linux-x86_64" { print $2, $5 }' "$lock") || true
if [[ -z "${old_url:-}" ]]; then
    printf 'pin-tool: %s is not in %s\n' "$name" "$lock" >&2
    exit 2
fi
repo="$(sed -E 's#^https://github.com/([^/]+/[^/]+)/.*#\1#' <<<"$old_url")"
asset="${old_url##*/}"
asset="${asset//$old_version/$version}"
release="$(curl -fsSL "https://api.github.com/repos/$repo/releases/tags/v$version" ||
    curl -fsSL "https://api.github.com/repos/$repo/releases/tags/$version" ||
    curl -fsSL "https://api.github.com/repos/$repo/releases/tags/$name-$version")"
line="$(jq -r --arg n "$name" --arg v "$version" --arg asset "$asset" '.assets[]
    | select(.name == $asset)
    | "\($n) \($v) linux-x86_64 \(.digest | sub("^sha256:"; "")) \(.browser_download_url)"' <<<"$release")"
if [[ "$(grep -c . <<<"$line")" -ne 1 || "$line" != *"$version"* ]]; then
    printf 'pin-tool: expected one asset %s for %s %s, found:\n%s\n' "$asset" "$name" "$version" "$line" >&2
    exit 1
fi
{
    grep -v -E "^$name " "$lock"
    printf '%s\n' "$line"
} | awk '/^#/ { print; next } { print | "sort" }' >"$lock.new"
mv "$lock.new" "$lock"
printf 'pin-tool: %s pinned to %s\n' "$name" "$version"
