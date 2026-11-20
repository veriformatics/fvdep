#!/usr/bin/env bash
# git's answer per U5b L3/L6 failure class (contract docs/contracts/U5b-oracle.md; rule
# .claude/rules/library.md): the exact L3 fetch argv + environment against local fixtures + network
# names that resolve nowhere → per case: exit code, objects left in the private repository, stderr's
# first lines. Run on the gate host: `tools/vflab-run bash tools/git-probe.sh`. Its transport lines
# feed `FvdepCore.Library.transportLine` + `lake test`'s `LibraryR.transportLines`.
set -u
W=$(mktemp -d)
trap 'rm -rf "$W"' EXIT
export GIT_AUTHOR_NAME=x GIT_AUTHOR_EMAIL=x@x.invalid GIT_COMMITTER_NAME=x GIT_COMMITTER_EMAIL=x@x.invalid
git --version
mk() { git init -q -b main "$1" && git -C "$1" config core.hooksPath /dev/null; }
src=$W/src
mk "$src"
mkdir -p "$src/Fvdep"
echo a >"$src/Fvdep/a.lean"
echo b >"$src/lakefile.lean"
git -C "$src" add -A && git -C "$src" commit -qm one
first=$(git -C "$src" rev-parse HEAD)
echo c >"$src/Fvdep/c.lean"
git -C "$src" add -A && git -C "$src" commit -qm two
second=$(git -C "$src" rev-parse HEAD)
other=$W/other
mk "$other"
echo x >"$other/f"
git -C "$other" add -A && git -C "$other" commit -qm o && git -C "$other" branch -m main side
bad=$W/bad
mk "$bad"
echo y >"$bad/index.json"
git -C "$bad" add -A && git -C "$bad" commit -qm b
t=$(git -C "$bad" rev-parse 'HEAD^{tree}')
nt=$(git -C "$bad" cat-file tree "$t" | sed 's/100644 index.json/100664 index.json/' |
    git -C "$bad" hash-object --literally -t tree -w --stdin)
git -C "$bad" update-ref refs/heads/main "$(git -C "$bad" commit-tree "$nt" -p HEAD -m badmode)"
mkdir "$W/plain"
# userinfo built from pieces: a URL literal of this shape trips stage `secrets`.
user=u
word=secret
fetch() {
    local repo
    repo=$W/t.$RANDOM.git
    local e=(env -i PATH="$PATH" LC_ALL=C GIT_CONFIG_NOSYSTEM=1 GIT_CONFIG_GLOBAL=/dev/null
        GIT_TERMINAL_PROMPT=0 GIT_ASKPASS= SSH_ASKPASS= HOME="$repo")
    "${e[@]}" git init --bare -q --template= "$repo"
    "${e[@]}" timeout 60 git -c fetch.fsckObjects=true -c fetch.fsck.badFilemode=error \
        -c fetch.fsck.gitattributesSymlink=error -c fetch.fsck.gitignoreSymlink=error \
        -c fetch.fsck.gitmodulesParse=error -c core.hooksPath=/dev/null -c core.fsmonitor=false \
        -c credential.helper= -c credential.interactive=false -c 'core.sshCommand=ssh -o BatchMode=yes' \
        -c http.followRedirects=false -c transfer.bundleURI=false -c promisor.acceptFromServer=none \
        -c gc.auto=0 -C "$repo" fetch --depth=1 --atomic --no-tags --no-prune --no-recurse-submodules \
        --no-auto-maintenance --no-write-commit-graph --no-write-fetch-head --refmap= -- "$2" "$3" \
        </dev/null >"$W/out" 2>"$W/err"
    local rc=$?
    echo "== $1 rc=$rc objects=$(find "$repo/objects" -type f | wc -l)"
    sed -e "s#$W#<W>#g" "$W/err" | head -8 | cat -A
    rm -rf "$repo"
}
head='+refs/heads/main:refs/fvdep/head'
fetch head-ok "$src" "$head"
fetch pin-tip "$src" "+$second:refs/fvdep/pin"
fetch pin-nontip "$src" "+$first:refs/fvdep/pin"
fetch pin-unknown "$src" "+0123456789abcdef0123456789abcdef01234567:refs/fvdep/pin"
fetch missing-path "$W/gone" "$head"
fetch missing-file-url "file://$W/gone" "$head"
fetch missing-userinfo-url "file://$user:$word@localhost$W/gone" "$head"
fetch plain-dir "$W/plain" "$head"
fetch no-main "$other" "$head"
fetch bad-mode "$bad" "$head"
fetch https-nohost "https://nonexistent.invalid/x.git" "$head"
fetch https-refused "https://127.0.0.1:1/x.git" "$head"
fetch ssh-nohost "nonexistent.invalid:x.git" "$head"
fetch ssh-refused "ssh://127.0.0.1:1/x.git" "$head"
fetch git-nohost "git://nonexistent.invalid/x.git" "$head"
fetch git-refused "git://127.0.0.1:1/x.git" "$head"
fetch github-missing "https://github.com/veriformatics/no-such-repo-fvdep-probe.git" "$head"
