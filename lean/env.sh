# Source this file to use the project-local Lean toolchain.
LEAN_PROJECT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]:-$0}")" && pwd)"
export ELAN_HOME="$LEAN_PROJECT_DIR/.elan"
export PATH="$ELAN_HOME/bin:$PATH"
export XDG_CACHE_HOME="$LEAN_PROJECT_DIR/.cache"
export GIT_TEMPLATE_DIR="${TMPDIR:-/tmp}/empty-git-template"; mkdir -p "$GIT_TEMPLATE_DIR"
