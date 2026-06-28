#!/usr/bin/env bash
# Setup script for verse-rocq Rocq development environment
# Run from the project root in WSL: bash scripts/setup-wsl.sh

set -euo pipefail

echo "=== [1/4] System packages ==="
sudo apt-get update -q
sudo apt-get install -y \
    opam ocaml ocaml-nox \
    m4 bubblewrap make pkg-config \
    libgmp-dev git curl

echo "=== [2/4] opam init ==="
if [ ! -d "$HOME/.opam" ]; then
    # --bare: don't create a switch yet
    opam init --bare --no-setup -y
fi
# Use system OCaml (4.14 from Ubuntu 24.04) — avoids recompiling OCaml
if ! opam switch list | grep -q "verse-rocq"; then
    opam switch create verse-rocq ocaml-system
fi
eval $(opam env --switch=verse-rocq)

echo "=== [3/4] Rocq (Coq 8.20) ==="
# Coq 8.20 = last stable before Rocq rename; coq-metalib supports it
opam install -y "coq>=8.19" "coq<9.0"

echo "=== [4/4] Metalib (Locally Nameless infrastructure) ==="
opam install -y coq-metalib

echo ""
coqc --version
echo ""
echo "Add to ~/.bashrc:"
echo '  eval $(opam env --switch=verse-rocq)'
