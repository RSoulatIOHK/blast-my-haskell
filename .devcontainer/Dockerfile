FROM mcr.microsoft.com/devcontainers/base:ubuntu-22.04

# System build deps for the GHC/Lean toolchains and the project.
RUN apt-get update && export DEBIAN_FRONTEND=noninteractive \
 && apt-get install -y --no-install-recommends \
      curl git build-essential libgmp-dev libtinfo-dev libncurses-dev \
      python3 ca-certificates \
 && apt-get clean && rm -rf /var/lib/apt/lists/*

USER vscode
ENV PATH=/home/vscode/.ghcup/bin:/home/vscode/.elan/bin:$PATH

# GHC 9.2.7 + cabal via ghcup (non-interactive).
RUN export BOOTSTRAP_HASKELL_NONINTERACTIVE=1 \
      BOOTSTRAP_HASKELL_GHC_VERSION=9.2.7 \
      BOOTSTRAP_HASKELL_INSTALL_NO_STACK=1 \
 && curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | sh \
 && ghcup install cabal --set

# Lean via elan; the v4.24.0 toolchain (from lean-toolchain) is fetched on first lake use.
RUN curl --proto '=https' --tlsv1.2 -sSf \
      https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
      | sh -s -- -y --default-toolchain none
