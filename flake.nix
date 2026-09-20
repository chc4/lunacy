{
  description = "lunacy — Lua 5.1 JIT; devshell for `just run <benchmark>`";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    fenix = {
      url = "github:nix-community/fenix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, nixpkgs, flake-utils, fenix }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };

        # Cargo.toml pins `cargo-features = ["panic-immediate-abort",
        # "profile-rustflags"]` and `edition = "2024"`, all of which require a
        # nightly toolchain. rust-src is included so the `unsafe`/`sonic`
        # profiles that build-std also work out of the box.
        rustToolchain = fenix.packages.${system}.complete.withComponents [
          "cargo"
          "rustc"
          "rust-src"
          "clippy"
          "rustfmt"
          "rust-std"
        ];

        # The Justfile invokes `lua5.1` / `luac5.1`, but nixpkgs' lua5_1
        # ships unversioned `lua` / `luac`. Provide the versioned aliases.
        luaVersioned = pkgs.runCommand "lua5.1-versioned" { } ''
          mkdir -p $out/bin
          ln -s ${pkgs.lua5_1}/bin/lua  $out/bin/lua5.1
          ln -s ${pkgs.lua5_1}/bin/luac $out/bin/luac5.1
        '';
      in
      {
        devShells.default = pkgs.mkShell {
          packages = [
            rustToolchain
            pkgs.just         # `just` task runner
            pkgs.lua5_1       # Lua 5.1 (unversioned `lua`/`luac`)
            luaVersioned      # `lua5.1` / `luac5.1` aliases for the Justfile
            pkgs.hyperfine    # used by the `just hyperfine*` recipes
          ];

          # mimalloc (and other -sys crates) need a C toolchain to build.
          nativeBuildInputs = [
            pkgs.stdenv.cc
            pkgs.pkg-config
          ];

          RUST_SRC_PATH = "${rustToolchain}/lib/rustlib/src/rust/library";

          shellHook = ''
            echo "lunacy devshell — try: just run nbody"
          '';
        };
      });
}
