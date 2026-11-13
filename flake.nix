{
  description = "swarm-lean, the swarm CLI (swarm/lean), with swarm-report, harness-retro and herdr-mods, plus the sqlite3 CLI";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  outputs = { self, nixpkgs }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];
      forAll = f: nixpkgs.lib.genAttrs systems (s: f nixpkgs.legacyPackages.${s});
      # default adds the sqlite3 CLI, for reading a swarm's board by hand.
      env = pkgs: pkgs.symlinkJoin { name = "jgetzel-skills-env"; paths = [ (swarm-lean pkgs) pkgs.sqlite ]; };
      sqlite = pkgs: pkgs.symlinkJoin { name = "sqlite-lib"; paths = [ pkgs.sqlite.out pkgs.sqlite.dev ]; };
      # the swarm CLI in Lean (swarm/lean), built by lake with nixpkgs' Lean; its lean-toolchain must name the same version
      swarm-lean = pkgs: pkgs.stdenv.mkDerivation {
        pname = "swarm-lean"; version = "0"; src = self;
        nativeBuildInputs = [ pkgs.lean4 ];
        SWARM_SQLITE = sqlite pkgs;
        buildPhase = ''
          export HOME=$TMPDIR
          grep -qx "leanprover/lean4:v${pkgs.lean4.version}" swarm/lean/lean-toolchain ||
            { echo "swarm/lean/lean-toolchain is not nixpkgs' lean4 ${pkgs.lean4.version}: nix flake update, or build with elan" >&2; exit 1; }
          cd swarm/lean && lake build swarm-lean swarm-report harness-retro herdr-mods
        '';
        installPhase = "install -Dm755 -t $out/bin .lake/build/bin/swarm-lean .lake/build/bin/swarm-report .lake/build/bin/harness-retro .lake/build/bin/herdr-mods";
        meta.mainProgram = "swarm-lean";
      };
    in {
      # sqlite: the library and header swarm/lean links (its lakefile builds this output)
      # luajit: lua-lean's reference interpreter (lua-lean/lua-lean, its CI), not in default
      packages = forAll (pkgs: { default = env pkgs; luajit = pkgs.luajit; sqlite = sqlite pkgs; swarm-lean = swarm-lean pkgs; });
      devShells = forAll (pkgs: { default = pkgs.mkShell { packages = [ (env pkgs) ]; }; });
    };
}
