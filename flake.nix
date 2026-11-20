{
  description = "swarm-lean, the swarm CLI (swarm/lean), with swarm-report, harness-retro and herdr-mods, the claim tool (claim/), plus the sqlite3 CLI";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  outputs = { self, nixpkgs }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];
      forAll = f: nixpkgs.lib.genAttrs systems (s: f nixpkgs.legacyPackages.${s});
      # default adds the sqlite3 CLI, for reading a swarm's board by hand.
      env = pkgs: pkgs.symlinkJoin { name = "jgetzel-skills-env"; paths = [ (swarm-lean pkgs) (claim pkgs) pkgs.sqlite ]; };
      sqlite = pkgs: pkgs.symlinkJoin { name = "sqlite-lib"; paths = [ pkgs.sqlite.out pkgs.sqlite.dev ]; };
      lib = nixpkgs.lib;
      # nixpkgs' Lean, refused at eval unless every lean-toolchain here names its version
      lean4 = pkgs: let
        ok = f: lib.assertMsg (lib.trim (builtins.readFile f) == "leanprover/lean4:v${pkgs.lean4.version}")
          "${toString f} is not nixpkgs' lean4 ${pkgs.lean4.version}: nix flake update, or build with elan";
      in assert ok ./swarm/lean/lean-toolchain && ok ./claim/lean-toolchain; pkgs.lean4;
      # only these dirs, so an edit elsewhere (a SKILL.md, a mod) is not a rebuild
      srcOf = dirs: lib.fileset.toSource { root = ./.; fileset = lib.fileset.unions dirs; };
      # the swarm CLI in Lean (swarm/lean), built by lake with nixpkgs' Lean
      swarm-lean = pkgs: pkgs.stdenv.mkDerivation {
        pname = "swarm-lean"; version = "0"; src = srcOf [ ./swarm/lean ./swarm/model ./claim ];
        nativeBuildInputs = [ (lean4 pkgs) ];
        SWARM_SQLITE = sqlite pkgs;
        buildPhase = ''
          export HOME=$TMPDIR
          cd swarm/lean && lake build swarm-lean swarm-report harness-retro herdr-mods
        '';
        installPhase = "install -Dm755 -t $out/bin .lake/build/bin/swarm-lean .lake/build/bin/swarm-report .lake/build/bin/harness-retro .lake/build/bin/herdr-mods";
        meta.mainProgram = "swarm-lean";
      };
      # claim (claim/), the compute claims tool: Lean core only (no sqlite), its own Lake package that swarm-lean also builds from
      claim = pkgs: pkgs.stdenv.mkDerivation {
        pname = "claim"; version = "0"; src = srcOf [ ./claim ];
        nativeBuildInputs = [ (lean4 pkgs) ];
        buildPhase = ''
          export HOME=$TMPDIR
          cd claim && lake build claim
        '';
        installPhase = "install -Dm755 -t $out/bin .lake/build/bin/claim";
        meta.mainProgram = "claim";
      };
    in {
      # sqlite: the library and header swarm/lean links (its lakefile builds this output)
      packages = forAll (pkgs: { default = env pkgs; claim = claim pkgs; sqlite = sqlite pkgs; swarm-lean = swarm-lean pkgs; });
      # lean: the Lean and C toolchain the build.sh scripts run lake in without elan, so .lake builds incrementally
      devShells = forAll (pkgs: { default = pkgs.mkShell { packages = [ (env pkgs) ]; }; lean = pkgs.mkShell { packages = [ (lean4 pkgs) ]; }; });
    };
}
