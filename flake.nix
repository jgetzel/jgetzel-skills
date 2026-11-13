{
  description = "swarm-lean, the swarm CLI (swarm/lean); LuaJIT with the rocks its Lua fallback needs (keep in sync with ROCKS in install.sh), plus the sqlite3 CLI";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  outputs = { self, nixpkgs }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];
      forAll = f: nixpkgs.lib.genAttrs systems (s: f nixpkgs.legacyPackages.${s});
      lj = pkgs: pkgs.luajit.withPackages (p: with p; [ lsqlite3 lua-cjson luaposix lrexlib-pcre2 luafilesystem argparse luautf8 ]);
      # default adds the sqlite3 CLI, for reading a swarm's board by hand; luajit is the interpreter alone.
      env = pkgs: pkgs.symlinkJoin { name = "jgetzel-skills-env"; paths = [ (lj pkgs) pkgs.sqlite ]; };
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
          cd swarm/lean && lake build swarm-lean
        '';
        installPhase = "install -Dm755 .lake/build/bin/swarm-lean $out/bin/swarm-lean";
        meta.mainProgram = "swarm-lean";
      };
    in {
      # sqlite: the library and header swarm/lean links (its lakefile builds this output)
      packages = forAll (pkgs: { default = env pkgs; luajit = lj pkgs; sqlite = sqlite pkgs; swarm-lean = swarm-lean pkgs; });
      devShells = forAll (pkgs: { default = pkgs.mkShell { packages = [ (env pkgs) ]; }; });
    };
}
