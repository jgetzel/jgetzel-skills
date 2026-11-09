{
  description = "LuaJIT with the rocks the swarm CLI needs (keep in sync with ROCKS in install.sh), plus the sqlite3 CLI";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  outputs = { self, nixpkgs }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];
      forAll = f: nixpkgs.lib.genAttrs systems (s: f nixpkgs.legacyPackages.${s});
      lj = pkgs: pkgs.luajit.withPackages (p: with p; [ lsqlite3 lua-cjson luaposix lrexlib-pcre2 luafilesystem argparse luautf8 ]);
      # default adds the sqlite3 CLI, for reading a swarm's board by hand; luajit is the interpreter alone.
      env = pkgs: pkgs.symlinkJoin { name = "jgetzel-skills-env"; paths = [ (lj pkgs) pkgs.sqlite ]; };
    in {
      packages = forAll (pkgs: { default = env pkgs; luajit = lj pkgs; });
      devShells = forAll (pkgs: { default = pkgs.mkShell { packages = [ (env pkgs) ]; }; });
    };
}
