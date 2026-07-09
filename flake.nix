{
  description = "rIC3 development shell";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs = { nixpkgs, ... }:
    let
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];

      forAllSystems = nixpkgs.lib.genAttrs systems;
    in
    {
      devShells = forAllSystems (system:
        let
          pkgs = import nixpkgs { inherit system; };
        in
        {
          default = pkgs.mkShell {
            packages = with pkgs; [
              rustc
              cargo
              rustfmt
              clippy
              cmake
              meson
              ninja
              pkg-config
              clang
              bitwuzla
              gmp
              mpfr
              zlib
              git
            ] ++ pkgs.lib.optionals pkgs.stdenv.isLinux [
              yosys
            ] ++ pkgs.lib.optionals pkgs.stdenv.isDarwin [
              pkgs.libiconv
            ];

            shellHook = ''
              if [ ! -f deps/aig-rs/Cargo.toml ]; then
                echo "rIC3 submodules are not initialized."
                echo "Run: git submodule update --init --recursive"
              fi
            '';
          };
        });
    };
}
