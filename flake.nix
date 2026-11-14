{
  description = "bend-frp: functional reactive programming in Bend, after Conal Elliott";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  # Bend 2.0.39, the one horas (bend-frp's other user) and ana build with
  inputs.bend2 = {
    url = "github:bendlang/bend/0ba4e5ec0d3c9e93d653883b9184488468040001";
    inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs =
    { self, nixpkgs, bend2 }:
    let
      systems = [
        "x86_64-linux"
        "aarch64-linux"
      ];
      each = f: nixpkgs.lib.genAttrs systems (system: f system nixpkgs.legacyPackages.${system});
      # What a build sees: the library, its proofs, its pages
      src = nixpkgs.lib.fileset.toSource {
        root = ./.;
        fileset = nixpkgs.lib.fileset.unions [
          ./Frp.bend
          ./LAWS.bend
          ./PROOF.bend
          ./Web.bend
          ./runtime.js
          ./probe
          ./examples
        ];
      };
      # Lean v4.34.0, the release `bend --verdict` builds its kernel with
      leanFor = pkgs: pkgs.callPackage ./nix/lean4.nix { };
      # BendTT, the kernel `bend --verdict` checks a book with: the
      # bendtt.lean of the pinned Bend, built as bend2/safe.ts kernel_bin
      # does (lean -c, then leanc -O3 -DNDEBUG), once, in the store.  bend
      # takes it from $BENDTT and builds nothing in ~/.bend.  (ana's, as is.)
      bendttFor =
        pkgs:
        pkgs.runCommandCC "bendtt" { nativeBuildInputs = [ (leanFor pkgs) ]; } ''
          export HOME=$TMPDIR LEAN_CC=${pkgs.stdenv.cc}/bin/cc
          cp ${bend2.packages.${pkgs.stdenv.hostPlatform.system}.default}/libexec/bend/bend2/bendtt.lean .
          lean -c bendtt.c bendtt.lean
          leanc -O3 -DNDEBUG bendtt.c -o bendtt
          install -Dm755 bendtt $out/bin/bendtt
        '';
      # the pinned bend, telemetry off, with the kernel: `bend FILE --verdict` works
      bendFor =
        pkgs:
        pkgs.writeShellScriptBin "bend" ''
          export BEND_NO_TELEMETRY=1
          export BENDTT="''${BENDTT:-${bendttFor pkgs}/bin/bendtt}"
          exec ${bend2.packages.${pkgs.stdenv.hostPlatform.system}.default}/bin/bend "$@"
        '';
      # run `script` in a writable copy of the source, with bend on PATH
      inSource =
        pkgs: name: script:
        pkgs.runCommand "bend-frp-${name}" { nativeBuildInputs = [ (bendFor pkgs) ]; } ''
          export HOME=$TMPDIR
          cp -r ${src} w
          chmod -R u+w w
          cd w
          ${script}
        '';
      # a page, bundled: the page and its JavaScript, a plain web directory
      # (what Capacitor takes as its webDir)
      pageFor =
        pkgs: name: dir:
        inSource pkgs name ''
          bend ${dir}/page.html -o $out
        '';
    in
    {
      packages = each (
        system: pkgs: {
          default = bendFor pkgs;
          bend = bendFor pkgs;
          lean4 = leanFor pkgs;
          bendtt = bendttFor pkgs;
          todo = pageFor pkgs "todo" "examples/todo";
          probe = pageFor pkgs "probe" "probe";
        }
      );

      checks = each (
        system: pkgs: {
          # the laws hold: Bend's checker, then BendTT's kernel
          proofs = inSource pkgs "proofs" ''
            bend PROOF.bend --verdict 2>&1 | tee $out
            grep -q 'ALL PROOFS CHECK' $out
          '';
          # every module and example checks
          modules = inSource pkgs "modules" ''
            for f in Frp.bend Web.bend probe/Probe.bend probe/Probe2.bend probe/Snap.bend probe/Switch.bend examples/todo/App.bend; do
              echo "== $f"
              bend $f --check-only 2>&1 | tee log
              grep -q 'ALL PROOFS CHECK' log
              cat log >> $out
            done
          '';
          # snap runs as its meaning says, on a sample input
          snap = inSource pkgs "snap" ''
            bend probe/Snap.bend 2>&1 | tee $out
            grep -qxF "[[10, 25, 37], [10, 25, 37], [1]]" $out
          '';
          # switch runs as its meaning says, on a sample input
          switch = inSource pkgs "switch" ''
            bend probe/Switch.bend 2>&1 | tee $out
            grep -qxF "[[1, 2, 10, 19, 1, 2], [1, 2, 10, 19, 1, 2]]" $out
          '';
          # the laws catch each mistake in probe/mutants/: PROOF.bend fails on every one
          mutants = inSource pkgs "mutants" ''
            bash probe/mutants.sh > $out 2>&1 || { cat $out; exit 1; }
            cat $out
          '';
          inherit (self.packages.${system}) todo probe;
        }
      );

      devShells = each (
        system: pkgs: {
          default = pkgs.mkShell {
            packages = [
              (bendFor pkgs)
              (leanFor pkgs)
              pkgs.nodejs
            ];
          };
        }
      );
    };
}
