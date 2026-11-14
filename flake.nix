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
          ./Dyn.bend
          ./Ops.bend
          ./LAWS.bend
          ./PROOF.bend
          ./proof
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
            for f in Frp.bend Dyn.bend Ops.bend Web.bend probe/Probe.bend probe/Probe2.bend probe/Snap.bend probe/Switch.bend probe/Time.bend probe/Dyn.bend probe/Ops.bend examples/todo/App.bend; do
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
          # Time's arithmetic and conversions, run, against values worked out by hand
          time = inSource pkgs "time" ''
            bend probe/Time.bend 2>&1 | tee $out
            grep -qxF "1+2147483648 0+4290672328 8+536870912 2+1073741824 2+4294967196 1+1007169830 2.5 2+3221225472 0+0 0+1073741824 0+4294967294" $out
          '';
          # zip and join run as their meanings say, on sample Dyns
          dyn = inSource pkgs "dyn" ''
            bend probe/Dyn.bend 2>&1 | tee $out
            grep -qxF "[[0, 100, 102, 304, 304, 504, 504, 504], [0, 100, 102, 304, 304, 504, 504, 504], [0, 1, 101, 103, 103, 200, 200, 207], [0, 1, 101, 103, 103, 200, 200, 207]]" $out
          '';
          # Ops.bend's combinators run as their meanings say, on sample events
          ops = inSource pkgs "ops" ''
            bend probe/Ops.bend 2>&1 | tee $out
            grep -qxF '[" 2:1 4:22 6:30 8:4", " 2:1 4:2 6:30 8:4", " 2:1 8:4", " 2:1 4:2", " 2:1 4:2 | 8:4", " 2:1 6:3", " 4:1 6:2 10:4", " 7:2 14:4 21:5", " 2:1 10:3 18:5"]' $out
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
