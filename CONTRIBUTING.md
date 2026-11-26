# Contributing to tenet-zfc

Thanks for helping. This file covers building, testing, setting up the checkers, and how changes land. The design is in [docs/spec.md](docs/spec.md), and the state of the model in [docs/milestone3.md](docs/milestone3.md).

## The one rule

**The translator is not trusted; the checkers are.** A change is done when its output passes all three checks:

1. **metamath-exe**, with no `?Error` line;
2. **mmverify.py**, with exit status 0;
3. **mmj2's `definitionCheck`** (`scripts/check-definitions`), for every definition the output introduces.

An output adds definitions and `$p` theorems to `set.mm`, never axioms.

## Build

You need the [.NET SDK](https://dotnet.microsoft.com) 10 (`global.json` rolls forward). Every project targets both .NET 8 and .NET 10, and CI builds both, with warnings as errors.

```bash
dotnet build -c Release
```

If only .NET 10 is installed, `dotnet build` still builds both targets; to run the net8.0 build you need the .NET 8 runtime too.

## Test

```bash
dotnet test -c Release
```

Without the checkers, the tests that need `set.mm` or a verifier skip themselves. To run them, set these variables (CI does, in the `emit-and-verify` job):

| Variable | Value |
|---|---|
| `TENET_ZFC_SETMM` | the directory holding `set.mm` |
| `TENET_ZFC_METAMATH` | the metamath-exe binary |
| `TENET_ZFC_MMVERIFY` | `mmverify.py` |
| `TENET_ZFC_JAVA` | Java 11 |
| `TENET_ZFC_MMJ2` | a directory holding `mmj2.jar` and `macros/` |

```bash
dotnet test tests/TenetZfc.Tests -c Release -f net10.0
```

`tenet-zfc run` and `tenet-zfc verify` read the same variables, plus `TENET_ZFC_PYTHON`, `TENET_ZFC_LEANOUT`, `TENET_ZFC_LEAN` and `TENET_ZFC_TENET`.

## Set up the checkers

Use the commits CI pins (the `env:` of the `emit-and-verify` job in [`.github/workflows/ci.yml`](.github/workflows/ci.yml)): outputs are written against an exact `set.mm`.

```bash
mkdir -p mm/setmm mm/mmj2/macros && cd mm
SETMM_COMMIT=6315535f37e5e58d14ece8c34ddb204926446264
curl -fsSL -o setmm/set.mm "https://raw.githubusercontent.com/metamath/set.mm/$SETMM_COMMIT/set.mm"

# metamath-exe (C)
git clone -q https://github.com/metamath/metamath-exe && git -C metamath-exe checkout -q 580b4bd5ae6f2a0d746398b0033cddccba1b418b
cc -O2 -w -o metamath metamath-exe/src/*.c

# mmverify.py (Python 3)
git clone -q https://github.com/david-a-wheeler/mmverify.py mmverify && git -C mmverify checkout -q 63a2aa3815cd5bf67892dbfc7f2048cbb177524c

# mmj2, for definitionCheck; it needs Java 11 (with Nashorn), e.g. Zulu 11
raw=https://raw.githubusercontent.com/digama0/mmj2/c8dd05548139c7003220caedde65a7abe44a00bf/mmj2jar
curl -fsSL -o mmj2/mmj2.jar "$raw/mmj2.jar"
for m in definitionCheck init; do curl -fsSL -o "mmj2/macros/$m.js" "$raw/macros/$m.js"; done
```

Then check an output (it must sit beside `set.mm`, which it includes by name):

```bash
cd mm/setmm                                          # out.mm is here, beside set.mm
../metamath "read out.mm" "verify proof *" exit      # fail on any ?Error line
python3 -I ../mmverify/mmverify.py out.mm
path/to/tenet-zfc/scripts/check-definitions java ../mmj2 out.mm
```

or all three at once, with `tenet-zfc verify out.mm`.

For the whole pipeline (`tenet-zfc run`) you also need:

- **Lean** through [elan](https://github.com/leanprover/elan). The fixtures use Lean 4.36.0.
- **[leanout](https://github.com/keithadler/leanout)**, built with `lake build` under the same toolchain as the code you export. `run` uses elan's `lean` at leanout's toolchain unless you pass `--lean`.
- **[Tenet](https://github.com/keithadler/tenet)** (optional), from its `main` branch, which has `tenet check --trace`. With it, theorems the milestone 2 translator covers are proved from their traces in seconds. Without it, every theorem goes through the model, which can take many minutes.

## Fixtures

`tests/fixtures/` holds Lean exports and Tenet traces; [its README](tests/fixtures/README.md) says how each was made. Exports come from Lean 4.36.0 through leanout. When you add one, record the command, and add a CI step that translates it and checks the output with all three checkers.

## Distinct-variable traps

Both verifiers have caught `$d` violations the translator's own checks missed. The usual fixes are renaming bound variables (`cbvmptv`, `cbvmpov`, `cbviunv`) and proving under only the hypotheses needed. See [docs/milestone3.md](docs/milestone3.md).

## Pull requests

- Work on a branch and open a pull request against `main`. CI must pass on Linux, macOS and Windows.
- Keep changes to `src/TenetZfc/Model.cs` small and in new methods where you can: several people work on the model at once.
- Update the docs and counts that your change moves (`README.md`, `docs/milestone3.md`), and add a line under the unreleased version in `CHANGELOG.md`.

## Releasing

Maintainers only.

1. Make sure CI on `main` is green.
2. In `CHANGELOG.md`, give the version's heading its date: `## [0.1.0] - 2026-12-01`. The release notes are that section.
3. Tag and push: `git tag v0.1.0 && git push origin v0.1.0`.

The [release workflow](.github/workflows/release.yml) runs all of CI again, builds the dotnet tool package and the linux-x64, osx-arm64 and win-x64 binaries with the version from the tag, and creates the GitHub Release with them, the verified fixture outputs, the worked example's run, and `SHA256SUMS`. A tag with a suffix (`v0.2.0-rc1`) makes a pre-release. Between releases, `Directory.Build.props` carries the next version with the suffix `dev`.

## License

By contributing, you agree that your contributions are licensed under the Apache License 2.0, like the rest of the project.
