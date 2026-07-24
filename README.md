# WaterproofGenre

WaterproofGenre provides the infrastructure for mixed-math-explanation formats for Lean-based Waterproof functionality. It uses Verso, which under the hood hooks into the LSP to compile the correct part of the document.

## Tests

The project has two test executables, run in CI by
[`.github/workflows/lean_action_ci.yml`](.github/workflows/lean_action_ci.yml).
They live in separate Lake environments, so they are run with different flags.

### Demo test (`test-demo`)

Elaborates [`WaterproofGenre/Demo.lean`](WaterproofGenre/Demo.lean) and checks
the resulting declarations (goals, `#eval` output, and `sorry` warnings). It runs
in the default environment:

```sh
lake exe test-demo
```

### Verbose test (`test-verbose`)

Elaborates [`WaterproofGenre/Verbose.lean`](WaterproofGenre/Verbose.lean), which
combines the document genre with [Verbose Lean](https://github.com/PatrickMassot/verbose-lean4)
tactics. Verbose Lean is a `dev`-only dependency (see the `meta if` blocks in
[`lakefile.lean`](lakefile.lean)), so this test **requires the `dev`
environment**. On a fresh checkout you must resolve the dev dependencies once
before building:

```sh
lake -Kenv=dev update                              # fetch verbose-lean4 (and its Mathlib dependency)
lake -Kenv=dev -d .lake/packages/mathlib exe cache get  # fetch the Mathlib build cache (optional but much faster)
lake -Kenv=dev exe test-verbose
```

> **Note:** `cache` is Mathlib's own executable, so it must be run from the
> Mathlib package directory (`-d .lake/packages/mathlib`). Running
> `lake -Kenv=dev exe cache get` from the root fails with
> `unknown executable cache`.

> **Note:** `lake -Kenv=dev update` rewrites `lake-manifest.json` to the
> dev dependency set. Do not commit that change — the committed manifest is the
> non-dev one, and CI regenerates the dev manifest itself.

## Stale environment issues

The `dev` and non-`dev` environments require mutually exclusive dependencies
(`verbose-lean4` + Mathlib vs. `proofwidgets`). Switching between them — or
reverting `lake-manifest.json` after a `-Kenv=dev update` — can leave Lake's
cached workspace configuration out of sync with the manifest.

**Symptoms:**

- `error: dependency '«verbose-lean4»' not in manifest` when running a non-dev
  command (e.g. `lake exe test-demo`) after having built in `dev` mode.
- `unknown module prefix 'Verbose'` / `No directory 'Verbose'` when the dev
  dependency hasn't been fetched, or when a stale non-dev config is being reused.
- `lake -Kenv=dev update` fetches only the non-dev dependencies (`proofwidgets`
  etc., but **not** `verbose-lean4`/Mathlib), and a later
  `-d .lake/packages/mathlib` command fails with
  `workspace directory not found: .lake/packages/mathlib`. This happens when a
  non-dev `lake` command ran first and cached a non-dev `lakefile.olean`: Lake
  reuses it and silently skips the dev `require`. **`lake -Kenv=dev update` must
  be the first `lake` invocation** (this is why the CI `verbose` job configures
  `lean-action` not to resolve dependencies).
  - In CI this same symptom is caused by a restored **GitHub Actions `.lake`
    cache** containing a non-dev resolution. `lean-action`'s built-in cache is
    keyed on the (non-dev) manifest and cannot be namespaced, so the `verbose`
    job disables it (`use-github-cache: false`) and instead caches `.lake` under
    a separate `dev-`prefixed key via an explicit `actions/cache` step. The
    `demo` and `verbose` jobs therefore never share a cache. If an old poisoned
    cache predates this setup, delete it once from the repo's Actions caches so
    the new keys take over.

**Fix:** clear Lake's cached per-configuration state and let it re-resolve
against the current `lake-manifest.json`:

```sh
rm -rf .lake/config
git checkout lake-manifest.json   # only if a -Kenv=dev update left it modified
```

Then re-run the relevant test command above. This does not delete built
artifacts under `.lake/build` or fetched packages under `.lake/packages`, so it
is cheap.

**When you need this:** after switching between `dev` and non-`dev` builds, or
after running `lake -Kenv=dev update` and reverting the manifest. A clean `git
clone` never needs it — that is what CI does, which is why CI runs the two tests
in separate jobs.
