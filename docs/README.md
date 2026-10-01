# Generated API reference

[`API.md`](API.md) documents all 92 public native declarations in thirteen
mathematical leaves, the aggregate module and six private test/example modules.
It retains the native displayed signatures, docstrings and module explanations.
Source links point into this checkout. No intermediate HTML, JavaScript, fonts,
dependency website, source PDF or external mathematical prose is distributed.

## Reproduction and binding

[`api-manifest.json`](api-manifest.json) identifies the exact analyzed revision,
all twenty Lean inputs and three configuration/pin inputs, twenty native records,
the public inventory and output hash. The final artifact's review binds these
inputs and generated files to its own commit and tree. Source or pin changes
require assessing affected build, API and documentation bindings, correcting
affected documentation or the manifest as needed, and renewing required affected
checks; unaffected evidence stays reusable. Native API regeneration is an optional
way to update affected documentation, not an automatic release prerequisite.
Documentation-only assembly does not change the mathematical inputs.

When the analyzed development commit exists locally, every input must match its
Git object. In an isolated parentless release where that object is absent, fresh
generation must instead reproduce the release's committed manifest byte-for-byte,
and every input must match the release commit. A present wrong object, changed
input, altered native record or uncommitted manifest is refused. This is a data
binding check, not authentication of the native run or proof correctness; the
development commit need not be obtainable from the public release history.

Build native doc-gen4 at `97d4ecdfc8e09e7f511724c25e303d448de6a3db` using its
committed five-dependency manifest and Lean `v4.34.0-rc2` in a separate checkout:
`lake build doc-gen4`. It is a core-only tool; do not change this library's pins.
Fetch this library's matching mathlib cache, then build all twenty modules using
the root README. Start with fresh analysis/render directories. Run `single` for
**each** module listed in `scripts/generate_api.py`, changing the module and source
path together. Use the full analyzed revision from the manifest, not a branch.

```sh
mkdir /tmp/quadratic-analysis /tmp/quadratic-render
lake env /path/to/doc-gen4 single --build /tmp/quadratic-analysis QuadraticAlgebras.AdjoinRoot api.db https://github.com/FormalFrontier/quadratic-algebras/blob/FULL_SOURCE_COMMIT/QuadraticAlgebras/AdjoinRoot.lean
lake env /path/to/doc-gen4 bibPrepass --build /tmp/quadratic-render --none
lake env /path/to/doc-gen4 fromDb --build /tmp/quadratic-render --manifest /tmp/quadratic-render/manifest.json /tmp/quadratic-analysis/api.db
python3 -B scripts/generate_api.py --native-data /tmp/quadratic-render/doc-data --source-revision FULL_SOURCE_COMMIT
python3 -B scripts/generate_api.py --native-data /tmp/quadratic-render/doc-data --source-revision FULL_SOURCE_COMMIT --check
python3 -B scripts/test_generate_api.py
```

The adapter accepts exactly the inspected names, native kinds, origins and source
ranges. Native metadata groups abbreviations with definitions; the displayed
inventory is 61 theorems, 19 noncomputable definitions, four other definitions,
three abbreviations and five instances. All header text tokens are retained,
normalizing whitespace only. Native pretty-printing may omit literal type
annotations; names, docstrings and linked sources supply their context. These
are display signatures, not standalone modules or proofs. Module documentation
is copied from the exact single, non-nested module comment in each source.

Data-only tests exercise missing/duplicate/unexpected declarations, altered kinds,
lost modifiers, malformed markup, ranges, source drift and parentless manifest
binding. They do not certify a native execution. The adapter is intentionally
library-specific, not a generic Lean parser, proof checker or release certificate.

## Provenance

Atlas adapted this renderer and its tests through the Formal Frontier Toric
Ideals, Minimal Primes and Integral Closure assemblies from Anchor's original
Ideal Completion recipe. This is documentation-tool lineage, not authorship of
this library's mathematical proofs. Collective credit and Apache-2.0 terms are
preserved. Generated mathematical text comes from this library's signatures
and original docstrings. Lean, mathlib and doc-gen4 remain separately credited
dependencies/tools; their code and prose are not bundled.
