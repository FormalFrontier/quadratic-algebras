# API reference and source binding

[`API.md`](API.md) retains 92 historical native signatures from thirteen
mathematical leaves and adds a separately identified, source-derived guide to
seven public chosen-coordinate declarations in a fourteenth production leaf.
The current library has that aggregate root and seven test/example modules:
six older modules are private-only, while the new coordinate test leaf exposes
only `QuadraticAlgebrasTest.gaussianWitness` among its fifteen named clients.
The 92 old signature blocks come from the
[published native output](https://github.com/FormalFrontier/quadratic-algebras/blob/e5ac018d29892d2a8612f4ca8d4babaabb9c4d15/docs/API.md).
The new supplement links the current source and is not native doc-gen output,
nor is this a generated inventory of every declaration in the current build.
No intermediate HTML, JavaScript, fonts,
dependency website, source PDF or external mathematical prose is distributed.

## Reproduction and binding

[`api-manifest.json`](api-manifest.json) records native analysis of source revision
`49e5e90c17970c0486876560eae2146ddd64e7ef`: twenty historical Lean inputs, three
configuration/pin inputs, twenty native records, the public inventory and the
output hash. It does not record native analysis of changed inputs in a later
checkout, including the new coordinate modules or the aggregate import.
Source or pin changes require assessing affected build and documentation
bindings; none of the recorded checks extends automatically to new inputs.

### Earlier 23-input comparison

These *recorded* SHA-256 hashes are of file bytes, not Git blob IDs, and describe
an earlier comparison of the manifest's 23 inputs with the
[published revision](https://github.com/FormalFrontier/quadratic-algebras/tree/e5ac018d29892d2a8612f4ca8d4babaabb9c4d15).
At that comparison, the following fourteen inputs differed: thirteen Lean
leaves have added references/docstrings, while the `Dedekind.lean`,
`FractionRing.lean` and `lakefile.toml` changes also contain earlier proof or
configuration edits. The other nine inputs matched their historical hashes
at that comparison. This table does not inventory or hash the subsequently
changed aggregate root, added coordinate production/test modules or the edited guides.

| Then-changed input | Recorded SHA-256 of that earlier file |
| --- | --- |
| `QuadraticAlgebras/AdjoinRoot.lean` | `f0445c4e640bfbf8823ff6d71c0986cee938b9140099a60f723c71fe52434604` |
| `QuadraticAlgebras/FractionRing.lean` | `c8ef88d0cdc6c802bfca0bcae709fe488e3e7b50ae209166982f9ac4f8945713` |
| `QuadraticAlgebras/Squarefree.lean` | `569469fc2825a6f7cb35499a086ab2368d81249d8d2132a1ee62b46081e05143` |
| `QuadraticAlgebras/Integral.lean` | `d53ed89a1ba42516ee36d8088d9b04ff1f8150f4a70fb55fc156bc90bf2d4736` |
| `QuadraticAlgebras/IntegralClosure.lean` | `7a276743318aa7dc7e8f920977047223e1513c92e8e22229797653cafdba8eba` |
| `QuadraticAlgebras/RepeatedSquare.lean` | `cf7ce20e182a0cba873701e560d4ca1835e69c5f29c029992832c34fef54a1e6` |
| `QuadraticAlgebras/IntegralClosureCriterion.lean` | `86dd18f2e4fbf1f621c17c3358fb87efa9f665f01de496576c45baec6851745d` |
| `QuadraticAlgebras/IntegralClosureInt.lean` | `52e080bed758db92f52d93b6ec208c4133484d5eff1273b0abfa6de47b5d6caa` |
| `QuadraticAlgebras/Dedekind.lean` | `6ba53d8a21e7517ad0744131b5f80aa52a5a6fca1abbf0b856b12888a960deee` |
| `QuadraticAlgebras/Diagonal.lean` | `dcf493e625162c3940b0522458fa206d1c35e94f9beed2167ce3095cdaf2202b` |
| `QuadraticAlgebras/SqrtNegFive.lean` | `ccee48b010656eb2284d2b8a6f7c099a2261a31fac672cf8bb556d9e9d9ca1b5` |
| `QuadraticAlgebras/NumberField.lean` | `7cf55e4eb4a08a09847f7ad7f9948c720bbdfb13eecc50bbc30b7e61e9343d70` |
| `QuadraticAlgebras/ClassNumberNegFive.lean` | `f2f9a45f3e6b626f06bd969a1fb59e75018bbb1e3783c639da1bf22a1fa1cea3` |
| `lakefile.toml` | `7d9992c5c15988dbd643ea2f58dcd2d97e1ce50a3e6fa772f1a8812f884d5f1a` |

The unchanged historical manifest's SHA-256 is
`72b9a964e729fd2c81ac73b5491c14f58f3ab9a0ea966ac750ac776025a98137`;
its API output digest `66316af0a97e3a12bb7a1598ab7fbf6b9a47db1e2806426a289133db22c246d5`
belongs to the published native output, **not** the current edited
[`API.md`](API.md). A previous API guide before the source-derived supplement
had SHA-256
`951dda3ea5f423af63a05cefa04c488ef6385f0f6d5d30b4dd00a2f436c2a779`.
All 92 historical native signature blocks and names/kinds are retained in the
guide; their recorded source-link assessment predates the new supplement.
The seven supplemental entries link the current declaration sources but do
not have native display signatures. These are not new native analysis or proof
checks and neither hash above authenticates this edited guide.

When the analyzed development commit exists locally, every input must match its
Git object. If that commit is missing from local history, generation must instead
produce a manifest byte-for-byte equal to the one committed at `HEAD`, and every
source input must equal `HEAD`. Missing history triggers this fallback, regardless
of whether `HEAD` has parents. It cannot bind the changed comparison inputs to
the unchanged historical manifest; native `--check` is not claimed to pass for
those inputs. A present but wrong Git object cannot activate the fallback;
in that fallback an uncommitted manifest is refused. In `--check` mode, changed
native records also differ from the committed output. Neither branch
authenticates a native run or proves mathematical correctness.

Build native doc-gen4 at `97d4ecdfc8e09e7f511724c25e303d448de6a3db` using its
committed five-dependency manifest and Lean `v4.34.0-rc2` in a separate checkout:
`lake build doc-gen4`. It is a core-only tool; do not change this library's pins.
For historical reproduction, check out the exact analyzed source revision,
fetch its matching mathlib cache and build its twenty modules using that
revision's README. Start with fresh analysis/render directories. Run `single` for
**each** module listed in `scripts/generate_api.py`, changing the module and source
path together. Use the full analyzed revision matching those inputs and records
(the manifest's revision for historical reproduction), not a branch.

```sh
mkdir /tmp/quadratic-analysis /tmp/quadratic-render
lake env /path/to/doc-gen4 single --build /tmp/quadratic-analysis QuadraticAlgebras.AdjoinRoot api.db https://github.com/FormalFrontier/quadratic-algebras/blob/FULL_SOURCE_COMMIT/QuadraticAlgebras/AdjoinRoot.lean
lake env /path/to/doc-gen4 bibPrepass --build /tmp/quadratic-render --none
lake env /path/to/doc-gen4 fromDb --build /tmp/quadratic-render --manifest /tmp/quadratic-render/manifest.json /tmp/quadratic-analysis/api.db
python3 -B scripts/generate_api.py --native-data /tmp/quadratic-render/doc-data --source-revision FULL_SOURCE_COMMIT
python3 -B scripts/generate_api.py --native-data /tmp/quadratic-render/doc-data --source-revision FULL_SOURCE_COMMIT --check
python3 -B scripts/test_generate_api.py
```

These are optional reproduction commands for exactly matching historical
sources and native records. `FULL_SOURCE_COMMIT` must be that analysis's full
revision; the historical adapter does not cover the new leaf or establish a
native check for the current twenty-two modules. The data-only tests use a
synthetic missing-history fixture, not release verification.

The adapter accepts exactly the inspected names, native kinds, origins and source
ranges. Native metadata groups abbreviations with definitions; the displayed
historical inventory is 61 theorems, 19 noncomputable definitions, four other
definitions, three abbreviations and five instances. All header text tokens are retained,
normalizing whitespace only. Native pretty-printing may omit literal type
annotations; names, docstrings and linked sources supply their context. These
are display signatures, not standalone modules or proofs. Module explanations
and declaration prose for those historical entries derive from their source
comments, separately from the historical native signature blocks. The new
chosen-coordinate entries are source-derived prose only.

Data-only tests exercise missing/duplicate/unexpected declarations, altered kinds,
lost modifiers, malformed markup, ranges, source drift and missing-history manifest
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
