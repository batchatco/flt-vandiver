# flt-vandiver

**Machine-checked Fermat's Last Theorem for every prime exponent `17 ≤ p < 1000` (regular and irregular), by the classical cyclotomic route, with no modularity input.**

A Lean 4 project, built on [flt-regular](https://github.com/leanprover-community/flt-regular)
and [Mathlib](https://github.com/leanprover-community/mathlib4), that proves FLT by classical
(Kummer-style) cyclotomic methods at irregular prime exponents — where `flt-regular`'s
regularity hypothesis fails — and reduces full FLT, with no modularity input, to a short list
of named open problems, machine-checked, with nothing hidden in prose.

Per-prime theorems `fermatLastTheoremFor_<p>` exist for **every prime `17 ≤ p < 1000`** (162 primes —
64 irregular, `37, 59, 67, …, 971`, and 98 regular) **and for both known Wolstenholme primes, `p = 16843` and
`p = 2124679`** — each resting on the standard axioms plus two `native_decide`
certificates; see the companion repository
[`flt-vandiver-primes`](#repository-layout). The distinctive feature is uniformity: one Vandiver
small-witness certificate discharges each exponent, so a single engine reaches the whole range. The
irregular primes `59` and `67` and every prime above `100` are reached here for the first time; the
smallest irregular prime, `37` (Kummer's 1857 case, first proved by hand that year), was
machine-checked earlier by [Birkbeck's AINTLIB](https://github.com/CBirkbeck/AINTLIB) via a bespoke
Eichler development. The formalized route here is the modern form of Kummer's argument (Vandiver-style
Case II descent + Legendre/Kummer Case I), driven per-prime by short certificates. Combined with
Mathlib's exponents 3 and 4 and `flt-regular`'s instances `5 ≤ p ≤ 13`, FLT for every
exponent `2 < n < 1000` follows by routine per-exponent assembly.

At `p = 59` the proof is search-free for Case I: Kummer's 1857 criterion
(`p ∤ B_{p−3} ⟹ Case I`) runs off the Bernoulli certificate, and Case II runs off the
same auxiliary pair `(ℓ, t) = (709, 2)` that proves Vandiver:

```lean
theorem fermatLastTheoremFor_59 : FermatLastTheoremFor 59   -- FltPrimes/FLT59.lean
```

## Quick start: clone the six libraries as siblings

The `lakefile.toml` here refers to sibling checkouts (`path = "../flt-stickelberger"`, `path = "../flt-cyclotomic-nt"`),
so cloning this repository alone and running `lake build` fails. Clone all six at the `afm-v2` tag into one directory:

```sh
for r in flt-stickelberger flt-cyclotomic-nt flt-vandiver flt-vandiver-primes \
         flt-vandiver-primes-kernel flt-regular-extended; do
  git clone --branch afm-v2 https://github.com/batchatco/$r
done
cd flt-vandiver           && lake exe cache get && lake build                    # the engine
cd ../flt-vandiver-primes && lake exe cache get && lake build FltPrimes.FLT59    # one certified prime
```

`lake build FltPrimes.FLT59` re-runs the two `native_decide` certificates for `p = 59` (seconds) on top of the
engine; `lake build FltPrimes` re-runs every prime below `1000` (minutes). Independent-kernel comparators for
`p = 59` and `p = 107` (`Challenge.lean`, Mathlib-only statements) live in `flt-vandiver-primes-kernel` and
`flt-regular-extended`. See [Building](#building) for the larger exponents.

## The crown theorems: FLT by the cyclotomic route, reduced to two named open problems

(`FltVandiver/Statement.lean`.) The main reduction:

```lean
theorem fermatLastTheorem_of_vandiver_sgAux
    (hswcert : ∀ (p : ℕ) [Fact p.Prime], 3 < p → SmallWitnessCert p)
    (haux : ∀ (p : ℕ), p.Prime → p ≠ 2 →
      ∃ q : ℕ, ∃ _ : NeZero q, q.Prime ∧ sgCert p q = true) :
    FermatLastTheorem
```

The two hypotheses are the open problems of the non-modular route, each stated in its
honest species:

* **`hswcert` — the effective small-witness Vandiver certificate, uniformly in `p`**
  (Washington Thm 9.5's hypothesis): an auxiliary pair `(ℓ, t)`, `ℓ ≡ 1 (mod p)` prime
  with `ℓ < p² − p`, whose `Q_i` cyclotomic-unit test fires at every even index. This is
  Vandiver's conjecture (`p ∤ h⁺`, a congruence-anomaly statement going back to Kummer and Vandiver)
  in effective, per-prime-checkable form; the same data powers the entire Case II descent.
  Verified numerically far beyond any exponent of interest; heuristically *expected* to
  have exceptions (Washington's `½ log log x` count) yet none has ever been found.
* **`haux` — a Sophie Germain/Legendre auxiliary prime exists for every `p`**: a
  prime-distribution statement, long open (Ribenboim, *13 Lectures*, calls it "a difficult
  problem"); Dickson (1909) showed each `p` admits only finitely many candidate auxiliary
  primes. GRH and all known conditional results give density-1 in `p`, never all `p`.

Each hypothesis alone is a recognized open problem; the point of the formalization is that
**the entire gap between Kummer-style methods and FLT is exhibited as these statements**.
A variant `fermatLastTheorem_of_vandiver_window` (crown v3) replaces `haux` by three averaged
statements about a window of candidate auxiliaries; its docstring calls those statements open
problems in `afm-v1`, but no constant `C` satisfies them, so the theorem is valid and vacuous
(see [History](#history)). `fermatLastTheorem_of_vandiver_caseI` is the coarse form with Case I
assumed directly. `p = 3` is closed unconditionally via Mathlib's `fermatLastTheoremThree`.

## Architecture: an axiom-free engine fed by per-prime certificates

Each certified prime is discharged from two `native_decide` facts (the `FltPrimes/FLT<p>.lean`
files in `flt-vandiver-primes`):

| Certificate | Checks | Discharges |
|---|---|---|
| `vandiverCert p ℓ t (evenIndices p)` | the `Q_i` cyclotomic-unit test at an auxiliary prime `ℓ ≡ 1 (mod 2p)`, `ℓ < p² − p`, at every even index | BOTH `IsVandiverPrime p` (via the `Q_i` bridge, `QiBridge.lean`) AND the entire Case II descent (Washington Thm 9.5) — uniformly for regular and irregular `p` |
| `irrListCert p [..]` | the list of irregular indices of `p` | the Bernoulli data for Kummer's Case I criterion |

The engine consuming the certificates:

* **Case II** — the fully proven Washington §9.1 + Thm 9.5 small-witness descent
  (`Descent92*.lean`, `CaseII95Core.lean`, `CaseII95Descent.lean`): the single auxiliary
  pair `(ℓ, t)` threads an `ℓ ∣ ξ` invariant through the classical descent, so no
  eigenspace hypothesis beyond the certificate itself is needed.
* **Case I** — Legendre's auxiliary-prime criterion, formalized from the Barlow relations up
  (`SophieGermain.lean`), or Kummer's criterion `p ∤ B_{p−3} ⟹ Case I`
  (`CaseIKummer.lean`, in the `flt-cyclotomic-nt` dependency).

Supporting results proven along the way (each, to our knowledge, a first formalization —
corrections welcome):

Most now live in the **`flt-cyclotomic-nt`** dependency rather than this repo:

* **Stickelberger's theorem** — Gauss-sum prime factorization + the integral Stickelberger
  relation (our standalone, independent clean-room `flt-stickelberger` library, Washington
  Ch. 6), with the all-ideals reduction and full class-group annihilation completed in
  `flt-cyclotomic-nt` (`stickelberger_annihilates`, axioms `propext`/`Classical.choice`/`Quot.sound`);
* **Herbrand's theorem** (`flt-cyclotomic-nt`);
* **Kummer's criterion (1857)** for Case I (`flt-cyclotomic-nt`);
* **the cyclotomic unit index** `[E : C] = h⁺` (Washington Thm 8.2; `flt-cyclotomic-nt`);
* **Legendre's auxiliary-prime criterion** for Case I (`SophieGermain.lean`, this repo);
* class-group functoriality (`flt-cyclotomic-nt`: extension, norm, `N∘ι = ·^[L:K]`,
  Galois action) — absent from Mathlib at the time of writing.

## Axiom status: no custom axioms

The project carries **no axioms of its own**; every mathematical input is a proven theorem.

Audit any claim yourself (in `flt-vandiver-primes`):

```lean
#print axioms FltVandiver.fermatLastTheoremFor_101
-- expected: propext, Classical.choice, Quot.sound, plus the certificates'
-- generated axioms `…._native.native_decide.ax_*` — native_decide's
-- compiler-trust markers on the pinned toolchain (v4.31.0)
```

**Trust note, stated plainly:** `native_decide` certificates trust the Lean compiler
(that is what the generated `…ax_*` axioms above record), not just the kernel. Everything
else is kernel-checked against Mathlib's three standard axioms.

## Repository layout

The development is split across small repositories so the core library builds fast:

| Repository | Content |
|---|---|
| **flt-vandiver** (this repo) | the engine: descent, certificates' soundness bridges, crown theorems |
| **flt-vandiver-primes** | `fermatLastTheoremFor_<p>` + the two `native_decide` certificates, for every prime `17 ≤ p < 1000` and for both Wolstenholme primes `p = 16843` and `p = 2124679` (the `p = 59` Case I, `FltPrimes/FLT59.lean`, is search-free via Kummer's Case-I criterion) |
| **flt-vandiver-primes-kernel** | kernel-only re-proofs of `fermatLastTheoremFor_<p>` for the **8 irregular primes `< 200`** (the regular primes in that range are kernel-checked in `flt-regular-extended`) — pure kernel `decide`, no `native_decide`, no compiler trust |
| **flt-regular-extended** | `FermatLastTheoremFor q` for every regular prime `17 ≤ q < 350` (47 primes), via `flt-regular` plus a kernel-`decide` Bernoulli regularity check (`native_decide`-free) |
| **flt-cyclotomic-nt** | analytic/algebraic NT foundations (Dedekind zeta factorization, generalized Bernoulli, L-values; sorry-free; builds on Mathlib, flt-stickelberger, flt-regular) |
| **flt-stickelberger** | our standalone, independent clean-room formalization of Stickelberger's theorem (Gauss-sum factorization + integral Stickelberger relation, following Washington Ch. 6; Mathlib-only, sorry-free) |

Release tag **`afm-v2`** across all six; GitHub topic
[`flt-vandiver`](https://github.com/batchatco?tab=repositories&q=topic:flt-vandiver); each ships
an `AxiomAudit.lean`. Companion paper in preparation.

Map of this repository:

| File(s) | Content |
|---|---|
| `Statement.lean` | the reduction theorems and the crowns (`fermatLastTheorem_of_vandiver_*`) |
| `SophieGermain.lean` | Case I: Legendre's auxiliary-prime criterion (Kummer's `p∤B_{p−3}` criterion is in the `flt-cyclotomic-nt` dependency) |
| `Descent92*.lean`, `CaseII95Core.lean`, `CaseII95Descent.lean`, `RouteA.lean` | Case II descent: the Washington §9.1 machinery and the Thm 9.5 small-witness route (Lemmas 9.6–9.9, the `ℓ ∣ ξ` invariant, and the certificate engines) |
| `QiCertificate.lean`, `QiCertAppend.lean`, `QiBridge.lean`, `QiBridgeProof.lean`, `QiCertFast.lean` | the `Q_i` Vandiver certificate, slice assembly, and bridges |
| `CertKernel.lean` | precompiled modular-exponentiation kernel used by the fast certificate form |
| `QiEvalFast.lean`, `QiCertFast2.lean` | (`afm-v2`) the machine-speed evaluator of the all-even `Q_i` certificate, precompiled like `CertKernel`, and its bridge `vandiverCert_of_fast2` to `vandiverCert` on the standard axioms; every table fact the bridge relies on is re-verified inside the certificate |
| `QiBaseIndep.lean` | (`afm-v2`) base independence: the `Q_i` verdict at an even index is the same for every valid base `t` (`qi_pow_eq_one_iff_of_base`, `vandiverCert_evenIndices_of_base`), so a witness is the prime `ℓ` alone |

The analytic/number-theoretic foundations — Stickelberger → Herbrand, the cyclotomic unit
index `[E:C]=h⁺`, eigenspace/real-subfield machinery, Bernoulli background, and class-group
functoriality — were moved out of this repo and now live in the **`flt-cyclotomic-nt`**
dependency; see its file map.

**History.** In `afm-v1`, `CaseII95Core.lean`'s module docstring pointed to a planning file
(`CASEII95_PLAN.md`) that was not part of the release; the reference was left in place because
that module sits in the `p = 2124679` build closure, whose recomputation then took days. The
machine-speed `Q_i` evaluator `QiEvalFast` (below) made the recomputation cheap, and the
docstring was corrected in `afm-v2`.

## History

**`FltVandiver/Statement.lean`, line 168 of `afm-v1`: the docstring of `fermatLastTheorem_of_vandiver_window`
overstated the theorem.** The `afm-v1` docstring presents the theorem as a reduction of Case I to three
averaged statements about the window `𝒬_p(C·p²)` of primes `q ≤ C·p²` with `q ≡ 1 (mod 2p)` and
`3 ∤ (q−1)/2p`, for one constant `C : ℕ` and every odd prime `p`: the window is nonempty (`hα`); the
number of ordered pairs of nonzero `p`-th power residues summing to `1`, totaled over the window,
is at most half the window's size (`hβA`); and on at most a quarter of the window `p` is a `p`-th
power (`hβB`). That description is withdrawn. No `C : ℕ` satisfies the three hypotheses, so the
implication is valid but vacuous:

* `C = 0`: the window is empty, so `hα` fails.
* `C = 1, 2, 3`: `hβA` fails at `p = 31`, `23`, `11` respectively. At `C = 1`, `p = 31` the window
  is `{311, 683}`, and `683` alone contributes the three pairs `(2, 682)`, `(682, 2)`, `(342, 342)`.
* `C ≥ 4`: `hβA` fails already at `p = 3`. The window contains `7`, `13`, `31`, and every member
  from `31` on contributes at least two pairs, by the Hasse bound for the cubic `X³ + Y³ = Z³`.

What survives is the per-prime pigeonhole `caseI_of_supply_of_cancellation`, which turns the three
conditions at a fixed `p` into a passing auxiliary and is correct; the window theorem is that
pigeonhole composed with `fermatLastTheorem_of_vandiver_caseI`, not a reduction to open problems.
The crown theorem `fermatLastTheorem_of_vandiver_sgAux` above is unaffected. In `afm-v1` the docstring was not
corrected in place, because `Statement.lean` was part of the frozen, commit-pinned release the
companion paper links to; from `afm-v2` the docstring states the vacuity itself.

## Relation to other projects

* [**flt-regular**](https://github.com/leanprover-community/flt-regular) — this project's
  foundation; proves FLT for regular primes. flt-vandiver weakens regularity to Vandiver
  and recovers the regular case as a corollary (every regular prime is a Vandiver prime).
* [**Formalizing Fermat's Last Theorem**](https://github.com/anthropics/fermats-last-theorem) (Peng et al.,
  Anthropic, 2026) — a complete Lean formalization of the modular route (Frey, Serre, Ribet, Wiles,
  Taylor–Wiles), settling every exponent at once. It shares Mathlib and `flt-regular` with this project and
  no mathematics above them. This project is not a competitor on range: it shows how far the
  *pre-modular* methods reach, one exponent at a time, and at which two named statements they stop.
* [**The FLT project**](https://github.com/ImperialCollegeLondon/FLT) (Buzzard et al.) — an independent,
  ongoing formalization of the modular route.
* **Mathlib** — the class-group functoriality, Stickelberger, and Bernoulli infrastructure
  here could be upstreamed to Mathlib, where they would outlive the certificates that motivate them.

## Building

Clone the sibling libraries first ([Quick start](#quick-start-clone-the-six-libraries-as-siblings)), then in this directory:

```sh
lake exe cache get   # fetch Mathlib cache
lake build           # core library
```

`lean-toolchain` pins the toolchain; `lakefile.toml` pins Mathlib, `flt-regular`, and the
flt-stickelberger and flt-cyclotomic-nt dependencies. The per-prime certificates live in `flt-vandiver-primes`
(`lake build FltPrimes` there re-runs every certificate: seconds for small `p`, a few
minutes for the largest below `1000`; through the `afm-v2` evaluator `QiEvalFast` the `p = 16843` certificate re-verifies in
seconds and the `p = 2124679` certificate in 31 core-hours as sixteen parallel slices
(118 minutes of wall time on 16 cores), see `flt-vandiver-primes` for measured figures; in `afm-v1` the same two runs took
twenty single-threaded minutes and about 250 core-days). The engine is uniform in `p`: to certify a new prime,
generate its witness pair `(ℓ, q)` (the smallest primes `≡ 1 (mod 2p)` passing each test)
and add the corresponding `FLT<p>` files.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, 2nd ed., Springer, 1997
  (Ch. 5–6, 8, 9: Stickelberger, cyclotomic units, the second case of FLT).
* `leanprover-community/flt-regular`. <https://github.com/leanprover-community/flt-regular>

## Blueprint & metadata

A dependency-graph blueprint of this library is under [`blueprint/`](blueprint/) (rendered web + PDF published to GitHub Pages once the family is public). Family-level metadata for all six libraries is in [`formalization.yaml`](formalization.yaml) in this repo's root.

---

Apache License 2.0 — see [LICENSE](LICENSE).
© Bradley Taylor. Code written largely by Claude (Anthropic) under the author's direction.
