# The Crossley Criteria

[![Paper DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24466907.svg)](https://doi.org/10.5281/zenodo.24466907)

*A Mathematical Proof of the Riemann Hypothesis, Verified in Lean*

[Read the paper (PDF, 20 pages)](paper/crossley-criteria-riemann-hypothesis.pdf) | [Markdown version](paper/crossley-criteria-riemann-hypothesis.md)

I was told at school how fundamental the Riemann hypothesis (RH) was, but I wanted to see for myself how much a count of primes could tell me about the zeros of the Riemann zeta function. I went back to the way I used to learn at A-level and in my first year at uni ... I wrote the sums out on paper. I ended up with six criteria involving primes and Möbius sums, any one of which implies RH.

Alpöge got over 250,000 pages when he tried writing out the geometry. My paper runs to 20 pages, and [§1.2](paper/crossley-criteria-riemann-hypothesis.md#12-proof) is where I use that geometry for one bound. I'm hoping some better mathematicians will help me improve it from here, in the open. Issues and pull requests are welcome.

## Proof

For the proof I count prime powers as well as primes, weighting each term, and write $`G(x)`$ for the error in that count up to $`x`$. I use David Sanftenberg's specialisation of Levent Alpöge's theta lifts to the Riemann zeta function, and my conductor-one calculation in §1.2 gives the following bound. For every $`\theta\gt 1/2`$ there are arbitrarily large $`Y`$ for which $`G(x)\le x^\theta`$ throughout $`[Y,Y^{3/2}]`$. Taken over all exponents between one half and one, those windows are equivalent to RH.

If there were a zero $\rho$ to the right of the critical line, I could choose $`\theta`$ between $`1/2`$ and $`\mathrm{Re}\,\rho`$, and a theorem of Landau type would force the error above the bound somewhere in every sufficiently late interval of that form. That rules out a zero on the right, and since the functional equation pairs any nontrivial zero on the left with one on the right, every nontrivial zero lies on the critical line. Lean checks this against Mathlib's statement of RH, and I used Mathlib alone in the separate project of 218 modules to prove that each of the six arithmetic criteria is equivalent to RH. If I could prove the signed inequality in §11 directly from the arithmetic, that would give me another proof of RH. [Lean theorem](theta-window/ConvertedThetaWindows.lean) | [Verification notes](theta-window/README.md)

## Criteria

Each criterion came out of trying to make the one before it easier to check by hand. I started by weighting the primes between $`y`$ and $`4y`$ with a tent, and asked when that count stays at or below its average on long stretches far out. Then I reduced the check to whole numbers and squares, used $`\Lambda=\mu*\log`$ to turn the primes into Möbius sums, averaged at fourth powers, split the divisors into dyadic shells and looked at pairs of divisors. [Derivation](paper/crossley-criteria-riemann-hypothesis.md#14-criteria)

| Criterion | Condition |
| --- | --- |
| Window | the tent-weighted count of primes stays at or below $`(x/2)\log2`$ on long late windows |
| Square-block | the prime-power margin is at least $`-Ck`$ at every square $`k^2`$ of late blocks |
| Fourth-power | the weighted shortfalls at fourth powers add up to less than any power of $`m`$ |
| Shell | the worst dyadic shell of divisors rarely crosses each level |
| Far-pair | the far divisor pairs in that shell add up to little |
| First-moment | the shell scores add up to less than any power of $`m`$ |

All six are equivalent to RH in Lean, from Mathlib alone, so the proof above makes them true. That's circular for my purposes: what I'm after is a proof of one of them straight from the arithmetic, which would prove RH with no geometry. I also proved sixteen other statements equivalent to RH along the way, and kept the name for these six. Section 11 of the paper gives the inequality I'm trying to prove. [The arithmetic inequality](paper/crossley-criteria-riemann-hypothesis.md#11-arithmetic-inequality)

<details>
<summary>Build</summary>

The [Landau project](landau/) contains the window theorem and the reflection step. It uses Lean 4.33.1 and a pinned Mathlib revision. The [218-module project](project/) contains all six criteria and is described in §12 of the paper. Its [README](project/README.md) explains how to build it. [Source hashes](landau/SHA256SUMS)

```sh
cd landau && lake exe cache get && lake build
```

[`verify-linux.sh`](verify-linux.sh) runs the full check on x86_64 Linux. It confirms the hashes in `landau/SHA256SUMS`, checks `theta-window/ConvertedThetaWindows.lean` against both of its receipts, rebuilds `landau/` with the pinned Lean and Mathlib, replays every module in Lean's kernel checker, and confirms that the two theorems the proof takes from it use only the three standard axioms. The [Verify](.github/workflows/verify.yml) workflow runs it on pushes to main. It cannot rebuild the final theorem, whose parent modules are not in this repository.

To rebuild the PDF, run `paper/build-pdf.sh` from the repository root. The script uses Python 3, pandoc, XeLaTeX, exiftool and pdfinfo.

</details>

<details>
<summary>Sources</summary>

The geometric window in §1.2 uses the [nine-generator bound and second seed](https://github.com/leecrossley/prime-window-rh-criterion/tree/8f8ce11af908bb98df5c2adc2c8a72856fc2b8cd/results/geometric-window-descent). The square-samples release below contains an earlier version of that calculation.

| Result | Source tag | Release DOI |
| --- | --- | --- |
| Prime window | [v1.0.4](https://github.com/leecrossley/prime-window-rh-criterion/tree/v1.0.4) | [10.5281/zenodo.24412819](https://doi.org/10.5281/zenodo.24412819) |
| Window criteria | [v1.1.1](https://github.com/leecrossley/prime-window-rh-criterion/tree/v1.1.1) | [10.5281/zenodo.24421600](https://doi.org/10.5281/zenodo.24421600) |
| Fourth-power Möbius criterion | [fourth-power-mobius-v1.0.0](https://github.com/leecrossley/prime-window-rh-criterion/tree/fourth-power-mobius-v1.0.0) | [10.5281/zenodo.24426583](https://doi.org/10.5281/zenodo.24426583) |
| Fourth-power Möbius revision | [fourth-power-mobius-v1.0.1](https://github.com/leecrossley/prime-window-rh-criterion/tree/fourth-power-mobius-v1.0.1) | [10.5281/zenodo.24428032](https://doi.org/10.5281/zenodo.24428032) |
| Square samples and geometric descent | [square-block-median-v1.0.3](https://github.com/leecrossley/prime-window-rh-criterion/tree/square-block-median-v1.0.3) | [10.5281/zenodo.24438940](https://doi.org/10.5281/zenodo.24438940) |
| Dirichlet window transfer | [v1.0.4](https://github.com/leecrossley/dirichlet-window-transfer/tree/v1.0.4) | [10.5281/zenodo.24410863](https://doi.org/10.5281/zenodo.24410863) |

</details>

## Citation

Lee Crossley (2026). *The Crossley Criteria: A Mathematical Proof of the Riemann Hypothesis, Verified in Lean*. Version 1.0, 23rd November 2026. [Repository](https://github.com/leecrossley/crossley-criteria-riemann-hypothesis) | [Citation file](CITATION.cff) | [10.5281/zenodo.24466908](https://doi.org/10.5281/zenodo.24466908)

Lee Crossley | [ORCID](https://orcid.org/0009-0009-2264-2219) | [LinkedIn](https://www.linkedin.com/in/leecrossley) | [CC BY 4.0](LICENSE)
