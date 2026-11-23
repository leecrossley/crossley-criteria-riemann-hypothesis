# The Lean proof of the Riemann hypothesis

[`ConvertedThetaWindows.lean`](ConvertedThetaWindows.lean) proves Mathlib's `RiemannHypothesis` as the theorem `ConvertedThetaWindows.ordinary_rh`. It is Theorem 1.1 of [the paper](../paper/crossley-criteria-riemann-hypothesis.md).

The proof joins two things. The first is the theta-lift window, `ThetaExplicit.ordinary_common`: for every $`\theta\gt 1/2`$ the prime-power ramp $`G`$ stays below $`x^\theta`$ on arbitrarily late windows $`[Y,Y^{3/2}]`$. It comes from Levent Alpöge's geometric proof, through David Sanftenberg's principal-character extraction and Lee Crossley's conductor-one, nine-generator and second-seed specialisation. The second is the Landau theorem `IndependentLandau.zeta_zeroFree_of_window`, proved in [`landau/`](../landau/) from Mathlib alone, which turns those windows into the absence of zeros to the right of $`\theta`$. The functional equation does the rest.

The file also proves two corollaries from the window at the single exponent $`87/100`$: $`\zeta(s)\ne0`$ for $`\mathrm{Re}\,s\ge349/400`$ (`zero_free_349_400`), and the Crossley shell inequality at exponent $`2.98`$ (`full_shell_298`).

## Verification

[`verification.json`](verification.json) is the receipt of the check. With Lean 4.33.1 and Mathlib at `0df444a360eaa60ab8c11dca51a86af692955474`, the file compiled at trust level zero with warnings as errors, each of the six declarations whose axioms it prints, `ordinary_rh` among them, reported the axioms `propext`, `Classical.choice` and `Quot.sound` only, and the stock checker `LeanChecker.replayFromImports` accepted the module in a fresh process. The receipt lists the SHA-256 digests of the source, the compiled object and the six parent modules.

A separate stock-kernel replay reproduced the compiled theorem module byte for byte and all six axiom reports. Five of the six parent digests matched. The rebuilt arithmetic module `PureArithmeticCancellation.FixedLossThetaConversion` had a different digest. A fresh replay of the source in this directory reproduced the same result. [Independent replay and both parent digests](independent-replay.json)

## Sources

The window rests on Alpöge's geometric archive. The archived proof it extends reaches 1,476,889 declarations. An audit of that graph found that none of the 767 declarations at the interface to the window reaches the archive's own theorem of the Riemann hypothesis, and a build with that theorem's module removed compiled the window to the same bytes. The check imports a selection of 9,314 archive records with their proofs. It does not rebuild the whole archive in the same run.

The compiled parent modules are not in this repository. Replaying the check needs the archive at [Alpöge's release](https://github.com/leanprover-community/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005) and [Sanftenberg's principal-character geometry](https://github.com/dbsanfte/RiemannGaussian/blob/0755e6518416ac74bbb0e7f986f8610c7b7ed347/scripts/CheckAlpogePrincipalArchivedGeometryRH.lean), built on the same toolchain, and the nine-generator and second-seed closure that the window extends. That closure is public in [`prime-window-rh-criterion`, `results/geometric-window-descent`](https://github.com/leecrossley/prime-window-rh-criterion/tree/8f8ce11af908bb98df5c2adc2c8a72856fc2b8cd/results/geometric-window-descent), with its audit of the 1,476,889 declarations. An earlier version of that folder, with the same audit, is archived in the repository's release `square-block-median-v1.0.3`, [doi:10.5281/zenodo.24438940](https://doi.org/10.5281/zenodo.24438940). This release includes the joining theorem and its replay records. Rebuilding it also requires the geometric producer and compiled parent modules listed above.
