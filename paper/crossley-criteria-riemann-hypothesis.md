# The Crossley Criteria

A Mathematical Proof\
of the Riemann Hypothesis\
Verified in Lean

Lee Crossley

ORCID [0009-0009-2264-2219](https://orcid.org/0009-0009-2264-2219)

[linkedin.com/in/leecrossley](https://www.linkedin.com/in/leecrossley)

v 1.0\
[10.5281/zenodo.24466908](https://doi.org/10.5281/zenodo.24466908)

23rd November 2026

# Abstract

I was told at school how fundamental the Riemann hypothesis (RH) was, but I wanted to see for myself how much a count of primes could tell me about the zeros of the Riemann zeta function. I went back to the way I used to learn at A-level and in my first year at uni ... I wrote the sums out on paper. I ended up with six criteria involving primes and Möbius sums, any one of which implies RH.

Alpöge got over 250,000 pages when he tried writing out the geometry. My paper runs to 20 pages, and §1.2 is where I use that geometry for one bound. I'm hoping some better mathematicians will help me improve it from here, in the open.

For the proof I count prime powers as well as primes, weighting each term, and write $`G(x)`$ for the error in that count up to $`x`$. I use David Sanftenberg's specialisation of Levent Alpöge's theta lifts to the Riemann zeta function, and my conductor-one calculation in §1.2 gives the following bound. For every $`\theta\gt 1/2`$ there are arbitrarily large $`Y`$ for which $`G(x)\le x^\theta`$ throughout $`[Y,Y^{3/2}]`$. Taken over all exponents between one half and one, those windows are equivalent to RH.

If there were a zero $\rho$ to the right of the critical line, I could choose $`\theta`$ between $`1/2`$ and $`\mathrm{Re}\,\rho`$, and a theorem of Landau type would force the error above the bound somewhere in every sufficiently late interval of that form. That rules out a zero on the right, and since the functional equation pairs any nontrivial zero on the left with one on the right, every nontrivial zero lies on the critical line. Lean checks this against Mathlib's statement of RH, and I used Mathlib alone in the separate project of 218 modules to prove that each of the six arithmetic criteria is equivalent to RH. If I could prove the signed inequality in §11 directly from the arithmetic, that would give me another proof of RH.

# 1. Introduction

I'd struggle to explain nine tenths of the geometry in Alpöge's proof with any confidence. Lean could check the argument, and I could trace which files it used, but I still wanted to understand how it got from theta lifts to a statement about primes. Alpöge was quite open about how much of the surrounding maths he still had to master. He tried generating a written account and got over 250,000 pages. [Alpöge's note, p. 2](https://alpo.ge/remark.pdf)

I could take the dead code out of the archive and still prove the theorem, and although that made it easier to trace a particular result, I was still looking at the same geometry afterwards. So I started again from scratch with the Riemann zeta function, counting primes between $y$ and $4y$ and giving more weight to the ones near $2y$.

In §1.2 I count prime powers, so the sum includes numbers like 4 and 8 as well as the primes themselves. The theta lifts give a bound on the error in that count. A zero to the right of the critical line would force the error above the bound, and the functional equation rules out a zero on the left too. That proves RH. In §3 I go back to primes and give the ones near the middle of the interval more weight. This gives the first of the six criteria.

## 1.1 Counting primes

Around $x$, roughly one integer in $\log x$ is prime. Integrating that density gives an estimate for how many primes there are up to $x$. Riemann's hypothesis, from 1859, is about how big the error is.

Riemann connected the error to the zeros of the zeta function $\zeta(s)$. Under RH the count differs from the logarithmic integral by at most a constant times $`\sqrt x\,\log x`$ for large $x$. A zero to the right of the line $`\mathrm{Re}\,s=1/2`$ would make the fluctuations larger by a power of $x$.

## 1.2 Proof

**Theorem 1.1 (The Riemann hypothesis).** Every zero of $\zeta$ with $`0\lt \mathrm{Re}\,s\lt 1`$ has $`\mathrm{Re}\,s=1/2`$. *Lean, unconditional, from the archive*: `ConvertedThetaWindows.ordinary_rh : RiemannHypothesis`.

Lean's kernel accepts the proof, and it only uses the three standard axioms `propext`, `Classical.choice` and `Quot.sound`. What I need from the geometry is a bound on this sum.

Write $`\Lambda(n)`$ for $`\log p`$ when $n$ is a power of a prime $p$, and $0$ otherwise, and $\gamma$ for Euler's constant. Let

```math
G(x)=\sum_{n\le x}\Lambda(n)\Big(\frac xn-1\Big)-x\log x+(1+\gamma)x .
```

For example, $8=2^3$ contributes $\log 2$ times the weight $x/8-1$ when $x\ge8$. The integer $6$ contributes nothing. After subtracting the main term, the error is $G(x)$.

**Theorem 1.2 (The theta-lift window).** For every $`\theta\gt 1/2`$ and every $`Y_0`$ there is $`Y\ge\max(Y_0,2)`$ with $`G(x)\le x^\theta`$ for every real $`x\in[Y,Y^{3/2}]`$. *Lean, unconditional, from the archive.* In Lean this is `ThetaExplicit.ordinary_common`.

*Proof of Theorem 1.1 from Theorem 1.2.* Suppose $\rho$ is a zero with $`\mathrm{Re}\,\rho\gt 1/2`$. Choose $`1/2\lt\theta\lt\min(\mathrm{Re}\,\rho,1)`$. By Remark 3.6, the zero would force $G(x)$ above $x^\theta$ somewhere in every sufficiently late window $[Y,Y^{3/2}]$. Theorem 1.2 gives a whole window past any starting point where $G(x)\le x^\theta$, so $\rho$ can't be there. By the functional equation (Proposition 3.1), any nontrivial zero on the left would give one on the right.

Remark 3.6 also gives the reverse implication, since RH supplies these ramp windows for every exponent between one half and one. I obtain the windows here from the geometric construction. The oscillation result uses the local form of Landau's theorem due to Kaczorowski and Pintz. It applies to the ramp $G$. In the rest of the paper I also use a tent weight on primes. Its window criterion (Theorem 3.2) asks for $`P(x/4)\le(x/2)\log2`$ with no error allowance.

## 1.3 Attribution

Levent Alpöge's proof uses theta lifts of automorphic forms. The modules imported for the Riemann zeta case contain about sixteen million lines of Lean. David Sanftenberg specialised the construction to the principal character. The corrected kernel and contour bound I use in §8 and §11 are his too.

I specialised Sanftenberg's comparison to one window of conductor one using the nine-generator bound, a finite frame and a second seed. Theorem 1.1 joins that window to my Lean proof of the implication from the window to RH. The linked repository gives the Lean source and dependency check for the nine-generator bound and second seed. An earlier version is archived on Zenodo. [Geometric window descent](https://github.com/leecrossley/prime-window-rh-criterion/tree/8f8ce11af908bb98df5c2adc2c8a72856fc2b8cd/results/geometric-window-descent), [doi:10.5281/zenodo.24438940](https://doi.org/10.5281/zenodo.24438940)

AI assistants wrote a lot of the Lean, working under my direction. Each result was rebuilt and checked by a different session from the one that wrote it.

## 1.4 Criteria

I've kept the step numbers from the Lean project.

**Windows (Steps 0 and 1).** Take the primes between $y$ and $4y$ and give each one a weight from a tent: zero at $y$, rising to one at $2y$, back to zero at $4y$. On average this weighted count is $`(x/2)\log2`$, where $`x=4y`$. A zero of $\zeta$ to the right of the critical line would make the count swing above its average, by a power of $x$, somewhere in every long enough stretch far out. That's Landau's theorem, in the local form of Kaczorowski and Pintz. So if the count never goes above $`(x/2)\log2`$ on long stretches arbitrarily far out, there's no such zero, and the functional equation deals with the left-hand side. That's the **window criterion** (Theorem 3.2).

**Squares (Steps 2 and 3).** The tent weights are straight lines between whole numbers, so it's enough to check integers, and on a block only its two ends and the doubled primes $2p$ (Theorem 3.4). Between two consecutive squares the margin can't bend far from the straight line joining its values. So I only need to look at the squares $k^2$, with an allowance of $Ck$ for one fixed $C$, on late blocks $[K,K^2]$. That's the **square-block criterion** (Theorem 4.1). It uses the prime-power margin $D$, which also counts prime squares and higher powers.

**Inversion (Step 4).** Primes are hard to count directly. Using $`\Lambda=\mu*\log`$, I rewrote the margin at $k^2$ as a sum over every integer $d$ up to $k^2$: the Möbius sign $`\mu(d)`$ times a bounded weight $`R(k^2/d)`$ (Proposition 5.1). The small $d$ only cost $O(k)$, so everything comes down to how much the terms with large $d$ cancel.

**Averaging (Steps 5 and 6).** I can ease the condition at the squares by sampling at fourth powers $n^4$, adding up the amounts by which the margin falls below zero and weighting each by $`1/n^3`$. RH holds exactly when that total grows more slowly than every power of $m$ on arbitrarily late blocks $[m,m^2]$. That's the **fourth-power criterion** (Theorem 6.1). Counting how often the scaled loss crosses each level $2^k$ gives the same thing (Theorem 7.1).

**Shells (Step 7).** I split the divisors at $n^4/2$, $n^4/4$ and so on, and at each sample took the worst of these dyadic shells. That gives the shell score $Z(n)$. Bounding how often $Z(n)$ crosses each level is the **shell criterion** (Theorem 8.1).

**Pairs and moments (Steps 8 and 9).** Squaring the sum on a shell gives pairs of divisors. Pairs that are close together, once you divide out their common factor, are already small (Theorem 9.1(b)). So only the far pairs matter, and that's the **far-pair criterion** (Theorem 9.1(c)). Adding up $Z(n)/n$ over a block, rather than counting crossings, gives the **first-moment criterion** (Theorem 10.1). Assuming a zero-free half-plane gives the converse directions (Theorem 10.2).

| Criterion | Condition | Theorem | Lean |
| ------------ | ------------------------------------------------------------ | -------------- | ---------------- |
| Window | the tent-weighted count of primes stays at or below $`(x/2)\log2`$ on long late windows | Theorem 3.2 | both directions |
| Square-block | $`D(k^2)\ge-Ck`$ at every square of late blocks $`[K,K^2]`$ | Theorem 4.1 | both directions |
| Fourth-power | the weighted shortfalls at fourth powers add up to less than any power of $m$ | Theorem 6.1 | both directions |
| Shell | the worst dyadic shell rarely crosses each level | Theorem 8.1 | both directions |
| Far-pair | the far divisor pairs in that shell add up to little | Theorem 9.1(c) | both directions |
| First-moment | the shell scores add up to less than any power of $m$ | Theorem 10.1 | both directions |

**Status.** I proved both directions of each equivalence in Lean using Mathlib alone, so all six criteria follow from Theorem 1.1. That still takes me through the geometry, and I’d need a direct arithmetic proof of just one row to get to RH without it. Joining Theorem 1.1 to each converse is a one-line step in Lean, but it needs one build that contains both the archive and my project. So far I've only done that for the shell inequality at exponent $2.98$ (`full_shell_298`, §11.2).

**Variants.** Along the way I proved sixteen other statements equivalent to RH in Lean. They include variants of the square-block and fourth-power conditions, the level-set condition, conditions on primes in the tail and near the centre of the tent, and the ramp window of Remark 3.6, which is the one Theorem 1.1 uses. I kept the name Crossley Criteria for the six that make up the chain from primes to Möbius shells. Section 11.5 lists the four statements I think are most worth attacking.

## 1.5 Dependencies

The 218 modules containing the criteria also contain the Landau theorem and the symmetry argument used in Theorem 1.1. Each module passed the kernel checker. The audit found no declaration from Alpöge's archive among the dependencies of the twenty-six theorems it examined (§12).

The proof behind the geometric window reaches 1,476,889 declarations. I checked the 767 declarations through which the window uses it. None depends on the archive's theorem of RH. Removing the module containing that theorem and rebuilding gave a byte-for-byte identical compiled window (§12.4).

Here *archive* means the formal source of Alpöge's proof. At *trust level zero*, Lean's kernel checks the proof terms as it compiles the module. The standalone checker can then replay the compiled proofs in a separate process.

# 2. Notation

I write $\Lambda$ for the von Mangoldt function, $\mu$ for the Möbius function, $\psi$ and $\vartheta$ for the Chebyshev functions, $\gamma$ for Euler's constant, and

$$ c=\frac{\log 2}{2}. $$

**The tent.** When I count at scale $x$, the term $n$ gets weight $W(n/x)$. It's zero at both ends of $[x/4,x]$ and goes up to one at $n=x/2$. Explicitly, for $`t\gt 0`$,

```math
W(t)=\begin{cases} 2-\dfrac{1}{2t}, & \tfrac14\le t\le\tfrac12,\\[4pt] \dfrac1t-1, & \tfrac12\lt t\le1,\\[4pt] 0, & \text{otherwise.} \end{cases}
```

Its Mellin transform is

```math
M(s)=\int_0^\infty W(t)\,t^{s-1}\,dt=\frac{(1-2^{-s})(1-2^{1-s})}{s(s-1)},\qquad M(1)=c.
```

**The prime-power margin.** For $`x\gt 0`$ set

```math
D(x)=c\,x-\sum_{n}\Lambda(n)\,W(n/x),
```

which is positive when there are fewer weighted prime powers in $[x/4,x]$ than average. The **sum over primes** leaves out prime squares and higher powers:

```math
P(y)=\sum_{y\lt p\lt 4y}(\log p)\,W\!\left(\frac{p}{4y}\right).
```

The prime powers add at most $\psi(x)-\vartheta(x)=O(\sqrt x)$ to $P(x/4)$, so the two margins are within $O(\sqrt x)$ of each other.

**Blocks.** A *block* is a finite integer interval $[K,K^2]$. A property holds *on arbitrarily late blocks* if for every $m$ there is $K\ge m$ such that the property holds at every integer of $[K,K^2]$. Any constant in a criterion has to be fixed before $K$ is chosen. If it could depend on the block, it could be set to the biggest error on that block (Lemma 4.2).

**Proof labels.** *Lean, unconditional* is a Lean theorem with no mathematical hypothesis. *Lean, implication* means the theorem assumes something, and I say what. *Lean, equivalence* means both directions of $P\leftrightarrow\mathrm{RH}$ are proved. *From the archive* means the Lean proof uses Alpöge's archive. *Paper proof* means I've written the argument out but haven't put it in Lean. *Open* means I don't have a proof. Where RH already gives the statement, *Open* means I don't have a direct one.

# 3. Prime windows

**Proposition 3.1 (Symmetry).** If $\zeta(s)\neq0$ whenever $`\mathrm{Re}\,s\gt 1/2`$ and $s\ne1$, then RH holds. *Lean, implication.*

*Proof.* The completed function $\xi$ satisfies $\xi(1-s)=\xi(s)$. A nontrivial zero to the left of the critical line reflects to one on the right. The trivial zeros and $s=0$ come from poles of the Gamma factor, so they're dealt with separately.

**Theorem 3.2 (Window criterion).** Fix $`\delta\gt 0`$. Suppose that for every $X_0$ there is $X\ge X_0$ with

$$ P(x/4)\le \frac{x}{2}\log 2\qquad\text{for every real } x\in[X,X^{1+\delta}]. $$

Then RH holds. *Lean, implication.* [Prime window criterion](https://doi.org/10.5281/zenodo.24412819)

*Proof.* Suppose $\zeta(\rho)=0$ with $`\mathrm{Re}\,\rho\gt 1/2`$.

On the windows in the hypothesis, $P(x/4)\le cx$. Adding back the higher prime powers costs at most $O(\sqrt x)$, so $D(x)\ge-C\sqrt x$ throughout each window.

The zero $\rho$ shows up in the Mellin transform of the margin too. For $`\mathrm{Re}\,s\gt 1`$,

```math
\int_1^\infty D(x)\,x^{-s-1}\,dx=\frac{c}{s-1}+M(s)\,\frac{\zeta'(s)}{\zeta(s)},
```

since $`\int_0^\infty W(n/x)\,x^{-s-1}\,dx=n^{-s}M(s)`$. The poles at $s=1$ cancel, because $M(1)=c$. At $\rho$ the right-hand side has a pole of residue $`\mathrm{ord}_\rho(\zeta)\,M(\rho)`$, which is nonzero: on $`0\lt \mathrm{Re}\,s\lt 1`$ we have $`|2^{-s}|\lt 1\lt |2^{1-s}|`$, so neither factor of $M$ vanishes.

In Lean I find the same pole through the centred ramp $G$ from §1.2. The ramp and the tent margin are related exactly by

$$ D(4y)=-G(4y)+3G(2y)-2G(y). $$

In the variable $\log y$ this multiplies the Laplace transform of $G$ by $(1-2^{-s})(2^{1-s}-1)$, which has no zero in the open critical strip and is positive on $(0,1)$. So any pole of the transform of $G$ in the strip is also a pole of the transform of $D$, in the same place. I call this the *delayed-difference transfer*. [Archived proof](https://doi.org/10.5281/zenodo.24410863)

Next I use the local oscillation theorem of Kaczorowski and Pintz. $\zeta$ has no real zeros in $(0,1)$, so there's no real pole, and the margin has to take both signs. For $`1/2\lt\theta\lt\mathrm{Re}\,\rho`$, some $x$ in every sufficiently late interval $[X,X^{1+\delta}]$ satisfies $`D(x)\lt -x^\theta`$. Since $x^\theta$ eventually beats $C\sqrt x$, that contradicts the lower bound on our windows. The argument still works with the weaker lower bound $D(x)\ge-x^{\theta'}$ for any $`\theta'\lt\mathrm{Re}\,\rho`$, and Theorems 4.1 and 7.1 use it that way.

So $\zeta$ has no zero to the right of the critical line, and Proposition 3.1 gives RH.

*Remark 3.3 (Converse).* Under RH, $`P(y)\lt 2y\log2`$ for every sufficiently large $y$. So the windows in Theorem 3.2 exist for every $`\delta\gt 0`$, and the window condition is equivalent to RH. *Lean, equivalence.*

The truncated explicit formula, cut at height $y$, gives $`D(4y)=\mathrm{Re}\!\left(\sum_\rho m_\rho M(\rho)(4y)^\rho\right)`$ up to $`O(\log^2y)`$, where $`m_\rho`$ is the multiplicity of the zero $`\rho`$. Under RH each term has size $`2\sqrt y\,m_\rho\lvert M(\rho)\rvert`$, and the critical-line mass identity bounds their total by $`(6\sqrt2-8-0.2199)\sqrt y\lt 0.266\sqrt y`$. The squares of the primes between $`1.125\sqrt y`$ and $`1.875\sqrt y`$ add at least $`0.3\sqrt y`$ to the prime-power sum, by the prime number theorem. That leaves $`2y\log2-P(y)\ge 0.034\sqrt y-O(\log^2y)`$.

The bound holds for every real $`y\gt 0`$ too, with margin above $0.2\sqrt y$ for $y\ge10^{16}$. *Paper proof*, from the explicit formula, Schoenfeld's inequalities and two finite certificates.

**Theorem 3.4 (Integer positions).** Call an integer $j$ *passing* if $P(j/4)\le (j/2)\log2$.

(a) If, for arbitrarily large $N$, every integer of $[N,N^2]$ passes, then RH holds.

(b) For integers $a\le b$, every integer of $[a,b]$ passes if and only if $a$ and $b$ pass and every doubled prime $2p\in(a,b)$ passes.

In Lean, (a) is an implication and (b) is unconditional.

*Proof.* Each prime's weight $W(p/(4y))$ is piecewise linear in $y$, with corners only where $`4y\in\{p,2p,4p\}`$. So the margin $2y\log2-P(y)$ is a straight line between consecutive integer values of $4y$, and checking the integers in $[N,N^2]$ gives the inequality for all real $x$ in the window of Theorem 3.2 with $\delta=1$. That's (a). The margin only bends upwards at the peaks $4y=2p$, so by discrete concavity its first interior minimum can't be at an integer that isn't a doubled prime. That's (b).

*Remark 3.5.* Clearing logarithms turns "$j$ passes" into an exact inequality between integers,

```math
\prod_{p\le j}p^{(D_j/p)\,h(j,p)}\le 2^{jD_j},\qquad D_j=\prod_{p\le j}p,
```

with integer exponents $h(j,p)$. If RH fails, every sufficiently late block contains both passing and failing integers. *Lean, unconditional.*

*Remark 3.6.* For the centred ramp $G(x)=\sum_{n\le x}\Lambda(n)(x/n-1)-x\log x+(1+\gamma)x$ and $`1/2\le\theta_0\lt 1`$, the following conditions are equivalent.

1. $G(x)\le x^\theta$ throughout arbitrarily late windows $[Y,Y^{3/2}]$ for every $\theta\in(\theta_0,1)$.
2. $\zeta(s)\ne0$ for $`\mathrm{Re}\,s\gt \theta_0`$.
3. $|G(x)|\le C_\theta x^\theta$ for all $x\ge1$ and every $\theta\in(\theta_0,1)$.

At $\theta_0=1/2$ the windows are equivalent to RH. *Lean, equivalence*, from Mathlib and the project's zeta modules.

# 4. Square blocks

Between $k^2$ and $(k+1)^2$ I know how far the margin can bend away from the line joining its endpoint values. The error in that comparison only grows logarithmically, so it's enough to test at the squares.

**Theorem 4.1 (Square-block criterion).** RH holds if and only if there is a constant $C$ such that, for arbitrarily large $K$,

```math
D(k^2)\ge -C\,k\qquad\text{for every integer } k\in[K,K^2].
```

*Lean, equivalence.*

*Proof.* ($\Leftarrow$) Between consecutive squares $a=n^2$ and $b=(n+1)^2$ the margin is piecewise linear, with $O(n)$ corners, each changing the slope by $O((\log b)/a)$. Comparing with the chord gives

$$ \min(D(a),D(b))-72\log b\ \le\ D(x)\ \le\ \max(D(a),D(b))+72\log b\qquad(a\le x\le b). $$

Since $\log b=o(\sqrt x)$, the bound $-Ck$ at the squares of a block $[K,K^2]$ carries over to $D(x)\ge-(C+\varepsilon)\sqrt x$ for every $x\in[K^2,K^4]$. That's the lower bound the proof of Theorem 3.2 needs on the windows $[K^2,K^4]$, so RH follows.

($\Rightarrow$) Under RH, integrating $(\psi(t)-t)/t^2$ twice in the explicit formula bounds the contribution of each zero $\rho$ to $D(x)$ by $O\big(x^{1/2}/|\rho(\rho-1)|\big)$. The sum $\sum_\rho|\rho(\rho-1)|^{-1}$ converges, so $|D(k^2)|\le Ck$ for all $k\ge3$.

**Lemma 4.2.** For every real sequence there is a block-dependent allowance under which the condition of Theorem 4.1 holds. *Lean, unconditional.*

*Attribution.* Earlier square-sampling and prime-centre observations are due to `bramble_trace`. The square-block criterion was published in the [fourth-power release](https://doi.org/10.5281/zenodo.24426583).

# 5. Möbius inversion

At a square $k^2$ the margin still involves all the prime powers in the tent. I use the identity $\Lambda=\mu*\log$ to replace that count by a sum over integers. The function $R$ below stays bounded, so if the sum gets large it's because its terms aren't cancelling enough.

**Proposition 5.1 (Möbius inversion).** Let $A=c(1+\gamma-c)$, let $H_N$ be the $N$-th harmonic number, and set

```math
R(x)=c\,x\,H_{\lfloor x\rfloor}-\sum_{d\le x}(\log d)\,W(d/x)-A\lfloor x\rfloor.
```

Then $|R(x)|\le 100$ for $x\ge1$, and

```math
D(x)=A+\sum_{1\le d\le x}\mu(d)\,R(x/d)\qquad(x\ge1).
```

*Lean, unconditional.*

*Proof.* Since $\Lambda=\mu*\log$, summing $D(x/n)$ over $n\le x$ replaces $\Lambda(n)$ by $\log n$ and produces $`c\,x\,H_{\lfloor x\rfloor}`$ minus a logarithmic tent sum. Taking off the main term $A\lfloor x\rfloor$ leaves $R$, and Euler-Maclaurin bounds it by 100. Möbius inversion, using $\sum_{d\le x}\mu(d)\lfloor x/d\rfloor=1$, gets $D$ back.

**Corollary 5.2 (Large-divisor tail).** At $x=k^2$ the divisors $d\le k$ contribute at most $100k$ in absolute value. With

```math
T(k)=\sum_{k\lt d\le k^2}\mu(d)\,R(k^2/d),\qquad |D(k^2)-A-T(k)|\le 100k,
```

RH holds if and only if some constant $B$ gives $T(k)\ge -Bk$ throughout arbitrarily late blocks. *Lean, equivalence.*

*Proof.* There are at most $k$ small divisors and $|R|\le100$. Dropping them moves the margin by at most a constant times $k$, the same allowance as in Theorem 4.1.

**Proposition 5.3 (Doubling pairs).** On $`3\le t\lt 4`$ the affine difference $R(t)-R(t/2)$ vanishes at a point $r\in[28/9,4)$. Pairing odd $d$ near $k^2/r$ with $2d$, for which $\mu(2d)=-\mu(d)$, reduces a group of terms with at least $k\lfloor\sqrt k\rfloor/1728$ of unsigned mass to a signed sum of absolute value at most $16k$. The *unpaired remainder* $U(k)$, the tail $T(k)$ with these pairs removed, lies within $117k$ of $D(k^2)$, and RH holds if and only if $U(k)\ge-Bk$ throughout arbitrarily late blocks for some $B$. *Lean, equivalence.*

*Remark 5.4.* Grouping the terms with a prime factor $`p\gt k`$ gives

```math
D(k^2)=A+S(k)-\sum_{k\lt p\le k^2}\big(D(k^2/p)-A\big).
```

The prime sum has unsigned weight at least $k^2/(1280\log k^2)$. So it has to cancel a lot to stay within $O(k)$. *Lean, unconditional.*

# 6. Fourth powers

**Theorem 6.1 (Fourth-power criterion).** For $`s\in\{+1,-1\}`$ let

```math
L_s(m)=\sum_{n=m}^{m^2}\frac{\max\big(s\,U(n^2),0\big)}{n^3},
```

Here $U(n^2)$ samples the remainder at $x=n^4$. With $s=-1$ a sample only counts when $U(n^2)$ is negative, and with $s=+1$ only when it's positive. Either sign gives the same equivalence.

1. RH.
2. there is $C\ge0$ with $L_s(m)\le C(1+2\log m)$ for arbitrarily large $m$.
3. for every $`\varepsilon\gt 0`$ there are arbitrarily large $m$ with $L_s(m)\le m^\varepsilon$.

*Lean, equivalence.*

*Proof.* Under RH, $|D(n^4)|\ll n^2$, so each summand is $O(1/n)$ and $L_s(m)=O(\log m)$. That's (2), and (3) follows because any positive power of $m$ eventually beats $\log m$.

For the converse, suppose RH fails, and pick a zero $\rho$ with $`\mathrm{Re}\,\rho`$ close to the supremum of $`\mathrm{Re}\,s`$ over all zeros $s$. The explicit formula then gives excursions of both signs on intervals $[x,x+x^{1-h}]$, of normalised height $x^{4h}$ for some $`h\gt 0`$. Each such interval inside $[m^4,m^8]$ contains about $x^{1/4-2h}$ fourth powers, whose $n^{-3}$-weighted contribution exceeds $m^h$ up to a factor $2(1+2\log m)$. So $`L_s(m)\gt m^{j}`$ on every late block for some fixed $`j\gt 0`$, contradicting (3).

*Attribution.* [First release](https://doi.org/10.5281/zenodo.24426583) and [revised release](https://doi.org/10.5281/zenodo.24428032). David Sanftenberg's related criterion for positive shortfalls in the prime count gives a parallel route at $s=+1$.

# 7. Level-set frequencies

At each fourth power I take the amount by which the retained Möbius sum falls below zero (zero if the sum is positive) and divide by $n^2$ to get $z_n$. For $n\ge10^5$ the retained sum is over $`n^3e^{\sqrt{\log n}}\lt d\le n^4/2`$ with the doubling pairs of Proposition 5.3 removed. To see how often $z_n$ goes above $t$ on a block, I count each such $n$ with weight $1/n$:

```math
H_m(t)=\sum_{\substack{m\le n\le m^2\\ z_n\gt t}}\frac1n.
```

**Theorem 7.1 (Level-set frequencies).** RH holds if and only if for every $`\delta\gt 0`$ there is $`C_\delta\gt 0`$ such that, for arbitrarily large $m$,

```math
t\,H_m(t)\le C_\delta\,m^\delta\qquad\text{for every } t=2^k,\ k\ge0,
```

with the same $m$ for all levels. *Lean, equivalence.*

*Proof.* A sample of size $z_n$ counts at every dyadic level below it. Adding up those levels, with weight $1/n$, gives back its share of $\sum z_n/n$, up to a factor of two and an $O(1/n)$ allowance for the bottom level. Over the whole block that allowance is $O(\log m)$. Since $z_n\le n^2$ for large $n$, there are at most $1+8\log m$ non-empty levels. A log factor disappears into any spare positive power of $m$, so the bounds at every positive exponent are equivalent to condition (3) of Theorem 6.1 with $s=-1$.

# 8. Dyadic shells

At a given $n$ I split the divisor sum at $n^4/2$, then at $n^4/4$, and keep halving. Each piece is a dyadic shell. For $`0\le j\lt B_n`$, where $B_n=1+\lfloor\log_2 n^4\rfloor$, its signed contribution is

```math
F_j(n)=\sum_{n^4/2^{j+1}\lt d\le n^4/2^j}\mu(d)\,H\!\left(\frac{n^4}{d}\right),
```

where $H$ is Sanftenberg's corrected fixed-band kernel (Appendix B). I use the most negative shell at each sample to define the **shell score**

```math
Z(n)=\frac{4B_n}{n^2}\max_{0\le j\lt B_n}\big(-F_j(n)\big).
```

The $j=0$ shell contributes zero, so $Z(n)$ is never negative. Which shell wins depends only on $n$. I write $H^Z_m(t)$ for the same weighted count as in §7, but counting samples with $`Z(n)\gt t`$.

**Theorem 8.1 (Shell criterion).** If for every $`\delta\gt 0`$ there is $`C_\delta\gt 0`$ such that, for arbitrarily large $m$,

```math
t\,H^Z_m(t)\le C_\delta\,m^\delta\qquad\text{for every } t=2^k,\ k\ge0,
```

then RH holds. *Lean, implication.* Theorem 10.2 proves the converse.

To compare a big negative excursion with a single shell, I first split the odd divisors from the even ones.

**Lemma 8.2 (Parity decomposition).** Partition the retained divisors into the $B_n$ bands $S_j$ according to $\lfloor n^4/d\rfloor$. Because $\mu(2r)=-\mu(r)$ for odd $r$ and $\mu(4r)=0$, each band is an odd-divisor sum $O_j$ minus an odd-cofactor sum $P_j$. If $`z_n\gt t`$, some band crosses its share $`\sigma=t\,n^2/(4B_n)`$:

```math
O_j\lt -\sigma\qquad\text{or}\qquad P_j\gt \sigma.
```

*Lean, unconditional.*

**Lemma 8.3 (Halving depths).** Let $T_i$ be the signed sum over the divisors of a band halved $i$ times, so that $O=\sum_{i\ge0}T_i$, $P=\sum_{i\ge1}T_i$ and $T_0=O-P$. An even divisor at depth $i$ cancels its odd half at depth $i+1$, and no two elements of one band at one depth differ by a factor $2^r$ with $r\ge1$. So every excursion at level $t$ either sets off a small-divisor event that's already handled at level $t/2$, or forces $`T_0\lt -\sigma`$ in some band. *Lean, unconditional.*

**Lemma 8.4 (Complete shells).** The kernel decays fast enough to bound every shell with $2^j\ge n^{1-3\delta/16}$. For large $n$ the lower divisor cut-offs of the earlier steps lie strictly below $n^4/2^{j+1}$ on all remaining shells, so those shells are complete dyadic intervals weighted by $H$. *Lean, unconditional.*

*Proof of Theorem 8.1.* By Lemmas 8.2 to 8.4, if $z_n$ crosses level $t$ then $Z(n)$ crosses a comparable level, apart from events already handled at level $t/2$ and on the high shells. Adding up over dyadic levels, the hypothesis on $Z$ gives the bound of Theorem 7.1 at every $`\delta\gt 0`$, and RH follows. Because the score takes the maximum over all shells, $\delta$ doesn't appear in it.

# 9. Far pairs

At a sample $n$ with $`Z(n)\gt t\ge1`$, let $j$ be the least shell attaining $Z(n)$ and write $w_d=\mu(d)H(n^4/d)$, so that $F_j(n)^2=\sum_{d,e}w_dw_e$. Each pair gets the sample weight

$$ \frac1n\cdot\frac{t}{Z(n)^2}\left(\frac{4B_n}{n^2}\right)^2. $$

To compare two divisors, first divide both by their greatest common divisor $g$. If $(d,e)=(ga,gb)$, their *reduced gap* is $|a-b|$. For example, $30$ and $36$ have reduced gap $1$. For $Q=2^j$ and $\eta\ge0$ set

```math
R_\eta=\left\lfloor\frac{t\,n^{\eta}\,Q^3}{(1+\log Q)^2}\right\rfloor.
```

**Theorem 9.1 (Far-pair criterion).**

(a) Summed over all pairs in the shell and over $n\in[m,m^2]$, the weighted squares equal $`t\,H^Z_m(t)`$. *Lean, unconditional.*

(b) If $`0\le\eta\lt \delta/2`$, the pairs with reduced gap at most $R_\eta$ contribute at most $m^\delta$ in absolute value on every sufficiently late block, uniformly in real $t\ge1$. *Lean, unconditional.*

(c) Let $\mathrm{farGapMass}(\delta,m,t)$ be the weighted signed sum over the pairs with reduced gap above $R_{\delta/4}$. The hypothesis of Theorem 8.1 holds if and only if for every $`\delta\gt 0`$ there is $C_\delta$ with $\mathrm{farGapMass}(\delta,m,2^k)\le C_\delta m^\delta$ for all $k\ge0$, for arbitrarily large $m$. *Lean, unconditional.* Hence this far-pair bound implies RH. *Lean, implication.*

*Proof.* (a) Dividing by the actual $Z(n)^2$ scales each crossing sample to $t/n$, with no second-moment assumption needed. (b) Let $U=\lfloor n^4/Q\rfloor$. For fixed $g$ there are at most $\lfloor U/g\rfloor$ choices of $\max(a,b)$ and $2R_\eta$ of the partner, so at most $U[1+2R_\eta(1+\log U)]$ close pairs. The kernel bound $K^2(1+\log Q)^2/Q^2$ cancels the factor $Q^3/(1+\log Q)^2$ in $R_\eta$ against $U\le n^4/Q$, bounding the close-pair sum by $`O(t\,n^{4+\eta+\kappa})`$ for every $`\kappa\gt 0`$. Since $`t/Z(n)^2\lt 1/t`$ at a crossing, the weighted sum over $[m,m^2]$ is $O(B_n^2n^{\eta+\kappa-1})$ summed, which stays below $m^\delta$ when $`2\eta\lt \delta`$. (c) Subtract (b) from (a).

*Remark 9.2.* For squarefree $g$ coprime to $ab$, $\mu(ga)\mu(gb)=\mu(a)\mu(b)$: the sign of a pair is constant along its ray. In a single shell, reduced pairs with $\max(a,b)\le5$ have $\mu(d)\mu(e)\ge0$, and $(5,6)$ is the smallest reduced pair of negative sign. *Lean, unconditional.*

# 10. First moments

You can also state the condition without picking a level $t$. Add up the shell scores on a block, weighting the sample at $n$ by $1/n$, to get the harmonic first moment

$$ \Phi(m)=\sum_{n=m}^{m^2}\frac{Z(n)}{n}. $$

**Theorem 10.1 (First-moment criterion).** The hypothesis of Theorem 8.1 holds if and only if, for every $`\varepsilon\gt 0`$, there are arbitrarily large $m$ with $\Phi(m)\le m^\varepsilon$. At any fixed $`\delta\gt 0`$, restricting the maximum in $Z(n)$ to shells with $`2^j\lt n^{1-3\delta/16}`$ gives an equivalent condition. So the first-moment bound implies RH. *Lean, implication.*

*Proof.* Since $Z\ge0$, Markov's inequality gives $`t\,H^Z_m(t)\le\Phi(m)`$ at every level on the same block. Conversely, one crossing $`Z(n)\gt t`$ on $[m,m^2]$ contributes at least $1/m^2$ to $H^Z_m(t)$, so $`t\,H^Z_m(t)\le C m^\delta`$ bounds $Z$ polynomially on the block, leaves $O(\log m)$ non-empty levels, and gives $\Phi(m)\ll m^\delta\log m$. The kernel's decay bounds the high shells.

**Theorem 10.2 (Converse).** Let $1/2\le\theta\le1$ and suppose $\zeta(s)\ne0$ for $`\mathrm{Re}\,s\gt \theta`$. Then for every $`\delta\gt 8\theta-4`$, on every sufficiently late block,

```math
t\,H^Z_m(t)\le 2\,m^\delta\qquad\text{for every } t\gt 0.
```

*Lean, implication.* With $\theta=1/2$, RH is equivalent to each of the conditions in Theorems 8.1, 9.1(c) and 10.1. *Lean, equivalence.*

*Proof.* A zero-free half-plane $`\mathrm{Re}\,s\gt \theta`$ gives $|M(N)|\le C(N+1)^{\theta+\varepsilon}$ for the Mertens function, by Littlewood's smoothed Perron argument for $1/\zeta$. The Lean project proves that from Mathlib alone, using the Borel-Carathéodory inequality, Hadamard's three-lines theorem and truncated Perron inversion. Abel summation against the kernel bounds each shell sum $F_j(n)$ by $O(n^{4\theta+\varepsilon})$, so $Z(n)=O(n^{4\theta-2+\varepsilon})$. On the block $n\le m^2$ this is $O(m^{8\theta-4+2\varepsilon})$, and as $`t\,H^Z_m(t)\le\max_n Z(n)\sum_{n=m}^{m^2}1/n`$, the frequency bound follows for every $`\delta\gt 8\theta-4`$.

**Corollary 10.3 (The Crossley Criteria).** RH is equivalent to each of the square-block and fourth-power conditions (Theorems 4.1 and 6.1), the level-set condition (Theorem 7.1) and the shell, far-pair and first-moment conditions (Theorems 8.1, 9.1(c) and 10.1). It's also equivalent to the window condition of Theorem 3.2 for every $`\delta\gt 0`$, by Remark 3.3.

# 11. Arithmetic inequality

Theorem 10.2 gives the next inequality if I assume RH. To run the proof in the other direction I need to bound the signed sums over divisors directly.

**The inequality.** For every real $`\delta\gt 0`$ there are $`C_\delta\gt 0`$ and arbitrarily large integers $m$ such that

```math
t\sum_{\substack{m\le n\le m^2\\ Z(n)\gt t}}\frac1n\ \le\ C_\delta\,m^\delta\qquad\text{for every } t=2^k,\ k\ge0.
```

For a fixed $\delta$, I need blocks starting arbitrarily far out on which one constant $C_\delta$ works at every level $t$. Raising $t$ leaves fewer terms in the sum, but multiplies their combined weight by a larger number. I need to bound that product for the worst shell at each sample, and I can't yet. I don't have a direct proof.

## 11.1 Available bounds

- **Exponent 4.** Without any hypothesis on zeros, the first moment satisfies $\Phi(m)\le Dm^4\exp\big(-c(\log m)^{1/3}\big)$ on every late block, from Sanftenberg's contour bound for Möbius prefixes. That doesn't get the exponent below 4. *Lean, unconditional.*
- **High shells and close pairs.** For every $`\delta\gt 0`$ the shells with $2^j\ge n^{1-b}$, $`0\le b\lt \delta/4`$, and the divisor pairs of small reduced gap (Theorem 9.1(b)) contribute at most $m^\delta$ on every late block. *Lean, unconditional.*
- **Exponents above $8\beta-4$.** Bebel's certified zero-free strip, with boundary $\beta\approx0.8733458561$, gives the inequality at every exponent above $8\beta-4\approx2.98677$ through Theorem 10.2. *Lean, implication*, from Bebel's theorem. To push that method past $349/400$ I'd need an energy bound for cubic Gauss sums twisted by quadratic symbols, and the quadratic large sieve doesn't give a strong enough one. Dunn and Radziwiłł's bilinear estimates don't get there either: their asymptotics assume GRH, and their unconditional result averages over cubic characters. Poisson summation in the moduli just turns the bound into a quadratic large sieve with the two lengths swapped, which is the same problem again. Multiple Dirichlet series, bilinear splitting and pointwise correlation bounds all get stuck at the same point. *Paper proof.*

## 11.2 Exponent 2.98

In Lean, `ConvertedThetaWindows.full_shell_298` gives the shell inequality at $`\delta=2.98`$. It uses Theorem 1.2 at $`87/100`$. The same window gives $`\zeta(s)\ne0`$ for $`\mathrm{Re}\,s\ge349/400`$, `ConvertedThetaWindows.zero_free_349_400`. *Lean, unconditional, from the archive.*

$2.98$ is just under the $2.98677$ that Bebel's strip gives. Proving the inequality at $\delta=2.98$, and nothing more, would, by the first-shell converse, rule out zeros of $\zeta$ to the right of the line $`\mathrm{Re}\,s=349/400=0.8725`$. In Lean that converse assumes the localised oscillation theorem of Kaczorowski and Pintz.

For the calculation at $\delta=2.98$ I took Bebel's two zero-free estimates as hypotheses in Lean, which lets me bound the sum over the following ranges.

1. The zero-free strip bounds the shells with $Q=2^j\ge n^{10/2581}$.
2. Bilinear dispersion bounds the contribution from cofactors $b\le n^{183/50}Q^{-1/3}/B_n^4$.
3. A Perron contour extends the cofactor range to $n^{3.9909}Q^{4/3}$.
4. Just counting is enough for cofactors divisible by a prime in the sparse moving set, and for the cap at the top of the first shell.
5. On every block the estimate covers samples up to $\lfloor m^\lambda\rfloor$, where $\lambda=5960000/2986767\approx1.99547$.

For the remaining samples I still need to bound the positive maximum over shells $`2\le Q\lt n^{10/2581}`$ of the signed sums of $\mu$ over the cofactors $`n^{3.9909}Q^{4/3}\lt b\le n^4/(6Q)`$ that avoid the moving primes, for the samples $`\lfloor m^\lambda\rfloor\lt n\le m^2`$. As $m$ grows, the proportion of samples left tends to one. The complementary multiplier $k=d/b$ satisfies $`6\le k\lt n^{0.0091}/Q^{7/3}`$, and that range gets longer as $n$ grows.

I checked the Lean export of Bebel's theorem together with these head and tail statements, in one environment of 149,686 declarations.

I've also shown in Lean that any of three other bounds would be enough at $\delta=2.98$. A window bound $G(x)\le x^\theta$ at one $`\theta\lt 349/400`$ gives the inequality on every late block, with no declaration from the archive. A signed bound $O(X^{2001/2000})$ on the correlations $\mu(d)\mu(d+h)$ inside short intervals of a dyadic grid gives $M(N)\ll(N+1)^{3489/4000}$ and hence the inequality. A count of exceptional cells gives it too, and reduces, at one sample per cell, to a signed bound $O(X^{1.873})$ on long-shift correlations in the shells $`Q\lt X^{0.065}`$. Pairing rows of opposite Möbius sign gets rid of every correlation that touches a matched row. I can't prove any of the three bounds. *Lean, implication.*

## 11.3 Sparse samples

The arithmetic inequality, the window bounds of Remark 3.6 and RH are also equivalent to a statement about finitely many samples per block. For $`0\lt \theta\lt 1`$, $c\ge0$ and an integer $L$, let

```math
N_{\theta,c}(L)=\#\big\{k\in[L^2,L^3]:\ G(k^4)\gt c\,k^{4\theta}\big\}
```

count the fourth powers at which the centred ramp $G$ fails the bound $`c\,x^\theta`$.

**Theorem 11.1 (Sparse failures).** RH holds if and only if for every $\theta\in(1/2,1)$ there are $`\varepsilon\gt 0`$ and $c\ge0$ with $N_{\theta,c}(L)\le L^{3-\varepsilon}$ for arbitrarily large $L$. At the single exponent $\theta=8699/10000$, the bound $N_{\theta,1/2}(L)\le L^{2.99}$ for arbitrarily large $L$ gives $|G(x)|\le x^{0.87}/2$ for all large $x$ and the arithmetic inequality at $\delta=2.98$. *Lean, equivalence*, from Mathlib and the project's zeta modules alone.

*Proof sketch.* The uncentred ramp is convex, because $\Lambda\ge0$, so between consecutive fourth powers the excess of $G$ over its chord is at most $\big((k+1)^4-k^4\big)^2/(4k^4)\le\tfrac{225}{4}k^2$, which is $o(k^{4\theta})$ for every $`\theta\gt 1/2`$. Conversely, a zero $\rho$ with $`\mathrm{Re}\,\rho\gt\theta`$ forces $`G(x)\gt c\,x^\theta`$ on a set of measure more than $Y^{1+d-\varepsilon}$ in every late window $[Y,Y^{1+d}]$, and that few failing samples can't cover it.

I can prove the ramp bound arithmetically, but only on a short stretch of each window.

**Proposition 11.2 (Good intervals).** For every fixed $`0\lt \theta\lt 1`$, every sufficiently late window $[R,R^{3/2}]$ contains an interval $[Y,Y+Y^\theta/16]$ on which $G(x)\le x^\theta$. *Lean, unconditional.* A point with $`G(Y)\lt Y^\theta/2`$ exists by Landau's theorem, and the one-sided slope bound $G(y)-G(x)\le8(y-x)$, from $\sum_{d\mid n}\Lambda(d)=\log n$ and Chebyshev's bound, carries it across the interval. As $R$ grows, the fraction of the window covered by this interval tends to zero.

**Proposition 11.3 (Fifteenth-power quadrature).** Let $`E(x)=\max\big(0,\,P(x/4)-(x/2)\log2\big)`$, $A_k=k^{15}$ and $Y=K^{30}$, and put $\theta=2181/2500$. On every sufficiently late window,

```math
\int_Y^{Y^{3/2}}E(x)\,x^{-\theta}\,\frac{dx}{x}\ \le\ \sum_{k=K^2}^{K^3-1}\log\frac{A_{k+1}}{A_k}\,A_k^{-\theta}\max\{E(A_k),E(A_{k+1})\}\ +\ \frac{\log Y}{2}\,Y^{-43/15000}.
```

*Lean, unconditional.* So $K^3-K^2+1$ samples are enough to bound the integral over the whole window. If the weighted sum grows more slowly than every positive power of $Y$ along arbitrarily late windows, the arithmetic inequality follows at $\delta=2.98$. I can't prove that sampled bound.

**Proposition 11.4 (Signed tent windows).** Let $F(x)=P(x/4)-\tfrac{x}{2}\log2$ for the tent-weighted sum over primes, put $x_n=n^4$, $w_n=x_n^{-\theta}\log(x_{n+1}/x_n)$ and $v_n=\max(F(x_n),F(x_{n+1}))$, and fix $`3/4\lt \theta\lt 1`$. For arbitrarily large $m$,

```math
\sum_{n=m}^{m^2-1}w_n v_n\ \le\ C_\theta\,m^{3-4\theta},
```

with $C_\theta$ depending only on $\theta$. *Paper proof*, from the Euler product and the real-axis form of Landau's theorem, with no zero-free region and no finite-height zero data. The sum is signed and can be negative. The positive budget, which is what would give the window bound for the tent, is bigger by exactly $\sum_n w_n\min\big([-F(x_n)]_+,[-F(x_{n+1})]_+\big)$, the deficits shared by both ends of a cell. I don't have a subpower bound for that term on the same blocks.

**Proposition 11.5 (The upper edge and interior runs).** Keep the notation of Proposition 11.4 with $\theta=2181/2500$, block $[m,M]$ for $M=m^2$, and write $P_\theta(a,b)$ for the positive budget over the cells $`a\le n\lt b`$. Call a sample $k$ high when $`[F(k^4)]_+\gt(\log m)^2(k^4)^\theta`$, and low otherwise.

(a) *Upper edge.* For fixed $`0\lt e,\nu\lt 1`$ and every large $T$, at least $\lfloor T^{1-\nu}\rfloor$ consecutive integers $m\in[T,2T]$ satisfy $P_\theta(M-\lfloor m^{2-e}\rfloor,M)\ll_\theta m^{-e}$. The right end is exactly $m^2$.

(b) *Short runs.* If every index strictly between $u$ and $v$ is high, then $`v/u\lt 126/125`$ for all large $m$.

(c) *One interior run decides.* Let $R_e(m)$ be the largest $P_\theta(u,v)$ over $`m\lt u\lt v\lt M`$ with low endpoints, high samples between them and $v-u\ge\lfloor m^{2-e}\rfloor$. Then $\log(1+R_e(m))/\log m\to8\max(0,\Theta-\theta)$, where $\Theta$ is the supremum of $`\mathrm{Re}\,\rho`$ over the zeros $\rho$. So a subpower bound on $R_e(m)$ on arbitrarily late blocks is equivalent to $\zeta(s)\ne0$ for $`\mathrm{Re}\,s\gt\theta`$, and would give the benchmark at $\delta=2.98$.

*Paper proof*, from the explicit formula, the published finite-height verification and zero-density estimates, with no zero-free strip and no theta lifts. I've checked the discrete estimate for the mass of one run in Lean, with the analytic input as a hypothesis. It bounds that mass by $(1+L)d+u^{4(\beta-\theta)}d^{27/10}$, but that's only small if you already know the zeros $\rho$ satisfy $`\beta=\mathrm{Re}\,\rho`$ with $\beta$ near $\theta$. So the upper edge is fine. I'd still need a bound on one complete interior run, and that's equivalent to the zero-free line at $\theta=0.8724$.

**Proposition 11.6 (Opposite pairs).** On arbitrarily late blocks there are three squarefree composite cofactors $b,b+h,b+2h$ in the first shell with the same residue modulo $16\cdot571\cdot599$ and the same local field coefficients, whose two neighbouring pairs have the same shift and opposite Möbius products. Together they contribute at most $3/200$ of the total sample weight throughout $199m^2/200\le n\le m^2$. *Lean, unconditional.* The same construction shows you can't predict the sign of a pair from this local data alone. I can't bound the rest of the correlations.

## 11.4 Obstructions

Thirty-two approaches I tried didn't work, and for each one there's a Lean theorem or a written argument showing why. Chebyshev's bound, the unconditional zero-free estimates considered here and the short-interval bounds for Möbius sums all leave errors that are too big for the exponent I need. Pushing the cofactor estimate to the top of its range with absolute values would mean solving that Mertens problem. Replacing each of the middle and far cofactor row sums $S$ by $\max(S,0)$ loses a quartic factor.

Some model sequences meet the local conditions and still break the inequality. Pairing divisors leaves isolated prime rows of positive mass. Taking a supremum over Dirichlet twists loses cancellation between signs, and a second moment with one sample per cell can't absorb even a single off-line mode with exponent $\rho$ satisfying $`\mathrm{Re}\,\rho\gt0.8715`$. For the shell estimate I still need cancellation *between* rows, before taking the maximum at each sample.

## 11.5 Sufficient bounds

A direct proof of any one of these would finish the arithmetic proof of RH.

1. the arithmetic inequality for every $`\delta\gt 0`$, through Theorem 10.1.
2. the sparse-failure bound of Theorem 11.1 for every $\theta\in(1/2,1)$.
3. the window bound $G(x)\le x^\theta$ on arbitrarily late windows $[Y,Y^{3/2}]$ for every $`\theta\gt 1/2`$, through Remark 3.6.
4. the tent bound for primes $P(x/4)\le(x/2)\log2$ at every real $x$ in arbitrarily late windows $[X,X^{1+\delta}]$, for one fixed $`\delta\gt 0`$, through Theorem 3.2.

The fourth is the one I find easiest to state. It only counts primes, and there's no error allowed in the inequality. On an integer block, Theorem 3.4 reduces the check to the endpoints and doubled primes. Under RH the bound holds at every late scale, and Lean checks that converse (Remark 3.3). My written proof gives it at every scale, with margin above $0.2\sqrt y$ for $y\ge10^{16}$.

If I get a Lean proof along any of these routes, I'll compile it at trust level zero, replay it with `leanchecker` and go through its dependencies for anything from the archive or an earlier proof of RH. It should only use `propext`, `Classical.choice` and `Quot.sound`. Even one of the single-exponent results in §11.2 and §11.3 would push the zero-free region I can reach without the archive further out.

# 12. Lean formalisation

## 12.1 Project

Steps 0 to 9 and twenty-five modules of partial results form a Lean project of 218 modules and 42,812 lines on Lean 4.33.1 and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, in `project/`. It imports nothing outside Mathlib.

| Module group | Modules | Lines |
| -------------------------------------------------------------------------- | ----------: | -----------: |
| The reduction, Steps 0 to 7, with its audits | 125 | 18,956 |
| Steps 8 and 9 and the converse | 10 | 3,555 |
| Partial results: ramp windows, sparse fourth powers, tails of sums over primes, prime centres, tents and the critical-line mass identity | 25 | 9,503 |
| Classical inputs for zeta | 34 | 6,125 |
| Window lemma, pole data, real zeros, dyadic ramp reconstruction, the named window criterion and its converse | 16 | 3,581 |
| Compatibility layer and headline audit | 6 | 614 |
| Sanftenberg's two unchanged modules (Apache 2.0). The first row includes his three modified modules | 2 | 478 |

The classical inputs are proved from Mathlib too. For the window argument that means the Landau window lemma, the pole data for zeta and the absence of real zeros in $(0,1)$. The zero count in a unit window is at most $C\log(|t|+2)$ with multiplicity. A classical zero-free region gives the prime number theorem for the centred ramp with error $Ky\exp(-c\sqrt{\log y})$. The proof of the truncated explicit formula for $\psi(u)-u$ uses a rectangular residue theorem and gives error $u\log^2(uT)/T+\log u$.

## 12.2 Kernel checks

On 23rd November 2026 I built all 218 modules into an empty output directory, restarting once after an interruption. Each compiled at trust level zero and passed `leanchecker`. The 217-module tree before it also passed `lake build`.

The dependency audit covered twenty-six theorems, including the window and square-block criteria and the converse of the window criterion. Each depended on between 9,464 and 68,335 constants, with none from Alpöge's archive. The only axioms were `propext`, `Classical.choice` and `Quot.sound`. One module, `PrimeBand`, only compiles with warnings as errors turned off.

One small statement is different from the published version of the reduction. The pole-preservation lemma `compactDifference_zeroFree` is stated for zeta, not for an arbitrary family of Dirichlet characters, since zeta is all the reduction uses.

## 12.3 External inputs

I first proved Steps 8 and 9, and the converse of Theorem 10.2, in Lean on top of Alpöge's archive. It gave me the explicit formula, the zero counts and the prime number theorem, but not its RH theorem. Those ten modules now build and pass the kernel checker in the Mathlib-only project too. Bebel proved his zero-free strip on Lean 4.34.1, so the results in §11 that use it take it as two explicit hypotheses.

## 12.4 Window replay

The module `ConvertedThetaWindows` connects Theorem 1.2 to the project's Landau theorem. It imports four modules directly, and the verification record has SHA-256 digests for six dependencies. I compiled it with Lean 4.33.1 and the pinned Mathlib at trust level zero, with warnings as errors, and the stock checker `LeanChecker.replayFromImports` accepted it in a fresh process. The six declarations I checked for axioms, `principal_window`, `principal_window_87`, `numerical_design`, `zero_free_349_400`, `full_shell_298` and `ordinary_rh`, only use the three standard ones.

The check pulls in 9,314 records from the archive, proofs included. It doesn't rebuild every geometric proof from scratch in the same run. The archive's authors checked their own release. The dependency audit of §1.5 covers all 1,476,889 names reachable in the archived proof that Theorem 1.2 extends, the second-seed closure published in [`prime-window-rh-criterion`](https://github.com/leecrossley/prime-window-rh-criterion/tree/8f8ce11af908bb98df5c2adc2c8a72856fc2b8cd/results/geometric-window-descent).

# 13. Alpöge's proof

Alpöge works with Dirichlet characters. His last step is a Landau window lemma plus the functional equation, and for the Riemann zeta function I can use the same argument once I have Theorem 1.2.

The published Lean proof of the shell criterion reached 496 declarations in the archive, all from its classical analysis: 171 for the explicit formula and zero counts, 162 for the zero-free region and prime number theorem, 111 for the window lemma and pole data, and 52 for non-vanishing and L-function bounds. None of them were geometric, and §12 replaces every one with a proof from Mathlib alone.

Michael Rubinstein's guide deduces RH from one inequality between weighted prime sums and two estimates for Dirichlet characters. Its first step uses the ramp bound $G(x)\le x^\theta$ on $[Y,Y^{3/2}]$, the bound in Remark 3.6. The tent in Theorem 3.2 is related to this ramp by the three-scale difference in §3. Steps 2 to 9 are where my arithmetic goes past it.

# 14. Related work

- **Landau, Kaczorowski and Pintz.** Landau's theorem on the real singularity of the transform of a function of one sign, and its localised form by Kaczorowski and Pintz (Acta Math. Hungar. 48 (1986), 173-185). Theorem 3.2 rests on these.
- **One-sided criteria.** The closest published thing to Theorem 3.2 I know of is Johnston's integrated Chebyshev criterion. Suzuki's one-sided criteria for weighted von Mangoldt sums and the second-difference smoothing of Dudek, Grenié and Molteni are related too.
- **Möbius sums.** Littlewood's smoothed Perron argument gives the converse of §10. Soundararajan's bounds for partial sums of $\mu$ assume RH. Matomäki and Radziwiłł, and Matomäki, Pandey, Pliego, Teräväinen and Wang, control Möbius sums in short intervals with logarithmic rather than power savings, and Guth and Maynard's large-value estimates bound $\Lambda$ in short intervals.
- **Formal work.** Section 1.3 describes the contributions of Alpöge and Sanftenberg. Bebel certified the zero-free strip used in §11.1. OpenAI's quasi-Riemann hypothesis preprint gives a $7/8$ zero-free half-plane. OVVO Financial independently reduced the problem to square blocks and proved $\mu(b)\log b=-(\mu*\Lambda)(b)$ in Lean. For Theorem 10.2 I used a port of the Littlewood development in the HGT repository.

# 15. Limitations

The replay for Theorem 1.1 used the geometric records listed in §12.4. The paper repository includes the Landau argument, the 218-module criteria project, the source of the final theorem and its replay records. A clean checkout lacks the parent modules needed to replay that theorem. Nobody outside the project has rebuilt the joined proof from a clean checkout yet.

I still don't have a direct proof of any of the bounds in §11.5. Bebel's zero-free strip enters the estimate for exponents above $8\beta-4$ in §11.1 as an explicit hypothesis. The bound at every scale in Remark 3.3 is a written proof, as is the first-shell converse in §11.2. The Lean version of that converse takes the Kaczorowski and Pintz theorem as a hypothesis.

# 16. Build

The 218-module criteria project described in §12 is in `project/`. With Lean 4.33.1 and a built copy of the pinned Mathlib, run the following command from that directory.

```
LEAN_BIN=/path/to/toolchain/bin MATHLIB=/path/to/built/mathlib4 python3 tools/build.py
```

In that project the script compiles each module at trust level zero in dependency order, then replays it in the kernel checker. It refuses to build anything that imports from outside the project and Mathlib. `SHA256SUMS` lists the source hashes. The [paper repository](https://github.com/leecrossley/crossley-criteria-riemann-hypothesis) also keeps the Landau proof and reflection step on their own in `landau/`. For the separate replay of Theorem 1.1, `theta-window/README.md` lists the required parent modules.

# Appendix A. Lean statements

Here's the proof of Theorem 1.1 and its two corollaries, from `ConvertedThetaWindows`. `RiemannHypothesis` is Mathlib's definition, and `ThetaExplicit.ordinary_common` is Theorem 1.2.

```lean
theorem ordinary_rh : RiemannHypothesis := by
  apply RiemannReduction.rh_of_right
  intro s hs _
  obtain ⟨θ, half, upper⟩ := exists_between (lt_min hs (by norm_num : (1/2:ℝ) < 1))
  exact zero_free_of_singleHost_window
    (principal_window half (upper.trans_le (min_le_right _ _))) s
    (upper.trans_le (min_le_left _ _))

theorem zero_free_349_400 (s : ℂ) (hs : (349/400:ℝ) ≤ s.re) : riemannZeta s ≠ 0

theorem full_shell_298 :
    (∀ᶠ m : ℕ in atTop, weighted uniformShellScore m ≤ (m : ℝ)^(149/50:ℝ)) ∧
    (∀ᶠ m : ℕ in atTop, ∀ t : ℝ, 0 < t →
      t * frequency uniformShellScore m t ≤ 2*(m : ℝ)^(149/50:ℝ))
```

And the main theorems of the Crossley Criteria, from the project.

```lean
theorem rh_of_right (right : ∀ s : ℂ, 1/2 < s.re → s ≠ 1 → riemannZeta s ≠ 0) :
    RiemannHypothesis

theorem rh_of_prime_sign_windows {δ : ℝ} (hδ : 0 < δ)
    (sign : ∀ X₀ : ℝ, ∃ X ≥ X₀, ∀ x ∈ Icc X (X ^ (1 + δ)),
      primeSum (x / 4) ≤ (x / 2) * Real.log 2) : RiemannHypothesis

theorem primeSum_lt_eventually (rh : RiemannHypothesis) :
    ∀ᶠ y : ℝ in atTop, primeSum y < 2 * y * Real.log 2

theorem window_criterion_iff {δ : ℝ} (hδ : 0 < δ) :
    (∀ X₀ : ℝ, ∃ X ≥ X₀, ∀ x ∈ Icc X (X ^ (1 + δ)),
      primeSum (x / 4) ≤ (x / 2) * Real.log 2) ↔ RiemannHypothesis

theorem block_passes_iff_endpoints_and_double_primes {a b : ℕ} (hab : a ≤ b) :
    (∀ j ∈ Icc a b, Passes j) ↔
      Passes a ∧ Passes b ∧ ∀ p : ℕ, p.Prime → a < 2*p → 2*p < b → Passes (2*p)

theorem square_blocks_iff_rh :
    (∃ C, PrimeGrid.SquareBoundBlocks C) ↔ RiemannHypothesis

theorem small_divisors_cost {k : ℕ} (hk : 0 < k) :
    |PrimeGrid.powerMargin (k^2) - mainSlope - largeDivisorSum k| ≤ 100*k

theorem rh_iff_subpower_quartic_budget (s : ℝ) (sign : s=1 ∨ s= -1) :
    RiemannHypothesis ↔
      ∀ ε : ℝ, 0<ε → ∀ A : ℕ, ∃ m ≥ A, mass (signedRemainder s) m ≤ (m:ℝ)^ε

theorem rh_iff_frequency : RiemannHypothesis ↔ sameBlockWeak score

theorem rh_of_uniform_shell_score (h : sameBlockWeak uniformShellScore) :
    RiemannHypothesis

theorem rh_iff_same_block_far_gap :
    RiemannHypothesis ↔ ∀ δ > (0:ℝ), sameBlockUpper (farGapMass δ) δ

theorem rh_iff_cofinal_shell_first_moment :
    RiemannHypothesis ↔ ∀ δ > (0:ℝ), cofinalMomentBound uniformShellScore δ
```

The last two are the converse equivalences of Theorem 10.2, built in the Mathlib-only project with everything else (§12.2). The conditions are defined like this.

```lean
def sameBlockWeak (z : ℕ → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ C > (0:ℝ), ∀ A : ℕ, ∃ m ≥ A, ∀ j : ℕ,
    (2:ℝ)^j * frequency z m ((2:ℝ)^j) ≤ C*(m:ℝ)^δ

def frequency (z : ℕ → ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Icc m (m^2), if t < z n then (n:ℝ)⁻¹ else 0

def fullFirstShell (n j : ℕ) : ℝ :=
  ∑ d ∈ Ioc (n^4/2^(j+1)) (n^4/2^j), (μ d:ℝ)*surviving ((n:ℝ)^4/d)

def uniformShellScore (n : ℕ) : ℝ :=
  (range (bandCount n 0)).sup' (nonempty_range_iff.mpr (by unfold bandCount; omega))
    (fun j => -fullFirstShell n j/share n 0 1)
```

# Appendix B. Kernel

The kernel $H$ of §8 is Sanftenberg's corrected fixed-band kernel, `surviving` in the project: the centred fixed-band kernel minus its first-quotient correction,

```math
H(y)=\log2\,\big(r(y)-r(y/2)\big)-\big(\log y+\kappa\big)\,L(y)-\Big((1-\gamma)\,\Delta(y)-\int_1^2 I(y,t)\,dt\Big),
```

where $r$ is the unit ramp, $L$ the lattice function of the fixed band, $\kappa$ its logarithmic constant, $\Delta$ the lattice difference and $I$ the correction integrand, each defined in `CheckAlpogeFixedPrimeBandCentered.lean` and `CheckAlpogeFixedPrimeBandFirstQuotient.lean`. Lean bounds the correction, the second bracket, by $1500/y$ in absolute value for $`y\gt 0`$.
