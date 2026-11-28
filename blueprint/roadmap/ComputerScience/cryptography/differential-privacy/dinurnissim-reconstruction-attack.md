# Dinur–Nissim reconstruction attack

Let $d \in \{0,1\}^n$. If a mechanism's answers to all $2^n$ subset-sum queries always have distortion at most $E$, then the adversary that asks all of them and outputs the first $c \in \{0,1\}^n$, in a fixed order, whose subset sums are all within $E$ of the answers (running in exponential time) outputs a candidate that differs from $d$ in at most $4E$ positions; in particular, a mechanism whose distortion is $o(n)$ is blatantly non-private. If the distortion is $E = o(\sqrt n)$, let the adversary ask $t = n (\log n)^2$ independent uniformly random subset-sum queries $q_1, \dots, q_t$, solve the linear program $|\sum_{i \in q_j} c_i - \tilde a_{q_j}| \le E$ for $j \le t$ and $0 \le c_i \le 1$ for $i \le n$, and round each $c_i$ to $1$ if $c_i > 1/2$ and to $0$ otherwise. This adversary runs in time polynomial in $n$, each answer of the mechanism counting as one step, and for every $\varepsilon > 0$ its candidate differs from $d$ in fewer than $\varepsilon n$ positions except with probability $\mathrm{neg}(n)$ over the coin tosses of the mechanism and of the adversary, where $\mathrm{neg}(n)$ is a function that is smaller than $n^{-k}$ for all large $n$, for every $k$. Consequently, a mechanism against which every adversary running in time polynomial in $n$ fails in this sense has distortion that is not $o(\sqrt n)$.

## Expansion

This node states two results of Dinur and Nissim: Theorem 2, and Theorem 3 with its consequence. A good expansion gives each theorem a page of its own, and gives the Theorem 3 page, as a prerequisite, a page stating the machine model of its time bound: probabilistic oracle Turing machines with access to a stateful randomized mechanism, whose time complexity counts each call to the mechanism as one step, as Dinur and Nissim define the time complexity of $M^A$ (p. 204), with an encoding of the mechanism's answers as the machine's input, which the source leaves open. Its building blocks are the deterministic oracle machines of "Polynomial time with an oracle" and "Evaluation of an oracle machine with adaptive queries", whose oracle is a fixed function and in which a query costs only the time to compute it, and "Probabilistic oracle program and its semantics against a stateful handler". The Theorem 3 page also lists the Disqualifying Lemma (their Lemma 4, p. 205, proved in Appendix A, p. 209) as a proof prerequisite.

## Depends on

- [Blatant non-privacy](blatant-non-privacy-and-distortion-of-subset.md)
- [Distortion](has-distortion.md)
- [Subset-sum query](subset-sum-query.md)
- [Negligible advantage](../security-games/asymptotic-security/negligible-adv.md)
- [Probabilistic polynomial-time Turing machines](../security-games/asymptotic-security/probabilistic-polynomial-time-turing-machines.md)
- [Probabilistic oracle program and its semantics against a stateful handler](../security-games/probabilistic-oracle-programs/probabilistic-oracle-program.md)
- [Efficient adversaries](../security-games/asymptotic-security/efficient-adversaries.md)

## Proof depends on

- [Azuma's inequality](../../../Probability/concentration-inequalities/azuma-inequality.md)
- [Linear programs are solvable in polynomial time](../../../Geometry/convex-geometry/polynomial-time-linear-programming/linear-programs-are-solvable-in-polynomial-time.md)

## Comparison with the source

The conventions above are those of Dinur and Nissim. On p. 204 they define $\mathrm{neg}(n)$ by "for all $c > 0$, for all sufficiently large $n$ it holds that $\mathrm{neg}(n) < 1/n^c$", define the time complexity of an adversary $M^A$ with access to the database algorithm $A$ "as usual, where each call to $A$ costs a unit time", and call a database $t(n)$-non-private (Definition 3) if for every constant $\varepsilon > 0$ some probabilistic Turing machine $M$ with time complexity $t(n)$ satisfies $\Pr[M^A(1^n) \text{ outputs } c \text{ s.t. } \mathrm{dist}(c, d) < \varepsilon n] \ge 1 - \mathrm{neg}(n)$, where "the probability is taken over the coin tosses of $A$ and $M$". Theorem 2 (p. 204) makes a database whose answers are within $o(n)$ perturbation $\exp(n)$-non-private, and its proof (p. 205) is the adversary of the first sentence above, with $\mathrm{dist}(d, c) \le 4E$. Theorem 3 (p. 205) makes a database whose answers are within $o(\sqrt n)$ perturbation $\mathrm{poly}(n)$-non-private. Its proof asks $t = n(\log n)^2$ queries, each chosen "uniformly at random" among the subsets of $[n]$ and independently of the others, solves the linear program $\tilde a_{q_j} - E \le \sum_{i \in q_j} c_i \le \tilde a_{q_j} + E$ for $j \le t$ and $0 \le c_i \le 1$ for $i \le n$, and outputs $c'$ with "$c'_i = 1$ if $c_i > 1/2$ and $c'_i = 0$ otherwise"; the algorithm does not depend on $\varepsilon$. The proof rests on their Lemma 4 (p. 205), whose proof in Appendix A (p. 209) applies Azuma's inequality, their Theorem 1 (p. 204), to the centered partial sums of a random subset sum of the differences $x_i - d_i$; the proof solves the linear program in polynomial time without naming an algorithm or saying how the answers are encoded. Dwork and Roth (Section 8.3, p. 170) attribute to Dinur and Nissim an attack "requiring only polynomial time computation and $O(n \log^2 n)$ queries, provided the noise is always $o(\sqrt n)$".

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/Papers/privacybook.pdf>, Section 8.1, Theorem 8.1 and its proof (p. 160), and Section 8.3 (p. 170)
- I. Dinur and K. Nissim, "Revealing information while preserving privacy", *Proceedings of the 22nd ACM PODS*, 2003, pp. 202–210, doi:10.1145/773153.773173: the notation $\mathrm{neg}(n)$, Definitions 2 and 3 and Theorems 1 and 2 (p. 204), the proof of Theorem 2 and Theorem 3 with its proof and Lemma 4 (p. 205), and Appendix A (p. 209)
