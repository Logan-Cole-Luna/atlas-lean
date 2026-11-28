# Search LWE advantage

Let $n$ and $m$ be natural numbers, $q \ge 1$, and $\chi$ a
probability distribution on $\mathbb{Z}_q$, and let a solver $F$ map a matrix in
$\mathbb{Z}_q^{m \times n}$, a vector in $\mathbb{Z}_q^m$ and coins in a finite nonempty set $S$
to a vector in $\mathbb{Z}_q^n$. Its search LWE advantage is the probability
$\Pr[F(A, As + e, c) = s]$ that it recovers the secret, where $A \in \mathbb{Z}_q^{m \times n}$,
the secret $s \in \mathbb{Z}_q^n$ and the coins $c \in S$ are uniform and the error
$e \in \mathbb{Z}_q^m$ is drawn from $\chi^m$, all independently: its probability of winning the
search LWE experiment.

## Sources

- C. Peikert, *A decade of lattice cryptography*, Found. Trends Theor. Comput. Sci. 10(4) (2016), 283–424, Definition 4.2.2.
