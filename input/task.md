# Theorems of record compositions

**Definition.** A _composition_ of $n\ge 0$ is a (possibly empty) sequence
$\alpha = (\alpha_1,\dots,\alpha_\ell)$ of positive integers with
$\alpha_1+\cdots+\alpha_\ell=n$; we write $\alpha\vDash n$.

**Definition.**
Let $\mathcal{A}_{2n}$ denote the set of down-up alternating permutations.
Given $w = a_1a_2\cdots a_{2n} \in \mathcal{A}_{2n}$ (so $a_1 > a_2 < a_3 > …$),
we let $\hat w = a_1 a_3 … a_{2n-1}$
and then define a composition $\operatorname{rc}(\hat w)$ as follows.
Consider all the indices $1 \le i \le n$ such that
$a_{2i-1} > a_{2j-1}$ for all $1\le j < i$;
let $r_1<r_2<\cdots<r_p$ (so $r_1=1$) be the set of such indices, and put $r_{p+1}:=n+1$.
We then set
$$\operatorname{rc}(\hat w) := (r_2-r_1, r_3-r_2, \dots, r_{p+1}-r_p) \vDash n.$$
For example, if $w = 7 \, 2 \, 5 \, 4 \, 8 \, 3 \, 10 \, 6 \, 9 \, 1 \in \mathcal{A}_{10}$
then $\hat w = 7 \, 5 \, 8 \, 10 \, 9$
and $\operatorname{rc}(\hat w) = (2,1,2)$.

For this problem, choose a composition $\alpha \vDash n$,
and let $N(\alpha)$ denote the number of $w \in \mathcal{A}_{2n}$ with
$\operatorname{rc}(\hat w) = \alpha$.
Also define the _partial sums_ by $s_j=s_j(\alpha)=\alpha_1+\cdots+\alpha_j$
for $0\le j \le \ell$ (so $s_0=0$ and $s_\ell=n$).
Finally, let $E_k$ denote the $k$th Euler number and $b_k = \frac{k E_{2k-1}}{(2k)!}$.

Prove that
$$ N(\alpha) = \prod_{j=1}^{\ell} \binom{2s_j-1}{2\alpha_j-1} E_{2\alpha_j-1}
= (2n)! \prod_{j=1}^{\ell} \frac{b_{\alpha_j}}{s_j}. $$

Throughout, $K$ denotes a fixed field of characteristic zero (the reader may take $K=\mathbb{Q}$ or $K=\mathbb{R}$). $\mathrm{NSym}$ is the free associative $K$-algebra $K\langle S_1,S_2,S_3,\dots\rangle$ on noncommuting generators $S_k$ of degree $k$, with $S_0:=1$; the noncommutative power sums of the first kind $\Psi_k$ are defined by $n\,S_n=\sum_{k=1}^{n}S_{n-k}\,\Psi_k$, and $\Psi^\alpha:=\Psi_{\alpha_1}\cdots\Psi_{\alpha_\ell}$; $b_k:=\frac{k\,E_{2k-1}}{(2k)!}$; let $\phi_b$ be the algebra endomorphism of $\mathrm{NSym}$ with $\phi_b(\Psi_k)=b_k\Psi_k$, and $\mathbf{A}_n:=\phi_b(S_n)$; let $\chi$ be the algebra homomorphism $\mathrm{NSym}\to\mathrm{Sym}$ with $\chi(S_n)=h_n$; $A_n=\sum_{\lambda\vdash n}z_\lambda^{-1}b_\lambda p_\lambda$, where $b_\lambda:=b_{\lambda_1}b_{\lambda_2}\cdots$.

For all $n\ge1$, we have that $$(2n)!\,\mathbf{A}_n\;=\;\sum_{\alpha\vDash n} N(\alpha)\,\Psi^\alpha \;=\;\sum_{\alpha\vDash n}\#\{w\in\mathcal{A}_{2n}:\operatorname{rc}(\hat w)=\alpha\}\, \Psi^\alpha$$ and $\chi(\mathbf{A}_n)=A_n$.  In particular, the expansion of $(2n)!\,\mathbf{A}_n$ in the basis $\{\Psi^\alpha\}$ has nonnegative integer coefficients with the combinatorial interpretiation above.
