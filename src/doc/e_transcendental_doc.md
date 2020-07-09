# $e$ is a transcendental number

## Basic definitions

- For any polynomial $f\in\mathbb Z[X]=a_0+a_1X+\cdots+a_nX^n$, $\bar f:=|a_0|+|a_1|X+\cdots+|a_n|X^n$. See in [`f_bar`](https://github.com/jjaassoonn/transcendental/blob/master/src/e_trans_helpers.lean#L406).

- For any prime number $p$ and natural number $n$ we can define a polynomial $f_{p,n}\in\mathbb{Z}[X]$ as $X^{p-1}(X-1)^p\cdots(X-n)^p$. If $p$ and $n$ is clear from context, we are going to ignore the subscript.

- $f_{p,n}$ has degree $(n+1)p-1$.

- With $f$ defined and any nonnegative real number $t$, we associate $f$ with an integral $I(f, t)$ to be

$$
  \int_0^t  e^{t-x} f(x)\mathrm{d} x
$$

- If $f$ has degree $n$, then using integrating by part $n$ times we have

$$
\begin{aligned}
I(f,t)&=e^t\sum_{i=0}^n f^{(i)}(0)-\sum_{i=0}^nf^{(i)}(t)\\
\end{aligned}
$$

- For any polynomial $g\in\mathbb Z$ with degree $d$ and coefficient $g_i$, $J_p(g)$ is defined to be

$$
J_{p}(g) = \sum_{i=0}^d g_i I(f_{p,d},i)
$$

So if $g(e)=0$, we will have
$$
\begin{aligned}
  J_{p}(g) &= \sum_{i=0}^d g_i I(f_{p,d},i)\\
           &= \sum_{i=0}^d g_i\left(e^i\sum_{j=0}^{(n+1)p-1} f_{p,d}^{(j)}(0)-\sum_{j=0}^{(n+1)p-1}f_{p,d}^{(j)}(i)\right)\\
           &= \sum_{j=0}^{(n+1)p-1}f_{p,d}^{(j)}(0)\sum_{i=0}^d g_ie^i-\sum_{j=0}^{(n+1)p-1}\sum_{i=0}^dg_i f_{p,d}^{(j)}(i)\\
           &=-\sum_{j=0}^{(n+1)p-1}\sum_{i=0}^dg_i f_{p,d}^{(j)}(i)
\end{aligned}
$$

We are going to deduce two contradictory bounds for $J_p(g)$ with a large prime $p$.
To evaluate the sum, we will split the big sum $\sum_{j=0}^{(n+1)p-1}$ to three sums: $j < p-1$, $j = p-1$ and $j > p-1$.

## Lower bound

Using the notation as above, for any prime $p$ and natural number $n$, we have the followings :

* If $j < p-1$ then in this case, in fact all the summand is zero;

* If $j = p-1$ then $f_{p,n}^{(j)}(0)=(p-1)! (-1)^{np}n!^p$ and $f_{p,n}^{(j)}(i)=0$ for all $i>0$.

* If $j > p-1$ then $p!|f_{p, n}^{(j)} (k)$ for all $k=0,\cdots,n$.

Then if $g\in\mathbb Z$ is any polynomial with degree $n$ and coefficient $g_i$ with $g_0\ne 0$ and $e$ as a root then, from above we can show that there is some $M\in\mathbb Z$ such that
$$
  J_p(g)=-g_0(p-1)!(-1)^{np}n!^p+M\times p!
$$

So if we choose $p$ to be a prime number such that $p > n$ and $p > |g_0|$, then $|J_p(g)|=(p-1)!\left|-g_0(-1)^{np}n!^p+Mp\right|$. So $(p-1)!\le J_p(g)$. Because otherwise $\left|-g_0(-1)^{np}n!^p+Mp\right|=0$. So $p|g_0n!^p$, then either $p|g_0$ or $p|n!^p$. The first case cannot happen as we chose $p>|g_0|$. The second happens if and only if $p|n!$ but we chose $p>n$.

## Upper bound

This time we utilize the integral definition of $I$. For a prime $p$ and $g\in\mathbb Z$ is any polynomial with degree $n$ and coefficient $g_i$ and $e$ as a root then: let $A$ be the maximum of $g_i$
$$
\begin{aligned}
|J_p(g)|&=\left|\sum_{i=0}^d g_i I(f_{p,d},i)\right|\\
        &\le\sum_{i=0}^d |g_i| \left|I(f_{p,d},i)\right|\\
        &\le\sum_{i=0}^d |g_i| \left|I(f_{p,d},i)\right|\\
        &=\sum_{i=0}^d |g_i|\left|\int_0^t  e^{i-x} f_{p,d}(x)\mathrm{d} x\right|\\
        &\le\sum_{i=0}^d|g_i| i e^i\bar{f}_{p,d}(i)\\
        &\le\sum_{i=0}^d|g_i| (d+1) e^{d+1}(2(d+1))^{p+pd}\\
        &\le A^p(d+1)^p(e^{d+1})^p((2(d+1))^{d+1})^p \\
\end{aligned}
$$

The point is for some real number $c$ (independent of $p$, depending on $g$), $|J_p(g)|\le c^p$.

## The desired contradiction

Assume $e$ is algebraic and $g\in\mathbb Z[X]$ admits $e$ as a root with degree $d$ and coefficient $g_i$. We can assume $g_0\ne 0$ by dividing a suitable power of $X$ if necessary. Then we know that for some real number $c$ independent of $g$, we have $(p-1)!\le J_p(g) \le c^p$ for all $p>|g_0|$ and $p>d$. But this is not possible.
