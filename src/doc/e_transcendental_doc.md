$e$ is a transcendental number
==============================

Basic definitions
-----------------

- For any polynomial $f\in\mathbb Z[X]=a_0+a_1X+\cdots+a_nX^n$,
  $\bar f:=|a_0|+|a_1|X+\cdots+|a_n|X^n$. This is ${\tt f\_bar}$ in ${\tt e\_trans\_helpers2.lean}$

- For any prime number $p$ and natural number $n$ we can define a
  polynomial $f_{p,n}\in\mathbb{Z}[X]$ as
  $X^{p-1}(X-1)^p\cdots(X-n)^p$. This is ${\tt f\_p}$ in ${\tt e\_transcendental.lean}$.

- $f_{p,n}$ has degree $(n+1)p-1$. This is ${\tt deg\_f\_p}$ in ${\tt e\_transcendental.lean}$.

- With $f$ an integer polynomial and any nonnegative real number $t$, we associate
  $f$ with an integral $I(f, t)$ to be
  $$
  \int_0^t  e^{t-x} f(x)\mathrm{d} x
  $$
  This is ${\tt II}$ in ${\tt e\_trans\_helpers2.lean}$

- If $f$ has degree $n$, then using integrating by part $n$ times we have
  $$
  \begin{aligned}
  I(f,t)&=e^t\sum_{i=0}^n f^{(i)}(0)-\sum_{i=0}^nf^{(i)}(t)\\
  \end{aligned}
  $$
  This is ${\tt II\_eq\_I}$ in ${\tt e\_trans\_helpers2.lean}$.

- For any polynomial $g\in\mathbb Z$ with degree $n$ and coefficient
  $g_i$, $J_p(g)$ is defined to be
  $$
  J_{p}(g) = \sum_{i=0}^n g_i I(f_{p,n},i)
  $$
  This is ${\tt J}$ in ${\tt e\_transcendental.lean}$.


So if $g(e)=0$, we will have
$$
\begin{aligned}
  J_{p}(g) &= \sum_{i=0}^n g_i I(f_{p,d},i) &[{\tt J\_eq1} \textrm{ in } {\tt e\_transcendental.lean}]\\
           &= \sum_{i=0}^n g_ie^i\sum_{j=0}^{(n+1)p-1} f_{p,n}^{(j)}(0)-\sum_{i=0}^ng_i\sum_{j=0}^{(n+1)p-1}f_{p,n}^{(j)}(i) &[{\tt J\_eq2}\textrm { in } {\tt e\_transcendental.lean}]\\
           &=0-\sum_{i=0}^n\sum_{j=0}^{(n+1)p-1}g_i f_{p,n}^{(j)}(i) &[{\tt J\_eq3}\textrm{ in }{\tt e\_transcendental.lean}]\\
           &=-\sum_{i=0}^n\sum_{j=0}^{(n+1)p-1}g_i f_{p,n}^{(j)}(i) &[{\tt J\_eq}\textrm{ in }{\tt e\_transcendental.lean}]\\
           &=-\sum_{j=0}^{(n+1)p-1}\sum_{i=0}^ng_i f_{p,n}^{(j)}(i) &[{\tt J\_eq''}\textrm{ in }{\tt e\_transcendental.lean}]\\
\end{aligned}
$$

We are going to deduce two contradictory bounds for $J_p(g)$ with a
large prime $p$.

Lower bound
-----------

We want to prove that for some $M\in\mathbb R$, $J_{p}(g)=-g_0(p-1)!(-1)^{np}n^p+p!M$ where $n$ is the degree of $g$. This is ${\tt J\_eq\_final}$ in ${\tt e\_transcendental.lean}$.

To evaluate the $J_p{g}$, we will split the big sum
$\sum_{j=0}^{(n+1)p-1}$ to three sums: $j < p-1$, $j = p-1$ and
$j > p-1$.

Using the notation as above, for any prime $p$ and natural number $n$,
we have the followings :

- If $j < p-1$ then in this case, in fact all the summand is zero. This is because
  
  * $f^{(j)}_{p,n}(0)=0$. This is ${\tt deriv\_f\_p\_k\_eq\_zero\_k\_eq\_0\_when\_j\_lt\_p\_sub\_one}$ in ${\tt e\_transcendental.lean}$
  * $f^{(j)}_{p,n}(i)=0$ for all $0<i\le d$. This is ${\tt deriv\_f\_p\_k\_eq\_zero\_k\_ge\_1\_when\_j\_lt\_p\_sub\_one}$ in ${\tt e\_transcendental.lean}$

  Thus
  $$ 
  \sum_{j=0}^{p-2}\sum_{i=0}^ng_i f_{p,n}^{(j)}(i)=0
  $$ 
  This is ${\tt J\_partial\_sum\_from\_one\_to\_p\_sub\_one}$ in ${\tt e\_transcendental.lean}$.
- If $j = p-1$ then 
  * $f_{p,n}^{(j)}(0)=(p-1)! (-1)^{np}n!^p$. This is ${\tt deriv\_f\_p\_zero\_when\_j\_eq\_p\_sub\_one}$ in ${\tt e\_transcendental.lean}$
  * $f_{p,n}^{(j)}(i)=0$ for all $i>0$. This is ${\tt deriv\_f\_p\_when\_j\_eq\_p\_sub\_one}$ in ${\tt e\_transcendental.lean}$
  
  Thus
  $$
  \sum_{i=0}^n g_if_{p,n}^{(p-1)}(i)=(p-1)!g_0(-1)^{np}n!^{p}
  $$
  This is ${\tt J\_partial\_sum\_from\_p\_sub\_one\_to\_p}$ in ${\tt e\_transcendental.lean}$.

- If $j > p-1$ then $p!|f_{p, n}^{(j)} (k)$ for all $k=0,\cdots,n$. This is ${\tt when\_j\_ge\_p\_k}$ in ${\tt e\_transcendental.lean}$. 
  
  Then
  $$
  \left.p!\right|\sum_{j=p}^{(n+1)p-1}\sum_{i=0}^ng_i f_{p,n}^{(j)}(i)
  $$
  This is ${\tt J\_partial\_sum\_rest}$ in ${\tt e\_transcendental.lean}$

Then if $g\in\mathbb Z$ is any polynomial with degree $n$ and
coefficient $g_i$ with $g_0\ne 0$ and $e$ as a root then, from above we
can show that there is some $M\in\mathbb Z$ such that
$$
  J_p(g)=-g_0(p-1)!(-1)^{np}n!^p+M\times p!
$$
This is ${\tt J\_eq\_final}$ in ${\tt e\_transcendental.lean}$

So if we choose $p$ to be a prime number such that $p > n$ and
$p > |g_0|$, then $|J_p(g)|=(p-1)!\left|-g_0(-1)^{np}n!^p+Mp\right|$. So
$(p-1)!\le J_p(g)$. Because otherwise $\left|-g_0(-1)^{np}n!^p+Mp\right|=0$. So $p|g_0n!^p$, then either
$p|g_0$ or $p|n!^p$. The first case cannot happen as we chose $p>|g_0|$.
The second happens if and only if $p|n!$ but we chose $p>n$. This is basically what happened in ${\tt abs\_J\_lower\_bound}$ in ${\tt e\_transcendental.lean}$

Upper bound
-----------

This time we utilize the integral definition of $I$. For a prime $p$ and
$g\in\mathbb Z$ is any polynomial with degree $n$ and coefficient $g_i$
and $e$ as a root then. Let us define $M\in\mathbb R$ to be 
$$(n+1)\left(\max_{0\le i\le n}\{|g_i|\}(n+1)e^{n+1}\right)(2(n+1))^{n+1}$$
Then

$$
\begin{aligned}
|J_p(g)|&\le\sum_{i=0}^n \left|g_i ie^i \overline{f_{p,n}}(i)\right| &[{\tt abs\_J\_ineq1''} \textrm{ in } {\tt e\_transcendental.lean}]\\
&\le(n+1)\max_{0\le i\le n}\{|g_i|\}(n+1)e^{n+1}(2(n+1))^{p+pn} &[{\tt sum\_ineq\_1}\textrm{ in }{\tt e\_transcendental.lean}]\\
&\le(n+1)^p\left(\max_{0\le i\le n}\{|g_i|\}\right)^p(n+1)^p\left(e^{n+1}\right)^p(2(n+1))^{p+pn}&[{\tt sum\_ineq\_2}\textrm{ in }{\tt e\_transcendental.lean}]\\
&= M^p &[{\tt abs\_J\_upper\_bound}\textrm{ in }{\tt e\_transcendental.lean}]
\end{aligned}
$$

The point is for some real number $c$ (independent of $p$, depending on
$g$), $|J_p(g)|\le c^p$.

The desired contradiction
-------------------------

We use that for any real number $M\ge0$ and an integer $z$ then there is a prime number $p > z$ such that $(p-1)!>M^p$ to get a contradiction. This fact is ${\tt contradiction}$ in ${\tt e\_transcendental.lean}$.

Assume $e$ is algebraic and $g\in\mathbb Z[X]$ admits $e$ as a root with
degree $n$ and coefficient $g_i$. We can assume $g_0\ne 0$ by dividing a
suitable power of $X$ if necessary. This process is ${\tt make\_const\_term\_nonzero}$ in ${\tt e\_transcendental.lean}$. The fact that after this possible change $e$ is still a root of $g$ is ${\tt non\_zero\_root\_same}$ in ${\tt e\_transcendental.lean}$. Then we know that for some real
number $c$ independent of $g$, we have $(p-1)!\le J_p(g) \le c^p$ for
all $p>|g_0|$ and $p>d$. But this is not possible by the previous paragraph.
