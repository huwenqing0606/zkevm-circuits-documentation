---
tags: scroll documentation
---

# Modexp Circuit

code: https://github.com/scroll-tech/misc-precompiled-circuit

Let $p$ be the prime used in Modexp. When $x$ is U256, $\langle x \rangle$ stands for its limb representation; and $\langle x \rangle_p$ stands for $x\mod p$.


## Iterative algorithm for computing $\langle a^b \rangle_p$

Write $b=b_{n-1}+b_{n-2}\cdot 2+...+b_1\cdot 2^{n-2}+b_0\cdot 2^{n-1}$, i.e., in big-endian form $b=\overline{b_0b_1...b_{n-2}b_{n-1}}$. Then 
$$a^b=a^{b_{n-1}}\cdot (a^{b_{n-2}})^2\cdot ... \cdot (a^{b_{0}})^{2^{n-1}} \ .$$
So $a^b$ can be computed recursively as
$$P_0=1, P_{k}=P_{k-1}^2\cdot a^{b_{k-1}}, k=1,...,n-1 \ ,$$
and $a^b=P_{n-1}$. This also applies when $\mod p$ is present, i.e., $a^b \mod p$ can be computed recursively as
$$\qquad R_0=1, R_k=R_{k-1}^2\cdot a^{b_{k-1}} \mod p \ , k=1,...,n-1 \ ,$$
and $\langle a^b\rangle_p=R_{n-1}$.

Note that in binary representation $b_{k-1}=0 \text { or } 1$ depending on the exact bit. Also, $\langle u \cdot v \rangle_p=\langle \langle u \rangle_p \cdot \langle v \rangle_p \rangle_p$, so the recursion for $R$ can be further written as

$$(1) \qquad R_0=1, R_k=\left\{
\begin{array}{ll}
\langle \langle R_{k-1}\cdot R_{k-1}\rangle_p\cdot a\rangle_p & \text{ if } b_{k-1}=1;
\\
\langle R_{k-1}\cdot R_{k-1}\rangle_p &  \text{ if } b_{k-1}=0 \ ,
\end{array}\right.$$
and $\langle a^b\rangle_p=R_{n-1}$.

Note that the number of iterations $n$ is the number of bits of the exponent $b$. If $b$ is U256, then $n$ will not exceed 256.


## U256 `Number` decomposed in limbs

Let $x$ be U256 (`Number`) and denote the limb representation of $x$ as $\langle x \rangle=[x_0, x_1, x_2, x_3]$. The rule is
$$x=x_0+x_1\cdot 2^{108}+x_2\cdot 2^{216} \ ,$$
i.e., $\langle x \rangle = \overline{
\underbrace{\xi_0\xi_1\cdots \xi_{107}}_{x_0}
\underbrace{\xi_{108}\xi_{109}\cdots  \xi_{215}}_{x_1}
\underbrace{\xi_{216}\xi_{217}\cdots  \xi_{255}}_{x_2}}$ in little-endian. This guarentees that $x_0\leq 2^{108}$, $x_1\leq 2^{108}$ and $x_2\leq 2^{108}$, so each of $x_0, x_1, x_2$ can be fit into an $\mathbb{F}_r$ element of Halo2.

In addition, $x_3$ stands for $x_3=x\mod r$.

## Constraint system for $x y \mod p = d$

Let $x, y$ be in U256 and $p$ be the prime used in Modexp, $d<p$ be the remainder, both also in U256. Then the constraints for $x y \mod p = d$ is the same of that for $x y= kp+d$ with some $k$ and $d<p$.

Note that $k$ may well overflow U256. For example, let $p=2$ and $x,y$ are close to $2^{256}-1$, then $k$ will easily overflow U256. We will first discuss the case when $k$ is in U256 only.

We use the [Chinese Remainder Theorem](https://en.wikipedia.org/wiki/Chinese_remainder_theorem) (CRT):

<b>Chinese Remainder Theorem</b>: <i> Let $n_1,...,n_k$ be pairwise co-prime numbers, and $a_1,...,a_k$ any integers. Then the system $x \equiv a_i \mod n_i$ for $i=1,...,k$ has a solution, and any two solutions $x_1$, $x_2$ are congruent modulo $N=n_1...n_k$, i.e. $x_1 \equiv x_2 \mod N$.</i>

In our case, we pick $n_1=2^{108}-1$, $n_2=2^{216}$ and $n_3=r$, so they are co-prime, and the system $xy\equiv kp+d \mod n_i$, $i=1,2,3$ is ensured to have a solution of the form $xy=kp+d+\delta\cdot n_1n_2n_3$ for some integer $\delta$. Since $n_1n_2n_3>2^{512}$ and $xy\leq 2^{512}$, we must take $\delta=0$, so $xy=kp+d$.

For any $n$ the relation $xy=kp+d \mod n$ is equivalent to
$$\langle x\rangle_n \langle y\rangle_n\equiv \langle k\rangle_n\langle p\rangle_n+\langle d \rangle_n \mod n \ .$$

For an $x$ expressed in limbs, we get
$$\begin{array}{l}
& \langle x \rangle_{n_1}
\\
= & x_0 + x_1 \cdot \langle 2^{108} \rangle_{n_1} +  x_2 \cdot \langle 2^{216} \rangle_{n_1} \mod (2^{108}-1)
\\
= & \langle x_0+x_1+x_2\rangle_{n_1}
\end{array}$$
since $\langle 2^{108} \rangle_{n_1}=\langle 2^{216} \rangle_{n_1}=1$. 

Also, 
$$\begin{array}{l}
& \langle x \rangle_{n_2}
\\
= & x_0  + x_1 \cdot  2^{108}  +  x_2 \cdot 2^{216} \mod 2^{216}
\\
= & \langle x_0 + x_1 \cdot 2^{108} \rangle_{n_2} \ .
\end{array}$$

And by definition $\langle x\rangle_{n_3}=x_3$. Notice that if both $x, y$ are decomposed into limbs, then 
$$\begin{array}{l}
& \langle x y \rangle_{n_2}
\\
= & (x_0 + x_1 \cdot 2^{108})(y_0 + y_1 \cdot 2^{108}) \mod n_2
\\
= & \langle x_0y_0 + (x_1y_0+x_0y_1)\cdot 2^{108}\rangle_{n_2} \ ,
\end{array}$$
because $n_2=2^{216}$.

So constraints that ensure $xy=kp+d$ when $k$ is in U256 is given by

$$(2) \left\{\begin{array}{rcll}
(x_0+x_1+x_2)(y_0+y_1+y_2) & \equiv & (k_0+k_1+k_2)(p_0+p_1+p_2) + (d_0+d_1+d_2)  & \mod (2^{108}-1) \ ,
\\
x_0y_0 + (x_1y_0+x_0y_1)\cdot 2^{108} & \equiv & k_0p_0 + (k_1p_0+k_0p_1)\cdot 2^{108} + d_0+d_1\cdot 2^{108} & \mod 2^{216} \ ,
\\
x_3y_3 & \equiv & k_3p_3 + d_3 & \mod r \ ,
\\
d & < & p \ . &
\end{array}\right.$$

### Discussion: When $k$ overflows U256 in $xy=kp+d$

When $x, y$ are in U256 and $p\geq 2$ is a prime, we must have $k$ in U512 (actually U511). So we can decompose $k$ into more limbs as
$$k=k_0+k_1\cdot 2^{108} + k_2\cdot 2^{216}+ k_3 \cdot 2^{324} + k_4 \cdot 2^{432} \ ,$$
i.e., $k=\overline{\underbrace{\kappa_0\kappa_1...\kappa_{107}}_{k_0}
\underbrace{\kappa_{108}\kappa_{109}...\kappa_{215}}_{k_1}
\underbrace{\kappa_{216}\kappa_{217}...\kappa_{323}}_{k_2}
\underbrace{\kappa_{324}\kappa_{325}...\kappa_{431}}_{k_3}
\underbrace{\kappa_{432}\kappa_{433}...\kappa_{511}}_{k_4}}$ in little-endian form. Then we have

$$\begin{array}{ll}
& k \mod n_1
\\
= & k_0+k_1+k_2\cdot (2^{108}-1+1)^2+k_3\cdot (2^{108}-1+1)^3+k_4\cdot (2^{108}-1+1)^4 \mod n_1
\\
= & k_0+k_1+k_2+k_3+k_4 \mod n_1 \ ,
\end{array}$$
and
$$\begin{array}{ll}
& k \mod n_2
\\
= & k_0+k_1\cdot 2^{108}+\left(k_2+k_3\cdot 2^{108}+k_4\cdot 2^{216}\right) \cdot 2^{216} \mod n_2
\\
= & k_0+k_1\cdot 2^{108} \mod n_2 \ .
\end{array}$$

Further we set $k \mod r =k_5$. So the number in limb representation for $k$ becomes $k=[k_0, k_1, k_2, k_3, k_4, k_5]$. Thus the constraints for $xy=kp+d$ for general $k$ becomes

$$(2')\left\{\begin{array}{rcll}
(x_0+x_1+x_2)(y_0+y_1+y_2) & \equiv & (k_0+k_1+k_2+k_3+k_4)(p_0+p_1+p_2) + (d_0+d_1+d_2)  & \mod (2^{108}-1) \ ,
\\
x_0y_0 + (x_1y_0+x_0y_1)\cdot 2^{108} & \equiv & k_0p_0 + (k_1p_0+k_0p_1)\cdot 2^{108} + d_0+d_1\cdot 2^{108} & \mod 2^{216} \ ,
\\
x_3y_3 & \equiv & k_5p_3 + d_3 & \mod r \ ,
\\
d & < & p \ . &
\end{array}\right.$$
As $k \mod n_2$ looks the same for the U256 case with 3 limbs, the second constraint will not change. 


## Circuit Design and Layout

### Circuit Design

To form a circuit for Modexp we shall apply (2) to each iteration step in (1). In the code, method `ModexpChip.modexp` fills this purpose, it calls `ModexpChip.modmult` to check each step of $\langle R_{k-1}\cdot R_{k-1}\rangle_p$ and $\langle\langle R_{k-1}\cdot R_{k-1}\rangle_p, a\rangle_p$ based on the current bit (`select`) being 0 or 1. The constraints in `ModexpChip.modmult` are those listed in (2).

### Circuit Layout 

Circuit uses 2-rows for one constraint, with layout as follows:

|advice|advice|advice|advice|advice|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|
|-|-|-|-|-|-|-|-|-|-|-|-|-|-|-|-|-|
|`l0`|`l1`|`l2`|`l3`|`d`|`c0`|`c1`|`c2`|`c3`|`cd`|`cdn`|`c`|`c03`|`c12`|`lookup_hint`|`lookup_ind`|`sel`|
|None|None|None|None|`dn`|None|None|None|None|None|None|None|None|None|None|None|None|

Here `l0`, `l1`, `l2`, `l3`, `d` are advice columns (5 advice columns) and rest are fixed columns (12 fixed columns). The context of each cell is explained as follows:

- `l0`-`l3` stand for the 4 limbs in decomposing a U256 `Number`; 
- `d` is a limb term;
- `dn` is a limb term, the next to `d`;
- `c0`-`c3` are coefficients for each of the 4 limbs;
- `cd`, `cdn` are coefficients for `d` and `dn`;
- `c03` is the coefficient for `l0 * l3` and `c12` is the coefficient for `l1 * l2`;
- `c` is a constant term added to the constraint equality;
- `sel` is a binary indicator that enables this constraint or not;
- `lookup_hint` is the size of limb lookup in terms of 12 bits (= one increment in size), so 108 bits takes size 9, usually use size 10 in case of overflow; (TODO: check this)
- `lookup_ind` indicates whether to do limb lookup, take values 0u64 (no lookup) and 1u64 (lookup).

### One-line constraint system

Each constraint equality will be written into the following general form ("one-line constraint") with different assignments for the advice and fixed cells:

`[c0 * l0 + c1 * l1 + c2 * l2 + c3 * l3 + cd * d + cdn * dn + l0 * l3 * c03 + l1 * l2 * c12 + c] * sel = 0`

### `assign_line` method

Modexp Circuit uses `assign_line` method to assign these cells. In `assign_line` method, witnesses are `l0`-`l3`, `d`, `dn`, coefficients are `c0`-`c3`, `cd`, `cdn`, `c03`, `c12`, `c`. The `sel` cell is taken to be 1, `lookup_ind` is `0u64` if `lookup_hint ==0` else it is `1u64`. The `assign_line` method returns the limbs `[l0, l1, l2, l3, d, dn]`.

### range checks of limbs via lookup

Range checks of the limbs are done in a separate `RangeCheckChip`. The range check is usually applied to `l0` limb, and it is decomposed into 12-bit sublimbs for range lookup. Each range lookup checks a table with terms in the range $[0, 2^{12}=4096-1]$ listed in order. Lookup is configured using `register` method and range check chip is assigned using `provide_lookup_evidence` method. (TODO, more details...)

## Constraints

Below we explain each constraint in (2) with its assignment of these specific cells.

### constraint for $\mod 2^{108}-1$

This is done in methods `mod_power108m1`, `mod_power108m1_mul` and `mod_power108m1zero`. 

#### `mod_power108m1` method

It takes a U256 `Number` decomposed into `[limb0, limb1, limb2]` (`limb3` not known) and computes `value=limb0+limb1+limb2`. After these results are obtained it assigns the following cells 

|advice|advice|advice|advice|advice|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|
|-|-|-|-|-|-|-|-|-|-|-|-|-|-|-|-|-|
|`l0`=limb0|`l1`=limb1|`l2`=limb2|`l3`=None|`d`=`value`|`c0`=1|`c1`=1|`c2`=1|`c3`=None|`cd`=-1|`cdn`=None|`c`=None|`c03`=None|`c12`=None|`lookup_hint`=0|`lookup_ind`=0u64|`sel`=1|
|None|None|None|None|`dn`=None|None|None|None|None|None|None|None|None|None|None|None|None|

So its one-line constraint is given by the equation
`limb0+limb1+limb2-value==0`.

This method returns `[limb0, limb1, limb2, limb0+limb1+limb2]`.

#### `mod_power108m1_mul` method

It takes two U256 `Number` denoted as `lhs` and `rhs`, and calls `mod_power108m1` to assign each one's limb0-limb2 and obtains
`ml=lhs.limb0+lhs.limb1+lhs.limb2`, `mr=rhs.limb0+rhs.limb1+rhs.limb2`. Then it computes `v=ml*mr`, `q`=`v / (2^{108}-1)` and `r=v-q*(2^{108}-1)`.
After these results are obtained it assigns the following cells

|advice|advice|advice|advice|advice|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|
|-|-|-|-|-|-|-|-|-|-|-|-|-|-|-|-|-|
|`l0`=`q`|`l1`=`ml`|`l2`=`mr`|`l3`=`r`|`d`=None|`c0`=`2^{108}-1`|`c1`=None|`c2`=None|`c3`=1|`cd`=None|`cdn`=None|`c`=None|`c03`=None|`c12`=-1|`lookup_hint`=10|`lookup_ind`=1u64|`sel`=1|
|None|None|None|None|`dn`=None|None|None|None|None|None|None|None|None|None|None|None|None|

So its one-line constraint is given by the equation
`q*(2^{108}-1)-ml*mr+r==0`.

This method returns `r`.

#### `mod_power108m1zero` method

It takes 3 limbs `limb0, limb1, limb2` and 3 signs `sign0, sign1, sign2`, computes `v=(2^{108}-1)*16+limb0*sign0+limb1*sign1+limb2*sign2` and `q=v/(2^{108}-1)`. After these results are obtained it assigns the following cells

|advice|advice|advice|advice|advice|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|
|-|-|-|-|-|-|-|-|-|-|-|-|-|-|-|-|-|
|`l0`=`q`|`l1`=`limb0`|`l2`=`limb1`|`l3`=`limb2`|`d`=None|`c0`=`-(2^{108}-1)`|`c1`=`sign0`|`c2`=`sign1`|`c3`=`sign2`|`cd`=None|`cdn`=None|`c`=`(2^{108}-1)*16`|`c03`=None|`c12`=None|`lookup_hint`=1|`lookup_ind`=1u64|`sel`=1|
|None|None|None|None|`dn`=None|None|None|None|None|None|None|None|None|None|None|None|None|

So its one-line constraint is given by the equation 

`-q*(2^{108}-1)+limb0*sign0+limb1*sign1+limb2*sign2+16*(2^{108}-1)==0`.

This method returns `OK`.

<i>Q: factor 16 is used to prevent overflow?</i>

#### constraint equation $(x_0+x_1+x_2)(y_0+y_1+y_2) \equiv (k_0+k_1+k_2)(p_0+p_1+p_2) + (d_0+d_1+d_2)  \mod (2^{108}-1)$ in (2) 

We take two U256 `Number` denoted as `lhs` (stand for $x$) and `rhs` (stand for $y$), then 

- call `mod_pow108m1_mul` with `lhs`$=x$ and `rhs`$=y$ to obtain `mod_108m1_lhs=`$(x_0+x_1+x_2)\cdot (y_0+y_1+y_2)\mod 2^{108}-1$;
- call `mod_pow108m1_mul` with `lhs`$=k$ and `rhs`$=p$ to obtain `mod_108m1_rhs=`$(k_0+k_1+k_2)\cdot (p_0+p_1+p_2)\mod 2^{108}-1$;
- call `mod_power108m1` to obtain `mod_108m1_rem=`$d_0+d_1+d_2$;
- call `mod_power108m1zero` with `limb0=mod_108m1_lhs`, `limb1=mod_108m1_rhs` and `limb2=mod_108m1_rem` and `sign0=1`, `sign1=-1`, `sign2=-1`. This checks $(x_0+x_1+x_2)(y_0+y_1+y_2) \equiv (k_0+k_1+k_2)(p_0+p_1+p_2) + (d_0+d_1+d_2)  \mod (2^{108}-1)$ in (2).


### constraint for $\mod 2^{216}$

This is done in methods `mod_power216`, `mod_power216_mul` and `mod_power216_zero`.

#### `mod_power126` method

It takes a U256 `Number` decomposed into `[limb0, limb1, limb2]` (`limb3` not known) and computes `value=limb0+limb1*2^{108}`. After these results are obtained it assigns the following cells 

|advice|advice|advice|advice|advice|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|
|-|-|-|-|-|-|-|-|-|-|-|-|-|-|-|-|-|
|`l0`=limb0|`l1`=limb1|`l2`=None|`l3`=None|`d`=`value`|`c0`=1|`c1`=`2^{108}`|`c2`=None|`c3`=None|`cd`=-1|`cdn`=None|`c`=None|`c03`=None|`c12`=None|`lookup_hint`=0|`lookup_ind`=0u64|`sel`=1|
|None|None|None|None|`dn`=None|None|None|None|None|None|None|None|None|None|None|None|None|

So its one-line constraint is given by the equation
`limb0+limb1*2^{108}-value == 0`.

This method returns `value=limb0+limb1*2^{108}`.

#### `mod_power216_mul` method

It takes two U256 `Number` denoted as `lhs` and `rhs` and then computes `v = lhs.limb0 * rhs.limb1 + lhs.limb1 * rhs.limb0`. After these results are obtained it assigns the following cells 

|advice|advice|advice|advice|advice|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|
|-|-|-|-|-|-|-|-|-|-|-|-|-|-|-|-|-|
|`l0`=`lhs.limb0`|`l1`=`lhs.limb1`|`l2`=`rhs.limb0`|`l3`=`rhs.limb1`|`d`=`v`|`c0`=None|`c1`=None|`c2`=None|`c3`=None|`cd`=-1|`cdn`=None|`c`=None|`c03`=1|`c12`=1|`lookup_hint`=0|`lookup_ind`=0u64|`sel`=1|
|None|None|None|None|`dn`=None|None|None|None|None|None|None|None|None|None|None|None|None|

So its one-line constraint is given by the equation
`lhs.limb0*rhs.limb1 + lhs.limb1*rhs.limb0 - v == 0`.

Next, this method computes the quotient `q=v/2^{108}` and the remainder `r=v-q^2^{108}`, so that this computes `r=(lhs.limb0*rhs.limb1+lhs.limb1*rhs.limb0)%2^{108}`. After these results are obtained it assigns the following cells 

|advice|advice|advice|advice|advice|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|
|-|-|-|-|-|-|-|-|-|-|-|-|-|-|-|-|-|
|`l0`=`q`|`l1`=`v`|`l2`=None|`l3`=`r`|`d`=None|`c0`=`2^{108}`|`c1`=-1|`c2`=None|`c3`=1|`cd`=None|`cdn`=None|`c`=None|`c03`=None|`c12`=None|`lookup_hint`=10|`lookup_ind`=1u64|`sel`=1|
|None|None|None|None|`dn`=None|None|None|None|None|None|None|None|None|None|None|None|None|

So its one-line constraint is given by the equation
`q*2^{108}-v+r == 0`.

After getting the `r`, final step is to compute an updated `v=lhs.limb0*rhs.limb0+r*2^{108}`. After these results are obtained it assigns the following cells 

|advice|advice|advice|advice|advice|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|
|-|-|-|-|-|-|-|-|-|-|-|-|-|-|-|-|-|
|`l0`=`r`|`l1`=`lhs.limb0`|`l2`=`rhs.limb0`|`l3`=None|`d`=`v`|`c0`=`2^{108}`|`c1`=None|`c2`=None|`c3`=None|`cd`=-1|`cdn`=None|`c`=None|`c03`=None|`c12`=1|`lookup_hint`=0|`lookup_ind`=1u64|`sel`=1|
|None|None|None|None|`dn`=None|None|None|None|None|None|None|None|None|None|None|None|None|

So its one-line constraint is given by the equation
`r*2^{108}+lhs.limb0*rhs.limb0-v == 0`.

This method finally returns `v=lhs.limb0*rhs.limb0+((lhs.limb0*rhs.limb1+lhs.limb1*rhs.limb0) % 2^{108})*2^{108}`.

#### `mod_power216_zero` method

This method takes 3 limbs `limb0`, `limb1`, `limb2` and 3 signs `sign0`, `sign1`, `sign2` and computes `v=2*2^{216}+limb0*sign0+limb1*sign1+limb2*sign2`, `q=v/2^{216}`. After these results are obtained it assigns the following cells 

|advice|advice|advice|advice|advice|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|
|-|-|-|-|-|-|-|-|-|-|-|-|-|-|-|-|-|
|`l0`=`q`|`l1`=`limb0`|`l2`=`limb1`|`l3`=`limb2`|`d`=None|`c0`=`-2^{216}`|`c1`=`sign0`|`c2`=`sign1`|`c3`=`sign2`|`cd`=None|`cdn`=None|`c`=`2*2^{216}`|`c03`=None|`c12`=None|`lookup_hint`=1|`lookup_ind`=1u64|`sel`=1|
|None|None|None|None|`dn`=None|None|None|None|None|None|None|None|None|None|None|None|None|

So its one-line constraint is given by the equation
`-q*2^{216}+limb0*sign0+limb1*sign1+limb2*sign2+2*2^{216} == 0`.

This method returns `OK`.

<i>Q: is $2*2^{216}$ enough to prevent overflow in `mod_power216_mul`?</i>

#### constraint equation $x_0y_0 + (x_1y_0+x_0y_1)\cdot 2^{108}  \equiv k_0p_0 + (k_1p_0+k_0p_1)\cdot 2^{108} + d_0+d_1\cdot 2^{108}  \mod 2^{216}$ in (2) 

We take two U256 `Number` denoted as `lhs` (stand for $x$) and `rhs` (stand for $y$), then 

- call `mod_pow216_mul` with `lhs`$=x$ and `rhs`$=y$ to obtain `mod_216_lhs=`$x_0y_0+(x_1y_0+x_0y_1 \mod 2^{108})\cdot 2^{108}$;
- call `mod_pow216_mul` with `lhs`$=k$ and `rhs`$=p$ to obtain `mod_216_rhs=`$k_0p_0+(k_1p_0+k_0p_1 \mod 2^{108})\cdot 2^{108}$;
- call `mod_power216` to obtain `mod_216_rem=`$d_0+d_1\cdot 2^{108}$;
- call `mod_power216zero` with `limb0=mod_216_lhs`, `limb1=mod_216_rhs` and `limb2=mod_216_rem` and `sign0=1`, `sign1=-1`, `sign2=-1`. This checks $x_0y_0 + (x_1y_0+x_0y_1)\cdot 2^{108}  \equiv k_0p_0 + (k_1p_0+k_0p_1)\cdot 2^{108} + d_0+d_1\cdot 2^{108}  \mod 2^{216}$ in (2).



### constraint for $\mod r$

This makes use of `mod_native_mul` method.

#### `mod_native_mul` method

This method takes 3 U256 `Number` named as `lhs`, `rhs` and `rem`. Then it assigns the following cells 

|advice|advice|advice|advice|advice|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|fixed|
|-|-|-|-|-|-|-|-|-|-|-|-|-|-|-|-|-|
|`l0`=`lhs.limb3`|`l1`=`rhs.limb3`|`l2`=`rem.limb3`|`l3`=None|`d`=None|`c0`=None|`c1`=None|`c2`=None|`c3`=-1|`cd`=None|`cdn`=None|`c`=None|`c03`=None|`c12`=1|`lookup_hint`=0|`lookup_ind`=0u64|`sel`=1|
|None|None|None|None|`dn`=None|None|None|None|None|None|None|None|None|None|None|None|None|

So its one-line constraint is given by the equation
`lhs.limb3*rhs.limb3-rem.limb3==0`.

This method returns `rem.limb3`.

#### constraint equation $x_3y_3=k_3p_3+d_3 \mod r$ in (2)

We take two U256 `Number` denoted as `lhs` (stand for $x$) and `rhs` (stand for $y$), then 

- call `mod_native_mul` with `lhs`$=x$, `rhs`=$y$ and `rem`$=d_3$. This checks $x_3y_3\equiv d_3 \mod r$ in (2). (Since field is $\mathbb{F}_r$, operation $\mod r$ is done automatically when doing field operations.)

<i>Q: this is not correct? k3 and p3 missing? Need to check.</i>