

  We already know $\measuredangle AOB=\measuredangle BOA'$ and $\measuredangle AOC=\measuredangle COA'$, so $2(\measuredangle AOC+\measuredangle AOB)\equiv 0$, so $2\measuredangle BOC\equiv 0$, so $\measuredangle BOC\equiv 0$ or $\pi$. $\blacksquare$

The K-map is:

(a): To verify, we need to compute $\sum_{y=0}^\infty{\frac{\lambda^y}{y!e^\lambda}}=\frac1{e^\lambda}\sum_{y=0}^\infty{\frac{\lambda^y}{y!}}$, according to the Taylor expansion of exponential it's equivalent to $\frac1{e^\lambda}e^\lambda=1$, so it's a valid PMF.

Gamma distribution's PDF $f(x\mid \alpha, \lambda)=\frac{x^{\alpha-1}e^{-x/\lambda}}{\Gamma(\alpha)\lambda^\alpha}$, the first moment $E(X)=\alpha\lambda$, and the second moment is $E(X^2)=\lambda^2\alpha(\alpha+1)$.

+ Polynomials $x^2+xy=f(x, y)$: use as algebraic expression or functions
+ Set of zeros: $\{(x, y)\in \R^2, f(x, y)=0\}$ is an algebraic curve
+ Example:
  + $y=x^2 \mapsto y-x^2=0$: curve
  + $y-x=0$
+ Will be talking about curves as specific polynomials instead of sets of zeros
+ Degree of polynomials (2 and 3 mostly)
+ $y^2-x^3=0$: <https://en.wikipedia.org/wiki/Singularity_(mathematics)> at $x=0$
+ $xy=1$, $x^2+y^2=1$, etc.
+ $x^4+2x^2y^2+y^4-x^2+y^2=0$ (see <https://www.wolframalpha.com/input?i=x%5E4%2B2x%5E2y%5E2%2By%5E4-x%5E2%2By%5E2%3D0>)
+ Derivative is a linear object: study nonlinear functions from linear ones
+ Linear things are good in mathematics

+ (b) There are four circuits:
  $$
  \begin{bmatrix}1&0&0&0\\0&1&0&0\\0&0&\frac1{\sqrt2}&\frac1{\sqrt2}\\
  0&0&\frac1{\sqrt2}&-\frac1{\sqrt2}\end{bmatrix},
  \begin{bmatrix}\frac1{\sqrt2}&\frac1{\sqrt2}&0&0\\
  \frac1{\sqrt2}&-\frac1{\sqrt2}&0&0\\0&0&1&0\\0&0&0&1\end{bmatrix},
  \begin{bmatrix}1&0&0&0\\0&1&0&0\\0&0&1&0\\0&0&0&i\end{bmatrix},
  \begin{bmatrix}1&0&0&0\\0&i&0&0\\0&0&1&0\\0&0&0&1\end{bmatrix}
  $$

+ Clock skew is the difference in arrival times of the same clock source at 2 different points. Clock jitter is external sources like noise, voltage variations may cause to disrupt the frequency of the clock. They cause unexpected states to appear.
+ Clock period: the interval between occurrences of  a specific clock edge in a periodic clock. Slack: extra time in the clock period in addition to the sum of the delays and setup time on a path.
  + Condition: must be greater than or equal to zero on all paths

Simplification:
$$
\begin{align*}
2\pi\sinh{(r+1)}&>2\cdot2\pi\sinh r\\
\sinh(r+1)&>2\sinh r\\
\frac{e^{r+1}-e^{-(r+1)}}2&>e^r-e^{-r}\\
e^{r+1}-e^{-(r+1)}&>2e^r-2e^{-r}\\
e\cdot e^r-e^{-1}\cdot e^{-r}&>2e^r-2e^{-r}\\
e\cdot e^r-2e^r&>e^{-1}\cdot e^{-r}-2e^{-r}\\
(e-2)e^r&>(e^{-1}-2)e^{-r}
\end{align*}
$$

### 11.10

Basically, it means that $P\mapsto P'$ maps degenerate triangles to degenerate triangles.

### 11.11

+ $\simeq, \cong$ - homeo; $\sim, \simeq$ - homotopic
+ Homotopy relative: you have a subset of domain that you cannot move points
+ A continuous map $f$ from a space $X$ to a subset $A\sub X$ which is relative to the subset itself is called a *retraction*, the subset is called a *retract*.
  + If $f\sim id_X$ then $f$ is a deformation retraction.
  + If $f\sim_{rel~A} id_X$ then $f$ is a strong deformation retraction (not very important).

Here's the circuit:

It won't go wrong according to our experiment *and* in that case the circuit just releases some energy stored in the capacitor, so it's not a disaster.

+ d) The hazard free version $F_0(A,B,C,D)=F(A,B,C,D)+B'CD'$

||O|A|B|AB|$X_{i+}$|
|:-:|:-:|:-:|:-:|:-:|:-:|
|Rh.positive|78|85|58|23|244|
|Rh.negative|12|25|10|9|56|
|$X_{+j}$|90|110|68|32|300|

Only $\{x\mid\norm{x}<1\}$ and $\{x\mid\norm{x}>1\}$ are connected in $\R^2$.

CDF: $F_X(1)=\frac{37}{60}, F_X(2)=\frac{14}{15}, F_X(3)=1$.

(a) Same as 2 (a), $3.33$.

(c): Suppose the score is $1$, so $1=\frac{x-18}6$, so $x=24$.


(n) $Cov(X,Y)=$ $E(XY)-E(X)E(Y)=$ $\frac7{40}-\frac14\frac58=\frac3{160}$.

Recall that $p=P(Y\geq 50)\simeq$ $P(X>49.5)$ and we further simplify: $p=P(Z>\frac{49.5-100e^{-1}}{\sqrt{100e^{-1}(1-e^{-1})}})=$ $P(Z>2.6361)\simeq$ $0.0042$.

Connect $AC$, and we replicate the proof in 11.9 with $\triangle ABC$. Since $\measuredangle DAB\equiv\measuredangle ABC\equiv\frac\pi2$, $\measuredangle DBC+\measuredangle ABD+\measuredangle DAB\equiv\pi$, the triangles $\triangle C_nA_nC_{n+1}$ correspond exactly to replications of $\triangle DBC$. Then, since we proved $c\leq d$ in 11.9 and $c$ correspond to $AB$, $d$ correspond to $CD$, it means $AB\leq CD$.

+ Cantor set (??)
  + Major source of counterexamples in analysis
+ Disjoint, infinite open cover
+ Diagonal of $Y\times Y$: find a square

4. ```
   <e1> -> <e1> + <e0> | <e1> - <e0> | <e0>
   <e0> -> ~<e0> | <n>
   <n>  -> <n><d> | <d>
   <d>  -> 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9
   ```

Suppose $(XB)$ intersects with $\ell$ on $Y$ and $(AB)$ intersects with $\ell$ on $O$.

Diagram:

Doubled observation:

  So $\alpha\alpha'=\frac12$ (1), $\alpha\beta'=\frac12$ (2), $\alpha'\beta=\frac12$ (3), $\beta\beta'=-\frac12$ (4).

+ (b) I did not consult without anyone my group members.

By exercise 8.14 (f), $D^2$ is homeomorphic to $([0,1]\times S^1)/\sim$ where $\sim$ is precisely the equivalence relation given above, let this homeomorphism be $\phi:D^2\to[0,1]\times S^1$, so $h\circ\phi:D^2\to X$ is a function such that $(h\circ\phi)\mid S^1=f$ -- precisely the definition of $g$. So, $f$ is null homotopic implies the existence of $h$, which implies the existence of $g$. Also, the existence of $g$ implies the existence of $g\circ(\phi^{-1})$, which is $h$, which shows $f$ to be null homotopic.

$\cosh(PQ_h)=\cosh(\frac12PQ_h)^2+\sinh(\frac12PQ_h)^2$ (definition) $=\sqrt{\frac{PQ'\cdot P'Q}{PP'\cdot QQ'}}^2+\sqrt{\frac{PQ\cdot P'Q'}{PP'\cdot QQ'}}^2$ (part (a) and (b)) $=\frac{PQ'\cdot P'Q}{PP'\cdot QQ'}+\frac{PQ\cdot P'Q'}{PP'\cdot QQ'}$ (cancellation) $=\frac{PQ'\cdot P'Q + PQ\cdot P'Q'}{PP'\cdot QQ'}$.

It is easy to see that $X$ is a subspace of $X^\infty$, because $\forall U\in \mathscr U^\infty, (U\cap X)\in\mathscr U$ by definition of $\mathscr U^\infty$.

## 11.13

## 0

SOP: $C+AB$

## 1

## 2

## 3

## 4

## 5

$$
\begin{align*}
AB^2=(AD+BD)^2&=AC^2+BC^2\\
AD^2+BD^2+2AD\cdot BD&=AD^2+CD^2+CD^2+BD^2\\
2AD\cdot BD&=2CD^2\\
AD\cdot BD&=CD^2
\end{align*}
$$


(d) This is Poisson distribution, .

+ Deutsch's problem

+ Curves in degree 1: everything's simple, fairly complete theory
+ Beyond: much more complex

## 3.15

Suppose $z\notin S^1$, then the following map from $D^2-\{z\}$ to $S^1$ is a deformation retraction:

## 3.13

(a) Similar to problem 2, we first compute $L(\lambda)$:
$$
\begin{align*}
L(\lambda)&=\prod^n_{i=1}\lambda e^{-\lambda x_i}
=\left(\prod^n_{i=1}\lambda\right)e^{-\lambda\sum^n_{i=1}x_i}
\end{align*}
$$
Then we take $\ln$ to get $\ell(\lambda)$ and its derivatives:
$$
\begin{align*}
\ell(\lambda)&=\ln{\left(\prod^n_{i=1}\lambda\right)}-\lambda\sum^n_{i=1}x_i\\
&=\sum^n_{i=1}\ln\lambda-\lambda n\bar X=n\ln\lambda-\lambda n\bar X\\
\ell'(\lambda)&=\frac n\lambda-n\bar X\\
\ell''(\lambda)&=-\frac n{\lambda^2}
\end{align*}
$$
Solve for $\ell'(\lambda)=0$ gets $\fbox{$\hat\lambda_{MLE}=\frac1{\bar X}$}$.

(f) $x=1,y=12, z=36$

## 3.11

Suppose $\lambda=\overline Y=0.48$, and we can compute:

+ $\R \in$ Metric spaces $\subset$ Top spaces.
+ Sends open sets to open sets: open map.
+ Generalize convergence into metric spaces.
  + $C\subset X$ if any convergent sequence has its limit in $C$.
+ $C$ closed implies complement is open: points go to the center converges to the center and contradiction.
+ Topology: a class of subsets closed under (in)finite union and finite intersection.
  + "Open sets"
  + For any set there's 'concrete topology': only two open sets
    + 'Discrete topology': all open sets
  + Example of top space that's not *metrizable*
+ *Interior*: for $A\sub X$, the maximal open subset of $A$ is called its interior: $A^o$. So, $A^o\sube A$
+ *Closure*: $\bar A$, minimal closed superset

+ (a) $01011+11101$
  + 1's complement: $11_{10}-2_{10}=9_{10}=01001$, no overflow
  + 2's complement: $01000$, no overflow
+ (b) $101011-111010$
  + 1's complement: $101011+000101=110000$, no overflow
  + 2's complement: $101011+000110=110001$, no overflow
+ (c) $01101010-11010010$
  + 1's complement: $01101010+00101101=10010111$, overflowed
  + 2's complement: $01101010+00101110=10011000$, overflowed

  input x;
  input reset;
  input clk;
  output[2:0] output_state_reg;
  output[6:0] sevenseg;
 
  // -----------------------------------------------
  // Internal signals
  // -----------------------------------------------
  reg [2:0] current_state, next_state; 
  wire[6:0] sevenseg;
  reg [3:0] sevenseg_input;
  reg [3:0] sevenseg_input_reg;

This should be easily achieved by enumerating $i$: consider $i=2$, if $f(2)$ is not perfect square we find a contradiction. If $f(2)$ is a perfect square, then consider $i=3$, if $f(3)$ is not perfect square we find a contradiction. If $f(3)$ is still a perfect square, then consider $i=4$. $f(4)$ must not be a perfect square (proved later), which is a contradiction.

+ Continuity correction
  + $P(Y=k)\simeq P(k-\frac12\leq X\leq k+\frac12)$
  + $P(Y\leq k)\simeq P(X\leq k+\frac12)$ (include $X=k$)
  + $P(Y< k)\simeq P(X\leq k-\frac12)$ (remove $X=k$)
  + The $\frac12$ intuition comes from "in between" of jumps in Bernouli experiments
+ Examples
+ Stat 415
+ ![image-20220426142628345](week14-1.assets/image-20220426142628345.png)
+ 

+ Moore's Law
+ Quantum mechanical effects
+ Classical
  + Deterministic/Probabilistic
  + Faster for several combinatorial search problems and evaluating game trees
+ Topics
  + Quantum information framework
  + Quantum algorithms (including Shor's factoring algorithm and Grover's search algorithm)
  + Many applications
+ No midterms, but has final. 5 assignments
+ Prob bit: state is $0$ with prob. $p_0$ and $1$ with prob. $p_1$ where $p_0,p_1\geq 0$ and $p_0+p_1=1$
+ Probability amplitude $\alpha_0,\alpha_1\in\C$ where $|a_0|^2+|a_1|^2=1$ where $\alpha_0=\sin\theta, \alpha_1=e^{i\psi}\cos\theta$
+ Particle spin or Photon polarization
+ Dirac bra/ket notation: $\ket\psi$ denotes a column vector, $\ket0=[1/0]$ and $\ket1=[0/1]$.
  + $[1/1/0/0]=\ket0+\ket1$
  + $\bra\psi$ denotes a row vector, conjugate transpose of ket.
  + Inner product of $\bra\phi$ and $\ket \psi$ is $\langle\phi|\psi\rangle$
+ Operations
  + Initialize qubits to $\ket0$ or $\ket1$
  + Apply unitary operation $U$ (operations that preserve inner products)
  + $U^\dagger$ is the inverse of $U$
  + ${AB}^\dagger=B^\dagger A^\dagger$

Consider the bisector of $\measuredangle BAC$ intersects $[BC]$ at $D$.

+ Linearity of expectations: $E(a+bX+cY)=a+bE(X)+cE(Y)$.
+ $var(a+bx)=b^2var(x)$ (integration??)
+ $\int^2_0{cy^2dy}=1, \frac c3y^3\mid^2_0=1,\frac c3 2^3=1$.
+ Definition of CDF: $F(c)=\int^c_{-\infty}f(x)dx$.

## 6.2 (c)

Link: https://www.edaplayground.com/x/nmQg

(b) To compute asymptotic distribution, we need from homework 1 that $\ell'(\theta)=\frac1{\theta^2}\sum^n_{i=1}\frac{X_i^2}{2a_i}-\frac n{2\theta}$ Fisher's information:
$$
\begin{align*}
I(\theta)&=-E(\ell''(\theta))\\
&=-E\left(\frac n{2\theta^2}-\frac2{\theta^3}\sum^n_{i=1}\frac{X_i^2}{2a_i}\right)
=-E\left(\frac n{2\theta^2}-\frac1{\theta^3}\sum^n_{i=1}\frac{X_i^2}{a_i}\right)\\
&=\frac1{\theta^3}E\left(\sum^n_{i=1}\frac{X_i^2}{a_i}\right)-\frac n{2\theta^2}
=\frac1{\theta^3}E\left(\sum^n_{i=1}\frac{a_i\theta}{a_i}\right)-\frac n{2\theta^2}\\
&=\frac1{\theta^3}E\left(\sum^n_{i=1}\theta\right)-\frac n{2\theta^2}\\
&=\frac{n\theta}{\theta^3}-\frac n{2\theta^2}
=\frac{n}{\theta^2}-\frac n{2\theta^2}=\frac{n}{2\theta^2}\\
\end{align*}
$$
Therefore $\fbox{$\hat\theta_{MLE}\sim N(0, \frac{2\theta^2}n)$}$ (as $n$ increases).

(c) For every pair of vertices $s, t\in G$ (where $s\ne t$), we decide if $\lang G,s,t,s\rang$ using $A$. If all answers are no, we reject. Otherwise consider the list of vertices $v_0$ which is empty in the beginning:

(a) So $\int_{[0,1]}\int^y_0 f(x,y)d(xy)=\int_{[0,1]}k(y-\frac{y^2}2) dy=\frac k3=1$, thus $k=3$.

![image-20211202160545473](submission2.assets/image-20211202160545473.png)

Simply construct a 2-tape TM $M_3$ such that it works like $M_1$ on the first tape and like $M_2$ on the second, and then we enumerate strings from short to long. If $h(M_1)\cap h(M_2)\ne\empty$ then at some point $M_1$ and $M_2$ both halt, and it's recognized. Otherwise we don't care.

(a) By def. of MGF, it's $E(e^{sX})=\sum_{x=0}^\infty P(X=x)e^{sx}$, by $P(x)=\frac{\lambda^xe^{-\lambda}}{x!}$ we get $e^{-\lambda}\sum_{x=0}^\infty\frac{(\lambda e^s)^x}{x!}$. This is equivalent to $e^{-\lambda}e^{\lambda e^s} =e^{\lambda(e^s-1)}$.

(b) $\frac{d\frac{pe^s}{1-(1-p)e^s}}{ds}=\frac{pe^s}{((p-1)e^s+1)^2}$, then let $s=0$, so $E(X)=\frac{p}{((p-1)+1)^2}=\frac p{p^2}=\frac1p$.

+ $[0,1]/[0,1)$: connected 2-pointed space that's not Hausdorff
+ Finite Hausdorff space have discrete topology
+ Product of Hausdorff space is Hausdorff
+ Repeated proofs
  + One-point set in Hausdorff space is closed
  + Compact is closed
+ From compact to Hausdorff: only need to check if it's bijection and continuous to guarantee it to be a homeomorphism
  + If it's continuous and onto, then the Hausdorff has the induced quotient topology
+ Connectedness
  + If $X$ has only these clopen sets: $\empty, X$

+ Calculate $\overline A$: $X\setminus (X\setminus A)^O$
+ $\overline{A \cup B} = \overline A \cup \overline B$ Both are closed, $A \cup B \subset \overline A \cup \overline B$
+ Intersection of closure might be nonempty
+ Induced topology defined in terms of universal property
+ The "weakest topology"
  + Induced topology $\subset$ pullback topology
    + $V\subset A$ open $\iff V=f^{-1}(W)$ for some open $W\sub X$ where $f:A\to X$
  + Pushforward topology
    + $W\sub B$ open $\iff f^{-1}(W)$ is open in $X$ where $f:X\to B$
+ Quotient topology

  // -----------------------------------------------
  // Combinational logic to decide the next state 
  always@(x or current_state)
  begin 
   next_state = current_state;
   case(current_state)
   s0 : begin
     sevenseg_input=4'h0;
     next_state=s1;
   end
   s1 : begin
     sevenseg_input=4'h1;
     if (x==1)
       next_state=s2;
   end
   s2 : begin
     sevenseg_input=4'h2;
     if (x==1)
       next_state=s3;
   end
   s3 : begin
     sevenseg_input=4'h3;
     if (x==1)
       next_state=s4;
   end
   s4 : begin
     sevenseg_input=4'h4;
     if (x==1)
       next_state=s5;
   end
   s5 : begin
     sevenseg_input=4'h5;
     if (x==1)
       next_state=s6;
   end
   s6 : begin
     sevenseg_input=4'h6;
     if (x==1)
       next_state=s7;
   end
   s7 : begin
     sevenseg_input=4'h7;
     if (x==1)
       next_state=s1;
   end
   endcase
  end

+ Second degree: conics (bc there are cones in intersections)
+ Study of quadratic forms is still linear algebra
  + Circles $x^2+y^2-1=0$
  + Ellipse $\frac-{a^2}, b^2$
  + Hyperbola: $\frac{x^2}{a^2}-\frac{y^2}{b^2}=1$
  + Parabola: $y^2=px$ 只有右半边
  + Exceptions: nothing, degenerate, parallel lines ($(x-y)^2=1$)
  + Classifications
    + Euclidean classifications (congruent triangles, etc.): same shape
    + What kind of curves can we get up to rigid motions (Euclidean transformations: preserve distances, affine transformations)


| C\AB | 00   | 01   | 11   | 10   |
| :--- | ---- | ---- | ---- | ---- |
| 0    | d    | 0    | 1    | 0    |
| 1    | 1    | 1    | d    | 1    |

## 9.8 (e)

Since we have at least two distinct points, name them $A$ and $O$. We take a half line from $O$ to $A$. Since $\alpha\in(-\pi,\pi]$ is an infinite set of real numbers, we can use infinitely many values for $\alpha$ to determine unique half-lines for all of them (axiom III a). The uniqueness of these lines means they are not the same, so fixing the point of intersection $O$, all of these lines have points different from $A$ (axiom II). So there are infinitely many points.

We will make a state machine generating this sequence of outputs (let's name the states $A,B,C,D$). The state machine has no input, so it's just like this:

   (b): Let $P(G\mid E)<\pi$ (the evidence makes it less likely to be suspicious), so that $\pi<\pi(\pi+2p_A(1-\pi))$, so that $1<\pi+2p_A(1-\pi)$, so that $1-\pi<2p_A(1-\pi)$, so that $p_A>\frac12$. So, if $p_A<\frac12$, then the evidence makes it more skeptical. If $p_A>\frac12$, then the evidence makes it less skeptical. If $p_A=\frac12$, nothing changes.

+ For every vertex $v\in G$ that $v\ne s, v\ne t, v\notin v_0$, decide $\lang G, s, t, s, v_0, v\rang$, and if all no, reject, otherwise add $v$ to the end of $v_0$ and repeat this step.
+ If $v_0\cup\{s,t\}$ is the set of vertices of $G$, we accept.

I plan to come up with the state changing diagram first (either written or just in my head) based on the corresponding input configuration of the states in the sequence. Then, I will turn that into a concrete circuit design diagram with gates. After that, I replace the gates in the circuit with more concrete IC-style gates which is isomorphic to the actual circuit.

![image-20210916232816710](hw3.assets/image-20210916232816710.png)

  + State $\ket0-\ket1$ is the eigenvector of NOT

#  HW 8

#  HW 9

(b): A majority-NFA is a valid NFA, so apply the NFA-to-DFA conversion gets us an equivalent DFA.

#  HW 6

+ Summary

Suppose ADDITION is regular, then we can choose a string $20^p=10^p+10^p$ for length $p$. In this case, given $y$, removing it (equivalent to choosing $i=0$) will make the resulting string not in ADDITION.

#  HW 7

(a) $(λf. λx. f (f~x)) (λy. 2 + y) 1=$ $(λx. (λy. 2 + y)((λy. 2 + y)x))1=$ $(λy. 2 + y)((λy. 2 + y)1)=$ $(λy. 2 + y)(2 + 1)=$ $(λy. 2 + y) 3=2+3=5$

Compactness: consider an open cover $\{U+\{\infty\}\mid U\in\mathscr U\}$ of $\mathscr U^\infty$. Then what? Idk.


Also, only $\{x\mid x_1^2+x_2^2-x_3^2=1\}$ and $\{x\mid x_1^2+x_2^2+x_3^2=-1\}$ (the empty set) are connected in $\R^3$.

   Note that `<Empty>` matches empty input.

```verilog
// Flip-flop

#  HW 1

#  HW 4

# Math 429 HW 11

#  HW 5

# Math 429 HW 10

#  HW 2

# Math 429 HW 13

(a): They do, because both have the same PMF $P(Y=x)=P(X=x)=\frac17$ for $x\in[1,7]$ and $0$ otherwise.

By Pasch's theorem, $\ell$ cross $[BC]$ (it doesn't cross $[AC]$ as it's parallel to it). By property 7.9, $\measuredangle BPQ\equiv\measuredangle BAC$. Also $\ang ABC$ is shared, so $\triangle ABC\sim\triangle PBQ$ and $\frac{PB}{AB}=\frac{QB}{CB}$.

| $C_{in}$ | $A$  | $B$  | $S$  | $C_{out}$ |
| -------- | ---- | ---- | ---- | --------- |
| 0        | 0    | 0    | 0    | 0         |
| 0        | 0    | 1    | 1    | 0         |
| 0        | 1    | 0    | 1    | 0         |
| 0        | 1    | 1    | 0    | 1         |
| 1        | 0    | 0    | 1    | 0         |
| 1        | 0    | 1    | 0    | 1         |
| 1        | 1    | 0    | 0    | 1         |
| 1        | 1    | 1    | 1    | 1         |

#  HW 3

+ Bijection.
+ 对着的 $\angle$ 相等，用 axiom III b 证明

(b) $H$ itself follows a binomial distribution $Bin(10, 0.6)$, so $E(H)=np_H=6$, $Var(H)=np_H(1-p_H)=2.4$.

(b) By hint:
$$
\begin{align*}
E(T_2)-E(T_1)&=E(T_2-T_1)\\
&=E\left(\frac1n \sum_{i=1}^n X_i^2-\bar X^2\right)\\
&=E\left(\frac1n \sum_{i=1}^n(X_i-\bar X)^2 \right)\\
&=\frac1n E\left(\sum_{i=1}^n(X_i-\bar X)^2 \right)\\
&=\frac1n\times n\sigma^2\\
&=\sigma^2
\end{align*}
$$
Since variance is non-negative, $\fbox{$ E(T_2)\geq E(T_1)$}$.

![image-20210923232213835](hw4.assets/image-20210923232213835.png)


(d): $P(X\in[0.6,0.8]\mid X>0.5)=\frac{P(X\in[0.6,0.8])}{P(X>0.5)}=\frac{596}{1625}$.

Only $\{z\mid |z|\geq 1\}$ and $\{z\mid z^2~\text{is real}\}$ are path connected in $\C$.

$0|01^*(1|\epsilon)|(1|\epsilon|01^*0)(1|01^*0)^*(0|01^*(1|\epsilon))$

(a): Since $\forall y\in B_\epsilon(x), d(x, y)<\epsilon$ (def. of open balls). So $B_\epsilon(x)$ is open.

+ Teleportation

(c): $F(X)=\frac{x-3}{6}$ for $x\in[3,9]$, and $0$ for $x<3$, and $1$ for $x>9$.

Let $\triangle_h ABC$ be inscribed in a horocycle and $\measuredangle_h ABC=\frac\pi2$ and $AB_h=BC_h$. Suppose $B$ is the center of the absolute, so $[AB]_h=[AB]$, $[BC]_h=[BC]$, and they overlap with radiuses of the absolute. So this is just a Euclidean circle inscribing a Euclidean isosceles right triangle, and the center of the absolute lies on the Euclidean circle.

![image-20211129001737944](writeup.assets/image-20211129001737944.png)

* $n$ choose $k$: $\left(\matrix{n\\k}\right)=$ permutation div by $k!$
* $\left(\matrix{n\\n-k}\right)=\left(\matrix{n\\k}\right)$
* Bose-Einstein: $k$ zeros, $n-1$ ones: getting $\left(\matrix{n+k-1\\k}\right)$
* $n_r$ are indistinguishable: $\left(\matrix{n\\\prod_{i} n_i}\right)=\frac{n!}{\prod_i {(n_i!)}}$
  * Remark: $\left(\matrix{n\\a, b}\right)=\left(\matrix{n\\a}\right)=\left(\matrix{n\\b}\right)$ because $n=a+b$
* Full house: 三带一对儿
  * $13\times \left(\matrix{4\\3}\right)\times 12 \times \left(\matrix{4\\2}\right)\div \mathscr U$
* $P(A)\in[0,1], P(S)=1$, nonoverlap events' probabilities are preserved by summing up
  * Derive $P(\empty)=0$
* $P(A^C)=1-P(A)$
* Subset relation on events is reflected by "less than" relation on probability
* $P(A\cup B)=P(A)+P(B)-P(A\cap B)$
* $P(A\mid B)$ "conditional probability" changing the sample space: probability of $A$ given $B$
  * $P(A\mid B)=\frac{P(A\cap B)}{P(B)}$

### Truth table

Charge, forward, charge, backward correspond to the sequence of inputs $(X,Y)=(0,0),(1,0),(0,0),(0,1)$. So there are four states in total.

  + $Z\ket0=\ket0$, $Z\ket1=-\ket1$
  + $X=\begin{bmatrix}0&1\\1&0\end{bmatrix}, Z=\begin{bmatrix}1&0\\0&-1\end{bmatrix}$
  + $X$ maps $\ket0$ to $\ket1$ and $\ket1$ to $\ket 0$
  + $Z$ maps $\ket0$ to $\ket0$ and $\ket1$ to $-\ket1$

![image-20211111164236168](writeup.assets/image-20211111164236168.png)

(f) By (d), we have  $\frac{\bar X-\bar Y}{0.5244}<-1.96$, thus $\bar X-\bar Y<-3.7376$, so the upper bound is $-3.7376$. Evidently, $3-7=-4<-3.7376$, so it supports (e) too.

(b) $x=24, y=12,z=36$

For $Var(E(X_i\mid I))$, we expand the definition to $E(E(X_i\mid I)^2)-$ $E(E(X_i\mid I))^2$, let $w=E(E(X_i\mid I)^2)$ and by Adam's law $E(E(X_i\mid I))^2=E(X_i)^2=1600$.

The gate on the left-hand-side is XOR, and it's AND on the right-hand-side.

Knots: take complement in $\R^3$ and find algorithm

Waves for $Y_1,Y_2,Z$:

![image-20220219235059654](h5.assets/image-20220219235059654.png)

## 13.12

### 19.7 (a)

  + If you can write a state as a product of two states, it's a product state. Otherwise it's an entangle state.

## 13.14

(ii) in $\R$, let $f(x)=g(x)=h(x)=0$ for $x\in[0,1]$.

Open sets in $Y$: $\{f(U)\mid U~\text{open in}~X\}$, open sets in $Z$: $\{g(U)\mid U~\text{open in}~Y\}$ which is equivalent to $\{g(f(U))\mid U~\text{open in}~X\}$.

(a) $X$ is the Hamiltonian problem and $X'$ is the Extend Hamiltonian problem, where $y=\lang G,s,t \rang$ is mapped to $y'=\lang G,s,t,s\rang$.

A|B|C|Result
--|--|--|--
0|0|0|0
0|0|1|0
0|1|0|0
0|1|1|1
1|0|0|0
1|0|1|1
1|1|0|1
1|1|1|1

```verilog
module seven_segment_display(input_Num, display_Out);

   (e): `<e> -> <d> | <d> * <e> | <d> / <e>`. Parse tree:

Closed: instead of proving directly, we prove its complement $(-\infty, t)\cup [s, +\infty)$ to be open. The union of open sets are open, and $\forall i\in \N^*, {[t-i, t)}$ and $[s, s+i)$ are both open by definition of $\mathscr U$. So, $\bigcup_{i=1}^\infty {[t-i, t)}=(-\infty, t)$ is open, and $\bigcup_{i=1}^\infty{[s, s+i)}=[s, +\infty)$ is also open, thus their union is also open.

(a) $T\sim Pois(\lambda_f+\lambda_m)$

## Exercise 7.5 (c)

   (b): `<e>` $\to$ `<e> / <e>` $\to$ `<e> / <e> * <e>` $\to$ `<d> / <d> * <d>` $\to$ `9 / 3 * 3`

Distance-preserving map $f:X\to Y$ satisfies $\forall A, B\in X, d_X(A, B)=d_Y(f(A), f(B))$.

(c) Similarly $E(X^2)=\lambda+\lambda^2$. So $\text{Var}(X)=E(X^2)-E(X)^2=\lambda$.

+ Sign-magnitude: one digit in the beginning for negativity, and the rest of the bits represent the magnitude.
+ 1's complement: positive numbers represented as-is, negative numbers are flipped.
+ 2's complement: positive numbers represented as-is, negative numbers are flipped _and added by 1_.
+ 2's complement is practical because we do not need to care about the change of the sign during arithmetic operations. In other representation systems, when addition/subtraction operations meet the change of signs, there need to be some ad-hoc calculations. This is not the case for 2's complement.

### Design

(a) This is $X\sim NBin(3, 0.4)$, negative binominal.

## Problem 14.6 (e)

(d): The intersection of all $S\subset X$ (where $X$ is a topological space) such that $\{S \mid S=B_{1/n}(x), n\in\N^*\}$

  + Quantum: reversible black box for $f$

(a) $E(X_i)=E(E(X_i\mid I))$ where $I$ is equally divided and $E(X_i\mid I_A)=50$ and $E(X_i\mid I_B)=30$, so it's $\frac12\cdot 50+\frac12\cdot 30=40$.

+ 5.4

 $|d_\chi(A,B)-d_\chi(A',B')|\leq$ $|d_\chi(A,B)-d_\chi(A',B)|+|d_\chi(A',B)-d_\chi(A',B')|$ $\leq d_\chi(A,A')+d_\chi(B,B')$, so we can take any $\delta\leq \frac12\epsilon$ to satisfy the original existential quantification.

`w` from line 2, `x`, `y` from line 8, `j` from line 3, `i` from line 9, `a`, `b` from line 15, `h` from line 1.

* 1.a. $nc$
* 1.b. $\frac{n+n^2}2$
* $\left(\matrix{n\\k}\right)=\frac{n!}{k!(n-k)!}$
* Binomial theorem
* $\sum_{i=0}^n {q^i}=\frac{1-q^{n+1}}{1-q}\to\frac1{1-q}$ ($s=OE, qs=s-q^0+q^{n+1}$)
* $\sum_{i=1}^n{q^i}=\frac q{1-q}$
* $\sum_{i=0}^n {iq^i}$? So $\int(\sum_{i=0}^n{q^i})(dq)=\int{\frac1{1-q}dq}$
* $\sum_{i=0}^\infty \frac{x^i}{i!}=e^x, e=\sum_{i=0}^\infty{\frac1{i!}}$
* Replacement of variables in calculus
* Gamma function $\Gamma(k)=\int_0^\infty{x^{k-1}e^{-x}dx}=\int^\infty_0-x^{k-1}d(e^{-x})$ (???)
  * $\Gamma(k)=(k-1)!, \Gamma(k)=(k-1)\cdot\Gamma(k-1)$
* 2.c. $\frac1\lambda \Gamma(2)$
* 2.e. Polar coordinates
  * $\int^\infty_{-\infty}{e^{-\frac{x^2}2}dx}=\sqrt{2\pi}$

So the test statistic is $\chi^2=124.77$.
Degrees of freedom: $(2-1)\times (3-1)=2$.

![image-20220427193725736](hw7.assets/image-20220427193725736.png)

## HW

Take the center of the inscribed circle $O$, so $AO=BO=CO=DO$, hence there are four isosceles triangles $\triangle ABO, \triangle BCO, \triangle CDO, \triangle DAO$.

![image-20211014220552679](writeup.assets/image-20211014220552679.png)

I tried.. In the picture $a$ and $w$ and $x$ intersect at point $R$. I have made $a$ and $w$ too close to parallel.

  always @(negedge clk or negedge reset)
  begin
    if (reset) begin
      q  <= 1'b0;
      qb <= 1'b1;
    end else begin
      q  <= D_input;
      qb <= ~D_input;
    end
  end
  
endmodule
```

By corollary 9.8, $O,M,N,L,X$ lie on the same circle with diameter $XO$. So, $\measuredangle MOL\equiv \measuredangle MNL=\frac\pi3$ and $\measuredangle NOM\equiv \measuredangle NLM\equiv\frac\pi3$. So, in $\triangle LMN$, there are two angles measured $\frac\pi3$, which implies the third angle measured $\pi-\frac{2\pi}3=\frac\pi3$, so all angles are equal. So this is an equilateral triangle.

   (b): The first card is randomly chosen, and the rest 4 cards have to be of the same suit ($12\times 11\times 10\times 9=11880$). For all 4 suits, there will be $11880\times 4\div 311875200$ probability which is $\frac{33}{216580}$.

![image-20210913041817526](writeup.assets/image-20210913041817526.png)

By MoM, $E(X^k)=\frac1n\sum^n_{i=1}X_i^k=\bar{X^k}$, so $\alpha\lambda=\bar X$ and $\lambda^2\alpha(\alpha+1)=\bar{X^2}$. So $\hat\alpha=\fbox{$\frac{\bar X^2}{\bar{X^2}-\bar X^2}$}$ and $\hat \lambda=\fbox{$\frac{\bar{X^2}-\bar X^2}{\bar X}$}$.

+ 平角 $\pi$ proof: constructing congruent triangles and there is a motion.
  + Converse: angle measure determines half lines
+ Sign of $\ang AOB$ is the same as the sign of $\measuredangle AOB$.

+ $(Z\otimes I)(\ket{00}+\ket{11})=(Z\otimes I)\ket{00}+(Z\otimes I)\ket{11}$

Variance: $\text{Var}(X)=E(X^2)-[E(X)]^2=\frac{149}{60}-1.45^2=\frac{457}{1200}$.

## Cmpen 270 Project 2

(a): $P(Y=0)=0.4, P(Y=1)=0.6$.

Mean: $E(X)=\sum_{x\in\{1, 2, 3\}}xP(X=x)=1.45$.

(d) By (c), when $X\geq 10$ we reject $H_0$, so when $X\leq 9$ we do not reject $H_0$. So $\beta=P(X\leq 9\mid H_1)$, and $H_1:\theta=\frac13$, so $\beta=F_{X}(9)$ for $X\sim Bin(30,\frac13)$.

## 5.3

## Problem 6.2 (d)

Destruct $\measuredangle ABC$ as $\measuredangle ABO+\measuredangle OBC$ and do the similar destruction to $\measuredangle BCD, \measuredangle CDA, \measuredangle DAB$. The destructed equation is a simple corollary of $\measuredangle ABO\equiv\measuredangle OAB$ and other similar angle measure equivalences derived by isosceles triangles proved above.

+ $\deg(f)=\tilde f(1)$ and show it to preserve homotopy type.
  + Induces a map $\pi_1(S^1,(0,1))\to \Z$.
+ Brower's FP theorem:
  + Consider $D^2$, assume $f:D^2\to D^2$ is cont. then there's a fixed point $x\in D^2$ s.t. $f(x)=x$
  + Choose any $x\in D^2$, take a half-line from image to original point $f(x)\mapsto x$ and project it onto the boundary, and we get a new map $\phi : D^2\to S^1$. If no fixed point, then $f$ is a retraction and thus induce an onto group homomorphism, and this is contradicted by $0\to \Z$ is not onto.
+ Simply connected: fundamental group is trivial
+ Complex polynomial of degree $\geq 1$, then it has a complex root.
  + $p(z)=a_0+a_1z+a_2z^2+\cdots a_n z^n$ for $a_n=1$.
  + Show there's $z_0\in\C$ s.t. $p(z_0)=0$.
  + Construct $q:\C\to S^1:=\lambda z. \frac{p(z)}{|p(z)|}$. Then send concentric circles to paths on $S^1$ and we destroy the continuity.
  + $\lim_{z\to \infty}q(z)= z^n$.

5. The probability is equivalent to $1-P(A_1\cup A_2\cup A_3\cup A_4)$ where $A_i$ is as in the hint. $P(A_1\cup A_2\cup A_3\cup A_4)=$ $\sum_{i=1}^4 P(A_1)-\sum_{1\leq i<j\leq n}P(A_i\cap A_j)+$ three intersection case - four intersection case, where the four intersection case is evidently impossible. This is again equal to $4P(A_1)-3P(A_1\cap A_2)+2P(A_1\cap A_2\cap A_3)$, which equals $4\times\frac34^6-3\times \frac24^6+2\times\frac14^6$ which computes to $0.66552734375\simeq0.67$. So the probability of interest is $1-0.67=0.33$.

$$
\begin{align*}
\chi_1^2&=\sum^n_{i=1}\frac{(Y_i-50p_i)^2}{50p_i}\\
&=\frac{(32-30.95)^2}{30.95}+\frac{(12-14.85)^2}{14.85}+\frac{(6-4.20)^2}{4.20}\\
&\approx 1.354
\end{align*}
$$

  + 

(c) So there will be $10$ failures, so $P(X=10)=\left(\matrix{15-1\\5-1}\right)0.4^50.6^5\simeq 0.797$.

(d) Let $p=P(|\bar X-75|<5)$ while $\bar X\sim N(75, 25/10)$, so $(\bar X-75)\sim N(0, 2.5)$, so $p=P(|\frac{\bar X-75}{\sqrt{2.5}}|<\frac5{\sqrt{2.5}})$ where $\frac{\bar X-75}{\sqrt{2.5}}\sim N(0, 1)$. Therefore $p=P(|Z|<\frac5{\sqrt{2.5}})\simeq$ $P(|Z|<3.162)$.

  + $\hat\sigma_{MLE}=\frac1n\sum(X_i-\bar X)^2$

Consider $X, Y$ two non-homeomorphic spaces, with the carrier sets of the same size (cardinality) $n$, let $G$ be the cyclic group of order $n$, which equalizes everything in $X$ and $Y$. So, $X/G\simeq Y/G\simeq \{1\}$.

(b) By $\chi^2=\sum_{i, j}\frac{(X_{i,j}-E_{i, j})^2}{E_{i, j}}$,

  + $\hat{\theta_0}=\arg\max L(\theta)$ for $\theta\in\Omega_0$

+ SAA
  + Still holds, require more work, use sum of two angles $<\pi$
+ $AB=A'B', BC=B'C',AC>A'C'$
+ defect$(\triangle ABC)=\pi-|\ang A|-|\ang B|-|\ang C|$ (these are angle measures)
+ defect$(\triangle ABC)=$ defect$(\triangle ADC)=$ defect$(\triangle DBC)$
+ defect$(\triangle ABC)+k\cdot$area$(\triangle ABC)=0$

Transitivity: by rational number property. Reflexivity: since $0$ is rational. Symmetry: negate a rational number gives rise to a rational number. So it's an equivalence relation.

  So $F(A,B,C,D)=BC'D+AB'C+A'CD'$

### 13.9

* Base $\mathscr B\sub \mathscr U$: that $\forall W\in\mathscr U,\forall x\in W, \exists V\in\mathscr B, x\in V$.

  + Totally didn't hear nothing

## 9.8 (f)

(a): The other states are $\forall q\in Q, \{q\}$.

+ Bayes theorem
+ Independence on fair coins: $P(H_2\mid H_1 F)=\frac12, P(H_2\mid F)=\frac12\implies H_1 \perp H_2 \mid P$. Also that $P(H_2\mid H_1 F^C)=\frac34, P(H_2\mid F^C)=\frac34$.
  + $P(H_1)=P(F)P(H_1\mid F)+P(F^C)P(H_1\mid F^C)$ decomposed probability. $=\frac12\frac12+\frac12\frac34=\frac58$.
  + $P(H_2)=$ the same.
  + $P(H_1 H_2)=$ $P(F)P(H_1H_2\mid F)+P(F^C)P(H_1H_2\mid F^C)=$ $\frac12(\frac12)^2+\frac12(\frac34)^2=\frac{13}{32}$ does not equal to the multiplication.
+ Conditionally independence does not imply unconditional independence
+ Alice and Bob: unconditionally independent but conditionally dependent
+ Baby cries
  + $c=P(C)=P(H\cup T)=P(H)+P(T)-P(H\cap T)$
  + Notation. $P(H\cap T)=P(HT)$
  + $c=h+t-ht$
  + $P(H\mid C)=\frac{P(H)P(C\mid H)}{P(C)}=\frac hc, P(T\mid C)=\frac tc$, $P(HT\mid C)=\frac{ht}c$
+ $P(S)=P(J)P(S\mid J)+P(J^C)P(S\mid J^C)$

+ ${\rm OUT8}=Q_1Q_2$

+ Unique limit point for all convergent sequences
  + Motivation of Hausdorff spaces
+ Any one-point set in a Hausdorff space is closed
  + Proof by definition
+ Compact spaces in a Hausdorff space is closed

To show that $\R^2/(\Z\times\Z)\simeq S^1\times S^1$, we observe that points in $\R^2/(\Z\times\Z)$ can be represented as $(a+i, b+j)$ for $i, j\in\Z$ and $a,b\in[0,1)\sub\R$, where $(a+i_1,b+j_1)$ and $(a+i_2,b+j_2)$ belong to the same equivalent class for any $i_1,i_2,j_1,j_2\in\Z$, so when considering elements in $\R^2/(\Z\times\Z)$, we can safely forget about $i$ and $j$. We think of $S^1$ as $[0,1)/\sim$ where $\sim$ equalizes $0$ and $1$, and the map $(a+i,b+j) \mapsto (a,b)$ is evidently continuous and bijective (the proof is similar to the proof that the identity function is continuous and bijective).

(a): So $\int^1_0{xf_X(x)dx}=\int^1_0{(ax+bx^3)dx}=\frac35$, so $\frac{2a+b}4=\frac35$. Then, $\int^1_0{(a+bx^2)dx}=1$, so $a+\frac b3=1$. Solving it gets $a=\frac35,b=\frac65$.

(b): $\frac12(1+\frac1{\sqrt2})\simeq 0.85$.

* Deformation retract
  * Retract that is homotopic to id
  * Strong: that this homotopy is relative
* Equivalence of paths

# Homework 3 Math 427

+ Homework
  + $\measuredangle BOC\equiv 0,\pi\implies 2\measuredangle BOC\equiv 0$
  + $\measuredangle BOC\equiv \measuredangle AOC-\measuredangle AOB$
+ Triangle congruence
  + Isosceles triangle
  + SAS, ASA (construct a new point, prove the same point), SSS (need an important lemma)
  + $AC=BC\implies \measuredangle ABC\equiv \pm\measuredangle BAC$
  + $\triangle ABC\cong\triangle BAC$
  + 

$ADD~2~1=2~SUCC~1=(SUCC(SUCC(1)))=3$

+ $\overline{A\cup B}\subseteq\overline A \cup \overline B$: so $\overline A \cup \overline B$ contains $A$ and $B$ and is closed. Any closed set containing $A\cup B$ also contains $\overline{A\cup B}$, so $\overline{A \cup B}$ is contained by $\overline A \cup \overline B$.
+ $\overline{A\cup B}\supseteq\overline A\cup \overline B$: for $x\in \overline A \cup \overline B$, either $x\in \overline A$ which means for all closed set $O$ containing $A$, $x\in O$. There are less such sets containing $A \cup B$, so $x\in \overline{A\cup B}$.

+ | Current | Input | Next  | Output |
  | ------- | ----- | ----- | ------ |
  | START   | T     | $T_1$ | 0      |
  | START   | A     | START | 0      |
  | $T_1$   | T     | START | 0      |
  | $T_1$   | A     | $A_1$ | 0      |
  | $A_1$   | T     | $T_2$ | 0      |
  | $A_1$   | A     | START | 0      |
  | $T_2$   | T     | START | 0      |
  | $T_2$   | A     | START | 1      |

![image-20220310165017387](h6.assets/image-20220310165017387.png)

* Recall the def. of top spaces and cont. functions
  * Conv. sequences in top spaces
  * For closed set $C$, $\overline{C^o}=C$, but for open set $W$, it's not necessarily true that $\overline{W}^o=W$. Example: $W=\R \setminus \{0\}$
  * Boundary of set (in space $X$) $\part A=\overline A \setminus A^o$, and $\forall x. \part A \iff$ any open neighborhood of $x$ intersects with $A$ and $X\setminus A$
    * Open neighborhood = open set containing $x$
* Cont. function: preimage of closed sets are closed
* Isomorphism: continuous function that has a continuous inverse

By proposition 2.13, $\measuredangle AOC\equiv\measuredangle BOD$, and since $O$ is a midpoint, $AO=OB$ and $CO=OD$. By Axiom IV, $\triangle AOC\cong \triangle BOD$, so $AC=BD$. $\blacksquare$

So, $\frac{XY'}{X'Y}=\frac{PX}{PY}=\frac{PY'}{PX'}$ (which means $PX\cdot PX'=PY\cdot PY'$),$\frac{PY}{PY'}=\frac{YZ'}{Y'Z}, \frac{PX}{PX'}=\frac{XZ'}{X'Z}$. Putting everything together results in $XY'\cdot ZX'\cdot YZ'=X'Y\cdot Z'X\cdot Y'Z$.

||O|A|B|AB|$\chi^2$|
|:-:|:-:|:-:|:-:|:-:|:-:|
|Rh.positive|146.40|178.93|110.61|52.05|2.0418|
|Rh.negative|33.60|41.07|25.39|11.95|8.8963|

## 5.13 (b)

(b) It is supposed to be normally distributed.

(b): $E(X)=\frac{3a-a}{2}=a=3$.

  + Let $f:\mathbb{2\to2}$

By corollary 1.9 (and the transitivity of if-and-only-if), we need to show $\triangle BOC$'s angles are either $0$ or $\pi$ $\iff$ $2\measuredangle AOB\equiv 2\measuredangle AOC$.

## Math 427 HW 12

1. Let $n$ be the number of states in $N$, which is the input.
2. Enumerate all strings of length $n$ with alphabet $\Sigma$, test these strings against $N$.
3. If any string is accepted, then reject. Otherwise accept.

By the properties of metric spaces, the Manhattan metric space satisfies $d(A,B)=0\implies A=B$ (and same for the maximum metric space), so being the same point in one implies being the same point in another. So they are isometric.

## Problem 14.6 (i)

## Math 427 HW 14

2. It is unambiguous. The equivalent unambiguous grammar is the same but replace `<n>` with the following rule:

+ (b) Assume $(\alpha\ket0+\beta\ket1)(\alpha'\ket0+\beta'\ket1)=$ $\frac12\ket{00}+\frac12\ket{01}+\frac12\ket{10}-\frac12\ket{11}$.

(a) Null: $H_0:\mu_1-\mu_2=0$, alternative: $H_1:\mu_1-\mu_2<0$

$A'+BC'$

(b) It's $(X\mid H_0)\sim Bin(30, \frac16)$.

## 9.6

(c) So $f_{Y\mid X}(y\mid x)=$ $\frac{f(x,y)}{f_X(x)}=$ $\frac{\frac1x}{1}=\frac1x$. So $(Y\mid X)\sim Uni(0,x)$.

(c) The $p$-value is $P(\chi_1^2>1.354)=0.2446>\alpha$
so we do not reject the null hypothesis.

## 2.3 (c)

By hint,
$$
\begin{align*}
\frac{L(\hat\theta_1)}{L(\hat\theta_0)}
&=\frac{\theta_1^{\sum_{i=1}^n X_i}(1-\theta_1)^{n-\sum_{i=1}^n X_i}}{\theta_0^{\sum_{i=1}^n X_i}(1-\theta_0)^{n-\sum_{i=1}^n X_i}}\\
&= \left(\frac{1 - \theta_0}{1 - \theta_1}\right)^n  \left(\frac{\theta_0 (1 - \theta_1)}{\theta_1 (1 - \theta_0)}\right)^{\sum_{i=1}^n X_i}
\end{align*}
$$
Note that $\left(\frac{1 - \theta_0}{1 - \theta_1}\right)^n$ is a known constant and $\frac{\theta_0 (1 - \theta_1)}{\theta_1 (1 - \theta_0)}$ is also a known constant. Replacing them with $u$ and $v$, we get $\frac{L(\hat\theta_1)}{L(\hat\theta_0)}=u\times v^{\sum_{i=1}^n X_i}$. The LRT states that if $\frac{L(\hat\theta_1)}{L(\hat\theta_0)}=u\times v^{\sum_{i=1}^n X_i}>c_0$ for some constant $c_0$, then we reject $H_0$. So:
$$
\begin{align*}
u\times v^{\sum_{i=1}^n X_i}&>c_0\\
v^{\sum_{i=1}^n X_i}&>\frac{c_0}{u}\\
{\sum_{i=1}^n X_i}&>\log_v{\frac{c_0}{u}}\\
\end{align*}
$$
So, the LRT is to reject $H_0$ if ${\sum_{i=1}^n X_i}>\log_v{\frac{c_0}{u}}$ (where $c_0,u,v$ are all constants, so this expression as a whole is a constant too).

This is a homotopy between $g_0 f_0$ and $g_1 f_1$.

## Problem 17.9 (m)

![image-20211021165247305](lab7.assets/image-20211021165247305.png)

## 1 a

(e) $x=1,y=24,z=48$

(h) $Var(Y)=E(Y^2)-E(Y)^2=$ $(\int^1_0\int^y_0 y^2(3-3x)d(xy))-\frac58^2=$ $\frac9{20}-\frac{25}{64}=\frac{19}{320}$. Thus $\sigma(Y)=\sqrt{\frac{19}{320}}=$ $\frac18\sqrt{\frac{19}5}$.

## 1 b

2. (a): $\frac{\left(\matrix{4\\4}\right)}{10^4}=\frac{3}{1250}$

(b) Under $M_1$, $\mu\sim N(15, 5^2)$.

|$\frac{(X_{i,j}-E_{i, j})^2}{E_{i, j}}$|Union|Confederate|
|--|-----|-----|
|Killed|6.9144|8.3242|
|Wounded|1.0535|1.2683|
|Missing/Captured|48.645|58.563|

Truth table:

+ Closed subset of a compact space is compact.

By 5.3 (I think I should be allowed to use it as a corollary, as it's already in the last homework which I proved it 😂), the perpendicular bisector $\ell$ to $[AB]$ should intersect $[AC]$. Say $\ell$ intersects with $[AB]$ at $O$, and intersects $[AC]$ at $X$. Since $\ell$ is a perpendicular bisector, $\triangle AXO\cong\triangle BXO$ (corollary of theorem 5.2), so $\measuredangle CAB=\measuredangle XAO\equiv \measuredangle XBO$. Since $\measuredangle CBO=\measuredangle CBX+\measuredangle XBO$, $|\measuredangle ABC|\equiv |\measuredangle CBO|$, and $\measuredangle CBX>0$, $|\measuredangle ABC|>|\measuredangle CAB|$.

By:  (@psu.edu)

## 1.16

![image-20211028225746613](writeup.assets/image-20211028225746613.png)

  + Superdense coding is sending classical info by sending qubits, while teleportation is sending qubits by sending classical info
  + $U\ket{k}$ is the $k+1$-th column of $U$ and these columns are orthonormal
  + Incomplete measurements

We prove this set-equivalence by proving two subset relations.

Since every component of a compact subset is bounded, the subset as a whole is bounded.

![image-20211021165446301](lab7.assets/image-20211021165446301.png)


   (b): It is dependent because "elder having the disease" implies "mother having the disease" implies "younger is more likely to have the disease", but conditioning the status of mother makes them independent.

## Problem 13.4 (a)

| $J$  | $K$  | $Q^*$         |
| ---- | ---- | ------------- |
| 0    | 0    | $Q$           |
| 0    | 1    | 0             |
| 1    | 0    | 1             |
| 1    | 1    | $\overline Q$ |

(g) Yes, by using the asymptotic distribution of the parameter $\theta$, we actually get a continuous distribution, and there is an exact rejection region for $\alpha=0.05$.

(a) Joint PDF:
$$
\begin{align*}
f(\mu,\sigma^2\mid x)
&=f(\mu, \sigma^2)f(x\mid \mu, \sigma^2)\\
&=\sigma^{-n-2}e^{-\frac1{2\sigma^2}\sum_i(X_i-\bar X)^2+\sum_i(\bar X-\mu)^2}\\
&=\sigma^{-n-2}e^{-\frac{(n-1)s^2}{2\sigma^2}+n(\bar X-\mu)^2}
\end{align*}
$$
Let $Q=(n-1)s^2+n(\bar X-\mu)^2$, which is constant to $\sigma^2$. Let $\omega=\frac Q{2\sigma^2}$, and notice $\sigma^{-n-2}=\left(\sigma^{-\frac{n+1}2}\right)^2$. Also $\frac{\part\omega}{\part\sigma^2}=-\frac Q{2(\sigma^2)^2}$, so $\frac{\part\sigma^2}{\part\omega}=-\frac Q{2\omega^2}$. By that the integration can be written as:
$$
\begin{align*}
f(\mu\mid x)&=\int_{\R^-}\left(\sigma^{-\frac{n+1}2}\right)^2e^{-\frac Q{2\sigma^2}}\left(-\frac Q{2\omega^2}\right) d\omega\\
&=\frac Q 2^{-n/2}\int_{\R^+}\omega^{\frac{n+2}2}\omega^{-2}e^{-\omega}d\omega\\
&\propto Q^{-n/2}\int_{\R^+}\omega^{\frac{n-2}2}e^{-\omega}d\omega\\
&\propto Q^{-n/2}\\
&\propto \left(1+\frac{n(\bar X-\mu)^2}{(n-1)s^2}\right)^{-n/2}
\end{align*}
$$
(b) It follows $t_{n-1}$-distribution, where $a=\bar X$, $b^2=\frac{s^2}{n}$ thus $b=s/\sqrt n$. Therefore, the distribution is $t_{n-1}(\bar X, s/\sqrt n)$.


  + For $X,Y\notin(PQ)$, there's $X,Y$ lie on the same half-plane $\iff[XY]\cap(PQ)=\empty$

By $n=256>30$, we may use the approximate normal distribution. So, by the property of standanrd normal distribution, the $95\%$ confidence interval gives us the following inequality:
$$
P\left(-1.96<\frac{\bar X-\lambda}{\sigma}<1.96\right)=0.95
$$
By CRLB, $S=\sqrt{\frac{1}{I(\lambda)}}$. So we need to compute $I(\lambda)$, which is by the second derivative of the log-likelihood function, so according to Poisson's PMF:
$$
\begin{align*}
L(\lambda)&=\prod^n_{i=1}\frac{\lambda^{x_i}e^{-\lambda}}{x_i!}\\
&=e^{-n\lambda}\prod^n_{i=1}\frac{\lambda^{x_i}}{x_i!}\\
&=e^{-n\lambda}\frac{\lambda^{\sum^n_{i=1}x_i}}{\prod^n_{i=1} (x_i!)}
\end{align*}
$$
Then:
$$
\begin{align*}
\ell(\lambda)&=\ln{(e^{-n\lambda})}-\ln{\left(\prod^n_{i=1} (x_i!)\right)}+\ln{\left(\lambda^{\sum^n_{i=1}x_i}\right)}\\
&=-n\lambda-\sum^n_{i=1}\ln{(x_i!)}+\ln{\lambda}\sum^n_{i=1}x_i\\
\ell'(\lambda)&=-n-0+\frac1{\lambda}\sum^n_{i=1}x_i
=\frac{n\bar X}\lambda -n\\
\ell''(\lambda)&=-\frac{n\bar X}{\lambda^2}
\end{align*}
$$
When $\ell'(\lambda)=0$, $\lambda=\bar X$, so $\hat\lambda_{MLE}=\bar X$, and the Fisher's information is:
$$
\begin{align*}
I(\lambda)&=-E\left(\ell''(\lambda)\right)=E\left(\frac{n\bar X}{\lambda^2}\right)\\
&=\frac{n}{\lambda^2} E\left(\bar X\right)=\frac{n}{\lambda^2} \mu=\frac{n}{\lambda^2} \lambda\\
&=n/\lambda
\end{align*}
$$
When $n$ is large, $I(\lambda)=$ $I(\hat\lambda_{MLB})=n/\hat\lambda_{MLB}$ $=n/\bar X$, so $S=\sqrt{\bar X/n}=$ $\sqrt{\bar X/256}=\sqrt{\bar X}/16$, so we go back to the original inequality and it's
$$
P\left(-1.96<\frac{\bar X-\lambda}{\sqrt{\bar X}/16}<1.96\right)=0.95
$$
So the interval is approximately:
$$
\fbox{$\left(\bar X-\frac{1.96\sqrt{\bar X}}{16}, \bar X+\frac{1.96\sqrt{\bar X}}{16}\right)$}
$$

The equation holds as in the final form, the LHS is positive ($e-2>0, e^r>0$) while the RHS is negative ($e^{-1}-2<0,e^{-r}>0$).

# Math 429 HW 5

# Math 429 HW 7

Actually, $s$ _can_ be pumped. Example 1.73 shows that $s$ cannot be pumped *in the language $0^n1^n$*, but if we change the language to $0^*1^*$, we can pump it.

# Math 429 HW 8

# Math 429 HW 1

3. In a circle means we can "rotate" a permutation without changing its configuration. So, it's the permutation of 5 divided by 5 -- $\frac{5!}5=4!=24$. It is not hard to generalize this to $n$ -- it should be $(n-1)!$.

# Math 429 HW 2

(e) $E(Y_1\mid Y_2=y_2)=\frac{y_2}2,$ $Var(Y_1\mid Y_2=y_2)=\frac{y_2^2}{12}$.

# Math 429 HW 3

# Math 429 HW 4

### 15.9

# Math 429 HW 9

   `<n> -> <n><d> | <d>`

### 15.6

So all loops are contractible, thus simply connected.

PMF: $P(X=1)=0.3\times 1+0.5\times \frac12+0.2\times \frac13=\frac{37}{60}$, $P(X=2)=0.5\times\frac12+0.2\times\frac13=\frac{19}{60}$, $P(X=3)=0.2\times\frac13=\frac1{15}$.

![image-20211021232003505](hw6.assets/image-20211021232003505.png)

  | Present State | $X_{next}=0$ | $X_{next}=1$ | $X_{out}=0$ | $X_{out}=1$ |
  | ------------- | ------------ | ------------ | ----------- | ----------- |
  | A             | F            | B            | 0           | 0           |
  | B             | D            | A            | 0           | 0           |
  | D             | G            | A            | 1           | 0           |
  | F             | F            | B            | 1           | 1           |
  | G             | G            | D            | 0           | 1           |

(c) $f_X(x)=\int^1_x f(x,y)dy=$ $\int^1_x(3-3x)dy=$ $3x^2-6x+3$, where $x\in[0,1]$.

## 7.24

## Problem 16.11 (b)

That all gates are open, so nothing happens at the right-hand side of the diagram. Thus $M$ is not turned on. The capacitor is charged as the enabler of the charging circuit is on.

1. So, $\Gamma(1/2)=\int^\infty_0{x^{1/2-1}e^{-x}dx}=\int^\infty_0{x^{-1/2}e^{-x}dx}$. Replace $x^{1/2}$ with $u$ (so $u^2=x, \frac{du}{dx}=\frac12 x^{-1/2}=\frac 1{2u}$) gives us $\int^\infty_0{e^{-u^2}\cdot u\cdot \frac1{2u} \cdot du}=\frac12\int^\infty_0{e^{-u^2}}du$. Recall a result from the class that $\int^\infty_{-\infty}{e^{-\frac{x^2}2}dx}=\sqrt{2\pi}$. Note that the function is even, so $\int^\infty_{0}{e^{-\frac{x^2}2}dx}=\frac12 \int^\infty_{-\infty}{e^{-\frac{x^2}2}dx}=\frac{\sqrt{2\pi}}2$, so $\int^\infty_0{e^{-x^2}dx}=\sqrt{4\pi}=2\sqrt\pi$, so $\Gamma(1/2)=\sqrt\pi$.

## 7.26

1. (a): It is evident that $P(E\mid G)=p_B$ because the other must be $p_A$ so we only choose the $B$ blood type, and $P(E\mid G^C)=p_A\cdot p_B+p_B\cdot p_A$. So $P(E\mid G)P(G)=p_B\cdot \pi$ By the Bayes rule, $P(G\mid E)=\frac{p_B\cdot\pi}{p_B\cdot \pi+2p_A\cdot p_B(1-\pi)}=\frac{\pi}{\pi+2p_A(1-\pi)}$.

+ Archimedean property of reals
  + Must be a natural number $n$ that makes $an>b$ for any positive real $a$ and $b$
  + Proof: by contradiction, if there is an upper bound $b$, there is a least upper bound $ka$ (for $k\in\N$), and adding it by $a$ still makes an element in this subset of reals, contradicts the fact that $ka$ is the upper bound

| C\AB | 00   | 01   | 11   | 10   |
| ---- | ---- | ---- | ---- | ---- |
| 0    | 1    | 1    | 1    | 0    |
| 1    | 1    | 1    | 0    | 0    |

+ In `main`, we can access: `j`, `i`, `h` from line 1, and `a`, `b` from line 15.
+ In `A`, we can access `j`, `h` from line 1, `i` from line 9, and `x`, `y` from line 8.
+ In `B`, we can access `i`, `h` from line 1, `w` from line 2, and `j` from line 3.

4. .It's $\frac12$ due to the independence of two children's genders and seasons.

For chord $XZ$, $\measuredangle ZX'X\equiv\measuredangle ZZ'X$. Similarly $\measuredangle ZY'Y\equiv\measuredangle ZZ'Y, \measuredangle Z'ZY'\equiv\measuredangle Z'YY'$,$\measuredangle Z'XX'\equiv\measuredangle Z'ZX'$, $\measuredangle YY'X\equiv\measuredangle YX'X,\measuredangle Y'YX'\equiv\measuredangle Y'XX'$. By all of these six angle congruence, we obtain $\triangle ZPY'\cong \triangle Z'PY, \triangle ZPX'\cong\triangle Z'PX$, $\triangle XPY'\cong\triangle X'PY$.

(g) $Cov(X_1,X_2)=Cov(Y_1+Y_2,Y_1-Y_2)=$ $Cov(Y_1,Y_1)-$ $Cov(Y_1,Y_2)+$ $Cov(Y_2,Y_1)-Cov(Y_2,Y_2)=$ $Var(Y_1)-Var(Y_2)=$ $1-1=0$.

![image-20210930165410942](lab5.assets/image-20210930165410942.png)

(b) Using results in (a):
$$
\begin{align*}
I(\lambda)&=-E\left(\ell''(\lambda)\right)=-E\left(-\frac n{\lambda^2}\right)\\
&=E\left(\frac{n}{\lambda^2}\right)=\fbox{$\frac{n}{\lambda^2}$}\\
\end{align*}
$$
(c) When $n$ large, $I(\lambda)=I(\hat\lambda_{MLE})=\frac n{1/{\bar X}^2}=n{\bar X}^2$. So, $\sqrt{I(\lambda)}=$ ${\sqrt{n{\bar X}^2}}={\bar X\sqrt n}$. By asymptotic normality of MLEs:
$$
\begin{align*}
P\left(-1.96<\sqrt{I(\lambda)}\times \left(\hat\lambda_{MLE}-\lambda\right)<1.96\right)&=0.95\\
P\left(-1.96<\bar X\sqrt n\times \left(\frac 1{\bar X}-\lambda\right)<1.96\right)&=0.95\\
\end{align*}
$$
So the interval is:
$$
\fbox{$\left(\frac1{\bar X}-\frac{1.96}{\sqrt{n}\bar X}, \frac1{\bar X}+\frac{1.96}{\sqrt{n}\bar X}\right)$}
$$
(d) By $\Delta$ method, $\hat\theta_{MLE}\sim N(\theta, \theta^2/n)=N(\frac{\log2}\lambda,\frac{\log^2 2}{\lambda^2n})$. Also $\hat\theta_{MLE}=\frac{\log2}{\hat\lambda_{MLE}}=(\log 2)\bar X$. So:
$$
\begin{align*}
P\left(-1.96<\frac{\hat\theta_{MLE}-\theta}{\hat\theta_{MLE}/\sqrt n}<1.96\right)&=0.95\\
P\left(-1.96<\frac{(\log 2)\bar X-\theta}{(\log 2)\bar X/\sqrt n}<1.96\right)&=0.95\\
\end{align*}
$$
So the interval for $\theta$ is:
$$
\fbox{$\left({(\log2)\bar X}-\frac{1.96(\log2)\bar X}{\sqrt{n}}, {(\log2)\bar X}+\frac{1.96(\log2)\bar X}{\sqrt{n}}\right)$}
$$

$XY//X'Y'\implies \measuredangle OXY\equiv \measuredangle XYO\equiv \measuredangle OY'X'\equiv \measuredangle Y'X'O$.

It holds intuitively.

  $=(Z\otimes I)(\ket0\otimes\ket0)+(Z\otimes I)(\ket1\otimes\ket1)$

(a) $\int^1_0\int^{y_2}_06(1-y_2)dy_1dy_2=6(\frac12-\frac13)=1$.

+ Tensor product states and entanglement

## 13.6

## 13.1

## 13.3

Suppose they do intersect, mark the point of intersection as $O$. Since $\forall X'\in[PX), \measuredangle X'PQ\equiv\measuredangle XPQ$ and $\forall Y'\in[QY), \measuredangle YQP\equiv \measuredangle Y'QP$. So, $\measuredangle OPQ\equiv \measuredangle XPQ$ and $\measuredangle YQP\equiv \measuredangle OQP$. So, $O,X$ lie in the same half-plane complement to $(PQ)$, and $O,Y$ lie in the same half-plane complement to $(PQ)$. So $X, Y$ lie in the same half-plane complement to $(PQ)$, which leads to a contradiction.


$AB+BC+AC$

0. $\forall i\in I,f(i)\in U$. Then the loop is contractible by the simply-connectedness of $U$.
1. $\exists i, j\in I, f(i)\in U, f(j)\in V$. By earlier exercise 14.6 (i), $f$ can be subdivided into $\prod_{k\in J} f_k$ where $J$ is any index set and for each $k\in J$, $f_k$ is a path in either $U$ or $V$. By simply connectedness, every such path in $U$ is homotopy-equivalent to a point in $U$, and the same for $V$. Since $U\cap V$ is path-connected, we may choose the same point in $U\cap V$ such that every $f_k$ is equivalent to this point. Since points are "identity loops", we may say $f=\prod_{k\in J} f_k=\prod_{k\in J} 1=1$, so (the image of) $f$ is contractible.

(b)

We cleaned it up!

(a) Since $Y=\frac{S_1/d_1}{S_2/d_2}$, where $S_1, S_2$ are independent random variables with $\chi^2$-distributions with respective degrees of freedom $d_1$ and $d_2$. Then, $X=\frac1Y=\frac{S_2/d_2}{S_1/d_1}$. Since $S_1$ and $S_2$ are independent, they are interchangeable, so $X$ follows $F$-distribution with numerator $d_2$ and denominator $d_1$.

![image-20211118161539545](submission1.assets/image-20211118161539545.png)

+ Bayes rules
  + $P(A_i\mid B)=\frac{P(A_i \cap B)=P(A_i)P(B\mid A_i)}{P(B)}$
  + $P(A\mid B)=\frac{P(A)P(B\mid A)}{P(A)P(B\mid A)+P(A^C)P(B\mid A^C)}$
+ $B$: what actually happened
  $A$: the objective we want to compute
+ Reverse methodology
+ COVID: $\frac{12\%\times 95\%}{12\%\times 95\%+88\%\times5\%}\simeq 0.7215$
+ $A$ and $B$ are independent if $P(A\mid B)=P(A)$, same as $P(A\cap B)=P(A)P(B)$, denoted $A\perp B$
+ Disjointedness and independences are totally independent

If $f$ is open, it must preserve open sets, which satisfies the definition of quotient topology, so ${\mathscr U}_f$ is homeomorphism to $\mathscr U$.

![image-20210916230602628](hw3.assets/image-20210916230602628.png)

$f_*(n)=kn$ (integer multiplication).

# HW 5 Stat 414

|$i$|$1$|$2$|$3$|
|-----|-----|-----|-----|
|$p_i$|0.619|0.297|0.084|
|$50p_i$|30.95|14.85|4.20|

    ![image-20210910144254125](week3-3.assets/image-20210910144254125.png)

$\frac{P(X>s+t)}{P(X>t)}=\frac{(1-p)^{s+t}}{(1-p)^t}=(1-p)^s=P(X>s)$.

(b) `'(Racket is fun)`

$$
\begin{align*}
p_1(\lambda)&=P(Y=0)=\exp{-\lambda}\\
p_2(\lambda)&=P(Y=1)=\lambda\exp{-\lambda}\\
p_3(\lambda)&=1-p_1(\lambda)-p_2(\lambda)
\end{align*}
$$

Consider a compact subset $S$ of $\R$. The open covering $\{C_i\mid i\in[0,+\infty)\}$ defined by $C_i=(-i, i)$ (which is always open) must have a finite subcover. Note the fact that $C_i\sub C_j\iff i<j$, which means that $C_i$ forms a total ordering. So, there exists some $j\in[0,+\infty)$ such that $S\sub C_j$.

Locally simply-connected spaces admit universal coverings

+ Inscribed circles
  + Angles are equal because they're inscribed in a circle
+ Chord: 弦
+ Four points inscribed in same circle $\implies$ 对角 sum up to $\pi$
+ Circlines = circle or line
+ Arcs
  + Circlines and arcs

(d): $P(Z=1)=1-P(Z=2)-P(Z=0)=$ $1-0.4\times0.7-0.6\times0.3=0.54$.

## Problem 13.4 (f)

(c)

## 12.24 (d)

  This is a static-1 hazard.

+ Pappus' theorem: projective transformation + parallel theorems (what the fuck??)
  + A bunch of similar triangles due to parallel ⛛
+ How models are constructed
  + Find inversive transformations (much larger set)

Each string over $\{1\}$ uniquely corresponds to a natural number, and a language $L$ consists of a (potentially infinite) set of natural numbers. Suppose the set of $L$, let's denote it $\Gamma$, is countable, so by definition of countable there is a set isomorphism $\phi:\N\to\Gamma$, which means the elements of $\Gamma$ can be listed in order ($\phi(0), \phi(1), ...$). Now take $Q=\{i\in\N \mid i \notin \phi(i)\}$ which does not belong to $\Gamma$ but is another set of natural numbers, a contradiction that $\phi$ is isomorphism.

+ Feasible: if circuit size scales in polynomial

(a): Their scopes are limited to the block they're defined (after the declaration of course), and can be shadowed. Their lifetime starts from the first time the function is called, and ends at the end of the program (source: https://stackoverflow.com/a/246568/7083401).

module state_machine(x,reset,clk,output_state_reg,sevenseg); 

+ (c)
  $$
  \frac1{\sqrt2}\begin{bmatrix}1&0&1&0\\0&1&0&1\\1&0&-1&0\\0&1&0&-1\end{bmatrix}
  \begin{bmatrix}1&0&0&0\\0&1&0&0\\0&0&1&0\\0&0&0&i\end{bmatrix}
  \frac1{\sqrt2} \begin{bmatrix}1&1&0&0\\1&-1&0&0\\0&0&1&1\\0&0&1&-1\end{bmatrix}
  \begin{bmatrix}1&0&0&0\\0&0&1&0\\0&1&0&0\\0&0&0&1\end{bmatrix}\\
  =\frac12 \begin{bmatrix}1&0&1&0\\0&1&0&i\\1&0&-1&0\\0&1&0&-i\end{bmatrix}
  \begin{bmatrix}1&1&0&0\\1&-1&0&0\\0&0&1&1\\0&0&1&-1\end{bmatrix}
  \begin{bmatrix}1&0&0&0\\0&0&1&0\\0&1&0&0\\0&0&0&1\end{bmatrix} \\
  =\frac12 \begin{bmatrix}1&0&1&0\\0&1&0&i\\1&0&-1&0\\0&1&0&-i\end{bmatrix}
  \begin{bmatrix}1&0&1&0\\1&0&-1&0\\0&1&0&1\\0&1&0&-1\end{bmatrix} \\
  =\frac12\begin{bmatrix}1&1&1&1\\1&i&-1&-i\\1&-1&1&-1\\1&-i&-1&i\end{bmatrix}
  $$

Since $f$ preserves distances, $AX=A f(X)=AY$, and similarly $BX=BY, CX=CY$. So $\triangle ABX\cong\triangle ABY$, so $\measuredangle ABX\equiv\pm\measuredangle ABY$. Also since $X\not=Y$, $\measuredangle ABX\equiv-\measuredangle ABY$, and similarly $\measuredangle CBX\equiv-\measuredangle CBY$. So, $\measuredangle ABC\equiv-\measuredangle ABC$, therefore $\measuredangle ABC\equiv0$ or $\pi$, which implies the degeneracy of $\triangle ABC$, contradicts the presumptions.

Note that I'm using $\fbox{G}$ symbol which can be replaced with either a XOR gate or a NAND gate, since they work the same way in our case (we never input two zeros at the same time).

(a)![image-20220427144259171](hw7.assets/image-20220427144259171.png)

Suppose the 2D tape has a coordinate on it, so there is an origin point. We build up a pathway from the origin (marked in red) and goes through the entire plane.

  // Sequential logic to update the current state
  always@(posedge clk or posedge reset)
  begin 
    if(reset) begin
      current_state<=s0;
      sevenseg_input_reg <= sevenseg_input;
    end else begin
      current_state<=next_state; 
      sevenseg_input_reg <= sevenseg_input;
    end
  end
  // -----------------------------------------------

### 2.1 b)

## Problem 18.4 (g)

(c) The $p$-value is $P(\chi_2^2>124.77)=8.064\times 10^{-28}<\alpha$,
so we reject the null hypothesis.

(a) Expected value of $\hat{\sigma}^2_{MLE}$:
$$
\begin{align*}
E(\hat{\sigma}^2_{MLE})&=E\left( \frac{\sum^n_{i=1}(X_i-\bar X)^2}n \right)\\
&=\frac1n E\left(\sum^n_{i=1}(X_i-\bar X)^2\right)\\
&=\frac1n E\left(\sum^n_{i=1}X_i^2-\bar X^2\right)\\
&=\frac1n \left(\sum^n_{i=1}E(X_i^2)-nE(\bar X^2)\right)\\
&=\frac1n \sum^n_{i=1}E(X_i^2)-E(\bar X^2)\\
&=\frac1n \sum^n_{i=1}(Var(X_i)+E^2(X_i))-(Var(\bar X)+E^2(\bar X))\\
&=\frac1n \sum^n_{i=1}(\sigma^2+\mu^2)-\left(\frac{\sigma^2}n+\mu^2\right)\\
&=\sigma^2+\mu^2-\frac{\sigma^2}n-\mu^2\\
&=\fbox{$\sigma^2\left(1-\frac1n\right)$}
\end{align*}
$$
Therefore biased, because it's unequal to $\sigma^2$. Then consider the expected value of $S^2$:
$$
\begin{align*}
E(S^2)&=E\left(\frac{n}{n-1}\hat\sigma^2_{MLE}\right)\\
&=\frac{n}{n-1}E(\hat\sigma^2_{MLE})\\
&=\frac{n}{n-1}\sigma^2\left(1-\frac1n\right)\\
&=\fbox{$\sigma^2$}
\end{align*}
$$
Which is unbiased too.

Observation:

# Lab 9

$F=CD\overline{AB}$

Truth table

# Lab 8

$$
\begin{align*}
F&=\overline{\overline A+\overline B}+\overline{(A+C)(B+\overline C)}\\
&=AB+\overline{A+C}+{\overline{B+\overline C}}\\
&=AB+\overline A~\overline C+\overline B~C\\
&=AB+A+C+B+\overline C\\
&=A+B\\
&=\overline{\overline A~\overline B}
\end{align*}
$$

   (b): This is also similar to the "LA" problem where only $7$ cookies are free of choice, so $\left(\matrix{3+7-1\\7}\right)=36$.

2. (a): $P(O^CY^C)=P(O^CY^C\mid M^C)P(M^C)$ $+P(O^CY^C\mid M)P(M)$ $=1\cdot\frac23+\frac14\cdot \frac13=\frac{8+1}{12}=\frac34$.

# 4.7

The decoder is a 138N decoder.

+ Natural numbers: start from $1$
+ Roots of polynomials

Apparently, the only case when $\Z\times \pi_1(Y)$ is finite is when $\pi_1(Y)$ is $0$ (otherwise it's an infinite group), so it cannot be isomorphic to $\Z_2$.

| Top spaces        | Groups           |
| ----------------- | ---------------- |
| Coverings         | Subgroups        |
| Regular coverings | Normal subgroups |

(f) $\beta=F_X(8)$ for a different $X$ (not as in (e), but in (d)), and by the references given, $\beta=0.286$. The power $\pi=1-\beta=0.714$.

## Problem 18.4 (f)

So we need to calculate $\Lambda(X)=\frac{L(\mu, \sigma_{0,MLE}^2)}{L(\mu, \sigma_{MLE}^2)}$, and $\alpha=P(\Lambda(X)\leq c\mid H_0)$.
Note that:
$$
\begin{align*}
\hat\sigma_{0,MLE}&=\frac1n\sum(x_i-\mu_0)^2\\
\hat\sigma_{MLE}&=\frac1n\sum(x_i-\bar x)^2
\end{align*}
$$
Using that we can simplify $\Lambda(X)$:
$$
\begin{align*}
\Lambda(X)&=\frac{L(\mu, \sigma_{0,MLE}^2)}{L(\mu, \sigma_{MLE}^2)}\\
&=\frac{\prod^n_{i=1}\left(
  \frac{1}{\sqrt{2\pi \sigma_{0,MLE}^2}}
  \exp{\left(-\frac{(x_i-\mu_0)^2}{2\sigma_{0, MLE}^2}\right)}
\right)}{\prod^n_{i=1}\left(
  \frac{1}{\sqrt{2\pi \sigma_{MLE}^2}}
  \exp{\left(-\frac{(x_i-\bar x)^2}{2\sigma_{MLE}^2}\right)}
\right)}\\
&=\frac{(2\pi \sigma_{0,MLE}^2)^{-n/2}
  \exp{\left(-\frac{\sum^n_{i=1}(x_i-\mu_0)^2}{2\sigma_{0, MLE}^2}\right)}
}{(2\pi \sigma_{MLE}^2)^{-n/2}
  \exp{\left(-\frac{\sum^n_{i=1}(x_i-\bar x)^2}{2\sigma_{MLE}^2}\right)}}\\
&=\left(\frac{\sigma_{0,MLE}^2}{\sigma_{MLE}^2}\right) ^{-n/2}
  \exp{\left(-\frac{\sum^n_{i=1}(x_i-\mu_0)^2}{2\sigma_{0, MLE}^2}+\frac{\sum^n_{i=1}(x_i-\bar x)^2}{2\sigma_{MLE}^2}\right)}\\
\end{align*}
$$
By homework 2 problems, we know that:
$$
-\frac{\sum^n_{i=1}(x_i-\mu_0)^2}{2\sigma_{0, MLE}^2}+\frac{\sum^n_{i=1}(x_i-\bar x)^2}{2\sigma_{MLE}^2}
=0
$$
This means $\Lambda(X)=\frac{\sigma_{0,MLE}^2}{\sigma_{MLE}^2}^{-n/2}$.
Given $H_0$, $\sigma_{0,MLE}^2=1.2^2$, so $\Lambda(X)=\frac{1.2^2}{\sum^n_{i=1}(x_i-\bar x)^2}^{-n/2}$.

## Problem 12.10 (b)

+ $E(g(x)\mid Y=y)=???$
+ Conditional expectation is the proportion between the joint and the marginal
+ $E(x\mid Y=y)$ will have no $x$ in the expression, but $y$ may remain.
+ Expectation $E(X\mid Y)$: first compute expectation $h(y)=E(X\mid Y=y)$, then $E(X\mid Y)=h(Y)$.
+ "Given $Y$" is random, but $Y=y$ is a function over the actual instantiation.
+ Adam's law: the expectation of $X$ is the expectation of expectation of $X$ given any other r.v.
+ $E(X)=\int x f_X(x)dx=$ $\int (x\int f_{X,Y}(x,y)dy)dx=$ $\iint x f_{X,Y}(x,y) dxdy=$ $\iint x f_Y(y)f_{X\mid Y}(x,y)dxdy$ OMG
+ Eve's law: $Var(X)=E(Var(X\mid Y))+Var(E(X\mid Y))$
+ 

For closed $A\sub X$, since $X$ is compact then $A$ is also compact, and compact subsets are sent by continuous maps to compact spaces, so $f(A)\sub Y$ is also compact, and compact subsets of a Hausdorff space are closed, so $f$ sends closed sets to closed sets, so $f$ sends their complements to their images' complements, so $Y$ has the quotient topology generated by $f$.

When $X=1,Y=0$:

### 2.1 a)

So the length of the leg, $AB$, is in Euclidean perspective $\frac r2$ assuming $r$ the Euclidean radius of the absolute. The hyperbolic length is $\ln{\frac{1+\frac r2}{1-\frac r2}}=\ln{\frac{r+2}{2-r}}$.

## 5.3 (b)

## Constructions

(b) So, `foo2` calls `bar(x, y)`, then in `bar`, `x = x - y = -5`, `y` unchanged, then it returns `2 * x` which is `-10`, so `sum` is assigned to `-10`, then `sum = sum + x = -10 + -5 = -15`.

Define $M$ to work as follows. First we store $w$ on the tape, and check if it's equivalent to the input $x$. If no, reject, if yes, run $M$. If $M$ halts on $w$, then $M'$ halts; otherwise we don't care anyway.

(a) Since they arrive exactly on time, it's uniform distribution. So the average time to wait is $5$ minutes.

### SOP

## 9.17

Picture of the testing circuit:

+ Probability mass function (PMF) of a random variable $X$: $p_X(x)=P(X=x)$.
+ Toss two coins, let $X$ be number of heads. $p_X(x)=\frac14$ for $x\in\{0, 2\}$, $\frac12$ for $x=1$, and $0$ otherwise.
  + Example: given distribution, compute probability
+ $p_X(x)\in[0,1]$, $\sum_x p_X(x)=1$
+ Cumulative distribution (CDF): $F_X(x)=P(X\leq x)$

  + $f$ - phase-shift

| CD\AB | 00   | 01   | 11   | 10   |
| :------------ | ---- | ---- | ---- | ---- |
| 00    | 1    | 0    | 0    | 1    |
| 01    | 0    | 1    | 0    | 0    |
| 11    | 0    | 0    | 0    | 1    |
| 10    | 1    | 1    | 1    | 1    |

## Problem 12.10 (a)

![image-20211021230714392](hw6.assets/image-20211021230714392.png)

(a) $P(X=x)=\frac1{10}$ for $x\in[1,10]$ due to "with replacement", and $p=P(X\geq 8)=3\times\frac1{10}=0.3$, so by geometric distribution the expectation is $\frac1p=\frac{10}3\simeq3.33$.

  // -----------------------------------------------
  // Name the FSM States
  parameter s0 = 3'b000, s1 = 3'b001, s2 = 3'b010,
            s3 = 3'b011, s4 = 3'b100, s5 = 3'b101,
            s6 = 3'b110, s7 = 3'b111;
  // -----------------------------------------------
  
  // -----------------------------------------------
  // Instantiate the 7-segment module
  seven_segment_display SSD(sevenseg_input_reg, sevenseg);
  // -----------------------------------------------

Critical value $c$ makes $P(\chi_1^2> c)=\alpha=0.05$,
by [calculator](http://courses.atlas.illinois.edu/spring2016/STAT/STAT200/pchisq.html) $c=3.841$.
Since $1.354\leq 3.841$, we do not reject the null hypothesis.

## Math 427 HWA-13

+ Binomial dist.:
  + Independence of trials
  + Binary result
  + Fixed number of trials $n$
  + Fixed succeed rate $p$
  + Notation: $Bin(n, p)$, $p(X=x)=\left(\matrix{n\\x}\right)p^x(1-p)^{n-x}$
  + Expectation: $E(x)=np$
  + Variance: $np(1-p)$
  + Standard deviation: sqrt of variance
+ Hypergeometric dist.:
  + Choose without replacement, result binary, fixed number of choices $n$, fixed number of wanted $k$, choosing from a total number of $l$
  + What the fuck is "support"? "Domain" (???)
  + Notation: $HG(n, k, l)$
  + Expectation: $n\frac kl$
  + Variance: TODO
+ Negative binomial dist.:
  + $NB(n, p)$ for continue trying until there are $n$ successes
  + Expectation: $\frac np$
+ Continuous Distribution
  + $f_X(x)$
  + $P(X\in[a,b])=\int^b_a{f_X(x)dx}$ Can be replaced with open intervals
+ Cumulative distribution functions $F(x)=P(X\leq x )$
  + $x\to-\infty$: $F(x)=0$
  + $x\to+\infty$: $F(x)=1$
  + Non-decreasing and continuous

+ c) ![image-20210930220241029](hw5.assets/image-20210930220241029.png)

+ A test is called a level-$\alpha$ test if Type I error rate $\leq\alpha$

## 8.14 (i)

By def., $\empty\in \mathscr U$ and $\R\in \mathscr U$, so the first condition of topology is satisfied. The intersection of two half-open half-closed intervals $[s_1, t_1), [s_2, t_2)$ on $\R$ are either empty (and we already know $\empty\in\mathscr U$) or nonempty $\big[\max(s_1, s_2), \min(t_1, t_2)\big)\in \mathscr U$ (by the def. of $\mathscr U$), so the second condition of topology is also satisfied. For unions $\bigcup_{i=0}^n{[s_i, t_i)}$, it is evident that $\big[\min(s_i), \max(t_i)\big)\in \mathscr U$, satisfying the third condition. 

Review

## Cmpen 270

(e) So we need to test if $\frac{\bar X-\bar Y}{\sqrt{\frac{\sigma_1^2}n+\frac{\sigma_2^2}m}}<-1.96$, plugging in that $\sigma_1=1$, $\sigma_2=1.5$, $n=20$, $m=10$, and $\bar X=4, \bar Y=7$, we get $\sqrt{\frac{\sigma_1^2}n+\frac{\sigma_2^2}m}=\sqrt{\frac{1}{20}+\frac{1.5^2}{10}}=0.5244$, and the left-hand-side becomes $\frac{4-7}{0.5244}\approx-5.7208$.

(a) $FV((λx.λy.y~x)(λz.y))=$ $FV(λx.λy.y~x)\cup FV(λz.y)=$ $\empty\cup \{y\}=\{y\}$

To show $p$ to be a homeomorphism, we show $p_*$ to be an isomorphism. Since $X$ is simply-connected and $p$ continuous, so $p_*$ is a group homomorphism targeting $0$, so it remains to show that $\tilde X$ is simply-connected.  ????

+ Construct $t\in[0,1]$, let $QQ_t=t\cdot QQ'$. Show $\ang PQ_t X\not=0$.
+ Need $t\mapsto Q_t$, use $\epsilon\delta$ notation ($\delta=\frac\epsilon{QQ'}$).
+ Intermediate value theorem + proof by negation: if they have the different sign, then for some $t$ there must be $\ang PQ_t X=0$.

+ a)![image-20210930212242877](hw5.assets/image-20210930212242877.png)

(a): $\frac{580-480}{100}=1$.

If: suppose for the sake of contradiction that we have a function that sends a connected space surjectively to a 2-pointed discrete space, then the two points' "one-point open set" must be lifted to distinct open sets, which contradicts the connectedness.

+ HW: about distinguishing quantum states

Each dynamic link points to the stack frame below, and each return address points to the place where the function is called. The bottom stack frame belongs to the function that calls `summation(3, 6)`.

We can take three mutually exclusive arcs on the absolute, whose endpoints (regarded as ideal points) determine one h-line per arc. These three h-lines do not intersect with each other because the corresponding arcs are mutually exclusive.

(b) ![image-20220413163159797](hw10.assets/image-20220413163159797.png)

So the total $\chi^2$ is $5.469$.
Degrees of freedom: $(2-1)\times (4-1)=3$.
Thus $P(\chi^2_3>5.469)\approx 0.130\%>\alpha$.
This indicates that the test result is not significant,
and the two classifications are likely to be independent.

(b): Taking the intersection of NFAs is similar to taking the intersection of DFAs, which is similar to taking the union of DFAs, which uses a cartesian product construction. So, the number of states will be $k_1\times 2^{k_2}$.

1. Consider a finite set $X=\{a, b, c\}$,
   
   1. A relation $R:X\times X\to X$ where only $R(a,a), R(b, b), R(c, c), R(a, b), R(b, a), R(b, c), R(c, b)$ are $\text{True}$, the others are $\text{False}$.
   2. A relation $R:X\times X\to X$ where only $R(a,a), R(b, b), R(c, c), R(a, b), R(b, c), R(a, c)$ are $\text{True}$, the others are $\text{False}$.
   3. A relation $R:X\times X\to X$ where only $R(a, b), R(b, c), R(a, c), R(b, a), R(c, b), R(c, a)$ are $\text{True}$, the others are $\text{False}$.
   
2. Induction does not allow changing the input of the induction hypothesis (say, if the horse of replacement is of a different color, the induction hypothesis no longer holds).

## Problem 20.7 (a)

### Question 2, digital design

+ Geometric distributions
  + $P_X(x)=P(X=x)=(1-p)^{x-1}p$
  + Mean: $E(X)=\frac1p$
  + Variance: $Var(X)=\frac{1-p}{p^2}$

||O|A|B|AB|$X_{i+}$|
|:-:|:-:|:-:|:-:|:-:|:-:|
|Rh.positive|156|170|116|46|488|
|Rh.negative| 24| 50| 20|18|112|
|$X_{+j}$|180|220|136|64|600|

For $w$, we expand it as $\frac12 E(X_i\mid I_A)^2+\frac12 E(X_i\mid I_B)^2=1700$, so $Var(E(X_i\mid I))=$ $1700-1600-100$, thus $Var(X_i)=230.5$.

If: since homeomorphism preserves compactness.

By lemma 3.7, $\ang PXQ$ and $\ang QPX$ have the same sign, and that $\ang PYQ$ and $\ang QPY$ have the same sign. Then we're essentially proving corollary 3.10 (a).

So ($\overline Q$ means inverse, $Q'$ means the $Q$ last time):

### 11.3

All gates are closed, thus the capacitor discharges (if it's charged), but flows directly to the ground. Since the enabler is (again) off, the source is not connected to the ground. So the entire circuit is super safe, no serious issues at all!

(a) It is known from homework 1 that the joint PDF $L(\theta)$ is $e^{-\sum^n_{i=1}\frac{X_i^2}{2{a_i \theta}}}\times (2\theta\pi)^{n/2}\times \prod^n_{i=1}a_i^{1/2}$, where we can drop everything except the factor $e^{-\sum^n_{i=1}\frac{X_i^2}{2{a_i \theta}}}$, which can be simplified further as $e^{-\frac1{2\theta}\sum^n_{i=1}\frac{X_i^2}{a_i}}$. Therefore $\fbox{$T=\sum^n_{i=1}\frac{X_i^2}{a_i}$}$ is a sufficient statistics. The MLE is a function out of this (also according to the computed MLE $\hat\theta=\fbox{$\frac1n\sum^n_{i=1}\frac{X_i^2}{a_i}$}$ in homework 1).

(i) They are independent for having $0$ covariance.

### 11.2

So, $\triangle ABC, \triangle ACD, \triangle BCD$ are all right triangles. By theorem 6.4, $AC^2=AD^2+CD^2$,$BC^2=CD^2+BD^2$, and:

+ Quantum circuits: input -- initialized quantum states, passing through some n-ary gates, and measure

$\impliedby$: The interior is open.

+ Teleportation
  + ![image-20210903145045025](week2-3.assets/image-20210903145045025.png)
  + 把这些 state apply $X,Z$ in the obvious way, 就可以得到 $\alpha\ket0+\beta\ket1$ 形式的结果
  + 中途是 measure in bell basis![image-20210903145647087](week2-3.assets/image-20210903145647087.png)
  + Summary![image-20210903150538900](week2-3.assets/image-20210903150538900.png)
+ No-cloning theorem

# 6.5

4. (a): $52\times 51\times 50\times 49\times 48=311875200$ possibilities.

(c) The free variable $y$ will become a bound variable, which changes the semantics of the term

(b) Let mean $\mu=75$, observe that $|65-\mu|=$ $|85-\mu|=10$, so we're actually computing $P(|X-\mu|< 10)=$ $1-P(|X-\mu|\geq 10)=$ $1-P(|X-75|\geq 10)$, which is (by Chebyshev's inequality) $\frac{\sigma^2}{10^2}$ where $\sigma=25$, thus $P(|X-75|\geq 10)=$ $\frac{25}{100}=0.25$, so $P(|X-75|< 10)=0.75$.

(a): So for all $\epsilon>0$ we need to find $\delta>0$ such that $|f(a)-f(b)|<\epsilon$ whenever $d(a, b)<\delta$. This is equivalent to saying $|f(a)-f(b)|=|d(a, y)-d(b,y)|<\epsilon$ whenever $d(a,b)<\delta$. By triangle inequality of $d$, $d(a,b)\leq |d(a,y)-d(b,y)|$, so simply picking $\delta=\epsilon$ should work.

+ Newton's Binomial
  + $(a+b)^n=\sum_{k=1}^n{\Bigg(\matrix{n\\k}\Bigg)a^kb^{n-k}}$
  + Proof by induction

# Cmpsc 461 HW 3

+ Conditional independence: $P(AB\mid E)=P(A\mid E)P(B\mid E)$
+ Mutually independent: each event is independent of the intersection of other events
+ 

(a) ![image-20220219231008293](h5.assets/image-20220219231008293.png)

   ![image-20220121135223581](hw1.assets/image-20220121135223581.png)

Circuit:

(c) This is $X\sim Geom(0.8)$, geometric.

The video demo is included as a separate file in the Canvas submission.

So we can simplify it as:

+ Path-connected and connected
  + ` *||_|__|___|____|`
  + Path-connected is preserved by taking product
+ Homotopy
  + $f:\mathbb I\to X \to Y$ is a homotopy from $f(0):X\to Y$ to $f(1):X\to Y$
  + 

Suppose $[0,1]\sub \R$ is compact. Then, for the covering $\{C_i\mid i\in[0, +\infty)\}$ where $C_0=\{1\}$ and for $i\geq 1$, $C_i=[1-i,1-\frac i2)$. It is evident that $\bigcup_{i\in [1, +\infty)} C_i$ covers $[0, 1)$ disjointedly, and adding $C_0$ to it will make it cover $[0, 1]$. Since the cover consists of disjointed sets, there is no finite subcover. Thus a contradiction.

![image-20211202163929132](submission2.assets/image-20211202163929132.png)

Let's denote the retract as $r:X\to A$.

SOP: $\overline{BD}+BD\overline{AC}+C\overline{D}+AC\overline{B}$

+ $\Gamma\sub \R^2\sub \R^3$ a closed subset homeo to $\R$ implies $\R^2\setminus \Gamma$ is not connected
+ Extension theorem (Titze): $M$ a metric space, $A\sub M$ closed, if $f:A\to \R$ cont. then there is extension $f_*:M\to \R$ such that (obvious equation in CT)
+ Let $h:\R\cong \Gamma$, so $h(t)=(a(t), b(t))$, so $h_*:\R^2\to \Gamma$ by extension satisfy $h_*(a(t), b(t))=t$. Now consider two homeomorphisms
  + $(x,y,z)\mapsto(x,y,z+h_*(x, y))$
  + $(x,y,z)\mapsto(x-a(z),y-b(z),z)$
  + Composing them gets $(a(t), b(t), 0)\mapsto (0, 0, t)$ which is also a homeomorphism. So $\Gamma$ is homeomorphic to the $z$ axis.
+ $f:X\to Y$ is a covering map if surjective and $\forall q\in Y. \exist$ nbhd $W\ni q$ such that $f^{-1}(W)=\bigcup_\alpha V_\alpha$ for $V_\alpha\sub X$ disjoint open subsets such that $f(V_\alpha)\cong W$
+ $\pi_1(8)=F_2$ (free group generated by two distinct elements)

When $X=0,Y=0$:

$Var(X_i)=$ $E(Var(X_i\mid I))+Var(E(X_i\mid I))$, where $E(Var(X_i\mid I))$ is similarly $\frac12\cdot 15^2+\frac12\cdot 6^2=130.5$.

In case of prebase, replace "union" with "finite intersection" in the "if" part, and "only-if" part remains the same.

(e) $Var(X)=E(X^2)-E(X)^2=$ $(\int_0^1\int^y_0 x^2(3-3x)d(xy))-\frac1{16}=$ $\frac1{10}-\frac1{16}=\frac{6}{160}=\frac{3}{80}$. Thus $\sigma(X)=\sqrt{Var(X)}=$ $\frac14\sqrt{\frac3{5}}$.

   (b): There can be $1$ failure in the first $4$ games, so the result is $\left(\matrix{4\\1}\right)=4$.

(b) $f(n)=n+n^2+\sin(\frac{n\pi}4)n^2$ where $\sin\frac{n\pi}4\in[-1,1]$. So using the same configuration in (a) would work.

(e) So $P(Y\leq\frac12)=F(\frac12)=1-e^{-(1/2)/2}\simeq 0.22$.

(b) $P(X_j=x)=\frac1{10}$ for $x\in[1,10]$ and $j\in\{1,2\}$.

(b): $P(Y\geq 2)=1-P(Y=0)-P(Y=1)=\frac1{e^\lambda}(\frac{\lambda^0}{0!}\frac{\lambda^1}{1!})=\frac\lambda{e^\lambda}$.

(c): Instead of using subsets of $\mathcal P(Q)$, use $Q\setminus F$ as $Q'$. Then, in $\delta'$, we copy $\delta$, but replace all states in $F$ with $q_0$ -- the initial state of $M$. Since $|F|>0$, the total number of states is reduced by at least $1$, so now we have $k-1$ or less states. Then, let $\{q_0\}$ be $F'$. Let $q_0$ be $q_0'$.

(a) Essentially we need to construct $c_1\dots c_n$ where either $c_u$ or $c_v$ is $0$ and all the others are arbitrary. Without the loss of generality, we may assume $v>u$, so the following construction of $A_e$ naturally arises ($p_{\text{start}}$ is the starting state, $p_n$ is the accept state, $p_{\text{fail}}$ is a state for failures, the states are listed in consecutive order):

`x`, `y` from line 8, `i` from line 9, `a`, `b` from line 15, `j`, `h` from line 1.

   (c): Leftmost:

$E(T_i)=10$ and $T_i$ follows exponential distribution, so  $T_i\sim Exp(\frac1{10})$, so $Y_i\sim Bin(100, P(T_i>10))$ where $P(T_i>10)=$ $1-P(T_i\leq 10)=$ $e^{-\frac1{10}\cdot10}=e^{-1}$, so $Y_i\sim Bin(100, e^{-1})$, so $E(Y)=E(Y_i)=100e^{-1}$, while $Var(Y)=\frac{Var(Y_i)}{100}=$ $100e^{-1}(1-e^{-1})$. Define $X\sim N(E(Y), Var(Y))=$ $N(100e^{-1}, 100e^{-1}(1-e^{-1}))$, so let $X'=\frac{X-100e^-1}{\sqrt{100e^{-1}(1-e^{-1})}}$ and we have $X'\sim N(0, 1)$.

$$
\begin{align*}
&~\overline{AB}~\overline{ABC}~\overline{ABCD}(A+C) \\
=~&\overline{AB}~\overline{ABC}(A+C)(\overline D+1) \\
=~&\overline{AB}~(\overline C+1)(A+C)(\overline D+1) \\
=~&\overline{AB}~\overline C~\overline D(A+C) \\
=~&(\overline{AB}~\overline C~\overline D)A+(\overline{AB}~\overline C~\overline D)C\\
=~&(\overline{AB}~\overline C~\overline D)A \\
=~&\overline B~\overline C~\overline D \\ & \\
&~\overline{\overline X~(\overline Y+\overline Z)}+\overline X+Y(XZ+XY+YZ)\\
=~&(X+\overline{\overline Y+\overline Z})+\overline X+XYZ+XYY+YYZ\\
=~&(X+YZ)+\overline X+XYZ+XY+YZ\\
=~&(X+\overline X)+(YZ+YZ)+XY(Z+1)\\
=~&1+YZ+XYZ\\
=~&YZ
\end{align*}
$$

(b) $P(X>9\mid X>6)=\frac{10-9}{10-6}=\frac14$.

Link: https://www.edaplayground.com/x/LNLD

![image-20211021165305702](lab7.assets/image-20211021165305702.png)

Then, $CF//ED\and EF//CD\implies \unicode{x25B1} EFCD\implies ED=CF$.

(a) Poisson distribution, because raindrops may fall randomly, and the probability doesn't change, and the time interval is fixed.

+ Project one plane on another
+ Projective completion
  + Concurrent lines: intersect at one point
  + Collinear points: share one line
+ Projective transformation
  + Bijection of projective planes, sends lines to lines
  + Perspective transformation: move certain lines to $\infty$ and move $\infty$ back to a line
+ Construction tool: ruler

   (c): It's a combination of 5 $\left(\matrix{4\\1}\right)$ cards, and there are $13-5=8$ such combinations. $8\times \left(\matrix{4\\1}\right)\times 5!=32\times 5!=3840$, and the probability is $3840\div 311875200=\frac2{162435}$.

+ Hausdorff space + one point is compact.
+ $\Z_2$ with discrete topology, consider $f:X\to \Z_2$ cont., then we obtain $G_X$, a group of all continuous functions from $X$ to $\Z_2$, with multiplication replaced by $h(x)=f(x)g(x)$.
  + $X$-connected, nonempty $\iff G_X\simeq \Z_2$ because connected spaces go to one point, and there are only two points in $\Z$.
  + "Open subdivision".
  + "WLOG".
+ Image of a connected space is connected.
+ Path: $[0,1]\to X$
+ $X=\bigcup_\alpha C_\alpha$ for $\bigcap_\alpha C_\alpha\ne\empty$, then $X$ is connected.
+ Spatial multiplication (not associative)

Then we show that $\Z\times\Z$-action is continuous. It is established that $f_k(x)=x+k:\R\to\R$ for $k\in\Z$ is continuous (in other words, $\R$ is a $\Z$-space), so $f_1,f_2:\R^2\to\R^2$ where $f_1(x,y)=(f_k(x), y), f_2(x, y)=(x, f_k(y))$ are both evidently continuous for $k\in\Z$, which means their composition is still continuous.

+ Query scenario

By Oren Halilov

Since $X\sub X$, we start directly from any subset $S$ of $X$.

(a) $X$ has the negative binomial distribution ($X\sim NB(5,0.4)$).

(d): $P(X>7\mid X\in[2,8])=\frac{8-7}{8-2}=\frac16$.

+ On input $\langle M_1,M_2\rangle$:
  + Construct the 2-tape TM $M'$ as in problem 2 (a).
  + Let $w\in h(M_1,M_2)$, it exists because the set is non empty by definition of RELATED.
  + Output $\langle M',w\rangle$.

+ The LEDs for 0 and 4 only turn on when the decoder outputs 0 or 4. So, no binary gate but only a NOT gate is needed.
+ The sign LED is on only when the third input (the 'sign' bit) is 1, so it can be connected to the input directly.
+ The LEDs for 1, 2, 3 turn on when the input is $\pm1,\pm2,\pm3$, so either output of the decoder should turn them on, and say, when it's neither $\pm1$, the LED for 1 should be off. So we need either a NAND gate or a XOR gate.

+ Main lemma: $X\in\ell\iff AX=BX$ (where $(AB)\perp\ell$)
+ Reflection
  + Line of reflection is the perpendicular bisector
  + Reflection is a motion
  + $\forall$ motions is a composition of at most 3 reflections
    + Idea: a nondegenerate triangle determines a motion

(a) By $E_{i, j}=\frac{X_{i+}\times X_{+j}}{X_{++}}$:

(c) $E(Y_2)=\int ^{y_2}_0 y_2 6(1-y_2)y_2dx=$ $6(\frac13-\frac14)=1$.

(b): Their scopes include everywhere after the declaration, and can be shadowed. Their lifetime starts from the program startup and ends at the end of program.

+ Incident structures
+ Bijection from Euclidean plane to itself that preserve lines: *affine transformation*
  + Sends parallel lines to parallel lines
  + Example: motion
  + $(x,y)\mapsto(kx,ky)$
  + $(x,y)\mapsto(kx,y)$ or $(x,ky)$
  + $(x,y)\mapsto(x+ky,y)$ or $(x,y+kx)$
  + $(x,y)\mapsto(ax+by+r,cx+dy+s)$
    + $\left(\matrix{x\\y}\right)\mapsto\left(\matrix{a&b\\c&d}\right)\left(\matrix{x\\y}\right)+\left(\matrix{r\\s}\right)$
    + ^ general form of any affine transformation (fundamental theorem)
    + Proof sketch: first, it doesn't mess with coordinates
+ Underlying construction rules: rule and parallel tool
+ Midpoints are preserved by affine transformations
  + Reduce to constructions of midpoints using rule-and-parallel-tool
+ It is in-fact continuous, but we don't assume it
+ Any affine transformation is a composition of inversions
+ Projective geometry

(b) $X$ and $X'$ are reversed as of (a). For $y=\lang G,s,t, v_1,\dots,v_p\rang$, $y'$ is the combination of $\lang G\setminus\{v_1,\dots,v_{p-1}\},v_p,t\rang$, and if $v_1, v_2,\dots,v_p$ is connected as a path (which can be decided in linear time), $y$ is accepted (otherwise rejected).

In this case, we have $S2,S4$ closed and $S1,S3$ open. The enabler is off, so the capacitor discharges (if it's charged), flowing from the capacitor to $S4$ to $M$ to $S2$ to the ground. Thus $M$ is on, but running backwards.

# Affine geometry

In this case, we have $S2,S4$ open and $S1,S3$ closed. The enabler is off, so the capacitor discharges (if it's charged), flowing from the capacitor to $S3$ to $M$ to $S1$ to the ground. Thus $M$ is on, running forwards.

(b) $f(y_2)=\int^{y_2}_0 6(1-y_2)dy_1=$ $6(1-y_2)y_2$.

Now we take the union of all such sets, which is still open, and it contains everything not in $A$ and is disjointed from $A$, meaning that it's the complement of $A$. So $A$ is closed.

Consider $X=\{1\}$ with discrete topology.

I think the answers are obvious enough to find (just scroll to the last line of the answers), so I decide to not circling them.

It is already showed on the book that path-connectedness is associative and symmetric. The constant map constructs the reflexive paths. Thus path-connectedness is an equivalence relation.

Given $A=(x_0,y_0),B=(x_1,y_0)$, the equilateral triangle $\triangle ABC$ has $C=(\frac{x_0+x_1}2, y_0+\sqrt3 \frac{|x_0-x_1|}2)$, which is refuted by 19.9 and the fact that $\sqrt3$ is not rational.

(c) 30%

Now, suppose $f(2)$ and $f(3)$ and $f(4)$ are all perfect squares, so like $f(2)=(a_0)^2,f(3)=(a_1)^2$ where $(a_1)^2=(a_0)^2+t$, and $f(4)=(a_2)^2=(a_0)^2+2t=(a_1)^2+t$, where $a_0,a_1,a_2\in\N^*$. So, $(a_2)^2-(a_1)^2=(a_1)^2-(a_0)^2$ which simplifies to $(a_2)^2+(a_0)^2=2(a_1)^2$ which implies $a_0=a_1=a_2$, contradicts the fact that $t\geq 1$.


(g) So $p=P\left(Z<-5.7208\right)=5.3\times 10^{-9}<\alpha$, so it supports (e, f) too.

+ $T=\hat\theta_{MLE}-\theta$, so $T=\theta$ if null is true.
+ Significant rate:
  + $P(T>c\mid H_0)=\alpha$
  + $P(T<c\mid H_0)=\alpha$
  + $P(|T|>c\mid H_0)=\alpha$
+ $\alpha$ predetermined, which determines $c$, which determines the rejection region
+ Example 3
  + $\hat\mu_{MLE}=\bar X\sim N(\mu, \sigma^2/10)$
  + Reject null if $T>c$ (if $c$ is 0, always reject)
  + $T=\frac{\hat\mu_{MLE}-15}{\sigma/\sqrt{n}}$ makes $T=N(0, 1)$
  + $c$ makes $P(T>c\mid H_0)=\alpha$, so we can compute $c$
    + $N(0, 1)$ is the dist. of $T$ if $H_0$ is true
    + Don't care the dist. when $H_1$ is true
  + $t=T$ replaced with observed data, $3.16$
  + If $p$-value less than $\alpha$ we reject the alternative
  + $p=P(T> 3.16\mid H_0)=$ something
+ Summary
  + Hype value: $H_0:\mu=15$, $H_1:\mu>15$
  + Test stat: $T=\frac{bla}{blah}\sim N(0,1)$
  + Rej reg: $R=\{T\mid T>c\}$
  + If observed $T$, called $t$, $\in R$ or not; or $p<\alpha$: reject null.

# Homework 4 Math 427

Screenshot: ![](t-in-terms-of-d.png)

## Problem 12.10 (i)

Suppose the waiting time of customer $i$ is $T_i$ and define $Y_i=1$ if $T_i>10$ and $0$ otherwise. So we need to compute $p=P(\sum^{100}_{i=1} Y_i \geq 50)$. Define $Y=\sum^{100}_{i=1} Y_i$.

### 1.3 a)

(c) Similarly $E(X^2)=-\frac{pe^s((p-1)e^s-1)}{((p-1)e^s+1)^3}\mid^{s=0}=$ $-\frac{p((p-1)-1)}{(p-1+1)^3}=2-p$, so $\text{Var}(X)=$ $E(X^2)-E(X)^2=$ $2-p-\frac1p^2=\frac{1-p}{p^2}$.

The output is **too long** for taking screenshot, so I'm including a textual copy of it here:

### Question 2

### Question 1

### Question 3

+ Bounded subsets of Euclidean spaces are compact
+ Not true: $X\times Y$ compact $\iff X$ compact and $Y$ compact
  + Stupid mistake: $X\times Y\mapsto X$ projections may not be onto
  + Example $X\times\empty\simeq\empty$
+ Infinite product of compact spaces is still compact
+ Sequentially compact
+ Hausdorff spaces: any sequence have unique limits

Suppose we have a point $(x, y)$ that has the same distance to $A$ and $B$, so $\sqrt{(x-x_A)^2+(y-y_A)^2}=\sqrt{(x-x_B)^2+(y-y_B)^2}$, doing the algebra simplifies it to $2(x_B-x_A)x+2(y_B-y_A)y=x^2_B+y^2_B-x^2_A-y^2_A$ (I think there's a typo, right?).

  Then, replace $E$ with $B$.

+ **Controlled-NOT**

# Week 1 homework

![image-20211028165702449](writeup.assets/image-20211028165702449.png)

## 8.14 (a)

  + $H_0:\theta\in\Omega_0,H_1:\theta\in\Omega_1$ where $\Omega_{0,1}$ disjoint

So $E(Y)=\int^1_0{3y(1-y)^2dy}=\frac14$, and $E(Y^2)=\int^1_0{3y^2(1-y)^2dy}=\frac1{10}$. Then, $E(10+20Y+4Y^2)=$ $10+20E(X)+4E(Y^2)=$ $10+20\times\frac14+4\times \frac1{10}=15.4$.

1. (a): `<e>` $\to$ `<e> * <e>` $\to$ `<e> / <e> * <e>` $\to$ `<d> / <d> * <d>` $\to$ `9 / 3 * 3`

(b) $P(X=x, Y=y)=P(X=x,Y=n-x)$, and by (a) we know $X\sim Pos(\lambda p)$, thus $P(X=x, Y=y)=P(X=x\mid N=n)P(N=n)$

| YZ\WX | 00   | 01   | 11   | 10   |
| ----- | ---- | ---- | ---- | ---- |
| 00    | 0    | 0    | 1    | 1    |
| 01    | 0    | 1    | 1    | 0    |
| 11    | 0    | 1    | 1    | 0    |
| 10    | 0    | 0    | 1    | 1    |

+ Models and Axioms
  + This course is about axiomatic approach (use $\R$)
  + Wednesday quiz/homework (but not this Wednesday)
  + No final, do midterms
+ Metric space
  + Distance function ($d$)
    + $d(A,B)=0 \iff A=B$
    + $d(A,B) \geq 0$
    + $d(A,B)=d(B,A)$
    + $d(A,B)+d(B,C)\geq d(A,C)$
  + Binary function on a set towards $\R$
  + Counterexample: $d(A,B)=|A-B|^2$
  + Notation: $AB=d(A,B)=d_\chi(A,B)$
  + Example: $AC+BD\leq AB+BC+CD+DA$
  + Distance preserving map, aka isometry, is injective (proof: $\forall A,B. f(A)=f(B)\implies$ $d(f(A),f(B))=0\implies d(A,B)=0\implies A=B$
  + Motion: isometry of metric spaces
  + Manhattan distance: $d_1(A,B)=|x_A-x_B|+|y_A-y_B|$, Manhattan spaces
  + Lines, half-lines

+ Quotient topology
  + Pushforward topology
  + Quotients
+ Identify opposite points of a disk: $\R P^2$ real projective plane
  + $S^1\simeq \R P^1$
+ 

  + Requires two queries classically

![image-20211206074928143](writeup.assets/image-20211206074928143.png)

## Problem 18.4 (k)

(o) $Corr(X,Y)=$ $\frac{Cov(X,Y)}{\sigma(X)\sigma(Y)}=$ $\frac{\frac3{160}}{\frac14\sqrt{\frac3{5}}\times \frac18\sqrt{\frac{19}5}}=$ $\sqrt{\frac3{19}}$.

The leftmost column represents when the function is first called, then it does a recursive call so a new stack frame is pushed, giving rise to the second column, then there's the third column, etc., in the end we pop the stack frame for `summation(3, 6)` and return, which corresponds to the rightmost column.

# Stat 414 HW 4

I decide to use Mealy style state machine because the input also affects the motor directly.

  + Turn it upside-down and replace: $\equiv \Lambda(X)$, generalized

## 7.10

# Stat 414 HW 1

+ Induction
+ $\sum_{k=0}^n{x^k}=\cfrac{1-x^{n+1}}{1-x}$
+ 

# Cmpen 270 Lab 7

## 7.16

![image-20220427144250939](hw7.assets/image-20220427144250939.png)

(c): $Var(X)=\int_0^1{x^2(1+2x^2)dx}-\frac35=\frac2{15}$.

By theorem 5.2, $AY=BY$ and $X\not=Y$ and by SSS $\triangle AYO\cong\triangle BYO$.

Critical value $c$ makes $P(\chi_2^2> c)=\alpha=0.05$,
by [calculator](http://courses.atlas.illinois.edu/spring2016/STAT/STAT200/pchisq.html) $c=5.991$.
Since $124.77> 5.991$, we reject the null hypothesis.

Open: $\forall t'\in[t, s), [t', s)\subseteq [t, s)$ so $[t, s)\in \mathscr U$ (belongs to the set of open sets), so it's open.

+ $\impliedby$: define half-line $[OA')$ so that $\measuredangle AOB=\measuredangle BOA'$, and define half-line $[OA'')$ so that $\measuredangle AOC=\measuredangle COA''$. So, $2\measuredangle AOB=\measuredangle AOB+\measuredangle BOA'=\measuredangle AOA'$ and $2\measuredangle AOC=\measuredangle AOC+\measuredangle COA''=\measuredangle AOA''$. By $2\measuredangle AOB+2\measuredangle AOC\equiv 0$, $\measuredangle AOA'=\measuredangle AOA''$, so $[OA')=[OA'')$. So, $0\equiv \measuredangle AOA'+\measuredangle A'OA$, so $0\equiv \measuredangle AOB+\measuredangle BOA'+\measuredangle AOC+\measuredangle COA'$.

* Probability and statistical inference
* Experiment: any action as long as the outcome is uncertain
  * Flip coins, roll dies, etc.
  * Take 3 free throws
* Sample space: the set of all possible outcomes, denoted by $S$
  * $\{H,S\}, \{1,2,3,4,5,6\},$ etc.
* Event: a collection of "outcomes" (in a series of experiments), a subset of $S$
*  Complement of event $A$: all outcomes not in $A$, denoted $A^C$
* Union $A \cup B$ and intersection $A \cap B$ of events
* Disjointed or mutually exclusive events
  * Distribution laws and de Morgan laws
* Basically all are set theoretic stuffs
* $P_{\text{na\"ive}}(A)=\cfrac{|A|}{|S|}$
* Multiplication rule
* Sample w/ replacement when order matters: $\cfrac{}{}$
* Sample w/o replacement when order matters (do not put it back), aka permutations: $\cfrac{n!}{(n-k)!}$
* A binomial coefficient $\cfrac{n!}{k!(n-k)!}$

6. Vertically, we go up $2$ times in the $9$ boxes. So we can reduce this problem into the "LA" problem. So, $\left(\matrix{2+9\\2}\right)=55$.

Thus $D^2-\{z\}$ is not simply connected because it has fundamental group $\Z$. This shows the first-half.

(a): So $\int^1_0{f(y)dy}=c\int^\infty_0{e^{-y/2}dy}=1$, so $-2c (e^{-y/2}\mid^\infty_0)=-2c(0-1)=1$, so $2c=1$, so $c=\frac{1}{2}$.

+ Parallel lines
+ Triangle angle measure sum is $\pi$
+ Parallelogram $\unicode{x25B1} ABCD$
  + Symmetric
  + Motion sends $A$ to $C$: intersection goes to intersection
+ 

> Find the leg of an isosceles right h-triangle inscribed in a horocycle.

Only-if: we construct the homeomorphism $\phi(i)=(i, f(i))$.

+ Single qubit gates
  + Pauli gates $X,Y,Z$
  + Hadamard gates
  + Phase gates
  + Clifford group
+ Fun quantum phenomena
  + Watched pot effect
    + $\sin^2\epsilon\simeq \epsilon^2$ when $\epsilon \to 0$
    + Repeat $\frac{\pi/2}\epsilon$ (a very large number) times, we get $\frac{\pi/2}\epsilon\cdot \epsilon^2=\frac{\pi\epsilon}2$
  + Quantum zeno effect
    + Move $\ket0$ to $\ket1$ without unitary operation
    + Repeat the same number of times, at least one measurement fails
+ Elitzur-Vaidman bomb
  + A suitcase with a bomb, opening will trigger
  + $R_\epsilon$: defined in the obvious way
  + Query in superposition: no bomb $\to$ id, bom $\to$ measure, $\ket0$ output $\ket0$, $\ket1$ blows up
    + So it's like repeating the measurement until some certain observation occurs, and if not, apply a unitary transformation
    + This number is $\frac{\pi}{2\epsilon}$
  + No bomb: $\ket0\mapsto\ket1$, bomb: each query with prob $1-\epsilon^2$ to get $\ket0$

The following machine $F$ computes $f$:

This is a direct consequence of 14.1 which says that parallel lines are mapped to parallel lines (so parallelograms are mapped to parallelograms).

(a): for any regular language, suppose a DFA recognizing it, converting it to an NFA makes it a majority-NFA.

  

Simply express $\R^2\setminus\{0\}$ in a polar coordinate system: each point on $\R^2\setminus\{0\}$ is specified by an angle (corresponds to a point on $S^1$) and a length (a number $\in (0, +\infty)$). So, $\R^2\setminus\{0\}\simeq (0, +\infty)\times S^1$. Then, $\R\simeq (0, +\infty)$ by the homeomorphism $f(x)=2^x$, so by exercise 6.2 (a) that $(0, +\infty)\times S^1\simeq \R\times S^1$, and by transitivity of homeomorphism we get the result.

So we need to find $E\left[\sum_{i=1}^5 I_i\right]$, by linearity it equals $\sum_{i=1}^5 E\left[I_i\right]$. For each roll, the value's PMS is $P(I_i=x)=\frac1{10}$ for $x\in[1, 10]$, so $E[I_i]=\sum_{i=1}^{10}x\times P(I_i=x)=\frac1{10}\frac{10\times (1+10)}2=5.5$. So $E[I_i]=5.5$, thus $E\left[\sum_{i=1}^5 I_i\right]=5\times 5.5=27.5$.

Homework 1 Cmpsc 497

The if-and-only-if relation can be concluded directly from the fact that affine transformations are bijections (so they're injective).

+ (c) I did not consult any non-class materials.

K-map:

## 10.20

(a) Under $M_0$, $\mu=15$, so $P(x\mid M_0)$ is just the normal distribution PDF with $\mu=15$ and $\sigma^2=2^2$, so:

Since $f$ is continuous, the graph of $f$ is homeomorphic to the domain of $f$ -- $X$ (by a previous exercise). So the statement is equivalent to "graph of $f$ is compact $\iff$ graph of $f$ is homeomorphic to $I$".

(b) Evaluation result: `'((b . c) b . c)`.

+ $\R, \empty, [a, \infty), (a, \infty)$ is a topology ($\R_\leq$)
+ Cofinite topologies (complements of all finite subsets)

* Compact spaces have their closed subsets compact
* $K\sub \R$ is compact $\implies K$ bounded (prove by showing $K$ is closed subset of $\R$, i.e. contains limit points)
* $[a, b]\sub\R$ is compact
  * Proof: by contradiction, assume no finite subcover, so there is a very very small bounded subset of $[a, b]$, which is contained in an open set in the cover
* Compactness is preserved by continuous functions

## 2.14

## 2.11

(d) $f(y_1\mid y_2)=\frac{f(y_1,y_2)}{f(y_2)}=\frac1{y_2}$, so $(Y_1\mid Y_2=y_2)\sim$ Unif$(0, y_2)$.

Suppose $W$ does not intersect $A$, then the complement $W^C$ is a closed set that contains $A$ but does not contain $W$, and it should be an instance of $A'$. Then, $\overline A$, the intersection of $W^C$ and all other $A'$ should exclude $W$, contradicting the fact that $W\sub Y \sub \overline A$.

(a) So $E(Y^c)=\int^\infty_{-\infty}x^c\frac{x^{\alpha-1}e^{-\lambda x}\lambda^\alpha}{\Gamma(\alpha)}dx$

+ (a): $AC=BC, CA'=CB',$ and $\ang ACB$ is shared, by SAS we get $\triangle AA'C\cong\triangle BB'C$.
+ (b): by (a), $\ang CB'B\equiv\ang CA'A$, so $\pi-\ang CB'B\equiv\pi-\ang CA'A$, thus $\ang B'AB\equiv\ang A'BA$. Also $\ang CAB\equiv\ang CBA$, and $AB$ is shared, by AAS we get $\triangle ABB'\cong\triangle BAA'$.

  //All inputs and outputs
  input [3:0]input_Num;
  output reg [6:0]display_Out;

## Additional problem

Enlonger $[AD)$ to $E$ so that $AD=DE$, and by vertical angles, $BD=DC$, and $AD=DE$, we have $\triangle CAD\cong \triangle BED$, so $\measuredangle CAD\equiv \measuredangle BED\equiv\measuredangle DAB$, so $\triangle ABE$ is isosceles, so $AB=BE$, so $AB=AC$, thus $\triangle ABC$ is isosceles.

(b) $(λx.λy.y~x)(λz.y)=$ $(λx.λw.w~x)(λz.y)=$ $λw.w~(λz.y)$

+ $h=\frac12\ln{\frac{1+\cos\phi}{1-\cos\phi}}$
+ Equidistant set of lines, horocycle
+ AAA proof
  + Lemma: defect is positive for nondegenerate triangles
  + Parallel line (by lemma, no intersection)
+ $\lim_{P\to Q}{\frac{PQ_h}{PQ}}=\frac2{1-OP^2}$
  + $2\pi R=\lim_{n\to\infty}{n\cdot X_n}$
  + $X_n$: the side of triangle
  + $2\pi\sinh{r}$
+ $\cosh{c}=\cosh{a}\cdot\cosh{b}$

By def. of circles, the distances from the centers of these three circles to the two points are the same. Therefore, they're all on the perpendicular bisector of the two points, so they're on the same line.

Code:

+ Lebesgue number lemma
  + $\{U_\alpha\}$ open cover of compact metric space
  + $\exist \epsilon > 0. B_\epsilon(x)\sub U_\alpha$ for some $\alpha$
+ Open sets
+ "What course do you teach next semester"
+ Inner automorphism
  + $G/Z(G)\simeq {\rm Inn}(G)$
  + $G\to{\rm Aut}(G)$ where $g\mapsto (h\mapsto ghg^{-1})$
    + The kernel of this map is the center
+ $\pi_1(X,x)$ -- depends on the choice of $x$
  + If the group is AbGroup then it's uniquely isomorphic
  + If it's path connected then it's isomorphic by inner automorphism
  + If it's not path connected then there can be different groups
+ $k$-periodic

(a) $\mu_1=E(Y_1+Y_2)=E(Y_1)+E(Y_2)=0$.

## Exercise 8.14 (b)


19.10 is an example that set-square cannot but compass-and-ruler can construct.

(b) This is $X\sim HGeom(40,20,200)$, hypergeometric.

| A    | B    | C    | F    |
| ---- | ---- | ---- | ---- |
| 0    | 0    | 0    | 1    |
| 0    | 0    | 1    | 1    |
| 0    | 1    | 0    | 1    |
| 0    | 1    | 1    | 1    |
| 1    | 0    | 0    | 0    |
| 1    | 0    | 1    | 0    |
| 1    | 1    | 0    | 1    |
| 1    | 1    | 1    | 0    |

Waves for $Y_1,Y_2,Z$ in the mutated circuit:

(a) Compute $1-\bigcap_{i\in[1,66]}P(T_i>60)$, and $P(T_i>60)=1-P(T_i<60)=$ $1-(1-e^{-60\lambda })=e^{-60\lambda}$ by the CDF of exponential distribution. So the result is $1-(e^{-60\lambda})^{66}=1-e^{-3960\lambda}$.

![image-20211028165653301](writeup.assets/image-20211028165653301.png)

(a) So $E(e^{sX})=\sum_{x=0}^\infty (1-p)^{k-1}p e^{sx}$ which simplifies to $\frac{pe^s}{1-(1-p)e^s}$.

Simplification:
$$
\begin{align*}
\frac{e^c+e^{-c}}2&=\frac{e^a+e^{-a}}2\cdot\frac{e^b+e^{-b}}2\\
e^c+e^{-c}&=e^{a+b-\ln2}+e^{-a-b-\ln2}+e^{a-b-\ln2}+e^{b-a-\ln2}
\end{align*}
$$
Since $c\leq a+b,-c\leq a-b,-c\leq b-a$ (triangle inequality) and $f(x)=e^x$ is positive and increasing, there are $e^c\leq e^{a+b},e^{-c}\leq e^{a-b},e^{-c}\leq e^{b-a}$, so:
$$
\begin{align*}
e^{a+b}+e^{-c}-e^{-a-b-\ln2}&\geq e^{a+b-\ln2}+e^{a-b-\ln2}+e^{b-a-\ln2}\\
e^{a+b}+2e^{-c}-(e^{-c}+e^{-a-b-\ln2})&\geq e^{a+b-\ln2}+e^{a-b-\ln2}+e^{b-a-\ln2}\\
e^{a+b}+(e^{a-b}+e^{b-a})&\\
-(e^{-c}+e^{-(a+b)-\ln2})&\geq e^{a+b-\ln2}+e^{a-b-\ln2}+e^{b-a-\ln2}
\end{align*}
$$
Since $e^{-c}+e^{-(a+b)-\ln2}>0$, $e^{a+b}+e^{a-b}+e^{b-a}>e^{a+b-\ln2}+e^{a-b-\ln2}+e^{b-a-\ln2}$.

+ https://www.statlect.com/fundamentals-of-statistics/Poisson-distribution-maximum-likelihood
+ https://www.statlect.com/fundamentals-of-statistics/exponential-distribution-maximum-likelihood
+ https://stats.stackexchange.com/q/204740

   (d): Similar to (b) which is $4$.

+ $h>50$, $h=\frac12\ln{\frac{1+\cos \phi}{1-\cos \phi}}$
  + $|\measuredangle|<2\phi$ because:
  + 作延长线，接 absolute，13.2 是关于 ideal point 的，比三角形大
  + 剩下就是脑瘫计算
+ 分 母 有 理 化
+ $c+\ln2>a+b$ equivalent to $2e^c>e^{a+b}$
  + $\cosh c=\cosh a\cdot\cosh b$
  + $2(e^c+e^{-c})=(e^a+e^{-a})(e^b+e^{-b})$
  + $e^{-(a+b)}$ 就是多出来凑数的

  // -----------------------------------------------
  // Continuous assignment for output state signal
  assign output_state_reg = current_state;
  // -----------------------------------------------

By theorem 5.12 on the textbook, $\pi^{-1}(\pi(U))=\bigcup_{g\in G}(g\cdot U)$, and group actions are homeomorphisms and they're open, so they're also closed.

## Problems

  + The way to "find a test" (LRT, score (derivative of log likelihood ratio) test)
  + Basically to find the rejection region
  + Format and critical value and form (the direction)
  + Based on $\alpha$ to determine $c$

+ Degenerate 

<!-- So, we have $P\left(\frac{1.2^2}{\sum^n_{i=1}(x_i-\bar x)^2}^{-n/2}\leq c\right)=0.05$. -->


 HW 5

 HW 6

Properties of Limit

| A    | B    | C    | F    |
| ---- | ---- | ---- | ---- |
| 0    | 0    | 0    | d    |
| 0    | 0    | 1    | 1    |
| 0    | 1    | 0    | 0    |
| 0    | 1    | 1    | 1    |
| 1    | 0    | 0    | 0    |
| 1    | 0    | 1    | 1    |
| 1    | 1    | 0    | 1    |
| 1    | 1    | 1    | d    |

 HW 2

 HW 3

 HW 4

+ $e:\R\to S^1:=x\mapsto (\cos{2\pi x}, \sin{2\pi x})$

## 1.5 (a, b)

Source: https://docs.microsoft.com/en-us/dotnet/csharp/language-reference/keywords/namespace

# Math 427 HW 11

  + $\hat\sigma_{0,MLE}=\frac1n\sum(X_i-\mu_0)^2$

If $S\sub X$ is empty, then it's evidently compact. Then let's assume $S$ to be nonempty. Let $S_i$ for $i\in I$ be an open cover of $S$ where $I$ is arbitrary nonempty index set. Take $S_0$, an open subset of $X$, so $X\setminus S_0$ is finite by definition of cofinite topology, so $(X\setminus S_0)\cup S$ is finite. Then, $\forall x\in (X\setminus S_0)\cup S$ we find $t\in I$ such that $x\in S_t$. We can always find such $t$ because it's a cover. By cofiniteness, there are finitely many $x$, so there are finitely many $S_t$. Adding these $S_t$ with $S_0$ results in a finite subcover.

So $h_f:[0,1]\times X\to Y$ continuous and $h_f(0,x)=f_0(x), h_f(1,x)=f_1(x)$. Also $h_g:[0,1]\times Y\to Z$ continuous and $h_g(0,x)=g_0(x), h_g(1,x)=g_1(x)$. Let's define $h_{gf}:[0,1]\times X\to Z$ and $h_{gf}(s,x)=h_g(s, h_f(s, x))$, which, surely $h_{gf}(0,x)=g_0(f_0(x))$ and $h_{gf}(1,x)=g_1(f_1(x))$.

Standard deviation: $\sqrt{\frac{457}{1200}}$.

+ Lifting of paths and their homotopies
+ Onto map: $\pi_1(X,x)\to p^{-1}(x)$ because for every point we can lift it
  + $n$-fold cover implies at least $n$ elements in the fundamental group
  + If $\tilde X$ simply connected, then the map is a bijection
    + Any loop is contractible in $\tilde X$
    + Consider $x\in X$ and $a, b\in p^{-1}(x)$, every loop $\in x=x$ is lifted to homotopic paths $\in a=b$
    + Universal cover
  + $S^2$ simply connected, $S^2\to \R P^2$ is a universal covering map ($\R P^2=S^2/\Z_2$)
  + $p_*$ is monic (?)
+ Doesn't exist $f\in S^2\to S^1$ that $f(-x)=-f(x)$
+ A map $S^2\to \R^2$ identifies two points
  + Construction: $f(x)=\frac{\psi(x)-\psi(-x)}{|\psi(x)-\psi(-x)|}$
  + Diagram construction: start from a nontrivial loop in $\R P^2$
+ Special covering map: totally discontinuous group action (in $G$) -- regular covering.
  + If for $x\in X$ there is a $V\sub X$ that $x\in V$, $gV\cap V=\empty$ for $\exist g\in G,g\ne e$
  + If totally discontinuous, then the map $X\to X/G$ is a covering map
  + Image of $p_*$ is a normal subgroup and $G\simeq \pi_1(X/G)/p_*(\pi_1(X))$

(a) $x=1,y=2,z=36$

(f) $f_Y(y)=\int^y_0 f(x,y)dx=3y-\frac{3y^2}2$, where $y\in[0,1]$.

A line on an h-plane is the intersection of a circline perp. to the absolute, which can be uniquely determined by its Euclidean center, which can uniquely determined by two Euclidean lines. These two lines are the tangent lines of the absolute passing thru the provided ideal points.

I didn't find a way to make a red circle in $\LaTeX$, so I used a black square instead.

## 4.8

(a) Evaluation result: `'((b . c) b . c)`

(d) $x=1,y=2,z=36$

It's a Poisson distribution where $k$ transitions happen in a distribution given by the PMS $f(k)=\frac{\lambda^k e^{-\lambda}}{k!}$.

Truth table for SN74LS148N:

  + Given an oracle $f$, assume each query takes 1 unital time.
  + Goal: determine some information 'bout $f$ by making as few queries as possible

## 4.3

Suppose $\exist X,Y. f(X)=Y$ where $X\not=A,X\not=B,X\not=C,X\not=Y$.

Index of subgroups: number of cosets, subgroups of free groups = intersections of subgroups of finite indices 树枝

## Problem 3.7 (d)

By AAA condition, the transformation preserves all triangles, so it's a motion.

So it's equivalent to $1-P(Y\leq\frac12)-P(X\geq \frac34)$, where $P(Y\leq \frac12)=$ $\int_0^{1/2}\int^y_0(3-3x)d(xy)=$ $\frac5{16}$, and $P(X\geq \frac34)=$ $\int_{3/4}^1\int_{3/4}^y(3-3y)d(xy)=$ $\frac1{64}$, so the result is $1-\frac5{16}-\frac1{64}=\frac{43}{64}$.

(c) CDF $F(x)=1-e^{-x/2}$ for $x>0$, and $F(x)=0$ for $x\leq 0$.

By theorem 18.1, $\forall x\in p^{-1}(x_0),$ $p_*:\pi_1(\tilde X, x)\to \Z$ is monic. By theorem 18.3, the image of $p_*$ for every $x\in p^{-1}(x_0)$ is a conjugacy class in $\Z$. Since $\Z$ is commutative and the conjugation is trivial, so $\pi_1(\tilde X, x)\simeq \Z$.

+ $AB\cdot CD+BC\cdot DA \geq AC\cdot BD$
  + Equal when inscribed
  + Take inversion: $AB+BC=AC$

+ Homotopy, deformation retraction, paths, loops
+ $\pi_1(X, p)$ for $p\in X$: set of homotopy classes of loops based at $p$
  + Does not have to pass through $p$ for each concatenation (!!)
+ $f:(X,p)\to(Y,q)$ induces $f_*:\pi_1(X,p)\to\pi_1(Y,q)$
  + Is $f_*$ a pullback?
  + No

### Build

+ Hidden subgroup problem
  + $H\subset G$ abelian and let $f:G\to T$ s.t. $f(x)=f(y)\iff x-y\in H$ (i.e. $x, y$ in the same coset of $H$)
  + Problem: give $f$ a black box, determine $H$
  + In case nonabelian, we take the same _left_ coset of $H$
  + Graph isomorphism problems
  + For commutative version, there's an efficient classical algorithm
+ Phase estimation problem

+ Angles' signs
  + Cor 3.5 is important
+ Motion = congruent triangles
+ Take home quiz today
+ 

Then, bring in the definition of geometric distribution's cumulative distribution function:

![image-20211118160620582](submission1.assets/image-20211118160620582.png)

||O|A|B|AB|$\chi^2$|
|:-:|:-:|:-:|:-:|:-:|:-:|
|Rh.positive|73.20|89.47|55.31|26.03|1.021|
|Rh.negative|16.80|20.53|12.69|5.97|4.448|

(a) Since $\hat\lambda_{MLE}=\overline Y$, $\hat\lambda=\frac{\sum^n_{i=1} Y_i}{n}=\frac{12+2\times 6}{50}=\frac{24}{50}=0.48$.

This is (by proposition 3.9) equivalent to show that $\angle ABA'$ and $\angle ABB'$ have the same sign.  Also by corollary 3.10, this is equivalent to show that $A',B'$ lie in the same half-plane complement to $(AB)$. Since $[AO)=[AA')$, $O$ and $A'$ lie in the same half-plane, and similarly for $O$ and $B'$. So $A'$ and $B'$ lie in the same half-plane.

   Rightmost:

+ $H^{\otimes n}$ and $x\in\{0,1\}^n, H^{\otimes n}\ket x=\frac1{2^{n/2}}\sum$ something
+ $\{0,1\}^n$ as a vector space: $\Z_2$ with add/mul mod 2 is a field
  + Make a vector space out of $\Z_2$
  + $x\cdot y=x_1y_1\oplus \cdots\oplus x_ny_n$ "dot product" of vectors
    + $\ket1\cdot\ket1=0$
  + Deutsch's problem
+ Simon's problem
  + $f:\Z_2^n\to\Z_2^n$ s.t. $\exist r\in\Z_2^n$ s.t. $f(x)=f(y) \iff x\oplus y=r\vee x=y$
  + Goal: find $r$ (by finding a collision where $f(x)=f(y)$ while $x\not=y$)
  + Classical algorithm for Simon: search for collision
  + Birthday paradox
  + Quantum algorithm for Simon
    + Compute $\sum_{x\in\Z_2^n}\ket x \ket{f(x)}$

$\impliedby$: So we have $Y$ discrete  where $|Y|\geq 2$ and for all continuous function $f:X\to Y$ we have $f(X)=\{y\}$ for some $y\in Y$. The suppose $X$ is not connected, so it's a disjointed union of two open sets, and we may construct a map from these open sets to distinct points $y_1,y_2\in Y$, a counterexample to the assumption.

$f*\bar g\sim \epsilon \implies f*\bar g*g\sim e*g\implies f*(\bar g*g)\sim g\implies f\sim g$

+ (a) $(\frac12\ket0-\frac12\ket1)(\ket0+i\ket1)$ which computes to the original formula.

Since $\triangle ABC$ is isosceles, $AC=BC$ and $\ang CAB\equiv\ang CBA$.

## Problem 13.10 (k)

+ Distance function proof
+ Triangle nondegenerate, perp. bisector of each side intersect on the same point.
  + Center of a circle
  + Circumcenter
+ Orthocenter
  + Altitude: 中垂线
+ Centroid
  + Median: 中线
+ Angle bisector and incenter
  + Escenter

(a) So $E_{i, j}=\frac{X_{i+}\times X_{+j}}{X_{++}}$,
and we test $\chi^2=\sum_{i, j}\frac{(X_{i,j}-E_{i, j})^2}{E_{i, j}}$.

+ b) There's only one: $1010,0010$

Suppose $Y=S$ but instead of having the topology of $S$, $Y$ has the induced topology of $S$. Let $f$ be identity, then $i:S\to X$ is inclusion and open sets in the induced topology of $S$ are mapped identically to $S$, so open sets in $S$ are in the induced topology of $S$.

### Problem 2

### 1.17 b)

### Problem 1

Only-if: suppose the space is not connected, then we must find two "separated points", then we can construct a continuous function sending these two points to distinct points in the discrete two-pointed space, a counterexample to the assumption.

+ a) by the following K-map:

+ 尺规作图
  + Initial configuration: finite set of points in a coordinate system
  + $(x-a)^2+(y-b)^2=r^2,(x-c)^2+(y-d)^2=r_0^2$ and can be solved (correspond to intersections of circles)
  + Replace one with $ax+by=c$: intersections of lines and circles
  + "Constructable numbers": $+,-,\times,\div,\sqrt~$ seems smaller than algebraic closure of $\Q$
  + $7,9$-tagon: no, $[3..6]+[8,10]$. Pattern: $n=2^k\cdot \prod_{i=0}^l p_i$ for $p_i$ unique $2^m+1$ numbers
    + Fermat prime: $3, 5, 17,256,65537$
+ Finding roots + polynomial (field theory)
+ Axiom V

(b) So $f_X(x)=\int^x_0 f(x,y)dy=$ $\int^x_0 \frac1x dy=1$, thus $X\sim Uni(0,1)$.

+ Complexity of quantum circuits
+ Multiplication
  + Grade school: $O(n^2)$
  + Best known classical algorithm $O(n\log n)$
  + Best known quantum algorithm $O(n\log n)$
+ Factoring
  + Trial division $2^{n/2}$
  + Best known classical algorithm ${(2^n)}^{\frac13}$
  + Shor's quantum algorithm $O(n^2\log n)$
+ Toffoli gate (controlled-controlled-gate)
  + $\ket a, \ket b, \ket c\mapsto \ket a, \ket b, \ket{(a\wedge b)\oplus c}$
  + Computational basis: "negates the 3rd qubit iff the first two are both $\ket1$"
  + Theorem: classical circuit of size $s$ can be simulated by a quantum circuit of size $O(s)$
  + **AND** gate: Toffoli gate specialize $\ket c$ to $\ket0$, and the output is $\ket{a \wedge b}$
  + **NOT** gate: Toffoli specialize to CNOT
  + Random number generator: $\ket0\to H\to$ measure and you get random bit
+ Classical simulation of quantum
  + Write down the vector representation of quantum states and use multiplications
  + Complexity classes (P, BPP, BQP, PSPACE, EXP)

# Cmpsc 464 HW 4

+ ${\rm OUT9}=Q_2\overline{Q_1}$

+ A unitary operation may perform on multiple states, causing some states to entangle (one-gate unitary transformation will not cause any entanglement)

(b) $\frac{de^{\lambda(e^s-1)}}{ds}=\lambda e^{\lambda(e^s-1)+s}$, then let $s=0$ we get $E(X)=\lambda e^0=\lambda$.

+ Digital systems
  + Analog systems: continuous-valued physical systems
  + Digital systems: operates on discrete symbols
+ Number systems

# Cmpsc 464 HW 3

# Homework 5 Math 427

## Problem 15.11 (a)

Since $A$ is a strong deformation retract, $\exists r:X\to A. \iota r\simeq_{\text{rel}~A} 1$. The relativity condition says that $r\iota= 1$. Then, by the functoriality of $\pi_1$, we have $r_*\iota_*=1$, $\iota_* r_*=1$, hence $r_*$ is bi-invertible, therefore an isomorphism.

+ 圆心角 圆周角 圆切角

$\overline{\overline A+\overline B}~\overline{\overline B+\overline C}~\overline{\overline A+\overline C}$

## 1.8 (a, d)

+ Neutral plane
  + No Axiom V
+ Circumcenter (perp. bisector)
  + May not exist in a neutral plane (3 perp. bisector either do not intersect or intersect at one point)
+ Centroid (median)
  + Exists, but proof is much more complicated
+ For $\triangle ABC$, $|\ang A|+|\ang B|+|\ang C|\leq\pi$

(a) First we need the joint pmf. Given $N\sim Poi(\lambda)$ and $P(Y \mid N=n)\sim Bin(n, 1-p)$, we can deduce $P(Y=y,N=n)=P(Y=y\mid N=n)P(N=n)$, so $P(Y=y)=\sum_{i=0}^n{P(Y=y,N=i)}$. By simplification $P(Y=y)=\frac{e^{-\lambda(1-p)}(\lambda (1-p))^y}{y!}$, therefore $Y\sim Poi(\lambda(1-p))$.

+ Perp. is shortest
+ Circles (center $O$ and radius $r$)
  + A set of points equi-distance from the center
  + Tangent line
    + Is right angle
  + Proof methodologies: take perp. line, show points are reflections, then contradiction
+ Similar triangles
  + SSS, AA, SAS where S: fix $k>0$, $A'B'=k\cdot AB$ etc.
  + $\triangle ABC\sim\triangle A'B'C'$

(b): $\text{Var}(X)=E(X^2)-[E(X)]^2=\frac{\sum_{x=1}^n x^2}n-(\frac{1+n}2)^2$. By $\sum_{x=1}^n x^2=\frac{n(n+1)(2n+1)}{6}$, it is not hard to compute $E(X^2)=\frac{(n+1)(2n+1)}{6}$, so $\text{Var}(X)=\frac{2n^2+3n+1}{6}-\frac{n^2+2n+1}4=\frac{4n^2+6n+2-3n^2-6n-3}{12}=\frac{n^2-1}{12}$.

(b): So for all $\epsilon>0$ we need to find $\delta>0$ such that $|f(a)-f(b)|<\epsilon$ whenever $d_0(a, b)<\delta$. Pick $\delta=1$, so $d_0(a,b)=0$, and $a=b=0$, and evidently $|f(a)-f(b)|=0<\epsilon$.

## Problem 13.10 (n)

(c) So $P(|\bar X-75|<5)>0.9$, thus $P(|\bar X-75|\geq 5)\leq 0.1$, so $\frac{\bar{\sigma}^2}{5^2}= 0.1$, thus $\bar{\sigma}^2= 2.5$, while by CLT $\bar X$ is normally distributed, so $\bar{\sigma}^2=\frac{\sigma^2}n=\frac{25}n$, so $\frac{25}n= 2.5$, so $n=10$.

+ (a) $a=2(x_B-x_A), b=2(y_B-y_A),c=x^2_B+y^2_B-x^2_A-y^2_A$
+ (b) $a=2(x_B-x_A), b=2(y_B-y_A),c=x^2_A-x^2_B,d=y^2_B-y^2_A$

### (a)

Product: by the definition of $\R^n, \R^m$ as metric spaces. The map $f:\R^n\times \R^m\to \R^{n+m}$ that $((x_1,...,x_n),(x_{n+1},...,x_{n+m}))\mapsto (x_1,...,x_{n+m})$ is evidently a bijection that is continuous on both directions (as it's just almost the identity function). Then, we turn these metric spaces into topological spaces.

## Problem 15.11 (b)

$q_q$ is the accept state. All the other cases lead to the reject state, thus omitted.

+ Only in Euclidean plane: $2\measuredangle ABC+2\measuredangle CDA\equiv0$.
+ No rectangles in neutral planes in general
+ Neutral plane: angle equal to $\pi$ means it's a line
+ Replicated ⛛s
+ Absolute
+ Cross-ratio: $\delta(A, B)$
  + Distance: $\ln(\delta(A,B))$
+ Let $OP=x$, $OP_h=y$, so $y=\ln{\frac{1+x}{1-x}}$, thus $x=\frac{e^y-1}{e^y-1}$

The problem in the Euclidean sense is equivalent to "Given $\Gamma$ a circle, $\Gamma_1,\Gamma_2$ circlines perp. to $\Gamma$, then $\Gamma_1,\Gamma_2$ have no point of intersection $\iff$ there exists $\Gamma_3$ a circline perp. to $\Gamma$ that is also perp. to $\Gamma_1,\Gamma_2$".

## 2.6 (d)

   ![image-20220121135348662](hw1.assets/image-20220121135348662.png)

   (c): $P(H_2\mid H_1)=$ $P(H_2\mid FH_1)P(F\mid H_1)+$ $P(H_2\mid F^C H_1)P(F^C\mid H_1)$. By known information, $P(H_2\mid H_1)=\frac25 P(H_2\mid FH_1)+\frac35 P(H_2\mid F^C H_1)$. Also, $P(H_2 \mid FH_1)=\frac12, P(H_2\mid F^CH_1)=\frac34$, so the result is $\frac25\frac12+\frac35\frac34=0.65$.

  This is a static-0 hazard.

# Homework 10

# Week 2 homework

  + Two bits $ab$. If $a=1$ then apply $X$. Then, if $b=1$, then apply $Z$.
  + Example: if $ab=11$, we apply $ZX\otimes I$ on the initial state $\ket{00}+\ket{11}$ as $(ZX\otimes I)(\ket{00}+\ket{11})$.
  + Bell basis: $ab=00, 01, 10, 11$ gives four states of the two qubits, and that form a Bell basis (they're orthogonal).
  + CNOT: if the second qubit is $\ket1$, then the first one is flipped.

## Question 2

## Question 1

+ $d_1(A,B)=0 \implies \sqrt{(x_A-x_B)^2+(y_A-y_B)^2}=0$ $\implies (x_A-x_B)^2+(y_A-y_B)^2=0 \implies$ $x_A-x_B=0, y_A-y_B=0\implies$ points $A$ and $B$ have the same $x$, $y$ position $\implies A=B$. Reversing the direction of the implications in this proof gives the proof of the other direction.
+ $d_1(A, B)\geq 0$ holds because square roots are positive.
+ $d_1(A,B)=\sqrt{(x_A-x_B)^2+(y_A-y_B)^2}=$ $\sqrt{|x_A-x_B|^2+|y_A-y_B|^2}=$ $\sqrt{|x_B-x_A|^2+|y_B-y_A|^2}=$ $d_1(B,A)$
+ Show $d_1(A,B)+d_1(B, C)\geq d_1(A,C)$. Prove by taking the power of 2 on both sides: $(d_1(A,B)+d_1(B, C))^2=$ $(x_A-x_B)^2+(y_A-y_B)^2+(x_B-x_C)^2+(y_B-y_C)^2$ $+2(d_1(A,B)d_1(B, C))=$ $((x_A-x_B)^2+(x_B-x_C)^2)+((y_A-y_B)^2+(y_B-y_C)^2)$, while $d_1(A,C)^2=(x_A-x_C)^2+(y_A-y_C)^2$. Since Euclidean distance is a metric, $(x_A-x_C)^2\leq (x_A-x_B)^2+(x_B-x_C)^2$ (and similarly for $y_A, y_B, y_C$). The original inequality is just this inequality where the left-hand-side  added by another non-negative value, so the inequality still holds.

Suppose $\pi_1(X, x)$ abelian, consider $f,g:I\to X$ such that $f(0)=g(0)=x, f(1)=g(1)=y$. Then, by abelian, $f*\bar g\simeq g*\bar f$, so $f*\bar g*f*g\simeq g*\bar f * f *g$, so $f^2=g^2$. This means all loops based on the same point are equivalent up to homotopy, so it doesn't depend on choice of $f$.

![image-20210913024050232](writeup.assets/image-20210913024050232.png)

The new total $\chi^2$ is $10.9381$, thus $P(\chi^2_3>10.9381)\approx 0.012\%<\alpha$, the result is much smaller and is now significant.


(a): $E(X)=\sum_{x\in C}x P(X=x)=\sum_{x\in C}\frac x{|C|}=\frac{\sum_{x\in C}x}{|C|}$. So, in case of $C=\{1,2,3,...,n\}$, $|C|=n$ and $\sum_{x\in C}x=\frac{n(1+n)}2$, so $E(X)=\frac{1+n}2$.

Quiz (take-home) 11

  + CNOT controlled by the function value

### 12.2

+ Deck transformation
  + Forms a group
  + Tells you the maximum number of elements in the group

+ a. $C=A,H=D$, so remove $C$ and $H$

![image-20211111164226695](writeup.assets/image-20211111164226695.png)

(c) $x=24,y=12,z=36$

(k) Similarly it's $\frac{f(x,y)}{f_X(x)}=$ $\frac{3-3x}{3x^2-6x+3}=$ $\frac{1-x}{x^2-2x+1}=$ $\frac{1-x}{(1-x)^2}=$ $\frac1{1-x}$.

### (c)

Metric: $d((x, y), (x, y))=\max(d_X(x, x), d_Y(y, y))=0$ and $d((x_1, y_1), (x_2, y_2))=0\implies$ $\max(d_X(x_1, x_2), d_Y(y_1, y_2))=0\implies$ $d_X(x_1, x_2)=0, d_Y(y_1, y_2)=0$ $\implies x_1=x_2, y_1=y_2$. Then we show triangle inequality, $d((x_1, y_1), (x_2, y_2))+d((x_2, y_2), (x_3, y_3))$ $=\max(d_X(x_1, x_2), d_Y(y_1, y_2))+\max(d_X(x_2, x_3), d_Y(y_2, y_3))$, while $d((x_1, x_3), (y_1, y_3))=\max(d_X(x_1, x_3), d_Y(y_1, y_3))$. Given that $d_X(x_1, x_3)\leq d_X(x_1, x_2)+d_X(x_2, x_3)$ and similarly for $d_Y$, by case analysis on the value of the two max functions we can obtain the inequality.

(b): $P(X<Y)=\frac67$ because only when $X=7$ does $Y<X$.

`w` from line 2, `j` from line 3, `a`, `b` from line 15, `i`, `h` from line 1.

If $p$ is homeo, then it maps loops from $\tilde X$ bijectively to $X$, so $p_*$ is a group isomorphism.

### K-map

## Problem 2.9 (j)

Let $\delta=\epsilon$ will make such implication hold.

## Problem 5.3 (g)

(d) $E(X=x)=$ $\int_0^1\int^y_0 x(3-3x)d(xy)=$ $\frac14$.

(f) $X_2\sim N(0,2)$.

So, $\triangle ABC$ is an isosceles triangle with base $[AB]$ _or_ $[BC]$ _or_ $[CA]$. So, by theorem 4.2, $\measuredangle ABC\equiv-\measuredangle BAC\equiv\measuredangle CAB$, and similarly $\measuredangle BCA\equiv-\measuredangle CBA\equiv\measuredangle ABC$, and by transitivity the original statement holds.

(b) $P(X_j=x)=x\frac{1}{10}$

| $Q_1$ | $Q_2$ | OUT9 (X) | OUT8 (Y) |
| ----- | ----- | -------- | -------- |
| 0     | 0     | 0        | 0        |
| 0     | 1     | 1        | 0        |
| 1     | 0     | 0        | 0        |
| 1     | 1     | 0        | 1        |

+ Distinguishing between states:
  + Between $\ket+=\cfrac1{\sqrt2}(\ket0+\ket1)$ and $\ket-=\cfrac1{\sqrt2}(\ket0-\ket1)$
    + Apply $H=\frac1{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$ and measure
    + It works because $H\ket+=\ket0$ and $H\ket-=\ket1$.
  + Between $\ket0$ and $\ket+$
    + Cannot, because they're not perfectly orthogonal
+ Properties
  + Unitary transformations are
    + Invertible: $U^\dagger U=I$
    + Deterministic
    + Continuous
  + Measurements
    + Irreversible
    + Probabilistic
    + Discontinuous
+ Connection: 2-norm
  + $\norm{\ket x}_2$
  + $p$-norm: $\sqrt[p]{\sum_{k=0}^d{|\alpha_k|^p}}$
  + Unitary transformation preserve the 2-norm
  + $\sqrt{\braket\phi}=\norm{\ket\phi}_2$
  + $\norm{U\ket\phi}=\sqrt{\bra\phi U^\dagger\cdot U\ket\phi}=\sqrt{\braket{\phi}}$
  + Measurement gives you the probability 'governed' by the 2-norm
+ $n$-qubit systems
  + Generalization of 2-qubit (squares sum up to $1$)
  + The basis is the enumeration of $\ket n$
  + Operations
    + Unitary operations (apply component-wise)

By 13.2, $BD_h<\frac12\ln{\frac{1+\cos{\measuredangle_h DBA}}{1-\cos{\measuredangle_h DBA}}}$. Let $\alpha=\measuredangle_h DBA$, and by the previous statement $50<\frac12\ln{\frac{1+\cos\alpha}{1-\cos\alpha}}$, so $100<\ln{\frac{1+\cos\alpha}{1-\cos\alpha}}$, so $\frac{1+\cos\alpha}{1-\cos\alpha}>e^{100}>2.6\times 10^{43}$, therefore $\cos\alpha>\frac{e^{100}-1}{e^{100}+1}$. This validates $|\cos{2\alpha}|<\frac{1}{10^{10}}$.

## Problem 15.6 (b)

(a): First convert $N_2$ into a DFA and take the complement, let's call it $D_2$. Then, take the intersection of $N_1$ and $D_2$ as NFAs. Since we didn't convert $N_1$ into a DFA, we have much less states.

For all $x\in X$ such that $x\notin A$, it is known that $r(x)\in A$ by the definition of retract. Since $X$ is Hausdorff, let's take the disjointed open neighborhood of $x$ and $r(x)$, namely $U$ and $V$. Note that $V\cap A$ is open in $A$, and $r^{-1}(V\cap A)$ is therefore open in $X$ and it contains $x$. Plus, $U$ is also open in $X$ that contains $x$. we take $r^{-1}(V\cap A)\cap U$ and it should still be open in $X$ and it contains $x$ and is disjointed from $A$.

POS: $(W+Z)(X+\overline Z)$

### (b)

## Exercise 6.6 (l)

3. Let $q=\sqrt{10}$. Assume for the sake of contradiction that $q$ is rational. Then, by definition of rationals, for $a, b\in\Z^*, \frac ab=\sqrt{10}$ and $a, b$ are coprime, which means $a^2=10 b^2=2b^2\cdot5$. This implies that $a^2$ is even, so $a$ is also even. Suppose $a=2k$ for some $k\in\Z$, so $5b^2=2k^2$, so $b$ is also even, contradicting the presupposition that $a, b$ are coprime.

![image-20220225173220953](hw3.assets/image-20220225173220953.png)

  | Present State | $X_{next}=0$ | $X_{next}=1$ | $X_{out}=0$ | $X_{out}=1$ |
  | ------------- | ------------ | ------------ | ----------- | ----------- |
  | A             | F            | B            | 0           | 0           |
  | B             | D            | A            | 0           | 0           |
  | D             | G            | A            | 1           | 0           |
  | E             | D            | A            | 0           | 0           |
  | F             | F            | B            | 1           | 1           |
  | G             | G            | D            | 0           | 1           |

## Problem 15.11 (e)

Choose $0^p1^{p^2}$, consider four cases:

There are only JK-flip flops in the lab :-(

So $Y\sub A'$ for all $A'$ closed such that $A\sub A'$. Suppose $Y$ is not connected, then $Y$ is the union of two disjointed, nonempty open subsets $W, V$. Now we show that $W$, $V$ must both intersect $A$, which leads to a "separation" of $A$, contradicting the fact that $A$ is connected.

+ About measurement
  + Single line: qubit, double line: classical data
  + Measure in $\ket0, \ket1$ is trivial
  + Measure in $\ket+,\ket-$ needs $H=\frac1{\sqrt2}\begin{bmatrix}1&1\\1&-1\end{bmatrix}$
    + Since $H\ket+=\ket0,H\ket-=\ket1$
  + Measure in different spaces: apply transformation to make it standard
  + Measure in Bell basis: $\ket{00}+\ket{11},\ket{01}+\ket{10},\ket{00}-\ket{11},\ket{01}-\ket{10}$

By  (@psu.edu), for Math 427.

Let's correspond $A,B,C,D$ to $00,01,10,11$ respectively, and for each state, it outputs $(0,0),(1,0),(0,0),(0,1)$ respectively.

+ $85_{10}=1010101_2, 29_{10}=11101_2$,$203_{10}=11001011$

+ Identity element: identity function. Left and right identity laws are obviously satisfied.
+ Closed: compositions of continuous functions are also continuous.
+ Inverse: from the definition: "a homeomorphism is a continuous function with a **continuous inverse**". 

## Problem 5

+ $f(f^{-1}(C))=C\iff f$ is onto, $f^{-1}(f(C))\supset C$
+ Concrete topology with at least two points is not Hausdorff
+ 8.14 (i): group action of $\Q$ on $\R$
+ There is an open subset of $\R$ that contains $\Q$ and is not $\R$.
+ 9.8 (f) adding one point is fine

Screenshots:

## Problem 6

## Problem 7

![image-20211118162637965](submission1.assets/image-20211118162637965.png)

## Problem 1

## Problem 2

(b): So $P(Y\leq\frac12)=\frac12\int^{\frac12}_0{e^{-y/2}dy}=\frac12(e^{-y/2}\mid^1_0)=\frac12e^{-y/2}$ .

## Problem 2 (b)

## Problem 3

## Problem 4

## 8.4

 , Cmpen 270 Lab 5

# Math 429 HW6

See next page:

## Problem 16.11 (f)

+ Multinomial distribution
  + ![image-20220414135557095](week12-2.assets/image-20220414135557095.png)
+ Bivariate normal distribution
  + $X_1$ independent $X_2\iff Cov(X_1,X_2)=0$
  + $Cov(X_1,X_2)=0\implies\rho=0\implies f(x_1,x_2)=0$
  + 

We expand the definition of null homotopic: it means that there's a continuous map $h:[0,1]\times S^1\to X$ such that $h(1, s)=f(s)$ and $h(0, s)=x$ for a constant $x\in X$. Using the definition of $S^1\sub \C$, we may think of the condition $h(0, s)=x$ as $h(z, r)=h(y, s)=x\iff zr=ys$, because $xr=ys\iff z=y=0$.

module ff(  
  input   wire clk,
  input   wire reset,
  input   wire val_in,
  output  reg  q,
  output  reg  qb
);
  wire T_input = val_in;
  wire D_input = T_input ^ q;

(b) Under $H_0$, the values of $p_i$ are:

## Problem 7.13 (h)

(e) So $f_{X\mid Y}(x\mid y)=$ $\frac{f(x,y)}{f_Y(y)}=$ $\frac{\frac1x}{-\ln y}=\frac1{-x\ln y}$, where $0\leq y\leq x\leq 1$.

## Problem 2 (c)

And the test statistic is $\chi^2=\sum^n_{i=1}\frac{(Y_i-np_i)^2}{np_i}$ with degrees of freedom $3-1-1=1$, so:

Suppose there is an injective function $f:M\to M_0$, then $f(a)\neq f(b)\implies a\neq b$, so $d_0(a,b)=1$, and simply pick $\epsilon=1$ makes it impossible to find $\delta$, so it's not continuous.

(b) So $T=\frac{Z}{\sqrt {V/v}}$ ([source](https://en.wikipedia.org/wiki/Student%27s_t-distribution#characterization)), where $V$ has $\chi^2$-distribution and is independent of $Z$. Then, $T^2=\frac{Z^2}{V/v}$ and can be written as $\frac{Z^2/1}{V/v}$. Therefore $T$ has $F$-distribution with numerator $1$ and denominator $v$.

Cut $n+\frac12$ where $n$ is the opened loops

|$E_{i,j}$|Union|Confederate|
|--|-----|-----|
|Killed|1982.9|1647.1|
|Wounded|9450.2|7849.8|
|Missing/Captured|966.87|803.13|

  First of all, non of $\alpha,\alpha',\beta,\beta'$ are zero. We can derive $\alpha'=\beta'$ from (1) and (2); and $\alpha=\beta$ from (1) and (3), so $\alpha\alpha'=\beta\beta'$. But from (1) and (4) we can derive a contradiction.

### (d)

+ $\langle \vec u,\vec v\rangle=|\vec u|\cdot |\vec v|\cdot \cos \alpha$

$F=\overline X+Y\overline Z=\overline{X\cdot\overline{Y\overline Z}}$

(c)![image-20220427144311823](hw7.assets/image-20220427144311823.png)


Consider a loop $f:I \to X$. Without the loss of generality, it must be in the following two cases:

## Problem 2 (a)

+ Any subgroup of integers is either isomorphic to integers or trivial.
+ $\pi_1(X)=0$ and $|p^{-1}(X)|\leq|\pi_1(X)|=1$, so $|p^{-1}(X)|=1$.
  + Loops and non-loops in $p^{-1}(X)$ are both mapped to $X$
+ $p_*(\pi_1(\tilde X))<\pi_1(X)$ (fact: $p_*$ is monic) this implies $\pi_1(\tilde X)<\pi_1(X)$
+ Key property of covering map: that you can lift homotopy
+ Any homeo is a covering map
  + So it has an inverse, so homeo $\implies$ induced homomorphism is isomorphic (trivial)
+ Induced homomorphism is onto implies the covering map to be homeo
  + Argument: 

$P(X+Y<1)=\iint f(x, y) d(xy)$ (where $X+Y\in[0, 1]$ and $x, y\in[0, 1]$), so $x\in[0, 1-y]$, so it's $\int^1_0\int_0^{1-y}f(x, y)dxdy$ $=\int^1_0\int_0^{1-y} 4xy dxdy$ $=\int^1_0 2y(1-y)^2 dy$ $=\fbox{$\frac16$}$.

If $p_*$ is a group isomorphism, then loops are mapped bijectively, so what???

+ Classification of algebraic curves (of all degrees)
+ Properties of algebraic curves, like intersections, tangents, singularities

+ Hyperbolic geometry has a contradiction $\iff$ Euclidean geometry has a contradiction
+ Take a sector in the unit circle of area $\frac\alpha2$, the axis $(\sin \alpha, \cos \alpha)$
  + Change the circle to double curves $x^2-y^2=1$
  + Get hyperbolic sin and cosine
  + $\cosh\alpha=\cos(i\alpha)$
+ $\cosh'=\sinh,\sinh'=\cosh,\cosh^2-\sinh^2=1$
+ $\cosh(2\alpha)=2\cosh^2(\alpha)-1$
+ In between: $\frac{e^\alpha}2$
+ $\cosh a\cdot \cosh b=\cosh c,\cos a\cdot \cos b=\cos c$
+ Ultraparallel: don't share ideal points
+ Limiting parallel

## Problem 15.11 (g)

### 14.4

For $S^n$ where $n\geq 2$, consider the construction of "suspensions", by induction:

3. ```
   <l> -> (<l>)) | <e>
   <e> ->
   ```

(a) As in problem 2, $\sum_{i=1}^nX_i=n\bar X$, so:
$$
\begin{align*}
\sum_{i=1}^n(X_i-\bar X)^2&=\sum_{i=1}^n(X_i^2+\bar X^2-2X_i\bar X)\\
&=\sum_{i=1}^n X_i^2+\sum_{i=1}^n\bar X^2-2 \sum_{i=1}^nX_i\bar X\\
&=\sum_{i=1}^n X_i^2+n\bar X^2-2\bar X\sum_{i=1}^nX_i\\
&=\sum_{i=1}^n X_i^2+n\bar X^2-2n\bar X^2\\
&=\sum_{i=1}^n X_i^2-n\bar X^2\\
&=n\left(\frac1n \sum_{i=1}^n X_i^2-\bar X^2\right)
\end{align*}
$$
Since $\sum_{i=1}^n(X_i-\bar X)^2\geq0$, so $n\left(\frac1n \sum_{i=1}^n X_i^2-\bar X^2\right)\geq 0$, so $\frac1n \sum_{i=1}^n X_i^2-\bar X^2\geq 0$, so $T_2-T_1\geq 0$ so $T_2\geq T_1$. This means $P(T_1\leq T_2)=\fbox 1$.

+ Brouwer's FP theorem
  + It's actually a strong deformation retraction
+ Polynomial with $\C$
  + $p:\C\to\C$ a continuous map, which is a polynomial
  + Goal: $z_0$ such that $p(z_0)=0$
  + Send circles (as point sets in $\C$) through $p$ to $\C$
  + Suppose no such $z_0$ exists, than $p:\C\to (\C\setminus\{0\})$, so we show that this function is not continuous to lead to a contradiction
    + If it's continuous, we get $p_*:0\to \Z$ a group homomorphism, which obviously must be a constant map
    + So by sending circles, the image of $p$ must only be loops with the same homotopy type
    + Send trivial circle (homotopic to a point) to $p$, we get trivial circle as image, so for all other circles, we can also only get trivial circles
    + When the radius is very very large, say, $k\to\infty$, then $p(k)\to k^n$ (where $n$ is from the polynomial) must be far away from origin, which is a circle contains the origin, and this is a nontrivial loop
    + We cannot have nontrivial loops
+ Formal proof (unintuitive)
  + $q(z)=\frac{p(z)}{|p(z)|}$ maps loops to *unit circles* (they were mapped to arbitrary circles before)
  + 

The closures are $[a, b), [a, b), [a, b], [a, b]$, respectively.

  + $\frac{(\bar X-\mu_0)^2}{\sigma^2/n}\geq c_1$, $\frac{\bar X-\mu_0}{\sigma/\sqrt n}\geq c_2$, and $c_2=1.96$

(b) By $\frac{(n-1)S^2}{\sigma^2} \sim \chi^2_{n-1}$, we know $\frac{(n-1)S^2}{\sigma^2} =\frac{\sum^n_{i=1}(X_i-\bar X)^2}{\sigma^2}$, so:
$$
\begin{align*}
Var(\hat\sigma^2_{MLE})
&=Var\left(\frac1n \sum^n_{i=1}(X_i-\bar X)^2\right)\\
&=Var\left(\frac{\sigma^2}n \times \frac{(n-1)S^2}{\sigma^2}\right)\\
&=\left(\frac{\sigma^2}n\right)^2 \times Var\left(\frac{(n-1)S^2}{\sigma^2}\right)\\
&=\left(\frac{\sigma^2}n\right)^2 \times 2(n-1)\\
&=\fbox{$\frac{2\sigma^4 (n-1)}{n^2}$}
\end{align*}
$$
Then, for $S^2$:
$$
\begin{align*}
Var(S^2)&=Var\left(\frac{n}{n-1}\hat\sigma^2_{MLE}\right)\\
&=\left(\frac n{n-1}\right)^2\times Var(\hat\sigma^2_{MLE})\\
&=\frac{n^2}{(n-1)^2}\times \frac{2\sigma^4 (n-1)}{n^2}\\
&=\fbox{$\frac{2\sigma^4}{n-1}$}
\end{align*}
$$
(c)
$$
\begin{align*}
\operatorname{eff}(\sigma^2, S^2)
&= \frac{Var(S^2)}{Var(\sigma^2)}\\
&= \frac{\frac{2\sigma^4}{n-1}}{\frac{2\sigma^4 (n-1)}{n^2}}\\
&= \fbox{$\left(\frac n{n-1}\right)^2$}\\
\end{align*}
$$
Since $n>n-1$, $\hat\sigma^2_{MLE}$ is more efficient than $S^2$. Since $n\to \infty \implies \frac n{n-1}\to 1$, so when $n\to \infty$ they become similarly efficient.


### 14.9

$A$ is $\langle M_1,M_2\rangle$ such that $h(M_1)\cap h(M_2)\ne\empty$.

## 4.5 (d)

   ![image-20220121134652211](hw1.assets/image-20220121134652211.png)

## 12.21

+ $[X,Y]\cap(P,Q)=\emptyset \implies \ang QPX, \ang QPY$ have the same sign

+ Cor: complement of $(PQ)$ is a union of two disjointed subsets of the plane

+ (a) $TX=\begin{bmatrix}1&0\\0&e^{2\pi i/8}\end{bmatrix}\begin{bmatrix}0&1\\1&0\end{bmatrix}=\begin{bmatrix}0&1\\e^{2\pi i/8}&0\end{bmatrix}$
+ (b) $THX=\begin{bmatrix}1&0\\0&e^{2\pi i/8}\end{bmatrix} \frac1{\sqrt2}\begin{bmatrix}1&1\\1&-1\end{bmatrix}\begin{bmatrix}0&1\\1&0\end{bmatrix}=\frac1{\sqrt2}\begin{bmatrix}1&1\\-e^{2\pi i/8}&e^{2\pi i/8}\end{bmatrix}$
+ (c) $THT=\begin{bmatrix}1&0\\0&e^{2\pi i/8}\end{bmatrix}\frac1{\sqrt2}\begin{bmatrix}1&1\\1&-1\end{bmatrix} \begin{bmatrix}1&0\\0&e^{2\pi i/8}\end{bmatrix}=\frac1{\sqrt2}\begin{bmatrix}1&e^{2\pi i/8}\\e^{2\pi i/8}&-i\end{bmatrix}$
+ (d) $HTH=\frac1{\sqrt2}\begin{bmatrix}1&1\\1&-1\end{bmatrix}\begin{bmatrix}1&0\\0&e^{2\pi i/8}\end{bmatrix}\frac1{\sqrt2}\begin{bmatrix}1&1\\1&-1\end{bmatrix}=\frac12\begin{bmatrix}1+e^{2\pi i/8}&1-e^{2\pi i/8}\\1-e^{2\pi i/8}&1+e^{2\pi i/8}\end{bmatrix}$

First, $AF//ED\implies \measuredangle EAD\equiv \measuredangle EDA\implies AE=ED$.

   (a): $P(H_1)=P(F)P(H_1\mid F)+P(F^C)P(H_1\mid F^C)$ $=\frac12\frac12+\frac12\frac34=\frac58$.

# 5.20

   (c): Similarly $\left(\matrix{4\\2}\right)=6$.

+ 15.12

To show $\iota_*$ is monic, we need to show that for every group homomorphism $g_1, g_2$ such that $\iota_*g_1=\iota_*g_2$ we can deduce $g_1=g_2$. So:
$$
\begin{align*}
\iota_*g_1=\iota_*g_2 &\implies \iota g_1^*\simeq\iota g_2^* \\
&\implies r(\iota g_1^*)\simeq r(\iota g_2^*)\\
&\implies (r\iota) g_1^*\simeq(r\iota) g_2^*\\
&\implies 1 g_1^*\simeq 1 g_2^*\\
&\implies g_1^*\simeq g_2^*\\
&\implies g_1=g_2
\end{align*}
$$
Conversely we need to show that for every group homomorphism $g_1, g_2$ such that $g_1r_*=g_2r_*$ we can deduce $g_1=g_2$.
$$
\begin{align*}
g_1r_*=g_2r_* &\implies g_1^*r\simeq g_2^*r \\
&\implies (g_1^*r)\iota\simeq(g_2^*r)\iota\\
&\implies g_1^*(r\iota)\simeq g_2^*(r\iota)\\
&\implies g_1^*1\simeq g_2^*1\\
&\implies g_1^*\simeq g_2^*\\
&\implies g_1=g_2
\end{align*}
$$

## 4.5 (e)

+ Condition for $PQ_h+QR_h=PR_h$
  + On the same h-line in order
+ $\R \lrarr$ h-line as $x \lrarr \ln{\frac{AX}{BX}}$
  + Construct the distance function for the line at the center
+ Prove neutral plane axioms

By 2.1 a), picking three distinct points will give three distinct lines; and picking different triples of points will give different triples of lines. So infinitely many points can give infinitely many lines.

Idea: the quotient topology is the finest topology given a continuous function, so it has more open sets than other topologies.

## Activity 3

## 8.6

## Activity 2

## Cmpen 270 HW 8

## Question b

## Activity 1

## Question a

(c) Also by normal distribution results, $\sigma^2$.

Consider the circle of radius $1$ and centered at $x_0$. Then, consider polar coordinate $\R^2$ centered at $x_0$, we construct the strong deformation $r(x, \theta)=(1,\theta)$ which maps $\R^2\setminus\{x_0\}$ to the given circle, and is continuous because it's constant.

  $=Z\ket0\otimes \ket0+Z\ket1\otimes\ket1$

![image-20220427143053777](hw7.assets/image-20220427143053777.png)

#  HW 11

#  HW 12

So, $P(X>s+t \mid X>t)=\frac{P(X>s+t\land X>t)}{P(X>t)}=\frac{P(X>s+t)}{P(X>t)}$.

+ Complement: sum up to $\frac\pi2$
  + Adjacent: sum up to $\pi$

+ $Q_1=Q_1'\oplus Q_2'$

#  Design Project 1

+ Pasch's theorem: if a line does not intersect with the vertices of a triangle, they must intersect with either 2 or 0 points

## Plan

(b) Let $\bar{X}=\frac1{40}\sum^{40}_{i=1} X_i$, so what we need to compute is simply $P(40 \bar X> 1700)=P(\bar X>42.5)$. By CLT, $\bar X\sim N(E(X_i), \frac{Var(X_i)}{40})=$ $N(40, 5.7625)$, so $\frac{\bar X-40}{\sqrt{5.7625}}\sim N(0, 1)$, so $P(\bar X>42.5)=$ $P(Z> \frac{2.5}{\sqrt{5.7625}})$, thus $c=1.04144$.

Say, $AB=i$, let $A=(0,0)$, so $B=(i,0)$. Let $M=(x,y)$, so $\frac{AM^2}{BM^2}=(\frac{AM}{BM})^2=k^2=\frac{x^2+y^2}{(i-x)^2+y^2}$, hence $k^2((i-x)^2+y^2)=x^2+y^2$, and
$$
\begin{align*}
k^2((i-x)^2+y^2)&=x^2+y^2\\
k^2(i^2+x^2-2xi+y^2)&=x^2+y^2\\
(k^2-1)(x^2+y^2)+k^2i^2-2k^2xi&=0\\
x^2+y^2-\frac{2k^2i}{k^2-1}x+\frac{k^2i^2}{k^2-1}&=0
\end{align*}
$$
Therefore, $a=\frac{2k^2i}{k^2-1},b=0,c=\frac{k^2i^2}{k^2-1}$.

## Exercise 7.13 (b)

Proof idea: if an NFA with $n$ states accept a finite string, then it must accept a finite string of length $\leq n$, because otherwise there must be loops in the states and can be removed. Then we enumerate all such strings to make sure that the NFA does not accept any finite string. Then it's cofinite.


    ![image-20210827145610931](C:\Users\lenovo\AppData\Roaming\Typora\typora-user-images\image-20210827145610931.png)

$H$ is orthocenter $\implies AH\perp BC,CH\perp AB,BH\perp AC$ $\implies AC, AB, AH$ are overlapped with the altitudes of $\triangle BCH$. Therefore, $AC,AB,AH$ intersect at one point. The point must be $A$ because $AC$, $AB$ share this point. So $A$ is the orthocenter of $\triangle BCH$.

+ (c) $(\frac35\ket0+\frac45\ket1)(\frac35\ket0+\frac45\ket1)$ which computes to the original formula.

7. These problems are equivalent to "one minus the probability of at least 6 numbers in range $[0,5]$ appears in 6 rolls", "... 11 numbers... 12 rolls", etc., so $A:1-\frac56^6$, $B:1-\frac56^{12}-\left(\matrix{12\\1}\right)\cdot\frac{5^{11}}{6^{12}}$, $C: 1-\frac56^{18}-\left(\matrix{18\\1}\right)\frac{5^{17}}{6^{18}}-\left(\matrix{18\\2}\right)\frac{5^{17}}{6^{18}}$, so $A$ has higher probability.

| $C$  | $A$  | $B$  | $Q$   | $\overline Q$ |
| ---- | ---- | ---- | ----- | ------------- |
| 1    | 0    | 0    |       |               |
| 1    | 0    | 1    |       |               |
| 1    | 1    | 0    |       |               |
| 1    | 1    | 1    | latch | latch         |
| 0    | 0    | 0    |       |               |
| 0    | 0    | 1    |       |               |
| 0    | 1    | 0    |       |               |
| 0    | 1    | 1    |       |               |

To show $Cl_Y(A)= Cl_X(A)$, consider $X=\{1, 2, 3, 4\}$ with the topology $\{\empty, X, \{2, 3\}\}$, $Y=\{1\}$ with the subspace topology $\{\empty, Y\}$, and $A=\{1\}$. $Cl_X(A)=\{1, 4\}$ while $Cl_Y(A)=\{1\}$.

6. ```
   <SNFloat>      -> <Float> <EExponent>
   <EExponent>    -> E<Exponent> | <Empty>
   <Float>        -> <NonZeroDigit><DotNum>
   <DotNum>       -> .<Num> | <Empty>
   <Exponent>     -> <Prefix><Num>
   <Prefix>       -> + | - | <Empty>
   <Num>          -> <Digit><Num> | <Digit>
   <Digit>        -> 0 | <NonZeroDigit>
   <NonZeroDigit> -> 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9
   <Empty>        ->
   ```

Let $Y$ and $X$ have the same carrier set $Z$ but $Y$ has less open sets. Say, $A\in X$ but $A\notin Y$. Let $f$ be the identity map on $Z$. Since $X$ has all open sets that $Y$ has, so $f$ is continuous, but the preimage of $f^{-1}(A)=A$ is not open in $Y$.

5. (a): Just $1$.

+ $P(A\mid B)=\frac{P(A\cap B)}{P(A)}=\frac{P(B)P(B\mid A)}{P(A)}$
+ Marginal probability = not conditional probability
+ Law of Total Probability (LTP)

(b) $(λz. z) (λy. y~y) (λx. x~a)=$ $(λy. y~y) (λx. x~a)=$ $(λx. x~a)(λx. x~a)=$ $(λx. x~a)(λy. y~a)=$ $(λy. y~a)a=$ $a~a$

+ (a) I worked with .

3. Suppose the probability of choosing the fair coin is $F$.

Example of $\mathscr U_f \not\simeq \mathscr U$: that $X$ and $Y$ share the same carrier set (say, of size greater than $2$), but $X$ has the discrete topology (all subsets are open) and $Y$ has the concrete topology, and $f$ maps elements identically. Then, $f$ is evidently continuous, and $\mathscr U_f$ is the same as the topology on $X$, but this is not homeomorphic to the concrete topology.

The following TM $M$ decides $\text{COF}_{NFA}$:

Since $l, m, n$ and $O$ form six equal angle, all of them are equal to $\frac\pi3$.

Basically, namespaces in C# helps organization of program modules. It also helps encapsulation of implementation details.

## 3 a

(b) By CLT, the desired distribution follows normal distribution with mean $\theta$ and variance $\frac1n \theta(1-\theta)$, so $c(b-a)\frac1n \sum^n_{j=1}I_j\sim N(\theta, \frac{\theta(1-\theta)}n)$.

![image-20211021162331630](lab7.assets/image-20211021162331630.png)

## 3 b

## 9.4

## 8.16

(a) So, `foo1 `calls `bar(x, y)`, then in `bar`, `x = x - y = -3`, `y` remains unchanged, then it returns `2 * x` which is `-6`, so `sum = -6 + 6 = 0`.

  + Game: check $\frac{L(\hat\theta_1)}{L(\hat\theta_0)}=\frac{\max_{\theta\in\Omega_1}L(\theta)}{..}>c$

![image-20220403192252983](hw11.assets/image-20220403192252983.png)

The (constant on points) map $[0,1]\to [0,1]/\sim$ where $0\sim1$ and $1\sim0$ where the closed intervals are regarded as subspaces of $\R$.

+ $0000, 0001$ as well as $1000,1001$ as well as $0101,1101$
+ SOP = $B'D'+AC'+C'D+A'BD$, consensus term $A'B'C'$
+ $(B+D)'+(A'+C)'+(C+D')'+(A+B'+D')'+(A+B+C)'$

POS: $(\overline{B}+C+D)(\overline{A}+\overline{D}+C)(\overline{B}+\overline{C}+\overline{D})(A+B+\overline{D})$

(b) So all students finished the exam after $30$ minutes, so it's $1-\frac{\bigcap_{i\in[1,65]}P(T_i>60)}{\bigcap_{i\in[1,65]}P(T_i>30)}=$ $1-\frac{P(T_i>60)}{P(T_i>30)}^{65}=$ $1-\frac{e^{-60\lambda}}{e^{-30\lambda}}^{65}=1-{e^{-1956\lambda}}$.

## Exercise 7.13 (c)

+ $\forall x>0,y>0.~x>y\iff x^2>y^2$
+ $x^2=2$ has no solutions in rational numbers

Suppose $B$ is the center of the absolute, take $D\in AC_h$ such that $BD_h\perp AC_h$. Since $\triangle_h ABC$ is equilateral (thus nondegenerate), $AD_h=CD_h=\frac12 AC_h=50$, by triangle inequality $BD_h>100-50=50$.

(i) in $\R$, let $f(x)=x, g(x)=x+1,h(x)=x+2$ for $x\in[0,1]$.

Then, realize the diagram in lab.

## 12.1

   (c): Let $K=O^CY^C$ for notational simplicity. $P(M\mid K)=\frac{P(M)P(K\mid M)}{P(K)}$ $=\frac{\frac13\frac14}{\frac34}=\frac13\frac14\frac43=\frac19$.

+ Properties of supremum and infimum
+ Defined open/closed intervals

+ Useful lemma: $(A\otimes B)(C\otimes D)=(AC)\otimes(BD)$

(c) Rejection region: $R=\{T:T<c\}$, so it goes from right to left.

Doubled expectation:

(b) 30%

$\implies$: There exists an open set $W\sub Y$ such that for all closed sets containing $W$, they contain $Y$ (say, $\overline W=Y$). This means all open subsets of $Y$ are also subsets of $W$, so $Y^o\sub W$. To show $\overline{Y^o}=\overline W$, we need to show $W\sub \overline{Y^o}$. Suppose the contrary, then $W$ has a smaller closure $\overline{T^o}$, but closure should be the smallest.

   (d): $13\times \left(\matrix{4\\2}\right)\times 12 \times \left(\matrix{4\\2}\right)\times 11 \times \left(\matrix{4\\1}\right)=3953664$ so the probability is $3953664\div 311875200=\frac{264}{20825}$.

8. (a): This is similar to the "LA" problem, so $\left(\matrix{3+10-1\\10}\right)=66$ ways to choose.

(a) $P(X=0)=P(X=2)=\frac14$, $P(X=1)=\frac12$

Pump: if $s$ starts with $0$, choose $y=0$ and we can repeat $0$ and it will still belong to the language. If $s$ starts with $1$, then $s$ must only contain $1$, which  can be pumped by any choice of $y$.

+ Example 6
  + $n=30$, $\sum_i X_i=15$, conduct $\alpha=0.05$.
  + $H_0:\theta=0.3$, $H_1:\theta> 0.3$ (because greater).
+ Two ways
  + Binomial dist.: $B:=\sum_i X_i\sim Bin(30,0.3)$ under $H_0$.
  + $p$-value: $\sum P(X\geq 15)$, $R=\{B:B>c\}$ s.t. $P(B\geq c)=\alpha$ and $B\sim Bin(30,0.3)$
  + Asymptotic dist.: when $n>30$: compute $T=\frac{\bar X-\theta}{S/\sqrt n}=\frac{\bar X-\theta}{\sqrt{\frac{\theta(1-\theta)}{n}}}\sim N(0,1)$.
  + The variance is about the r.v. under the null dist.
  + $\theta_{MLE}=\frac{15}{30}$ (???)
  + Reject region: $R=\{T:T>c\}$ s.t. $P(T>c)=\alpha$. Make $t=T[]$ (???)
  + $p$-value: $P(T>t)$
+ Doing a test = find a rejection region
  + $\frac{L(\theta_0)}{L(\theta_1)}=\frac{f(x\mid\theta_0)}{f(x\mid\theta_1)}$, if $>1$, then $\theta_0$ is more likely to maximize
  + Convention: $1/0$
+ Ex 7
  + $R=\{\frac{L(\lambda_1)}{L(\lambda_0)}>c\}$, where $L(\lambda)=\lambda e^{-\lambda x}$, thus ratio is $\frac{\lambda_1}{\lambda_0}e^{-x(\lambda_1-\lambda_0)}$

![image-20210930163302292](lab5.assets/image-20210930163302292.png)

### Question 2, state machine design

The quotient space contains all rationals as a single element. Each irrational $x$ is glued together with numbers that can be written as $x+k$ for $k\in\Q$. So this is essentially $\R\setminus\Q$ with one more point (for all rationals) on the space. This point cannot be separated with other points because the set of all rationals is not open in $\R$ (so it's not sent to the quotient topology), thus not Hausdorff.

The goal is to prove that $d_1$ satisfies the properties of metrics:

Let $U\sub f(S)\sub Y$ be open in $f(S)$, then by the continuity of $f$, we know $f^{-1}(U)\sub X$ is open in $X$. Since $U\sub f(S)$, $f^{-1}(U)\sub S$, so $f^{-1}(U)$ is open in $S$, so $f\mid S$ is also continuous.

| $A$  | $B$  | $C_{in}$ | $C_{out}$ | $S$  |
| :--: | :--: | :------: | :-------: | :--: |
|  0   |  0   |    0     |     0     |  0   |
|  1   |  0   |    0     |     0     |  1   |
|  0   |  1   |    0     |     0     |  1   |
|  1   |  1   |    0     |     1     |  0   |
|  0   |  0   |    1     |     0     |  1   |
|  1   |  0   |    1     |     1     |  0   |
|  0   |  1   |    1     |     1     |  0   |
|  1   |  1   |    1     |     1     |  1   |

(l) Let $x=1/2$, then $P(Y=y)=\frac1{1-1/2}=2$, so $P(Y\geq 3/4)=$ $\int^1_{3/4}2dy=\frac12$.

It is obvious that a leg has Euclidean length $BC=\frac1{\sqrt2}$ given the Euclidean radius of the absolute 1, and since $B$ is the center, the h-distance of the leg is $BC_h=\frac2{1-BC^2}=\frac2{1-\frac12}=4$.

Then we interpret the 2D grid with a 1D half-line, and all moves can be converted into moves on the line. Then we get a(n inefficient) construction of a 1D TM.

Logic circuit:

(e) $\sigma_2^2=Var(X_2)=Var(Y_1-Y_2)=$ $Var(Y_1)+Var(Y_2)=2$.

+ https://q.uiver.app/?q=WzAsNSxbMSwwLCJTXm4iXSxbMiwwLCJTXjEiXSxbMSwxLCJcXG1hdGhiYiBSUF5uIl0sWzIsMSwiU14xIl0sWzAsMCwiZih4KT0tZigteCkiXSxbMCwyLCJwXzIiLDJdLFsxLDMsInBfMiJdLFswLDEsImYiXSxbMiwzLCJoIiwyXV0=
  + Start from an open path $\phi$ from $x$ to $-x$ in $S^n$, so $f\phi$ is an open loop in $f(x)$ and $f(-x)$.
+ If lifting opens a loop in $S^1$, then it's nontrivial
  + This is a general result
+ Lemma: $\R P^n\to S^1$ must be trivial because $\Z_2\mapsto \Z$, and $S^n\to \R P^n$ is always a double cover

(c) $Cov(H,B)=-np_Hp_B=-1.8$.

Construct a right pentagon and its two diagonals with a point of intersection using the following named points:

(e) The goal is to make $\alpha\to 0.05$, so $1-F_X(k)\to 0.05$, so $F_X(k)\to 0.95$ for $X\sim Bin(30, \frac16)$. By the references given, $k=8$, and $\alpha=1-F_X(8)=1-0.949=0.051$.

   (d): `<e> -> <d> | <e> * <d> | <e> / <d>`. This is the only one because only one (instead of two) nonterminal is in each derivation step. Parse tree:

(m) $E(XY)=$ $\int_0^1\int^y_0 xy(3-3x)d(xy)=$ $\frac7{40}$.

+ $\frac12\ln3$
+ Horocycles: limit of equidistance h-lines
+ 3-D hyperbolic space
+ Hyperbolic plane: $AAA$ congruence
  + Lemma: defect is positive for nondegenerate ⛛ 

(b): $P(X=0)=0.7, P(X=1)=0.3$.

  + $$
    \Lambda(X)=\frac{\mu_0}{\mu_{MLE}}\\
    =e^{-\frac{n(\bar X-\mu_0)}{2\sigma^2}}\leq c
    $$

(b) Mean is simply by normal distribution results, $\mu$.

![image-20211118161048503](submission1.assets/image-20211118161048503.png)

(b) I'm for 30%

# Homework 8 Math 427

(b): $F(x)=\int_0^x f_X(y)dy=\frac35\int^x_0{(1+2y^2)dy}=\frac{2x^3+3x}5$. This is for $x\in[0,1]$, in case of $x<0$, $F(x)=0$, in case of $x>1$, $F(x)=1$.

## Problem 14.6 (a)

+ Operations
  + Initialization
  + Apply unitary operations
  + Measurement: collapse it to $0$ or $1$
  + Other operations can be simulated by these

Apart from that, by the definition of circles, $OX=OY=OX'=OY'$, so by AAS $\triangle OXY\cong \triangle OY'X'$ which implies $XX'=YY'$.

First we show that $\sum^n_{i=1}(X_i-\bar X)=$ $(\sum^n_{i=1}X_i)-n\bar X=0$. Since $\bar X=\frac1n\sum^n_{i=1}X_i$, we know $n\bar X=\sum^n_{i=1}X_i$, and hence the result. Then we apply the hint to the origin equation's left-hand-side:
$$
\begin{align*}
\sum^n_{i=1}(X_i-\mu)^2&=\sum^n_{i=1}(X_i-\bar X+\bar X-\mu)^2\\
&=\sum^n_{i=1}\left((X_i-\bar X)+(\bar X-\mu)\right)^2\\
&=\sum^n_{i=1}\left((X_i-\bar X)^2+(\bar X-\mu)^2+2(X_i-\bar X)(\bar X-\mu)\right)\\
&=\sum^n_{i=1}(X_i-\bar X)^2+\sum^n_{i=1}(\bar X-\mu)^2+2\sum^n_{i=1}(X_i-\bar X)(\bar X-\mu)\\
&=\sum^n_{i=1}(X_i-\bar X)^2+\sum^n_{i=1}(\bar X-\mu)^2\\
&=\fbox{$\sum^n_{i=1}(X_i-\bar X)^2+n(\bar X-\mu)^2$}
\end{align*}
$$

  + Proof: $t\in\mathbb I\mapsto \measuredangle QPX_t$, $\not=0, \not=\pi$

(a) So $p_H=0.6,p_B=0.3, p_M=0.1$, apply the multinomial PMF we get $P(H=7, B=3, M=0)=$ $\frac{(7+3+0)!}{7!3!0!}p_H^7p_B^3p_M^0=$ $\frac{10!}{7!3!}0.6^70.3^3=$ $0.091$

$B$ is $\langle M',w\rangle\in H$.

$$
P(x\mid M_0)=\frac{\exp{(-(x-15)^2/8)}}{2\sqrt{2\pi}}
$$

Mark the center of the circle as $O$, and by isosceles property $\measuredangle OAX\equiv-\measuredangle OXA$ and $\measuredangle BAC\equiv\measuredangle ACB$, and also $\measuredangle OAX+\measuredangle AXO+\measuredangle XOA\equiv\pi$, $\measuredangle XAC+\measuredangle ACX+\measuredangle CXA\equiv\pi$, and also $\measuredangle CXA+\measuredangle AXO\equiv\frac\pi2$. So, by some equational substitution, $\measuredangle XOA+\measuredangle OAX+\measuredangle XAC+\measuredangle BAC\equiv \frac{3\pi}2$, and simplifying to $\measuredangle XOA+\measuredangle OAX+\measuredangle XAC +\measuredangle AXO+\measuredangle XAC\equiv \frac{3\pi}2$, so $\pi+2\measuredangle XAC\equiv\frac{3\pi}2$, so $\measuredangle XAC\equiv \pm\frac{\pi}4$.

  + $\ket0$ or $\ket+$
  + Method 1: measure in $\{\ket0,\ket1\}$, report in the obvious way
  + Method 2: measure in $\{\ket\psi, \ket{\psi'}\}$ (where they're orthogonal)![image-20210827144143073](C:\Users\lenovo\AppData\Roaming\Typora\typora-user-images\image-20210827144143073.png)
  + Only for orthogonal states can we distinguish 'em perfectly. For other cases, we may fail to distinguish 'em.
  + These measurements are gonna be in the exams

+ Review
  + Boundary, interior, closure, neighborhood
  + Weaker (less open sets), stronger (more) topologies
+ Continuous bijection that are not isomorphism: like $[0, 1)\cup \{2\}\mapsto [0,1]$
+ Isomorphism on top spaces is a homeomorphism
+ $(0,1)\lrarr \R$: $x\mapsto (\arctan x+\frac\pi2)/\pi$
+ Open disk to E. plane
+ Open map: preserves open sets
+ Closed map: preserves closed sets
+ Bijective maps on top spaces are closed iff they're open

(b) This is exponential distribution, $Y\sim \textrm{Expo}(\frac12)$.

(c) So $\alpha=P(X\geq10\mid H_0)=1-P(X<10\mid H_0)$, and $H_0$ tells us $\theta=\frac16$. So $\alpha=1-F_{X}(9)$ for $X\sim Bin(30,\frac16)$.

endmodule
```

  always@(*)
    begin
      case(input_Num)
        4'b0000:begin
          display_Out <= 7'b0111111;//0
        end
        4'b0001:begin
          display_Out <= 7'b0000110;//1
        end
        4'b0010:begin
          display_Out <= 7'h5B;//2
        end
        4'b0011:begin
          display_Out <= 7'h4F;//3
        end
        4'b0100:begin
          display_Out <= 7'h66;//4
        end
        4'b0101:begin
          display_Out <= 7'b1101101;//5
        end
        4'b0110:begin
          display_Out <= 7'b1111101;//6
        end
        4'b0111:begin
          display_Out <= 7'b0000111;//7
        end
      endcase
    end
endmodule
```

# 5.4

  + $\Lambda(X)=\frac{L(\mu_0,\sigma^2_{0,MLE})}{L(\mu,\sigma^2_{MLE})}=\frac{\sum(X_i-\mu_0)^2}{\sum(X_i-\bar X)^2}^{-n/2}$

Driven

### 19.14 (a, b)

  | CD\AB | 00   | 01   | 11   | 10   |
  | ----- | ---- | ---- | ---- | ---- |
  | 00    | 0    | 0    | 0    | 0    |
  | 01    | 0    | 1    | 1    | 0    |
  | 11    | 0    | 0    | 0    | 1    |
  | 10    | 1    | 1    | 0    | 1    |

(g) $E(Y=y)=$ $\int^1_0\int^y_0 y(3-3x)d(xy)=$ $\frac58$.

SOP: $XZ+W\overline Z$

Consider string $1^{p+k}$ for any $k$ as long as $p+k=r^2$ for $r\in\N$, so that $1^{p+k}\in L$. For any choice of $y=1^t$ (this implies $1\leq t\leq p+k$, equivalently $1 \le t\le r^2$), so that $xy^iz=1^{p+k+(i-1)t}=1^{r^2+(i-1)t}$, let $f(i)=r^2+(i-1)t$, so pick any $i$ that makes $f(i)$ not a perfect square will do the job.

+ $\implies$: Depending on whether $Y\in[BX]$, $BX=BY\pm XY=AY\pm XY$. Since $AX<BX$ and $AX+XY>AY$ (so $AX>AY-XY$), we know $BX>AY-XY$, so $BX=AY+XY$, so $Y\in[BX]$, so $\measuredangle OYX+\measuredangle OYB\equiv\pi$. Also $\measuredangle OYA=\measuredangle OYB$ due to the congruence, thus $\measuredangle OYX+\measuredangle OYA\equiv\pi$, so they have the same sign, so by lemma 3.8 $A,X$ are on the same side of $\ell$ which is $(YO)$.
+ $\impliedby$: By corollary 3.10 (b), $Y\in[BX]$, so $BX=BY+XY=AY+XY>AX$.

If: consider $B\sub Y$ open, then either $B\in \mathscr B$ or $B$ is a union of sets in $B$. For the former case, $f^{-1}(B)$ is already said to be open. For the latter case, take these sets in $B$ and take all of their inverses against $f$ (which are all open), the union of these sets is open in $X$ because $X$ is a space. So $f$ is continuous.

  + $S^2=\frac1{n-1}\sum(X_i-\bar X)^2$

4. My guess of the value is $(-1)^n (n+1)^2$.
   By induction on $n$,
   + Base case: $n=0$, the result is $1\times 1=1$, verified.
   + Induction step: $n>0$, suppose the sum for $n-1$ is $(-1)^{n-1} n^2=-(-1)^n n^2$ (induction hypothesis), then the sum for $n$ is $-(-1)^n n^2+(-1)^n(2n(n+1)+1)$ $=(-1)^n(2n^2+2n+1-n^2)$ $=(-1)^n(n^2+2n+1)=(-1)^n(n+1)^2$, verified.
   
5. $\{\{q_0, q_1, q_2, q_3\}, \{0,1,2,3\}, \delta, q_0, \{q_1\}\}$ where $\delta$ is defined as:
   | |0|1|2|3|
   |-|-|-|-|-|
   |$q_0$|$q_0$|$q_1$|$q_2$|$q_3$|
   |$q_1$|$q_1$|$q_2$|$q_3$|$q_0$|
   |$q_2$|$q_2$|$q_3$|$q_0$|$q_1$|
   |$q_3$|$q_3$|$q_0$|$q_1$|$q_2$|

Lemma. $Q'\in[P,Q),Q'\not=P,X\notin(P,Q)$, $\ang PQX$ and $\ang PQ'X$ have the same sign.

Look at my ✨beautiful✨ mspaint drawing!!

When $X=1,Y=1$:

$$
\begin{align*}
&\quad~\textrm{defect}(\triangle ABC)\\
&=\pi-|\measuredangle ABC|-|\measuredangle BCA|-|\measuredangle CAB|\\
&=2\pi-|\measuredangle ABC|-|\measuredangle BCA|-|\measuredangle CAB|-\pi\\
&=2\pi-|\measuredangle ABC|-(|\measuredangle BCD|+|\measuredangle ACD|)\\
 &\quad~-|\measuredangle CAB|-(|\measuredangle ADC|+|\measuredangle BDC|)\\
&=(\pi-|\measuredangle ABC|-|\measuredangle BCD|-|\measuredangle BDC|)\\
&\quad~+(\pi-|\measuredangle ACD|-|\measuredangle ADC|-|\measuredangle CAB|)\\
&=\textrm{defect}(\triangle BCD)+\textrm{defect}(\triangle ACD)
\end{align*}
$$

(a) By LLN, the experiment's successful rate ($\frac1n\sum^n_{j=1} I_j$) converges to $\theta$, while $\theta=\frac{\int^b_a f(x)dx}{c(b-a)}$, so the desired area equals $\theta c(b-a)$, substitute $\theta$ results in $c(b-a)\frac1n\sum^n_{j=1} I_j$.

Expected:

+ $\forall P,\ell.\exists! m. m//\ell \and P\in m$. Uniqueness.
+ Reflection across a point is a direct motion (direct: preserve the sign, indirect: invert the sign)

+ SAS, ASA, SSS
+ AAS (not now)
+ Right angle $|\measuredangle|=\frac\pi2$, acute angle $|\measuredangle|<\frac\pi2$, obtuse angle $|\measuredangle|>\frac\pi2$
+ $P$ lies in perpendicular bisector to $[AB] \iff PA=PB$
+ $\forall \ell$ a line, $\exist!m$ a line through a fixed point $P$ s.t. $m\perp \ell$

So, $AE=CF$.

  + Reject $H_0$ if $\Lambda(X)\leq c$

# HW 7

## Problem 15.16 (c)

(a) So it's $E(X^k)$ where $X=e^Y$, so it's $E(e^{kY})$, which is simply the MGF of $Y$, which is $\exp(\mu k+\frac12 \sigma^2k^2)$.

By def. of MGF, it's $E(e^{sX})=$ $\sum_{x=r}^\infty{x-1\choose r-1}p^r(1-p)^{x-r}e^{sx}=$ $(pe^s)^r\sum_{x=r}^\infty{x-1\choose r-1}((1-p)e^s)^{x-r}=$ $\frac{(pe^s)^r}{(1-(1-p)e^s)^r}=$ $(\frac{pe^s}{1-(1-p)e^s})^r$.

When $X=0,Y=1$:

## 10.3

### 1.7

## Problem 5.3 (d)

Applying $U$ to the 1st qubit is applying $U\otimes I$ to the entangled qubit:
$$
(U\otimes I)\ket{\psi}=\begin{bmatrix} a & 0 & b & 0 \\ 0 & a & 0 & b \\ c & 0 & d & 0 \\ 0 & c & 0 & d \end{bmatrix}\begin{bmatrix} \frac1{\sqrt 2} \\ 0 \\ 0 \\ \frac1{\sqrt 2} \end{bmatrix}=\frac1{\sqrt 2}\begin{bmatrix} a \\ b \\ c \\d \end{bmatrix}
$$
Applying $U^T$ to the 2st qubit is applying $I\otimes U^T$ to the entangled qubit:
$$
(I\otimes U^T)\ket{\psi}=\begin{bmatrix} a & c & 0 & 0 \\ b & d & 0 & 0 \\ 0 & 0 & a & c \\ 0 & 0 & b & d \end{bmatrix}\begin{bmatrix} \frac1{\sqrt 2} \\ 0 \\ 0 \\ \frac1{\sqrt 2} \end{bmatrix}=\frac1{\sqrt 2}\begin{bmatrix} a \\ b \\ c \\d \end{bmatrix}
$$
The results are the same. $\blacksquare$

(d) $\mu_2=E(Y_1-Y_2)=0$.

+ Absolute value (defined as $x$ and $-x$ for positive and negative values)
  + $|x|=0 \iff x=0$
  + $|ab|=|a|\cdot|b|$
  + $|a+b|\leq|a|+|b|$
  + $-|x|\leq x \leq |x|$
+ Supremum and maximum and upper bound, infimum and minimum and lower bound
  + In the subset $\to$ maximum
  + Not in the subset, but smallest $\to$ supremum
  + Not in the subset, not necessarily smallest $\to$ upper bound 
+ Axioma de Completude
  + Bounded sets have supremum

(c) The Bayes factor $B$ is $\frac{P(x\mid M_0)}{P(x\mid M_1)}$.

Observe our goal:

(a): $var(X)=3=\frac{(3a-a)^2}{12}$ so $2a=6$ so $a=3$.

(c) By invariance property of MLE, $\log\theta=\log{\hat\theta}$, so by asymptotic distribution we need to compute $I(\log{\hat\theta})$. For that there's a lemma from [calculator](https://www.wolframalpha.com/input?i2d=true&i=D%5Blog+%5C%2840%29L%5C%2840%29%CE%B8%5C%2841%29%5C%2841%29%2Clog+%CE%B8%5D): $\frac{\part{\log{L(\theta)}}}{\part \log \theta}=0$, so:
$$
\begin{align*}
I(\log{\hat\theta})&=-E\left(\frac{\part^2\log{L(\theta)}}{\part^2(\log \theta)^2}\right)\\
&=-E\left(0+\sum^n_{i=1}\frac{X_i^2}{2a_i}\times \frac{\part e^{-\log\theta}}{\part \log\theta}\right)\\
&=-E\left(-e^{-\log\theta}\sum^n_{i=1}\frac{X_i^2}{2a_i}\right)\\
&=-E\left(-\frac1\theta\sum^n_{i=1}\frac{X_i^2}{2a_i}\right)=\frac1{2\theta}E\left(\sum^n_{i=1}\frac{X_i^2}{a_i}\right)\\
&=\frac1{2\theta}\left(n\theta\right)=\frac n2\\
\end{align*}
$$
And since $\log{\hat\theta}\sim N\left(0, \frac1{I(\log(\theta))}\right)$, it's just $\fbox{$N(0, 2/n)$}$.

  + Product state

![image-20211028222641683](writeup.assets/image-20211028222641683.png)

### 19.10

Take $\triangle ABC$, so $[AY],[CX]$ are medians, so $\frac{BY}{BC}=\frac12,\frac{BX}{BA}=\frac12$, also $\ang ABC$ is shared, so by AA $\triangle BXY\sim \triangle BAC$, so $\measuredangle BYX\equiv\measuredangle BCA$, so $XY//AC$, and similarly (for $\triangle ADC$, repeat the same proof) $VW//AC$, so $XY//VW$, and similarly $XW//YV$, so $\unicode{x25B1} XYVW$.

  + Notation: $\ket0\ket0\equiv\ket{00}$

+ Conditions where Neutral plane is Euclidean
  + Exists many things, like $\triangle$ with arbitrarily large in-radius
  + Et cetera
+ h-V
+ Hyperbolic plane

Continuous function: $f:X \to Y$ satisfies $\forall \epsilon > 0, \exist \delta >0,$ such that $\forall A,B\in Y, d_X(A,B)<\delta \implies d_Y(f(A), f(B))<\epsilon$.

+ $v=0^n,y=0^m$ for arbitrary $n,m$. In this case we remove $v$ and $y$, then $i$ will be too small.
+ $v=1^n,y=1^m$ for arbitrary $n,m$. In this case we remove $v$ and $y$, then $j$ will be too large.
+ Either $v$ or $y$ consists of both $0$ and $1$. In this case we duplicate it and it will violate the syntax (there will be $0101$).
+ $v=0^n,y=1^m$. If $n=0$, then remove $y$ make $i$ too small. Otherwise we repeat $y$ many times to make $j$ very large.

+ Quadratic polynomials
  + Discriminant
+ Cauchy-Schwarz inequality
  + Norm: $\norm{\overline x}=\sqrt{\overline x\cdot\overline x}$
  + $\norm{\overline x+\overline y}\leq\norm{\overline x}+\norm{\overline y}$
  + $\cfrac{\overline x\cdot\overline y}{\norm{\overline x}\times \norm{\overline y}}$

## Problem 9.8 (d)

https://edaplayground.com/x/bCRP

(f) So $P(Y>1\mid Y>\frac12)=\frac{1-P(Y\leq1)}{1-P(Y\leq\frac12)}$ $=\frac{1-(1-e^{-1/2})}{1-(1-e^{-1/4})}=\frac{e^{-1/2}}{e^{-1/4}}=e^{-1/4}=0.78$.

## Problem 6.6 (c)

(d) So $f_Y(y)=\int^1_y f(x,y)dx=$ $-\ln{y}$, where $y\in[0,x]$.

Since $2\alpha\equiv 0$, $2\alpha+2k\pi=0$ for some $k\in\Z$, so $\alpha=-k\pi$. For all even number $k$, $\alpha\equiv 0$, while for all odd number $k$, $\alpha\equiv \pi$.

+ Superdense coding
  + Holevo's theorem (proof out of scope)

   ![image-20220121134849268](hw1.assets/image-20220121134849268.png)

  + $(\alpha\ket0+\beta\ket1)(\alpha'\ket0+\beta'\ket1)=$ $\alpha\alpha'\ket{00}+\alpha\beta'\ket{01}+\beta\alpha'\ket{10}...$

(b) $P(Y=0)=0$, so $E(Y)=\frac14\cdot1+\frac14\cdot3+\frac12\cdot2=2$

By the functoriality of $\pi_1$, $\pi_1(S^1\times Y)=\pi_1(S^1)\times \pi_1(Y)=$ $\Z\times \pi_1(Y)$. On the other hand, $\pi_1(\R P^2)=\Z_2$ and $\pi_1(S^2)=0$.

(c): $Z=1$ means she is either having a surgery or buying a coffee.

This is surjective (obviously) but $[0,1]$ has trivial fundamental group because it's contractible, while $[0,1]/\sim$ is just another way of defining $S^1$, which has an interesting fundamental group $\Z$.

(d) Expected value: $E(Y)=2$, variance: $\text{Var}(Y)=4$.

![image-20211111164214264](writeup.assets/image-20211111164214264.png)

+ From a group $G$ to a space
  + $\langle a,b,c \mid abcbcbabcba \rangle$ means the group generated with $a, b, c$ where $abcbcbabcba=e$.
  + Generators into loops, glue unit disks for identities
  + Collapse spanning tree to a point -- get same homo group
  + Subgroups of free group is also free
    + Prove topologically: construct covering
  + Groups of covering must be subgroups but subgroups may not be groups of covering
    + Counterexample: sequence of circles (getting smaller) with a common point

![image-20220425232703375](h9.assets/image-20220425232703375.png)

The constant map $S^1 \to D^2$, where $\pi_1(S^1)=\Z$ but $\pi_1(D^2)=$ the trivial group.

### Circuit design

(b) Mean $E(X)=r\frac{1-p}p=5\times\frac32=7.5$, variance $Var(X)=r\frac{1-p}{p^2}=7.5\div 0.4=18.75$, so standard deviation $SD(X)=\sqrt{Var(X)}\simeq 4.33$.

## Problem 4.5 (g)

   Note that `<e>` denotes empty strings.

  + Determine if $f(0)=f(1)$ (i.e., $f(0)\oplus f(1)$)

The goal is to show that $\forall \epsilon > 0.\exist \delta>0. d_\chi(A,A')<\delta$ and $d_\chi(B,B')<\delta$ $\implies|d_\chi(A,B)-d_\chi(A',B')|<\epsilon$. 

![image-20211111164243228](writeup.assets/image-20211111164243228.png)

+ Random variables and probability distribution
+ $x$'s value is randomly chosen on a sample space

The inverse of the given point in the absolute also lies on the circline that overlaps with the h-line, so we have three points (original, inverse, the ideal point) on the circline, which determines a circle uniquely.

(b) By independence, $\sigma_1^2=Var(X_1)=Var(Y_1+Y_2)=$ $Var(Y_1)+Var(Y_2)=$ $1+1=2$.

Only if: $A$ closed $\implies$ $A$ complement is open $\implies$ $f^{-1}(A)$ complement is open $\implies$ $f^{-1}(A)$ closed.

Yes, just take the isosceles right h-triangle in Problem 1, make its legs $\frac14$ of its original length and construct its circumcircle (evidently exists), which is smaller than a horocycle (so it's indeed a circle).

+ $Q_2=\overline{Q_2'}$

+ Continuous function: $f:\R \to \R$ with the obvious properties ($\epsilon, \delta$ one)
  + Generalize to metric spaces
  + $f:X\to Y$ where $X, Y$ are metric spaces
  + Example: generalized open ball $B(x,R)=$ the obvious thing (closed ball: $\bar B$)
  + $B(x,R)=\{y\in X\mid d_X(x,y)<R\}$
+ $\ell_p(A,B)=\sqrt[p]{|x_A-x_B|^p+|y_A-y_B|^p}, p\in[1,+\infty)$
+ ^ produce equivalent sets of continuous functions, so people wanna study metrices where they produce different sets of continuous functions
  + This motivates the open sets definition (they're like open balls)
+ $V\subset X$ open $\iff \forall x\in V, \exists \epsilon >0, B(x,\epsilon)\subset V$
  + Infinite unions, finite intersections
  + Continuous functions: preserve open sets (preimage of open sets are open)
+ Lemma: open sets are finite unions of smaller open sets

Connect $BE$, $AC$ at $D$. Due to right pentagon, $AD=BD$, $BC=CD=AB$. By SAS, $\triangle ABD\simeq \triangle ACB$, so $AC\cdot AD=AB^2$, while $AD=AC-CD=AC-AB$, so $AC(AC-AB)=AB^2$, so $AC^2-AC\cdot AB-AB^2=0$, and it's a quadratic equation with solution $AC=(\frac{1\pm\sqrt5}2)AB$, and we take the positive solution, hence the result $\frac{AC}{AB}=\frac{1+\sqrt5}2$.

(a) So $\int^\infty_0 f(y)dy=c\int^\infty_0 e^{-y/2} dy=1$, so $-2c (e^{-y/2}\mid^\infty_0)=-2c(0-1)=1$, so $2c=1$, so $c=\frac{1}{2}$.

Suppose $B$ is the center of the absolute, and let $BA,BC$ intersect the absolute (in a Euclidean way) with $A',C'$, suppose $\triangle_h ABC$ is inscribed in a horocycle. From a Euclidean perspective, since $B$ is the center of the absolute, $BA_h,BA$ overlap and $BC_h,BC$ overlap, so $\measuredangle ABC=\frac\pi2$ so $AC$ is the diameter of the Euclidean version of the horocycle.

5. ```
   <email>   -> <letter><name>@<domain><postfix>
   <domain>  -> <name>.<domain> | <name>.
   <name>    -> <char><name> | <name>
   <char>    -> <digit> | <letter>
   <letter>  -> a | b | c | d | e | f | g | h | i | j | k | l | m | n | o | p | q | r | s | t | u | v | w | x | y | z | A | B | C | D | E | F | G | H | I | J | K | L | M | N | O | P | Q | R | S | T | U | V | W | X | Y | Z
   <digit>   -> 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9
   <postfix> -> com | org | gov | net
   ```

# 1

# 2

(a) It is a good choice because $(X\mid H_0)\sim Bin(n,\frac16)$, $(X\mid H_1)\sim Bin(n,\frac13)$. Choosing different hypotheses can cause the distribution of $X$ to change, so we expect the observation to be .

 (@psu.edu)

By MLE and the independence of $X_i$, $L(\theta)=\prod_{i=1}^n P(X_i\mid \theta)$, while $P(X_i \mid \theta)=\frac{e^{-\frac12(\frac{X_i-\mu}{\sigma})^2}}{\sigma\sqrt{2\pi}}$, so:
$$
\begin{align*}
L(\theta)&=\prod^n_{i=1}P(X_i\mid \theta)\\
&= \prod^n_{i=1}\frac{e^{-\frac12(\frac{X_i-\mu}{\sigma})^2}}{\sigma\sqrt{2\pi}}\\
&= \prod^n_{i=1} \frac{e^{-\frac12(\frac{X_i}{\sqrt{a_i \theta}})^2}}{\sqrt{a_i \theta}\sqrt{2\pi}}\\
&= \prod^n_{i=1}\frac{e^{-\frac{X_i^2}{2{a_i \theta}}}}{\sqrt{2a_i \theta\pi}}\\
&= \prod^n_{i=1}\left(e^{-\frac{X_i^2}{2{a_i \theta}}}\times (2\theta\pi)^{1/2}\times a_i^{1/2}\right)\\
&= \left(\prod^n_{i=1}e^{-\frac{X_i^2}{2{a_i \theta}}}\right)\times (2\theta\pi)^{n/2}\times \prod^n_{i=1}a_i^{1/2}\\
&= e^{-\sum^n_{i=1}\frac{X_i^2}{2{a_i \theta}}}\times (2\theta\pi)^{n/2}\times \prod^n_{i=1}a_i^{1/2}
\end{align*}
$$
So $L(\theta)=e^{-\sum^n_{i=1}\frac{X_i^2}{2{a_i \theta}}}\times (2\theta\pi)^{n/2}\times \prod^n_{i=1}a_i^{1/2}$. Then, we take $\ln$ on both side0s, and after that we take the derivative of $\ell$:
$$
\begin{align*}
\ell(\theta)&=-\sum^n_{i=1}\frac{X_i^2}{2{a_i \theta}}+ \ln((2\theta\pi)^{n/2})+ \ln\left(\prod^n_{i=1}a_i^{1/2}\right)\\
&=-\frac{1}{\theta}\sum^n_{i=1}\frac{X_i^2}{2a_i}+ \ln((2\pi)^{n/2})+\ln(\theta^{n/2})+ \ln\left(\prod^n_{i=1}a_i^{1/2}\right)\\
\ell'(\theta)&=-(-\theta^{-2})\sum^n_{i=1}\frac{X_i^2}{2a_i}-\frac n{2\theta}
\end{align*}
$$
And it is known that $\ell'(\theta)\equiv 0$, so:
$$
\begin{align*}
\frac1{\theta^{2}}\sum^n_{i=1}\frac{X_i^2}{2a_i}&=\frac n{2\theta}\\
\sum^n_{i=1}\frac{X_i^2}{2a_i}&=\frac {n\theta}2\\
\hat\theta&=\frac2n\sum^n_{i=1}\frac{X_i^2}{2a_i}\\
\hat\theta&=\fbox{$\frac1n\sum^n_{i=1}\frac{X_i^2}{a_i}$}
\end{align*}
$$

## Problem 9.8 (e)

```verilog
// -----------------------------------------------
// A state machine in Verilog
// -----------------------------------------------

By the definition of subspace topology and closure, $Cl_Y(A)$ is the intersection of all closed sets in $Y$ containing $A$, while $Cl_X(A)$ is the intersection of closed sets in $X$ containing $A$. Since intersection is the subset of both sides, and closed sets in $Y$ are intersections of $Y$ and closed sets in $X$, everything in $Cl_Y(A)$ are in $Cl_X(A)$, so $Cl_Y(A)\subseteq Cl_X(A)$.

+ (a) The circuit looks like

![image-20210909132248348](hw1.assets/image-20210909132248348.png)
$$
(I\otimes H)~\text{CNOT}~(I\otimes H)=\frac12
\begin{bmatrix}1&1&0&0\\1&-1&0&0\\0&0&1&1\\0&0&1&-1\end{bmatrix}
\begin{bmatrix}1&0&0&0\\0&1&0&0\\0&0&0&1\\0&0&1&0\end{bmatrix}
\begin{bmatrix}1&1&0&0\\1&-1&0&0\\0&0&1&1\\0&0&1&-1\end{bmatrix}\\=\frac12
\begin{bmatrix}1&1&0&0\\1&-1&0&0\\0&0&1&1\\0&0&-1&1\end{bmatrix}
\begin{bmatrix}1&1&0&0\\1&-1&0&0\\0&0&1&1\\0&0&1&-1\end{bmatrix}=
\begin{bmatrix}1&0&0&0\\0&1&0&0\\0&0&1&0\\0&0&0&-1\end{bmatrix}
$$

+ Example 9
  + $c'$: 

* Cover: a collection of open sets whose union is the carrier.

# Homework 9

(b): $k+1$.

We will prove (b). Assume $U=\begin{bmatrix} a & b \\ c & d \end{bmatrix}$.

$\implies$: So we have: $X$ connected and $Y$ discrete  where $|Y|\geq 2$ and $f:X\to Y$ any continuous function. Suppose there are more than one points in $Y$ satisfy that for the point $y\in Y$, $f^{-1}(y)\ne\empty$. Suppose one of these points is $y'$ and all the others are $y_i$ for $i\in I$. Then $\bigcup_{i\in I}f^{-1}(y_i)\sub X$ is an open set and its complement $f^{-1}(y')$ is also open, contradicting the fact that $X$ is connected.

+ a. I would say a Mealy machine, since the input affects the state change.
+ b. <img src="hw8.assets/image-20211118191522875.png" alt="image-20211118191522875" style="zoom: 67%;" />

+ Superdense coding: so Alice wanna message Bob. Bob create the state $\ket{00}+\ket{11}$ and send the first to Alice. Alice has two bits of information, and apply $X$ or $Z$ to the received qubit, and send it back to Bob.

## 3.7 (a)

$3_{10}\times 6_{10}=11_2\times 110_2=1100_2+110_2=10010_2=18_{10}$

+ "Inversion lines"
+ "Inversion parallelogram"
  + $\ang DAB+\ang BCD\equiv -(\ang C'B'A' +\ang A'D'C')$

By 11.10, $AB\leq CD$ and $CD\leq AB$. Thus $AB=CD$.

Only-if: consider $B\in \mathscr B$, it is open in $Y$ by definition of base, so $f^{-1}(B)$ is open as $f$ is continuous.

+ $\overline{A\cup B}$ is the intersection of all closed sets containing $A\cup B$.
+ $\overline A \cup \overline B$ is the union of the intersection of all closed sets containing $A$ and the intersection of all closed sets containing $B$.

If: $f^{-1}(A)$ closed $\implies$ $f^{-1}(A)$ complement is open $\implies$ $A$ complement is open $\implies$ $A$ closed.

+ Perp. circle: tangent lines at the two points of intersection are perpendicular
+ $\forall \Gamma\not=\Omega,$ say inversion of $\Gamma$ over $\Omega$ is $\Gamma'$, so $\Gamma=\Gamma'\iff \Gamma\perp\Omega$
+ Two arcs' tangent angle is preserved after inversion


(j) So $P(X=x\mid Y=y)=$ $\frac{P(X=x,Y=y)}{P(Y=y)}=$ $\frac{f(x,y)}{f_Y(y)}=$ $\frac{3-3x}{3y-3y^2/2}=$ $\frac{2-2x}{2y-y^2}$.

Say $\Omega_1, \Omega_2$ intersect at $P$, so $O_1P$ is tangent to $\Omega_2$, i.e. $O_1P\perp PO_2$. Take the foot of $P$ on $O_1O_2$, $T$, so $TP$ is an altitude of the right triangle $\triangle O_1O_2P$, giving rise to the obvious triangle similarity $\triangle O_1PT\sim\triangle O_1O_2P$, so $O_1P^2=O_1T\cdot O_1O_2$. Similarly $O_2P^2=O_2T\cdot O_1O_2$, so both of the two inversions lie on $T$.

![image-20211028165957144](writeup.assets/image-20211028165957144.png)

(a) So we need to compute the upper bound of $P(X\geq 85)$ which is (by Markov's inequality) $\frac{E(X)}{85}$ where $E(X)=\frac{75}{85}=\frac{15}{17}\simeq 0.882$.

Hawaiian earrings -- no universal covering, so trivial subgroup has no universal covering

```
[2021-11-11 16:35:56 EST] xrun -Q -unbuffered '-timescale' '1ns/1ns' '-sysv' '-access' '+rw' design.sv testbench.sv  
TOOL:	xrun	20.09-s003: Started on Nov 11, 2021 at 16:35:57 EST
xrun: 20.09-s003: (c) Copyright 1995-2020 Cadence Design Systems, Inc.
	Top level design units:
		segment_test
xmelab: *W,DSEMEL: This SystemVerilog design will be simulated as per IEEE 1800-2009 SystemVerilog simulation semantics. Use -disable_sem2009 option for turning off SV 2009 simulation semantics.
Loading snapshot worklib.segment_test:sv .................... Done
xmsim: *W,DSEM2009: This SystemVerilog design is simulated as per IEEE 1800-2009 SystemVerilog simulation semantics. Use -disable_sem2009 option for turning off SV 2009 simulation semantics.
xcelium> source /xcelium20.09/tools/xcelium/files/xmsimrc
xcelium> run
================================
=== Initializing modules =======
================================
_______________
|     ---     |
|    |   |    |
|    |   |    |
|     ---     |
_______________
x=0;after reset
_______________
|     ---     |
|    |   |    |
|    |   |    |
|     ---     |
_______________
x=0;after reset
_______________
|        |    |
|        |    |
_______________
================================
x=1;after reset
_______________
|        |    |
|        |    |
_______________
toggle x for a clock
_______________
|     ---     |
|        |    |
|     ---     |
|    |        |
|     ---     |
_______________
toggle x for a clock
_______________
|     ---     |
|        |    |
|     ---     |
|        |    |
|     ---     |
_______________
toggle x for a clock
_______________
|    |   |    |
|     ---     |
|        |    |
_______________
toggle x for a clock
_______________
|     ---     |
|    |        |
|     ---     |
|        |    |
|     ---     |
_______________
toggle x for a clock
_______________
|     ---     |
|    |        |
|     ---     |
|    |   |    |
|     ---     |
_______________
toggle x for a clock
_______________
|     ---     |
|        |    |
|        |    |
_______________
toggle x for a clock
_______________
|        |    |
|        |    |
_______________
toggle x for a clock
_______________
|     ---     |
|        |    |
|     ---     |
|    |        |
|     ---     |
_______________
toggle x for a clock
_______________
|     ---     |
|        |    |
|     ---     |
|        |    |
|     ---     |
_______________
x=0;with reset=0
_______________
|    |   |    |
|     ---     |
|        |    |
_______________
x=0;with reset=0
_______________
|    |   |    |
|     ---     |
|        |    |
_______________
x=1;with reset=1
_______________
|     ---     |
|    |   |    |
|    |   |    |
|     ---     |
_______________
Simulation complete via $finish(1) at time 68 NS + 0
./testbench.sv:155       $finish;
xcelium> exit
TOOL:	xrun	20.09-s003: Exiting on Nov 11, 2021 at 16:35:58 EST  (total: 00:00:01)
Finding VCD file...
./dump.vcd
[2021-11-11 16:35:58 EST] Opening EPWave...
Done
```

First we show that $\R^2$ is a $\Z\times\Z$-set. The identity element of $\Z\times\Z$ is $(0,0)$, so the identity law and the associativity law hold by identity and associativity of real number addition.

Suppose $Y=S$ and has the same topology. Let $f$ be identity, then the inclusion $i$ is continuous. So open sets in the induced topology have their preimage open in $S$.


+ $\alpha\equiv\beta\mod{2\pi}$
  + Angle and angle measure
+ Some theory 'bout modulo
  + Cannot multiply by any real number: $\pi\equiv-\pi$ but $\frac\pi2\not\equiv-\frac\pi2$
+ Continuity of angle functions
  + Defined continuous function
+ Triangle: triple of distinct points (there may not be lines among 'em)
  + $\triangle ABC\cong \triangle A'B'C'\iff\exist$ a motion between 'em
  + Not true for all metric spaces, but true for Euclidean spaces (as well as Manhattan spaces)
+ Euclidean plan:
  + It's a metric space with at least two points
  + Unique line between two distinct points
  + $\forall \ang AOB.\exist \alpha\in(-\pi,\pi], \alpha=\ang AOB.$ s.t.
    + For any $\alpha'\in(-\pi,\pi]$ can we find such half-line $OA$
    + $\forall A,B,C\not=O.\ang AOB+\ang BOC\equiv \ang AOC$
    + $(A,B,O)\mapsto \ang AOB$ is continuous at any triple if $\ang AOB\not\equiv\pi$
  + $\triangle ABC\cong \triangle A'B'C'\iff AB=A'B',AC=A'C',\ang CAB\equiv \pm \ang C'A'B'$

# 3c

## 2.9 (d)

+ Digital design
+ Friday lectures is gonna be prerecorded, some Wednesday lectures will too
+ DEB-1002 for labs, design projects and HW.
  + Can do labs from home using DEB
+ Midterms * 2, final exam, HW/Labs/Quizzes, Design project. Each 20%.
+ Final exam adjustment is 2 weeks before
+ Lowest 2 scores dropped

![image-20211021223023013](hw6.assets/image-20211021223023013.png)

(c) $P(X_i=10\cup X_j=10)=P(X_i=10)+P(X_j=10)$ because $X_i$ and $X_j$ are independent. Thus the result is $\frac15$.

# 3 b

Two angle measures sum up to $\pi$ then they have the same sign.

## 5.9 (c)

(c) $X_1\sim N(0,2)$.

# 3 a

Closed under union: for $U_i\in\mathscr U$ where $i\in I$ and $I$ is any index set, $\bigcup_i(U_i+\{\infty\})=(\bigcup_i U_i)+\{\infty\}$, and $\bigcup_i U_i\in\mathscr U$, so $\mathscr U^\infty$ is closed under (infinite) union. For a similar proof we can deduce that $\mathscr U^\infty$ is closed under finite intersections (I think the book forgets to mention that the empty set should also belong to $\mathscr U^\infty$.

Given a nondegenerate triangle, if it maps it to a degenerate map, then the backward direction of this bijection will lead to a contradiction, so it has to map nondegenerate triangles to nondegenerate ones.

+ $\implies$: if $O\in(BC)$ then there's straight angle $\angle BOC$ (by theorem 2.8) and $\measuredangle AOB+\measuredangle AOC=\measuredangle BOC=\pi$, while otherwise $\measuredangle BOC=0$ and $\measuredangle AOB=\measuredangle AOC$ due to the half-line equivalence $[OB)=[OC)$. In the former case, $2\measuredangle AOB+2\measuredangle AOC=2\pi\equiv 0$ and in the latter case, $2\measuredangle AOB+2\measuredangle AOC=0\equiv 0$. $\blacksquare$

+ NP lemma: LRT is most powerful when we control $\alpha$, in case of one-sided it's UMP
  + Two-sided alternatives: no UMP
+ 5.4: reject $H_0$ when $\bar X>\mu_0+1.645\times S/\sqrt n$, where $1.645=qnorm(0.95)$
+ Asymptotic dist. of GLRT (Wilk's theorem): $-2\log{(\Lambda(X))}\sim \chi^2_p$ where $p=$ # of parameters in $\Omega$ minus the # in $\Omega_0$.
+ Suppose $X\sim N(\mu, \sigma^2)$ with unknown $\sigma^2$, and $H_0:\mu=\mu_0, H_1:\mu\ne \mu_0$, so $2-\log{(\Lambda(X))}\sim \chi^2_p$. $\Omega=\{(\mu, \sigma^2), \mu\in\R, \sigma^2\in \R^+\}$, so $2$. $\Omega_0$ fixes $\mu_0$, so $1$, so $p=2-1=1$.
+ Proof of Wilk's: $R:\{X:\frac{L(\theta_1)}{L(\theta_0)}>c\}$, and $L(\theta)=\prod_i f(X_i\mid \theta)$. Transform to $Q:=\left(f(X\mid \theta_1-cf(X\mid \theta_0))\right)I_{R_{LR}}$, where $R$ is rejection region, $LR$ is for LRT. Or multiply by $I_{R_{T}}$ where $T$ is for any test.
  + Indicator function: $I_S(x)$: $1$ if $x\in S$ and $0$ otherwise.
  + $E(I_S)=P(X\geq 1)$
  + Integrate $Q$: $E(I_{R_{LR}}\mid \theta_1)-cE(I_{R_{LR}}\mid \theta_0)$.
  + Show $\pi_{LR}-\pi_T\geq c(\alpha_{LR}-\alpha_T)$
+ Bayes factor: $B=\frac{P(X\mid M_i)}{P(X\mid M_j)}$, ratio of prior: $\frac{P(M_i)}{P(M_j)}$, multiplication: ratio of posterior

  + So like if we want $P(H_1\mid H_0)\leq \alpha$
  + Size of test: size-$\alpha$ test if TIER $=\alpha$
  + Example 11
    + $H_1:\mu>\mu_0$, $H_1:\mu=\mu_1$ for any $\mu_1>\mu_0$
    + The only thing we used about $\mu_1$ is $\mu_1>\mu_0$
    + $R=\{X:\bar X>c_t\}$
    + One-sided: rejection region is free from $\mu_1$
    + $P(\frac{\bar X-\mu_0}{\sigma/\sqrt n}>\frac{c-\mu_1}{\sigma/\sqrt n})=\alpha$ (??)
    + So $P(\bar X>c_t\mid H_0)=P(\frac{\bar X-\mu_0}{\sigma/\sqrt n}>\frac{c_t-\mu_0}{\sigma/\sqrt n}\mid H_0)=P(Z>\frac{c_t-\mu_0}{\sigma/\sqrt n})<\alpha$
    + So $\frac{\bar X-\mu_0}{\sigma/\sqrt n}>1.645$
    + Type II: $\beta=P(Z\leq \frac{\mu_0-\mu_1}{\sigma/\sqrt n}+1.645)=P(\mu_1)$
      + $=F(1.645+frac)$ ($F$: CDF of standard normal)
    + $\mu_1\uarr\implies \pi\uarr$
    + $H_0\implies$ $\alpha=F(1.645+\frac{\mu_0-\mu_1}{\sigma/\sqrt n})$
    + Uniformly most powerful test: $\forall \mu_1>\mu_0$, LRT is most powerful, $\alpha$

(i) Since $Y\leq1/2$ implies $X\leq 3/4$, so $P(Y\leq1/2\mid X\leq 3/4)=$ $\frac{P(Y\leq 1/2)}{P(X\leq 3/4)}=$ $\frac{\frac5{16}}{1-\frac1{64}}=$ $\frac{20}{63}$.

| Problem # | sign-magnitude | 1's complement | 2's complement |
| --------- | -------------- | -------------- | -------------- |
| a         | `01010101`     | `01010101`     | `01010101`     |
| b         | `10011101`     | `11100010`     | `11100011`     |
| c         | impossible     | impossible     | impossible     |

That gives the above picture of design, it's straightforward.

+ Euclidean space -- continued
  + $\forall [OA), \alpha\in(-\pi,\pi], \exist![OB).\measuredangle AOB=\alpha$
+ SAS triangle congruence
+ $\forall C'\in[AC), B'\in[AB). \exist k\in\R^*,AB'=k\cdot AB,AC'=k\cdot AC.$
  + $B'C'=k\cdot BC,\measuredangle ABC=\measuredangle AB'C',\measuredangle ACB=\measuredangle AC'B'$
+ Lemmata
  + $\measuredangle AOA=0$ (prove $\measuredangle AOA\equiv 0$ and use the interval)
  + Two lines have at most one unique point of intersection
  + $\measuredangle AOB=-\measuredangle BOA$
  + $\measuredangle AOB=\pi \iff O\in[AB]$
    + $\triangle AOB \cong \triangle BOA$
  + 平角 180$\degree$
    + 找一个新的点，构成平角的反面，然后证明这两个平角加起来是圆周（用三角形全等）
+ Angle a is vertical to angle b: they share the same point

+ (a) We observe in the standard basis, and if we get $0$, we guess it to be $0$, otherwise we guess it to be $\cos\theta\ket0+\sin\theta\ket1$. If the input is $0$ ($\frac12$ probability), then the observation must be $0$, and we'll be right ($\frac12$ chance of success in total). If the input is $\cos\theta\ket0+\sin\theta\ket1$ ($\frac12$ probability), we have $\sin^2\theta$ probability to get $1$ (in this case we're right), and we'll be wrong otherwise ($\cos^2\theta$ probability). So, we'll be right in a $\frac{1+\sin^2\theta}2$ probability, and $\frac{\cos^2\theta}2$ probability to get it wrong.
+ (b) TODO

0. $S^2$ is homotopy equivalent to the union of two disjointed $D^2$ with their boundaries (as $S^1$) glued together, where $D^2$ is simply connected and $S^1$ is path-connected.
1. $S^n$ is ... to two disjointed $D^n$ with their boundaries (as $S^{n-1}$) glued together, where $D^n$ is simply connected as well as $S^{n-1}$.

(f) $E(Y_1)=E(E(Y_1\mid Y_2))=E(\frac{Y_2}2)=\frac12\frac12=\frac14$.

+ b) ![image-20210930212715779](hw5.assets/image-20210930212715779.png)

   (b): $P(F \mid H_1)=\frac{P(F)P(H_1\mid F)}{P(H_1)}=\frac{\frac12\frac12}{\frac58}=\frac14\frac85=\frac25$.

(a) Both. For $O$ and $\Omega$, let $n_0=5$. For $O$, let $c=2$, for $\Omega$, let $c=\frac12$.

(d) Since $c$ makes $P(T<c\mid H_0)=\alpha=0.05$, and $H_0$ makes $\mu_1=\mu_2$, so it's $P\left(\frac{\bar X-\bar Y}{\sqrt{\frac{\sigma_1^2}n+\frac{\sigma_2^2}m}}<c\right)=0.05$, so  $c=-1.96$.

* Center the random variable, the average of the square is variance (??)
  * The variability of the dist.
* Standard deviation
* Properties of variance 方差:
  * $var(X)=E[(X-E(X))^2]$ (??)
  * $var(ax+b)=a^2\cdot var(x)$
    * $var(ax+b)=E([ax+b-E(ax+b)]^2)=$
    * $E([ax+b-aE(x)-b^2]^2)=E[a^2(x-E(x))^2]$
  * $SD(ax+b)=|a|SD(x)$
* Mean: weighted average of values
  * $E(x)=\sum_x P(X=x)x$
  * $var(x)=E(x^2)-[E(x)]^2$
  * $SD(x)=\sqrt{var(x)}$
  * Linearity property: $E(f(x))=f(E(x))$ **given $f$ linear**.
    * So, $E(X^2)\neq E(X)^2$
* $E(x)=np$ ($n$ trial with prob. $p$, i.e. $Bin(n, p)\sim X$)

### 1.13

(b) Since $X\sim N(\mu_1,\sigma_1^2)$ and $Y\sim N(\mu_2,\sigma_2^2)$, so $\bar X\sim N(\mu_1,\frac{\sigma_1^2}n)$ and $\bar Y\sim N(\mu_2,\frac{\sigma_2^2}m)$. Thus $(\bar X-\bar Y)\sim N(\mu_1-\mu_2,\frac{\sigma_1^2}n+\frac{\sigma_2^2}m)$, and it can be simplified to $T:=\frac{(\bar X-\bar Y)-(\mu_1-\mu_2)}{\sqrt{\frac{\sigma_1^2}n+\frac{\sigma_2^2}m}}\sim N(0,1)$.

## 2.8 (b)

  + $\alpha=P(\Lambda(X)\leq c\mid H_0)$, $H_0=\theta\in\Omega_0$

+ Internal group of `Top`
+ $SO(3)$ -- 3D rotation group, $\pi_1(SO(3))=\Z_2$. The rotation is not commutative, but the fundamental group is!
+ Fundamental group of Klein bottle is a subgroup of fundamental group of Torus
+ $(f*h)(t)=\{f(t/2)~(t\in[0,1/2]), h(1+t/2)~(t\in[1/2,1])\}$, $(f\cdot h)(t)=f(t)h(t)$.
  + Construction: $g(t,a)=f(t/a)h(t)~(t\in[0,a]), f(1)h(t)~(t\in[a,1])$
  + 

+ Not meant to be simple
+ 5.3 (b): use "quotient topology" condition: inverse image of an open set is open
+ $\R/\Z\simeq S^1, \R\not\simeq S^1$
+ $\Z_2/\Z_2\simeq \Z_2/\Z_2/\Z_2$
+ Basis. Product topology can be defined in terms of it.

+ Induced topology: generated by taking union of a certain subset $A\subset X$ and all open sets of $X$.
  + Well-definedness: evident
+ $f:X\to Y$ where $Y$ is a space. Induce a topology on $X$ by constructing the weakest topology that makes $f$ continuous.

(a) Known facts: PDF of $X$: $f(x)=1$ for $x\in[0,1]$, and conditional PDF of $Y$: $f_{Y\mid X}(y\mid x)=\frac1x$ for $y\in[0,x]$, so $f(x,y)=$ $f_X(x)f_{Y\mid X}(y\mid x)=$ $\frac1x$ for $0\leq y\leq x\leq 1$.

## Problem 7.5 (a)

+ Hypergeometric distribution

For any $x, y\in X$ where $X$ is a space with concrete topology, then the only open set containing $x, y$ is $X$, so take $f:[0,1]\to X$ such that $f(0)=x$ and for all other input $i$, $f(i)=y$. It is evidently continuous (there's only one open set to lift), so $x$ and $y$ are path connected.

Suppose the center of $\Gamma$ is $O$. By def. of inversion, $P,P',O$ are on the same line. Since $X\in\Gamma$, the inverse of $X$ is itself, so by lemma 10.2 $\triangle OP'X\sim\triangle OXP$, so $\frac{PX}{P'X}=\frac{OP}{OX}$ which is a fixed value.

+ 可选课题
  + 四元数