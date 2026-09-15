# Research lane 06: global strict log concavity of the reciprocal Xi density

Status: controller-developed analytic proof with an executed directed-arithmetic certificate, subject to the stated published zero-data inputs. Machine-assisted research; not independent proof certification. No novelty or RH claim.

Exact parent: [the compact-gap reduction for reciprocal Xi log concavity](https://flywheel.paradigma.inc/node/326d0d8a-69d3-49c4-b4d0-3dd2601c6cab). This branch supplies bounds and a finite certificate closing that particular compact gap. The [positive reciprocal Fourier law](https://flywheel.paradigma.inc/node/ddd3eaa1-2995-4544-8748-debd25b87249) supplies positivity, normalization and regularity.

Set
    F(z)=Xi(z/2)/4,  L(u)=F(iu)=xi((1+u)/2)/4,
    phi(u)=F(0)/L(u),
    Lambda(x)=(1/(2pi)) integral_R phi(u) exp(-ixu) du.

The conclusion is
    Lambda'(x)^2-Lambda(x)Lambda''(x)>0  for every real x.       (1)

In particular Lambda is a strictly log-concave, even, positive probability density, and its translation kernel has strictly positive minors of orders one and two on strictly increasing nodes. This is PF2, not positivity at all orders. Schoenberg's RH equivalence concerns PF-infinity and is not established here.

## 1. A strip bound independent of any unknown zero location

Write the standard positive theta kernel as
    P(t)=exp(t) sum_(n>=1) (2v_n^2-3v_n) exp(-v_n),
    v_n=pi n^2 exp(4t), t>=0.
Then L(y)=2 integral_0^infinity P(t) cosh(yt)dt. All needed differentiations converge.

We first prove
    |L(y+iv)| >= L(y)/5  (y real, |v|<=1).                     (2)

For |y|<=3, positivity and cos(vt)>=1-v^2t^2/2 give
    Re L(y+iv)>=L(y)-L''(3)/2.
Since t^2 exp(-3t)<=4/(9e^2), cosh(3t)<=exp(3t) and exp(6t)<=2cosh(6t),
    L''(3)<=8L(6)/(9e^2).
The exact special-function formula gives
    L(6)=(35/32)pi^(-7/4) Gamma(7/4) zeta(7/2)<49/192.
Here Gamma(7/4)<=1 by log convexity between 1 and 2, zeta(7/2)<=7/5 by the integral test, and pi^(7/4)>6 because 3^7>6^4. Thus L''(3)/2<49/1728<.03.

For completeness, L(0)>1/10 can be proved without a decimal evaluation. Keeping only n=1 and integrating by parts after v=pi exp(4t) gives
    L(0)>=pi exp(-pi)-(1/(4pi^(1/4))) integral_pi^infinity v^(1/4)exp(-v)dv
         >=exp(-pi)[pi-1/4-1/(16pi)]>131/1152>1/10.
The middle inequality uses concavity of (1+x/pi)^(1/4). For the final one use 3<pi<22/7 and exp(22/7)<24. One elementary check of the latter is e<11/4 and
    exp(1/7)<=1+1/7+(1/98)/(1-1/21)=2261/1960<15/13;
then (11/4)^3(15/13)=19965/832<24.
Consequently Re L(y+iv)>.7L(y) in this compact range.

For y>=3 let s=sigma+i tau=(1+y+iv)/2, so sigma>=2 and |tau|<=1/2. The rational factor s(s-1) has modulus at least sigma(sigma-1). The Euler product gives
    |zeta(s)|/zeta(sigma)>=1/zeta(sigma)^2>=1/4.
For x=sigma/2>=1 and t=tau/2, the Gamma product yields
    |Gamma(x+it)|/Gamma(x)
      =product_(n>=0)(1+t^2/(x+n)^2)^(-1/2)
      >=exp(-t^2)>=exp(-1/16),
using sum_(n>=0)(x+n)^(-2)<=2. The modulus of the pi factor has the same value as on the real axis. Thus the ratio in (2) is at least exp(-1/16)/4>1/5. Evenness handles y<=-3.

In particular phi is holomorphic throughout this strip and
    |phi(y+iv)|<=5phi(y).                                    (3)

## 2. Real-axis tail bounds for phi

Put s=(1+u)/2. For u>=200, logarithmic differentiation gives
    L'/L=1/(2s)+1/(2(s-1))-(log pi)/4
          +psi(s/2)/4+(zeta'/zeta)(s)/2.
Gamma log convexity and its recurrence imply psi(x)>=log x-1/x. Also
    (zeta'/zeta)(s)>=zeta'(s)
      >=-[2^(1-s)+2^(2-s)/(s-2)]>-1/100
for s>=100. The integral test used here applies to sum_(n>=2)n^(1-s), which bounds sum log(n)n^(-s).
The correction from psi cancels 1/(2s). Since s/(2pi)>100/8>exp(9/4), we obtain
    L'(u)/L(u)>9/16-1/200>1/2  (u>=200).                      (4)
For example exp(9/4)<(11/4)^2(4/3)=121/12<100/8, using exp(1/4)<4/3. Therefore
    phi(u)<=phi(U) exp(-(u-U)/2)  (u>=U>=200).                 (5)

We also need a much coarser bound valid everywhere:
    phi(u)<=min(1,exp(64-|u|/2)).                             (6)
Indeed, on 1/2<=t<=3/5 the first theta atom has 12<v_1<64, hence P(t)>=144exp(-64). Integrating over this interval gives L(u)>=14.4exp(-64+|u|/2), whereas L(0)<=L(3)=pi/24<1. Positivity of cosh gives phi<=1.

## 3. Rigorous finite real-axis evaluations

The attached node generator uses 160-digit Decimal intervals, directed down/up for every algebraic operation. Integer powers use interval multiplication. The exp and log endpoints use correctly rounded values with one outward adjacent value. [Python's Decimal specification](https://docs.python.org/3/library/decimal.html) documents correctly rounded exp and log; no noninteger Decimal power operation is used.

Pi is enclosed by Machin's formula, with alternating arctangent series of 150 and 45 terms at 1/5 and 1/239. All rational constants and Bernoulli numbers are computed exactly.

For real s>0 and N>=1, set
    w_j=2^(-N) sum_(k=j+1)^N binomial(N,k),
    eta_N(s)=sum_(j=0)^(N-1)(-1)^j w_j (j+1)^(-s).
The exact polynomial identity, for 0<x<1, is
    sum_(j=0)^(N-1)(-1)^j w_j x^(j+1)
       =x/(1+x) [1-((1-x)/2)^N].                            (7)
To verify it, swap the two finite sums and use
sum_(j=0)^(k-1)(-x)^j=(1-(-x)^k)/(1+x), followed by the binomial theorem.
The Gamma integral then gives
    eta(s)-eta_N(s)
      =2^(-N)/Gamma(s) integral_0^infinity
          t^(s-1) exp(-t)(1-exp(-t))^N/(1+exp(-t))dt,
and consequently
    0<=eta(s)-eta_N(s)<=2^(-N).                              (8)
The integral formula for eta holds also when 0<s<=1: the finite geometric partial sums for its integrand are bounded in absolute value by 2exp(-t), so dominated convergence applies against t^(s-1). The finite interchanges in (7) require no convergence argument. No uniform complex-s remainder is claimed.

Use N=400 and the positive regularization
    xi(s)/4=s Gamma(s/2)pi^(-s/2)eta(s)
                     [(s-1)/(1-2^(1-s))]/8,                 (9)
where the bracket is 1/log 2 at s=1. Every factor in (9) is positive for real s>0. Formula (9) follows from eta(s)=(1-2^(1-s))zeta(s), with the removable limit at 1.

For Gamma, the script evaluates the logarithmic Stirling expansion with terms k=1,...,64 at the 160 residue classes x=100+r/160, 0<=r<160, and adds the interval from zero to the positive k=65 first omitted term. The positive-real remainder bound is stated in [DLMF 5.11(ii)](https://dlmf.nist.gov/5.11). Exact recurrences Gamma(x+1)=xGamma(x) then supply the grid x=(k+40)/160. Geometric interval recurrences supply the powers of pi, 2 and the integers in (9).

The result is an enclosure of phi(k/40), 0<=k<=24000. The maximum interval width is less than 2*10^(-120). In particular,
    phi(200)<10^(-42),  phi(340)<10^(-89).                    (10)
The report includes checks at L(1)=1/8 and L(3)=pi/24; those checks supplement, rather than replace, the enclosure proof. All node comparisons used by the certificate are checked by directed intervals.

## 4. A uniform Fourier approximation, including complex neighborhoods

Let h=1/40 and K=13600, so Kh=340. Let v_k be the rounded midpoint of the kth phi interval, and p the rounded midpoint of the pi interval. These midpoints are fixed rational numbers. Define the exact entire function
    A(x)=(h/p)[v_0/2+sum_(k=1)^K v_k cos(khx)].                (11)

For every center c in [0,3.175] and complex |x-c|<=.01,
    |Lambda(x)-A(x)|<10^(-85)=E.                             (12)

Here are the three error bounds. From (5) and (10),
    integral_R phi(u)exp(.01|u|)du<3601:
the part |u|<=200 is at most 400e^2<3600 and the two tails are less than one. By (3), the Fourier integrand on any line of imaginary height at most one has integral of its absolute value less than 5e^4*3601<1.5*10^6, since |Re x|<4. Its decay is uniform on this strip, by (5).
The real-line strip quadrature theorem, [Trefethen and Weideman, Theorem 5.1](https://people.maths.ox.ac.uk/trefethen/publication/PDF/2014_149.pdf), bounds the unnormalized trapezoidal error by 2M/(exp(2pi/h)-1). After division by 2pi our error is less than 10^6 exp(-240).

The omitted grid tail is bounded by
    (h/pi)sum_(k>K)phi(kh)exp(.01kh)
      <=phi(340)exp(3.4)/(pi*.49)<60phi(340).                 (13)
This uses exp(.49h)-1>=.49h and e^4<81.
Replacing the nodes and pi by their rounded midpoints costs less than 10^(-115). In detail, the node discrepancies are below 2*10^(-120), so their contribution is less than
    (.025/3)*13601*81*2*10^(-120)<2*10^(-116);
the pi-midpoint contribution is less than 10^(-150).
Thus the directed calculation verifies
    10^6 exp(-240)+60phi(340)+10^(-115)<E.

For the larger discs |x-c|<=1/4 we need only
    |A(x)|<exp(66)=M.                                      (14)
Indeed (6) bounds the geometric main sum by
    exp(64)*h/[3(1-exp(-h/4))]
       <=exp(64)*(4+h)/3<2exp(64).
The midpoint discrepancies contribute less than
(h/3)*13601*2*10^(-120)*exp(85), which is negligible compared with exp(64). This proves (14).

## 5. From analytic errors to an interval certificate for curvature

Take delta=1/200 and centers c_p=(2p+1)/200, 0<=p<=317. The corresponding closed intervals cover [0,3.18]. For each center use the variable z=(x-c_p)/delta and let P be the degree-64 Taylor polynomial of A(c_p+delta z).

Cauchy's bound from (14) gives Taylor coefficients at most M50^(-n). For n=65+k,
    n(n-1)<=66^2 binomial(k+2,2).
The same bound covers derivative orders zero and one. Hence the Taylor remainder and its first two derivatives with respect to z, on |z|<=1, are bounded by
    tau=M50^(-65)*66^2/(1-1/50)^3.
The error in (12) is analytic on |z|<=2. A Cauchy circle of radius 1/2 around each real |z|<=1 bounds its derivatives of orders zero, one and two by 8E. Therefore
    |D_z^j[Lambda(c_p+delta z)-P(z)]|<=e:=8E+tau
       (j=0,1,2; real |z|<=1).                              (15)

Let Q=P'^2-PP''=sum q_j z^j, and let N_j be an upper bound on the coefficient l1 norm of P^(j). Expanding with r=Lambda(c_p+delta z)-P gives
    Q(P+r)-Q(P)=2P'r'+(r')^2-Pr''-rP''-rr''.
Consequently the sufficient inequality checked on each whole panel is
    q_0-sum_(j>=1)|q_j|
          -e(2N_1+N_0+N_2)-2e^2>0.                        (16)
All quantities on the left are enclosed outward. The physical curvature is the normalized expression divided by delta^2. No derivative bound is inferred from real samples.

## 6. Rounding audit for the Taylor coefficients

The coefficient calculation uses midpoint arithmetic only where covered by a uniform explicit enclosure. Each exact coefficient of P is enclosed by its computed value plus/minus 10^(-125). Subsequent polynomial multiplication, differentiation, absolute sums, norms and margins are all directed.

Here is a deliberately conservative rounding bound. The exact coefficients in (11) have weights
    w_(0,k)=(h/p)v_k, with k=0 halved,
    w_(j,k)=w_(j-1,k)(delta kh)/j.
Their trigonometric factor is cos(khc) or sin(khc) with the appropriate alternating sign. The script verifies every computed weight has absolute value below 1000; the factors delta kh are exact decimals in [0,1.7]. Every weight intermediate has magnitude below 10^6. At precision 160, the absolute local rounding error of each such elementary operation is below 10^(-153). Taking three such errors at initialization and two thereafter, the weight error obeys
    epsilon_j<=2epsilon_(j-1)+2*10^(-153),
and is below 10^(-132) through j=64.

For the initial rotation angle hc, 0<=hc<.08. Directed sine and cosine Taylor series through degrees 121 and 120, enlarged by 1/121!, give widths below 10^(-150). Their rounded midpoint errors are below 2*10^(-150). The computed sine/cosine recurrence is checked to stay componentwise below 2 in absolute value for all 13601 steps. Comparing it with the exact orthogonal rotation, each step increases its Euclidean error by less than 2*10^(-149), including local arithmetic rounding. Thus each trigonometric component error stays below 10^(-144).

Each coefficient sum has 13601 products, with product magnitude below 2000 and partial sums below 3*10^7. The rounding error per addition is below 10^(-151). The accumulated coefficient error is therefore less than
    13601[2*10^(-132)+1000*10^(-144)+2*10^(-151)]
      <10^(-125).                                         (17)
The midpoint numbers in (11) themselves define A exactly; their discrepancy from phi was already covered in (12). The estimate does not assume that a nearest-rounded sum is an upper bound. Norms in (16) are accumulated with upward rounding and endpoint absolute values use exact sign changes.

## 7. Closing the two tails

The parent proves the following analytic reduction. Let a<b<c be the first three positive zeros of F, simple and real, and remove the first two factors. Its remaining reciprocal factor is the characteristic function of an even probability measure mu. For any b<R<c,
    integral exp(R|y|)mu(dy)
      <=M_R:=2F(0)(1-R^2/a^2)(1-R^2/b^2)/F(R).              (18)
This is a genuine exponential-moment bound derived by positive Levy truncations, not a conclusion from formal analytic continuation.

Let C0=ab/[2(b^2-a^2)], Delta=b-a, and
    d_j=2C0 M_R(ba^j+ab^j), j=0,1,2,
    U1=(d_2+2ad_1+a^2d_0)/(C0 a Delta^2),
    U2=(d_2+2bd_1+b^2d_0)/(C0 b Delta^2),
    U3=(d_1^2+d_0d_2)/(C0^2 ab Delta^2).
The parent establishes strict positive curvature on |x|>=X, where
    X=max(0, log(6U1)/(R-b), log(6U2)/(R-a),
                 log(6U3)/(2R-a-b)).                       (19)

For the finite input here, [Platt, Isolating some non-trivial zeros of zeta, Theorem 5.1](https://research-information.bris.ac.uk/ws/files/78836669/platt_zeta_submitted.pdf) explicitly establishes simplicity and critical-line location of the first 103800788359 zeros through ordinate 3.0610046*10^10. We use the first three published ordinates from the [LMFDB zero list](https://www.lmfdb.org/zeros/zeta/list?N=1&limit=3):
    14.1347251417346937904572519835625,
    21.0220396387715549926284795938969,
    25.0108575801456887632137909925628.
The database [describes the data source](https://www.lmfdb.org/knowledge/show/rcs.source.zeros.zeta) and its [zero index](https://www.lmfdb.org/zeros/zeta/) states precision +/-2.5*10^(-31). Each displayed ordinate is enlarged by +/-10^(-29), then multiplied by two for F. These are external rigorous-data inputs; this computation does not repeat their completeness verification.

Take R=48. A directed theta-integral evaluation gives
    5.29169286414*10^(-7)<F(48)<5.29196177592*10^(-7).
The method is the degree-16 closed Newton-Cotes certificate from the [four-node canonical-kernel branch](https://flywheel.paradigma.inc/node/c1038977-e066-4414-9f6d-e73bacf62312), now at x=48. It uses 100 panels on [0,1], exact rational weights, the theta sum through n=4 with remainder 120exp(-37.5), and the tail 30000exp(-160). On discs of radius 1/20 centered on [0,1], its analytic integrand bound 10000 still holds: |cos(48z)|<=exp(2.4)<27. With normalized weight variation W, the quadrature error before the factor two is
    10000(1+W)*10^(-17)/.9.
The attached script derives the weights exactly and verifies all monomial identities through degree 16.

Using the interval for F(0) from (9), the full directed calculation yields
    M_R<268341,
    X<3.17649680434<3.18.                                  (20)
The positive residual transform in (18) also uses the published finite RH verification and unconditional counting estimate detailed in the parent. No RH assumption at unbounded heights is introduced.

## 8. Executed certificate and implication

The node table, tail constants and corrected compact certificate were executed using Python's standard library. All 318 closed panels passed (16). The attached compact report records each individual outward lower margin, the common analytic error bounds and the hash of the node table. The minimum normalized curvature lower bound exceeds 1.22*10^(-92); the exact outward value is recorded in the report. The evidence archive contains the three scripts, node enclosures, all reports, the zero-data response, this proof and a reproduction README.

Equations (15)-(17) turn the finite inequalities into H(Lambda)>0 on [0,3.18]. Equations (18)-(20) cover [3.18,infinity). Evenness covers the negative axis, proving (1).

Finally let d,e>0 and t be real. Since (log Lambda)''<0,
    log Lambda(t)-log Lambda(t-e)
      >log Lambda(t+d)-log Lambda(t+d-e).
Exponentiation proves
    Lambda(t)Lambda(t+d-e)-Lambda(t-e)Lambda(t+d)>0.
These are precisely all order-two translation minors. The result does not certify order three or any higher order.

This is an analytic partial theorem supported by a finite directed computation and explicit external zero inputs, not numerical agreement presented as an RH proof. The code and inequalities are preserved for review; no independent certification or novelty is claimed.
