module

public import Certificates.Kernel.Sporadic.ON6.Data
public import Certificates.Data.Kernel.Spor.ChainGK
public import CFSG.Certificates.Kernel.Spor.TabWords

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON6K

open CFSG.KC.Enum CFSG.KS CFSG.KS.CB CFSG.KS.CH CFSG.KS.ON

@[expose] noncomputable def tabAt (T : Nat → Nat) (n j x : Nat) : Nat := tab T (Nat.add (Nat.mul n j) x)

@[expose] noncomputable def lvSel (fs : List (Nat → Nat)) (i k : Nat) : Nat :=
  tab (List.getD fs i fun _ => nat_lit 0) k

@[expose] noncomputable def smallK (n s nb m : Nat) (F FI : Nat → Nat → Nat) (B LEN Mr : Nat → Nat)
    (IDX : Nat → Nat → Nat) (PTS POS PAR LAB : Nat → Nat → Nat) (S : Array (Array Nat))
    (D : Array (List Int)) : Bool :=
  (allN s fun j => allN n fun x => F j x == (S[j]!)[x]! && decide (F j x < n) &&
    decide (FI j x < n) && FI j (F j x) == x) &&
  (allN s fun j => decide (j < m) || allN n fun x =>
    F j x == (D[j - m]!).foldr (CFSG.KS.TW.GZ F FI) x) &&
  (allN nb fun i => decide (B i < n) && idxOK F s B i (IDX i) (LEN i) &&
    cbHead n (Mr i) (B i) (PTS i) (PAR i) (LAB i) &&
    allN (Mr i) (cbPt n (Mr i) (Nat.mul 2 (LEN i)) (stepX F FI (IDX i) (LEN i)) (PTS i) (POS i)
      (PAR i) (LAB i)) &&
    allN n (cbPos n (Mr i) (PTS i) (POS i))) &&
  termG n s nb F B

@[expose] noncomputable def schAll (n nb : Nat) (F FI : Nat → Nat → Nat) (B LEN Mr : Nat → Nat)
    (IDX : Nat → Nat → Nat) (PTS POS PAR LAB : Nat → Nat → Nat) (i h : Nat) : Bool :=
  allN (Nat.mul 2 (LEN i)) fun j => schG n nb (fun i => stepX F FI (IDX i) (LEN i))
    (fun i => invX F FI (IDX i) (LEN i)) PTS POS PAR LAB Mr B i h j

@[expose] noncomputable def schK' (n nb : Nat) (F FI : Nat → Nat → Nat) (B LEN Mr : Nat → Nat)
    (IDX : Nat → Nat → Nat) (PTS POS PAR LAB : Nat → Nat → Nat) : Bool :=
  allN nb fun i => allN (Mr i) (schAll n nb F FI B LEN Mr IDX PTS POS PAR LAB i)

@[expose] noncomputable def schSl (n nb g c : Nat) (F FI : Nat → Nat → Nat) (B LEN Mr : Nat → Nat)
    (IDX : Nat → Nat → Nat) (PTS POS PAR LAB : Nat → Nat → Nat) (s : Nat) : Bool :=
  strictB (Nat.div s c) fun i => strictB (Nat.mul (Nat.mod s c) g) fun lo =>
    allN g fun d => strictB (Nat.add lo d) fun h =>
      bIf(Nat.blt h (Mr i), schAll n nb F FI B LEN Mr IDX PTS POS PAR LAB i h, true)

open CFSG.ONSchreier

@[expose] noncomputable def tFF (j x : Nat) : Nat := tabAt ON6T.TF 32 j x
@[expose] noncomputable def tFI (j x : Nat) : Nat := tabAt ON6T.TI 32 j x
@[expose] noncomputable def tBB (i : Nat) : Nat := Data.T32Chain.base[i]!
@[expose] noncomputable def tXL (i : Nat) : List Nat := List.getD [ON6.TX0, ON6.TX1, ON6.TX2] i []
@[expose] noncomputable def tLEN (i : Nat) : Nat := (tXL i).length
@[expose] noncomputable def tIDX (i t : Nat) : Nat := List.getD (tXL i) t 0
@[expose] noncomputable def tMr (i : Nat) : Nat := List.getD [ON6TL.M0, ON6TL.M1, ON6TL.M2] i 0
@[expose] noncomputable def tPTS : Nat → Nat → Nat := lvSel [ON6TL.PTS0, ON6TL.PTS1, ON6TL.PTS2]
@[expose] noncomputable def tPOS : Nat → Nat → Nat := lvSel [ON6TL.POS0, ON6TL.POS1, ON6TL.POS2]
@[expose] noncomputable def tPAR : Nat → Nat → Nat := lvSel [ON6TL.PAR0, ON6TL.PAR1, ON6TL.PAR2]
@[expose] noncomputable def tLAB : Nat → Nat → Nat := lvSel [ON6TL.LAB0, ON6TL.LAB1, ON6TL.LAB2]

@[expose] noncomputable def mFF (j x : Nat) : Nat := tabAt ON6T.MF 120 j x
@[expose] noncomputable def mFI (j x : Nat) : Nat := tabAt ON6T.MI 120 j x
@[expose] noncomputable def mBB (i : Nat) : Nat := Data.M120Chain.base[i]!
@[expose] noncomputable def mXL (i : Nat) : List Nat := List.getD [ON6.MX0, ON6.MX1, ON6.MX2] i []
@[expose] noncomputable def mLEN (i : Nat) : Nat := (mXL i).length
@[expose] noncomputable def mIDX (i t : Nat) : Nat := List.getD (mXL i) t 0
@[expose] noncomputable def mMr (i : Nat) : Nat := List.getD [ON6ML.M0, ON6ML.M1, ON6ML.M2] i 0
@[expose] noncomputable def mPTS : Nat → Nat → Nat := lvSel [ON6ML.PTS0, ON6ML.PTS1, ON6ML.PTS2]
@[expose] noncomputable def mPOS : Nat → Nat → Nat := lvSel [ON6ML.POS0, ON6ML.POS1, ON6ML.POS2]
@[expose] noncomputable def mPAR : Nat → Nat → Nat := lvSel [ON6ML.PAR0, ON6ML.PAR1, ON6ML.PAR2]
@[expose] noncomputable def mLAB : Nat → Nat → Nat := lvSel [ON6ML.LAB0, ON6ML.LAB1, ON6ML.LAB2]

@[expose] noncomputable def lFF (j x : Nat) : Nat := tabAt ON6T.LF 120 j x
@[expose] noncomputable def lFI (j x : Nat) : Nat := tabAt ON6T.LI 120 j x
@[expose] noncomputable def lBB (i : Nat) : Nat := Data.L120Chain.base[i]!
@[expose] noncomputable def lXL (i : Nat) : List Nat := List.getD [ON6.LX0, ON6.LX1, ON6.LX2] i []
@[expose] noncomputable def lLEN (i : Nat) : Nat := (lXL i).length
@[expose] noncomputable def lIDX (i t : Nat) : Nat := List.getD (lXL i) t 0
@[expose] noncomputable def lMr (i : Nat) : Nat := List.getD [ON6LL.M0, ON6LL.M1, ON6LL.M2] i 0
@[expose] noncomputable def lPTS : Nat → Nat → Nat := lvSel [ON6LL.PTS0, ON6LL.PTS1, ON6LL.PTS2]
@[expose] noncomputable def lPOS : Nat → Nat → Nat := lvSel [ON6LL.POS0, ON6LL.POS1, ON6LL.POS2]
@[expose] noncomputable def lPAR : Nat → Nat → Nat := lvSel [ON6LL.PAR0, ON6LL.PAR1, ON6LL.PAR2]
@[expose] noncomputable def lLAB : Nat → Nat → Nat := lvSel [ON6LL.LAB0, ON6LL.LAB1, ON6LL.LAB2]

@[expose] noncomputable def pFF (j x : Nat) : Nat := tabAt ON6T.PF 21 j x
@[expose] noncomputable def pFI (j x : Nat) : Nat := tabAt ON6T.PI 21 j x
@[expose] noncomputable def pBB (i : Nat) : Nat := Data.PSL21Chain.base[i]!
@[expose] noncomputable def pXL (i : Nat) : List Nat :=
  List.getD [ON6.PX0, ON6.PX1, ON6.PX2, ON6.PX3] i []
@[expose] noncomputable def pLEN (i : Nat) : Nat := (pXL i).length
@[expose] noncomputable def pIDX (i t : Nat) : Nat := List.getD (pXL i) t 0
@[expose] noncomputable def pMr (i : Nat) : Nat := List.getD [ON6PL.M0, ON6PL.M1, ON6PL.M2, ON6PL.M3] i 0
@[expose] noncomputable def pPTS : Nat → Nat → Nat :=
  lvSel [ON6PL.PTS0, ON6PL.PTS1, ON6PL.PTS2, ON6PL.PTS3]
@[expose] noncomputable def pPOS : Nat → Nat → Nat :=
  lvSel [ON6PL.POS0, ON6PL.POS1, ON6PL.POS2, ON6PL.POS3]
@[expose] noncomputable def pPAR : Nat → Nat → Nat :=
  lvSel [ON6PL.PAR0, ON6PL.PAR1, ON6PL.PAR2, ON6PL.PAR3]
@[expose] noncomputable def pLAB : Nat → Nat → Nat :=
  lvSel [ON6PL.LAB0, ON6PL.LAB1, ON6PL.LAB2, ON6PL.LAB3]

@[expose] noncomputable def qFF (j x : Nat) : Nat := tabAt ON6T.QF 120 j x
@[expose] noncomputable def qFI (j x : Nat) : Nat := tabAt ON6T.QI 120 j x
@[expose] noncomputable def qBB (i : Nat) : Nat := Data.PSL120Chain.base[i]!
@[expose] noncomputable def qXL (i : Nat) : List Nat := List.getD [ON6.QX0, ON6.QX1, ON6.QX2] i []
@[expose] noncomputable def qLEN (i : Nat) : Nat := (qXL i).length
@[expose] noncomputable def qIDX (i t : Nat) : Nat := List.getD (qXL i) t 0
@[expose] noncomputable def qMr (i : Nat) : Nat := List.getD [ON6QL.M0, ON6QL.M1, ON6QL.M2] i 0
@[expose] noncomputable def qPTS : Nat → Nat → Nat := lvSel [ON6QL.PTS0, ON6QL.PTS1, ON6QL.PTS2]
@[expose] noncomputable def qPOS : Nat → Nat → Nat := lvSel [ON6QL.POS0, ON6QL.POS1, ON6QL.POS2]
@[expose] noncomputable def qPAR : Nat → Nat → Nat := lvSel [ON6QL.PAR0, ON6QL.PAR1, ON6QL.PAR2]
@[expose] noncomputable def qLAB : Nat → Nat → Nat := lvSel [ON6QL.LAB0, ON6QL.LAB1, ON6QL.LAB2]

@[expose] noncomputable def tSmall : Bool := smallK 32 Data.T32Chain.strongGenerators.size 3
  Data.T32Chain.generators.size tFF tFI tBB tLEN tMr tIDX tPTS tPOS tPAR tLAB
  Data.T32Chain.strongGenerators Data.T32Chain.derivations
@[expose] noncomputable def mSmall : Bool := smallK 120 Data.M120Chain.strongGenerators.size 3
  Data.M120Chain.generators.size mFF mFI mBB mLEN mMr mIDX mPTS mPOS mPAR mLAB
  Data.M120Chain.strongGenerators Data.M120Chain.derivations
@[expose] noncomputable def lSmall : Bool := smallK 120 Data.L120Chain.strongGenerators.size 3
  Data.L120Chain.generators.size lFF lFI lBB lLEN lMr lIDX lPTS lPOS lPAR lLAB
  Data.L120Chain.strongGenerators Data.L120Chain.derivations
@[expose] noncomputable def pSmall : Bool := smallK 21 Data.PSL21Chain.strongGenerators.size 4
  Data.PSL21Chain.generators.size pFF pFI pBB pLEN pMr pIDX pPTS pPOS pPAR pLAB
  Data.PSL21Chain.strongGenerators Data.PSL21Chain.derivations
@[expose] noncomputable def qSmall : Bool := smallK 120 Data.PSL120Chain.strongGenerators.size 3
  Data.PSL120Chain.generators.size qFF qFI qBB qLEN qMr qIDX qPTS qPOS qPAR qLAB
  Data.PSL120Chain.strongGenerators Data.PSL120Chain.derivations

@[expose] noncomputable def tSch (s : Nat) : Bool :=
  schSl 32 3 8 4 tFF tFI tBB tLEN tMr tIDX tPTS tPOS tPAR tLAB s
@[expose] noncomputable def mSch (s : Nat) : Bool :=
  schSl 120 3 4 30 mFF mFI mBB mLEN mMr mIDX mPTS mPOS mPAR mLAB s
@[expose] noncomputable def lSch (s : Nat) : Bool :=
  schSl 120 3 4 30 lFF lFI lBB lLEN lMr lIDX lPTS lPOS lPAR lLAB s
@[expose] noncomputable def pSch (s : Nat) : Bool :=
  schSl 21 4 3 7 pFF pFI pBB pLEN pMr pIDX pPTS pPOS pPAR pLAB s
@[expose] noncomputable def qSch (s : Nat) : Bool :=
  schSl 120 3 4 30 qFF qFI qBB qLEN qMr qIDX qPTS qPOS qPAR qLAB s

end CertificateChecks.KernelSpor.ON6K

end
