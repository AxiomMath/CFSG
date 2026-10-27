module

public import Certificates.Kernel.Sporadic.OddCore.McLTwo
public import Certificates.Data.GH74.McLSylowKlein
meta import Certificates.Data.GH74.McLSylowKlein
meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.McLKlH CFSG.Sporadic.Recognition.McLAS.sylAHex
#kmisc_hexflat CertificateChecks.KernelSpor.McLKlH CFSG.Sporadic.Recognition.McLAS.sylAHex 3 275 9 3

namespace CertificateChecks.KernelSpor.McLKl

open CFSG.Sporadic.Recognition.McLAS CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native

meta def idM : Array Nat := idTab 275

meta def idsM : Array (Array Nat) := Array.replicate 3 idM

meta def sM : Array (Array Nat) := sylAGens.map natArr

meta def siM : Array (Array Nat) := sM.map (CFSG.Monster.B.Co2.Native.invCand 275)

meta def recM : Array (Array Nat) := (bfs (fun j t => conjTab 275 idM sM[j]! t) 3 idM 200).tabs

meta def clM : Array (Array Nat) :=
  (recM.map fun x => (sM ++ siM).map fun g => comp 275 x g).flatten

end CertificateChecks.KernelSpor.McLKl

#kmulh CertificateChecks.KernelSpor.McLKlS 275 9 CertificateChecks.KernelSpor.McLKl.idsM
  CertificateChecks.KernelSpor.McLKl.sM CertificateChecks.KernelSpor.McLKl.idM 200
#kmisc_packarrs CertificateChecks.KernelSpor.McLKlSI CertificateChecks.KernelSpor.McLKl.siM 9
#kfind CertificateChecks.KernelSpor.McLKlCl CertificateChecks.KernelSpor.McLKl.recM
  CertificateChecks.KernelSpor.McLKl.clM

namespace CertificateChecks.KernelSpor.McLKl

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CertificateChecks.KernelCensus
open CFSG.KLie.CT (notB)

@[expose] noncomputable def cK (p : Nat) : Bool := canonK 275 9 (mask 9) (275 * 9) p

@[expose] noncomputable def memKl (cnt : Nat) (T : Nat → Nat) (x : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun i ih => bIf(Nat.beq (T i) x, true, ih)) cnt

@[expose] noncomputable def conjKl (s si a : Nat) : Nat :=
  pcomp 275 9 (mask 9) (pcomp 275 9 (mask 9) s a) si

theorem base_ok : bAnd(szOK 275 9, bAnd(cK (pidn 275 9), bAnd(CFSG.KS.Prim.idK 275 9 (mask 9),
    bAnd(allN 3 (fun j => bAnd(cK (McLKlH.F j), bAnd(Nat.beq (McLKlS.GI j) (McLKlH.F j),
      bAnd(Nat.beq (McLKlS.G j) (pidn 275 9), bAnd(cK (McLKlSI j),
        invEqK 275 9 (mask 9) (275 * 9) (McLKlH.F j) (McLKlSI j)))))),
    bAnd(Nat.beq McLKlS.cnt 8, penumHdK (pidn 275 9) McLKlS.cnt 200 McLKlS.T McLKlS.PL)))))
      = true := by
  quickRfl

theorem sift_ok : allN 3 (fun j => siftK 275 9 (mask 9) (275 * 9) (pidn 275 9) McLC.LR McLC.TRI
    McLC.BP 5 0 (McLKlH.F j)) = true := by
  quickRfl

theorem sE : penumSlK 275 9 (mask 9) (275 * 9) true McLKlS.G McLKlS.GI 3 McLKlS.cnt McLKlS.T
    McLKlS.PL McLKlS.POS McLKlS.SRT McLKlS.SRI 0 McLKlS.cnt = true := by quickRfl

theorem sH : slK McLKlS.cnt (hsortPtK 275 9 (mask 9) McLKlS.cnt McLKlS.T McLKlS.HS McLKlS.HSI)
    0 McLKlS.cnt = true := by quickRfl

theorem sCl : slK (Nat.mul McLKlS.cnt 6)
    (findPtK McLKlS.cnt McLKlS.T (prodQK 275 9 (mask 9) 6 McLKlS.T (bothK 3 McLKlS.GI McLKlSI))
      McLKlCl) 0 (Nat.mul McLKlS.cnt 6) = true := by quickRfl

theorem sSq : allN 8 (fun i => bAnd(cK (McLKlS.T i),
    Nat.beq (pidn 275 9) (pcomp 275 9 (mask 9) (McLKlS.T i) (McLKlS.T i)))) = true := by quickRfl

theorem sNorm : allN 7 (fun j => allN 8 fun i =>
    memKl 8 McLKlS.T (conjKl (McLTwoH.F j) (McLTwoSI j) (McLKlS.T i))) = true := by quickRfl

theorem neg_mem : notB (allN 7 (fun j => allN 8 fun i =>
    memKl 8 McLKlS.T (conjKl (McLTwoH.F j) (McLTwoSI j) (McLTwoH.F i)))) = true := by quickRfl

theorem neg_count : notB (Nat.beq McLKlS.cnt 16) = true := by quickRfl

end CertificateChecks.KernelSpor.McLKl

end
