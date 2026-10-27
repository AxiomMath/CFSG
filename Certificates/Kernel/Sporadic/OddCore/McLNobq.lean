module

public import Certificates.Kernel.Sporadic.McLK.Data
public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Data.Kernel.Spor.MulHQ
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.McLData
meta import CFSG.ClassicalInvolution.SmallCases.Sporadic.McLData
meta import Certificates.Data.CFSGNative.PSL3Four.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

#ks_perm CertificateChecks.KernelSpor.McLNA 9 CertificateChecks.KernelSpor.McLK.alM
#ks_perm CertificateChecks.KernelSpor.McLNB 9 CertificateChecks.KernelSpor.McLK.beM

namespace CertificateChecks.KernelSpor.McLNobq

open CFSG.ClassicalInvolution.McLData CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native

meta def idM : Array Nat := idTab 275

meta def idsM : Array (Array Nat) := Array.replicate 4 idM

meta def sM : Array (Array Nat) := sgens.toArray.map natArr

end CertificateChecks.KernelSpor.McLNobq

#kmulh CertificateChecks.KernelSpor.McLNS 275 9 CertificateChecks.KernelSpor.McLNobq.idsM
  CertificateChecks.KernelSpor.McLNobq.sM CertificateChecks.KernelSpor.McLNobq.idM 50000

namespace CertificateChecks.KernelSpor.McLNobq

open CFSG.ClassicalInvolution.McLData
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CertificateChecks.KernelSpor.McLK

@[expose] noncomputable def cK (p : Nat) : Bool := canonK 275 9 (mask 9) (275 * 9) p

@[expose] noncomputable def abS (l : Nat) : Nat := nIf(Nat.beq l 1, McLNA, McLNB)

@[expose] noncomputable def kP (j : Nat) : Nat :=
  wfoldK 275 9 (mask 9) abS (kWords.getD j []) (pidn 275 9)

@[expose] noncomputable def kS (l : Nat) : Nat := kP (l - 1)

@[expose] noncomputable def sP (j : Nat) : Nat :=
  wfoldK 275 9 (mask 9) kS (sWords.getD j []) (pidn 275 9)

theorem letters_ok : (kWords.all fun w => w.all fun l => l == 1 || l == 2) = true ∧
    (sWords.all fun w => w.all fun l => l == 1 || l == 2) = true ∧ kWords.length = 2 ∧
    sWords.length = 4 := by
  decide +kernel

theorem base_ok : bAnd(szOK 275 9, bAnd(cK (pidn 275 9), bAnd(CFSG.KS.Prim.idK 275 9 (mask 9),
    bAnd(cK McLNA, bAnd(cK McLNB,
    bAnd(allN 275 (fun x => bAnd(Nat.beq (pg 9 (mask 9) McLNA x) (r32 AL x),
      Nat.beq (pg 9 (mask 9) McLNB x) (r32 BE x))),
    bAnd(allN 4 (fun j => bAnd(cK (McLNS.GI j), bAnd(Nat.beq (McLNS.GI j) (sP j),
      Nat.beq (McLNS.G j) (pidn 275 9)))),
    penumHdK (pidn 275 9) McLNS.cnt 50000 McLNS.T McLNS.PL))))))) = true := by
  quickRfl

theorem sE : penumSlK 275 9 (mask 9) (275 * 9) true McLNS.G McLNS.GI 4 McLNS.cnt McLNS.T
    McLNS.PL McLNS.POS McLNS.SRT McLNS.SRI 0 McLNS.cnt = true := by quickRfl

theorem sH : slK McLNS.cnt (hsortPtK 275 9 (mask 9) McLNS.cnt McLNS.T McLNS.HS McLNS.HSI)
    0 McLNS.cnt = true := by quickRfl

@[expose] noncomputable def ncAt (t i : Nat) : Bool :=
  bAnd(Nat.beq (pcomp 275 9 (mask 9) (McLNS.T i) (McLNS.T i)) (pidn 275 9),
    bAnd(bIf(Nat.beq (McLNS.T i) (pidn 275 9), false, true), bIf(Nat.beq (McLNS.T i) t, false, true)))

theorem nc_ok : (List.range McLNS.cnt).any (ncAt McLNA) = true := by
  quickRfl

theorem nc_neg : (List.range McLNS.cnt).all (fun i => !ncAt (McLNS.T i) i) = true := by
  quickRfl

end CertificateChecks.KernelSpor.McLNobq

end
