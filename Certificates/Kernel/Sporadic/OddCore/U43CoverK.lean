module

public import Certificates.Kernel.Multipliers.U43BChain
public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.Spor.MulHQ
public import CFSG.Certificates.Kernel.Spor.BindList
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43CoverKInputs
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43CoverKInputs
meta import Certificates.Data.CFSGNative.PSL3Four.Basic
meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelSpor.U43CoverK

open CFSG.EvenSporadicStandard.HSStd.U43 CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native

meta def inM : Array (Array Nat) :=
  #[yBArr, kB1a, kB1b, kB2p, kB3a, kB3b, yCArr, kC1a, kC1b, kC2p, kC3a, kC3b, kC4a, kC4b]

meta def inIM : Array (Array Nat) := inM.map (CFSG.Monster.B.Co2.Native.invCand 820)

meta def idM : Array Nat := idTab 820

meta def gBM : Array (Array Nat) := (kTabs yBTab kBComm kBCube).map natArr

meta def gCM : Array (Array Nat) := (kTabs yCTab kCComm kCCube).map natArr

meta def gBIM : Array (Array Nat) := gBM.map (CFSG.Monster.B.Co2.Native.invCand 820)

meta def gCIM : Array (Array Nat) := gCM.map (CFSG.Monster.B.Co2.Native.invCand 820)

meta def ids4M : Array (Array Nat) := Array.replicate 4 idM

meta def ids5M : Array (Array Nat) := Array.replicate 5 idM

meta def recBM : Array (Array Nat) := (bfs (fun j t => conjTab 820 idM gBM[j]! t) 4 idM 400).tabs

meta def recCM : Array (Array Nat) := (bfs (fun j t => conjTab 820 idM gCM[j]! t) 5 idM 400).tabs

meta def clBM : Array (Array Nat) :=
  (recBM.map fun x => (gBM ++ gBIM).map fun g => comp 820 x g).flatten

meta def clCM : Array (Array Nat) :=
  (recCM.map fun x => (gCM ++ gCIM).map fun g => comp 820 x g).flatten

end CertificateChecks.KernelSpor.U43CoverK

#kmisc_packarrs CertificateChecks.KernelSpor.U43KP CertificateChecks.KernelSpor.U43CoverK.inM 10
#kmisc_packarrs CertificateChecks.KernelSpor.U43KI CertificateChecks.KernelSpor.U43CoverK.inIM 10
#kmisc_packarrs CertificateChecks.KernelSpor.U43KBI CertificateChecks.KernelSpor.U43CoverK.gBIM 10
#kmisc_packarrs CertificateChecks.KernelSpor.U43KCI CertificateChecks.KernelSpor.U43CoverK.gCIM 10
#kmulh CertificateChecks.KernelSpor.U43KB 820 10 CertificateChecks.KernelSpor.U43CoverK.ids4M
  CertificateChecks.KernelSpor.U43CoverK.gBM CertificateChecks.KernelSpor.U43CoverK.idM 400
#kmulh CertificateChecks.KernelSpor.U43KC 820 10 CertificateChecks.KernelSpor.U43CoverK.ids5M
  CertificateChecks.KernelSpor.U43CoverK.gCM CertificateChecks.KernelSpor.U43CoverK.idM 400
#kfind CertificateChecks.KernelSpor.U43KBCl CertificateChecks.KernelSpor.U43CoverK.recBM
  CertificateChecks.KernelSpor.U43CoverK.clBM
#kfind CertificateChecks.KernelSpor.U43KCCl CertificateChecks.KernelSpor.U43CoverK.recCM
  CertificateChecks.KernelSpor.U43CoverK.clCM

namespace CertificateChecks.KernelSpor.U43CoverK

open CFSG.EvenSporadicStandard.HSStd.U43
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CertificateChecks.KernelU43B

@[expose] noncomputable def cK (p : Nat) : Bool := canonK 820 10 (mask 10) (820 * 10) p

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 820 10 (mask 10) p q

@[expose] noncomputable def cm (i j : Nat) : Nat := pc (pc (U43KP i) (U43KP j)) (pc (U43KI i) (U43KI j))

@[expose] noncomputable def cb (i : Nat) : Nat := pc (U43KP i) (pc (U43KP i) (U43KP i))

@[expose] noncomputable def gB (j : Nat) : Nat :=
  nIf(Nat.beq j 0, U43KP 0, nIf(Nat.beq j 1, cm 1 2, nIf(Nat.beq j 2, cm 4 5, cb 3)))

@[expose] noncomputable def gC (j : Nat) : Nat :=
  nIf(Nat.beq j 0, U43KP 6, nIf(Nat.beq j 1, cm 7 8, nIf(Nat.beq j 2, cm 10 11,
    nIf(Nat.beq j 3, cm 12 13, cb 9))))

@[expose] noncomputable def inK (y k : Nat) : Bool :=
  bAnd(cK (U43KP k), bAnd(cK (U43KI k), bAnd(invEqK 820 10 (mask 10) (820 * 10) (U43KP k) (U43KI k),
  bAnd(siftK 820 10 (mask 10) (820 * 10) (pidn 820 10) C.LR C.TRI C.BP 3 0 (U43KP k),
    Nat.beq (pc (U43KP k) (U43KP y)) (pc (U43KP y) (U43KP k))))))

theorem in_ok : bAnd(cK (U43KP 0), bAnd(cK (U43KP 6),
    bAnd(invEqK 820 10 (mask 10) (820 * 10) (U43KP 0) (U43KI 0),
    bAnd(invEqK 820 10 (mask 10) (820 * 10) (U43KP 6) (U43KI 6),
    bAnd(allN 5 (fun k => inK 0 (Nat.add k 1)), allN 7 (fun k => inK 6 (Nat.add k 7))))))) = true := by
  quickRfl

theorem bind_ok : bindListK 820 10 (U43KP 0) yBArr.toList = true ∧
    bindListK 820 10 (U43KP 1) kB1a.toList = true ∧ bindListK 820 10 (U43KP 2) kB1b.toList = true ∧
    bindListK 820 10 (U43KP 3) kB2p.toList = true ∧ bindListK 820 10 (U43KP 4) kB3a.toList = true ∧
    bindListK 820 10 (U43KP 5) kB3b.toList = true ∧ bindListK 820 10 (U43KP 6) yCArr.toList = true ∧
    bindListK 820 10 (U43KP 7) kC1a.toList = true ∧ bindListK 820 10 (U43KP 8) kC1b.toList = true ∧
    bindListK 820 10 (U43KP 9) kC2p.toList = true ∧ bindListK 820 10 (U43KP 10) kC3a.toList = true ∧
    bindListK 820 10 (U43KP 11) kC3b.toList = true ∧ bindListK 820 10 (U43KP 12) kC4a.toList = true ∧
    bindListK 820 10 (U43KP 13) kC4b.toList = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> quickRfl

theorem base_ok : bAnd(szOK 820 10, bAnd(cK (pidn 820 10), bAnd(CFSG.KS.Prim.idK 820 10 (mask 10),
    bAnd(allN 4 (fun j => bAnd(Nat.beq (U43KB.GI j) (gB j), bAnd(Nat.beq (U43KB.G j) (pidn 820 10),
      bAnd(cK (U43KB.GI j), bAnd(cK (U43KBI j), invEqK 820 10 (mask 10) (820 * 10) (U43KB.GI j)
        (U43KBI j)))))),
    bAnd(allN 5 (fun j => bAnd(Nat.beq (U43KC.GI j) (gC j), bAnd(Nat.beq (U43KC.G j) (pidn 820 10),
      bAnd(cK (U43KC.GI j), bAnd(cK (U43KCI j), invEqK 820 10 (mask 10) (820 * 10) (U43KC.GI j)
        (U43KCI j)))))),
    bAnd(Nat.beq U43KB.cnt 324, bAnd(Nat.beq U43KC.cnt 324,
    bAnd(penumHdK (pidn 820 10) U43KB.cnt 400 U43KB.T U43KB.PL,
      penumHdK (pidn 820 10) U43KC.cnt 400 U43KC.T U43KC.PL)))))))) = true := by
  quickRfl

theorem bE : penumSlK 820 10 (mask 10) (820 * 10) true U43KB.G U43KB.GI 4 U43KB.cnt U43KB.T
    U43KB.PL U43KB.POS U43KB.SRT U43KB.SRI 0 U43KB.cnt = true := by quickRfl

theorem cE : penumSlK 820 10 (mask 10) (820 * 10) true U43KC.G U43KC.GI 5 U43KC.cnt U43KC.T
    U43KC.PL U43KC.POS U43KC.SRT U43KC.SRI 0 U43KC.cnt = true := by quickRfl

theorem bH : slK U43KB.cnt (hsortPtK 820 10 (mask 10) U43KB.cnt U43KB.T U43KB.HS U43KB.HSI)
    0 U43KB.cnt = true := by quickRfl

theorem cH : slK U43KC.cnt (hsortPtK 820 10 (mask 10) U43KC.cnt U43KC.T U43KC.HS U43KC.HSI)
    0 U43KC.cnt = true := by quickRfl

theorem bCl : slK (Nat.mul U43KB.cnt 8)
    (findPtK U43KB.cnt U43KB.T (prodQK 820 10 (mask 10) 8 U43KB.T (bothK 4 U43KB.GI U43KBI))
      U43KBCl) 0 (Nat.mul U43KB.cnt 8) = true := by quickRfl

theorem cCl : slK (Nat.mul U43KC.cnt 10)
    (findPtK U43KC.cnt U43KC.T (prodQK 820 10 (mask 10) 10 U43KC.T (bothK 5 U43KC.GI U43KCI))
      U43KCCl) 0 (Nat.mul U43KC.cnt 10) = true := by quickRfl

theorem in_neg : inK 6 1 = false := by
  decide +kernel

end CertificateChecks.KernelSpor.U43CoverK

end
