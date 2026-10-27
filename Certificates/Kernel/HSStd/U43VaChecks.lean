module

public import Certificates.Kernel.HSStd.U43VaData
public import Certificates.Kernel.Multipliers.U43BChain
public import Certificates.Data.Kernel.Spor.MulHQ
public import CFSG.Certificates.Kernel.Spor.BindList
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CertificateChecks.KernelHSStd.U43Va

open CFSG.EvenSporadicStandard.HSStd.U43 CFSG.EvenSporadicStandard.M24Std.CU43
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CertificateChecks.KernelU43B CertificateChecks.KernelHSStd

@[expose] noncomputable def cK (p : Nat) : Bool := canonK 820 10 (mask 10) (820 * 10) p

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 820 10 (mask 10) p q

@[expose] noncomputable def ppow (p : Nat) (e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (pidn 820 10) (fun _ acc => pc p acc) e

@[expose] noncomputable def TK (k : Nat) : Nat :=
  pc (ppow (U43VP 7) (Nat.div k 4)) (ppow (U43VP 8) (Nat.mod k 4))

@[expose] noncomputable def TKI (k : Nat) : Nat := pinvS 820 10 (mask 10) (TK k)

@[expose] noncomputable def GJ (j : Nat) : Nat := U43VI (Nat.add j 2)

@[expose] noncomputable def cosK (i : Nat) : Bool :=
  strictB (U43VC i) fun k => bAnd(Nat.blt k 8, bAnd(Nat.beq (Nat.mod k 2) 0,
    siftK 820 10 (mask 10) (820 * 10) (pidn 820 10) C.LR C.TRI C.BP 3 0 (pc (U43VP i) (TKI k))))

theorem kBind : bindListK 820 10 (U43VP 0) rep8.toList = true ∧
    bindListK 820 10 (U43VP 1) vaZ.toList = true ∧
    bindListK 820 10 (U43VP 2) vaCg[0]!.toList = true ∧
    bindListK 820 10 (U43VP 3) vaCg[1]!.toList = true ∧
    bindListK 820 10 (U43VP 4) vaCg[2]!.toList = true ∧
    bindListK 820 10 (U43VP 5) vaCg[3]!.toList = true ∧
    bindListK 820 10 (U43VP 6) vaCg[4]!.toList = true ∧
    bindListK 820 10 (U43VP 7) phiArr.toList = true ∧
    bindListK 820 10 (U43VP 8) deltaArr.toList = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> quickRfl

theorem kSz : (szOK 820 10 && cK (pidn 820 10) && CFSG.KS.Prim.idK 820 10 (mask 10) &&
    Nat.beq vaCg.size 5) = true := by
  quickRfl

theorem kIn : allN 9 (fun i => bAnd(cK (U43VP i), bAnd(cK (U43VI i),
    invEqK 820 10 (mask 10) (820 * 10) (U43VP i) (U43VI i)))) = true := by
  quickRfl

theorem kTK : allN 8 (fun k => bAnd(cK (TK k), permOK 820 10 (mask 10) (820 * 10) (TK k) (TKI k))) =
    true := by
  quickRfl

theorem kCos : allN 6 (fun i => cosK (Nat.succ i)) = true := by quickRfl

theorem kZ : (Nat.beq (pc (U43VP 1) (U43VP 0)) (pc (U43VP 0) (U43VP 1)) &&
    !Nat.beq (U43VP 1) (pidn 820 10) && !Nat.beq (U43VP 1) (U43VP 0)) = true := by
  quickRfl

theorem kComm : allN 5 (fun j => bAnd(Nat.beq (pc (U43VP (Nat.add j 2)) (U43VP 0))
    (pc (U43VP 0) (U43VP (Nat.add j 2))),
    Nat.beq (pc (U43VP 1) (U43VP (Nat.add j 2))) (pc (U43VP (Nat.add j 2)) (U43VP 1)))) = true := by
  quickRfl

theorem kHead : bAnd(allN 5 (fun j => bAnd(Nat.beq (U43VA.GI j) (U43VP (Nat.add j 2)),
      Nat.beq (U43VA.G j) (pidn 820 10))),
    bAnd(Nat.beq U43VA.cnt 2880, bAnd(Nat.beq U43VA.k 5,
      penumHdK (pidn 820 10) U43VA.cnt 50000 U43VA.T U43VA.PL))) = true := by
  quickRfl

@[expose] noncomputable def pe (s : Nat) : Bool :=
  penumSlK 820 10 (mask 10) (820 * 10) true U43VA.G U43VA.GI 5 U43VA.cnt U43VA.T U43VA.PL
    U43VA.POS U43VA.SRT U43VA.SRI (Nat.mul 96 s) 96

@[expose] noncomputable def hs (s : Nat) : Bool :=
  slK U43VA.cnt (hsortPtK 820 10 (mask 10) U43VA.cnt U43VA.T U43VA.HS U43VA.HSI) (Nat.mul 288 s) 288

@[expose] noncomputable def cl (s : Nat) : Bool :=
  slK (Nat.mul U43VA.cnt 10) (findPtK U43VA.cnt U43VA.T
    (prodQK 820 10 (mask 10) 10 U43VA.T (bothK 5 U43VA.GI GJ)) U43VACl) (Nat.mul 960 s) 960

end CertificateChecks.KernelHSStd.U43Va

#kc_each CertificateChecks.KernelHSStd.U43Va.pe 0 30
#kc_each CertificateChecks.KernelHSStd.U43Va.hs 0 10
#kc_each CertificateChecks.KernelHSStd.U43Va.cl 0 30

end
