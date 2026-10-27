module

public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Data.Kernel.Spor.MulHQ
public import CFSG.Certificates.Kernel.Spor.BindList
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Data3
meta import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Data3
meta import Certificates.Data.CFSGNative.PSL3Four.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelSpor.CU43Syl

open CFSG.EvenSporadicStandard.M24Std.CU43 CFSG.PSL3Four.Native

meta def idM : Array Nat := idTab 820

meta def idsM : Array (Array Nat) := Array.replicate 5 idM

meta def sM : Array (Array Nat) := #[sylGen0, sylGen1, sylGen2, sylGen3, sylGen4]

end CertificateChecks.KernelSpor.CU43Syl

#kmulh CertificateChecks.KernelSpor.CU43S 820 10 CertificateChecks.KernelSpor.CU43Syl.idsM
  CertificateChecks.KernelSpor.CU43Syl.sM CertificateChecks.KernelSpor.CU43Syl.idM 256

namespace CertificateChecks.KernelSpor.CU43Syl

open CFSG.EvenSporadicStandard.M24Std.CU43
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH

@[expose] noncomputable def cK (p : Nat) : Bool := canonK 820 10 (mask 10) (820 * 10) p

theorem base_ok : bAnd(szOK 820 10, bAnd(cK (pidn 820 10), bAnd(CFSG.KS.Prim.idK 820 10 (mask 10),
    bAnd(allN 5 (fun j => bAnd(cK (CU43S.GI j), Nat.beq (CU43S.G j) (pidn 820 10))),
    bAnd(Nat.beq CU43S.cnt 128, penumHdK (pidn 820 10) CU43S.cnt 256 CU43S.T CU43S.PL))))) =
      true := by
  quickRfl

theorem bind0 : bindListK 820 10 (CU43S.GI 0) sylGen0.toList = true := by quickRfl
theorem bind1 : bindListK 820 10 (CU43S.GI 1) sylGen1.toList = true := by quickRfl
theorem bind2 : bindListK 820 10 (CU43S.GI 2) sylGen2.toList = true := by quickRfl
theorem bind3 : bindListK 820 10 (CU43S.GI 3) sylGen3.toList = true := by quickRfl
theorem bind4 : bindListK 820 10 (CU43S.GI 4) sylGen4.toList = true := by quickRfl

theorem sE : penumSlK 820 10 (mask 10) (820 * 10) true CU43S.G CU43S.GI 5 CU43S.cnt CU43S.T
    CU43S.PL CU43S.POS CU43S.SRT CU43S.SRI 0 CU43S.cnt = true := by quickRfl

theorem sH : slK CU43S.cnt (hsortPtK 820 10 (mask 10) CU43S.cnt CU43S.T CU43S.HS CU43S.HSI)
    0 CU43S.cnt = true := by quickRfl

@[expose] noncomputable def commK (i j : Nat) : Bool :=
  Nat.beq (pcomp 820 10 (mask 10) (CU43S.T i) (CU43S.T j))
    (pcomp 820 10 (mask 10) (CU43S.T j) (CU43S.T i))

@[expose] noncomputable def involK (i : Nat) : Bool :=
  bAnd(Nat.beq (pcomp 820 10 (mask 10) (CU43S.T i) (CU43S.T i)) (pidn 820 10),
    bIf(Nat.beq (CU43S.T i) (pidn 820 10), false, true))

@[expose] noncomputable def centK (i : Nat) : Bool := (List.range 128).all (commK i)

@[expose] noncomputable def cntK (i : Nat) : Nat :=
  (List.range 128).countP fun j => involK j && commK i j

@[expose] noncomputable def rankK (c d : Nat) : Bool :=
  Nat.ble ((List.range 128).countP centK) c &&
    (List.range 128).all fun i => !involK i || centK i || Nat.ble (cntK i) d

theorem rank_ok : rankK 16 30 = true := by
  quickRfl

theorem rank_neg : rankK 16 1 = false := by
  decide +kernel

end CertificateChecks.KernelSpor.CU43Syl

end
