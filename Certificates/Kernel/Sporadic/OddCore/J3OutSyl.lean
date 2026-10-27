module

public import Certificates.Kernel.Sporadic.OddCore.J3Cent
public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.SporSch.PairJ3.Chain
public import Certificates.Data.Kernel.Spor.MulHQ
public import Certificates.Data.Kernel.Spor.Prim
public import Certificates.Data.Kernel.Spor.MulHF
meta import CFSG.Sporadic.SmallOddCore.J3DataInputs
meta import Certificates.Data.CFSGNative.PSL3Four.Basic
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelSpor.J3OutSyl

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

meta def idM : Array Nat := CFSG.PSL3Four.Native.idTab 6156

meta def idsM : Array (Array Nat) := Array.replicate 8 idM

meta def sM : Array (Array Nat) := (List.range 8).toArray.map fun k => natArr (j3CentTbl (k + 1))

end CertificateChecks.KernelSpor.J3OutSyl

#kmulh CertificateChecks.KernelSpor.J3XS 6156 13 CertificateChecks.KernelSpor.J3OutSyl.idsM
  CertificateChecks.KernelSpor.J3OutSyl.sM CertificateChecks.KernelSpor.J3OutSyl.idM 256

namespace CertificateChecks.KernelSpor.J3OutSyl

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CertificateChecks.KernelSporSch

@[expose] noncomputable def cK (p : Nat) : Bool := canonK 6156 13 (mask 13) (6156 * 13) p

theorem base_ok : bAnd(szOK 6156 13, bAnd(cK (pidn 6156 13), bAnd(CFSG.KS.Prim.idK 6156 13 (mask 13),
    bAnd(cK (J3CentP 9),
    bAnd(allN 8 (fun j => bAnd(cK (J3XS.GI j), bAnd(Nat.beq (J3XS.GI j) (J3CentP (Nat.add j 1)),
      Nat.beq (J3XS.G j) (pidn 6156 13)))),
    bAnd(Nat.beq J3XS.cnt 256, penumHdK (pidn 6156 13) J3XS.cnt 256 J3XS.T J3XS.PL)))))) =
      true := by
  quickRfl

@[expose] noncomputable def sEBlk (k : Nat) : Bool :=
  penumSlK 6156 13 (mask 13) (6156 * 13) true J3XS.G J3XS.GI 8 J3XS.cnt J3XS.T
    J3XS.PL J3XS.POS J3XS.SRT J3XS.SRI (16 * k) 16

#kc_each sEBlk 0 16

theorem sHF : slK J3XS.cnt (hsortPtKF 6156 13 (mask 13) J3XS.cnt J3XS.T J3XS.HS J3XS.HSI)
    0 J3XS.cnt = true := by quickRfl

theorem sHF_neg : hsortPtKF 6156 13 (mask 13) J3XS.cnt (fun _ => 0) J3XS.HS J3XS.HSI 0 = false := by
  decide +kernel

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 6156 13 (mask 13) p q

@[expose] def xWord : List Int := [3, -5, 2, -3, 2, 1, 2, 1, -3, 5, 3, 1, 5]

@[expose] noncomputable def xW : Nat := wordK 6156 13 (mask 13) (pidn 6156 13) PJ3.S PJ3.SI xWord

@[expose] noncomputable def commAll (p : Nat) : Bool :=
  (List.range 8).all fun j => Nat.beq (pc p (J3XS.GI j)) (pc (J3XS.GI j) p)

@[expose] noncomputable def cenRow (i : Nat) : Bool :=
  !commAll (J3XS.T i) || Nat.beq (J3XS.T i) (pidn 6156 13) || Nat.beq (J3XS.T i) (J3CentP 9)

@[expose] noncomputable def cenBlk (k : Nat) : Bool :=
  (List.range 16).all fun l => cenRow (16 * k + l)

theorem t0_mem : (List.range 256).any (fun i => Nat.beq (J3XS.T i) (J3CentP 9)) = true := by
  quickRfl

#kc_each cenBlk 0 16

theorem x_mem : (List.range 256).any (fun i => Nat.beq (J3XS.T i) xW) = true := by
  quickRfl

theorem x_four : Nat.beq (pc (pc xW xW) (pc xW xW)) (J3CentP 9) = true := by
  quickRfl

theorem x_word : wordEqK 6156 13 (mask 13) (pidn 6156 13) PJ3.S PJ3.SI 5 xWord xW = true := by
  quickRfl

theorem neg_center : (!commAll xW) = true := by
  quickRfl

theorem neg_sq : (!Nat.beq (pc xW xW) (J3CentP 9)) = true := by
  quickRfl

end CertificateChecks.KernelSpor.J3OutSyl

end
