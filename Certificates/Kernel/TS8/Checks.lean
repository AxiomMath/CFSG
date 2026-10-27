module

public import Certificates.Kernel.TS8.Data
public import Certificates.Data.Kernel.TS8.Defs
public import Certificates.Data.Kernel.S63K.OrbRun
public import Certificates.Data.Kernel.Spor.Raw
public import Certificates.Kernel.Misc.Perm.J5B
public import Certificates.Kernel.Census.J3.Text
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8D8Words
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTS8

open CFSG.KC.TS8 CFSG.KC.S63K CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
  CFSG.EvenSporadicStandard.Fin76b.TS8D8

@[expose] noncomputable def f8 (T : Nat → Nat) (t i : Nat) : Nat := pg 8 (mask 8) (T t) i

@[expose] noncomputable def PA2 : Nat := CertificateChecks.KernelMisc.J2F.JS.F 0
@[expose] noncomputable def PB2 : Nat := CertificateChecks.KernelMisc.J2F.JS.F 1
@[expose] noncomputable def PU2 : Nat := CertificateChecks.KernelMisc.J2F.JU.F 0
@[expose] noncomputable def GW2 (k : Nat) : Nat := J2P k
@[expose] noncomputable def EP2 (i : Nat) : Nat := J2P (3 + i)
@[expose] noncomputable def W2 (i : Nat) : Nat := f8 J2T 0 i
@[expose] noncomputable def Pa2 (i : Nat) : Nat := f8 J2T 1 i
@[expose] noncomputable def La2 (i : Nat) : Nat := f8 J2T 2 i
@[expose] noncomputable def S2 (i : Nat) : Nat := f8 J2T 3 i
@[expose] noncomputable def IT2 (i : Nat) : Nat := f8 J2T 4 i
@[expose] noncomputable def MT2 (a b : Nat) : Nat := f8 J2T (5 + a) b

theorem sz2 : szOK 315 9 = true := by quickRfl

theorem perm2 : bAnd(permOK 315 9 (mask 9) (315 * 9) PA2 (pinvS 315 9 (mask 9) PA2),
    bAnd(permOK 315 9 (mask 9) (315 * 9) PB2 (pinvS 315 9 (mask 9) PB2),
      permOK 315 9 (mask 9) (315 * 9) PU2 (pinvS 315 9 (mask 9) PU2))) = true := by
  quickRfl

theorem word2 : (allN 3 fun k =>
    Nat.beq (wordP 315 9 PA2 PB2 PU2 (j2SylowWords.getD k [])) (GW2 k)) = true := by
  quickRfl

theorem len2 : Nat.beq j2SylowWords.length 3 = true := by decide +kernel

theorem dist2 : sortDK EP2 S2 256 = true := by quickRfl

theorem root2 : bAnd(Nat.beq (EP2 0) (pidn 315 9), bAnd(Nat.beq (Pa2 0) 0, Nat.beq (La2 0) 0)) =
    true := by
  quickRfl

theorem tree2 : (allN 255 fun c => bAnd(Nat.blt (Pa2 (c + 1)) (c + 1),
    bAnd(Nat.blt (La2 (c + 1)) 3, Nat.beq (W2 (3 * Pa2 (c + 1) + La2 (c + 1))) (c + 1)))) = true := by
  quickRfl

theorem act2 : (allN 256 fun h => allN 3 fun k => bAnd(Nat.blt (W2 (3 * h + k)) 256,
    Nat.beq (pcomp 315 9 (mask 9) (EP2 h) (GW2 k)) (EP2 (W2 (3 * h + k))))) = true := by
  quickRfl

theorem run2 : Nat.beq (orbRunK W2 Pa2 La2 3 257 0 1) 256 = true := by quickRfl

theorem mt2 : mtK MT2 W2 Pa2 La2 3 = true := by quickRfl

theorem it2 : (allN 256 fun a => bAnd(Nat.blt (IT2 a) 256,
    Nat.beq (pinvS 315 9 (mask 9) (EP2 a)) (EP2 (IT2 a)))) = true := by
  quickRfl

theorem search2 : searchF (mF MT2) (iF IT2) = true := by quickRfl

theorem chain2 : bIf(hasChainF (mF MT2) 5 [0] (invsF (mF MT2)), false, true) = true := by quickRfl

@[expose] noncomputable def PA3 : Nat := CertificateChecks.KernelCensus.J3S.F 0
@[expose] noncomputable def PB3 : Nat := CertificateChecks.KernelCensus.J3S.F 1
@[expose] noncomputable def PU3 : Nat := CertificateChecks.KernelCensus.J3UT.F 0
@[expose] noncomputable def GW3 (k : Nat) : Nat := J3P k
@[expose] noncomputable def EP3 (i : Nat) : Nat := J3P (4 + i)
@[expose] noncomputable def W3 (i : Nat) : Nat := f8 J3T 0 i
@[expose] noncomputable def Pa3 (i : Nat) : Nat := f8 J3T 1 i
@[expose] noncomputable def La3 (i : Nat) : Nat := f8 J3T 2 i
@[expose] noncomputable def S3 (i : Nat) : Nat := f8 J3T 3 i
@[expose] noncomputable def IT3 (i : Nat) : Nat := f8 J3T 4 i
@[expose] noncomputable def MT3 (a b : Nat) : Nat := f8 J3T (5 + a) b

theorem sz3 : szOK 6156 13 = true := by quickRfl

theorem perm3 : bAnd(permOK 6156 13 (mask 13) (6156 * 13) PA3 (pinvS 6156 13 (mask 13) PA3),
    bAnd(permOK 6156 13 (mask 13) (6156 * 13) PB3 (pinvS 6156 13 (mask 13) PB3),
      permOK 6156 13 (mask 13) (6156 * 13) PU3 (pinvS 6156 13 (mask 13) PU3))) = true := by
  quickRfl

theorem word3 : (allN 4 fun k =>
    Nat.beq (wordP 6156 13 PA3 PB3 PU3 (j3SylowWords.getD k [])) (GW3 k)) = true := by
  quickRfl

theorem len3 : Nat.beq j3SylowWords.length 4 = true := by decide +kernel

theorem dist3 : sortDK EP3 S3 256 = true := by quickRfl

theorem root3 : bAnd(Nat.beq (EP3 0) (pidn 6156 13), bAnd(Nat.beq (Pa3 0) 0, Nat.beq (La3 0) 0)) =
    true := by
  quickRfl

theorem tree3 : (allN 255 fun c => bAnd(Nat.blt (Pa3 (c + 1)) (c + 1),
    bAnd(Nat.blt (La3 (c + 1)) 4, Nat.beq (W3 (4 * Pa3 (c + 1) + La3 (c + 1))) (c + 1)))) = true := by
  quickRfl

@[expose] noncomputable def act3 (b : Nat) : Bool :=
  allN 64 fun r => allN 4 fun k => bAnd(Nat.blt (W3 (4 * (64 * b + r) + k)) 256,
    Nat.beq (pcomp 6156 13 (mask 13) (EP3 (64 * b + r)) (GW3 k)) (EP3 (W3 (4 * (64 * b + r) + k))))

theorem act3_0 : act3 0 = true := by quickRfl
theorem act3_1 : act3 1 = true := by quickRfl
theorem act3_2 : act3 2 = true := by quickRfl
theorem act3_3 : act3 3 = true := by quickRfl

theorem run3 : Nat.beq (orbRunK W3 Pa3 La3 4 257 0 1) 256 = true := by quickRfl

theorem mt3 : mtK MT3 W3 Pa3 La3 4 = true := by quickRfl

@[expose] noncomputable def it3 (b : Nat) : Bool :=
  allN 64 fun r => bAnd(Nat.blt (IT3 (64 * b + r)) 256,
    Nat.beq (pinvS 6156 13 (mask 13) (EP3 (64 * b + r))) (EP3 (IT3 (64 * b + r))))

theorem it3_0 : it3 0 = true := by quickRfl
theorem it3_1 : it3 1 = true := by quickRfl
theorem it3_2 : it3 2 = true := by quickRfl
theorem it3_3 : it3 3 = true := by quickRfl

theorem search3 : searchF (mF MT3) (iF IT3) = true := by quickRfl

theorem chain3 : bIf(hasChainF (mF MT3) 5 [0] (invsF (mF MT3)), false, true) = true := by quickRfl

end CertificateChecks.KernelTS8

end
