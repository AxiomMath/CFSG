module

public import Certificates.Kernel.SporSch.Ru.Gens
public import Certificates.Kernel.LocalQT.PEnumD
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.TMemRuCheck
public import CFSG.Certificates.Kernel.Common.Loop
public import Certificates.Data.Kernel.L34K
meta import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.TMemRuCheck
import CFSG.Certificates.Kernel.Common.Harness

namespace CertificateChecks.KernelSporSch.TMem27100

meta def sM : Array (Array Nat) := CFSG.EvenSporadicStandard.Induction.TMemRu.tmSTabs

meta def idM : Array Nat := CFSG.PSL3Four.Native.idTab 4060

end CertificateChecks.KernelSporSch.TMem27100

public section

set_option maxRecDepth 400000

#kpenum_d CertificateChecks.KernelSporSch.TMem27100.SE 4060 12 false
  CertificateChecks.KernelSporSch.TMem27100.sM CertificateChecks.KernelSporSch.TMem27100.sM
  CertificateChecks.KernelSporSch.TMem27100.idM 64

namespace CertificateChecks.KernelSporSch.TMem27100

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.L34K
open CertificateChecks.KernelSporSch.RuG CFSG.EvenSporadicStandard.Induction.TMemRu
open CFSG.KLie.CT (andB orB notB)

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 4060 12 (mask 12) p q

@[expose] noncomputable def pinv (p : Nat) : Nat := pinvS 4060 12 (mask 12) p

@[expose] noncomputable def cn (p : Nat) : Bool := canonK 4060 12 (mask 12) (4060 * 12) p

@[expose] noncomputable def e : Nat := pidn 4060 12

@[expose] noncomputable def sel2 (a b j : Nat) : Nat := nIf(Nat.beq j 0, a, b)

@[expose] noncomputable def sel4 (a b c d j : Nat) : Nat :=
  nIf(Nat.beq j 0, a, nIf(Nat.beq j 1, b, nIf(Nat.beq j 2, c, d)))

@[expose] noncomputable def W2 (w : List Int) : Nat := wordK 4060 12 (mask 12) e (sel2 A0 A1)
  (sel2 A0I A1I) w

@[expose] noncomputable def TA : Nat := W2 tmWordA
@[expose] noncomputable def TB : Nat := W2 tmWordB
@[expose] noncomputable def TL : Nat := W2 tmWordL
@[expose] noncomputable def TAI : Nat := pinv TA
@[expose] noncomputable def TBI : Nat := pinv TB
@[expose] noncomputable def TLI : Nat := pinv TL

@[expose] noncomputable def WAB (w : List Int) : Nat := wordK 4060 12 (mask 12) e (sel2 TA TB)
  (sel2 TAI TBI) w

@[expose] noncomputable def TZ : Nat := WAB tmWordZ
@[expose] noncomputable def TAl : Nat := pc (pc TL TA) TLI
@[expose] noncomputable def TBl : Nat := pc (pc TL TB) TLI
@[expose] noncomputable def TAlI : Nat := pinv TAl
@[expose] noncomputable def TBlI : Nat := pinv TBl
@[expose] noncomputable def SG (i : Nat) : Nat := WAB (tmWordsS.getD i [])
@[expose] noncomputable def CG (j : Nat) : Nat := WAB (tmWordsC.getD j [])
@[expose] noncomputable def ZJ (j : Nat) : Nat := pc (pc (CG j) TZ) (pinv (CG j))

@[expose] noncomputable def ok (p : Nat) : Bool := andB (cn p) (andB (cn (pinv p)) (pk p (pinv p)))

theorem kInv : andB (ok TA) (andB (ok TB) (andB (ok TL) (andB (ok TAl) (andB (ok TBl)
    (andB (cn TZ) (andB (allN 4 fun i => ok (SG i)) (allN 7 fun j => ok (CG j)))))))) = true := by
  quickRfl

theorem kBasic : andB (Nat.beq (pc A0 A0) e) (andB (notB (Nat.beq A0 e))
    (allN 4060 fun i => notB (Nat.beq (pg 12 (mask 12) A0 i) i))) = true := by
  quickRfl

theorem kAB : andB (Nat.beq (pc TA A0) (pc A0 TA)) (andB (Nat.beq (pc TB A0) (pc A0 TB))
    (andB (Nat.beq (ppow 4060 12 (mask 12) e TA 5) e) (andB (notB (Nat.beq TA e))
    (andB (Nat.beq (ppow 4060 12 (mask 12) e TB 7) e) (andB (notB (Nat.beq TB e))
    (andB (Nat.beq (ppow 4060 12 (mask 12) e (pc TA TB) 13) e)
      (notB (Nat.beq (pc TA TB) e)))))))) = true := by
  quickRfl

theorem kZL : andB (Nat.beq (pc TZ TZ) e) (andB (notB (Nat.beq TZ e))
    (andB (Nat.beq (pg 12 (mask 12) TZ 0) 0) (Nat.beq (pc (pc TL A0) TLI) (pc A0 TZ)))) = true := by
  quickRfl

theorem kGen : andB (Nat.beq (wordK 4060 12 (mask 12) e (sel4 TA TB TAl TBl)
    (sel4 TAI TBI TAlI TBlI) tmWordG0) A0) (Nat.beq (wordK 4060 12 (mask 12) e
    (sel4 TA TB TAl TBl) (sel4 TAI TBI TAlI TBlI) tmWordG1) A1) = true := by
  quickRfl

theorem kSyl : allN 4 (fun i => Nat.beq (pc (SG i) TZ) (pc TZ (SG i))) = true := by
  quickRfl

theorem kEnum : andB (Nat.beq SE.cnt 64) (andB (Nat.beq SE.k 4) (andB (penumHdK e SE.cnt 64 SE.T SE.PL)
    (andB (allN 4 fun i => Nat.beq (SE.G i) (SG i))
      (penumSlK 4060 12 (mask 12) (4060 * 12) false SE.G SE.GI 4 SE.cnt SE.T SE.PL SE.POS SE.SRT
        SE.SRI 0 64)))) = true := by
  quickRfl

theorem kCover : allN 64 (fun t => strictB (SE.T t) fun x =>
    orB (Nat.beq x e) (orB (notB (invPt 4060 12 x)) (orB (notB (allN 4 fun g => commPt 4060 12 x (SG g)))
      (notB (allN 7 fun j => notB (Nat.beq x (ZJ j))))))) = true := by
  quickRfl

theorem kNeg : notB (Nat.beq (pc TZ TZ) TZ) = true := by quickRfl

end CertificateChecks.KernelSporSch.TMem27100

end
