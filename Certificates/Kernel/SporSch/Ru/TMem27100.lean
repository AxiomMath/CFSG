module

public import Certificates.Kernel.SporSch.Ru.Gens
public import Certificates.Kernel.LocalQT.PEnumD
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.TMemRuCheck
public import CFSG.Certificates.Kernel.Common.Loop
public import Certificates.Data.Kernel.L34K
meta import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.TMemRuCheck
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.Common.Eval

set_option Elab.async false

namespace CertificateChecks.KernelSporSch.TMem27100

meta def sM : Array (Array Nat) := CFSG.EvenSporadicStandard.Induction.TMemRu.tmSTabs

meta def idM : Array Nat := CFSG.PSL3Four.Native.idTab 4060

open CFSG.EvenSporadicStandard.Induction.TMemRu CFSG.Monster.B.Co2.Native CFSG.Sporadic.RuSchreier
  CFSG.KC.Eval in
meta def tmStep (_ : Array Val) : Except String (Array (Lean.Name × Val)) :=
  let pk (a : Array Nat) : Nat := a.foldr (fun x acc => (acc <<< 12) ||| x) 0
  let base : Array (Lean.Name × Val) := #[(`TA, Val.nat (pk tmTA)), (`TB, Val.nat (pk tmTB)),
    (`TL, Val.nat (pk tmTL)), (`TZ, Val.nat (pk tmTZ))]
  let sg : List (Lean.Name × Val) :=
    (List.range 4).map fun i => (Lean.Name.mkSimple s!"SG{i}", Val.nat (pk (tmSGen i)))
  let cg : List (Lean.Name × Val) :=
    (List.range 7).map fun j => (Lean.Name.mkSimple s!"CG{j}", Val.nat (pk (tmCGen j)))
  let cgi : List (Lean.Name × Val) :=
    (List.range 7).map fun j => (Lean.Name.mkSimple s!"CGI{j}", Val.nat (pk (ruInv (tmCGen j))))
  .ok (base ++ sg.toArray ++ cg.toArray ++ cgi.toArray)

end CertificateChecks.KernelSporSch.TMem27100

public section

set_option maxRecDepth 400000

#kc_eval CertificateChecks.KernelSporSch.TMem27100 V CertificateChecks.KernelSporSch.TMem27100.tmStep

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

@[expose] noncomputable def TA : Nat := V.TA
@[expose] noncomputable def TB : Nat := V.TB
@[expose] noncomputable def TL : Nat := V.TL

theorem kTA : Nat.beq (W2 tmWordA) TA = true := by quickRfl
theorem kTB : Nat.beq (W2 tmWordB) TB = true := by quickRfl
theorem kTL : Nat.beq (W2 tmWordL) TL = true := by quickRfl

@[expose] noncomputable def TAI : Nat := pinv TA
@[expose] noncomputable def TBI : Nat := pinv TB
@[expose] noncomputable def TLI : Nat := pinv TL

@[expose] noncomputable def WAB (w : List Int) : Nat := wordK 4060 12 (mask 12) e (sel2 TA TB)
  (sel2 TAI TBI) w

@[expose] noncomputable def TZ : Nat := V.TZ
@[expose] noncomputable def TAl : Nat := pc (pc TL TA) TLI
@[expose] noncomputable def TBl : Nat := pc (pc TL TB) TLI
@[expose] noncomputable def TAlI : Nat := pinv TAl
@[expose] noncomputable def TBlI : Nat := pinv TBl
@[expose] noncomputable def SG (i : Nat) : Nat := sel4 V.SG0 V.SG1 V.SG2 V.SG3 i
@[expose] noncomputable def CG (j : Nat) : Nat :=
  nIf(Nat.blt j 4, sel4 V.CG0 V.CG1 V.CG2 V.CG3 j, sel4 V.CG4 V.CG5 V.CG6 V.CG6 (Nat.sub j 4))
@[expose] noncomputable def CGI (j : Nat) : Nat :=
  nIf(Nat.blt j 4, sel4 V.CGI0 V.CGI1 V.CGI2 V.CGI3 j, sel4 V.CGI4 V.CGI5 V.CGI6 V.CGI6 (Nat.sub j 4))

theorem kTZ : Nat.beq (WAB tmWordZ) TZ = true := by quickRfl
theorem kSG : allN 4 (fun i => Nat.beq (WAB (tmWordsS.getD i [])) (SG i)) = true := by quickRfl
theorem kCG : allN 7 (fun j => Nat.beq (WAB (tmWordsC.getD j [])) (CG j)) = true := by quickRfl
@[expose] noncomputable def ZJ (j : Nat) : Nat := pc (pc (CG j) TZ) (CGI j)

@[expose] noncomputable def ok (p : Nat) : Bool := andB (cn p) (andB (cn (pinv p)) (pk p (pinv p)))

@[expose] noncomputable def okI (p q : Nat) : Bool := andB (cn p) (andB (cn q) (pk p q))

theorem kInv : andB (ok TA) (andB (ok TB) (andB (ok TL) (andB (ok TAl) (andB (ok TBl)
    (andB (cn TZ) (andB (allN 4 fun i => ok (SG i))
      (allN 7 fun j => okI (CG j) (CGI j)))))))) = true := by
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
        SE.SRI 0 16)))) = true := by
  quickRfl

@[expose] noncomputable def enumSl (lo : Nat) : Bool :=
  penumSlK 4060 12 (mask 12) (4060 * 12) false SE.G SE.GI 4 SE.cnt SE.T SE.PL SE.POS SE.SRT SE.SRI lo 16

theorem kEnum1 : enumSl 16 = true := by quickRfl
theorem kEnum2 : enumSl 32 = true := by quickRfl
theorem kEnum3 : enumSl 48 = true := by quickRfl

@[expose] noncomputable def coverPt (x : Nat) : Bool :=
  orB (Nat.beq x e) (orB (notB (invPt 4060 12 x)) (orB (notB (allN 7 fun j => notB (Nat.beq x (ZJ j))))
    (notB (allN 4 fun g => commPt 4060 12 x (SG g)))))

theorem kCover : allN 64 (fun t => strictB (SE.T t) coverPt) = true := by
  quickRfl

theorem kNeg : notB (Nat.beq (pc TZ TZ) TZ) = true := by quickRfl

end CertificateChecks.KernelSporSch.TMem27100

end
