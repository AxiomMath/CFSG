module

public import Certificates.Kernel.Sporadic.OddCore.Suz27215D
public import Certificates.Kernel.Sporadic.SuzInv.Text3
public import Certificates.Data.Kernel.CoverScan
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzOuterData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.S27215

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CertificateChecks.KernelSpor
open CFSG.KC.CoverScan CFSG.EvenSporadicStandard.SuzOuter
open CFSG.KLie.CT (andB notB)

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 1782 11 (mask 11) p q

@[expose] noncomputable def e : Nat := pidn 1782 11

@[expose] noncomputable def cn (p : Nat) : Bool := canonK 1782 11 (mask 11) (1782 * 11) p

@[expose] noncomputable def letK (j : Nat) : Nat := nIf(Nat.blt j 5, SOA.G j, SOA.GI (Nat.sub j 5))

@[expose] noncomputable def wfK (G : Nat → Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) e (fun l _ ih => strictN ih fun acc => pc (G l) acc) w

@[expose] noncomputable def ON (o : Nat) : Nat := nIf(Nat.beq o 0, SOA.cnt, nIf(Nat.beq o 1, SOB.cnt, SOC.cnt))

@[expose] noncomputable def OT (o j : Nat) : Nat :=
  nIf(Nat.beq o 0, SOA.T j, nIf(Nat.beq o 1, SOB.T j, SOC.T j))

theorem kGens : andB (Nat.beq SOA.k 5) (allN 5 fun j =>
    andB (Nat.beq (SOA.G j) (SuzInvT3.F (Nat.add 20 j))) (andB (cn (SOA.G j))
      (andB (cn (SOA.GI j)) (Nat.beq (pc (SOA.G j) (SOA.GI j)) e)))) = true := by
  quickRfl

theorem kShare : andB (andB (Nat.beq SOB.k 5) (Nat.beq SOC.k 5)) (allN 5 fun j =>
    andB (Nat.beq (SOB.G j) (SOA.G j)) (andB (Nat.beq (SOB.GI j) (SOA.GI j))
      (andB (Nat.beq (SOC.G j) (SOA.G j)) (Nat.beq (SOC.GI j) (SOA.GI j))))) = true := by
  quickRfl

theorem kP : andB (Nat.beq SOP.k 3) (allN 3 fun j =>
    andB (Nat.beq (SOP.G j) (wfK letK (wordsP.getD j []))) (cn (SOP.G j))) = true := by
  quickRfl

theorem kHd : andB (andB (Nat.beq SOP.cnt 256) (penumHdK e SOP.cnt 256 SOP.T SOP.PL))
    (andB (andB (Nat.beq SOA.cnt 315)
      (penumHdK (wfK SOP.G (repWords.getD 0 [])) SOA.cnt 315 SOA.T SOA.PL))
    (andB (andB (Nat.beq SOB.cnt 2520)
      (penumHdK (wfK SOP.G (repWords.getD 1 [])) SOB.cnt 2520 SOB.T SOB.PL))
    (andB (andB (Nat.beq SOC.cnt 1800)
      (penumHdK (wfK SOP.G (repWords.getD 2 [])) SOC.cnt 1800 SOC.T SOC.PL))
    (andB (andB (Nat.beq SOE.cnt 128) (andB (Nat.beq SOE.k 4)
      (penumHdK e SOE.cnt 128 SOE.T SOE.PL)))
      (allN 4 fun j => andB (cn (SOE.G j)) (Nat.beq (SOE.G j)
        (pc (SOA.T (pairsE.getD j (0, 0)).1) (SOA.T (pairsE.getD j (0, 0)).2)))))))) = true := by
  quickRfl

@[expose] noncomputable def aSl (s : Nat) : Bool :=
  penumSlK 1782 11 (mask 11) (1782 * 11) true SOA.G SOA.GI 5 SOA.cnt SOA.T SOA.PL SOA.POS SOA.SRT
    SOA.SRI (Nat.mul s (nat_lit 45)) (nat_lit 45)

@[expose] noncomputable def bSl (s : Nat) : Bool :=
  penumSlK 1782 11 (mask 11) (1782 * 11) true SOB.G SOB.GI 5 SOB.cnt SOB.T SOB.PL SOB.POS SOB.SRT
    SOB.SRI (Nat.mul s (nat_lit 45)) (nat_lit 45)

@[expose] noncomputable def cSl (s : Nat) : Bool :=
  penumSlK 1782 11 (mask 11) (1782 * 11) true SOC.G SOC.GI 5 SOC.cnt SOC.T SOC.PL SOC.POS SOC.SRT
    SOC.SRI (Nat.mul s (nat_lit 45)) (nat_lit 45)

@[expose] noncomputable def pSl (_s : Nat) : Bool :=
  penumSlK 1782 11 (mask 11) (1782 * 11) false SOP.G SOP.GI 3 SOP.cnt SOP.T SOP.PL SOP.POS SOP.SRT
    SOP.SRI (nat_lit 0) (nat_lit 256)

@[expose] noncomputable def eSl (_s : Nat) : Bool :=
  penumSlK 1782 11 (mask 11) (1782 * 11) false SOE.G SOE.GI 4 SOE.cnt SOE.T SOE.PL SOE.POS SOE.SRT
    SOE.SRI (nat_lit 0) (nat_lit 128)

@[expose] noncomputable def covSl (_s : Nat) : Bool :=
  allN 256 fun i => coverK 1782 11 3 ON OT e (r32 SOW i) (SOP.T i)

theorem kNeg : notB (coverK 1782 11 3 ON OT e (Nat.add (r32 SOW 1) 1) (SOP.T 1)) = true := by
  quickRfl

end CertificateChecks.KernelSpor.S27215

end
