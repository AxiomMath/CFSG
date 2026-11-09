module

public import Certificates.Kernel.Fi22F.TabHData
public import Certificates.Kernel.Fi22F.TabParts
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelFi22F

open CFSG.KC CFSG.KC.LceS CFSG.KC.LceJson CFSG.Certificates.LCE CFSG.KD.FiFH

namespace TabH

theorem inv : invOK INV INV8 (nat_lit 12) = true := by quickRfl

theorem words : wordsOK (selW WT m) (sel1 RT) (sel1 ST) INV INV8 m HS = true := by quickRfl

theorem hints : CFSG.KC.Bind.hintsOK (selW WT m) m (nat_lit 204) (nat_lit 8) HS = true := by
  quickRfl

theorem alive : aliveOK (sel1 LV) mLV nC a = true := by quickRfl

theorem norm : relsNorm (sel1 RT) (nat_lit 204) = true := by quickRfl

theorem run :
    Nat.beq (runFacts (sel2 B) (selW WT m) INV nC (nat_lit 12) JF (mkS (nat_lit 0) (nat_lit 1))) S1 = true := by
  quickRfl

theorem cov : Nat.beq (runCover (sel2 B) (sel1 LV) nf (nat_lit 12) JV (nat_lit 1)) X1 = true := by
  quickRfl

end TabH

theorem tabH_ok : tabOk B WT RT ST LV INV INV8 (nat_lit 12) nC mLV a m HS (nat_lit 204) (nat_lit 8) nf JF JV
    S1 X1 = true := by
  unfold tabOk lceOk
  rw [TabH.inv, TabH.words, TabH.hints, TabH.alive, wtPer_selW, TabH.norm, TabH.run,
    TabH.cov]
  quickRfl

end CertificateChecks.KernelFi22F

end
