module

public import Certificates.Kernel.Fi22F.TabSData
public import Certificates.Kernel.Fi22F.TabParts
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelFi22F

open CFSG.KC CFSG.KC.LceS CFSG.KC.LceJson CFSG.Certificates.LCE CFSG.KD.FiFS

namespace TabS

theorem inv : invOK INV INV8 (nat_lit 12) = true := by quickRfl

theorem words : wordsOK (selW WT m) (sel1 RT) (sel1 ST) INV INV8 m HS = true := by quickRfl

theorem hints : CFSG.KC.Bind.hintsOK (selW WT m) m (nat_lit 204) (nat_lit 73) HS = true := by
  quickRfl

theorem alive : aliveOK (sel1 LV) mLV nC a = true := by quickRfl

theorem norm : relsNorm (sel1 RT) (nat_lit 204) = true := by quickRfl

theorem run :
    Nat.beq (runFacts (sel2 B) (selW WT m) INV nC (nat_lit 12) JF (mkS (nat_lit 0) (nat_lit 1))) S1 = true := by
  quickRfl

theorem cov : Nat.beq (runCover (sel2 B) (sel1 LV) nf (nat_lit 12) JV (nat_lit 1)) X1 = true := by
  quickRfl

end TabS

theorem tabS_ok : tabOk B WT RT ST LV INV INV8 (nat_lit 12) nC mLV a m HS (nat_lit 204) (nat_lit 73) nf JF JV
    S1 X1 = true := by
  unfold tabOk lceOk
  rw [TabS.inv, TabS.words, TabS.hints, TabS.alive, wtPer_selW, TabS.norm, TabS.run,
    TabS.cov]
  quickRfl

end CertificateChecks.KernelFi22F

end
