module

public import Certificates.Data.Kernel.ThCensus.Defs
public import Certificates.Kernel.ThCensus.Data
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_const
public import CFSG.Certificates.Kernel.Th.S.Data.Seed_const
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelThCensus

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.ThCensus CFSG.KD.ThCensus

theorem ch17305L :
    andB (Nat.beq (lenN slp) 3) (andB (Nat.beq (slpStart slp 3) nreg) (andB (regsIn pr 10 nreg)
      (andB (regBelow regX1 nreg) (andB (regBelow regX2 nreg) (andB (regBelow regB2 nreg)
        (andB (regBelow regS nreg) (andB (regBelow regU nreg) (Nat.beq regZ (regAt pr 9))))))))) =
      true := by
  quickRfl

theorem ch17305S : seedsOK RB CFSG.KD.ThSeed.SA CFSG.KD.ThSeed.SB = true := by quickRfl

@[expose] noncomputable def ch17305R (i : Nat) : Bool :=
  slpChunkOK RB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE slp i

#kc_each ch17305R 0 3

theorem ch17305W : pwOK RB PW CFSG.KD.ThS.c CFSG.KD.ThS.rm pr 10 3 = true := by quickRfl

theorem ch17305P :
    Nat.beq (runPc RB PW CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE pr 10 3 2 pc 1) 11 = true := by
  quickRfl

end CertificateChecks.KernelThCensus

end
