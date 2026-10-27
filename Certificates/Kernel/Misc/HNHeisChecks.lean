module

public import Certificates.Data.Kernel.Misc.HNHeis
public import Certificates.Kernel.SporSch.HN.Seeds2106K
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.HNCheck
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHNHeis

open CFSG.KC.Misc.HNHeis CFSG.KS.SporSch.LyM CertificateChecks.KernelSporSch
open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

@[expose] noncomputable def AK : Nat := payRunP 5 133 13 1729 HNSeedA.chars 0 0 0

@[expose] noncomputable def BK : Nat := payRunP 5 133 13 1729 HNSeedB.chars 0 0 0

@[expose] noncomputable def RK : List Nat := slpH AK BK hnHeisProg

theorem consts_ok : constsH = true := by quickRfl

theorem seeds_ok : (vldH AK && vldH BK) = true := by quickRfl

theorem heis_ok :
    (relH RK [hnHeisX1, hnHeisX1, hnHeisX1, hnHeisX1, hnHeisX1] [] &&
      relH RK [hnHeisX2, hnHeisX2, hnHeisX2, hnHeisX2, hnHeisX2] [] &&
      relH RK [hnHeisY1, hnHeisY1, hnHeisY1, hnHeisY1, hnHeisY1] [] &&
      relH RK [hnHeisY2, hnHeisY2, hnHeisY2, hnHeisY2, hnHeisY2] [] &&
      relH RK [hnHeisZ, hnHeisZ, hnHeisZ, hnHeisZ, hnHeisZ] [] &&
      relH RK [hnHeisX1, hnHeisZ] [hnHeisZ, hnHeisX1] &&
      relH RK [hnHeisX2, hnHeisZ] [hnHeisZ, hnHeisX2] &&
      relH RK [hnHeisY1, hnHeisZ] [hnHeisZ, hnHeisY1] &&
      relH RK [hnHeisY2, hnHeisZ] [hnHeisZ, hnHeisY2] &&
      relH RK [hnHeisX1, hnHeisY1] [hnHeisY1, hnHeisX1, hnHeisZ] &&
      relH RK [hnHeisX2, hnHeisY2] [hnHeisY2, hnHeisX2, hnHeisZ] &&
      relH RK [hnHeisX1, hnHeisX2] [hnHeisX2, hnHeisX1] &&
      relH RK [hnHeisY1, hnHeisY2] [hnHeisY2, hnHeisY1] &&
      relH RK [hnHeisX1, hnHeisY2] [hnHeisY2, hnHeisX1] &&
      relH RK [hnHeisX2, hnHeisY1] [hnHeisY1, hnHeisX2] &&
      !(Nat.beq (regH RK (hnHeisZ - 1)) ONEH)) = true := by
  quickRfl

end CertificateChecks.KernelHNHeis

end
