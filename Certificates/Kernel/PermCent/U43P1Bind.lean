module

public import Certificates.Data.Kernel.PermCent.U43P1Chk
public import Certificates.Kernel.PermCent.U43P1A6
public import Certificates.Kernel.PermCent.U43P1Fa
public import Certificates.Kernel.PermCent.U43P1Fb
public import Certificates.Kernel.PermCent.U43P1Ia
public import Certificates.Kernel.PermCent.U43P1In
public import Certificates.Kernel.PermCent.U43P1M1a
public import Certificates.Kernel.PermCent.U43P1M1b

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.KernelPermCent.U43P1

open CFSG.ComponentClassification.HarrisLit.P1.U43.Cover CFSG.LieType.Multipliers.U43
open CFSG.KC.Enum CFSG.KS

theorem bindsC :
    (tabOK tabA (CIn.G 0) && tabOK tabB (CIn.G 1) && matOK repIn.1 repIn.2 (CIn.T CIn.r0) &&
      tabOK tabA (CM1a.G 0) && tabOK tabB (CM1a.G 1) &&
      matOK repM1a.1 repM1a.2 (CM1a.T CM1a.r0) &&
      tabOK tabA (CM1b.G 0) && tabOK tabB (CM1b.G 1) &&
      matOK repM1b.1 repM1b.2 (CM1b.T CM1b.r0) &&
      tabOK tabA (CFa.G 0) && tabOK tabB (CFa.G 1) && matOK repFa.1 repFa.2 (CFa.T CFa.r0) &&
      tabOK tabA (CFb.G 0) && tabOK tabB (CFb.G 1) && matOK repFb.1 repFb.2 (CFb.T CFb.r0) &&
      tabOK tabA (CIa.G 0) && tabOK tabB (CIa.G 1) &&
      matOK repIa.1 repIa.2 (CIa.T CIa.r0)) = true ∧
    CIn.N = 2835 ∧ CM1a.N = 4536 ∧ CM1b.N = 540 ∧ CFa.N = 5670 ∧ CFb.N = 126 ∧ CIa.N = 4536 ∧
    CIn.ng = 2 ∧ CM1a.ng = 2 ∧ CM1b.ng = 2 ∧ CFa.ng = 2 ∧ CFb.ng = 2 ∧ CIa.ng = 2 ∧
    CIn.r0 < 2835 ∧ CM1a.r0 < 4536 ∧ CM1b.r0 < 540 ∧ CFa.r0 < 5670 ∧ CFb.r0 < 126 ∧
    CIa.r0 < 4536 := by
  decide +kernel

theorem bindsD :
    (dgOK (lM1a.getD 0 0) (a6Gens.getD 0 []) (DgM1a.G 0) &&
      dgOK (lM1a.getD 1 0) (a6Gens.getD 1 []) (DgM1a.G 1) &&
      dgOK (lIa.getD 0 0) (a6Gens.getD 0 []) (DgIa.G 0) &&
      dgOK (lIa.getD 1 0) (a6Gens.getD 1 []) (DgIa.G 1) &&
      y6OK (a6Gens.getD 0 []) (Y6.G 0) && y6OK (a6Gens.getD 1 []) (Y6.G 1) &&
      Nat.beq (DgM1a.T 0) (pidn 826 10) && Nat.beq (DgIa.T 0) (pidn 826 10) &&
      Nat.beq (Y6.T 0) (pidn 6 3)) = true ∧
    DgM1a.N = 360 ∧ DgIa.N = 360 ∧ Y6.N = 360 ∧ DgM1a.ng = 2 ∧ DgIa.ng = 2 ∧ Y6.ng = 2 := by
  decide +kernel

end CertificateChecks.KernelPermCent.U43P1

end
