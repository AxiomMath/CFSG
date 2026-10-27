module

public import Certificates.Kernel.Om1K.OrbDefs
public meta import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelOm1.A

open CFSG.KC.Enum CFSG.KC.SetOrb CFSG.KC.BfsPin
open CertificateChecks.KernelLC.E8 (FT NEG)

theorem kNO : Orb.N = 3150 := rfl

theorem kDist : distinctK 3150 (fun i => keyK 240 8 24 (Orb.C i)) Orb.S = true := by quickRfl

theorem kF0 : Nat.beq (eqMaskK 240 8 (FT 15) NEG) (Orb.M 0) = true := by quickRfl

theorem kSub0 : subOK Sub.c0.N Sub.c0.X Sub.c0.D (WS.G 0) = true := by quickRfl
theorem kSub1 : subOK Sub.c1.N Sub.c1.X Sub.c1.D (WS.G 1) = true := by quickRfl
theorem kSub2 : subOK Sub.c2.N Sub.c2.X Sub.c2.D (WS.G 2) = true := by quickRfl
theorem kSub3 : subOK Sub.c3.N Sub.c3.X Sub.c3.D (WS.G 3) = true := by quickRfl
theorem kSub4 : subOK Sub.c4.N Sub.c4.X Sub.c4.D (WS.G 4) = true := by quickRfl
theorem kSub5 : subOK Sub.c5.N Sub.c5.X Sub.c5.D (WS.G 5) = true := by quickRfl
theorem kSub6 : subOK Sub.c6.N Sub.c6.X Sub.c6.D (WS.G 6) = true := by quickRfl
theorem kSub7 : subOK Sub.c7.N Sub.c7.X Sub.c7.D (WS.G 7) = true := by quickRfl

theorem kTrN : Tr.c0.N = 3150 ∧ Tr.c1.N = 3150 ∧ Tr.c2.N = 3150 ∧ Tr.c3.N = 3150 ∧
    Tr.c4.N = 3150 ∧ Tr.c5.N = 3150 ∧ Tr.c6.N = 3150 ∧ Tr.c7.N = 3150 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem kTr0 : transOK Tr.c0.N Tr.c0.X Tr.c0.Y Tr.c0.D (WS.G 0) = true := by quickRfl
theorem kTr1 : transOK Tr.c1.N Tr.c1.X Tr.c1.Y Tr.c1.D (WS.G 1) = true := by quickRfl
theorem kTr2 : transOK Tr.c2.N Tr.c2.X Tr.c2.Y Tr.c2.D (WS.G 2) = true := by quickRfl
theorem kTr3 : transOK Tr.c3.N Tr.c3.X Tr.c3.Y Tr.c3.D (WS.G 3) = true := by quickRfl
theorem kTr4 : transOK Tr.c4.N Tr.c4.X Tr.c4.Y Tr.c4.D (WS.G 4) = true := by quickRfl
theorem kTr5 : transOK Tr.c5.N Tr.c5.X Tr.c5.Y Tr.c5.D (WS.G 5) = true := by quickRfl
theorem kTr6 : transOK Tr.c6.N Tr.c6.X Tr.c6.Y Tr.c6.D (WS.G 6) = true := by quickRfl
theorem kTr7 : transOK Tr.c7.N Tr.c7.X Tr.c7.Y Tr.c7.D (WS.G 7) = true := by quickRfl

end CertificateChecks.KernelOm1.A

#kc_each CertificateChecks.KernelOm1.A.orbOKc 0 63

end
