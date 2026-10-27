module

public import Certificates.Kernel.Om2K.OrbDefs
public meta import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.Each
public import Certificates.Data.Holder1711.Om2Check
public import Certificates.Data.Kernel.BfsPin
public import Certificates.Kernel.Om2K.Defs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelOm2

open CFSG.KC.Enum CFSG.KC.SetOrb CFSG.KC.BfsPin

theorem kDist : distinctK 6300 (fun i => keyK 240 9 48 (Orb.C i)) Orb.S = true := by quickRfl

theorem kF0 : Nat.beq (eqMaskK 480 9 (EL.G 0) (cAK 2)) (Orb.M 0) = true := by quickRfl

theorem kN : Orb.N = 6300 := rfl

theorem kCov : allN 6300 covK = true := by quickRfl

theorem kSub0 : subOK Sub.c0.N Sub.c0.X Sub.c0.Y Sub.c0.E Sub.c0.D (WS.G 0) = true := by quickRfl
theorem kSub1 : subOK Sub.c1.N Sub.c1.X Sub.c1.Y Sub.c1.E Sub.c1.D (WS.G 1) = true := by quickRfl
theorem kSub2 : subOK Sub.c2.N Sub.c2.X Sub.c2.Y Sub.c2.E Sub.c2.D (WS.G 2) = true := by quickRfl
theorem kSub3 : subOK Sub.c3.N Sub.c3.X Sub.c3.Y Sub.c3.E Sub.c3.D (WS.G 3) = true := by quickRfl
theorem kSub4 : subOK Sub.c4.N Sub.c4.X Sub.c4.Y Sub.c4.E Sub.c4.D (WS.G 4) = true := by quickRfl
theorem kSub5 : subOK Sub.c5.N Sub.c5.X Sub.c5.Y Sub.c5.E Sub.c5.D (WS.G 5) = true := by quickRfl
theorem kSub6 : subOK Sub.c6.N Sub.c6.X Sub.c6.Y Sub.c6.E Sub.c6.D (WS.G 6) = true := by quickRfl
theorem kSub7 : subOK Sub.c7.N Sub.c7.X Sub.c7.Y Sub.c7.E Sub.c7.D (WS.G 7) = true := by quickRfl
theorem kSub8 : subOK Sub.c8.N Sub.c8.X Sub.c8.Y Sub.c8.E Sub.c8.D (WS.G 8) = true := by quickRfl
theorem kSub9 : subOK Sub.c9.N Sub.c9.X Sub.c9.Y Sub.c9.E Sub.c9.D (WS.G 9) = true := by quickRfl
theorem kSub10 : subOK Sub.c10.N Sub.c10.X Sub.c10.Y Sub.c10.E Sub.c10.D (WS.G 10) = true := by
  quickRfl
theorem kSub11 : subOK Sub.c11.N Sub.c11.X Sub.c11.Y Sub.c11.E Sub.c11.D (WS.G 11) = true := by
  quickRfl

theorem kTr0 : transOK Tr.c0.N Tr.c0.X Tr.c0.Y Tr.c0.E Tr.c0.D (WS.G 0) = true := by quickRfl
theorem kTr1 : transOK Tr.c1.N Tr.c1.X Tr.c1.Y Tr.c1.E Tr.c1.D (WS.G 1) = true := by quickRfl
theorem kTr2 : transOK Tr.c2.N Tr.c2.X Tr.c2.Y Tr.c2.E Tr.c2.D (WS.G 2) = true := by quickRfl
theorem kTr3 : transOK Tr.c3.N Tr.c3.X Tr.c3.Y Tr.c3.E Tr.c3.D (WS.G 3) = true := by quickRfl
theorem kTr4 : transOK Tr.c4.N Tr.c4.X Tr.c4.Y Tr.c4.E Tr.c4.D (WS.G 4) = true := by quickRfl
theorem kTr5 : transOK Tr.c5.N Tr.c5.X Tr.c5.Y Tr.c5.E Tr.c5.D (WS.G 5) = true := by quickRfl
theorem kTr6 : transOK Tr.c6.N Tr.c6.X Tr.c6.Y Tr.c6.E Tr.c6.D (WS.G 6) = true := by quickRfl
theorem kTr7 : transOK Tr.c7.N Tr.c7.X Tr.c7.Y Tr.c7.E Tr.c7.D (WS.G 7) = true := by quickRfl
theorem kTr8 : transOK Tr.c8.N Tr.c8.X Tr.c8.Y Tr.c8.E Tr.c8.D (WS.G 8) = true := by quickRfl
theorem kTr9 : transOK Tr.c9.N Tr.c9.X Tr.c9.Y Tr.c9.E Tr.c9.D (WS.G 9) = true := by quickRfl
theorem kTr10 : transOK Tr.c10.N Tr.c10.X Tr.c10.Y Tr.c10.E Tr.c10.D (WS.G 10) = true := by
  quickRfl
theorem kTr11 : transOK Tr.c11.N Tr.c11.X Tr.c11.Y Tr.c11.E Tr.c11.D (WS.G 11) = true := by
  quickRfl

end CertificateChecks.KernelOm2

#kc_each CertificateChecks.KernelOm2.orbOKc 0 63

end
