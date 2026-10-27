module

public import Certificates.Kernel.Om1K.Elts
public import Certificates.Kernel.LocalComp.E8Tables
public meta import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelOm1.A

open CFSG.KC.Enum CFSG.KS
open CertificateChecks.KernelOm2 (pc2 wAK)
open CertificateChecks.KernelLC.E8 (FT NEG)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Data
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check (wT wCa wCc repMasks)

theorem kEL : allN 6 (fun k => Nat.beq (EL.G k) (wAK (elW.getD k []))) = true := by quickRfl
theorem kTG : allN 7 (fun k => Nat.beq (TG.G k) (wAK (wT.getD k []))) = true := by quickRfl
theorem kCA : allN 8 (fun k => Nat.beq (CA.G k) (wAK (wCa.getD k []))) = true := by quickRfl
theorem kCC : allN 5 (fun k => Nat.beq (CC.G k) (wAK (wCc.getD k []))) = true := by quickRfl
theorem kWS : allN 8 (fun k => Nat.beq (WS.G k) (wAK (wSub.getD k []))) = true := by quickRfl
theorem kXG : allN 7 (fun k => Nat.beq (XG.G k) (wAK (wX.getD k []))) = true := by quickRfl
theorem kXI : allN 7 (fun k => Nat.beq (XI.G k) (wAK (wXr.getD k []))) = true := by quickRfl

theorem kLens : elW.length = 6 ∧ wT.length = 7 ∧ wCa.length = 8 ∧ wCc.length = 5 ∧
    wSub.length = 8 ∧ wX.length = 7 ∧ wXr.length = 7 := by decide +kernel

theorem kS1 : Nat.beq (pc2 (EL.G 3) (EL.G 5)) pid1 = true := by quickRfl

theorem kXinv : allN 7 (fun k => Nat.beq (pc2 (XG.G k) (XI.G k)) pid1) = true := by quickRfl

theorem kR0 : Nat.beq (EL.G 0) (FT 15) = true := by quickRfl

theorem kR1 : Nat.beq (pc2 (EL.G 1) (EL.G 1)) (FT 15) = true := by quickRfl

theorem kR2 : Nat.beq (pc2 (EL.G 2) (EL.G 2)) (FT 15) = true := by quickRfl

theorem kR3 : Nat.beq (pc2 (EL.G 1) (pc2 (EL.G 2) (EL.G 1))) (EL.G 2) = true := by quickRfl

theorem kR4 : Nat.beq (pc2 (EL.G 4) (FT 15)) (pc2 (pc2 (FT 15) NEG) (EL.G 4)) = true := by
  quickRfl

theorem kR5 : bAnd(allN 7 (fun k => cmK (TG.G k) (FT 15)), cmK (EL.G 3) (FT 15)) = true := by
  quickRfl

theorem kR6 : allN 8 (fun k => cmK (CA.G k) (FT 3)) = true := by quickRfl

theorem kR7 : allN 5 (fun k => cmK (CC.G k) (FT 23)) = true := by quickRfl

theorem kR8 : Nat.beq (FT 252) (pc2 NEG (FT 3)) = true := by quickRfl

@[expose] noncomputable def maskOK (j : Nat) : Bool :=
  let d := maskData.getD j (0, 0, [])
  bAnd(Nat.blt d.2.1 4,
    strictB (wAK d.2.2) fun g => Nat.beq (pc2 g (FT d.1)) (pc2 (FT (repMasks.getD d.2.1 0)) g))

@[expose] noncomputable def maskOKc (c : Nat) : Bool :=
  allN 14 fun d => maskOK (Nat.add (Nat.mul 14 c) d)

theorem kMaskLen : maskData.length = 126 := by decide +kernel

@[expose] noncomputable def r0L : List Nat := q8L (EL.G 1) (EL.G 2)

theorem kQa : r0L.all (fun a => r0L.all fun b => strictB (pc2 a b) fun c => r0L.any (Nat.beq c)) =
    true := by quickRfl

theorem kQb : r0L.all (fun a => r0L.any fun b => Nat.beq (pc2 a b) pid1) = true := by quickRfl

end CertificateChecks.KernelOm1.A

#kc_each CertificateChecks.KernelOm1.A.maskOKc 0 9

end
