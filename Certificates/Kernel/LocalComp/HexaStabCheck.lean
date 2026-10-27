module

public import Certificates.Kernel.LocalComp.HexaCheck
public import Certificates.Kernel.LocalComp.HexaStabEnum
public import CFSG.Certificates.Kernel.HexaStabKSound
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sporadic.ON.Gen

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.HexaStabCheck

open CFSG.KC.BfsPin CFSG.KC.HexaK CFSG.KC.HexaStabK CFSG.KC.Enum CFSG.KS CFSG.KS.Prim
open CFSG.KS.Raw CFSG.ComponentClassification.AS81.Hexa CertificateChecks.KernelLC
open CertificateChecks.KernelLC.HexaOrb CertificateChecks.KernelLC.HexaCheck
open CFSG.KLie.CT (pw2)

theorem kBindM2 : (Nat.beq hexaM2Gens.toArray.size HexaM2.ng &&
    allN HexaM2.ng fun k => bindArrK hexaM2Gens.toArray[k]! 64 7 (HexaM2.G k)) = true := by
  quickRfl

theorem kPermM2 : gensPerm HexaM2.ng HexaM2.G = true := by quickRfl

theorem kTransl : (Nat.beq HexaT.ng 6 && allN 6 (fun k => Nat.beq (HexaT.G k) (translK 7 (pw2 k))) &&
    Nat.beq HexaR.ng 2 && Nat.beq (HexaR.G 0) (translK 7 1) && Nat.beq (HexaR.G 1) (translK 7 2)) =
    true := by quickRfl

theorem kOval : ovalOK hexaOval = true := by quickRfl

theorem kM2 : (Nat.beq HexaM2.N 2160 && allN HexaM2.ng (fun k => inL HexaM.N HexaM.T (HexaM2.G k)) &&
    allN HexaM2.ng (fun k => Nat.beq (pow4 64 7 (HexaM2.G k)) (pidn 64 7))) = true := by quickRfl

theorem kComp : ovalCompNG hexaOval = true := by decide +kernel

@[expose] noncomputable def blk (i : Nat) : Bool :=
  stabBlockK 7 hexaOval (ovalPairsG hexaOval) HexaM.N HexaM.T hexaStabW i

end CertificateChecks.KernelLC.HexaStabCheck

set_option Elab.async false

#kon_slices CertificateChecks.KernelLC.HexaStabCheck.blk 0 36
#kon_join CertificateChecks.KernelLC.HexaStabCheck.blkAll
  CertificateChecks.KernelLC.HexaStabCheck.blk 36

namespace CertificateChecks.KernelLC.HexaStabCheck

open CFSG.KC.BfsPin CFSG.KC.HexaK CFSG.KC.HexaStabK CFSG.KC.Enum CFSG.KS CFSG.KS.Prim
open CFSG.KS.Raw CFSG.ComponentClassification.AS81.Hexa CertificateChecks.KernelLC
open CertificateChecks.KernelLC.HexaOrb CertificateChecks.KernelLC.HexaCheck

theorem blocks : ∀ i < (ovalPairsG hexaOval).length, blk i = true := by
  have hL : (ovalPairsG hexaOval).length = 36 := by decide
  rw [hL]
  exact blkAll

theorem hexaStabCheck_true : hexaStabCheck = true := by
  have kp := kPermG
  simp only [Bool.and_eq_true] at kp
  rw [hexaStabCheck_eq]
  exact hexaStabK_sound (binds_of_check kBindT) (binds_of_check kBindR)
    (pin kBindM kp.1.1.1.1.2 HexaM.ok (by decide)) (pin kBindM2 kPermM2 HexaM2.ok (by decide))
    kTransl kOval blocks kM2 kComp

end CertificateChecks.KernelLC.HexaStabCheck

end
