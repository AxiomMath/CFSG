module

public import Certificates.Kernel.LocalComp.HeAutPin
public import Certificates.Kernel.LocalComp.HeSylEnum
public import CFSG.Certificates.Kernel.HeSylowQEKSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeSylowTests

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelLC.HeSylowQECheck

open CFSG.KC.BfsPin CFSG.KC.HexaK CFSG.KC.HeAutK CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw
open CFSG.ComponentClassification.AS81.HeSylow CertificateChecks.KernelLC
open CertificateChecks.KernelLC.HeAutCheck

@[expose] noncomputable def Pz16 : Nat := packA 5 heSylZ16.toList

@[expose] noncomputable def gensPerm16 (g : Nat) (G : Nat → Nat) : Bool :=
  allN g fun k => permOK 16 5 (mask 5) (16 * 5) (G k) (pinvS 16 5 (mask 5) (G k))

theorem kBindX16 : (Nat.beq heSyl16.toArray.size HeSylX.ng &&
    allN HeSylX.ng fun k => bindArrK heSyl16.toArray[k]! 16 5 (HeSylX.G k)) = true := by quickRfl

theorem kBindQ16 : (Nat.beq heSylQ16.toArray.size HeSylQ.ng &&
    allN HeSylQ.ng fun k => bindArrK heSylQ16.toArray[k]! 16 5 (HeSylQ.G k)) = true := by quickRfl

theorem kBindE16 : (Nat.beq heSylE16.toArray.size HeSylE.ng &&
    allN HeSylE.ng fun k => bindArrK heSylE16.toArray[k]! 16 5 (HeSylE.G k)) = true := by quickRfl

theorem kBindF16 : (Nat.beq heSylF16.toArray.size HeSylF.ng &&
    allN HeSylF.ng fun k => bindArrK heSylF16.toArray[k]! 16 5 (HeSylF.G k)) = true := by quickRfl

theorem kBindZ16 : bindArrK heSylZ16 16 5 Pz16 = true := by quickRfl

theorem kPerm16 : (gensPerm16 HeSylX.ng HeSylX.G && gensPerm16 HeSylQ.ng HeSylQ.G &&
    gensPerm16 HeSylE.ng HeSylE.G && gensPerm16 HeSylF.ng HeSylF.G &&
    permOK 16 5 (mask 5) (16 * 5) Pz16 (pinvS 16 5 (mask 5) Pz16)) = true := by quickRfl

theorem k16 : (interK HeSylE.N HeSylE.T HeSylQ.N HeSylQ.T 16 48 &&
    interK HeSylF.N HeSylF.T HeSylQ.N HeSylQ.T 16 48 &&
    centK 16 5 HeSylX.N HeSylX.T HeSylQ.ng HeSylQ.G Pz16) = true := by quickRfl

theorem k32 : (interK HeAutE.N HeAutE.T HeAutQ.N HeAutQ.T 16 48 &&
    interK HeAutF.N HeAutF.T HeAutQ.N HeAutQ.T 16 48 &&
    centK 32 6 HeAutY.N HeAutY.T HeAutQ.ng HeAutQ.G Pz) = true := by quickRfl

theorem pin16 {gs : List (Array Nat)} {g N : Nat} {G T E S : Nat → Nat}
    (hb : (Nat.beq gs.toArray.size g && allN g fun k => bindArrK gs.toArray[k]! 16 5 (G k)) = true)
    (hp : gensPerm16 g G = true) (hk : bfsK 16 5 g G N T E S = true) (hf : N ≤ 4000) :
    Pin 16 5 gs g G N T E S :=
  ⟨(binds_of_check hb).1, (binds_of_check hb).2, allN_spec hp, hk, hf⟩

theorem heSylowQECheck_true : heSylowQECheck = true := by
  have kp := kPerm16
  simp only [Bool.and_eq_true] at kp
  obtain ⟨⟨⟨⟨pX, pQ⟩, pE⟩, pF⟩, pz⟩ := kp
  have kq := kPermG
  simp only [Bool.and_eq_true] at kq
  obtain ⟨⟨⟨⟨qY, qQ⟩, qE⟩, qF⟩, -⟩ := kq
  rw [heSylowQECheck_eq]
  exact heSylowQEK_sound (pin16 kBindE16 pE HeSylE.ok (by decide))
    (pin16 kBindF16 pF HeSylF.ok (by decide)) (pin16 kBindQ16 pQ HeSylQ.ok (by decide))
    (pin16 kBindX16 pX HeSylX.ok (by decide)) (pin kBindE qE HeAutE.ok (by decide))
    (pin kBindF qF HeAutF.ok (by decide)) (pin kBindQ qQ HeAutQ.ok (by decide)) (pinY qY)
    (unpack_eq_of_bindArrK kBindZ16) (unpack_eq_of_bindArrK kBindZ) pz kPermZ k16 k32

end CertificateChecks.KernelLC.HeSylowQECheck

end
