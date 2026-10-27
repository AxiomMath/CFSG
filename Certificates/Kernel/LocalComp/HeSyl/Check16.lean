module

public import Certificates.Kernel.LocalComp.HeSylEnum
public import Certificates.Kernel.LocalComp.HeSyl.Flags
public import CFSG.Certificates.Kernel.HeSylKSound
public import CFSG.Certificates.Kernel.LocalCompUnpack
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelLC.HeSyl

open CFSG.KC.BfsPin CFSG.KC.HexaK CFSG.KC.HeAutK CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw
open CFSG.ComponentClassification.AS81.HeSylow CertificateChecks.KernelLC

@[expose] noncomputable def Pz : Nat := packA 5 heSylZ16.toList

@[expose] noncomputable def Pr : Nat := packA 5 heSylR16.toList

@[expose] noncomputable def Ps : Nat := packA 5 heSylS16.toList

@[expose] noncomputable def gensPerm (g : Nat) (G : Nat → Nat) : Bool :=
  allN g fun k => permOK 16 5 (mask 5) (16 * 5) (G k) (pinvS 16 5 (mask 5) (G k))

@[expose] noncomputable def bindK (gs : List (Array Nat)) (g : Nat) (G : Nat → Nat) : Bool :=
  Nat.beq gs.toArray.size g && allN g fun k => bindArrK gs.toArray[k]! 16 5 (G k)

theorem kBind : (bindK heSyl16 HeSylX.ng HeSylX.G && bindK heSylQ16 HeSylQ.ng HeSylQ.G &&
    bindK heSylE16 HeSylE.ng HeSylE.G && bindK heSylF16 HeSylF.ng HeSylF.G &&
    bindK heSylEz16 HeSylU.ng HeSylU.G) = true := by quickRfl

theorem kBindZ : bindArrK heSylZ16 16 5 Pz = true := by quickRfl
theorem kBindR : bindArrK heSylR16 16 5 Pr = true := by quickRfl
theorem kBindS : bindArrK heSylS16 16 5 Ps = true := by quickRfl

theorem kPermG : (gensPerm HeSylX.ng HeSylX.G && gensPerm HeSylQ.ng HeSylQ.G &&
    gensPerm HeSylE.ng HeSylE.G && gensPerm HeSylF.ng HeSylF.G && gensPerm HeSylU.ng HeSylU.G) =
    true := by quickRfl

theorem kPermZ : permOK 16 5 (mask 5) (16 * 5) Pz (pinvS 16 5 (mask 5) Pz) = true := by quickRfl
theorem kPermR : permOK 16 5 (mask 5) (16 * 5) Pr (pinvS 16 5 (mask 5) Pr) = true := by quickRfl
theorem kPermS : permOK 16 5 (mask 5) (16 * 5) Ps (pinvS 16 5 (mask 5) Ps) = true := by quickRfl

theorem kFlags : flagsK 16 5 HeSylX.N HeSylX.T Pz F.FZ F.F1 = true := by quickRfl

theorem kRest : restK16 16 5 HeSylX.ng HeSylX.G HeSylX.N HeSylX.T HeSylQ.ng HeSylQ.G HeSylQ.N
    HeSylQ.T HeSylE.ng HeSylE.G HeSylE.N HeSylE.T HeSylF.ng HeSylF.G HeSylF.N HeSylF.T
    HeSylU.ng HeSylU.G HeSylU.N HeSylU.T Pz Pr Ps = true := by quickRfl

@[expose] noncomputable def U : Nat → Bool := uqAt 16 5 HeSylX.N HeSylX.T HeSylQ.N HeSylQ.T F.FZ Pz

@[expose] noncomputable def V : Nat → Bool :=
  ueAt 16 5 HeSylX.N HeSylX.T HeSylE.N HeSylE.T HeSylF.N HeSylF.T F.F1

theorem uq0 : Nat.beq (cntR U 0 256) 0 = true := by quickRfl
theorem uq1 : Nat.beq (cntR U 256 256) 0 = true := by quickRfl
theorem uq2 : Nat.beq (cntR U 512 256) 0 = true := by quickRfl
theorem uq3 : Nat.beq (cntR U 768 256) 0 = true := by quickRfl

theorem ue0 : allR V 0 256 = true := by quickRfl
theorem ue1 : allR V 256 256 = true := by quickRfl
theorem ue2 : allR V 512 256 = true := by quickRfl
theorem ue3 : allR V 768 256 = true := by quickRfl

theorem uqTotal : cntR U 0 1024 = 0 := by
  have a1 := cntR_add U 0 256 256
  have a2 := cntR_add U 0 512 256
  have a3 := cntR_add U 0 768 256
  simp only [Nat.reduceAdd] at a1 a2 a3
  rw [a3, a2, a1, Nat.eq_of_beq_eq_true uq0, Nat.eq_of_beq_eq_true uq1,
    Nat.eq_of_beq_eq_true uq2, Nat.eq_of_beq_eq_true uq3]

theorem ueTotal : allR V 0 1024 = true := by
  have a1 := allR_add V 0 256 256
  have a2 := allR_add V 0 512 256
  have a3 := allR_add V 0 768 256
  simp only [Nat.reduceAdd] at a1 a2 a3
  rw [a3, a2, a1, ue0, ue1, ue2, ue3]
  rfl

theorem pin {gs : List (Array Nat)} {g N : Nat} {G T E S : Nat → Nat} (hb : bindK gs g G = true)
    (hp : gensPerm g G = true) (hk : bfsK 16 5 g G N T E S = true) (hf : N ≤ 4000) :
    Pin 16 5 gs g G N T E S := by
  unfold bindK at hb
  exact ⟨(binds_of_check hb).1, (binds_of_check hb).2, allN_spec hp, hk, hf⟩

theorem sylCheck16_true : sylCheck16 = true := by
  have kb := kBind
  simp only [Bool.and_eq_true] at kb
  obtain ⟨⟨⟨⟨bX, bQ⟩, bE⟩, bF⟩, bU⟩ := kb
  have kp := kPermG
  simp only [Bool.and_eq_true] at kp
  obtain ⟨⟨⟨⟨pX, pQ⟩, pE⟩, pF⟩, pU⟩ := kp
  have hN : HeSylX.N = 1024 := rfl
  rw [sylCheck16_eq]
  exact heSylK_sound (pin bX pX HeSylX.ok (by decide)) (pin bQ pQ HeSylQ.ok (by decide))
    (pin bE pE HeSylE.ok (by decide)) (pin bF pF HeSylF.ok (by decide))
    (pin bU pU HeSylU.ok (by decide)) ⟨rfl, rfl, rfl, rfl, rfl⟩
    (unpack_eq_of_bindArrK kBindZ) (unpack_eq_of_bindArrK kBindR) (unpack_eq_of_bindArrK kBindS)
    kPermZ kPermR kPermS kFlags kRest (by rw [hN]; exact uqTotal) (by rw [hN]; exact ueTotal)

end CertificateChecks.KernelLC.HeSyl

end
