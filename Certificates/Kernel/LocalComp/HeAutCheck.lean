module

public import Certificates.Kernel.LocalComp.HeAutPin
public import Certificates.Kernel.LocalComp.HeAutFlags
public import CFSG.Certificates.Kernel.HeAutKSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelLC.HeAutCheck

open CFSG.KC.BfsPin CFSG.KC.HexaK CFSG.KC.HeAutK CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw
open CFSG.ComponentClassification.AS81.HeSylow CFSG.ComponentClassification.GrSLit.HeldFix
open CertificateChecks.KernelLC

theorem kFlags : flagsK 32 6 HeAutY.N HeAutY.T Pz HeAutFZ HeAutF1 = true := by quickRfl

theorem kRest : restK 32 6 HeAutY.ng HeAutY.G HeAutY.N HeAutY.T HeAutQ.ng HeAutQ.G HeAutQ.N HeAutQ.T
    HeAutE.ng HeAutE.G HeAutE.N HeAutE.T HeAutF.ng HeAutF.G HeAutF.N HeAutF.T
    HeAutU.ng HeAutU.G HeAutU.N HeAutU.T Pz Pr Ps = true := by quickRfl

@[expose] noncomputable def U : Nat → Bool := uqAt 32 6 HeAutY.N HeAutY.T HeAutQ.N HeAutQ.T HeAutFZ Pz

@[expose] noncomputable def V : Nat → Bool :=
  ueAt 32 6 HeAutY.N HeAutY.T HeAutE.N HeAutE.T HeAutF.N HeAutF.T HeAutF1

theorem uq0 : Nat.beq (cntR U 0 256) 0 = true := by quickRfl
theorem uq1 : Nat.beq (cntR U 256 256) 0 = true := by quickRfl
theorem uq2 : Nat.beq (cntR U 512 256) 0 = true := by quickRfl
theorem uq3 : Nat.beq (cntR U 768 256) 3 = true := by quickRfl
theorem uq4 : Nat.beq (cntR U 1024 256) 0 = true := by quickRfl
theorem uq5 : Nat.beq (cntR U 1280 256) 4 = true := by quickRfl
theorem uq6 : Nat.beq (cntR U 1536 256) 3 = true := by quickRfl
theorem uq7 : Nat.beq (cntR U 1792 256) 6 = true := by quickRfl

theorem ue0 : allR V 0 256 = true := by quickRfl
theorem ue1 : allR V 256 256 = true := by quickRfl
theorem ue2 : allR V 512 256 = true := by quickRfl
theorem ue3 : allR V 768 256 = true := by quickRfl
theorem ue4 : allR V 1024 256 = true := by quickRfl
theorem ue5 : allR V 1280 256 = true := by quickRfl
theorem ue6 : allR V 1536 256 = true := by quickRfl
theorem ue7 : allR V 1792 256 = true := by quickRfl

theorem uqTotal : cntR U 0 2048 = 16 := by
  have a1 := cntR_add U 0 256 256
  have a2 := cntR_add U 0 512 256
  have a3 := cntR_add U 0 768 256
  have a4 := cntR_add U 0 1024 256
  have a5 := cntR_add U 0 1280 256
  have a6 := cntR_add U 0 1536 256
  have a7 := cntR_add U 0 1792 256
  simp only [Nat.reduceAdd] at a1 a2 a3 a4 a5 a6 a7
  rw [a7, a6, a5, a4, a3, a2, a1, Nat.eq_of_beq_eq_true uq0, Nat.eq_of_beq_eq_true uq1,
    Nat.eq_of_beq_eq_true uq2, Nat.eq_of_beq_eq_true uq3, Nat.eq_of_beq_eq_true uq4,
    Nat.eq_of_beq_eq_true uq5, Nat.eq_of_beq_eq_true uq6, Nat.eq_of_beq_eq_true uq7]

theorem ueTotal : allR V 0 2048 = true := by
  have a1 := allR_add V 0 256 256
  have a2 := allR_add V 0 512 256
  have a3 := allR_add V 0 768 256
  have a4 := allR_add V 0 1024 256
  have a5 := allR_add V 0 1280 256
  have a6 := allR_add V 0 1536 256
  have a7 := allR_add V 0 1792 256
  simp only [Nat.reduceAdd] at a1 a2 a3 a4 a5 a6 a7
  rw [a7, a6, a5, a4, a3, a2, a1, ue0, ue1, ue2, ue3, ue4, ue5, ue6, ue7]
  rfl

theorem heAutSylowCheck_true : heAutSylowCheck = true := by
  have kp := kPermG
  simp only [Bool.and_eq_true] at kp
  obtain ⟨⟨⟨⟨pY, pQ⟩, pE⟩, pF⟩, pU⟩ := kp
  have hN : HeAutY.N = 2048 := rfl
  have huq : cntR U 0 HeAutY.N < 64 := by
    rw [hN, uqTotal]
    decide
  have hue : allR V 0 HeAutY.N = true := by
    rw [hN]
    exact ueTotal
  rw [heAutSylowCheck_eq]
  exact heAutK_sound (pinY pY) (pin kBindQ pQ HeAutQ.ok (by decide))
    (pin kBindE pE HeAutE.ok (by decide)) (pin kBindF pF HeAutF.ok (by decide))
    (pin kBindU pU HeAutU.ok (by decide)) ⟨rfl, rfl, rfl, rfl, rfl⟩
    (unpack_eq_of_bindArrK kBindZ) (unpack_eq_of_bindArrK kBindR) (unpack_eq_of_bindArrK kBindS)
    kPermZ kPermR kPermS kFlags kRest huq hue

end CertificateChecks.KernelLC.HeAutCheck

end
