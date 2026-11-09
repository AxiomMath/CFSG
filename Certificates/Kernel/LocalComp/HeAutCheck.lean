module

public import Certificates.Kernel.LocalComp.HeAutPin
public import Certificates.Kernel.LocalComp.HeAutFlags
public import CFSG.Certificates.Kernel.HeAutKSound
public import CFSG.Certificates.Kernel.HeAutKPt
import CFSG.Certificates.Kernel.HeAutKLoops
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

@[expose] noncomputable def U : Nat → Bool :=
  uqAtPt 32 6 HeAutY.N HeAutY.T HeAutQ.N HeAutQ.T HeAutFZ Pz

@[expose] noncomputable def V : Nat → Bool :=
  ueAtPt 32 6 HeAutY.N HeAutY.T HeAutE.N HeAutE.T HeAutF.N HeAutF.T HeAutF1

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

theorem cntR_blocks8 (f : Nat → Bool) {c0 c1 c2 c3 c4 c5 c6 c7 : Nat}
    (h0 : Nat.beq (cntR f 0 256) c0 = true) (h1 : Nat.beq (cntR f 256 256) c1 = true)
    (h2 : Nat.beq (cntR f 512 256) c2 = true) (h3 : Nat.beq (cntR f 768 256) c3 = true)
    (h4 : Nat.beq (cntR f 1024 256) c4 = true) (h5 : Nat.beq (cntR f 1280 256) c5 = true)
    (h6 : Nat.beq (cntR f 1536 256) c6 = true) (h7 : Nat.beq (cntR f 1792 256) c7 = true) :
    cntR f 0 2048 = c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 := by
  have a1 := cntR_add f 0 256 256
  have a2 := cntR_add f 0 512 256
  have a3 := cntR_add f 0 768 256
  have a4 := cntR_add f 0 1024 256
  have a5 := cntR_add f 0 1280 256
  have a6 := cntR_add f 0 1536 256
  have a7 := cntR_add f 0 1792 256
  simp only [Nat.reduceAdd] at a1 a2 a3 a4 a5 a6 a7
  rw [a7, a6, a5, a4, a3, a2, a1, Nat.eq_of_beq_eq_true h0, Nat.eq_of_beq_eq_true h1,
    Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4,
    Nat.eq_of_beq_eq_true h5, Nat.eq_of_beq_eq_true h6, Nat.eq_of_beq_eq_true h7]

theorem allR_blocks8 (f : Nat → Bool) (h0 : allR f 0 256 = true) (h1 : allR f 256 256 = true)
    (h2 : allR f 512 256 = true) (h3 : allR f 768 256 = true) (h4 : allR f 1024 256 = true)
    (h5 : allR f 1280 256 = true) (h6 : allR f 1536 256 = true) (h7 : allR f 1792 256 = true) :
    allR f 0 2048 = true := by
  have a1 := allR_add f 0 256 256
  have a2 := allR_add f 0 512 256
  have a3 := allR_add f 0 768 256
  have a4 := allR_add f 0 1024 256
  have a5 := allR_add f 0 1280 256
  have a6 := allR_add f 0 1536 256
  have a7 := allR_add f 0 1792 256
  simp only [Nat.reduceAdd] at a1 a2 a3 a4 a5 a6 a7
  rw [a7, a6, a5, a4, a3, a2, a1, h0, h1, h2, h3, h4, h5, h6, h7]
  rfl

theorem uqTotal : cntR U 0 2048 = 16 := cntR_blocks8 U uq0 uq1 uq2 uq3 uq4 uq5 uq6 uq7

theorem ueTotal : allR V 0 2048 = true := allR_blocks8 V ue0 ue1 ue2 ue3 ue4 ue5 ue6 ue7

theorem heAutSylowCheck_true : heAutSylowCheck = true := by
  have kp := kPermG
  simp only [Bool.and_eq_true] at kp
  obtain ⟨⟨⟨⟨pY, pQ⟩, pE⟩, pF⟩, pU⟩ := kp
  have hN : HeAutY.N = 2048 := rfl
  have hX := PP_pts (pinY pY).ok (pinY pY).perm
  have hz : PP 32 6 Pz := PP_of_permOK (hX 0 (by rw [hN]; decide)).sz kPermZ
  have eU : cntR U 0 HeAutY.N =
      cntR (uqAt 32 6 HeAutY.N HeAutY.T HeAutQ.N HeAutQ.T HeAutFZ Pz) 0 HeAutY.N :=
    cntR_congrH0 fun k hk => uqAtPt_eq hX hz hk
  have eV : allR V 0 HeAutY.N =
      allR (ueAt 32 6 HeAutY.N HeAutY.T HeAutE.N HeAutE.T HeAutF.N HeAutF.T HeAutF1) 0 HeAutY.N :=
    allR_congr0 fun k hk => ueAtPt_eq hX hk
  have huq : cntR (uqAt 32 6 HeAutY.N HeAutY.T HeAutQ.N HeAutQ.T HeAutFZ Pz) 0 HeAutY.N < 64 := by
    rw [← eU, hN, uqTotal]
    decide
  have hue : allR (ueAt 32 6 HeAutY.N HeAutY.T HeAutE.N HeAutE.T HeAutF.N HeAutF.T HeAutF1) 0
      HeAutY.N = true := by
    rw [← eV, hN]
    exact ueTotal
  rw [heAutSylowCheck_eq]
  exact heAutK_sound (pinY pY) (pin kBindQ pQ HeAutQ.ok (by decide))
    (pin kBindE pE HeAutE.ok (by decide)) (pin kBindF pF HeAutF.ok (by decide))
    (pin kBindU pU HeAutU.ok (by decide)) ⟨rfl, rfl, rfl, rfl, rfl⟩
    (unpack_eq_of_bindArrK kBindZ) (unpack_eq_of_bindArrK kBindR) (unpack_eq_of_bindArrK kBindS)
    kPermZ kPermR kPermS kFlags kRest huq hue

end CertificateChecks.KernelLC.HeAutCheck

end
