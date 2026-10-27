module

public import Certificates.Kernel.GLQ.HNFive
public import CFSG.Certificates.Kernel.OpsHomRels

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelGLQ.HNFiveK

open CFSG.KC.Ord CFSG.KC.OpsK CFSG.KC.OpsHom CFSG.SectionRank.Native CFSG.Sporadic.GLQ
open CFSG.KS.SporSch.LyM CFSG.Blueprint CFSG.RankThree.PartOne.KS.HNFive
open CertificateChecks.KernelGLQ.HNTwo

noncomputable abbrev H5 : Hom (opsP 5 133) O5 := homP kConsts (by norm_num)

theorem lt_iQ : ∀ j, iQ j < hnFiveN := by decide +kernel

theorem lt_iR : ∀ j, iR j < hnFiveN := by decide +kernel

theorem hn5_of {cs1 cs2 : List Char} (e1 : NativeSporadic.HNSeed1 = String.ofList cs1)
    (e2 : NativeSporadic.HNSeed2 = String.ofList cs2)
    (hk : forceB (pay cs1) (fun A => forceB (pay cs2) fun B => checkHN5 hnFiveProg A B) = true) :
    hnFiveCheck = true := by
  rw [forceB_eq, forceB_eq] at hk
  generalize hpa : pay cs1 = A at hk
  generalize hpb : pay cs2 = B at hk
  unfold checkHN5 at hk
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨hvA, hvB⟩, hk⟩ := hk
  rw [forceB_eq, powN_eq _ _ _ _ (by norm_num), runK_eq] at hk
  have hdec : ∀ {cs : List Char} {X : Nat}, pay cs = X →
      (opsP 5 133).decode (String.ofList cs) = unpackL 133 13 1729 X := by
    intro cs X h
    rw [← h]
    exact payRunP_eqL cs (by norm_num) (by norm_num) (by norm_num)
  have hA : (opsP 5 133).decode NativeSporadic.HNSeed1 = H5.U A := by rw [e1]; exact hdec hpa
  have hB : (opsP 5 133).decode NativeSporadic.HNSeed2 = H5.U B := by rw [e2]; exact hdec hpb
  have hPA : H5.P A := hvA
  have hPB : H5.P B := hvB
  obtain ⟨eB2, pB2⟩ := H5.pow_U 2 hPB
  have hlt : hnFiveProg.all (Instr.lt hnFiveN) = true := by decide +kernel
  have hinit : initRegsN (opsP 5 133) hnFiveN ((opsP 5 133).decode NativeSporadic.HNSeed1,
      (opsP 5 133).decode NativeSporadic.HNSeed1)
      ((opsP 5 133).decode NativeSporadic.HNSeed2,
        (opsP 5 133).pow ((opsP 5 133).decode NativeSporadic.HNSeed2) 2) =
      (initRegsN O5 hnFiveN (A, A) (B, O5.pow B 2)).map H5.UU := by
    rw [hA, hB, eB2]
    exact H5.initRegsN_U hnFiveN (A, A) (B, O5.pow B 2)
  obtain ⟨hrun, hsize, hP⟩ := H5.runProgN_U hnFiveN hnFiveProg hlt
    (initRegsN O5 hnFiveN (A, A) (B, O5.pow B 2)) (by simp [initRegsN])
    (H5.initRegsN_P ⟨hPA, hPA⟩ ⟨hPB, pB2⟩)
  unfold hnFiveCheck hnFiveRegs
  rw [hlt, Bool.true_and, hinit, hrun, H5.hnRelsOK_U hP (by rw [hsize]; decide)
    (by rw [hsize]; decide) (fun j => by rw [hsize]; exact lt_iQ j)
    (fun j => by rw [hsize]; exact lt_iR j)]
  exact hk

theorem facts14985 : hnFiveCheck = true := hn5_of HS1.eq HS2.eq kHN5

end CertificateChecks.KernelGLQ.HNFiveK

end
