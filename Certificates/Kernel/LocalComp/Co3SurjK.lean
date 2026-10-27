module

public import Certificates.Kernel.LocalComp.Co3SurjChecks
public import CFSG.Certificates.Kernel.SurjKSound
public import CFSG.Certificates.Kernel.SurjKSeedSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.Co3Surj

open CFSG.KC.SurjK CFSG.KC.M1F2 CFSG.KC.Co3Bfs CFSG.KLie.CT
open CFSG.KS (allN_spec lget)
open CFSG.Sporadic.Bridge.SurjD.Native CFSG.Sporadic.SmallF2.Native CFSG.EvenSmallLie.SympSix.Co3Ident

theorem img_eq : vSpec.imgWords = Li.toArray := by
  change vImgWords = _
  unfold vImgWords Li
  rw [IT.eq, wordsK_sound kIT, Array.toArray_toList]

theorem surj_eq : vSpec.surjWords = Ls.toArray := by
  change vSurjWords = _
  unfold vSurjWords Ls
  rw [ST.eq, wordsK_sound kST, List.map_toArray]

theorem himg (k : Nat) (hk : k < 7) :
    matW 22 (baseF CS.A CS.AI CS.B CS.BI) (Li.getD k []) = lget CS.Ims k := by
  interval_cases k
  · exact Nat.eq_of_beq_eq_true kImg0
  · exact Nat.eq_of_beq_eq_true kImg1
  · exact Nat.eq_of_beq_eq_true kImg2
  · rw [Li3]
    exact kImg3
  · exact Nat.eq_of_beq_eq_true kImg4
  · exact Nat.eq_of_beq_eq_true kImg5
  · exact Nat.eq_of_beq_eq_true kImg6

theorem orb_all (k : Nat) (hk : k < 11178) : orbF k = true :=
  cover_of_blocks (B := 1024) (nb := 11) (by omega) (by decide) BO.all k hk

theorem facts3092 : seedLetterChecks CFSG.Sporadic.Co3.Native.co3Data vSpec = true := by
  have hs : (Li.length == 7 && Ls.length == 2 && CS.Ims.length == 7 && CS.ImsI.length == 7) = true :=
    kSizes
  simp only [Bool.and_eq_true, beq_iff_eq] at hs
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hs
  exact seedLetter_sound (D := CFSG.Sporadic.Co3.Native.co3Data) (S := vSpec)
    (Ims := CS.Ims) (ImsI := CS.ImsI) (Li := Li) (Ls := Ls) SA.eq SB.eq kA kB
    (Nat.eq_of_beq_eq_true kAI) (Nat.eq_of_beq_eq_true kBI) (by decide) (by decide) (by decide)
    orb_all
    (by rw [h3]; rfl) (by rw [h4, h3]) img_eq surj_eq (by rw [h1]; rfl) h2 kBase himg
    (fun k hk => Nat.eq_of_beq_eq_true (allN_spec kInv k hk)) kRel kSl
    (Nat.eq_of_beq_eq_true kSA) (Nat.eq_of_beq_eq_true kSB)

end CertificateChecks.KernelLC.Co3Surj

end
