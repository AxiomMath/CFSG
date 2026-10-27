module

public import Certificates.Kernel.SporSch.Ly.BS18009
public import Certificates.Kernel.Misc.LyGen45Checks

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLyGen45

open CFSG.KC.Ord CFSG.KD.OrdLy CFSG.KS.SporSch.LyM CertificateChecks.KernelSporSch.LyBS
open CertificateChecks.KernelSporSch.LyBSF CFSG.Sporadic.Ly.Gen CFSG.Sporadic.Ly.Gen45
open CFSG.Sporadic.He.Native CFSG.Sporadic.Ly.Native

local notation "U" X:max => unpackL 111 12 1332 X

theorem letter_eq (z : Int) :
    letterM matA matB (powM 5 111 matB 4) z = U (letK z) ∧ vld (letK z) = true := by
  unfold letterM letK
  split_ifs
  · exact ⟨matA_eq, vA⟩
  · exact ⟨matB_eq, vB⟩
  · exact ⟨b4_eq, vB4⟩

theorem wordM_eq (w : List Int) :
    wordM matA matB (powM 5 111 matB 4) w = U (w.foldr (fun z P => mul (letK z) P) ONE) ∧
      vld (w.foldr (fun z P => mul (letK z) P) ONE) = true := by
  unfold wordM
  induction w with
  | nil =>
    rw [List.foldr_nil, List.foldr_nil]
    exact ⟨idE, vOne⟩
  | cons z w ih =>
    obtain ⟨h1, h2⟩ := letter_eq z
    rw [List.foldr_cons, List.foldr_cons, h1, ih.1, mulE h2 ih.2]
    exact ⟨rfl, mulV h2 ih.2⟩

theorem entry0 (X j : Nat) (hj : j < 111) : ((U X)[0]!)[j]! = ent0 X j := by
  unfold unpackL
  rw [ofFn_get! _ (by norm_num : 0 < 111), ofFn_get! _ hj]
  simp only [ent0, Nat.mul_zero, Nat.zero_add]
  rfl

theorem bCertificate_true : bCertificate () = true := by
  have hT : wordM matA matB (powM 5 111 matB 4) genWords[5]! = U TK := (wordM_eq _).1
  have vT : vld TK = true := (wordM_eq _).2
  have vAT : vld (mul A TK) = true := mulV vA vT
  have hD : powM 5 111 (mulM 5 111 matA (U TK)) 3 = U DK := by
    rw [matA_eq, mulE vA vT]
    exact (powM_eq consts (hv vAT) 3).1
  have vD : vld DK = true := (powM_eq consts (hv vAT) 3).2
  have h := b_ok
  unfold bCertificate bCheck
  simp only
  rw [hT, hD, entry0 DK 2 (by norm_num), entry0 DK 0 (by norm_num), matA_eq,
    entry0 A 0 (by norm_num), mulE vD vD, idE, beqE (mulV vD vD) vOne, mulE vA vD, mulE vD vA,
    beqE (mulV vA vD) (mulV vD vA), mulE vT vD, mulE vD vT, beqE (mulV vT vD) (mulV vD vT)]
  exact h

end CertificateChecks.KernelLyGen45

end
