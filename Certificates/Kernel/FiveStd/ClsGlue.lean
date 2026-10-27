module

public import Certificates.Kernel.FiveStd.Tree
public import Certificates.Kernel.FiveStd.Cls
public import Certificates.Kernel.FiveStd.GenInv
public import CFSG.Certificates.Kernel.FiveStdKOrbSound
public import CFSG.GH74.GLS.LU.Local.FiveStdMat4

public section

namespace CertificateChecks.FiveStd

open CFSG.KC.FiveStdK CFSG.GH74.GLS.LU.Local.FiveStd

theorem clsF_eq (k : Nat) : clsF k = clsOK G GI 2 (RP.getD k 0) (OR.getD k 0) (OM.getD k 0)
    (CB.getD k 0) (CM.getD k 0) (IV.getD k 0) := rfl

theorem cls_ok : ∀ k < 5, clsF k = true := by
  intro k hk
  interval_cases k
  · exact ch5147c.c0
  · exact ch5147c.c1
  · exact ch5147c.c2
  · exact ch5147c.c3
  · exact ch5147c.c4

theorem cls_card : ∀ k < 5, OM.getD k 0 * CM.getD k 0 = 28800 := by decide +kernel

theorem tree_all : ∀ i < 28800, tPt T G 2 28800 i = true := by
  intro i hi
  have h := (allN_iff _ _).1 (tree_chunks (i / 900) (by omega)) (i % 900) (Nat.mod_lt _ (by omega))
  have hi' : Nat.add (900 * (i / 900)) (i % 900) = i := by
    rw [nat_add]
    omega
  rw [hi'] at h
  exact h

theorem cls_glue (k : Nat) (hk : k < 5) :
    validE (decE (RP.getD k 0)) = true ∧
    (∀ x, validE x = true → ((∃ c, validE c = true ∧ conjE c (decE (RP.getD k 0)) = x) ↔
      x ∈ decL (fun j => oCode (f96 (OR.getD k 0) j)) (OM.getD k 0))) ∧
    (decL (fun j => oCode (f96 (OR.getD k 0) j)) (OM.getD k 0)).Nodup ∧
    (∀ b, validE b = true → (mulE b (decE (RP.getD k 0)) = mulE (decE (RP.getD k 0)) b ↔
      b ∈ decL (f20 (CB.getD k 0)) (CM.getD k 0))) ∧
    (decL (f20 (CB.getD k 0)) (CM.getD k 0)).Nodup ∧
    validE (decE (IV.getD k 0)) = true ∧
      conjE (decE (IV.getD k 0)) (decE (RP.getD k 0)) = invE (decE (RP.getD k 0)) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcls := cls_ok k hk
  rw [clsF_eq] at hcls
  have hgen := (clsOK_spec hcls).1
  have hg : ∀ l < 2, validE (decE (f20 G l)) = true ∧ codeE (decE (f20 G l)) = f20 G l :=
    fun l hl => ⟨valid_decE (hgen l hl).1, codeE_decE (validK_lt (hgen l hl).1)⟩
  exact cls_sound (Mat.model_ιF (F := ZMod 5)) (fun l => decE (f20 G l)) hg
    ((allN_iff _ _).1 gi_valid) tree_all hcls (cls_card k hk)

end CertificateChecks.FiveStd

end
