
module

public import Certificates.Kernel.SporSch.Co2M.Local
public import CFSG.Certificates.Kernel.SporSch.PosTable
public import CFSG.Sporadic.Co2Schreier.ClassCheckInputs
public import CFSG.Monster.B.Co2.PermArr
public meta import CFSG.Sporadic.Co2Schreier.ClassCheckInputs
meta import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.SporSch.HN.GenNTree
import CFSG.Certificates.Kernel.Common.Harness
import Init.Data.Nat.Fold
import Init.Data.Range.Basic
import Init.Data.Array.Basic
import Certificates.Kernel.Misc.Perm.HexCmd
import Certificates.Kernel.SporSch.HN.GenNTree

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.Sporadic.Co2Schreier CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co2Cert

meta def repRows : Array (Array Nat) :=
  (Array.range 3).map fun r => transposeRows 22 CFSG.Sporadic.Co2Inv.co2InvReps[r]!

meta def repArrs : Array (Array Nat) := (Array.range 3).map (cRepArr co2PosTable)

meta def uMoved : List Nat := [((List.range 2300).find? fun i => uArr[i]! != i).getD 0]

end CertificateChecks.KernelSporSch.Co2M

#kmisc_packarrs CertificateChecks.KernelSporSch.Co2M.RM CertificateChecks.KernelSporSch.Co2M.repRows 22
#kmisc_packarrs CertificateChecks.KernelSporSch.Co2M.RP CertificateChecks.KernelSporSch.Co2M.repArrs 12
#kss_ntree CertificateChecks.KernelSporSch.Co2M.UW CertificateChecks.KernelSporSch.Co2M.uMoved

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Co2M CFSG.KS.MatRep CFSG.RankThree.Native.F2
open CFSG.Sporadic.Co2Schreier CFSG.Sporadic.Co2Cert CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native CFSG.Sporadic.SmallF2.Native

@[expose] noncomputable def uP : ℕ × ℕ := cmpP (sT.getD 8 (0, 0)) (sT.getD 0 (0, 0))

@[expose] noncomputable def xRP (r : ℕ) : ℕ × ℕ := (RM r, RM r)

@[expose] noncomputable def pickP (r : ℕ) : ℕ × ℕ :=
  bif Nat.beq r 0 then zP else bif Nat.beq r 1 then tP else uP

@[expose] noncomputable def fwP (r : ℕ) : ℕ × ℕ := wP aT (fuseWords.getD r [])

@[expose] noncomputable def powL (p : ℕ × ℕ) : ℕ → ℕ × ℕ
  | 0 => (I22, I22)
  | e + 1 => cmpP (powL p e) p

@[expose] noncomputable def fuseP (r : ℕ) : ℕ × ℕ :=
  cmpP (pickP r) (cmpP (cmpP (fwP r) (xRP r)) (invP (fwP r)))

theorem rows_ok : allN 3 (fun r => allN 22 fun k =>
    Nat.beq (pg 22 M22 (RM r) k) ((transposeRows 22 CFSG.Sporadic.Co2Inv.co2InvReps[r]!)[k]?.getD 0)) =
    true := by
  quickRfl

theorem bind_ok : allN 3 (fun r => bindK (PV 0) (RP r) (RM r) (RM r)) = true := by quickRfl

theorem fuse_ok : allN 3 (fun r => Nat.beq (powL (fuseP r) (fuseExps.getD r 0)).1 I22) = true := by
  quickRfl

theorem u_ok : (Nat.beq (cmpP uP uP).1 I22 &&
    !Nat.beq (vmK (VG (PV 0) (UW 0)) uP.1) (VG (PV 0) (UW 0)) && Nat.blt (UW 0) 2300) = true := by
  quickRfl

theorem fuse_words_ok : (lettersOK 2 (fuseWords.getD 0 []) && lettersOK 2 (fuseWords.getD 1 []) &&
    lettersOK 2 (fuseWords.getD 2 [])) = true := by
  decide +kernel

theorem eqA_self (n : ℕ) (t : Array ℕ) : eqA n t t = true := by
  rw [eqA, CFSG.Monster.B.Co2.allLt_iff]
  intro i _
  exact beq_self_eq_true _

theorem isInvA_rep {a : Array ℕ} {M M' : ℕ} (ha : MatRep.Rep 22 co2PackedVecs a M M') :
    isInvA 2300 a (invCand 2300 a) = true := by
  have h := isInvA_permOfMat good.hd good.nodup good.lt ha.2
  rw [V_size] at h
  rw [(rep_inv (p := (M, M')) ha).1, ha.1]
  exact h

theorem idA_eq : idA 2300 = permOfMat 22 co2PackedVecs I22 := by
  rw [I22_eq, permOfMat_idM good.hd good.nodup good.lt, V_size]

theorem rep_powL {t : Array ℕ} {p : ℕ × ℕ} (ht : MatRep.Rep 22 co2PackedVecs t p.1 p.2) :
    ∀ e, MatRep.Rep 22 co2PackedVecs (CFSG.Sporadic.Co2Schreier.powA t e) (powL p e).1
      (powL p e).2
  | 0 => by
    have h := rep_idA good
    rw [V_size, ← I22_eq] at h
    exact h
  | e + 1 => rep_cmp (rep_powL ht e) ht

theorem uRep : MatRep.Rep 22 co2PackedVecs uArr uP.1 uP.2 := by
  have h8 : 8 < sT.length := by decide +kernel
  have h0 : 0 < sT.length := by omega
  exact rep_cmp (repT_get sRep h8) (repT_get sRep h0)

theorem pick_rep {r : ℕ} : MatRep.Rep 22 co2PackedVecs (pickRep zArr tArr uArr r) (pickP r).1
    (pickP r).2 := by
  unfold pickRep pickP
  by_cases h0 : r = 0
  · subst h0
    exact zRep
  · by_cases h1 : r = 1
    · subst h1
      exact tRep
    · rw [ite_eq_right h0, ite_eq_right h1]
      have e0 : Nat.beq r 0 = false := by
        cases h : Nat.beq r 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h) h0
      have e1 : Nat.beq r 1 = false := by
        cases h : Nat.beq r 1
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h) h1
      rw [e0, e1]
      exact uRep

theorem rm_rows {r : ℕ} (hr : r < 3) (k : ℕ) (hk : k < 22) :
    row 22 (RM r) k = (transposeRows 22 CFSG.Sporadic.Co2Inv.co2InvReps[r]!)[k]?.getD 0 := by
  rw [← Nat.eq_of_beq_eq_true (allN_spec (allN_spec rows_ok r hr) k hk)]
  exact (land_mask_eq_row M22_eq (RM r) k).symm

theorem rpRep {r : ℕ} (hr : r < 3) :
    MatRep.Rep 22 co2PackedVecs (unpack 2300 12 (RP r)) (RM r) (RM r) :=
  bindK_sound good V_size (fun i hi => V_get hi) rfl (allN_spec bind_ok r hr)

theorem matPerm_eq {pt : Array UInt32}
    (hpt : ∀ j < 2300, (pt[co2PackedVecs[j]!]!).toNat = j) {rows : List ℕ} {a : Array ℕ}
    {M M' : ℕ} (hR : ∀ k < 22, row 22 M k = (transposeRows 22 rows.toArray)[k]?.getD 0)
    (ha : MatRep.Rep 22 co2PackedVecs a M M') (hs : a.size = 2300) : matPerm pt rows = a := by
  unfold matPerm
  apply Array.ext
  · rw [Array.size_ofFn, hs]
  · intro i h1 h2
    have hi : i < 2300 := by rwa [Array.size_ofFn] at h1
    have hg := get_rep ha (by rw [V_size]; exact hi)
    rw [Array.getElem_ofFn, ← getElem!_pos a i h2, vecMulN_eq_vmul hR, ← hg.2]
    exact hpt _ (by rw [← V_size]; exact hg.1)

theorem cRep_eq {r : ℕ} (hr : r < 3) : cRepArr co2PosTable r = unpack 2300 12 (RP r) := by
  unfold cRepArr
  refine matPerm_eq (fun j hj => ?_) (fun k hk => ?_) (rpRep hr) (by simp [unpack])
  · unfold co2PosTable
    exact posTable_get good.nodup good.lt (by rw [V_size]; norm_num) (by rw [V_size]; exact hj)
  · rw [Array.toArray_toList]
    exact rm_rows hr k hk

theorem class_check : classCheck co2PosTable zArr tArr uArr = true := by
  have hu := u_ok
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.blt_eq] at hu
  obtain ⟨⟨huu, hmov⟩, hlt⟩ := hu
  unfold classCheck
  simp only [Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rewrite [(rep_cmp uRep uRep).1, Nat.eq_of_beq_eq_true huu, idA_eq]
    exact eqA_self _ _
  · rewrite [Bool.not_eq_true']
    cases h : eqA 2300 uArr (idA 2300)
    · rfl
    · exfalso
      have hx := CFSG.Monster.B.Co2.allLt_iff.1 h (UW 0) hlt
      rw [CFSG.Monster.B.Co2.idA_get hlt, beq_iff_eq] at hx
      have hg := (get_rep uRep (i := UW 0) (by rw [V_size]; exact hlt)).2
      rw [hx, V_get hlt, ← vmK_eq] at hg
      rw [← hg, Nat.beq_refl] at hmov
      exact Bool.false_ne_true hmov.symm
  · rewrite [CFSG.Monster.B.Co2.allLt_iff]
    intro r hr
    have hC : MatRep.Rep 22 co2PackedVecs (cRepArr co2PosTable r) (xRP r).1 (xRP r).2 := by
      rewrite [cRep_eq hr]
      exact rpRep hr
    have hl : lettersOK 2 (fuseWords.getD r []) = true := by
      have hw := fuse_words_ok
      simp only [Bool.and_eq_true] at hw
      interval_cases r
      · exact hw.1.1
      · exact hw.1.2
      · exact hw.2
    have hW : MatRep.Rep 22 co2PackedVecs (wordArr aArrs (fuseWords.getD r [])) (fwP r).1
        (fwP r).2 := rep_wordArr good V_size mmK_eq I22_eq aRep hl
    have hX := rep_cmp (pick_rep (r := r)) (rep_cmp (rep_cmp hW hC) (rep_inv hW))
    have hP := rep_powL hX (fuseExps.getD r 0)
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨isInvA_rep hC, ?_⟩, hl⟩, isInvA_rep hW⟩, ?_⟩
    · rewrite [CFSG.Monster.B.Co2.allLt_iff]
      intro k hk
      rewrite [(get_rep hC (by rw [V_size]; exact hk)).2,
        vecMulN_eq_vmul (fun j hj => rm_rows hr j hj)]
      exact beq_self_eq_true _
    · rewrite [hP.1]
      change eqA 2300 (permOfMat 22 co2PackedVecs (powL (fuseP r) (fuseExps.getD r 0)).1)
        (idA 2300) = true
      rewrite [Nat.eq_of_beq_eq_true (allN_spec fuse_ok r hr), idA_eq]
      exact eqA_self _ _

end CertificateChecks.KernelSporSch.Co2M

end
