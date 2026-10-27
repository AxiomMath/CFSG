module

public import Certificates.Kernel.Sporadic.J3C.GlueK

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelSpor.J3CGlue

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.PC CFSG.KS.CentReg CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.J3Data CFSG.Monster.B CFSG.Monster.B.Co2.Native CFSG.Sporadic.J3.Native
  CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen CertificateChecks.KernelSpor
  CertificateChecks.KernelSpor.J3K CertificateChecks.KernelSpor.J3C
  CertificateChecks.KernelSchreierFam

theorem κP : ∀ h < 2, κ h ∈ J3Groups.P := by
  intro h hh
  have hw : lettersOK 2 kWordsAB[h]! = true := by interval_cases h <;> decide +kernel
  obtain ⟨g, hg, hrep⟩ := exists_rep_wordA (gs := fun h => Co2.permOfArr 20520 abArr[h]!)
    (H := J3Groups.P) abRep abInvRep abMem kWordsAB[h]! hw
  have e : kStrong[h]! = wordA 20520 abArr abInv kWordsAB[h]! :=
    J3CqBind.toArray_map_get _ _ (by rw [J3CqBind.kWords_len]; exact hh)
  rw [← e] at hrep
  rw [(repK h hh).1.unique hrep]
  exact hg

theorem κComm0 : κ 0 * J3Groups.pa = J3Groups.pa * κ 0 := by
  refine (commutesA_iff (repK 0 (by norm_num)).1 (abRep 0 (by norm_num))).1 ?_
  unfold commutesA
  have cK := (SchreierFam.PP_of_permOK' J3CqBind.hsz (J3CqBind.kk_perm 0 (by norm_num))).1
  have cA := (SchreierFam.PP_of_permOK' J3CqBind.hsz (J3CqBind.ab_perm 0 (by norm_num))).1
  rw [J3CqBind.kk_bind 0 (by norm_num), J3CqBind.ab_bind 0 (by norm_num),
    CFSG.KC.BfsPin.compA_unpack cK cA, CFSG.KC.BfsPin.compA_unpack cA cK]
  change eqA 20520 (CFSG.KS.Raw.unpack 20520 15 (pcomp 20520 15 (mask 15) J3Cq.K0 J3Cq.A))
    (CFSG.KS.Raw.unpack 20520 15 (pcomp 20520 15 (mask 15) J3Cq.A J3Cq.K0)) = true
  rw [Nat.eq_of_beq_eq_true comm0]
  exact eqASelf _

theorem κComm1 : κ 1 * J3Groups.pa = J3Groups.pa * κ 1 := by
  refine (commutesA_iff (repK 1 (by norm_num)).1 (abRep 0 (by norm_num))).1 ?_
  unfold commutesA
  have cK := (SchreierFam.PP_of_permOK' J3CqBind.hsz (J3CqBind.kk_perm 1 (by norm_num))).1
  have cA := (SchreierFam.PP_of_permOK' J3CqBind.hsz (J3CqBind.ab_perm 0 (by norm_num))).1
  rw [J3CqBind.kk_bind 1 (by norm_num), J3CqBind.ab_bind 0 (by norm_num),
    CFSG.KC.BfsPin.compA_unpack cK cA, CFSG.KC.BfsPin.compA_unpack cA cK]
  change eqA 20520 (CFSG.KS.Raw.unpack 20520 15 (pcomp 20520 15 (mask 15) J3Cq.K1 J3Cq.A))
    (CFSG.KS.Raw.unpack 20520 15 (pcomp 20520 15 (mask 15) J3Cq.A J3Cq.K1)) = true
  rw [Nat.eq_of_beq_eq_true comm1]
  exact eqASelf _

theorem κComm : ∀ h < 2, κ h * J3Groups.pa = J3Groups.pa * κ h := by
  intro h hh
  interval_cases h
  · exact κComm0
  · exact κComm1

theorem kLeC : J3Groups.K ≤ centIn J3Groups.P J3Groups.pa := by
  unfold J3Groups.K J3Groups.gen
  rw [Subgroup.closure_le]
  rintro _ ⟨h, hh, rfl⟩
  exact mem_centIn.2 ⟨κP h hh, κComm h hh⟩

theorem repTK : TBfs.Rep 20520 0 TK.cnt 4 KLr (fun t => t) TK.PTS TK.POS TK.PAR TK.LAB TK.TI :=
  ⟨TBfs.hd_spec tkHd, fun k hk => TBfs.pt_spec (Raw.Orb.allN_iff.1 tkPt k hk)⟩

theorem tkCntEq : TK.cnt = 1920 := Nat.eq_of_beq_eq_true tkCnt

theorem kFree : J3Groups.K = centIn J3Groups.P J3Groups.pa ∧ TK.cnt ≤ Nat.card J3Groups.K ∧
    ∀ g ∈ J3Groups.K, g (⟨0, root_lt repTK⟩ : Fin 20520) = ⟨0, root_lt repTK⟩ → g = 1 :=
  tree_free repTK actSK σKK kLeC (by rw [tkCntEq]; exact centLe)

theorem kCard : Nat.card J3Groups.K = 1920 := by
  have h1 := kFree.2.1
  have h2 : Nat.card J3Groups.K ≤ 1920 := by
    rw [kFree.1]
    exact centLe
  rw [tkCntEq] at h1
  omega

theorem kRep : ∀ g ∈ J3Groups.K, ∃ k < TK.cnt,
    r32 TK.PTS k = (g (⟨0, root_lt repTK⟩ : Fin 20520) : Nat) ∧ g = tw σK TK.PAR TK.LAB k :=
  (card_of_free repTK actSK σKK
    (fun _ hg => tree_closed repTK actSK (kRange hg)) kFree.2.2).2

theorem kP : J3Groups.K ≤ J3Groups.P := fun _ hg => (mem_centIn.1 (kLeC hg)).1

end CertificateChecks.KernelSpor.J3CGlue

end
