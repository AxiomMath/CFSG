module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Om
public import CFSG.Sporadic.J4.QTProof
public import Certificates.Kernel.J4M2.C7951Checks
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Om
public import CFSG.Sporadic.J4
import CFSG.Certificates.Kernel.J4Q.VOrbBFS
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPrimeCompatibility
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.J4.QT2LocCntMainBase
public import CFSG.Sporadic.J4.QTOutChar
public import CFSG.Sporadic.J4.QTRankInvProof
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootGroups
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import Certificates.Certificate43

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4M2

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT
  CFSG.Quasithin.J4M2 CertificateChecks.KernelJ4Q Matrix

theorem pt77_conj {G : Type*} [Group G] {t η u : G} (h : t⁻¹ * η * t * u = u * (t⁻¹ * η * t)) :
    η * t * u = t * u * t⁻¹ * η * t :=
  calc η * t * u = t * (t⁻¹ * η * t * u) := by group
    _ = t * (u * (t⁻¹ * η * t)) := by rw [h]
    _ = t * u * t⁻¹ * η * t := by group

theorem pt77_vec {t η u : J} (hc : t⁻¹ * η * t * u = u * (t⁻¹ * η * t))
    {a b : Fin 112 → ZMod 2} (hb : b ᵥ* Mx t = a ᵥ* Mx t ᵥ* Mx u) :
    a ᵥ* Mx η ᵥ* Mx t ᵥ* Mx u = b ᵥ* Mx η ᵥ* Mx t := by
  have hb' : b = a ᵥ* Mx (t * u * t⁻¹) := by
    calc b = b ᵥ* Mx (t * t⁻¹) := by rw [mul_inv_cancel, map_one, vecMul_one]
      _ = b ᵥ* Mx t ᵥ* Mx t⁻¹ := by rw [map_mul, vecMul_vecMul]
      _ = a ᵥ* Mx (t * u * t⁻¹) := by rw [hb]; simp only [map_mul, vecMul_vecMul]
  have e1 : a ᵥ* Mx η ᵥ* Mx t ᵥ* Mx u = a ᵥ* Mx (η * t * u) := by
    simp only [map_mul, vecMul_vecMul]
  have e2 : b ᵥ* Mx η ᵥ* Mx t = a ᵥ* Mx (t * u * t⁻¹ * η * t) := by
    rw [hb']
    simp only [map_mul, vecMul_vecMul]
  rw [e1, e2, pt77_conj hc]

theorem pt77_shl (k : Nat) : Nat.shiftLeft 1 k = 2 ^ k := (Nat.shiftLeft_eq 1 k).trans (one_mul _)

section Sound


theorem pt77One_sound {i : Nat} (hi : i < 77) {x : Nat × Nat × Nat × Nat}
    (h : pt77One (getN one (tOf gL) i) x = true) :
    ∃ c ∈ pt77Masks, (ptElt i)⁻¹ * eta uJ 11 c * ptElt i ∉ Eg uJ 11 := by
  obtain ⟨ci, j, k, w⟩ := x
  unfold pt77One at h
  simp only [andB_eq, Bool.and_eq_true, strictB_eq, notB_eq, Bool.not_eq_true'] at h
  obtain ⟨hci, hj, hk, hw, ha, hb⟩ := h
  have hci' := lt_of_blt hci
  have hj' := lt_of_blt hj
  have hk' := lt_of_blt hk
  have hw' : w < 2 ^ 112 := by
    have := lt_of_blt hw
    rwa [pt77_shl] at this
  have hl : pt77Masks.length = 7 := rfl
  have hmem : getN 0 pt77Masks ci ∈ pt77Masks := by
    rw [getN_eq_getD, List.getD_eq_getElem _ _ (by rw [hl]; exact hci')]
    exact List.getElem_mem _
  refine ⟨getN 0 pt77Masks ci, hmem, fun hx => ?_⟩
  have hM := j4Facts.mat
  have hMt := (Mx_ptElt_wfR hM hi).1
  have hT := tMats_enc i hi
  have hU := uRowsT_enc j hj'
  have hMu : Mx (uJ j) = rowsMatrix (uRowsT[j]?.getD (idRows ())) := by
    have e : uRowsT[j]?.getD (idRows ()) = CFSG.Quasithin.J4M2.wordT (uWord j) := by
      simp [uRowsT, hj']
    rw [e, Mx_uJ' hM hj']
  have hE := etaM_enc (getN 0 pt77Masks ci)
  have hMe := (rowsMatrix_etaM hM (getN 0 pt77Masks ci)).symm
  have hk2 : (2 : Nat) ^ k < 2 ^ 112 := Nat.pow_lt_pow_right (by norm_num) hk'
  have hv : Nat.shiftLeft 1 k = v2N (natToV2 (2 ^ k)) := by
    rw [pt77_shl, v2N_natToV2 hk2]
  have hV : (natToV2 (2 ^ k)).wf = true := wf_of_lt (by rw [v2N_natToV2 hk2]; exact hk2)
  have hW : (natToV2 w).wf = true := wf_of_lt (by rw [v2N_natToV2 hw']; exact hw')
  have hwv : w = v2N (natToV2 w) := (v2N_natToV2 hw').symm
  rw [← hT.2, ← hU.2, hv, hwv] at ha
  rw [← hT.2, ← hU.2, ← hE.2, hv, hwv] at hb
  rw [← v2N_frApply hK hT.1 hW, ← v2N_frApply hK hT.1 hV,
    ← v2N_frApply hK hU.1 (wf_frApply hT.1 _)] at ha
  rw [← v2N_frApply hK hE.1 hV, ← v2N_frApply hK hT.1 (wf_frApply hE.1 _),
    ← v2N_frApply hK hU.1 (wf_frApply hT.1 _), ← v2N_frApply hK hE.1 hW,
    ← v2N_frApply hK hT.1 (wf_frApply hE.1 _)] at hb
  have ha' := congrArg V2.toVec (CFSG.KC.J4Q.VOrbBFS.v2N_inj (Nat.eq_of_beq_eq_true ha))
  simp only [frApply_toVec_eq_vecMul, ← hMt, ← hMu] at ha'
  have hc := Eg_comm (elem_uJ hM) hx (u_mem_Eg hj')
  have key := pt77_vec hc ha'
  rw [hMe, hMt, hMu] at key
  simp only [← frApply_toVec_eq_vecMul] at key
  rw [V2.toVec_inj (wf_frApply hU.1 _) (wf_frApply hT.1 _)] at key
  rw [key] at hb
  simp at hb

theorem pt77_sound : ∀ i, 0 < i → i < 77 → ∃ c ∈ pt77Masks,
    (ptElt i)⁻¹ * eta uJ 11 c * ptElt i ∉ Eg uJ 11 := by
  intro i hi0 hi
  have h := allR_spec pt77_chk (i - 1) (by omega)
  have e : Nat.succ (i - 1) = i := by omega
  rw [e] at h
  exact pt77One_sound hi h

end Sound

theorem c7951 :
 ∀ i, 0 < i → i < 77 → ∃ c ∈ [133, 778, 911, 1131, 1262, 1889, 2020],
    (CFSG.Quasithin.J4M2.ptElt i)⁻¹ * CFSG.Sporadic.J4.QT.eta CFSG.Sporadic.J4.QT.uJ 11 c *
      CFSG.Quasithin.J4M2.ptElt i ∉ CFSG.Sporadic.J4.QT.Eg CFSG.Sporadic.J4.QT.uJ 11 := pt77_sound

end CertificateChecks.KernelJ4M2

end
