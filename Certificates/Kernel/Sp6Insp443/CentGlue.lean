module

public import Certificates.Kernel.Sp6Insp443.Facts
public import Certificates.Kernel.Sp6Insp443.Inv
public import Certificates.Kernel.Sp6Insp443.Cent0
public import Certificates.Kernel.Sp6Insp443.Cent1
public import Certificates.Kernel.Sp6Insp443.Cent2
public import Certificates.Kernel.Sp6Insp443.Cent3
public import Certificates.Kernel.Sp6Insp443.Cent4
public import Certificates.Kernel.Sp6Insp443.Cent5
public import Certificates.Kernel.Sp6Insp443.Cent6
public import Certificates.Kernel.Sp6Insp443.Cent7
public import Certificates.Kernel.Sp6Insp443.Cent8
public import Certificates.Kernel.Sp6Insp443.Cent9
public import Certificates.Kernel.Sp6Insp443.Cent10
public import Certificates.Kernel.Sp6Insp443.Cent11
public import Certificates.Kernel.LocalComp.Sp6J.Facts
public import CFSG.Certificates.Kernel.Sp6Insp443.CentSound
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelS6I

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Prim CFSG.KS.Sp6I
  CFSG.KS.SporSch.MOC CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.EvenSmallLie.Sp6
  CFSG.SectionRank.QTK.Insp443.Sp6 CFSG.SectionRank.QTK.Insp443.PermKit.Native
  CFSG.Quasithin.KGC31.Native CertificateChecks.KernelLC.Sp6J CertificateChecks.KernelLC.ExcGlue

theorem prepOne : PRep 36 6 One36 1 := prep_pidn (by norm_num) (by norm_num)

theorem shrOne : One36 >>> (36 * 6) = 0 := (PF.canon_facts kOne).2.2.1

theorem prepGen : ∀ j < 2, PRep 36 6 (XQ.S j) (sp6Gens.getD j 1) := fun j hj =>
  prep_of_imageList (imgX j hj)

theorem prepGenInv : ∀ j < 2, PRep 36 6 (XQ.SI j) (sp6Gens.getD j 1)⁻¹ := fun j hj =>
  prep_inv_of_permOK (pX j hj) (prepGen j hj)

theorem genMem : ∀ j < 2, sp6Gens.getD j 1 ∈ sp6Q.originalSubgroup := fun j hj => by
  apply sp6Gens_mem
  have hl : sp6Gens.length = 2 := rfl
  rw [List.getD_eq_getElem _ _ (by rw [hl]; exact hj)]
  exact List.getElem_mem _

theorem prepRep {i : Nat} (hi : i < 4) :
    PRep 36 6 (wordK 36 6 (mask 6) One36 XQ.S XQ.SI (sp6InvRepWords.getD i []))
      (sp6InvReps.getD i 1) := by
  have h := (and_of_bAnd (Orb.allN_iff.1 kWX i hi)).2
  have e : wordK 36 6 (mask 6) One36 XQ.S XQ.SI (sp6InvRepWords.getD i []) =
      wordK 36 6 (mask 6) (pidn 36 6) XQ.S XQ.SI (sp6InvRepWords.getD i []) := rfl
  rw [e, Nat.eq_of_beq_eq_true h]
  exact prep_of_imageList (rep_img i hi)

theorem centTest_of {k : Nat} (hd : ch725106d k = true) (hi : ch725106i k = true)
    {gens : List (Equiv.Perm (Fin 36))} {words : List (List Int)} {bv : Vector (Fin 36) 4}
    (hbs : bv.toList.Nodup) {PS PSI LR TR TRI : Nat → Nat} {kS BP : Nat}
    (hQ : ChainK 36 6 gens words bv PS PSI LR TR TRI kS BP 1 36)
    (hC : centralizerIn sp6Q.originalSubgroup (sp6InvReps.getD (D.cls.getD k 0) 1) ≤
      (certificate (by norm_num) gens words bv hbs).originalSubgroup)
    (hcnt : Nat.beq (centCntK 36 6 (mask 6) (36 * 6) LR TR 4 One36 (D.uP.getD k 0)
      (D.nU.getD k 0) (D.sP.getD k 0) (D.nW.getD k 0)) 0 = true)
    {g : Equiv.Perm (Fin 36)} (hg : g ∈ sp6Q.originalSubgroup) {T : Table} (hT : Rep 36 T g) :
    centTestS 36 ((candT k).getD (candI k) [])
      (spanTabs 36 ((candT k).getD (D.wIdx.getD k 0) [])) T = false := by
  unfold ch725106d at hd
  simp only [Orb.strictB_eq, Orb.bAnd_eq, Bool.and_eq_true] at hd
  obtain ⟨h1, h2, h3, -, -, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hd
  unfold ch725106i at hi
  rw [Orb.bAnd_eq, Bool.and_eq_true] at hi
  obtain ⟨c, hcH, hc⟩ := wordNK_prep (by norm_num) prepOne prepGen prepGenInv genMem _ h1
  rw [Nat.eq_of_beq_eq_true h2] at hc
  have hci := prep_inv_of_permOK h3 hc
  have hr := prepRep (Nat.le_of_ble_eq_true h12)
  rw [← Nat.eq_of_beq_eq_true h13] at hr
  exact centTestS_false_of_cnt (by norm_num) (by norm_num) (by norm_num) hbs hQ hC prepOne shrOne
    hc hci hcH h8 h9 (Nat.eq_of_beq_eq_true h6) (Nat.eq_of_beq_eq_true h7) hi.1 hi.2 h10 h11 hr h14
    (Nat.eq_of_beq_eq_true hcnt) hg hT

theorem cnt2 {k : Nat} (h : ch725106q2_ k = true) :
    Nat.beq (centCntK 36 6 (mask 6) (36 * 6) C2Q.LR C2Q.TR 4 One36 (D.uP.getD k 0)
      (D.nU.getD k 0) (D.sP.getD k 0) (D.nW.getD k 0)) 0 = true := h

theorem cnt3 {k : Nat} (h : ch725106q3_ k = true) :
    Nat.beq (centCntK 36 6 (mask 6) (36 * 6) C3Q.LR C3Q.TR 4 One36 (D.uP.getD k 0)
      (D.nU.getD k 0) (D.sP.getD k 0) (D.nW.getD k 0)) 0 = true := h

theorem cnt4 {k : Nat} (h : ch725106q4_ k = true) :
    Nat.beq (centCntK 36 6 (mask 6) (36 * 6) C4Q.LR C4Q.TR 4 One36 (D.uP.getD k 0)
      (D.nU.getD k 0) (D.sP.getD k 0) (D.nW.getD k 0)) 0 = true := h

theorem hC2 :
    centralizerIn sp6Q.originalSubgroup (sp6InvReps.getD 1 1) ≤ sp6CentQ2.originalSubgroup :=
  sp6_cent_spec₂.1.le

theorem hC3 :
    centralizerIn sp6Q.originalSubgroup (sp6InvReps.getD 2 1) ≤ sp6CentQ3.originalSubgroup :=
  sp6_cent_spec₃.1.le

theorem hC4 :
    centralizerIn sp6Q.originalSubgroup (sp6InvReps.getD 3 1) ≤ sp6CentQ4.originalSubgroup :=
  sp6_cent_spec₄.1.le

theorem cands5_centTest
    {k : Nat} (hk : k < 6) {g : Equiv.Perm (Fin 36)}
    (hg : g ∈ co3X36) {T : Table} (hT : Rep 36 T g) :
    centTestS 36 (cands5.getD k []) (spanTabs 36 (cands5.getD ([1, 1, 3, 3, 4, 4].getD k 0) []))
      T = false := by
  rw [← sp6Q_originalSubgroup] at hg
  interval_cases k
  · exact centTest_of ch725106d0 ch725106i0 (by decide) chainC3 hC3 (cnt3 ch725106q3_0) hg hT
  · exact centTest_of ch725106d1 ch725106i1 (by decide) chainC3 hC3 (cnt3 ch725106q3_1) hg hT
  · exact centTest_of ch725106d2 ch725106i2 (by decide) chainC3 hC3 (cnt3 ch725106q3_2) hg hT
  · exact centTest_of ch725106d3 ch725106i3 (by decide) chainC3 hC3 (cnt3 ch725106q3_3) hg hT
  · exact centTest_of ch725106d4 ch725106i4 (by decide) chainC3 hC3 (cnt3 ch725106q3_4) hg hT
  · exact centTest_of ch725106d5 ch725106i5 (by decide) chainC3 hC3 (cnt3 ch725106q3_5) hg hT

theorem cands7_centTest
    {k : Nat} (hk : k < 6) {g : Equiv.Perm (Fin 36)}
    (hg : g ∈ co3X36) {T : Table} (hT : Rep 36 T g) :
    centTestS 36 (cands7.getD k []) (spanTabs 36 (cands7.getD ([2, 4, 2, 2, 4, 4].getD k 0) []))
      T = false := by
  rw [← sp6Q_originalSubgroup] at hg
  interval_cases k
  · exact centTest_of ch725106d6 ch725106i6 (by decide) chainC2 hC2 (cnt2 ch725106q2_6) hg hT
  · exact centTest_of ch725106d7 ch725106i7 (by decide) chainC2 hC2 (cnt2 ch725106q2_7) hg hT
  · exact centTest_of ch725106d8 ch725106i8 (by decide) chainC4 hC4 (cnt4 ch725106q4_8) hg hT
  · exact centTest_of ch725106d9 ch725106i9 (by decide) chainC4 hC4 (cnt4 ch725106q4_9) hg hT
  · exact centTest_of ch725106d10 ch725106i10 (by decide) chainC4 hC4 (cnt4 ch725106q4_10) hg hT
  · exact centTest_of ch725106d11 ch725106i11 (by decide) chainC4 hC4 (cnt4 ch725106q4_11) hg hT

end CertificateChecks.KernelS6I

end
