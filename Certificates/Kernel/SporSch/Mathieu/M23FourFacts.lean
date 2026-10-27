module

public import Certificates.Kernel.SporSch.Mathieu.M23FourChecks
public import Certificates.Kernel.SporSch.Mathieu.M23Facts
public import Certificates.Kernel.Sporadic.OddCore.CentGlue
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
public import Certificates.Data.GH74.BTFinCkM23
public import CFSG.Certificates.Kernel.SporSch.CodesImg
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckBase
public import CFSG.Sporadic.SmallOddCore.ClassSimple

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M23FourK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.KS.SporSch.MOC CFSG.KS.SporSch.FourK CertificateChecks.KernelSporSch
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Schreier CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu
open CertificateChecks.KernelSporSch.M23OC

theorem and_of_bAnd {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := by
  cases a <;> simp_all

theorem strictB_id (y : Nat) (f : Nat → Bool) : strictB y f = f y := by
  cases y <;> rfl

theorem hcnt : M23F.cnt = 2688 := Nat.eq_of_beq_eq_true cnt

theorem hid : idT 23 = tabT (unpack 23 5 (pidn 23 5)) := by rw [idT_tabT, idK_sound kid]

theorem tab_of_img {g : Equiv.Perm (Fin 23)} {P : Nat}
    (h : imageList g = (unpack 23 5 P).toList) : toTable g = tabT (unpack 23 5 P) := by
  rw [CFSG.KS.SporSch.CodesImg.toTable_eq_arrTable_of_img h]
  unfold CFSG.ComponentClassification.J2Cover.arrTable tabT
  apply Array.ext (by simp [unpack])
  intro i h1 h2
  simp only [Array.getElem_ofFn, Array.getElem_map]
  rw [getElem!_pos _ i (by simpa [unpack] using h1)]

abbrev gensT : Array Table := ((m23CentWords1.map (evalCodes [m23PermA, m23PermB])).map toTable).toArray

theorem gen_facts {j : Nat} (hj : j < 4) : M23F.GI j = M23C1.S j ∧ M23F.G j = pidn 23 5 ∧
    canonK 23 5 (mask 5) (23 * 5) (M23C1.S j) = true := by
  obtain ⟨h1, h2⟩ := and_of_bAnd (allN_spec gens j hj)
  obtain ⟨h2, h3⟩ := and_of_bAnd h2
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, h3⟩

theorem tabs : TabsOK 23 5 4 M23F.GI gensT := by
  refine ⟨by simp [gensT, m23CentWords1], fun j hj => ⟨?_, ?_⟩⟩
  · have hj' : j < (m23CentWords1.map (evalCodes [m23PermA, m23PermB])).length := by
      simpa [m23CentWords1] using hj
    rw [getElem!_pos _ j (by simpa [gensT] using hj'), (gen_facts hj).1]
    simp only [gensT, List.getElem_toArray, List.getElem_map]
    have h := chainC1.2.2.2.1 j hj'
    rw [List.getD_eq_getElem _ _ hj', List.getElem_map] at h
    exact tab_of_img h
  · rw [(gen_facts hj).1]
    exact (gen_facts hj).2.2

theorem pe_all : ∀ i < M23F.cnt, penumPtK 23 5 (mask 5) (23 * 5) true M23F.G M23F.GI 4 M23F.cnt
    M23F.T M23F.PL M23F.POS M23F.SRT M23F.SRI i = true :=
  fun i hi => penumSl_spec pe i (Nat.zero_le _) (by rw [hcnt] at hi; omega) hi

theorem hs_all : ∀ i < M23F.cnt, hsortPtK 23 5 (mask 5) M23F.cnt M23F.T M23F.HS M23F.HSI i =
    true :=
  fun i hi => slK_spec hs i (Nat.zero_le _) (by rw [hcnt] at hi; omega) hi

theorem closure : mulClosureH 23 gensT 3000 = hRec 23 5 M23F.cnt M23F.T M23F.PL ∧
    mulTreeOK 23 gensT (hRec 23 5 M23F.cnt M23F.T M23F.PL).1
      (hRec 23 5 M23F.cnt M23F.T M23F.PL).2.1 (hRec 23 5 M23F.cnt M23F.T M23F.PL).2.2 = true ∧
    hkeysDistinct 23 (hRec 23 5 M23F.cnt M23F.T M23F.PL).1.toList = true :=
  mulH_sound sz (fun _ hj => (gen_facts hj).2.1) tabs head pe_all hs_all

theorem canonT {i : Nat} (hi : i < M23F.cnt) : canonK 23 5 (mask 5) (23 * 5) (M23F.T i) = true :=
  penumPt_canon (pe_all i hi)

theorem four_all : ∀ j < M23F.cnt,
    fourAt 23 5 M23F.cnt M23F.T (M23CK.getD 0 clsD0).R (2 ^ 30 * 3 ^ 30) j = true := by
  intro j hj
  rw [hcnt] at hj
  have h := fun lo (hb : blk lo = true) (l : Nat) (hl : l < 448) => allBlk_spec hb l hl
  have e : ∀ lo l, Nat.add lo l = lo + l := fun _ _ => rfl
  rcases (by omega : j < 448 ∨ (448 ≤ j ∧ j < 896) ∨ (896 ≤ j ∧ j < 1344) ∨
      (1344 ≤ j ∧ j < 1792) ∨ (1792 ≤ j ∧ j < 2240) ∨ (2240 ≤ j ∧ j < 2688)) with
    h0 | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simpa [e] using h 0 b0 j h0
  · simpa [e, Nat.add_sub_cancel' h1] using h 448 b1 (j - 448) (by omega)
  · simpa [e, Nat.add_sub_cancel' h1] using h 896 b2 (j - 896) (by omega)
  · simpa [e, Nat.add_sub_cancel' h1] using h 1344 b3 (j - 1344) (by omega)
  · simpa [e, Nat.add_sub_cancel' h1] using h 1792 b4 (j - 1792) (by omega)
  · simpa [e, Nat.add_sub_cancel' h1] using h 2240 b5 (j - 2240) (by omega)

theorem fourOK_rec : Certificates.BTFinCk.fourOK 23 (hRec 23 5 M23F.cnt M23F.T M23F.PL).1
    (tabT (unpack 23 5 (M23CK.getD 0 clsD0).R)) (2 ^ 30 * 3 ^ 30) = true := by
  have hsize : (hRec 23 5 M23F.cnt M23F.T M23F.PL).1.size = M23F.cnt := by simp [hRec]
  unfold Certificates.BTFinCk.fourOK
  rw [CFSG.Sporadic.Th.allIn_eq_true]
  intro j _ hj
  rw [hsize] at hj
  have hX := canonT hj
  have h := four_all j hj
  unfold fourAt at h
  rw [strictB_id] at h
  have hcomm : Certificates.BTFinCk.commCount 23 (hRec 23 5 M23F.cnt M23F.T M23F.PL).1
      (hRec 23 5 M23F.cnt M23F.T M23F.PL).1[j]! = commCntK 23 5 M23F.cnt M23F.T (M23F.T j) := by
    unfold Certificates.BTFinCk.commCount commCntK
    rw [hsize]
    apply List.countP_congr
    intro k hk
    have hk' : k < M23F.cnt := List.mem_range.1 hk
    rw [hRec_get hk', hRec_get hj]
    unfold CFSG.Sporadic.Schreier.Native.commT
    rw [compT_unpack (canonT hk') hX, compT_unpack hX (canonT hk'),
      tblEq_unpack (canonK_pcomp (canonT hk') hX) (canonK_pcomp hX (canonT hk'))]
  rw [hcomm, hRec_get hj, invoOK_eq' (by norm_num), compT_unpack hX hX, hid,
    tblEq_unpack (canonK_pcomp hX hX) idc, tblEq_unpack hX idc, tblEq_unpack hX rc]
  simpa using h

theorem fourCk : Certificates.BTFinCk.M23.m23FourCk = true := by
  have hu : toTable (m23InvReps.getD 0 1) = tabT (unpack 23 5 (M23CK.getD 0 clsD0).R) :=
    tab_of_img imgRep0
  unfold Certificates.BTFinCk.M23.m23FourCk Certificates.BTFinCk.centFourOK
  rw [hu]
  obtain ⟨e, ht, hk⟩ := closure
  have e' : mulClosureH 23 ((m23CentWords1.map (evalCodes [m23PermA, m23PermB])).map
      toTable).toArray 3000 = hRec 23 5 M23F.cnt M23F.T M23F.PL := e
  simp only [e', Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨ht, hk⟩, by simp [hRec, hcnt]⟩, fourOK_rec⟩

end CertificateChecks.KernelSporSch.M23FourK

end
