module

public import CFSG.Certificates.Kernel.Sp6Two.X1Sound
public import Certificates.Kernel.Sp6Two.X1Checks
public import Certificates.Kernel.Sp6Two.Final

public section

namespace CFSG.KD.Sp62X1

open CFSG.KD.Sp62 CFSG.KD.Sp6Two CFSG.KC.Sp62 CFSG.KC.Sp6Two CFSG.KC.Sp62X1 CFSG.KC.Loop
  CFSG.Quasithin.H13.U3 CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U

theorem sylow4195 : closureOK (sylowP.map Prod.fst) sylowT 512 = true ∧
    ∀ t < 512, canon6 (sylowT.getD t []) = true ∧ pk (sylowT.getD t []) = recX REC 34728 t :=
  closureKG_ok rfl (by decide) (by decide) (by decide) (by decide +kernel) tabS_ok (by decide)
    (by decide) (by decide)

theorem gensA_pk : ∀ s < 6, canon6 (sp62AC.getD s []) = true ∧
    pk (sp62AC.getD s []) = at2 XR 0 s := by
  decide +kernel

theorem tabA4195 : closureOK sp62AC (closureT sp62AC) 64 = true ∧
    ∀ t < 64, canon6 ((closureT sp62AC).getD t []) = true ∧
      pk ((closureT sp62AC).getD t []) = recX XR 16 t :=
  closureKG_ok rfl (by decide) (by decide) (by decide) gensA_pk tabA_ok (by decide) (by decide)
    (by decide)

theorem peelSeq_canon : sp62PeelSeq.all canon6 = true := by decide +kernel

theorem pairY0 : pairT (sp62Y0, sp62Y0) = true := by decide +kernel
theorem pairY1 : pairT (sp62Y1, sp62Y1) = true := by decide +kernel
theorem pairY2 : pairT (sp62Y2, sp62Y2) = true := by decide +kernel
theorem pairY3 : pairT (sp62Y3, sp62Y3) = true := by decide +kernel

theorem yOK_of {T : Array (List ℕ)} {o n i : ℕ} {y : List ℕ} (hT : T.size = n)
    (hr : ∀ t < n, canon6 (T.getD t []) = true ∧ pk (T.getD t []) = recX REC o t)
    (hp : pairT (y, y) = true)
    (hres : (sp62PeelRes sp62Invs sp62PeelSeq).map pk = resN invL peelL ∧
      ∀ c ∈ sp62PeelRes sp62Invs sp62PeelSeq, canon6 c = true)
    (h : (inTab REC o n i (pk y) && allL (fun w => commN w (pk y)) (resN invL peelL)) = true) :
    sp62YOK T y = true := by
  have hy : canon6 y = true := by
    simp only [pairT, Bool.and_eq_true] at hp
    exact hp.1.1.1
  rw [Bool.and_eq_true] at h
  unfold sp62YOK
  rw [pairCheck_of hp, found_of_inTab hT hr hy h.1, all_pk hy hres.2, hres.1, h.2]
  rfl

theorem sp62X1OK_ok : sp62X1OK = true := by
  have hS := sylow4195
  have hSs := size_of_closureOK hS.1
  have hgm : sp62AGens.map Prod.fst = sp62AC := by simp [sp62AGens, Function.comp_def]
  have hA := tabA4195
  have hPc := List.all_eq_true.1 peelSeq_canon
  have hI : sp62Invs.map pk = ((List.range 512).map (recX REC 34728)).filter invN ∧
      ∀ c ∈ sp62Invs, canon6 c = true := invs_pk hSs hS.2
  have hres : (sp62PeelRes sp62Invs sp62PeelSeq).map pk = resN invL peelL ∧
      ∀ c ∈ sp62PeelRes sp62Invs sp62PeelSeq, canon6 c = true := by
    have r := res_pk sp62PeelSeq hPc hI.2
    rw [hI.1] at r
    exact r
  have hpairs : sp62AGens.all pairCheck = true := all_pairs (by decide +kernel)
  have hgs : sp62AGens.all (fun cc => sylowT.contains cc.1) = true := by
    rw [List.all_eq_true]
    intro cc hcc
    simp only [sp62AGens, List.mem_map] at hcc
    obtain ⟨c, hc, rfl⟩ := hcc
    obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem hc
    have hl : sp62AC.length = 6 := rfl
    have hs6 : s < 6 := hl ▸ hs
    have hg := gensA_pk s hs6
    rw [List.getD_eq_getElem _ _ hs] at hg
    refine contains_of_inTab (i := at2 XR 6 s) hSs hS.2 hg.1 ?_
    rw [hg.2]
    exact CFSG.KC.G2Three.allBelow_g2 gensA_ok (by decide) s hs6
  have hcl : closureOK (sp62AGens.map Prod.fst) sp62ATab 64 = true := by
    unfold sp62ATab
    rw [hgm]
    exact hA.1
  have habl : sp62ATab.all (fun c => mul6 c c == one6 && sp62ATab.all fun c' => commutes6 c c') =
      true := by
    unfold sp62ATab
    rw [hgm]
    exact all_tab (size_of_closureOK hA.1) hA.2 abelA_ok (by decide)
  have hpeel : sp62PeelOK 62 sp62Invs sp62PeelSeq = true := by
    rw [peel_pk 62 sp62PeelSeq hPc hI.2, hI.1]
    exact peelA_ok
  unfold sp62X1OK
  rw [hpairs, hgs, hcl, habl, hpeel,
    yOK_of orb0_8151.2.1 orb0_8151.2.2 pairY0 hres y0A_ok,
    yOK_of orb1_8151.2.1 orb1_8151.2.2 pairY1 hres y1A_ok,
    yOK_of orb2_8151.2.1 orb2_8151.2.2 pairY2 hres y2A_ok,
    yOK_of orb3_8151.2.1 orb3_8151.2.2 pairY3 hres y3A_ok]
  rfl

end CFSG.KD.Sp62X1

end
