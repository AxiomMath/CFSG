module

public import Certificates.Kernel.RouteP.Obj.Run
public import Certificates.Kernel.RouteP.Obj.Pts
public import Certificates.Kernel.RouteP.Obj.EpsGlue
public import Certificates.Kernel.RouteP.Bridge.Glue
public import Certificates.Kernel.RouteP.Bridge.Misc
public import Certificates.Kernel.RouteP.Text.Layout
public import Certificates.Kernel.RouteP.Lines.Run
public import CFSG.Certificates.Kernel.RouteP.Triple
public import CFSG.Certificates.Kernel.RouteP.TreeBFS

public section

namespace CertificateChecks.KernelRouteP

open Equiv CFSG.KC CFSG.KC.RouteP CFSG.KS.RouteP CFSG.KD.RouteP CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native

#kc_forall_tree tck_all (fun g => CFSG.KD.RouteP.tck g = true) 2 CFSG.KD.RouteP.ObjCk.t
#kc_forall_tree invck_all (fun g => CFSG.KD.RouteP.invck g = true) 220 CFSG.KD.RouteP.ObjCk.i
#kc_forall_tree commck_all (fun g => CFSG.KD.RouteP.commck g = true) 2420 CFSG.KD.RouteP.ObjCk.c
#kc_forall_tree pck_all (fun g => CFSG.KD.RouteP.pck g = true) 264 CFSG.KD.RouteP.ObjCk.p
#kc_forall_tree abck_all (fun g => CFSG.KD.RouteP.abck g = true) 48 CFSG.KD.RouteP.ObjCk.a

theorem ap_of_ptOK {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {T : Table} {r x y : Nat}
    (hT : Rep 920808 T (gT NW KA KB r)) (hl : LOK NW KA KB (Int.ofNat (r + 1))) (hx : x < 920808)
    (hy : y < 920808) (h : ptOK NW KA KB [((r + 1 : Nat) : Int)] x y = true) : ap T y = x := by
  have e := ptOK_spec (fun z hz => by rw [List.mem_singleton] at hz; subst hz; exact hl) hx hy h
  rw [eW_cons] at e
  have e2 : ((gT NW KA KB r)⁻¹ ⟨x, hx⟩).val = y := by
    rw [gT_inv_apply hl]
    exact e
  have e3 : (⟨y, hy⟩ : Fin 920808) = (gT NW KA KB r)⁻¹ ⟨x, hx⟩ := Fin.ext e2.symm
  rw [hT y hy, idx_of_lt _ hy, Perm.smul_def, e3]
  simp

theorem wordG_one_of_id {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {w : List ℤ} (hz : ∀ z ∈ w, z ≠ 0)
    (hw : WOK NW KA KB w) (h : ∀ k < 19, idOK NW w k = true) (hk : idKOK NW KA KB w = true) :
    wordG (ρT NW KA KB) w = 1 :=
  wordG_eq_one (NW := NW) (KA := KA) (KB := KB) (ρT NW KA KB) id (u := w)
    (fun l hl y => ρT_apply (hz l hl) (hw l hl) y) (by rw [List.map_id]; exact hw)
    (by rw [List.map_id]; exact h) (by rw [List.map_id]; exact hk)

theorem idck_spec {w : List ℤ} (h : ∀ k < 20, idck w k = true) :
    (∀ k < 19, idOK NWO w k = true) ∧ idKOK NWO KAO KBO w = true := by
  refine ⟨fun k hk => ?_, ?_⟩
  · have e := h k (by omega)
    unfold idck at e
    rw [Nat.blt_eq.mpr hk] at e
    exact e
  · have e := h 19 (by omega)
    unfold idck at e
    rw [show Nat.blt 19 19 = false from rfl] at e
    exact e

theorem lokO_reg {r : Nat} (hr : r < 58) : LOK NWO KAO KBO (Int.ofNat (r + 1)) := lokO (by simp; omega)

theorem lokO_pos {r : Nat} (hr : r < 58) : LOK NWO KAO KBO ((r + 1 : Nat) : ℤ) := lokO (by simp; omega)

theorem lokO_neg {r : Nat} (hr : r < 58) : LOK NWO KAO KBO (-((r + 1 : Nat) : ℤ)) := lokO (by simp; omega)

theorem eps_sq {j : Nat} (hj : j < 11) : gO (epsReg j) * gO (epsReg j) = 1 := by
  have hr : epsReg j < 58 := by unfold epsReg; omega
  have hck : ∀ k < 20, idck [oL (epsReg j), oL (epsReg j)] k = true := by
    intro k hk
    have h := invck_all (20 * j + k) (by have h' : 20 * j + k < 220 := (by omega); exact h')
    unfold invck at h
    have e1 : Nat.mod (20 * j + k) 20 = k := by change (20 * j + k) % 20 = k; omega
    have e2 : Nat.div (20 * j + k) 20 = j := by change (20 * j + k) / 20 = j; omega
    rw [e1, e2] at h
    exact h
  obtain ⟨h1, h2⟩ := idck_spec hck
  have hw := wordG_one_of_id (KA := KAO) (KB := KBO)
    (by intro z hz; simp only [oL, List.mem_cons, List.not_mem_nil, or_false] at hz; omega)
    (by
      intro z hz
      simp only [oL, List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl <;> exact lokO_pos hr) h1 h2
  simp only [wordG, oL, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    ρT_pos] at hw
  rw [← mul_inv_rev, inv_eq_one] at hw
  exact hw

theorem eps_comm {i j : Nat} (hi : i < 11) (hj : j < i) :
    gO (epsReg i) * gO (epsReg j) = gO (epsReg j) * gO (epsReg i) := by
  have hri : epsReg i < 58 := by unfold epsReg; omega
  have hrj : epsReg j < 58 := by unfold epsReg; omega
  have hck : ∀ k < 20,
      idck [oL (epsReg i), oL (epsReg j), -oL (epsReg i), -oL (epsReg j)] k = true := by
    intro k hk
    have h := commck_all (20 * (11 * i + j) + k)
      (by have h' : 20 * (11 * i + j) + k < 2420 := (by omega); exact h')
    unfold commck at h
    have e1 : Nat.mod (20 * (11 * i + j) + k) 20 = k := by
      change (20 * (11 * i + j) + k) % 20 = k; omega
    have e2 : Nat.div (20 * (11 * i + j) + k) 20 = 11 * i + j := by
      change (20 * (11 * i + j) + k) / 20 = 11 * i + j; omega
    have e3 : Nat.div (11 * i + j) 11 = i := by change (11 * i + j) / 11 = i; omega
    have e4 : Nat.mod (11 * i + j) 11 = j := by change (11 * i + j) % 11 = j; omega
    rw [e2] at h
    beta_reduce at h
    rw [e3, e4, Nat.blt_eq.mpr hj, e1] at h
    exact h
  obtain ⟨h1, h2⟩ := idck_spec hck
  have hw := wordG_one_of_id (KA := KAO) (KB := KBO)
    (by intro z hz; simp only [oL, List.mem_cons, List.not_mem_nil, or_false] at hz; omega)
    (by
      intro z hz
      simp only [oL, List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact lokO_pos hri
      · exact lokO_pos hrj
      · exact lokO_neg hri
      · exact lokO_neg hrj) h1 h2
  simp only [wordG, oL, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    ρT_pos, ρT_neg] at hw
  calc gO (epsReg i) * gO (epsReg j)
      = gO (epsReg j) * gO (epsReg i) * ((gO (epsReg i))⁻¹ * ((gO (epsReg j))⁻¹ *
          (gO (epsReg i) * gO (epsReg j)))) := by group
    _ = gO (epsReg j) * gO (epsReg i) := by rw [hw, mul_one]

theorem planeArr_lt : ∀ i < 24, planeArr[i]! < 920808 ∧ planeArr[planeAArr[i]!]! < 920808 ∧
    planeArr[planeBArr[i]!]! < 920808 := by
  decide +kernel

theorem zpTreeOK_of (hm : Rep 920808 (mTabs ())[0]! (gP 0) ∧ Rep 920808 (mTabs ())[1]! (gP 1)) :
    zpTreeOK (genTabs ()) = true := by
  have hzl : ∀ l ∈ zpLetters, l < 22 := by decide
  have hap : ∀ l ∈ zpLetters, ∀ x (hx : x < 920808),
      ap (genTabs ())[l]! x = eL NWP KAP KBP (cq ((l + 1 : Nat) : ℤ)) x := by
    intro l hl x hx
    rw [ap_genTabs hm (hzl l hl) hx]
    exact (gq_act (hzl l hl) ⟨x, hx⟩).1
  have hzL : zpL = zpLetters.toList.map fun l => cq ((l + 1 : Nat) : ℤ) := by decide
  have hg : ∀ z ∈ zpL, LOK NWP KAP KBP z := by
    intro z hz
    simp only [zpL, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact lokP (by decide)
  obtain ⟨hroot, hcl, hmin, hcnt⟩ := orb_spec (by decide) hg BridgeCk.zp
  set S := closeS NWP KAP KBP zpL 33 (single 1479)
  have hF : ∀ l ∈ zpLetters, ∀ x < degree, ap (genTabs ())[l]! x < degree := by
    intro l hl x hx
    rw [ap_genTabs hm (hzl l hl) hx]
    exact (gq l ⟨x, hx⟩).isLt
  have hsize : (CFSG.Perm.Native.treeBFS degree 1479 (genTabs ()) zpLetters).pts.size = 31671 := by
    refine treeBFS_size (O := fun x => decide (x < 920808) && memS S x) hn32 (by decide) hF
      (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨by decide, hroot⟩)
      (fun x hx => by simp only [Bool.and_eq_true, decide_eq_true_eq] at hx; exact hx.1)
      (fun x hx l hl => ?_) (fun P hP0 hP x hx => ?_) ?_
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hx ⊢
      have hz : cq ((l + 1 : Nat) : ℤ) ∈ zpL := by
        rw [hzL]
        exact List.mem_map.2 ⟨l, by simpa using hl, rfl⟩
      rw [hap l hl x hx.1]
      exact ⟨eL_lt (hg _ hz) hx.1, hcl x hx.1 hx.2 _ hz⟩
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
      refine hmin P hP0 (fun N hN z hz => ?_) x hx.1 hx.2
      rw [hzL] at hz
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hz
      have hl' : l ∈ zpLetters := by simpa using hl
      by_cases hN' : N < 920808
      · rw [← hap l hl' N hN']
        exact hP N hN l hl'
      · unfold eL
        rw [if_neg hN']
        exact hN
    · rw [← hcnt]
      exact congrArg List.length (List.filter_congr fun x hx => by
        have hx' : x < 920808 := List.mem_range.1 hx
        simp [hx'])
  unfold zpTreeOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨hsize, treeOK_treeBFS hn32 (by decide) hF (fun l hl => by have := hzl l hl; omega)⟩

theorem objOKAt_of (hmO : Rep 920808 (mTabs ())[0]! (gO 0) ∧ Rep 920808 (mTabs ())[1]! (gO 1))
    (hmP : Rep 920808 (mTabs ())[0]! (gP 0) ∧ Rep 920808 (mTabs ())[1]! (gP 1)) :
    objOKAt (objRun ()) (genTabs ()) = true := by
  have hR : ∀ r < 58, Rep 920808 (objRun ()).1[r]! (gO r) := objRun_rep
  have hrun := mRun_flag (extra := 57) (prog := objProg ()) hmO objProg_ok
  have hpt : ∀ {r x y : Nat}, r < 58 → x < 920808 → y < 920808 →
      ptOK NWO KAO KBO [oL r] x y = true → ap (objRun ()).1[r]! y = x :=
    fun hr hx hy h => ap_of_ptOK (hR _ hr) (lokO_reg hr) hx hy h
  unfold objOKAt
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hrun.1, hrun.2⟩, objProg_ok⟩, dataOK_true⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩,
    epsTreeOK_of_rep hR⟩, genTabs_size⟩, zpTreeOK_of hmP⟩, tripleCheck_eq_true⟩
  ·
    have h0 := tck_all 0 (by decide)
    have h1 := tck_all 1 (by decide)
    unfold tck at h0 h1
    rw [show Nat.beq 0 0 = true from rfl] at h0
    rw [show Nat.beq 1 0 = false from rfl] at h1
    unfold tauOK
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨hpt (by decide) (by decide) (by decide) h0, hpt (by decide) (by decide) (by decide) h1⟩
  ·
    unfold epsInvOK
    rw [allIn_eq_true]
    intro j _ hj
    exact invoOK_of_rep (hR _ (by unfold epsReg; omega)) (eps_sq hj)
  ·
    unfold epsCommOK
    rw [allIn_eq_true]
    intro i _ hi
    rw [allIn_eq_true]
    intro j _ hj
    exact commOK_of_rep (hR _ (by unfold epsReg; omega)) (hR _ (by unfold epsReg; omega))
      (eps_comm hi hj)
  ·
    unfold epsPlaneOK
    rw [allIn_eq_true]
    intro j _ hj
    rw [allIn_eq_true]
    intro i _ hi
    rw [beq_iff_eq]
    have h := pck_all (24 * j + i) (by have h' : 24 * j + i < 264 := (by omega); exact h')
    unfold pck at h
    have e1 : Nat.mod (24 * j + i) 24 = i := by change (24 * j + i) % 24 = i; omega
    have e2 : Nat.div (24 * j + i) 24 = j := by change (24 * j + i) / 24 = j; omega
    rw [e1, e2] at h
    have hp := (planeArr_lt i hi).1
    exact hpt (by unfold epsReg; omega) hp hp h
  ·
    unfold abPlaneOK
    rw [allIn_eq_true]
    intro i _ hi
    simp only [Bool.and_eq_true, beq_iff_eq]
    obtain ⟨hp, hpa, hpb⟩ := planeArr_lt i hi
    have ha := abck_all i (by have h' : i < 48 := (by omega); exact h')
    have hb := abck_all (24 + i) (by have h' : 24 + i < 48 := (by omega); exact h')
    unfold abck at ha hb
    have e1 : Nat.mod i 24 = i := by change i % 24 = i; omega
    have e2 : Nat.mod (24 + i) 24 = i := by change (24 + i) % 24 = i; omega
    rw [e1, Nat.blt_eq.mpr hi] at ha
    have e3 : Nat.blt (24 + i) 24 = false := by
      cases h : Nat.blt (24 + i) 24
      · rfl
      · exact absurd (Nat.blt_eq.mp h) (by omega)
    rw [e2, e3] at hb
    exact ⟨hpt (by decide) hpa hp ha, hpt (by decide) hpb hp hb⟩

end CertificateChecks.KernelRouteP

end
