module

public import Certificates.Kernel.ONOutK3.Cover
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONK3

open CFSG.KC.Enum CFSG.KC.ONK3 CFSG.KS.ONK3 CFSG.KS.Bfs3 CFSG.KS.BfsReplay
open CFSG.ONSchreier.Native
open CertificateChecks.KernelSpor.ON3 (ZT)

local notation "fParA" => CFSG.ComponentClassification.SolMax.ONOut.fPar
local notation "fLabA" => CFSG.ComponentClassification.SolMax.ONOut.fLab
local notation "fImA" => CFSG.ComponentClassification.SolMax.ONOut.fIm

theorem fFix0 : Nat.beq (mapK (evalWK (uG G UL UW) (FW 0)) BK) (mapK (fG G 0) BK) = true := by
  quickRfl

theorem fFix1 : Nat.beq (mapK (evalWK (uG G UL UW) (FW 1)) BK) (mapK (fG G 1) BK) = true := by
  quickRfl

theorem fComm0 : Nat.beq (mapK (fun p => evalFK G (CX 0) (evalFK G (CY 0) p)) BK)
    (mapK (fun p => fG G 0 (evalFK G (CY 0) (evalFK G (CX 0) p))) BK) = true := by
  quickRfl

theorem fComm1 : Nat.beq (mapK (fun p => evalFK G (CX 1) (evalFK G (CY 1) p)) BK)
    (mapK (fun p => fG G 1 (evalFK G (CY 1) (evalFK G (CX 1) p))) BK) = true := by
  quickRfl

theorem fPar_eq : fParA = Array.ofFn (n := 60) fun i => CFSG.KC.ONK3.fPar (fRec FL i.val) := by
  unfold CFSG.ComponentClassification.SolMax.ONOut.fPar
  rw [fTree_eq]

theorem fLab_eq : fLabA = Array.ofFn (n := 60) fun i => CFSG.KC.ONK3.fLab (fRec FL i.val) := by
  unfold CFSG.ComponentClassification.SolMax.ONOut.fLab
  rw [fTree_eq]

theorem BK_fields : tA BK = 0 ∧ tB BK = 227759 ∧ tC BK = 100817 := by
  rw [tA_eq, tB_eq, tC_eq]
  exact ⟨rfl, rfl, rfl⟩

theorem mapK_BK (g : Nat → Nat) : mapK g BK = key3 (g 0) (g 227759) (g 100817) := by
  unfold mapK
  rw [BK_fields.1, BK_fields.2.1, BK_fields.2.2]

theorem key3_inj2 {a b c a' b' c' : Nat} (ha : a < 2 ^ 18) (hb : b < 2 ^ 18) (hc : c < 2 ^ 18)
    (ha' : a' < 2 ^ 18) (hb' : b' < 2 ^ 18) (hc' : c' < 2 ^ 18) (h : key3 a b c = key3 a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  rw [key3_eq, key3_eq] at h
  omega

theorem lt18 {x : Nat} (hx : x < 245520) : x < 2 ^ 18 := Nat.lt_trans hx NP_lt

theorem evalFW_eq : ∀ (w : List Nat), (∀ a ∈ w, a < 2) → ∀ x < 245520,
    CFSG.ComponentClassification.SolMax.ONOut.evalFW w x = evalFK G w x ∧ evalFK G w x < 245520
  | [], _, x, hx => ⟨rfl, hx⟩
  | a :: w, hw, x, hx => by
    obtain ⟨e, hlt⟩ := evalFW_eq w (fun b hb => hw b (List.mem_cons_of_mem a hb)) x hx
    have ha := hw a List.mem_cons_self
    have e1 : CFSG.ComponentClassification.SolMax.ONOut.evalFW (a :: w) x =
        CFSG.ComponentClassification.SolMax.ONOut.evalW CFSG.ComponentClassification.SolMax.ONOut.hArrs
          CFSG.ComponentClassification.SolMax.ONOut.fw[a]!
          (CFSG.ComponentClassification.SolMax.ONOut.evalFW w x) := rfl
    have e2 : evalFK G (a :: w) x = fG G a (evalFK G w x) := rfl
    rw [e1, e2, e, (fStep_eq ha hlt).1]
    exact ⟨rfl, (fStep_eq ha hlt).2⟩

theorem CX_lets {l : Nat} (hl : l < 2) : ∀ a ∈ CX l, a < 2 := by
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> decide

theorem CY_lets {l : Nat} (hl : l < 2) : ∀ a ∈ CY l, a < 2 := by
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> decide

theorem commX_eq {l : Nat} (hl : l < 2) :
    CFSG.ComponentClassification.SolMax.ONOut.commX[l]! = CX l := by
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl

theorem commY_eq {l : Nat} (hl : l < 2) :
    CFSG.ComponentClassification.SolMax.ONOut.commY[l]! = CY l := by
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl

theorem base3_pt : CFSG.ComponentClassification.SolMax.ONOut.base3 = (0, 227759, 100817) := rfl

open CFSG.ComponentClassification.SolMax.ONOut in
theorem f_tree : treeOK 60 2 fStep base3 fParA fLabA fImA = true := by
  have := treeOK_of_R3 RF
  rw [← fPar_eq, ← fLab_eq, ← fIm_eq] at this
  exact this

open CFSG.ComponentClassification.SolMax.ONOut in
theorem f_size : ((fImA).size == 60) = true := by
  rw [fIm_size]
  rfl

open CFSG.ComponentClassification.SolMax.ONOut in
theorem f_dist : distinctOK 60 fImA = true := distinctOK_of_inj fIm_size fIm_inj

open CFSG.ComponentClassification.SolMax.ONOut in
theorem f_closed : fClosedOK = true := by
  unfold fClosedOK
  rw [CFSG.ONSchreier.allBelowN_iff]
  intro j hj
  rw [CFSG.ONSchreier.allBelowN_iff]
  intro l hl
  obtain ⟨p1, p2, -⟩ := RF.close j hj l hl
  have e : fStep l fImA[j]! = fImA[CFSG.KC.ONK3.fPos (fRec FL j) l]! := by
    rw [fIm_get hj, fIm_get p1]
    exact p2
  rw [e]
  exact (posMap3_mem fIm_size fIm_inj _).2 ⟨_, p1, rfl⟩

open CFSG.ComponentClassification.SolMax.ONOut in
theorem f_noz : fNoZOK = true := by
  unfold fNoZOK
  rw [CFSG.ONSchreier.allBelowN_iff]
  intro j hj
  cases h : (fImA[j]! == zIm)
  · rfl
  · exfalso
    have e := beq_iff_eq.1 h
    rw [fIm_get hj] at e
    unfold zIm TF map3 at e
    rw [base3_pt] at e
    simp only [Prod.mk.injEq] at e
    rw [zA_get (by decide), zA_get (by decide), zA_get (by decide)] at e
    apply (f_at hj).noz
    rw [← key3_tK, e.1, e.2.1, e.2.2, mapK_BK]
    rfl

open CFSG.ComponentClassification.SolMax.ONOut in
theorem f_fix_of {l : Nat} (hl : l < 2)
    (hk : mapK (evalWK (uG G UL UW) (FW l)) BK = mapK (fG G l) BK) :
    (map3 (evalW vArrs fw[l]!) base3 == map3 (evalW hArrs fw[l]!) base3) = true := by
  rw [beq_iff_eq, fw_eq hl, base3_pt]
  rw [mapK_BK, mapK_BK] at hk
  have v0 := evalW_v (FW l) (FW_lets hl) 0 (by decide)
  have v1 := evalW_v (FW l) (FW_lets hl) 227759 (by decide)
  have v2 := evalW_v (FW l) (FW_lets hl) 100817 (by decide)
  have g0 := evalW_h (FW l) (FW_lets hl) 0 (by decide)
  have g1 := evalW_h (FW l) (FW_lets hl) 227759 (by decide)
  have g2 := evalW_h (FW l) (FW_lets hl) 100817 (by decide)
  obtain ⟨k1, k2, k3⟩ := key3_inj2 (lt18 v0.2) (lt18 v1.2) (lt18 v2.2) (lt18 g0.2) (lt18 g1.2)
    (lt18 g2.2) hk
  unfold map3
  dsimp only
  rw [v0.1, v1.1, v2.1, g0.1, g1.1, g2.1, k1, k2, k3]

open CFSG.ComponentClassification.SolMax.ONOut in
theorem f_fix : fFixOK = true := by
  unfold fFixOK
  rw [CFSG.ONSchreier.allBelowN_iff]
  intro l hl
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · exact f_fix_of (by decide) (beqT fFix0)
  · exact f_fix_of (by decide) (beqT fFix1)

open CFSG.ComponentClassification.SolMax.ONOut in
theorem f_comm_of {l : Nat} (hl : l < 2)
    (hk : mapK (fun p => evalFK G (CX l) (evalFK G (CY l) p)) BK =
      mapK (fun p => fG G l (evalFK G (CY l) (evalFK G (CX l) p))) BK) :
    (map3 (fun p => evalFW commX[l]! (evalFW commY[l]! p)) base3 ==
      map3 (fun p => evalW hArrs fw[l]! (evalFW commY[l]! (evalFW commX[l]! p))) base3) = true := by
  rw [beq_iff_eq, commX_eq hl, commY_eq hl, fw_eq hl, base3_pt]
  rw [mapK_BK, mapK_BK] at hk
  have ev : ∀ x < 245520, evalFW (CX l) (evalFW (CY l) x) = evalFK G (CX l) (evalFK G (CY l) x) ∧
      evalFK G (CX l) (evalFK G (CY l) x) < 245520 := by
    intro x hx
    obtain ⟨a1, a2⟩ := evalFW_eq _ (CY_lets hl) x hx
    obtain ⟨b1, b2⟩ := evalFW_eq _ (CX_lets hl) _ a2
    rw [a1, b1]
    exact ⟨rfl, b2⟩
  have ev2 : ∀ x < 245520, evalW hArrs (FW l) (evalFW (CY l) (evalFW (CX l) x)) =
      fG G l (evalFK G (CY l) (evalFK G (CX l) x)) ∧
      fG G l (evalFK G (CY l) (evalFK G (CX l) x)) < 245520 := by
    intro x hx
    obtain ⟨a1, a2⟩ := evalFW_eq _ (CX_lets hl) x hx
    obtain ⟨b1, b2⟩ := evalFW_eq _ (CY_lets hl) _ a2
    have := evalW_h (FW l) (FW_lets hl) _ b2
    rw [a1, b1, this.1]
    exact ⟨rfl, this.2⟩
  have e0 := ev 0 (by decide)
  have e1 := ev 227759 (by decide)
  have e2 := ev 100817 (by decide)
  have f0 := ev2 0 (by decide)
  have f1 := ev2 227759 (by decide)
  have f2 := ev2 100817 (by decide)
  obtain ⟨k1, k2, k3⟩ := key3_inj2 (lt18 e0.2) (lt18 e1.2) (lt18 e2.2) (lt18 f0.2) (lt18 f1.2)
    (lt18 f2.2) hk
  unfold map3
  dsimp only
  rw [e0.1, e1.1, e2.1, f0.1, f1.1, f2.1, k1, k2, k3]

open CFSG.ComponentClassification.SolMax.ONOut in
theorem f_comm : fCommOK = true := by
  unfold fCommOK
  rw [CFSG.ONSchreier.allBelowN_iff]
  intro l hl
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · exact f_comm_of (by decide) (beqT fComm0)
  · exact f_comm_of (by decide) (beqT fComm1)

open CFSG.ComponentClassification.SolMax.ONOut in
theorem f_ok : (treeOK 60 2 fStep base3 fParA fLabA fImA && (fImA).size == 60 && distinctOK 60 fImA &&
    fClosedOK && fNoZOK && fFixOK && fCommOK) = true := by
  rw [f_tree, f_size, f_dist, f_closed, f_noz, f_fix, f_comm]
  rfl

end CertificateChecks.KernelSpor.ONK3

end
