module

public import Certificates.Kernel.Sp6Insp443.SubChk7
public import Certificates.Kernel.Sp6Insp443.Count7
public import CFSG.Certificates.Kernel.Sp6Insp443.SubSound

public section

namespace CertificateChecks.KernelS6I

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Sp6I CFSG.KC.KGC31P CFSG.KC.BfsPin
  CFSG.SectionRank.QTK.Insp443.Sp6 CFSG.SectionRank.QTK.Insp443.PermKit.Native
  CFSG.Quasithin.KGC31.Native CFSG.Sporadic.Th.Native
open CFSG.KC.Child3 (tabP)

theorem sz36 : szOK 36 6 = true := by decide +kernel

theorem cand7 {k : Nat} (hk : k < 6) :
    cands7.getD k [] = ((cands7.getD k []).map (packT 6)).map (tabP 36 6) ∧
      ∀ a ∈ (cands7.getD k []).map (packT 6), PP 36 6 a := by
  have hl : k < cands7.length := hk
  refine tabsK_spec sz36 (List.all_eq_true.mp ch725107k.1 _ ?_)
  rw [List.getD_eq_getElem _ _ hl]
  exact List.getElem_mem _

theorem x7_tab : x7T = tabP 36 6 (packT 6 x7T) ∧ PP 36 6 (packT 6 x7T) := by
  obtain ⟨e, h⟩ := tabsK_spec sz36 ch725107k.2
  exact ⟨List.head_eq_of_cons_eq e, h _ List.mem_cons_self⟩

theorem sub7 {k j : Nat} (hk : k < 6) (hj : j < 6)
    (h : psubOK 36 6 ((cands7.getD k []).map (packT 6)) ((cands7.getD j []).map (packT 6)) = true) :
    subOK 36 (cands7.getD k []) (cands7.getD j []) = true := by
  obtain ⟨e1, p1⟩ := cand7 hk
  obtain ⟨e2, p2⟩ := cand7 hj
  exact (congrArg₂ (subOK 36) e1 e2).trans ((subOK_tabP sz36 p1 p2).trans h)

theorem irr7 {k j : Nat} (hk : k < 6) (hj : j < 6) {R : List (List Nat)}
    (h : pirrW 36 6 7 (packT 6 x7T) (pinv 36 6 (packT 6 x7T)) ((cands7.getD k []).map (packT 6))
      ((cands7.getD j []).map (packT 6)) R = true) :
    irrOK 36 7 x7T (invT 36 x7T) (cands7.getD k []) (cands7.getD j []) = true := by
  obtain ⟨e1, p1⟩ := cand7 hk
  obtain ⟨e2, p2⟩ := cand7 hj
  obtain ⟨ex, px⟩ := x7_tab
  have key := irrOK_of_pirrW sz36 px p1 p2 h
  have tr : ∀ X U W, X = tabP 36 6 (packT 6 x7T) →
      U = ((cands7.getD k []).map (packT 6)).map (tabP 36 6) →
      W = ((cands7.getD j []).map (packT 6)).map (tabP 36 6) →
      irrOK 36 7 X (invT 36 X) U W = true := by
    rintro _ _ _ rfl rfl rfl
    exact key
  exact tr _ _ _ ex e1 e2

theorem chkP7_true :
    chkP7 () = true := by
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := ch725107b
  obtain ⟨r0, r1, r2, r3⟩ := ch725107r
  unfold chkP7
  simp only []
  rw [sub7 (by norm_num) (by norm_num) b0, sub7 (by norm_num) (by norm_num) b1,
    sub7 (by norm_num) (by norm_num) b2, sub7 (by norm_num) (by norm_num) b3,
    sub7 (by norm_num) (by norm_num) b4, sub7 (by norm_num) (by norm_num) b5,
    irr7 (by norm_num) (by norm_num) r0, irr7 (by norm_num) (by norm_num) r1,
    irr7 (by norm_num) (by norm_num) r2, irr7 (by norm_num) (by norm_num) r3, count7]
  rfl

end CertificateChecks.KernelS6I

end
