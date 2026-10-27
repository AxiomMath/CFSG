module

public import Certificates.Kernel.KGC31M12.Checks
public import Certificates.Kernel.SporSch.Mathieu.M12Facts
public import CFSG.Certificates.Kernel.KGC31PBSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelKGC31M12

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.KGC31P CFSG.KC.Child3 CFSG.KC.BfsPin
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Quasithin.KGC31.Native CFSG.Quasithin.KGC31.M12
open CertificateChecks.KernelSporSch

theorem hsz : szOK 12 4 = true := M12OC.szOK'

theorem ppA : PP 12 4 (M12Q.S 0) := CFSG.KC.HeGlueK.PP_of_permOK2 hsz M12OC.pA

theorem ppB : PP 12 4 (M12Q.S 1) := CFSG.KC.HeGlueK.PP_of_permOK2 hsz M12OC.pB

theorem ppG (l : Int) : PP 12 4 (G l) := by
  unfold G
  split
  · exact ppA
  · exact ppB

theorem gensT_eq (l : Int) : gensT l = tabP 12 4 (G l) := by
  unfold gensT G
  split
  · exact CFSG.KS.SporSch.CodesImg.toTable_eq_arrTable_of_img M12OC.imgA
  · exact CFSG.KS.SporSch.CodesImg.toTable_eq_arrTable_of_img M12OC.imgB

theorem wT (wd : List Int) : wordT 12 gensT wd = tabP 12 4 (pw wd) :=
  wordT_tabP hsz gensT_eq ppG wd

theorem ppw' (wd : List Int) : PP 12 4 (pw wd) := PP_pword hsz ppG wd

theorem ppTL : ∀ L ∈ TL, ∀ t ∈ L, PP 12 4 t := fun L hL t ht =>
  PP_of_permOK hsz (List.all_eq_true.1 (List.all_eq_true.1 kTR L hL) t ht)

theorem ppI : ∀ t ∈ I, PP 12 4 t :=
  PP_pfilterProducts hsz _ ppTL _ [] (PP.id hsz) (fun _ h => absurd h List.not_mem_nil)

theorem invs_eq : orderTables m12Certificate 2 = I.map (tabP 12 4) := by
  have hL : levelTables m12Certificate = TL.map (List.map (tabP 12 4)) :=
    levelTables_eq M12OC.chainQ (by decide) (by decide)
  have h := filterProducts_tabP (f := ordTest 12 2) (fk := pord 12 4 2)
    (fun X hX => ordTest_tabP hX 2) TL ppTL (pidn 12 4) [] (PP.id hsz)
  rw [List.map_nil] at h
  rw [orderTables, hL, idT_tabP hsz]
  exact h

theorem act_eq {m X : Nat} (hX : PP 12 4 X) (hk : actAll m X = true) :
    actCheck 12 m (orderTables m12Certificate 2) (powTabs 12 (tabP 12 4 X) m) = true := by
  rw [invs_eq, actCheck, powTabs, List.all_map, List.all_eq_true]
  intro a ha
  have hp := PP_ppw hX a
  simp only [Function.comp_apply, powT_tabP hX, invOK_tabP hp, Bool.true_and, List.all_map,
    List.all_eq_true]
  intro t ht
  rw [actOne_tabP hp (ppI t ht)]
  exact List.all_eq_true.1 (List.all_eq_true.1 hk a ha) t ht

open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Quasithin.KGC31.Native
  CFSG.Quasithin.KGC31.M12 in
open Certificates in
theorem cert7198 : ordTest 12 5 x5T = true ∧ ordTest 12 11 x11T = true ∧
    actCheck 12 5 (orderTables m12Certificate 2) (powTabs 12 x5T 5) = true ∧
    actCheck 12 11 (orderTables m12Certificate 2) (powTabs 12 x11T 11) = true := by
  have ho := kOrd
  simp only [Bool.and_eq_true] at ho
  have h5 : x5T = tabP 12 4 X5 := wT w5
  have h11 : x11T = tabP 12 4 X11 := wT w11
  have p5 : PP 12 4 X5 := ppw' w5
  have p11 : PP 12 4 X11 := ppw' w11
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h5, ordTest_tabP p5]
    exact ho.1
  · rw [h11, ordTest_tabP p11]
    exact ho.2
  · rw [h5]
    exact act_eq p5 kAct5
  · rw [h11]
    exact act_eq p11 kAct11

end CertificateChecks.KernelKGC31M12

end
