module

public import Certificates.Kernel.KGC31M24.Defs
public import Certificates.Kernel.SporSch.Mathieu.M24Facts
public import CFSG.Certificates.Kernel.KGC31PSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelKGC31M24

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.KGC31P CFSG.KC.Child3 CFSG.KC.BfsPin
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Quasithin.KGC31.Native CFSG.Quasithin.KGC31.M24 CFSG.Sporadic.Mathieu
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.M24OC
open CFSG.KS.SporSch.MOC CFSG.Monster.B.Mathieu

theorem hsz : szOK 24 5 = true := szOK'

theorem ppA : PP 24 5 (M24Q.S 0) := CFSG.KC.HeGlueK.PP_of_permOK2 hsz pA

theorem ppB : PP 24 5 (M24Q.S 1) := CFSG.KC.HeGlueK.PP_of_permOK2 hsz pB

theorem ppG (l : Int) : PP 24 5 (G l) := by
  unfold G
  split
  · exact ppA
  · exact ppB

theorem gensT_eq (l : Int) : gensT l = tabP 24 5 (G l) := by
  unfold gensT G
  split
  · exact CFSG.KS.SporSch.CodesImg.toTable_eq_arrTable_of_img imgA
  · exact CFSG.KS.SporSch.CodesImg.toTable_eq_arrTable_of_img imgB

theorem wT (wd : List Int) : wordT 24 gensT wd = tabP 24 5 (pw wd) :=
  wordT_tabP hsz gensT_eq ppG wd

theorem ppw' (wd : List Int) : PP 24 5 (pw wd) := PP_pword hsz ppG wd

theorem ppX5 : PP 24 5 X5 := ppw' w5
theorem ppX7 : PP 24 5 X7 := ppw' w7
theorem ppX11 : PP 24 5 X11 := ppw' w11
theorem ppX23 : PP 24 5 X23 := ppw' w23

theorem ppL (ws : List (List Int)) : ∀ b ∈ ws.map pw, PP 24 5 b := by
  intro b hb
  obtain ⟨wd, -, rfl⟩ := List.mem_map.1 hb
  exact ppw' wd

theorem mapW (ws : List (List Int)) : ws.map (wordT 24 gensT) = (ws.map pw).map (tabP 24 5) := by
  rw [List.map_map]
  exact List.map_congr_left fun wd _ => wT wd

theorem ppcAll {c : Nat} {bs : List Nat} (hc : PP 24 5 c) (hb : ∀ b ∈ bs, PP 24 5 b) :
    ∀ b ∈ cAll c bs, PP 24 5 b := by
  intro b hbb
  obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hbb
  exact PP_pcj hc hc.pinv (hb b' hb')

theorem conjAll_eq {c : Nat} {bs : List Nat} (hc : PP 24 5 c) (hb : ∀ b ∈ bs, PP 24 5 b) :
    conjAll (tabP 24 5 c) (bs.map (tabP 24 5)) = (cAll c bs).map (tabP 24 5) := by
  rw [conjAll, cAll, invT_tabP hc, List.map_map, List.map_map]
  exact List.map_congr_left fun b hbb => conjTab_tabP hc hc.pinv (hb b hbb)

theorem cA (wd : List Int) (ws : List (List Int)) :
    conjAll (wordT 24 gensT wd) (ws.map (wordT 24 gensT)) =
      (cAll (pw wd) (ws.map pw)).map (tabP 24 5) := by
  rw [wT, mapW]
  exact conjAll_eq (ppw' wd) (ppL ws)

theorem cands5_eq : cands5 = C5.map (List.map (tabP 24 5)) := by
  simp only [cands5, C5, candT, cnd, s32T, s32P, s16T, s16P, oT, oP, cA, List.map_cons,
    List.map_nil]

theorem cands7_eq : cands7 = C7.map (List.map (tabP 24 5)) := by
  simp only [cands7, C7, candT, cnd, u4T, u4P, r2T, r2P, u5T, u5P, oT, oP, u6T, u6P, cA,
    List.map_cons, List.map_nil]

theorem ppC5 : ∀ c ∈ C5, ∀ b ∈ c, PP 24 5 b := by
  simp only [C5, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, forall_const,
    and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact ppcAll (ppw' _) (ppL _)

theorem ppC7 : ∀ c ∈ C7, ∀ b ∈ c, PP 24 5 b := by
  simp only [C7, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, forall_const,
    and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact ppcAll (ppw' _) (ppL _)

theorem frameCands_eq (fr : List (ℕ × List ℤ)) :
    frameCands fr = (fC fr).map (List.map (tabP 24 5)) := by
  rw [frameCands, fC, List.map_map]
  refine List.map_congr_left fun p _ => ?_
  simp only [Function.comp]
  have e : (if p.1 = 1 then oT else tT) = (if p.1 = 1 then oW else tW).map (wordT 24 gensT) := by
    split <;> rfl
  rw [e, cA]
  congr 2
  split <;> rfl

theorem ppfC (fr : List (ℕ × List ℤ)) : ∀ c ∈ fC fr, ∀ b ∈ c, PP 24 5 b := by
  intro c hc
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 hc
  refine ppcAll (ppw' _) ?_
  split
  · exact ppL oW
  · exact ppL tW

end CertificateChecks.KernelKGC31M24

end
