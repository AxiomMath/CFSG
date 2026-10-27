module

public import Certificates.Kernel.SporSch.Mathieu.M12OddChecks
public import Certificates.Kernel.SporSch.Mathieu.M12OddZ3
public import Certificates.Kernel.SporSch.Mathieu.M12OddZ5
public import Certificates.Kernel.SporSch.Mathieu.M12OddZ11
public import Certificates.Kernel.SporSch.Mathieu.M12Facts
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
public import Certificates.Kernel.Sporadic.OddCore.MulHGlue
public import CFSG.Certificates.Kernel.SporSch.CodesImg
public import Certificates.Data.Kernel.Spor.MulH
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckBase
public import CFSG.Sporadic.SmallOddCore.ClassSimple

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M12Odd

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu
open CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Mathieu CFSG.Sporadic.Th.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.MEnum CFSG.KS.SporSch.MOC
open CFSG.KS.SporSch.CodesImg CFSG.KC.Child3 CFSG.KS.PEnum CFSG.KS.MulH
open CertificateChecks.KernelSporSch.M12OC Certificates.BTFinCk Certificates.BTFinCk.M12

theorem img_wK {wd : List Int} (hw : abOK wd = true) :
    imageList (evalCodes [m12gA, m12gB] wd) = (unpack 12 4 (wK wd)).toList :=
  img_word hw (Nat.beq_refl _)

theorem tab_of_img {g : Equiv.Perm (Fin 12)} {P : Nat}
    (h : imageList g = (unpack 12 4 P).toList) : toTable g = tabT (unpack 12 4 P) := by
  rw [toTable_eq_arrTable_of_img h]
  unfold CFSG.ComponentClassification.J2Cover.arrTable tabT
  apply Array.ext (by simp [unpack])
  intro i h1 h2
  simp only [Array.getElem_ofFn, Array.getElem_map]
  rw [getElem!_pos _ i (by simpa [unpack] using h1)]

theorem fourOK_zero (L : Array Table) (a : Table) : fourOK 12 L a 0 = true := by
  unfold fourOK
  rw [CFSG.Sporadic.Th.allIn_eq_true]
  intro j _ _
  simp

theorem centFour_of {ws : List (List Int)} {cnt ord : Nat}
    {G GI T PL POS SRT SRI HS HSI : Nat → Nat} (a : Table)
    (hr : recK ws G GI = true) (hh : penumHdK (pidn 12 4) cnt 1000 T PL = true)
    (hp : penumSlK 12 4 (mask 4) (12 * 4) true G GI ws.length cnt T PL POS SRT SRI 0 cnt = true)
    (hs : slK cnt (hsortPtK 12 4 (mask 4) cnt T HS HSI) 0 cnt = true) (hc : cnt = ord) :
    centFourOK 12 ((ws.map (evalCodes [m12gA, m12gB])).map toTable) a ord 1000 0 = true := by
  have hj : ∀ j < ws.length, abOK (ws.getD j []) = true ∧ GI j = wK (ws.getD j []) ∧
      G j = pidn 12 4 ∧ canonK 12 4 (mask 4) (12 * 4) (GI j) = true := by
    intro j hjl
    have h := allN_spec hr j hjl
    simp only [Bool.and_eq_true] at h
    exact ⟨h.1.1.1, Nat.eq_of_beq_eq_true h.1.1.2, Nat.eq_of_beq_eq_true h.1.2, h.2⟩
  have tabs : TabsOK 12 4 ws.length GI ((ws.map (evalCodes [m12gA, m12gB])).map toTable).toArray := by
    refine ⟨by simp, fun j hjl => ⟨?_, (hj j hjl).2.2.2⟩⟩
    rw [getElem!_pos _ j (by simpa using hjl)]
    simp only [List.getElem_toArray, List.getElem_map]
    rw [(hj j hjl).2.1]
    have e := img_wK (hj j hjl).1
    rw [← List.getD_eq_getElem ws [] hjl]
    exact tab_of_img e
  obtain ⟨e, ht, hk⟩ := mulH_sound szOK' (fun j hjl => (hj j hjl).2.2.1) tabs hh
    (fun i hi => penumSl_spec hp i (Nat.zero_le _) (by omega) hi)
    (fun i hi => slK_spec hs i (Nat.zero_le _) (by omega) hi)
  unfold centFourOK
  rw [e]
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨⟨ht, hk⟩, by simp [hRec, hc]⟩, fourOK_zero _ _⟩

theorem rowOK_of {p cs ord : Nat} {w : List Int} {ws : List (List Int)}
    (hw : abOK w = true) (hc : canonK 12 4 (mask 4) (12 * 4) (wK w) = true)
    (ho : ordIs 12 4 (mask 4) (pidn 12 4) (wK w) (p - 1) = true) (hp : 0 < p)
    (hcm : allN ws.length (fun j => abOK (ws.getD j []) &&
      commK 12 4 (mask 4) (12 * 4) (wK (ws.getD j [])) (wK w)) = true)
    (hsz : (conjClosure 12 gT gIT (toTable (evalCodes [m12gA, m12gB] w)) 20000).1.size = cs)
    (hm : cs * ord = 95040)
    (hf : centFourOK 12 ((ws.map (evalCodes [m12gA, m12gB])).map toTable)
      (toTable (evalCodes [m12gA, m12gB] w)) ord 1000 0 = true) :
    rowOK (p, w, cs, ord, ws) = true := by
  have hA := img_wK hw
  unfold rowOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨ordTest_of_ordIs szOK' hA hc hp ho, ?_⟩, hsz⟩, hm⟩, by simpa using hf⟩
  rw [List.all_eq_true]
  intro h hh
  obtain ⟨wd, hwd, rfl⟩ := List.mem_map.1 hh
  obtain ⟨j, hjl, rfl⟩ := List.getElem_of_mem hwd
  have h2 := allN_spec hcm j hjl
  simp only [Bool.and_eq_true] at h2
  rw [← List.getD_eq_getElem ws [] hjl]
  exact commT_of_commK (img_wK h2.1) hA h2.2

theorem gens_img {GP : Nat → Nat} (h : allN 2 (fun j => Nat.beq (GP j) (M12Q.S j)) = true) :
    ∀ j < [m12gA, m12gB].length, imageList ([m12gA, m12gB].getD j 1) =
      (unpack 12 4 (GP j)).toList := by
  intro j hj
  have e := Nat.eq_of_beq_eq_true (allN_spec h j hj)
  have hj2 : j < 2 := hj
  interval_cases j
  · rw [e]
    exact imgA
  · rw [e]
    exact imgB

theorem classes_of {p N : Nat} {ws : List (List Int)} {GP GIP CI E P L K S SI : Nat → Nat}
    {CS OFF : List Nat}
    (hreps : repsOf p = ws.map (evalCodes [m12gA, m12gB]))
    (hb : allN 2 (fun j => Nat.beq (GP j) (M12Q.S j)) = true)
    (hpm : allN 2 (fun j => permOK 12 4 (mask 4) (12 * 4) (GP j) (GIP j)) = true)
    (hcn : allN 2 (fun j => canonK 12 4 (mask 4) (12 * 4) (GP j) &&
      canonK 12 4 (mask 4) (12 * 4) (GIP j)) = true)
    (hl : ws.length = CS.length)
    (hw : allN ws.length (fun i => abOK (ws.getD i []) &&
      Nat.beq (wK (ws.getD i [])) (E (lget OFF i))) = true)
    (hoff : offOK CS OFF N = true) (hpos : CFSG.KC.J2Cover.allL (fun c => Nat.blt 0 c) CS = true)
    (hcnt : (cosetOrderTables m12Certificate 1 p).length = N)
    (hk : allN N (repK 12 4 GP GIP 2 CS OFF CI E P L K S SI N 20000) = true) :
    repsOK 12 gT gIT (cosetOrderTables m12Certificate 1 p) ((repsOf p).map toTable) 20000 =
        true ∧
      repSizes 12 gT gIT ((repsOf p).map toTable) 20000 = CS := by
  have hri : ∀ i < CS.length, imageList ((repsOf p).getD i 1) =
      (unpack 12 4 (E (lget OFF i))).toList := by
    intro i hi
    have hi' : i < ws.length := hl ▸ hi
    have h := allN_spec hw i hi'
    simp only [Bool.and_eq_true] at h
    rw [hreps, getD_map_of_lt' hi', img_wK h.1, Nat.eq_of_beq_eq_true h.2]
  exact repsOK_of_img (gs := [m12gA, m12gB]) (cap := 20000) rfl (gens_img hb)
    (fun j hj => allN_spec hpm j hj)
    (fun j hj => by
      have h := allN_spec hcn j hj
      simp only [Bool.and_eq_true] at h
      exact h)
    (by rw [hreps, List.length_map, hl]) hri hoff hpos hcnt (fun j hj => allN_spec hk j hj)
where
  getD_map_of_lt' {ws : List (List Int)} {i : Nat} (hi : i < ws.length) :
      (ws.map (evalCodes [m12gA, m12gB])).getD i 1 = evalCodes [m12gA, m12gB] (ws.getD i []) := by
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi,
      List.getElem_map]

theorem size_of {ws : List (List Int)} {CS : List Nat}
    (h : repSizes 12 gT gIT ((ws.map (evalCodes [m12gA, m12gB])).map toTable) 20000 = CS)
    {i : Nat} (hi : i < ws.length) :
    (conjClosure 12 gT gIT (toTable (evalCodes [m12gA, m12gB] (ws.getD i []))) 20000).1.size =
      CS.getD i 0 := by
  rw [← h]
  unfold repSizes
  simp [List.getD_eq_getElem?_getD, hi]

theorem cnt3 : (cosetOrderTables m12Certificate 1 3).length = K3.N :=
  (chainK_cosetCount (by decide) (by decide) chainQ imgOne cOne (by norm_num) (by norm_num)
    (by decide) Z3.hc).trans (by decide)

theorem cnt5 : (cosetOrderTables m12Certificate 1 5).length = K5.N :=
  (chainK_cosetCount (by decide) (by decide) chainQ imgOne cOne (by norm_num) (by norm_num)
    (by decide) Z5.hc).trans (by decide)

theorem cnt11 : (cosetOrderTables m12Certificate 1 11).length = K11.N :=
  (chainK_cosetCount (by decide) (by decide) chainQ imgOne cOne (by norm_num) (by norm_num)
    (by decide) Z11.hc).trans (by decide)

theorem cls3 :
    repsOK 12 gT gIT (cosetOrderTables m12Certificate 1 3) ((repsOf 3).map toTable) 20000 =
        true ∧ repSizes 12 gT gIT ((repsOf 3).map toTable) 20000 = K3.CS :=
  classes_of (ws := ws3) rfl k3b k3m k3c rfl k3w k3o k3p cnt3 k3r
theorem cls5 :
    repsOK 12 gT gIT (cosetOrderTables m12Certificate 1 5) ((repsOf 5).map toTable) 20000 =
        true ∧ repSizes 12 gT gIT ((repsOf 5).map toTable) 20000 = K5.CS :=
  classes_of (ws := ws5) rfl k5b k5m k5c rfl k5w k5o k5p cnt5 k5r
theorem cls11 :
    repsOK 12 gT gIT (cosetOrderTables m12Certificate 1 11) ((repsOf 11).map toTable) 20000 =
        true ∧ repSizes 12 gT gIT ((repsOf 11).map toTable) 20000 = K11.CS :=
  classes_of (ws := ws11) rfl k11b k11m k11c rfl k11w k11o k11p cnt11 k11r

theorem rowOK_at {k : Nat} {ws : List (List Int)} {i : Nat} {CS : List Nat}
    (hr : repK' k = true) (hm : commRow k = true) (hp : 0 < (rows.getD k default).1)
    (hs : repSizes 12 gT gIT ((ws.map (evalCodes [m12gA, m12gB])).map toTable) 20000 = CS)
    (hi : i < ws.length) (hw : ws.getD i [] = (rows.getD k default).2.1)
    (hcs : CS.getD i 0 = (rows.getD k default).2.2.1)
    (hmul : (rows.getD k default).2.2.1 * (rows.getD k default).2.2.2.1 = 95040)
    (hf : centFourOK 12 (((rows.getD k default).2.2.2.2.map (evalCodes [m12gA, m12gB])).map
      toTable) (toTable (evalCodes [m12gA, m12gB] (rows.getD k default).2.1))
      (rows.getD k default).2.2.2.1 1000 0 = true) :
    rowOK (rows.getD k default) = true := by
  simp only [repK', Bool.and_eq_true] at hr
  have hsz := size_of hs hi
  rw [hw, hcs] at hsz
  exact rowOK_of hr.1.1 hr.1.2 hr.2 hp hm hsz hmul hf

theorem row0 : rowOK (rows.getD 0 default) = true :=
  rowOK_at r0 m0 (by decide) (ws := ws3) cls3.2 (i := 0) (by decide) rfl (by decide) (by decide)
    (centFour_of _ f0r f0h f0p f0s (Nat.eq_of_beq_eq_true f0c))
theorem row1 : rowOK (rows.getD 1 default) = true :=
  rowOK_at r1 m1 (by decide) (ws := ws3) cls3.2 (i := 1) (by decide) rfl (by decide) (by decide)
    (centFour_of _ f1r f1h f1p f1s (Nat.eq_of_beq_eq_true f1c))
theorem row2 : rowOK (rows.getD 2 default) = true :=
  rowOK_at r2 m2 (by decide) (ws := ws5) cls5.2 (i := 0) (by decide) rfl (by decide) (by decide)
    (centFour_of _ f2r f2h f2p f2s (Nat.eq_of_beq_eq_true f2c))
theorem row3 : rowOK (rows.getD 3 default) = true :=
  rowOK_at r3 m3 (by decide) (ws := ws11) cls11.2 (i := 0) (by decide) rfl (by decide) (by decide)
    (centFour_of _ f3r f3h f3p f3s (Nat.eq_of_beq_eq_true f3c))
theorem row4 : rowOK (rows.getD 4 default) = true :=
  rowOK_at r4 m4 (by decide) (ws := ws11) cls11.2 (i := 1) (by decide) rfl (by decide) (by decide)
    (centFour_of _ f4r f4h f4p f4s (Nat.eq_of_beq_eq_true f4c))

theorem m12OddCk_eq : m12OddCk = true := by
  have e : rows = [rows.getD 0 default, rows.getD 1 default, rows.getD 2 default,
      rows.getD 3 default, rows.getD 4 default] := rfl
  unfold m12OddCk
  rw [e]
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  exact ⟨⟨row0, row1, row2, row3, row4⟩, cls3.1, cls5.1, cls11.1⟩

end CertificateChecks.KernelSporSch.M12Odd

end
