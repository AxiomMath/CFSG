module

public import Certificates.Kernel.O8Twin.PNeg
public import Certificates.Kernel.OmegaEight.Aut
public import Certificates.Kernel.LocalComp.ExcGlue
public import CFSG.Certificates.Kernel.S7TwinKSound
public import CFSG.Certificates.Kernel.SporSch.ChainKEnum
public import CFSG.Certificates.Kernel.SporSch.ChainKReps
public import CFSG.Certificates.Kernel.SporSch.MathieuOCSound
public import CFSG.Certificates.Kernel.SporSch.CodesImg
public import CFSG.Certificates.Kernel.AE6CoreParse
public import CFSG.Certificates.Kernel.HeGlueKGlue
public import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.HeModelKSound
public import CFSG.Certificates.Kernel.HexaKSound
public import CFSG.Certificates.Kernel.SporSch.ChainKOdd
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckBase
public import CFSG.Quasithin.Vol2.KGFactC31CosetCheck

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8Twin

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Schreier.Co3
open CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Mathieu CFSG.ComponentClassification.M12Cover
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch.MOC
open CFSG.KS.SporSch.MBT CFSG.KS.SporSch.CodesImg CFSG.KC.Child3 CFSG.KS.M11
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.KC.BfsPin CFSG.KC.KGC31P
open CFSG.KC.S7TwinK CFSG.Sporadic.Th.Native CFSG.KC.HeGlueK
open CertificateChecks.KernelLC.ExcGlue
open Certificates.S7TwinO8 Certificates.S7Twin

theorem kSz : szOK 120 7 = true := by decide

theorem kId : idK 120 7 (mask 7) = true := by decide +kernel

theorem kOne : canonK 120 7 (mask 7) (120 * 7) One120 = true := by decide +kernel

theorem kGA : allN 8 (fun j => allN 120 (fun i =>
    Nat.beq (pg 7 (mask 7) (GPf j) i) (pg 9 (mask 9) (CertificateChecks.KernelO8.AP.S j) i))) =
    true := by
  decide +kernel

theorem kGW : allN sylWords.length (fun j => bAnd(lettersK 8 (sylWords.getD j []),
    Nat.beq (wordK 120 7 (mask 7) (pidn 120 7) GPf GPf (sylWords.getD j [])) (ST.S j))) =
    true := by
  decide +kernel

theorem one120 : imageList (1 : Equiv.Perm (Fin 120)) = (unpack 120 7 (pidn 120 7)).toList :=
  one_img kId

theorem PP_of_prep {P : Nat} {g : Equiv.Perm (Fin 120)} (hP : CFSG.KS.Raw.Orb.PRep 120 7 P g)
    (sP : P >>> (120 * 7) = 0) : PP 120 7 P := by
  have hlt : ∀ i < 120, pg 7 (mask 7) P i < 120 := fun i hi => by
    rw [hP ⟨i, hi⟩]
    exact (g ⟨i, hi⟩).isLt
  refine ⟨?_, hlt, fun a ha b hb e => ?_⟩
  · unfold canonK
    simp only [bAnd_iff]
    exact ⟨kSz, Nat.beq_eq.mpr sP, CFSG.KS.Raw.Orb.allN_iff.2 fun i hi => Nat.blt_eq.mpr (hlt i hi)⟩
  · rw [hP ⟨a, ha⟩, hP ⟨b, hb⟩] at e
    exact congrArg Fin.val (g.injective (Fin.ext e))

theorem tab_of_img {g : Equiv.Perm (Fin 120)} {X : Nat}
    (hg : imageList g = (unpack 120 7 X).toList) (hc : canonK 120 7 (mask 7) (120 * 7) X = true) :
    PP 120 7 X ∧ toTable g = tabP 120 7 X ∧ toTable g⁻¹ = tabP 120 7 (pinv 120 7 X) := by
  have hP : PP 120 7 X := PP_of_prep (prep_of_imageList hg) (PF.canon_facts hc).2.2.1
  have e : toTable g = tabP 120 7 X := toTable_eq_arrTable_of_img hg
  refine ⟨hP, e, ?_⟩
  have hn : (120 : Nat) < 2 ^ 32 := by norm_num
  rw [← invT_tabP hP, ← e]
  exact (CFSG.KS.Tbl.toTable_ext hn (CFSG.KS.Tbl.invT_size _ _)
    (CFSG.KS.Tbl.invT_rep hn (rep_toTable hn g))).symm

theorem pGP {j : Nat} (hj : j < 8) : permOK 120 7 (mask 7) (120 * 7) (GPf j) (GPf j) = true :=
  (and_of_bAnd (allN_spec kGPp j hj)).1

theorem cGP {j : Nat} (hj : j < 8) : canonK 120 7 (mask 7) (120 * 7) (GPf j) = true :=
  (and_of_bAnd (allN_spec kGPp j hj)).2

theorem genArr_eq {j : Nat} (hj : j < 8) : genArr j = unpack 120 7 (GPf j) := by
  have e := CertificateChecks.KernelO8.genAP.2 j (by omega)
  have hk := allN_spec kGA j hj
  unfold genArr
  rw [e]
  apply Array.ext (by simp [CFSG.EvenSmallLie.OmegaEight.copy0Arr, unpack])
  intro i h1 _
  have hi : i < 120 := by simpa [CFSG.EvenSmallLie.OmegaEight.copy0Arr] using h1
  simp only [CFSG.EvenSmallLie.OmegaEight.copy0Arr, unpack, Array.getElem_ofFn]
  rw [getElem!_pos _ i (by simp; omega), Array.getElem_ofFn]
  exact (Nat.eq_of_beq_eq_true (allN_spec hk i hi)).symm

theorem invPairB_of {t r : Array Nat} {g : Equiv.Perm (Fin 120)}
    (ht : CFSG.Monster.B.Co2.Rep 120 t g) (hr : CFSG.Monster.B.Co2.Rep 120 r g⁻¹) :
    invPairB 120 t r = true := by
  simp only [invPairB, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    beq_iff_eq]
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have e : t[i]! = g ⟨i, hi⟩ := ht ⟨i, hi⟩
    rw [e, hr (g ⟨i, hi⟩)]
    exact ⟨(g _).isLt, by simp⟩
  · have e : r[i]! = g⁻¹ ⟨i, hi⟩ := hr ⟨i, hi⟩
    rw [e, ht (g⁻¹ ⟨i, hi⟩)]
    exact ⟨(g⁻¹ _).isLt, by simp⟩

theorem invPair_gen {j : Nat} (hj : j < 8) :
    invPairB 120 (genArr j) (invCand 120 (genArr j)) = true := by
  have hp : PP 120 7 (GPf j) := PP_of_permOK2 kSz (pGP hj)
  rw [genArr_eq hj, invCand_PP hp]
  exact invPairB_of (rep_sg hp) (rep_sg_inv hp)

theorem gens : o8TwinGens () = true := by
  unfold o8TwinGens
  rw [List.all_eq_true]
  intro i hi
  exact invPair_gen (List.mem_range.1 hi)

theorem gens1c_length : (gens1c ()).length = 8 := by simp [gens1c]

theorem prep_gen {j : Nat} (hj : j < 8) :
    CFSG.KS.Raw.Orb.PRep 120 7 (GPf j) ((gens1c ()).getD j 1) := by
  have hinv := invPair_gen hj
  have e : (gens1c ()).getD j 1 = permOfInv 120 (genArr j) (invCand 120 (genArr j)) := by
    rw [gens1c, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
      Option.map_some, Option.getD_some]
  rw [e]
  intro x
  unfold permOfInv
  rw [dif_pos hinv]
  change _ = (genArr j)[x.val]!
  rw [genArr_eq hj, Orb.unpack_get x.isLt]

theorem imgG : ∀ j < (gens1c ()).length,
    imageList ((gens1c ()).getD j 1) = (unpack 120 7 (GPf j)).toList := fun j hj =>
  CFSG.KC.KGC31P.imageList_of_prep (prep_gen (gens1c_length ▸ hj))

theorem pG : ∀ j < (gens1c ()).length, permOK 120 7 (mask 7) (120 * 7) (GPf j) (GPf j) = true :=
  fun j hj => pGP (gens1c_length ▸ hj)

theorem perm_head {n w kS kO nb BP : Nat} {PS PSI : Nat → Nat} {D : List (List Int)}
    (h : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true) :
    allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true := by
  unfold headK at h
  simp only [bAnd_iff] at h
  exact h.2.2.2.2.1

theorem sylGens_eq : sylGens () = sylWords.map (evalCodes (gens1c ())) := by
  simp only [sylGens, tab_eq]

theorem sylQ_eq : sylQ () = certificate (by decide) (sylWords.map (evalCodes (gens1c ())))
    sylDerive (#v[0, 2, 4, 24, 8] : Vector (Fin 120) 5) (by decide) := by
  unfold sylQ
  rw [sylGens_eq]

theorem imgS : ∀ j < (sylWords.map (evalCodes (gens1c ()))).length,
    imageList ((sylWords.map (evalCodes (gens1c ()))).getD j 1) =
      (unpack 120 7 (ST.S j)).toList :=
  fun j hj => words_img (gs := gens1c ()) gens1c_length kSz imgG pG one120 kGW j
    (by rw [List.length_map] at hj; exact hj)

theorem hl4 : (sylWords.map (evalCodes (gens1c ()))).length = 4 := rfl

theorem pS : ∀ j < (sylWords.map (evalCodes (gens1c ()))).length,
    permOK 120 7 (mask 7) (120 * 7) (ST.S j) (ST.SI j) = true :=
  fun j hj => allN_spec (perm_head ST.head) j (Nat.lt_of_lt_of_le (hl4 ▸ hj) (by decide))

theorem cS {j : Nat} (hj : j < 4) : canonK 120 7 (mask 7) (120 * 7) (ST.S j) = true ∧
    canonK 120 7 (mask 7) (120 * 7) (ST.SI j) = true := by
  rw [Nat.eq_of_beq_eq_true (allN_spec kSI j hj), ← Nat.eq_of_beq_eq_true (allN_spec kG j hj)]
  exact ⟨cGP (by omega), cGP (by omega)⟩

theorem chainS : ChainK 120 7 (sylWords.map (evalCodes (gens1c ()))) sylDerive
    (#v[0, 2, 4, 24, 8] : Vector (Fin 120) 5) ST.S ST.SI ST.LR ST.TR ST.TRI 7 ST.BP 5 24 :=
  ⟨by norm_num, by norm_num, by norm_num, imgS, by decide, ST.head, ST.hl, by norm_num, ST.hs⟩

theorem sylow : o8TwinSylow () = true := by
  obtain ⟨h1, h2⟩ := chainK_check (by decide) (by decide) chainS
  simp only [o8TwinSylow, sylQ_eq, h1, h2, Nat.eq_of_beq_eq_true kN, Bool.true_and,
    beq_self_eq_true]

theorem imgR : ∀ i < fourWords.length,
    imageList ((fourWords.map (evalCodes (sylWords.map (evalCodes (gens1c ()))))).getD i 1) =
      (unpack 120 7 (RS.E (lget RS.OFF i))).toList :=
  words_img (gs := sylWords.map (evalCodes (gens1c ()))) (k := 4) hl4 kSz imgS pS one120 kW

theorem reps : o8TwinReps () = true := by
  have hcnt : (cosetOrderTables (certificate (by decide) (sylWords.map (evalCodes (gens1c ())))
      sylDerive (#v[0, 2, 4, 24, 8] : Vector (Fin 120) 5) (by decide)) 1 4).length = RS.N :=
    (chainK_cosetCount (by decide) (by decide) chainS one120 kOne (by norm_num) (by norm_num)
      (by decide +kernel) NS.hc).trans (Nat.eq_of_beq_eq_true kT)
  have hlen : fourWords.length = RS.CS.length := by decide +kernel
  obtain ⟨h1, -⟩ := repsOK_of_img (g := 4) hl4 (fun j hj => imgS j (by rw [hl4]; exact hj))
    (fun j hj => pS j (by rw [hl4]; exact hj)) (fun j hj => cS hj)
    (by simpa using hlen) (fun i hi => imgR i (by omega)) kOff kPos hcnt
    (fun j hj => allN_spec kR j hj) (cap := 4000)
    (reps := fourWords.map (evalCodes (sylWords.map (evalCodes (gens1c ())))))
  have hordT := ord_all kSz (e := 4) (List.length_map _) imgR kO (by norm_num)
  simp only [o8TwinReps, fourReps, sylGens_eq, sylQ_eq, Bool.and_eq_true]
  exact ⟨h1, hordT⟩

theorem imgX0 : imageList (x0 ()) = (unpack 120 7 X0).toList := by
  rw [x0, sylGens_eq]
  exact evalCodes_img kSz imgS pS one120 (by rw [hl4]; exact kXL)

theorem imgY0 : imageList (y0 ()) = (unpack 120 7 Y0).toList := by
  rw [y0, sylGens_eq]
  exact evalCodes_img kSz imgS pS one120 (by rw [hl4]; exact kYL)

theorem tX0 : PP 120 7 X0 ∧ toTable (x0 ()) = tabP 120 7 X0 ∧
    toTable (x0 ())⁻¹ = tabP 120 7 (pinv 120 7 X0) :=
  tab_of_img imgX0 kXC

theorem tY0 : PP 120 7 Y0 ∧ toTable (y0 ()) = tabP 120 7 Y0 ∧
    toTable (y0 ())⁻¹ = tabP 120 7 (pinv 120 7 Y0) :=
  tab_of_img imgY0 kYC

theorem k0 : o8TwinK0 () = true := by
  simp only [o8TwinK0]
  rw [tX0.2.1, tX0.2.2, tY0.2.1, tY0.2.2,
    q8RelT_tabP tX0.1 tX0.1.pinv tY0.1 tY0.1.pinv]
  exact kK0

#kc_forall_chunks badKA (fun k => badK k = true) 64 CertificateChecks.KernelO8Twin.badK 1

theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem enumFrom_add {n w m nw : Nat} {LR TR : Nat → Nat} {p : Nat → Bool} :
    ∀ d i G s, enumFrom n w m nw LR TR p d i G s = s + enumFrom n w m nw LR TR p d i G 0
  | 0, i, G, s => by
    rw [enumFrom_zero, enumFrom_zero]
    split <;> omega
  | d + 1, i, G, s => by
    rw [enumFrom_succ, enumFrom_succ,
      foldl_eq_add (X := fun k => enumFrom n w m nw LR TR p d (i + 1)
        (pcomp n w m G (TR (roff n nw (LR i) + k))) 0) _ (fun k _ s => enumFrom_add d _ _ s) s,
      foldl_eq_add (X := fun k => enumFrom n w m nw LR TR p d (i + 1)
        (pcomp n w m G (TR (roff n nw (LR i) + k))) 0) _ (fun k _ s => enumFrom_add d _ _ s) 0,
      Nat.zero_add]

theorem enum_zero :
    enumFrom 120 7 (mask 7) (120 * 7) ST.LR ST.TR badY 5 0 One120 0 = 0 := by
  rw [enumFrom_succ,
    foldl_eq_add (X := fun k => enumFrom 120 7 (mask 7) (120 * 7) ST.LR ST.TR badY 4 (0 + 1)
      (pcomp 120 7 (mask 7) One120 (ST.TR (roff 120 (120 * 7) (ST.LR 0) + k))) 0) _
      (fun k _ s => enumFrom_add 4 _ _ s) 0, Nat.zero_add]
  have hc := Nat.ble_eq.mp ch517202o
  refine List.sum_eq_zero fun x hx => ?_
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
  have hk' := List.mem_range.1 hk
  have h := badKA k (Nat.lt_of_lt_of_le hk' hc)
  rw [badK, strictB_eq', Nat.blt_eq.mpr hk'] at h
  exact Nat.eq_of_beq_eq_true h

@[expose] noncomputable def qY (x : Equiv.Perm (Fin 120)) : Bool :=
  decide (orderOf x = 4) && !pairsY 120 7 sp0K repsK candsK (packL 7 (imageList x))

theorem hpq : ∀ P x, CFSG.KS.Raw.Orb.PRep 120 7 P x → P >>> (120 * 7) = 0 → badY P = qY x := by
  intro P x hP sP
  obtain ⟨hL, sL⟩ := prep_packL (w := 7) (g := x) (by norm_num)
  have e : P = packL 7 (imageList x) :=
    PF.eq_of_fields (by norm_num) sP sL fun i hi => by rw [hP ⟨i, hi⟩, hL ⟨i, hi⟩]
  unfold badY qY
  rw [ordIs_eq kSz hP sP (by norm_num), ← e]
  cases decide (orderOf x = 4) <;> rfl

theorem cover : ∀ T ∈ cosetOrderTables (sylQ ()) 1 4,
    ∃ Y, PP 120 7 Y ∧ T = tabP 120 7 Y ∧ pairsY 120 7 sp0K repsK candsK Y = true := by
  intro T hT
  rw [sylQ_eq] at hT
  have hs : T.size = 120 := by
    unfold cosetOrderTables at hT
    exact filterProducts_size _ _ [] (by simp [toTable]) (fun _ h => absurd h List.not_mem_nil) T hT
  obtain ⟨h, hh, hTh⟩ := exists_of_forall₂
    (forall₂_cosetOrderTables (by norm_num : (120 : ℕ) < 2 ^ 32) _ 1 (by norm_num : 0 < 4)) T hT
  rw [List.mem_reverse, List.mem_filter, decide_eq_true_eq] at hh
  obtain ⟨hmem, ho⟩ := hh
  have hc := enumFrom_spec chainS (q := qY) hpq 5 0 (by norm_num) One120 1 0
    (prep_of_imageList one120) (by unfold One120; exact PF.pidn_shr (by norm_num) (by norm_num))
  rw [enum_zero, Nat.zero_add] at hc
  rw [enumeration_trL chainS (by decide) (by decide)] at hmem
  simp only [Nat.zero_add] at hc
  have hq := List.countP_eq_zero.1 hc.symm h hmem
  simp only [qY, ho, decide_true, Bool.true_and, Bool.not_eq_true', Bool.not_eq_false'] at hq
  obtain ⟨hP, sP⟩ := prep_packL (w := 7) (g := h) (by norm_num)
  exact ⟨_, PP_of_prep hP sP, eq_tabP_of_rep (by norm_num) hs hTh
    (CFSG.KC.KGC31P.imageList_of_prep hP), by simpa using hq⟩
where
  exists_of_forall₂ {α β : Type} {R : α → β → Prop} :
      ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ a ∈ l₁, ∃ b ∈ l₂, R a b
    | _, _, .nil, _, h => absurd h List.not_mem_nil
    | _, _, .cons hr hs, a, h => by
      rcases List.mem_cons.1 h with rfl | h
      · exact ⟨_, List.mem_cons_self, hr⟩
      · obtain ⟨b, hb, hab⟩ := exists_of_forall₂ hs a h
        exact ⟨b, List.mem_cons_of_mem _ hb, hab⟩

theorem candWords_eq : candWords () = candL := by
  rw [CW.eq, CFSG.KC.AE6Core.parseWords_ofList _ kToks]
  rfl

theorem candL_length : candL.length = 12 := Nat.eq_of_beq_eq_true kCandN

theorem candPerms_eq : candPerms () = candL.map (evalCodes (gens1c ())) := by
  unfold candPerms
  rw [candWords_eq]

theorem cand_facts {j : Nat} (hj : j < 12) :
    PP 120 7 (candK j) ∧ toTable ((candPerms ()).getD j 1) = tabP 120 7 (candK j) ∧
      toTable ((candPerms ()).getD j 1)⁻¹ = tabP 120 7 (pinv 120 7 (candK j)) := by
  have hj' : j < candL.length := by rw [candL_length]; exact hj
  have h1 := allN_spec kCandL j hj'
  have h2 := allN_spec kCandC j hj'
  have himg : imageList ((candPerms ()).getD j 1) = (unpack 120 7 (candK j)).toList := by
    rw [candPerms_eq, List.getD_eq_getElem _ _ (by simpa using hj'), List.getElem_map,
      ← List.getD_eq_getElem _ [] hj']
    exact evalCodes_img kSz imgG pG one120 (by rw [gens1c_length]; exact h1)
  exact tab_of_img himg h2

theorem repCands_eq :
    repCands () = candsK.map (List.map fun c => (tabP 120 7 c.1, tabP 120 7 c.2)) := by
  have hlt : ∀ l ∈ perRep, ∀ j ∈ l, j < 12 := by decide
  unfold repCands candsK
  rw [List.map_map]
  refine List.map_congr_left fun l hl => ?_
  rw [Function.comp_apply, List.map_map]
  refine List.map_congr_left fun j hj => ?_
  have h12 := hlt l hl j hj
  obtain ⟨-, e1, e2⟩ := cand_facts h12
  have hjl : j < (candPerms ()).length := by
    rw [candPerms_eq, List.length_map, candL_length]
    exact h12
  simp only [Function.comp_apply, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getElem?_map, List.getElem?_eq_getElem hjl, Option.map_some, Option.getD_some]
  rw [← List.getD_eq_getElem _ 1 hjl, e1, e2]

theorem pairs : o8TwinPairs () = true := by
  have hR : (fourReps ()).map toTable = repsK.map (tabP 120 7) := by
    apply List.ext_getElem (by simp [fourReps, repsK])
    intro i h1 h2
    have hi : i < fourWords.length := by simpa [fourReps] using h1
    have e := imgR i hi
    rw [List.getD_eq_getElem _ _ (by simpa using hi)] at e
    simp only [List.getElem_map, repsK, List.getElem_range, fourReps, sylGens_eq]
    rw [List.getElem_map] at e
    exact toTable_eq_arrTable_of_img e
  have hreps : ∀ r ∈ repsK, PP 120 7 r := by
    intro r hr
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hr
    have hi' := List.mem_range.1 hi
    exact (tab_of_img (imgR i hi') (and_of_bAnd (allN_spec kO i hi')).1).1
  have hsp0 : ∀ a ∈ sp0K, PP 120 7 a := by
    intro a ha
    simp only [sp0K, CFSG.KC.S7TwinK.pspan, List.mem_cons, List.not_mem_nil, or_false] at ha
    have hX := tX0.1
    have hY := tY0.1
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [PP.id kSz, hX.pc hX, hX, hX.pinv, hY, hY.pinv, hX.pc hY, hY.pc hX]
  have hc : ∀ l ∈ candsK, ∀ c ∈ l, PP 120 7 c.1 ∧ PP 120 7 c.2 := by
    have hlt : ∀ l ∈ perRep, ∀ j ∈ l, j < 12 := by decide
    intro l hl c hc
    obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hc
    have h := (cand_facts (hlt l' hl' j hj)).1
    exact ⟨h, h.pinv⟩
  have hlen : repsK.length = candsK.length := by
    simp only [repsK, candsK, List.length_map, List.length_range]
    rfl
  have hspan : spanT 120 (toTable (x0 ())) (toTable (x0 ())⁻¹) (toTable (y0 ()))
      (toTable (y0 ())⁻¹) = sp0K.map (tabP 120 7) := by
    rw [tX0.2.1, tX0.2.2, tY0.2.1, tY0.2.2, spanT_tabP tX0.1 tY0.1]
    rfl
  simp only [o8TwinPairs]
  rw [hspan, hR, repCands_eq]
  exact pairsOK_of hlen hsp0 hreps hc cover

theorem facts517202 : o8TwinGens () = true ∧ o8TwinSylow () = true ∧ o8TwinReps () = true ∧
    o8TwinK0 () = true ∧ o8TwinPairs () = true :=
  ⟨gens, sylow, reps, k0, pairs⟩

end CertificateChecks.KernelO8Twin

end
