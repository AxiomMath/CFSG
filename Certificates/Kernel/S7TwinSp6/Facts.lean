module

public import Certificates.Kernel.S7TwinSp6.Checks
public import Certificates.Kernel.LocalComp.Sp6J.Facts
public import CFSG.Certificates.Kernel.S7TwinKSound
public import CFSG.Certificates.Kernel.SporSch.ChainKEnum
public import CFSG.Certificates.Kernel.SporSch.ChainKReps
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.HeModelKSound
public import CFSG.Certificates.Kernel.HexaKSound
public import CFSG.Certificates.Kernel.SporSch.ChainKOdd
public import CFSG.Quasithin.Vol2.KGFactC31CosetCheck

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelS7Sp6

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Schreier.Co3
open CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Mathieu CFSG.ComponentClassification.M12Cover
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch.MOC
open CFSG.KS.SporSch.MBT CFSG.KS.SporSch.CodesImg CFSG.KC.Child3 CFSG.KS.M11 CFSG.EvenSmallLie.Sp6
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.KC.BfsPin CFSG.KC.KGC31P
open CFSG.KC.S7TwinK CFSG.Sporadic.Th.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelLC.ExcGlue CertificateChecks.KernelLC.Sp6J
open Certificates.S7TwinSp6 Certificates.S7Twin

theorem PP_of_prep {P : Nat} {g : Equiv.Perm (Fin 36)} (hP : CFSG.KS.Raw.Orb.PRep 36 6 P g)
    (sP : P >>> (36 * 6) = 0) : PP 36 6 P := by
  have hlt : ∀ i < 36, pg 6 (mask 6) P i < 36 := fun i hi => by
    rw [hP ⟨i, hi⟩]
    exact (g ⟨i, hi⟩).isLt
  refine ⟨?_, hlt, fun a ha b hb e => ?_⟩
  · unfold canonK
    simp only [bAnd_iff]
    exact ⟨kSz, Nat.beq_eq.mpr sP, CFSG.KS.Raw.Orb.allN_iff.2 fun i hi => Nat.blt_eq.mpr (hlt i hi)⟩
  · rw [hP ⟨a, ha⟩, hP ⟨b, hb⟩] at e
    exact congrArg Fin.val (g.injective (Fin.ext e))

theorem tab_of_img {g : Equiv.Perm (Fin 36)} {X : Nat}
    (hg : imageList g = (unpack 36 6 X).toList) (hc : canonK 36 6 (mask 6) (36 * 6) X = true) :
    PP 36 6 X ∧ toTable g = tabP 36 6 X ∧ toTable g⁻¹ = tabP 36 6 (pinv 36 6 X) := by
  have hP : PP 36 6 X := PP_of_prep (prep_of_imageList hg) (PF.canon_facts hc).2.2.1
  have e : toTable g = tabP 36 6 X := toTable_eq_arrTable_of_img hg
  refine ⟨hP, e, ?_⟩
  have hn : (36 : Nat) < 2 ^ 32 := by norm_num
  rw [← invT_tabP hP, ← e]
  exact (CFSG.KS.Tbl.toTable_ext hn (CFSG.KS.Tbl.invT_size _ _)
    (CFSG.KS.Tbl.invT_rep hn (rep_toTable hn g))).symm

theorem sylGens_eq : sylGens () = sylWords.map (evalCodes sp6Gens) := by
  simp only [sylGens, tab_eq]

theorem sylQ_eq : sylQ () = certificate (by decide) (sylWords.map (evalCodes sp6Gens)) sylDerive
    (#v[4, 2, 0, 1] : Vector (Fin 36) 4) (by decide) := by
  unfold sylQ
  rw [sylGens_eq]

theorem imgS : ∀ j < (sylWords.map (evalCodes sp6Gens)).length,
    imageList ((sylWords.map (evalCodes sp6Gens)).getD j 1) = (unpack 36 6 (SQ.S j)).toList :=
  fun j hj => words_img (gs := sp6Gens) rfl kSz imgX pX one36 kG j
    (by rw [List.length_map] at hj; exact hj)

theorem hl4 : (sylWords.map (evalCodes sp6Gens)).length = 4 := rfl

theorem pS : ∀ j < (sylWords.map (evalCodes sp6Gens)).length,
    permOK 36 6 (mask 6) (36 * 6) (SQ.S j) (SQ.SI j) = true :=
  fun j hj => allN_spec kP j (by rw [hl4] at hj; exact hj)

theorem chainS : ChainK 36 6 (sylWords.map (evalCodes sp6Gens)) sylDerive
    (#v[4, 2, 0, 1] : Vector (Fin 36) 4) SQ.S SQ.SI SQ.LR SQ.TR SQ.TRI 7 SQ.BP 1 36 :=
  ⟨by norm_num, by norm_num, by norm_num, imgS, by decide, SQ.head, SQ.hl, by norm_num, SQ.hs⟩

theorem sylow : sp6TwinSylow () = true := by
  obtain ⟨h1, h2⟩ := chainK_check (by decide) (by decide) chainS
  simp only [sp6TwinSylow, sylQ_eq, h1, h2, Nat.eq_of_beq_eq_true kN, Bool.true_and,
    beq_self_eq_true]

theorem imgR : ∀ i < fourWords.length,
    imageList ((fourWords.map (evalCodes (sylWords.map (evalCodes sp6Gens)))).getD i 1) =
      (unpack 36 6 (RS.E (lget RS.OFF i))).toList :=
  words_img (gs := sylWords.map (evalCodes sp6Gens)) (k := 4) hl4 kSz imgS pS
    one36 kW

theorem reps : sp6TwinReps () = true := by
  have hcnt : (cosetOrderTables (certificate (by decide) (sylWords.map (evalCodes sp6Gens))
      sylDerive (#v[4, 2, 0, 1] : Vector (Fin 36) 4) (by decide)) 1 4).length = RS.N :=
    (chainK_cosetCount (by decide) (by decide) chainS one36 kOne (by norm_num) (by norm_num)
      (by decide +kernel) NS.hc).trans (Nat.eq_of_beq_eq_true kT)
  have hlen : fourWords.length = RS.CS.length := by decide +kernel
  obtain ⟨h1, -⟩ := repsOK_of_img (g := 4) hl4 (fun j hj => imgS j (by rw [hl4]; exact hj))
    (fun j hj => pS j (by rw [hl4]; exact hj)) (fun j hj => and_of_bAnd (allN_spec kC j hj))
    (by simpa using hlen) (fun i hi => imgR i (by omega)) kOff kPos hcnt
    (fun j hj => allN_spec kR j hj) (cap := 4000)
    (reps := fourWords.map (evalCodes (sylWords.map (evalCodes sp6Gens))))
  have hordT := ord_all kSz (e := 4) (List.length_map _) imgR kO (by norm_num)
  simp only [sp6TwinReps, fourReps, sylGens_eq, sylQ_eq, Bool.and_eq_true]
  exact ⟨h1, hordT⟩

theorem imgX0 : imageList (x0 ()) = (unpack 36 6 X0).toList := by
  rw [x0, sylGens_eq]
  exact evalCodes_img kSz imgS pS one36 (by rw [hl4]; exact kXL)

theorem imgY0 : imageList (y0 ()) = (unpack 36 6 Y0).toList := by
  rw [y0, sylGens_eq]
  exact evalCodes_img kSz imgS pS one36 (by rw [hl4]; exact kYL)

theorem tX0 : PP 36 6 X0 ∧ toTable (x0 ()) = tabP 36 6 X0 ∧
    toTable (x0 ())⁻¹ = tabP 36 6 (pinv 36 6 X0) :=
  tab_of_img imgX0 kXC

theorem tY0 : PP 36 6 Y0 ∧ toTable (y0 ()) = tabP 36 6 Y0 ∧
    toTable (y0 ())⁻¹ = tabP 36 6 (pinv 36 6 Y0) :=
  tab_of_img imgY0 kYC

theorem k0 : sp6TwinK0 () = true := by
  simp only [sp6TwinK0]
  rw [tX0.2.1, tX0.2.2, tY0.2.1, tY0.2.2,
    q8RelT_tabP tX0.1 tX0.1.pinv tY0.1 tY0.1.pinv]
  exact kK0

@[expose] noncomputable def qY (x : Equiv.Perm (Fin 36)) : Bool :=
  decide (orderOf x = 4) && !pairsY 36 6 sp0K repsK candsK (packL 6 (imageList x))

theorem hpq : ∀ P x, CFSG.KS.Raw.Orb.PRep 36 6 P x → P >>> (36 * 6) = 0 → badY P = qY x := by
  intro P x hP sP
  obtain ⟨hL, sL⟩ := prep_packL (w := 6) (g := x) (by norm_num)
  have e : P = packL 6 (imageList x) :=
    PF.eq_of_fields (by norm_num) sP sL fun i hi => by rw [hP ⟨i, hi⟩, hL ⟨i, hi⟩]
  unfold badY qY
  rw [ordIs_eq kSz hP sP (by norm_num), ← e]
  cases decide (orderOf x = 4) <;> rfl

theorem cover : ∀ T ∈ cosetOrderTables (sylQ ()) 1 4,
    ∃ Y, PP 36 6 Y ∧ T = tabP 36 6 Y ∧ pairsY 36 6 sp0K repsK candsK Y = true := by
  intro T hT
  rw [sylQ_eq] at hT
  have hs : T.size = 36 := by
    unfold cosetOrderTables at hT
    exact filterProducts_size _ _ [] (by simp [toTable]) (fun _ h => absurd h List.not_mem_nil) T hT
  obtain ⟨h, hh, hTh⟩ := exists_of_forall₂
    (forall₂_cosetOrderTables (by norm_num : (36 : ℕ) < 2 ^ 32) _ 1 (by norm_num : 0 < 4)) T hT
  rw [List.mem_reverse, List.mem_filter, decide_eq_true_eq] at hh
  obtain ⟨hmem, ho⟩ := hh
  have hc := enumFrom_spec chainS (q := qY) hpq 4 0 (by norm_num) One36 1 0
    (prep_of_imageList one36) (by unfold One36; exact PF.pidn_shr (by norm_num) (by norm_num))
  rw [Nat.eq_of_beq_eq_true ch517201p, Nat.zero_add] at hc
  rw [enumeration_trL chainS (by decide) (by decide)] at hmem
  simp only [Nat.zero_add] at hc
  have hq := List.countP_eq_zero.1 hc.symm h hmem
  simp only [qY, ho, decide_true, Bool.true_and, Bool.not_eq_true', Bool.not_eq_false'] at hq
  obtain ⟨hP, sP⟩ := prep_packL (w := 6) (g := h) (by norm_num)
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

theorem cand_facts {j : Nat} (hj : j < 4) :
    PP 36 6 (candK j) ∧ toTable ((candPerms ()).getD j 1) = tabP 36 6 (candK j) ∧
      toTable ((candPerms ()).getD j 1)⁻¹ = tabP 36 6 (pinv 36 6 (candK j)) := by
  have h1 := allN_spec kCandL j (by simpa [candWords] using hj)
  have h2 := allN_spec kCandC j (by simpa [candWords] using hj)
  have hj' : j < candWords.length := by simpa [candWords] using hj
  have himg : imageList ((candPerms ()).getD j 1) = (unpack 36 6 (candK j)).toList := by
    rw [candPerms, List.getD_eq_getElem _ _ (by simpa using hj'), List.getElem_map,
      ← List.getD_eq_getElem _ [] hj']
    exact evalCodes_img kSz imgX pX one36 h1
  exact tab_of_img himg h2

theorem repCands_eq :
    repCands () = candsK.map (List.map fun c => (tabP 36 6 c.1, tabP 36 6 c.2)) := by
  have hlt : ∀ l ∈ perRep, ∀ j ∈ l, j < 4 := by decide
  unfold repCands candsK
  rw [List.map_map]
  refine List.map_congr_left fun l hl => ?_
  rw [Function.comp_apply, List.map_map]
  refine List.map_congr_left fun j hj => ?_
  have h4 := hlt l hl j hj
  obtain ⟨-, e1, e2⟩ := cand_facts h4
  have hsz : ((candPerms ()).map fun g => (toTable g, toTable g⁻¹)).toArray.size = 4 := by
    simp [candPerms, candWords]
  have hjl : j < (candPerms ()).length := by simpa [candPerms, candWords] using h4
  simp only [Function.comp_apply, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getElem?_map, List.getElem?_eq_getElem hjl, Option.map_some, Option.getD_some]
  rw [← List.getD_eq_getElem _ 1 hjl, e1, e2]

theorem pairs : sp6TwinPairs () = true := by
  have hR : (fourReps ()).map toTable = repsK.map (tabP 36 6) := by
    apply List.ext_getElem (by simp [fourReps, repsK])
    intro i h1 h2
    have hi : i < fourWords.length := by simpa [fourReps] using h1
    have e := imgR i hi
    rw [List.getD_eq_getElem _ _ (by simpa using hi)] at e
    simp only [List.getElem_map, repsK, List.getElem_range, fourReps, sylGens_eq]
    rw [List.getElem_map] at e
    exact toTable_eq_arrTable_of_img e
  have hreps : ∀ r ∈ repsK, PP 36 6 r := by
    intro r hr
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hr
    have hi' := List.mem_range.1 hi
    exact (tab_of_img (imgR i hi') (and_of_bAnd (allN_spec kO i hi')).1).1
  have hsp0 : ∀ a ∈ sp0K, PP 36 6 a := by
    intro a ha
    simp only [sp0K, CFSG.KC.S7TwinK.pspan, List.mem_cons, List.not_mem_nil, or_false] at ha
    have hX := tX0.1
    have hY := tY0.1
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [PP.id kSz, hX.pc hX, hX, hX.pinv, hY, hY.pinv, hX.pc hY, hY.pc hX]
  have hc : ∀ l ∈ candsK, ∀ c ∈ l, PP 36 6 c.1 ∧ PP 36 6 c.2 := by
    have hlt : ∀ l ∈ perRep, ∀ j ∈ l, j < 4 := by decide
    intro l hl c hc
    obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hc
    have h := (cand_facts (hlt l' hl' j hj)).1
    exact ⟨h, h.pinv⟩
  have hlen : repsK.length = candsK.length := by
    simp only [repsK, candsK, List.length_map, List.length_range]
    rfl
  have hspan : spanT 36 (toTable (x0 ())) (toTable (x0 ())⁻¹) (toTable (y0 ())) (toTable (y0 ())⁻¹)
      = sp0K.map (tabP 36 6) := by
    rw [tX0.2.1, tX0.2.2, tY0.2.1, tY0.2.2, spanT_tabP tX0.1 tY0.1]
    rfl
  simp only [sp6TwinPairs]
  rw [hspan, hR, repCands_eq]
  exact pairsOK_of hlen hsp0 hreps hc cover

theorem facts517201 : sp6TwinSylow () = true ∧ sp6TwinReps () = true ∧ sp6TwinK0 () = true ∧
    sp6TwinPairs () = true :=
  ⟨sylow, reps, k0, pairs⟩

end CertificateChecks.KernelS7Sp6

end
