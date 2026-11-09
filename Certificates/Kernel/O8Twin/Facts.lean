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
import CFSG.Certificates.Kernel.KGC31PPow
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
  rw [dite_eq_left hinv]
  change _ = (genArr j)[x.val]!
  rw [genArr_eq hj, Orb.unpack_get x.isLt]

theorem imgG : ∀ j < (gens1c ()).length,
    imageList ((gens1c ()).getD j 1) = (unpack 120 7 (GPf j)).toList := fun _ hj =>
  CFSG.KC.KGC31P.imageList_of_prep (prep_gen (gens1c_length ▸ hj))

theorem pG : ∀ j < (gens1c ()).length, permOK 120 7 (mask 7) (120 * 7) (GPf j) (GPf j) = true :=
  fun _ hj => pGP (gens1c_length ▸ hj)

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
  ⟨by norm_num, by norm_num, by norm_num, imgS, by decide, ST.head, ST.hl, by norm_num, .inl ST.hs⟩

theorem sylow : o8TwinSylow () = true := by
  obtain ⟨h1, h2⟩ := chainK_check (by decide) (by decide) chainS
  simp only [o8TwinSylow, sylQ_eq, h1, h2, Nat.eq_of_beq_eq_true kN, Bool.true_and,
    beq_self_eq_true]

theorem imgR : ∀ i < fourWords.length,
    imageList ((fourWords.map (evalCodes (sylWords.map (evalCodes (gens1c ()))))).getD i 1) =
      (unpack 120 7 (RS.E (lget RS.OFF i))).toList :=
  words_img (gs := sylWords.map (evalCodes (gens1c ()))) (k := 4) hl4 kSz imgS pS one120 kW

theorem repLK_facts {n w g N j : Nat} {GP GIP CI E P L S SI : Nat → Nat} {CS OFF : List Nat}
    (h : repLK n w GP GIP g CS OFF CI E P L S SI N j = true) :
    CI j < CS.length ∧ lget OFF (CI j) ≤ j ∧ canonK n w (mask w) (n * w) (E j) = true ∧
    (j - lget OFF (CI j) ≠ 0 → P j < j - lget OFF (CI j) ∧ L j < g ∧
      cj n w GP GIP (L j) (E (lget OFF (CI j) + P j)) = E j) ∧
    S j < N ∧ SI j < N ∧ S (SI j) = j ∧ (j + 1 < N → E (S j) < E (S (j + 1))) := by
  unfold repLK at h
  have e1 : ∀ a b : Nat, Nat.add a b = a + b := fun _ _ => rfl
  have e2 : ∀ a b : Nat, Nat.mul a b = a * b := fun _ _ => rfl
  have e3 : ∀ a b : Nat, Nat.sub a b = a - b := fun _ _ => rfl
  simp only [PF.strictB_eqP, bAnd_iff, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq, e1, e2, e3,
    Nat.succ_eq_add_one] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨h1, h2, h3, fun hk => ?_, h5, h6, h7, fun hj => ?_⟩
  · have hk0 : Nat.beq (j - lget OFF (CI j)) 0 = false := by
      cases e : Nat.beq (j - lget OFF (CI j)) 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) hk
    simp only [hk0, bAnd_iff, Nat.blt_eq, Nat.beq_eq] at h4
    exact h4
  · have e' : Nat.blt (j + 1) N = true := Nat.blt_eq.mpr hj
    simp only [e', Nat.blt_eq] at h8
    exact h8

theorem E_injL {n w g N : Nat} {GP GIP CI E P L S SI : Nat → Nat} {CS OFF : List Nat}
    (h : ∀ j < N, repLK n w GP GIP g CS OFF CI E P L S SI N j = true) {a b : Nat}
    (ha : a < N) (hb : b < N) (e : E a = E b) : a = b := by
  have F := fun j (hj : j < N) => repLK_facts (h j hj)
  have mono : ∀ x y, x < y → y < N → E (S x) < E (S y) := by
    intro x y hxy hy
    induction y with
    | zero => omega
    | succ y ih =>
      have := (F y (by omega)).2.2.2.2.2.2.2 hy
      rcases Nat.lt_or_ge x y with h1 | h1
      · exact Nat.lt_trans (ih h1 (by omega)) this
      · have : x = y := by omega
        subst this
        exact this
  have ea := (F a ha).2.2.2.2.2.2.1
  have eb := (F b hb).2.2.2.2.2.2.1
  rcases Nat.lt_trichotomy (SI a) (SI b) with h1 | h1 | h1
  · have := mono _ _ h1 (F b hb).2.2.2.2.2.1
    rw [ea, eb, e] at this
    omega
  · rw [← ea, ← eb, h1]
  · have := mono _ _ h1 (F a ha).2.2.2.2.2.1
    rw [ea, eb, e] at this
    omega

theorem kRL : ∀ j < RS.N, repLK 120 7 ST.S ST.SI 4 RS.CS RS.OFF RS.CI RS.E RS.P RS.L RS.S RS.SI
    RS.N j = true := fun j hj => allN_spec kR j hj

theorem fourWords_len : fourWords.length = RS.CS.length := by decide +kernel

theorem fourReps_eq :
    fourReps () = fourWords.map (evalCodes (sylWords.map (evalCodes (gens1c ())))) := by
  rw [fourReps, sylGens_eq]

theorem sylGen_mem {l : Nat} (hl : l < 4) :
    (sylWords.map (evalCodes (gens1c ()))).getD l 1 ∈ (sylQ ()).originalSubgroup := by
  rw [sylQ_eq, certificate_originalSubgroup]
  apply Subgroup.subset_closure
  rw [List.getD_eq_getElem _ _ (by rw [hl4]; exact hl)]
  exact List.getElem_mem _

theorem sylGens_memQ : ∀ g ∈ sylWords.map (evalCodes (gens1c ())), g ∈ (sylQ ()).originalSubgroup := by
  intro g hg
  obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hg
  have e := sylGen_mem (l := l) (by rw [hl4] at hl; exact hl)
  rwa [List.getD_eq_getElem _ _ hl] at e

theorem rec_conj : ∀ j < RS.N, ∃ x : Equiv.Perm (Fin 120),
    imageList x = (unpack 120 7 (RS.E j)).toList ∧
      ∃ r ∈ fourReps (), ∃ s ∈ (sylQ ()).originalSubgroup, x = s * r * s⁻¹ := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hj
  obtain ⟨hi, ho, -, htree, -⟩ := repLK_facts (kRL j hj)
  by_cases hk : j - lget RS.OFF (RS.CI j) = 0
  · have hi' : RS.CI j < fourWords.length := by rw [fourWords_len]; exact hi
    have e : lget RS.OFF (RS.CI j) = j := by omega
    refine ⟨(fourReps ()).getD (RS.CI j) 1, ?_, (fourReps ()).getD (RS.CI j) 1, ?_, 1,
      Subgroup.one_mem _, by group⟩
    · have h := imgR _ hi'
      rw [e] at h
      rw [fourReps_eq]
      exact h
    · rw [List.getD_eq_getElem _ _ (by rw [fourReps_eq, List.length_map]; exact hi')]
      exact List.getElem_mem _
  · obtain ⟨hP, hL, hc⟩ := htree hk
    obtain ⟨x, hx, r, hr, s, hs, rfl⟩ := ih (lget RS.OFF (RS.CI j) + RS.P j) (by omega) (by omega)
    have hG := imgS (RS.L j) (by rw [hl4]; exact hL)
    have hGi := invK_rep hG (pS _ (by rw [hl4]; exact hL))
    set G := (sylWords.map (evalCodes (gens1c ()))).getD (RS.L j) 1
    refine ⟨G * (s * r * s⁻¹) * G⁻¹, ?_, r, hr, G * s,
      Subgroup.mul_mem _ (sylGen_mem hL) hs, by group⟩
    rw [mulK_rep kSz (mulK_rep kSz hG hx) hGi, ← hc]
    rfl

theorem o8Reps_ord : ∀ r ∈ fourReps (), orderOf r = 4 := by
  have hordT := ord_all kSz (e := 4) (List.length_map _) imgR kO (by norm_num)
  intro r hr
  rw [← fourReps_eq] at hordT
  exact (ordTest_iff perm_faithful (rep_toTable (by norm_num) r) (by norm_num)).1
    (List.all_eq_true.1 hordT _ (List.mem_map_of_mem hr))

theorem o8Reps_mem : ∀ r ∈ fourReps (), r ∈ (sylQ ()).originalSubgroup := by
  intro r hr
  rw [fourReps_eq] at hr
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hr
  exact evalCodes_mem _ sylGens_memQ w

theorem rec_cover : ∀ u ∈ (sylQ ()).originalSubgroup, orderOf u = 4 → ∃ j < RS.N,
    imageList u = (unpack 120 7 (RS.E j)).toList ∧
      ∃ r ∈ fourReps (), ∃ s ∈ (sylQ ()).originalSubgroup, u = s * r * s⁻¹ := by
  have hn : (120 : Nat) < 2 ^ 32 := by norm_num
  set H := (sylQ ()).originalSubgroup
  have hQ : ValidSchreier (sylQ ()) := by
    have h := sylow
    simp only [o8TwinSylow, Bool.and_eq_true] at h
    exact h.1
  have hord := o8Reps_ord
  have hrS := o8Reps_mem
  have hcnt : (cosetOrderTables (sylQ ()) 1 4).length = RS.N := by
    rw [sylQ_eq]
    exact (chainK_cosetCount (by decide) (by decide) chainS one120 kOne (by norm_num)
      (by norm_num) (by decide +kernel) NS.hc).trans (Nat.eq_of_beq_eq_true kT)
  set U := (List.range RS.N).map fun j => tablePerm 120 (tabP 120 7 (RS.E j))
  have hUj : ∀ j < RS.N, imageList (tablePerm 120 (tabP 120 7 (RS.E j))) =
      (unpack 120 7 (RS.E j)).toList ∧ ∃ r ∈ fourReps (), ∃ s ∈ H,
        tablePerm 120 (tabP 120 7 (RS.E j)) = s * r * s⁻¹ := by
    intro j hj
    obtain ⟨x, hx, hc⟩ := rec_conj j hj
    have e : tablePerm 120 (tabP 120 7 (RS.E j)) = x := by
      apply tablePerm_eq
      rw [tabP, ← toTable_eq_arrTable_of_img hx]
      exact rep_toTable hn x
    rw [e]
    exact ⟨hx, hc⟩
  have hnodup : U.Nodup := by
    refine List.Nodup.map_on (fun a ha b hb e => ?_) List.nodup_range
    have ha' := List.mem_range.1 ha
    have hb' := List.mem_range.1 hb
    have hi := (hUj a ha').1
    rw [e, (hUj b hb').1] at hi
    have hu : unpack 120 7 (RS.E b) = unpack 120 7 (RS.E a) := Array.toList_inj.1 hi
    exact E_injL kRL ha' hb' (eq_of_key_tabP (repLK_facts (kRL a ha')).2.2.1
      (repLK_facts (kRL b hb')).2.2.1 (by rw [tabP, tabP, hu]))
  set XG := ((enumeration (sylQ ())).map (1 * ·)).filter fun h => decide (orderOf h = 4)
  have hX := forall₂_cosetOrderTables hn (sylQ ()) 1 (m := 4) (by norm_num)
  have hXG : ∀ u, u ∈ XG ↔ u ∈ H ∧ orderOf u = 4 := by
    intro u
    simp only [XG, List.mem_filter, List.mem_map, mem_enumeration_iff _ hQ, decide_eq_true_eq,
      one_mul, exists_eq_right]
    exact Iff.rfl
  have hsub : U ⊆ XG := by
    intro y hy
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
    obtain ⟨-, r, hr, s, hs, e⟩ := hUj j (List.mem_range.1 hj)
    rw [e, hXG]
    exact ⟨H.mul_mem (H.mul_mem hs (hrS r hr)) (H.inv_mem hs),
      (MulEquiv.orderOf_eq (MulAut.conj s) r).trans (hord r hr)⟩
  have hlen : XG.length ≤ U.length := by
    rw [List.length_map, List.length_range, ← hcnt, hX.length_eq, List.length_reverse]
  have hperm := (hnodup.subperm hsub).perm_of_length_le hlen
  intro u hu ho
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 (hperm.symm.subset ((hXG u).2 ⟨hu, ho⟩))
  exact ⟨j, List.mem_range.1 hj, hUj j (List.mem_range.1 hj)⟩

theorem cover4 : ∀ u ∈ (sylQ ()).originalSubgroup, orderOf u = 4 →
    ∃ r ∈ fourReps (), ∃ s ∈ (sylQ ()).originalSubgroup, u = s * r * s⁻¹ := fun u hu ho =>
  let ⟨_, _, _, h⟩ := rec_cover u hu ho
  h

theorem reps : o8TwinReps () = true := by
  have hordT := ord_all kSz (e := 4) (List.length_map _) imgR kO (by norm_num)
  rw [← fourReps_eq] at hordT
  simp only [o8TwinReps, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨cover4, hordT⟩

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

#kc_forall_chunks recKA (fun k => recK k = true) 64 CertificateChecks.KernelO8Twin.recK 1

theorem inv_of_four {Y : Nat} (hP : PP 120 7 Y) (h4 : sg 120 7 Y ^ 4 = 1) :
    pc 120 7 (pc 120 7 Y Y) Y = pinv 120 7 Y := by
  have hYY := hP.pc hP
  rw [PP_eq_iff (hYY.pc hP) hP.pinv, sg_pc hYY hP, sg_pc hP hP, sg_pinv' hP]
  apply eq_inv_of_mul_eq_one_left
  rw [← h4, pow_succ, pow_succ, pow_succ, pow_one]

theorem sg_of_prep {P : Nat} {g : Equiv.Perm (Fin 120)} (hP : PP 120 7 P)
    (hR : CFSG.KS.Raw.Orb.PRep 120 7 P g) : sg 120 7 P = g := by
  refine Equiv.ext fun x => Fin.ext ?_
  have e := rep_sg hP x
  rw [CFSG.KS.Raw.Orb.unpack_get x.isLt, hR x] at e
  exact e.symm

theorem rec_pairs {j : Nat} (hj : j < RS.N) (hP : PP 120 7 (RS.E j))
    (h4 : sg 120 7 (RS.E j) ^ 4 = 1) : pairsO8C (RS.E j) = true := by
  suffices h : pairsZ (RS.E j) = true from pairsZ_spec h (inv_of_four hP h4)
  have hk : j / 53 < 64 := by
    have := Nat.ble_eq.mp ch517202r
    change RS.N ≤ 64 * 53 at this
    omega
  have h2 := allN_spec (recKA (j / 53) hk) (j % 53) (Nat.mod_lt _ (by norm_num))
  beta_reduce at h2
  have e : Nat.add (Nat.mul (j / 53) 53) (j % 53) = j := by
    change j / 53 * 53 + j % 53 = j
    omega
  rw [e, Nat.blt_eq.mpr hj] at h2
  exact h2

theorem q8_partner {G : Type*} [Group G] {r y : G} (h1 : r * r = y * y) (h2 : r * y = y * r⁻¹)
    (h4 : y ^ 4 = 1) {y' : G} (hy : y' = y⁻¹ ∨ y' = r * y ∨ y' = y * r) :
    r * r = y' * y' ∧ r * y' = y' * r⁻¹ ∧ y' * y' = y * y ∧
      ∀ g, g ∈ [1, r * r, r, r⁻¹, y, y⁻¹, r * y, y * r] ↔
        g ∈ [1, r * r, r, r⁻¹, y', y'⁻¹, r * y', y' * r] := by
  have e4 : y * (y * (y * y)) = 1 := by
    rw [← h4]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have hR4 : ∀ z, r * (r * (r * (r * z))) = z := fun z => by
    have e : r * (r * (r * (r * z))) = (r * r) * (r * r) * z := by group
    rw [e, h1]
    calc y * y * (y * y) * z = y * (y * (y * y)) * z := by group
      _ = z := by rw [e4, one_mul]
  have hr4 : r * (r * (r * r)) = 1 := by simpa using hR4 1
  have hri : r⁻¹ = r * (r * r) := inv_eq_of_mul_eq_one_right hr4
  have hyr : y * r = r * (r * (r * y)) := by
    have hc : y⁻¹ * r * y = r⁻¹ := by
      rw [mul_assoc, h2]
      group
    calc y * r = (y * y) * (y⁻¹ * r * y) * (y * y)⁻¹ * y := by group
      _ = r * (r * (r * y)) := by
        rw [hc, ← h1, hri]
        group
        simp only [zpow_ofNat, pow_three, mul_assoc]
  have hYR : ∀ z, y * (r * z) = r * (r * (r * (y * z))) := fun z => by
    rw [← mul_assoc, hyr]
    group
  have hyy : y * y = r * r := h1.symm
  have hyi : y⁻¹ = r * (r * y) :=
    inv_eq_of_mul_eq_one_right (by simp only [hYR, hyy, hR4, hr4])
  rcases hy with rfl | rfl | rfl <;> refine ⟨?_, ?_, ?_, fun g => ?_⟩ <;>
    simp only [mul_assoc, hri, hyi, mul_inv_rev, hYR, hyr, hyy, hR4, hr4, mul_one,
      List.mem_cons, List.not_mem_nil, or_false] <;>
    tauto

theorem ppairWit_congr (n w : Nat) (sp0 : List Nat) {sp sp' : List Nat} (h : ∀ x, x ∈ sp ↔ x ∈ sp')
    (R C Ci : Nat) : ppairWit n w sp0 sp R C Ci = ppairWit n w sp0 sp' R C Ci := by
  have ha : ∀ f : Nat → Bool, sp.any f = sp'.any f := fun f =>
    Bool.eq_iff_iff.2 (by simp only [List.any_eq_true, h])
  have hl : ∀ f : Nat → Bool, sp.all f = sp'.all f := fun f =>
    Bool.eq_iff_iff.2 (by simp only [List.all_eq_true, h])
  unfold ppairWit pmem
  simp only [List.all_map, List.any_map, ha, hl]

theorem mem_iff_sg {L L' : List Nat} (hL : ∀ a ∈ L, PP 120 7 a) (hL' : ∀ a ∈ L', PP 120 7 a)
    (h : ∀ g, g ∈ L.map (sg 120 7) ↔ g ∈ L'.map (sg 120 7)) : ∀ x, x ∈ L ↔ x ∈ L' := by
  have k : ∀ {A B : List Nat}, (∀ a ∈ A, PP 120 7 a) → (∀ a ∈ B, PP 120 7 a) →
      (∀ g, g ∈ A.map (sg 120 7) → g ∈ B.map (sg 120 7)) → ∀ x ∈ A, x ∈ B := by
    intro A B hA hB hAB x hx
    obtain ⟨b, hb, e⟩ := List.mem_map.1 (hAB _ (List.mem_map_of_mem hx))
    rwa [(PP_eq_iff (hB b hb) (hA x hx)).2 e] at hb
  exact fun x => ⟨k hL hL' (fun g => (h g).1) x, k hL' hL (fun g => (h g).2) x⟩

theorem pspan_PP {R Y : Nat} (hR : PP 120 7 R) (hY : PP 120 7 Y) :
    ∀ a ∈ pspan 120 7 R (pinv 120 7 R) Y (pinv 120 7 Y), PP 120 7 a := by
  intro a ha
  simp only [CFSG.KC.S7TwinK.pspan, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [PP.id kSz, hR.pc hR, hR, hR.pinv, hY, hY.pinv, hR.pc hY, hY.pc hR]

theorem pspan_sg {R Y : Nat} (hR : PP 120 7 R) (hY : PP 120 7 Y) :
    (pspan 120 7 R (pinv 120 7 R) Y (pinv 120 7 Y)).map (sg 120 7) =
      [1, sg 120 7 R * sg 120 7 R, sg 120 7 R, (sg 120 7 R)⁻¹, sg 120 7 Y, (sg 120 7 Y)⁻¹,
        sg 120 7 R * sg 120 7 Y, sg 120 7 Y * sg 120 7 R] := by
  simp only [CFSG.KC.S7TwinK.pspan, List.map_cons, List.map_nil, sg_id kSz, sg_pc hR hR, sg_pc hR hY,
    sg_pc hY hR, sg_pinv' hR, sg_pinv' hY]

theorem o8Rec_facts {j : Nat} (hj : j < RS.N) : PP 120 7 (RS.E j) ∧
    sg 120 7 (RS.E j) ∈ (sylQ ()).originalSubgroup ∧ orderOf (sg 120 7 (RS.E j)) = 4 := by
  obtain ⟨x, hx, r, hr, s, hs, e⟩ := rec_conj j hj
  have hc := (repLK_facts (kRL j hj)).2.2.1
  have hP := prep_of_imageList hx
  have hPP := PP_of_prep hP (PF.canon_facts hc).2.2.1
  rw [sg_of_prep hPP hP, e]
  set H := (sylQ ()).originalSubgroup
  exact ⟨hPP, H.mul_mem (H.mul_mem hs (o8Reps_mem r hr)) (H.inv_mem hs),
    (MulEquiv.orderOf_eq (MulAut.conj s) r).trans (o8Reps_ord r hr)⟩

theorem o8Rep_facts {R : Nat} (hR : R ∈ repsK) : PP 120 7 R ∧
    sg 120 7 R ∈ (sylQ ()).originalSubgroup ∧ orderOf (sg 120 7 R) = 4 := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hR
  have hi' := List.mem_range.1 hi
  have himg := imgR i hi'
  have hPP := (tab_of_img himg (and_of_bAnd (allN_spec kO i hi')).1).1
  have hm : (fourWords.map (evalCodes (sylWords.map (evalCodes (gens1c ()))))).getD i 1 ∈
      fourReps () := by
    rw [fourReps_eq, List.getD_eq_getElem _ _ (by simpa using hi')]
    exact List.getElem_mem _
  rw [sg_of_prep hPP (prep_of_imageList himg)]
  exact ⟨hPP, o8Reps_mem _ hm, o8Reps_ord _ hm⟩

theorem pq8_iff {R Y : Nat} (hR : PP 120 7 R) (hY : PP 120 7 Y) :
    pq8Pair 120 7 R (pinv 120 7 R) Y = true ↔ sg 120 7 R * sg 120 7 R = sg 120 7 Y * sg 120 7 Y ∧
      sg 120 7 R * sg 120 7 Y = sg 120 7 Y * (sg 120 7 R)⁻¹ := by
  simp only [pq8Pair, Bool.and_eq_true, Nat.beq_eq, PP_eq_iff (hR.pc hR) (hY.pc hY),
    PP_eq_iff (hR.pc hY) (hY.pc hR.pinv), sg_pc hR hR, sg_pc hY hY, sg_pc hR hY,
    sg_pc hY hR.pinv, sg_pinv' hR]

theorem o8_order_four {G : Type*} [Group G] {y y' : G} (hy : orderOf y = 4) (e : y' * y' = y * y) :
    orderOf y' = 4 := by
  have h2 : ∀ x : G, x ^ 2 = x * x := fun x => by simp only [pow_succ, pow_zero, one_mul]
  have h4 : ∀ x : G, x ^ 4 = x * x * (x * x) := fun x => by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have e4 : (4 : ℕ) = 2 ^ (1 + 1) := by norm_num
  rw [e4]
  refine orderOf_eq_prime_pow ?_ ?_
  · intro h
    rw [Nat.pow_one, h2, e, ← h2] at h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hy] at this
    omega
  · rw [← e4, h4, e, ← h4, ← hy, pow_orderOf_eq_one]

theorem prep_all : ∀ k j, j < RS.N → pg 7 (mask 7) (RS.E j) 0 = k →
    ∀ p ∈ repsK.zip candsK, prepY 120 7 sp0K p.1 p.2 (RS.E j) = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro j hj hk p hp
  obtain ⟨hYP, hyH, hy4⟩ := o8Rec_facts hj
  obtain ⟨hRP, hrH, -⟩ := o8Rep_facts (List.of_mem_zip hp).1
  have hc := List.all_eq_true.1 (rec_pairs hj hYP (by rw [← hy4]; exact pow_orderOf_eq_one _)) p hp
  cases hcq : canonQ 7 p.1 (RS.E j) (pinv 120 7 (RS.E j))
  case true =>
    rw [hcq, Bool.not_true, Bool.false_or] at hc
    exact hc
  unfold prepY
  cases hq : pq8Pair 120 7 p.1 (pinv 120 7 p.1) (RS.E j)
  case false => rfl
  obtain ⟨h1, h2⟩ := (pq8_iff hRP hYP).1 hq
  have h4 : sg 120 7 (RS.E j) ^ 4 = 1 := by
    rw [← hy4]
    exact pow_orderOf_eq_one _
  have hsp0 : ∀ a ∈ sp0K, PP 120 7 a := by
    have hX := tX0.1
    have hY := tY0.1
    exact pspan_PP hX hY
  have step : ∀ Y', PP 120 7 Y' → (sg 120 7 Y' = (sg 120 7 (RS.E j))⁻¹ ∨
      sg 120 7 Y' = sg 120 7 p.1 * sg 120 7 (RS.E j) ∨
      sg 120 7 Y' = sg 120 7 (RS.E j) * sg 120 7 p.1) → pg 7 (mask 7) Y' 0 < k →
      (p.2.any fun c =>
        ppairWit 120 7 sp0K (pspan 120 7 p.1 (pinv 120 7 p.1) (RS.E j) (pinv 120 7 (RS.E j)))
          p.1 c.1 c.2) = true := by
    intro Y' hP' hy' hlt
    obtain ⟨g1, g2, g3, gm⟩ := q8_partner h1 h2 h4 hy'
    have hH : sg 120 7 Y' ∈ (sylQ ()).originalSubgroup := by
      rcases hy' with e | e | e <;> rw [e]
      exacts [Subgroup.inv_mem _ hyH, Subgroup.mul_mem _ hrH hyH, Subgroup.mul_mem _ hyH hrH]
    obtain ⟨j', hj', himg', -⟩ := rec_cover _ hH (o8_order_four hy4 g3)
    have hPj := (o8Rec_facts hj').1
    have eY : RS.E j' = Y' :=
      (PP_eq_iff hPj hP').2 (sg_of_prep hPj (prep_of_imageList himg'))
    have hI := ih _ (by rw [eY]; exact hlt) j' hj' rfl p hp
    rw [eY] at hI
    unfold prepY at hI
    rw [(pq8_iff hRP hP').2 ⟨g1, g2⟩, Bool.not_true, Bool.false_or] at hI
    have hm := mem_iff_sg (pspan_PP hRP hYP) (pspan_PP hRP hP') (by
      rw [pspan_sg hRP hYP, pspan_sg hRP hP']
      exact gm)
    rw [← hI]
    simp only [ppairWit_congr 120 7 sp0K hm]
  have hne : pg 7 (mask 7) (pinv 120 7 (RS.E j)) 0 < k ∨
      pg 7 (mask 7) (pc 120 7 p.1 (RS.E j)) 0 < k ∨ pg 7 (mask 7) (pc 120 7 (RS.E j) p.1) 0 < k := by
    rw [pg_pc0, pg_pc0, ← hk]
    by_contra hn
    simp only [not_or, Nat.not_lt] at hn
    have hct : canonQ 7 p.1 (RS.E j) (pinv 120 7 (RS.E j)) = true := by
      unfold canonQ
      simp only [bAnd_iff, Nat.ble_eq]
      exact ⟨hn.1, hn.2.1, hn.2.2⟩
    rw [hcq] at hct
    exact Bool.noConfusion hct
  rw [Bool.not_true, Bool.false_or]
  rcases hne with hl | hl | hl
  · exact step _ hYP.pinv (.inl (sg_pinv' hYP)) hl
  · exact step _ (hRP.pc hYP) (.inr (.inl (sg_pc hRP hYP))) hl
  · exact step _ (hYP.pc hRP) (.inr (.inr (sg_pc hYP hRP))) hl

theorem cover : ∀ T ∈ cosetOrderTables (sylQ ()) 1 4,
    ∃ Y, PP 120 7 Y ∧ T = tabP 120 7 Y ∧ pairsY 120 7 sp0K repsK candsK Y = true := by
  intro T hT
  have hQ : ValidSchreier (sylQ ()) := by
    have h := sylow
    simp only [o8TwinSylow, Bool.and_eq_true] at h
    exact h.1
  have hs : T.size = 120 := by
    have hT' := hT
    rw [sylQ_eq] at hT'
    unfold cosetOrderTables at hT'
    exact filterProducts_size _ _ [] (by simp [toTable]) (fun _ h => absurd h List.not_mem_nil) T
      hT'
  obtain ⟨h, hh, hTh⟩ := exists_of_forall₂
    (forall₂_cosetOrderTables (by norm_num : (120 : ℕ) < 2 ^ 32) _ 1 (by norm_num : 0 < 4)) T hT
  rw [List.mem_reverse, List.mem_filter, decide_eq_true_eq] at hh
  obtain ⟨hmem, ho⟩ := hh
  have hH : h ∈ (sylQ ()).originalSubgroup := by
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hmem
    rw [one_mul]
    exact (mem_enumeration_iff _ hQ g).1 hg
  obtain ⟨j, hj, himg, -⟩ := rec_cover h hH ho
  have hc := (repLK_facts (kRL j hj)).2.2.1
  have hP := prep_of_imageList himg
  have hPP := PP_of_prep hP (PF.canon_facts hc).2.2.1
  exact ⟨RS.E j, hPP, eq_tabP_of_rep (by norm_num) hs hTh (CFSG.KC.KGC31P.imageList_of_prep hP),
    List.all_eq_true.2 (prep_all _ j hj rfl)⟩
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
