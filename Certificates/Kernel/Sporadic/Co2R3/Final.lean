
module

public import Certificates.Kernel.Sporadic.Co2R3.Rows
public import Certificates.Kernel.Sporadic.Co2R3.Cells
public import Certificates.Kernel.Sporadic.Co2R3.Orbs
public import Certificates.Kernel.Sporadic.Co2.Order
public import CFSG.Certificates.Kernel.Co2R3KSound
public import CFSG.Certificates.Kernel.Fi22Nbr3153Sound
public import CFSG.Certificates.Kernel.Misc.ArrEnumOps
public import CFSG.Certificates.Kernel.Fi22Snd.Rows
public import CFSG.Monster.B.Mathieu.SylowSound
public import CFSG.Sporadic.Co2Rank3.CheckInputsT
public import CFSG.Sporadic.Co2Rank3.GraphBase
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.NativeRefine
public import CFSG.Sporadic.Co2Rank3.Wales

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Co2R3

open CFSG.KC.Enum CFSG.KC.N3153 CFSG.KC.Co2R3 CFSG.KD.Co2R3 CFSG.KS.Raw CFSG.KC.BfsPin
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Co2Cert CFSG.Sporadic.Co2Rank3 CFSG.Sporadic.Co2Rank3.Native
open CFSG.Sporadic.FischerOddCore.Native CertificateChecks.KernelSpor

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem of_blocks {f : Nat → Bool}
    (h : ∀ s < 36, allBlk (Nat.mul 64 s) (fun x => bIf(Nat.blt x 2300, f x, true)) 64 = true) :
    ∀ x < 2300, f x = true := by
  intro x hx
  have h2 := CFSG.KC.Pack.allBlk_spec (h (x / 64) (by omega)) (x % 64) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul 64 (x / 64)) (x % 64) = x := by
    change 64 * (x / 64) + x % 64 = x
    omega
  have hb : Nat.blt x 2300 = true := Eq.mpr Nat.blt_eq hx
  rw [e, hb] at h2
  exact h2

theorem rows : ∀ x < 2300, rowOK 2300 891 R M S x = true := of_blocks Row.all

theorem imgs : ∀ k < 2, ∀ x < 2300, imgOK 2300 891 (PK k) R M x = true := by
  intro k hk
  interval_cases k
  · exact of_blocks Img0.all
  · exact of_blocks Img1.all

theorem pk_strong : ∀ j < 11, PK j = Co2A.S j := by
  intro j hj
  interval_cases j <;> exact Nat.eq_of_beq_eq_true (by quickRfl)

theorem strong_eq {j : Nat} (hj : j < 11) : co2StrongArrs[j]! = unpack 2300 12 (PK j) := by
  rw [pk_strong j hj]
  exact Co2A.binds.2.2.2.2.1 j hj

theorem strong_size : co2StrongArrs.size = 11 := Co2A.binds.2.2.2.1

theorem orig_get {k : Nat} (hk : k < 2) : co2OrigArrs[k]! = unpack 2300 12 (PK k) := by
  rw [pk_strong k (by omega)]
  exact Co2Order.a_eq k hk

theorem orig_size : co2OrigArrs.size = 2 := by
  rw [Co2Order.orig_eq, Array.size_extract, strong_size]
  rfl

theorem hw : szOK 2300 12 = true := by decide +kernel

theorem permS : ∀ h < 11, CFSG.KC.Misc.ArrEnum.permB 2300 12 (PK h) = true :=
  fun h hh => CFSG.KC.Pack.allN_spec perms h hh

theorem inv_eq {h : Nat} (hh : h < 11) :
    (rawInvs 2300 co2StrongArrs)[h]! = unpack 2300 12 (CFSG.KS.pinvS 2300 12 (CFSG.KS.mask 12) (PK h)) := by
  rw [CFSG.Monster.B.Mathieu.rawInvs_get _ (by rw [strong_size]; exact hh), strong_eq hh]
  exact invCand_PP (CFSG.KC.Misc.ArrEnum.pp_of_permB hw (permS h hh))

theorem stabGens_get {k : Nat} (hk : k < 3) :
    CFSG.Sporadic.Co2Rank3.stabGens[k]! = unpack 2300 12 (PK (11 + k)) := by
  have hk' : k < (stabWords ()).length := by simpa [stabWords] using hk
  rw [CFSG.Sporadic.Co2Rank3.stabGens, getElem!_toArray_map (d := []) hk']
  have hl : lettersOK 11 ((stabWords ()).getD k []) = true := by
    interval_cases k <;> decide
  rw [CFSG.KC.Misc.ArrEnum.wordA_eq hw (fun h hh => strong_eq hh) (fun h hh => inv_eq hh) permS
    (fun h hh => CFSG.KC.Misc.ArrEnum.permB_pinvS hw (permS h hh)) _ hl]
  congr 1
  exact Nat.eq_of_beq_eq_true (CFSG.KC.Pack.allN_spec words k hk)

theorem stabGens_size : CFSG.Sporadic.Co2Rank3.stabGens.size = 3 := by simp [CFSG.Sporadic.Co2Rank3.stabGens, stabWords]

theorem lev1_size : lev1Gens.size = 10 := by simp [lev1Gens, level1Idx]

theorem lev2_size : lev2Gens.size = 8 := by simp [lev2Gens, level2Idx]

theorem lev1_get : ∀ k < 10, lev1Gens[k]! = unpack 2300 12 (G0 k) := by
  intro k hk
  have hk' : k < level1Idx.length := by simpa [level1Idx] using hk
  rw [lev1Gens, getElem!_toArray_map (d := 0) hk']
  exact strong_eq (by interval_cases k <;> decide)

theorem lev2_get : ∀ k < 8, lev2Gens[k]! = unpack 2300 12 (G2 k) := by
  intro k hk
  have hk' : k < level2Idx.length := by simpa [level2Idx] using hk
  rw [lev2Gens, getElem!_toArray_map (d := 0) hk']
  exact strong_eq (by interval_cases k <;> decide)

theorem stab_get : ∀ k < 3, CFSG.Sporadic.Co2Rank3.stabGens[k]! = unpack 2300 12 (G1 k) :=
  fun k hk => stabGens_get hk

theorem allLt_eq_all (n : Nat) (p : Nat → Bool) : allLt n p = (List.range n).all p := by
  apply Bool.eq_iff_iff.2
  rw [allLt_iff, List.all_eq_true]
  simp [List.mem_range]

theorem fix_eq {i j : Nat} (hi : i ≤ 6) (hj : j < 11) :
    fixesFirst co2BaseArr co2StrongArrs[j]! i = (List.range i).all (fun k =>
      (if pg 12 (CFSG.KS.mask 12) Co2A.BP k < 2300 then pg 12 (CFSG.KS.mask 12) (PK j) (pg 12 (CFSG.KS.mask 12) Co2A.BP k)
        else 0) == pg 12 (CFSG.KS.mask 12) Co2A.BP k) := by
  unfold fixesFirst
  rw [allLt_eq_all, strong_eq hj]
  apply Bool.eq_iff_iff.2
  simp only [List.all_eq_true, List.mem_range]
  refine forall₂_congr fun k hk => ?_
  rw [Co2A.binds.2.2.2.2.2.2 k (by omega), unpack_getElem!]

theorem lev_eq {i : Nat} (hi : i ≤ 6) : levelIdx co2StrongArrs co2BaseArr i =
    (List.range 11).filter (fun j => (List.range i).all (fun k =>
      (if pg 12 (CFSG.KS.mask 12) Co2A.BP k < 2300 then pg 12 (CFSG.KS.mask 12) (PK j) (pg 12 (CFSG.KS.mask 12) Co2A.BP k)
        else 0) == pg 12 (CFSG.KS.mask 12) Co2A.BP k)) := by
  unfold levelIdx
  rw [strong_size]
  exact List.filter_congr fun j hj => fix_eq hi (List.mem_range.1 hj)

theorem lev1 : (levelIdx co2StrongArrs co2BaseArr 1 == level1Idx) = true := by
  rw [lev_eq (by norm_num)]
  decide +kernel

theorem lev2 : (levelIdx co2StrongArrs co2BaseArr 2 == level2Idx) = true := by
  rw [lev_eq (by norm_num)]
  decide +kernel

theorem id_eq : idA 2300 = unpack 2300 12 (PK 14) := by
  rw [Nat.eq_of_beq_eq_true idp]
  exact idA_eq hw

theorem root_eq : co2DeltaList = decodeRow 891 (R 0) := by decide +kernel

theorem graph : adjSearch 2300 co2OrigArrs co2DeltaList = rowsArr 2300 891 R ∧
    adjOK 2300 co2OrigArrs (rowsArr 2300 891 R) co2DeltaList = true :=
  graph_sound (ng := 2) (G := PK) (T := T) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    orig_size (fun k hk => orig_get hk) rows imgs (CFSG.KC.Pack.allN_spec tree)
    (CFSG.KC.Pack.allN_spec sym0) root_eq

theorem nbr_eq : co2Nbr = rowsArr 2300 891 R := graph.1

theorem adj : adjOK 2300 co2OrigArrs co2Nbr co2DeltaList = true := by
  rw [nbr_eq]
  exact graph.2

theorem delta_eq : co2DeltaList = (rowsArr 2300 891 R)[0]! := by
  rw [CFSG.KC.Fi22Snd.rowsArr_get (by norm_num)]
  exact root_eq

theorem symm :
    ∀ x < 2300, ∀ y ∈ co2Nbr[x]!, x ∈ co2Nbr[y]! := by
  intro x hx y hy
  have hA := adjFacts_of_adjOK adj
  have hy' : y < 2300 := (hA.point ⟨x, hx⟩).lt y hy
  obtain ⟨g, hg, hgx⟩ := co2P_exists_smul ⟨x, hx⟩ 0
  have hinv : NbrInv co2Nbr g :=
    hA.inv_of_mem_closure (fun _ hk => rep_co2Gen (by rwa [co2OrigArrs_size] at hk))
      (co2P_eq_closure_gens ▸ hg)
  have e : g ⟨x, hx⟩ = 0 := hgx
  have h1 := (hinv ⟨x, hx⟩ ⟨y, hy'⟩).1 hy
  rw [e, Fin.val_zero] at h1
  have h2 := hA.root_symm _ h1
  have h3 := (hinv ⟨y, hy'⟩ ⟨x, hx⟩).2
  rw [e, Fin.val_zero] at h3
  exact h3 h2

theorem p0_eq : p0Rec = (unpack 2300 12 (PK 15), unpack 2300 12 (PK 16), unpack 2300 12 (PK 17),
    unpack 2300 12 (PK 18)) :=
  orbReplay_sound (by norm_num) lev1_size lev1_get replay0

theorem stab_eq : stabRec = (unpack 2300 12 (PK 21), unpack 2300 12 (PK 22),
    unpack 2300 12 (PK 23), unpack 2300 12 (PK 24)) :=
  orbReplay_sound (by norm_num) stabGens_size stab_get replay1

theorem p01_eq : p01Rec = (unpack 2300 12 (PK 27), unpack 2300 12 (PK 28),
    unpack 2300 12 (PK 29), unpack 2300 12 (PK 30)) :=
  orbReplay_sound (by norm_num) lev2_size lev2_get replay2

theorem lab_get {L x v : Nat} (hx : x < 2300) (h : Nat.beq (at12 L x) v = true) :
    (unpack 2300 12 L)[x]! = v := by
  rw [unpack_getElem!, if_pos hx]
  exact Nat.eq_of_beq_eq_true h

theorem l0_eq : p0Rec.1 = unpack 2300 12 (PK 15) := by rw [p0_eq]

theorem lb_eq : stabRec.1 = unpack 2300 12 (PK 21) := by rw [stab_eq]

theorem lc_eq : p01Rec.1 = unpack 2300 12 (PK 27) := by rw [p01_eq]

theorem letters : (stabWords ()).all (lettersOK 11) = true := by decide +kernel

theorem stabFix : CFSG.Sporadic.Co2Rank3.stabGens.all (fun g => g[0]! == 0 && g[3]! == 3) = true := by
  rw [Array.all_eq_true]
  intro k hk
  rw [stabGens_size] at hk
  rw [← getElem!_pos CFSG.Sporadic.Co2Rank3.stabGens k (by rw [stabGens_size]; exact hk), stabGens_get hk]
  simp only [Bool.and_eq_true, beq_iff_eq]
  interval_cases k
  · exact ⟨lab_get (by norm_num) (by quickRfl), lab_get (by norm_num) (by quickRfl)⟩
  · exact ⟨lab_get (by norm_num) (by quickRfl), lab_get (by norm_num) (by quickRfl)⟩
  · exact ⟨lab_get (by norm_num) (by quickRfl), lab_get (by norm_num) (by quickRfl)⟩

theorem recP0 : recOK lev1Gens p0Rec p0Roots = true := by
  rw [p0_eq]
  exact rec_sound lev1_size lev1_get rec0

theorem recStab : recOK CFSG.Sporadic.Co2Rank3.stabGens stabRec stabRoots = true := by
  rw [stab_eq]
  exact rec_sound stabGens_size stab_get rec1

theorem recP01 : recOK lev2Gens p01Rec p01Roots = true := by
  rw [p01_eq]
  exact rec_sound lev2_size lev2_get rec2

theorem l0_36 : (p0Rec.1[36]! == 3) = true := by
  rw [l0_eq, lab_get (by norm_num) (by quickRfl : Nat.beq (at12 (PK 15) 36) 3 = true)]
  rfl

theorem l0_4 : (p0Rec.1[4]! == 3) = true := by
  rw [l0_eq, lab_get (by norm_num) (by quickRfl : Nat.beq (at12 (PK 15) 4) 3 = true)]
  rfl

theorem l0_5 : (p0Rec.1[5]! == 3) = true := by
  rw [l0_eq, lab_get (by norm_num) (by quickRfl : Nat.beq (at12 (PK 15) 5) 3 = true)]
  rfl

theorem l0_2 : (p0Rec.1[2]! == 1) = true := by
  rw [l0_eq, lab_get (by norm_num) (by quickRfl : Nat.beq (at12 (PK 15) 2) 1 = true)]
  rfl

theorem l0_8 : (p0Rec.1[8]! == 1) = true := by
  rw [l0_eq, lab_get (by norm_num) (by quickRfl : Nat.beq (at12 (PK 15) 8) 1 = true)]
  rfl

theorem llDelta : listLabelOK 2300 co2DeltaList p0Rec.1 [3] = true := by
  rw [l0_eq, delta_eq]
  exact listLabel_sound (rows 0 (by norm_num)) (by norm_num) ll0

theorem llNbr3 : listLabelOK 2300 co2Nbr[3]! stabRec.1 [0, 36, 4, 2] = true := by
  rw [lb_eq, nbr_eq]
  exact listLabel_sound (rows 3 (by norm_num)) (by norm_num) ll3

theorem llNbr1 : listLabelOK 2300 co2Nbr[1]! p01Rec.1 [4, 2] = true := by
  rw [lc_eq, nbr_eq]
  exact listLabel_sound (rows 1 (by norm_num)) (by norm_num) ll1

theorem colLab :
    colourLabelOK 2300 (colourT 2300 co2Nbr (idA 2300) (refineBase.take 2) 3) stabRec.1
      [0, 1, 2, 3, 4, 5, 36] = true := by
  rw [lb_eq]
  have h := clab
  rw [strictB_eq] at h
  exact colourLabel_sound (d := 891) (R := R) (M := M) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) nbr_eq rows symm id_eq (by decide) h

theorem bounds :
    boundsOK 2300 co2Nbr (idA 2300) refineBase refineBounds 3 = true := by
  refine bounds_sound (d := 891) (T := PK 14) (P := O 0) (R := R) (M := M) (S := S)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) nbr_eq rows symm id_eq (by decide)
    (by decide) (fun s hs => ?_) ?_
  · have h := Cell.all s hs
    rw [cellB, strictB_eq] at h
    exact h
  · have h := inj
    rw [strictB_eq] at h
    exact h

theorem common3 : (commonCount co2Nbr[0]! co2Nbr[3]! == 378) = true := by
  rw [nbr_eq, common_sound (rows 0 (by norm_num)) (rows 3 (by norm_num)) (by norm_num)
    (by norm_num) cc3]
  rfl

theorem common1 : (commonCount co2Nbr[0]! co2Nbr[1]! == 324) = true := by
  rw [nbr_eq, common_sound (rows 0 (by norm_num)) (rows 1 (by norm_num)) (by norm_num)
    (by norm_num) cc1]
  rfl

theorem facts10079 :
    co2Rank3TOK = true := by
  unfold co2Rank3TOK
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨adj, ?_⟩, ?_⟩, letters⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩,
    ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact lev1
  · exact lev2
  · exact stabFix
  · rw [stabGens_size]
    rfl
  · exact recP0
  · exact recStab
  · exact recP01
  · exact l0_36
  · exact l0_4
  · exact l0_5
  · exact l0_2
  · exact l0_8
  · exact llDelta
  · exact llNbr3
  · exact llNbr1
  · exact colLab
  · exact bounds
  · exact common3
  · exact common1

end CertificateChecks.KernelSpor.Co2R3

end
