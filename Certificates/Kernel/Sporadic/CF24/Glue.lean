module

public import Certificates.Kernel.Sporadic.CF24.Checks
public import Certificates.Kernel.Sporadic.OddCore.Suz23000F
public import Certificates.Kernel.CosetJ.SuzTab
public import CFSG.Certificates.Kernel.Misc.ArrEnumOps
public import CFSG.Certificates.Kernel.Fi22Rk.Side
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Suzuki

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.CF24

open CFSG.KC CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.CF24 CFSG.KC.Misc.ArrEnum CFSG.KC.BfsPin
open CertificateChecks.KernelSpor.Suz23000 CFSG.ComponentClassification.GSThmB.CF24
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Recognition.SuzMultiplier CFSG.Sporadic.SuzOddCore
open CFSG.Sporadic.Schreier.Tits CFSG.LieType.Multipliers.Tits CFSG.LieType.Multipliers
open CFSG.ComponentClassification.CatFactsL4U4.SuzCS CFSG.PSL3Four.Native
open CFSG.Monster.B.Co2 (allLt_iff)
open CFSG.Sporadic.Bridge.SuzGPL.Native CFSG.KS.Prim

local notation "pc" => pcomp 1782 11 (mask 11)
local notation "pv" => pinvS 1782 11 (mask 11)
local notation "wk" => wordK 1782 11 (mask 11) (pidn 1782 11)

theorem sz : szOK 1782 11 = true := by quickRfl

theorem beq_of {a b : Nat} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem zword_one {c : Nat} (hc : c < 14) : zword (suzW [c]) = [zc c] := by
  interval_cases c <;> decide +kernel

theorem zword_codes : ∀ cs : List Nat, (∀ c ∈ cs, c < 14) → zword (suzW cs) = codesZ cs
  | [], _ => rfl
  | c :: cs, h => by
    have e : suzW (c :: cs) = suzW [c] ++ suzW cs := by
      simp [suzW, CFSG.CosetTable.wordOfCodes, List.flatMap_cons]
    rw [e, zword, List.map_append, ← zword, ← zword, zword_one (h c List.mem_cons_self),
      zword_codes cs fun c' hc' => h c' (List.mem_cons_of_mem c hc')]
    rfl

theorem lettersOK_codes : ∀ cs : List Nat, (∀ c ∈ cs, c < 14) → lettersOK 7 (codesZ cs) = true
  | [], _ => rfl
  | c :: cs, h => by
    have hc := h c List.mem_cons_self
    have e : codesZ (c :: cs) = zc c :: codesZ cs := rfl
    rw [e, CFSG.Monster.B.Co2.Native.lettersOK, List.all_cons, Bool.and_eq_true]
    refine ⟨?_, lettersOK_codes cs fun c' hc' => h c' (List.mem_cons_of_mem c hc')⟩
    interval_cases c <;> decide +kernel

theorem xCodes : ∀ c ∈ cf24XCodes, c < 14 := by
  have h : cf24XCodes.all (fun c => Nat.blt c 14) = true := by decide +kernel
  intro c hc
  exact Nat.blt_eq.mp (List.all_eq_true.1 h c hc)

theorem yCodes : ∀ c ∈ cf24YCodes, c < 14 := by
  have h : cf24YCodes.all (fun c => Nat.blt c 14) = true := by decide +kernel
  intro c hc
  exact Nat.blt_eq.mp (List.all_eq_true.1 h c hc)

theorem gcS_eq : gcS = 7 := by decide

theorem lx : lettersOK gcS (zword cf24X) = true := by
  rw [cf24X, zword_codes _ xCodes, gcS_eq]
  exact lettersOK_codes _ xCodes

theorem ly : lettersOK gcS (zword cf24Y) = true := by
  rw [cf24Y, zword_codes _ yCodes, gcS_eq]
  exact lettersOK_codes _ yCodes

theorem nthW_eq : ∀ (L : List (List Int)) (h : Nat), nthW L h = L.getD h []
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: L, h + 1 => nthW_eq L h

theorem ppGH {k : Nat} (hk : k < 7) : PP 1782 11 (GH (k + 1)) :=
  pp_of_permB sz (allN_spec permGH k hk)

theorem genA {k : Nat} (hk : k < 7) : (invInnerGenArrs 0)[k]! = unpack 1782 11 (GH (k + 1)) :=
  gen_get (by omega)

theorem ell_val {j : Nat} (hj : j < 5) : pc (pc (pc (GH 2) (GH (j + 3))) (pv (GH 2)))
    (pv (GH (j + 3))) = LF j :=
  beq_of (allN_spec lK j hj)

theorem ppL {j : Nat} (hj : j < 5) : PP 1782 11 (LF j) := by
  rw [← ell_val hj]
  have h1 := ppGH (k := 1) (by norm_num)
  have h2 := ppGH (k := j + 2) (by omega)
  exact ((h1.mul h2).mul h1.inv).mul h2.inv

theorem ell_eq {j : Nat} (hj : j < 5) : cf24EllArrs[j]! = unpack 1782 11 (LF j) := by
  have h1 := ppGH (k := 1) (by norm_num)
  have h2 := ppGH (k := j + 2) (by omega)
  rw [cf24EllArrs, getElem!_ofFn_of_lt _ hj]
  simp only
  rw [genA (k := 1) (by norm_num), genA (k := j + 2) (by omega), invCand_PP h1, invCand_PP h2,
    compA_PP h1 h2, compA_PP (h1.mul h2) h1.inv, compA_PP ((h1.mul h2).mul h1.inv) h2.inv,
    ← ell_val hj]

theorem ellSize : cf24EllArrs.size = 5 := by
  rw [cf24EllArrs, Array.size_ofFn]

theorem ellInv_eq {j : Nat} (hj : j < 5) : (cf24EllArrs.map (invCand 1782))[j]! =
    unpack 1782 11 (LIF j) := by
  rw [getElem!_map_of_lt (by rw [ellSize]; exact hj), ell_eq hj, invCand_PP (ppL hj),
    beq_of (allN_spec liK j hj)]

theorem ppLI {j : Nat} (hj : j < 5) : PP 1782 11 (LIF j) := by
  rw [← beq_of (allN_spec liK j hj)]
  exact (ppL hj).inv

theorem b0K : B0 = CFSG.KD.CJSuzTab.PB0 := rfl
theorem b1K : B1 = CFSG.KD.CJSuzTab.PB1 := rfl

theorem bParts : permB 1782 11 B0 = true ∧ permB 1782 11 B1 = true ∧ pv B0 = B0I ∧ pv B1 = B1I := by
  have h := permB01
  simp only [bAnd_iff] at h
  exact ⟨h.1, h.2.1, beq_of h.2.2.1, beq_of h.2.2.2⟩

theorem ppB {h : Nat} (hh : h < 2) : PP 1782 11 (BF h) := by
  interval_cases h
  · exact pp_of_permB sz bParts.1
  · exact pp_of_permB sz bParts.2.1

theorem bfi {h : Nat} (hh : h < 2) : BIF h = pv (BF h) := by
  interval_cases h
  · exact bParts.2.2.1.symm
  · exact bParts.2.2.2.symm

theorem bS {h : Nat} (hh : h < 2) : (#[b0Arr, b1Arr] : Array (Array ℕ))[h]! = unpack 1782 11 (BF h) := by
  interval_cases h
  · change b0Arr = _
    rw [KernelCosetJ.SuzTab.b0_eq, ← b0K]
    rfl
  · change b1Arr = _
    rw [KernelCosetJ.SuzTab.b1_eq, ← b1K]
    rfl

theorem bSI {h : Nat} (hh : h < 2) : ((#[b0Arr, b1Arr] : Array (Array ℕ)).map (invCand 1782))[h]! =
    unpack 1782 11 (BIF h) := by
  rw [getElem!_map_of_lt (by simp; omega), bS hh, invCand_PP (ppB hh), bfi hh]

theorem imgW {h : Nat} (hh : h < 7) : imgWords[h]! = nthW IW.W h := by
  have e : IW.W = KernelCosetJ.SuzTabIT.W := rfl
  have hl : KernelCosetJ.SuzTabIT.W.length = 7 := by
    have := KernelCosetJ.SuzTab.himg.1
    rwa [KernelCosetJ.SuzTab.img_eq, List.size_toArray] at this
  rw [nthW_eq, e, KernelCosetJ.SuzTab.img_eq, getElem!_pos _ h (by simp; omega),
    List.getElem_toArray, List.getD_eq_getElem _ _ (by omega)]

theorem imgL {h : Nat} (hh : h < 7) : lettersOK 2 imgWords[h]! = true := by
  have hs := KernelCosetJ.SuzTab.himg.1
  have hil := KernelCosetJ.SuzTab.himg.2.1
  rw [getElem!_pos imgWords h (by omega)]
  exact (Array.all_eq_true.1 hil) h (by omega)

theorem sg_val {h : Nat} (hh : h < 7) : wk BF BIF (nthW IW.W h) = SGF h :=
  beq_of (allN_spec sgK h hh)

theorem genSize : suzGenArrs.size = 7 := by
  rw [suzGenArrs, Array.size_map]
  exact KernelCosetJ.SuzTab.himg.1

theorem sg_eq {h : Nat} (hh : h < 7) : suzGenArrs[h]! = unpack 1782 11 (SGF h) := by
  have e : suzGenArrs[h]! = wordArr 1782 #[b0Arr, b1Arr] imgWords[h]! := by
    have hi : h < imgWords.size := by rw [KernelCosetJ.SuzTab.himg.1]; exact hh
    rw [suzGenArrs, getElem!_pos _ h (by rw [Array.size_map]; exact hi), Array.getElem_map,
      getElem!_pos imgWords h hi]
  rw [e, wordArr, wordA_unpack sz (j := 2) (fun _ h' => bS h') (fun _ h' => bSI h')
    (fun _ h' => permB_of_pp (ppB h')) (fun _ h' => by rw [bfi h']; exact permB_of_pp (ppB h').inv)
    (imgL hh), imgW hh, sg_val hh]

theorem ppSG {h : Nat} (hh : h < 7) : PP 1782 11 (SGF h) := by
  rw [← sg_val hh]
  refine pp_of_permB sz (permB_wordK sz (j := 2) (fun _ h' => permB_of_pp (ppB h'))
    (fun _ h' => by rw [bfi h']; exact permB_of_pp (ppB h').inv) ?_)
  rw [← imgW hh]
  exact imgL hh

theorem sgi_val {h : Nat} (hh : h < 7) : pv (SGF h) = SGIF h :=
  beq_of (allN_spec sgiK h hh)

theorem sgInv_eq {h : Nat} (hh : h < 7) : (suzGenArrs.map (invCand 1782))[h]! =
    unpack 1782 11 (SGIF h) := by
  rw [getElem!_map_of_lt (by rw [genSize]; exact hh), sg_eq hh, invCand_PP (ppSG hh), sgi_val hh]

theorem ppSGI {h : Nat} (hh : h < 7) : PP 1782 11 (SGIF h) := by
  rw [← sgi_val hh]
  exact (ppSG hh).inv

theorem x_eq : cf24XArr = unpack 1782 11 XK := by
  have hl : lettersOK 7 (codesZ cf24XCodes) = true := lettersOK_codes _ xCodes
  rw [cf24XArr, cf24X, zword_codes _ xCodes, wordArr, wordA_unpack sz (j := 7)
    (fun _ h' => sg_eq h') (fun _ h' => sgInv_eq h') (fun _ h' => permB_of_pp (ppSG h'))
    (fun _ h' => permB_of_pp (ppSGI h')) hl, beq_of xK]

theorem y_eq : cf24YArr = unpack 1782 11 YK := by
  have hl : lettersOK 7 (codesZ cf24YCodes) = true := lettersOK_codes _ yCodes
  rw [cf24YArr, cf24Y, zword_codes _ yCodes, wordArr, wordA_unpack sz (j := 7)
    (fun _ h' => sg_eq h') (fun _ h' => sgInv_eq h') (fun _ h' => permB_of_pp (ppSG h'))
    (fun _ h' => permB_of_pp (ppSGI h')) hl, beq_of yK]

theorem lxp : lettersOK 5 cf24XP = true := by decide
theorem lyp : lettersOK 5 cf24YP = true := by decide

theorem xyParts : wk LF LIF cf24XP = XK ∧ wk LF LIF cf24YP = YK ∧ pc XK YK = pc YK XK := by
  have h := xyK
  simp only [bAnd_iff] at h
  exact ⟨beq_of h.1, beq_of h.2.1, beq_of h.2.2⟩

theorem wL {wd : List Int} (hl : lettersOK 5 wd = true) :
    wordArr 1782 cf24EllArrs wd = unpack 1782 11 (wk LF LIF wd) :=
  wordA_unpack sz (j := 5) (fun _ h' => ell_eq h') (fun _ h' => ellInv_eq h')
    (fun _ h' => permB_of_pp (ppL h')) (fun _ h' => permB_of_pp (ppLI h')) hl

theorem ppX : PP 1782 11 XK := by
  rw [← xyParts.1]
  exact pp_of_permB sz (permB_wordK sz (j := 5) (fun _ h' => permB_of_pp (ppL h'))
    (fun _ h' => permB_of_pp (ppLI h')) lxp)

theorem ppY : PP 1782 11 YK := by
  rw [← xyParts.2.1]
  exact pp_of_permB sz (permB_wordK sz (j := 5) (fun _ h' => permB_of_pp (ppL h'))
    (fun _ h' => permB_of_pp (ppLI h')) lyp)

theorem testBit_maskL : ∀ (L : List Nat) (x : Nat), (maskL L).testBit x = decide (x ∈ L)
  | [], x => by simp [maskL]
  | a :: L, x => by
    have e : maskL (a :: L) = Nat.lor (Nat.shiftLeft 1 a) (maskL L) := rfl
    rw [e]
    change ((1 <<< a) ||| maskL L).testBit x = _
    rw [Nat.testBit_or, testBit_maskL L x, Nat.one_shiftLeft, Nat.testBit_two_pow]
    by_cases h : a = x
    · subst h
      simp
    · simp [h, Ne.symm h, List.mem_cons]

theorem pg1 (P x : Nat) : pg 1 (mask 1) P x = if P.testBit x then 1 else 0 := by
  have hm : mask 1 = 1 := by decide
  have e1 : Nat.mul 1 x = x := Nat.one_mul x
  change Nat.land (Nat.shiftRight P (Nat.mul 1 x)) (mask 1) = _
  rw [hm, e1]
  change (P >>> x) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (P / 2 ^ x) with h | h <;> simp [h]

theorem inO1_eq (x : Nat) : cf24InO1 x = (pg 1 (mask 1) OM x == 1) := by
  rw [pg1, ← beq_of omK, testBit_maskL, cf24InO1]
  by_cases h : x ∈ cf24O1 <;> simp [h, List.contains_iff_mem]

theorem bk_canon : canonK 1782 11 (mask 11) (1782 * 11) BK = true := betaK_parts.2.1

theorem check : cf24PermCheck = true := by
  have hx := x_eq
  have hy := y_eq
  have pts := ptK
  simp only [bAnd_iff] at pts
  obtain ⟨p1, p2, p3, p4⟩ := pts
  unfold cf24PermCheck
  simp only [Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, lx⟩, ly⟩, lxp⟩, lyp⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [allLt_iff]
    intro k hk
    rw [genA hk]
    exact CFSG.KC.Fi22RkS.isInvA_PP (ppGH hk)
  · rw [allPermsOK, ellSize, allLt_iff]
    intro j hj
    rw [ell_eq hj]
    exact CFSG.KC.Fi22RkS.isInvA_PP (ppL hj)
  · rw [hx, wL lxp, xyParts.1, eqA_PP ppX ppX, Nat.beq_refl]
  · rw [hy, wL lyp, xyParts.2.1, eqA_PP ppY ppY, Nat.beq_refl]
  · rw [hx, hy, compA_PP ppX ppY, compA_PP ppY ppX, xyParts.2.2, eqA_PP (ppY.mul ppX) (ppY.mul ppX),
      Nat.beq_refl]
  · simp only [allBelow, List.all_eq_true, List.mem_range]
    intro j hj x hx'
    rw [ell_eq hj, unpack_getElem!, if_pos hx', inO1_eq, inO1_eq]
    have e := beq_of (allN_spec (allN_spec oK j hj) x hx')
    rw [e]
    exact beq_self_eq_true _
  · simp only [allBelow, List.all_eq_true, List.mem_range]
    intro j hj
    rw [betaArr_eq, ell_eq hj, compA_unpack bk_canon (ppL hj).1, compA_unpack (ppL hj).1 bk_canon,
      eqA_unpack (canonK_pcomp bk_canon (ppL hj).1) (canonK_pcomp (ppL hj).1 bk_canon)]
    exact allN_spec bK j hj
  · rw [inO1_eq, beq_of p1]
    rfl
  · rw [t0_eq, unpack_getElem!, if_pos (by norm_num), inO1_eq, beq_of p2]
    rfl
  · rw [betaArr_eq, unpack_getElem!, if_pos (by norm_num), inO1_eq, beq_of p3]
    rfl
  · rw [tBetaArr, t0_eq, betaArr_eq, compA_unpack t0_canon bk_canon, unpack_getElem!,
      if_pos (by norm_num), inO1_eq, beq_of p4]
    rfl

end CertificateChecks.KernelSpor.CF24

end
