module

public import Certificates.Kernel.Sporadic.OddCore.S8147E
public import CFSG.Certificates.Kernel.HeFixKSnd.Basic
public import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.S8147

open CFSG.RankThree.Native CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Fischer CFSG.Monster.B.Mathieu CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.KC.BfsPin CFSG.KC.Misc.ArrEnum CFSG.KS.HNA CFSG.KC.PermTool CFSG.KS.EnumBase
open CFSG.KS.PEnum (r32)
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.OddCore

@[expose] noncomputable def pm (P : Nat) : Equiv.Perm (Fin 1782) := permOfArr 1782 (unpack 1782 11 P)

theorem rep_pm {P : Nat} (h : PP 1782 11 P) : Rep 1782 (unpack 1782 11 P) (pm P) :=
  rep_of_validA (validU h)

theorem pm_mul {P Q : Nat} (hP : PP 1782 11 P) (hQ : PP 1782 11 Q) :
    pm (pcomp 1782 11 (mask 11) P Q) = pm P * pm Q := by
  have h := rep_compA (rep_pm hP) (rep_pm hQ)
  rw [cmpU hP hQ] at h
  exact (rep_pm (hP.mul hQ)).unique h

theorem pm_inv {P : Nat} (hP : PP 1782 11 P) : pm (pinvS 1782 11 (mask 11) P) = (pm P)⁻¹ := by
  have h := rep_compA (rep_pm hP.inv) (rep_pm hP)
  have e : compA 1782 (unpack 1782 11 (pinvS 1782 11 (mask 11) P)) (unpack 1782 11 P) =
      idA 1782 := CFSG.KC.HeFixKSnd.comp_inv_left_PP hP
  rw [e] at h
  exact eq_inv_of_mul_eq_one_left (rep_idA.unique h).symm

theorem pm_get {P : Nat} (hP : PP 1782 11 P) (x : Fin 1782) :
    (pm P x : Nat) = pg 11 (mask 11) P x := by
  rw [← (rep_pm hP).apply x.2, upk_get x.2]

theorem pm_ext {P Q : Nat} (hP : PP 1782 11 P) (hQ : PP 1782 11 Q) (h : pm P = pm Q) : P = Q := by
  obtain ⟨-, hw, hp1, -⟩ := CFSG.KS.PF.canon_facts hP.1
  obtain ⟨-, -, hq1, -⟩ := CFSG.KS.PF.canon_facts hQ.1
  refine CFSG.KS.PF.eq_of_fields (CFSG.KS.PF.w_pos hw) hp1 hq1 fun i hi => ?_
  rw [← pm_get hP ⟨i, hi⟩, ← pm_get hQ ⟨i, hi⟩, h]

theorem pm_commP {P Q : Nat} (hP : PP 1782 11 P) (hQ : PP 1782 11 Q) :
    pm (commP 1782 11 P Q) = pm P * pm Q * (pm P)⁻¹ * (pm Q)⁻¹ := by
  unfold commP
  rw [pm_mul (hP.mul hQ) (hP.inv.mul hQ.inv), pm_mul hP hQ, pm_mul hP.inv hQ.inv, pm_inv hP,
    pm_inv hQ]
  group

@[expose] def keysF : List (Fin 1782) := [0, 1, 2, 3, 4, 8, 5, 6]

theorem keysF_mem : ∀ b ∈ keysF, (b : Nat) ∈ [0, 1, 2, 3, 4, 8, 5, 6] := by decide

theorem keys_memF : ∀ p ∈ [0, 1, 2, 3, 4, 8, 5, 6], ∃ b ∈ keysF, (b : Nat) = p := by decide

theorem keyK_congr {ps : List Nat} {t u : Nat}
    (h : ∀ p ∈ ps, pg 11 (mask 11) t p = pg 11 (mask 11) u p) :
    CFSG.KC.BfsPin.keyK 1782 11 ps t = CFSG.KC.BfsPin.keyK 1782 11 ps u := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    change Nat.add (pg 11 (mask 11) t p) (Nat.mul 1782 (CFSG.KC.BfsPin.keyK 1782 11 ps t)) =
      Nat.add (pg 11 (mask 11) u p) (Nat.mul 1782 (CFSG.KC.BfsPin.keyK 1782 11 ps u))
    rw [h p List.mem_cons_self, ih fun q hq => h q (List.mem_cons_of_mem p hq)]

theorem sep_enum {gs : Array (Array Nat)} {c : ArrCert} {N : Nat} {T : Nat → Nat} {SK : List Nat}
    (he : enumOK 1782 gs suzFiveKeys c = true) (hs : c.pts.size = N)
    (hT : ∀ i < N, c.pts[i]! = unpack 1782 11 (T i)) (hTP : ∀ i < N, PP 1782 11 (T i))
    (hk : keysSK 1782 11 [0, 1, 2, 3, 4, 8, 5, 6] N T SK = true) {P Q : Nat} (hP : PP 1782 11 P)
    (hQ : PP 1782 11 Q) (hPm : pm P ∈ Subgroup.closure (permsA 1782 gs))
    (hQm : pm Q ∈ Subgroup.closure (permsA 1782 gs))
    (h : ∀ b ∈ [0, 1, 2, 3, 4, 8, 5, 6], pg 11 (mask 11) P b = pg 11 (mask 11) Q b) : P = Q := by
  obtain ⟨hmem, hcard, -⟩ := enumOK_spec keys_lt he
  have hεm : ∀ k < N, pm (T k) ∈ Subgroup.closure (permsA 1782 gs) := fun k hk' =>
    (hmem _).2 ⟨k, by rw [hs]; exact hk', by rw [hT k hk']; rfl⟩
  refine pm_ext hP hQ (CFSG.KS.CardSep.eq_of_base (hcard.trans hs) (ε := fun k => pm (T k)) hεm
    (B := keysF) (fun i hi j hj hij => keysSK_spec hk i hi j hj (keyK_congr fun p hp => ?_))
    hPm hQm fun b hb => Fin.ext ?_)
  · obtain ⟨b, hb, rfl⟩ := keys_memF p hp
    rw [← pm_get (hTP i hi), ← pm_get (hTP j hj), hij b hb]
  · rw [pm_get hP, pm_get hQ]
    exact h b (keysF_mem b hb)

theorem allL_iff {ps : List Nat} {f : Nat → Bool} : CFSG.KS.BaseEq.allL ps f = true ↔ ∀ p ∈ ps, f p = true := by
  induction ps with
  | nil => simp [CFSG.KS.BaseEq.allL]
  | cons q ps ih =>
    change bAnd(f q, CFSG.KS.BaseEq.allL ps f) = true ↔ _
    rw [bAnd_eq, Bool.and_eq_true, ih]
    simp

theorem commA_key {gs : Array (Array Nat)} {c : ArrCert} {N : Nat} {T : Nat → Nat} {SK : List Nat}
    (he : enumOK 1782 gs suzFiveKeys c = true) (hs : c.pts.size = N)
    (hT : ∀ i < N, c.pts[i]! = unpack 1782 11 (T i)) (hTP : ∀ i < N, PP 1782 11 (T i))
    (hk : keysSK 1782 11 [0, 1, 2, 3, 4, 8, 5, 6] N T SK = true) {P D : Nat} (hP : PP 1782 11 P)
    (hD : PP 1782 11 D) (hPm : pm P ∈ Subgroup.closure (permsA 1782 gs))
    (hDm : pm D ∈ Subgroup.closure (permsA 1782 gs)) :
    commA 1782 (unpack 1782 11 P) (unpack 1782 11 D) = keyCommK P D := by
  rw [commAU hP hD]
  unfold keyCommK
  apply Bool.eq_iff_iff.2
  rw [allL_iff, Nat.beq_eq]
  constructor
  · intro e b hb
    have hb' : b < 1782 := by simp at hb; omega
    rw [Nat.beq_eq, ← CFSG.KS.PF.pg_pcomp (by norm_num) hb', ← CFSG.KS.PF.pg_pcomp (by norm_num) hb', e]
  · intro h
    refine sep_enum he hs hT hTP hk (hP.mul hD) (hD.mul hP)
      (by rw [pm_mul hP hD]; exact Subgroup.mul_mem _ hPm hDm)
      (by rw [pm_mul hD hP]; exact Subgroup.mul_mem _ hDm hPm) fun b hb => ?_
    have hb' : b < 1782 := by simp at hb; omega
    rw [CFSG.KS.PF.pg_pcomp (by norm_num) hb', CFSG.KS.PF.pg_pcomp (by norm_num) hb']
    exact Nat.eq_of_beq_eq_true (h b hb)

theorem nB_true {b : Bool} (h : nB b = true) : b = false := by
  rw [nB_eq] at h
  simpa using h

theorem allLt_eq_allN {m : Nat} {f g : Nat → Bool} (h : ∀ i < m, f i = g i) :
    allLt m f = allN m g := by
  apply Bool.eq_iff_iff.2
  rw [CFSG.Monster.B.Co2.allLt_iff, CFSG.KS.Raw.Orb.allN_iff]
  exact ⟨fun h' i hi => (h i hi) ▸ h' i hi, fun h' i hi => (h i hi).symm ▸ h' i hi⟩

theorem cGen_PP {i k : Nat} (hi : i < 6) (hk : k < 2) : PP 1782 11 (SFvT.F (Nat.add (6 + 2 * i) k)) :=
  fv_PP (by change 6 + 2 * i + k < 18; omega)

theorem pm_cGen {i k : Nat} (hi : i < 6) (hk : k < 2) :
    pm (SFvT.F (Nat.add (6 + 2 * i) k)) ∈ Subgroup.closure (permsA 1782 (suzFiveCArrs i)) := by
  refine Subgroup.subset_closure ⟨k, by rw [cArrs_size hi]; exact hk, ?_⟩
  change permOfArr 1782 (suzFiveCArrs i)[k]! = pm _
  rw [cArrs_fv hi hk]
  rfl

theorem dCheck_of {i N Nd nd dsz cnt : Nat} {TC TD DG : Nat → Nat} {SKc : List Nat}
    (hi : i < 6)
    (hC : enumOK 1782 (suzFiveCArrs i) suzFiveKeys (suzFiveCCert i) = true ∧
      (suzFiveCCert i).pts.size = N ∧
      (∀ j < N, (suzFiveCCert i).pts[j]! = unpack 1782 11 (TC j)) ∧ ∀ j < N, PP 1782 11 (TC j))
    (hkC : keysSK 1782 11 [0, 1, 2, 3, 4, 8, 5, 6] N TC SKc = true)
    (hD : enumOK 1782 (suzFiveDArrs i) suzFiveKeys (suzFiveDCert i) = true ∧
      (suzFiveDCert i).pts.size = Nd ∧
      (∀ j < Nd, (suzFiveDCert i).pts[j]! = unpack 1782 11 (TD j)) ∧ ∀ j < Nd, PP 1782 11 (TD j))
    (hNd : Nd = dsz) (hds : (suzFiveDArrs i).size = nd) (hnd : 2 ≤ nd)
    (hdg : ∀ l < nd, (suzFiveDArrs i)[l]! = unpack 1782 11 (DG l)) (hDP : ∀ l < nd, PP 1782 11 (DG l))
    (hDm : ∀ l < nd, pm (DG l) ∈ Subgroup.closure (permsA 1782 (suzFiveCArrs i)))
    (hchk : dChk (SFvT.F (Nat.add (6 + 2 * i) 0)) (SFvT.F (Nat.add (6 + 2 * i) 1)) nd DG Nd TD N TC
      cnt = true)
    (hpow : cnt = 5 → powChk nd DG N TC (SFvT.F i) = true) :
    suzFiveDCheck (suzFiveCArrs i) (suzFiveCCert i) (suzFiveDArrs i) (suzFiveDCert i) dsz
      (suzFiveLineArr i) cnt = true := by
  obtain ⟨c1, c2, c3, c4⟩ := hC
  obtain ⟨d1, d2, d3, d4⟩ := hD
  have hG : ∀ k < 2, PP 1782 11 (SFvT.F (Nat.add (6 + 2 * i) k)) := fun k hk => cGen_PP hi hk
  unfold dChk at hchk
  simp only [bAnd_eq, Bool.and_eq_true] at hchk
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hchk
  have hcl : ∀ j < N, pm (TC j) ∈ Subgroup.closure (permsA 1782 (suzFiveCArrs i)) := by
    intro j hj
    obtain ⟨hmem, -, -⟩ := enumOK_spec keys_lt c1
    exact (hmem _).2 ⟨j, by rw [c2]; exact hj, by rw [c3 j hj]; rfl⟩
  have hkey : ∀ j < N, (allLt (suzFiveDArrs i).size fun l =>
      commA 1782 (suzFiveCCert i).pts[j]! (suzFiveDArrs i)[l]!) =
      allN nd fun l => keyCommK (TC j) (DG l) := by
    intro j hj
    rw [hds]
    refine allLt_eq_allN fun l hl => ?_
    rw [c3 j hj, hdg l hl]
    exact commA_key c1 c2 c3 c4 hkC (c4 j hj) (hDP l hl) (hcl j hj) (hDm l hl)
  unfold suzFiveDCheck
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨d1, by rw [d2, hNd]⟩, by rw [hds]; exact hnd⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro k hk
    rw [cArrs_size hi] at hk
    rw [CFSG.Monster.B.Co2.allLt_iff]
    intro l hl
    rw [hds] at hl
    have hm := allN_spec h1 l hl
    rw [Bool.and_eq_true] at hm
    rw [cArrs_fv hi hk, hdg l hl, conjU (hG k hk) (hDP l hl)]
    refine memK_any d2 d3 d4 (cnjPP (hG k hk) (hDP l hl)) ?_
    interval_cases k
    · exact hm.1
    · exact hm.2
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro k hk
    rw [cArrs_size hi] at hk
    rw [CFSG.Monster.B.Co2.allLt_iff]
    intro l hl
    rw [cArrs_size hi] at hl
    rw [cArrs_fv hi hk, cArrs_fv hi hl, commU (hG k hk) (hG l hl)]
    refine memK_any d2 d3 d4 (commPP (hG k hk) (hG l hl)) ?_
    interval_cases k <;> interval_cases l
    · exact h2
    · exact h3
    · exact h4
    · exact h5
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro l hl
    rw [hds] at hl
    rw [hdg l hl, inM_C (hDP l hl).1]
    exact allN_spec h6 l hl
  · rw [hdg 0 (by omega), hdg 1 (by omega), commAU (hDP 0 (by omega)) (hDP 1 (by omega))]
    rw [nB_true h7]
    rfl
  · unfold suzFiveCentCount
    rw [← List.countP_eq_length_filter, c2]
    rw [← Nat.eq_of_beq_eq_true h8, cntN_eq]
    exact List.countP_congr fun j hj => by rw [hkey j (List.mem_range.1 hj)]
  · rw [Bool.or_eq_true]
    by_cases h5' : cnt = 5
    · right
      have hp := hpow h5'
      unfold powChk at hp
      rw [CFSG.Monster.B.Co2.allLt_iff]
      intro j hj
      rw [c2] at hj
      have hpj := allN_spec hp j hj
      rw [hkey j hj, Bool.or_eq_true]
      by_cases hc : (allN nd fun l => keyCommK (TC j) (DG l)) = true
      · right
        rw [bIf_eq, if_pos hc, anyNP_eq, List.any_eq_true] at hpj
        obtain ⟨e, he, hq⟩ := hpj
        rw [List.any_eq_true]
        refine ⟨e, he, ?_⟩
        rw [c3 j hj, line_eq hi, powU (fv_PP (by omega)) e,
          eqU (c4 j hj) (pwPP (fv_PP (by omega)) e)]
        exact hq
      · left
        simpa using hc
    · left
      simp [h5']

end CertificateChecks.KernelSpor.S8147

end
