
module

public import Certificates.Kernel.Misc.Tits.E07043K
public import Certificates.Kernel.Sporadic.Tits.Order2264
import Certificates.Kernel.Misc.Tits.Pi7092
import CFSG.Certificates.Kernel.BfsPinAlg
import CFSG.Certificates.Kernel.BfsPinSetSound
import CFSG.Certificates.Kernel.SporSch.OrbLabelsSound
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic
import all Init.Data.List.Basic
import CFSG.Certificates.Kernel.Spor.RawSiftK

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.E7043

open CFSG CFSG.Quasithin CFSG.Quasithin.RuRank3 CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.RuSchreier
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.OrbLab
open CertificateChecks.KernelMisc CertificateChecks.KernelMisc.Tits7050
open CertificateChecks.KernelSpor.Tits2264 CertificateChecks.KernelSporSch

abbrev Cn (p : Nat) : Prop := canonK 1755 11 (mask 11) (1755 * 11) p = true

theorem szOK' : szOK 1755 11 = true := by decide

theorem cId : Cn (pidn 1755 11) := (CFSG.KC.BfsPin.PP.id szOK').1

theorem idA_eq' : idA 1755 = unpack 1755 11 (pidn 1755 11) := CFSG.KC.BfsPin.idA_eq szOK'

theorem cmp {p q : Nat} (hp : Cn p) (hq : Cn q) :
    compA 1755 (unpack 1755 11 p) (unpack 1755 11 q) = unpack 1755 11 (pc p q) :=
  CFSG.KC.BfsPin.compA_unpack hp hq

theorem cmpC {p q : Nat} (hp : Cn p) (hq : Cn q) : Cn (pc p q) :=
  CFSG.KC.BfsPin.canonK_pcomp hp hq

theorem eqU {p q : Nat} (hp : Cn p) (hq : Cn q) :
    eqA 1755 (unpack 1755 11 p) (unpack 1755 11 q) = Nat.beq p q :=
  CFSG.KC.BfsPin.eqA_unpack hp hq

theorem powU {p : Nat} (hp : Cn p) :
    ∀ k, powArr 1755 (unpack 1755 11 p) k = unpack 1755 11 (pw p k) ∧ Cn (pw p k)
  | 0 => ⟨idA_eq', cId⟩
  | k + 1 => by
    obtain ⟨h1, h2⟩ := powU hp k
    refine ⟨?_, cmpC hp h2⟩
    rw [powArr, h1, cmp hp h2]
    rfl

theorem cOf {P : Nat} (h : permC P = true) : Cn P := (permC_spec h).2.1

theorem cIOf {P : Nat} (h : permC P = true) : Cn (pinvS 1755 11 (mask 11) P) := (permC_spec h).2.2

theorem invU {P : Nat} (h : permC P = true) :
    invCand 1755 (unpack 1755 11 P) = unpack 1755 11 (pinvS 1755 11 (mask 11) P) :=
  CFSG.KC.BfsPin.invCand_unpack (permC_spec h).1

theorem pSA : permC SA = true := ((bAnd_iff (permC SA) (permC SB)).1 kPerm).1
theorem pSB : permC SB = true := ((bAnd_iff (permC SA) (permC SB)).1 kPerm).2
theorem pK {j : Nat} (hj : j < 5) : permC (TK.F j) = true := allN_spec permK j hj

theorem sa_eq : ruSdA = unpack 1755 11 SA := by
  change hexTable 3 1755 (1755 * 0) ruSdText = _
  rw [TSd.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable_sound TSd.all 0 (by norm_num)

theorem sb_eq : ruSdB = unpack 1755 11 SB := by
  change hexTable 3 1755 (1755 * 1) ruSdText = _
  rw [TSd.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable_sound TSd.all 1 (by norm_num)

theorem bl_eq : titsK0Bl = unpack 1755 11 (TBl.F 0) := by
  change hexTable 2 1755 (1755 * 0) titsK0BlText = _
  rw [TBl.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable_sound TBl.all 0 (by norm_num)

theorem k_eq {j : Nat} (hj : j < 5) : titsK0Strong[j]! = unpack 1755 11 (TK.F j) := by
  rw [titsK0Strong, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  change hexTable 3 1755 (1755 * j) titsK0Text = _
  rw [TK.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable_sound TK.all j hj

theorem gens_eq {i : Nat} (hi : i < 3) : titsK0Gens[i]! = unpack 1755 11 (TK.F i) := by
  rw [titsK0Gens, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  exact k_eq (by omega)

theorem bl_get {x : Nat} (hx : x < 1755) : titsK0Bl[x]! = Bf x := by
  rw [bl_eq, CFSG.KC.BfsPin.unpack_get' hx]
  rfl

theorem g_get {i x : Nat} (hi : i < 3) (hx : x < 1755) : (titsK0Gens[i]!)[x]! = gK i x := by
  rw [gens_eq hi, CFSG.KC.BfsPin.unpack_get' hx]
  rfl

theorem g_lt {i x : Nat} (hi : i < 3) (hx : x < 1755) : gK i x < 1755 := by
  have := allN_spec (allN_spec kRange i hi) x hx
  simpa using this

theorem lab_get {x : Nat} (hx : x < 1755) : titsK0Lab[x]! = Lf x := by
  have hs : titsK0Gens.size = 3 := by simp [titsK0Gens]
  have hg : ∀ k < 3, ∀ x < 1755, ga titsK0Gens k x = gK k x := fun k hk x hx => g_get hk hx
  rw [titsK0Lab, orbLab]
  exact (orbLabels_of_K hs hg kOrb).2 x hx

theorem tauK : ∀ i < 3, ∀ c < 26, (titsK0Tau[i]!)[c]! = Tf i c := by decide +kernel

theorem repsK : ∀ c < 26, titsK0BlReps[c]! = Rp c := by decide +kernel

theorem T_le : T ≤ titsA := by
  unfold T
  rw [Subgroup.closure_le]
  rintro _ ⟨j, rfl⟩
  exact titsD_le_titsA (titsT_mem_titsD (i := j.val) (by omega))

theorem t_mem : t ∈ titsA := by
  have e : t = titsGen 1 := by
    rw [titsGen, gen_eq (by norm_num)]
    rfl
  rw [e]
  exact titsGen_mem_titsA (by norm_num)

theorem inA_of_mem {P : Nat} (hP : permC P = true)
    (hm : permOfArr 1755 (unpack 1755 11 P) ∈ titsA) : inTitsA (unpack 1755 11 P) = true := by
  rw [← titsQA_original] at hm
  exact (siftA_iff_mem_ofArrays (n := 1755) (hn := by norm_num) (hk := by
      rw [titsAmbientArrs_size]; norm_num) (hb := by decide) (chunks := 4)
    titsChains_check.2.2.2.2.2.1 (by norm_num) titsChains_check.2.2.2.2.2.2.2.2.1
    (rep_of hP).1).2 hm

theorem inA_of_D {P : Nat} (hP : permC P = true) (hs : siftD P = true) :
    inTitsA (unpack 1755 11 P) = true :=
  inA_of_mem hP (T_le (mem_T hs hP))

theorem inA_of_a {P : Nat} (hP : permC P = true)
    (hs : bAnd(siftD (pc P (GI 1)), permC (pc P (GI 1))) = true) :
    inTitsA (unpack 1755 11 P) = true := by
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 hs
  refine inA_of_mem hP ?_
  have hm := mem_T h1 h2
  rw [pc, perm_mul hP TitsPi.permGI h2] at hm
  have hinv : permOfArr 1755 (unpack 1755 11 (GI 1)) = t⁻¹ :=
    (rep_of TitsPi.permGI).1.unique (rep_of (gperm 1 (by norm_num))).2
  rw [hinv] at hm
  have h3 := mul_mem (T_le hm) t_mem
  rwa [inv_mul_cancel_right] at h3

theorem bindsK : Binds 1755 11 TitsK0.S 5 3 TitsK0.BP titsK0Strong (ruBaseArr 1755 [0, 12, 1]) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [titsK0Strong], fun j hj => ?_, rfl,
    fun t ht => ?_⟩
  · rw [k_eq hj, Nat.eq_of_beq_eq_true (allN_spec kS j hj)]
  · rw [Nat.eq_of_beq_eq_true (allN_spec kB t ht)]
    interval_cases t <;> rfl

theorem permsK :
    allN 5 (fun j => permOK 1755 11 (mask 11) (1755 * 11) (TitsK0.S j) (TitsK0.SI j)) = true :=
  (CFSG.KS.Raw.Orb.head_facts TitsK0.head).1

theorem inK0_of {G : Nat} (hp : permC G = true) (h : sk G = true) :
    inTitsK0 (unpack 1755 11 G) = true :=
  siftK_soundR bindsK permsK TitsK0.hl rfl (hiOf (permC_spec hp).2.1)
    (range_of_permOK (permC_spec hp).1) h

theorem conj_eq {c i : Nat} (hc : permC c = true) (hi : i < 3) :
    CFSG.Quasithin.RuRank3.conjArr (unpack 1755 11 c) titsK0Gens[i]! = unpack 1755 11 (cj c (TK.F i)) := by
  unfold CFSG.Quasithin.RuRank3.conjArr
  rw [gens_eq hi, invU hc, cmp (cOf hc) (cOf (pK (by omega))),
    cmp (cmpC (cOf hc) (cOf (pK (by omega)))) (cIOf hc)]
  rfl

theorem bne_one (a : Nat) : (a != 1) = !(Nat.beq a 1) := by
  have e : (a == 1) = Nat.beq a 1 := by rw [Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq]
  rw [bne, e]

theorem partA1 : (allLt 3 fun i => allLt 1755 fun x => titsK0Lab[x]! != 1 ||
    (decide (titsK0Bl[x]! < 26) &&
      titsK0Bl[(titsK0Gens[i]!)[x]!]! == (titsK0Tau[i]!)[titsK0Bl[x]!]!)) = true := by
  rw [allLt_iff]
  intro i hi
  rw [allLt_iff]
  intro x hx
  have hb := allN_spec (allN_spec kBlk i hi) x hx
  unfold blkK at hb
  rw [lab_get hx, bl_get hx, g_get hi hx, bl_get (g_lt hi hx), bne_one]
  cases h1 : Nat.beq (Lf x) 1
  · rfl
  · rw [h1] at hb
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, Nat.blt_eq] at hb
    obtain ⟨hb1, hb2⟩ := hb
    rw [tauK i hi _ hb1, Nat.eq_of_beq_eq_true hb2]
    simp [hb1]

theorem partA2 : (allLt 26 fun c => decide (titsK0BlReps[c]! < 1755) &&
    titsK0Lab[titsK0BlReps[c]!]! == 1 && titsK0Bl[titsK0BlReps[c]!]! == c) = true := by
  rw [allLt_iff]
  intro c hc
  have h := allN_spec kReps c hc
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  rw [repsK c hc, lab_get h1, bl_get h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3]
  simp [h1]

theorem partA3 : (allLt 3 fun i => isInvA 26 titsK0Tau[i]! (invCand 26 titsK0Tau[i]!) &&
    lettersOK 3 (titsK0TauWords.getD i []) &&
    eqA 26 (wordA 26 psl26GensA psl26GensInvA (titsK0TauWords.getD i [])) titsK0Tau[i]!) = true := by
  decide +kernel

theorem partA4 : (allLt 3 fun i => lettersOK 3 (psl26TauWords.getD i []) &&
    eqA 26 (wordA 26 titsK0Tau titsK0TauInv (psl26TauWords.getD i [])) psl26GensA[i]!) = true := by
  decide +kernel

theorem partA5 : (allLt 3 fun i => isInvA 26 psl26GensA[i]! (invCand 26 psl26GensA[i]!)) = true := by
  decide +kernel

open Certificates in
open CFSG CFSG.Quasithin CFSG.Quasithin.RuRank3 CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.RuSchreier in
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native in
theorem c7043 :
    ((allLt 3 fun i => allLt 1755 fun x => titsK0Lab[x]! != 1 ||
         (decide (titsK0Bl[x]! < 26) &&
           titsK0Bl[(titsK0Gens[i]!)[x]!]! == (titsK0Tau[i]!)[titsK0Bl[x]!]!)) = true ∧
       (allLt 26 fun c => decide (titsK0BlReps[c]! < 1755) && titsK0Lab[titsK0BlReps[c]!]! == 1 &&
         titsK0Bl[titsK0BlReps[c]!]! == c) = true ∧
       (allLt 3 fun i => isInvA 26 titsK0Tau[i]! (invCand 26 titsK0Tau[i]!) &&
         lettersOK 3 (titsK0TauWords.getD i []) &&
         eqA 26 (wordA 26 psl26GensA psl26GensInvA (titsK0TauWords.getD i [])) titsK0Tau[i]!) = true ∧
       (allLt 3 fun i => lettersOK 3 (psl26TauWords.getD i []) &&
         eqA 26 (wordA 26 titsK0Tau titsK0TauInv (psl26TauWords.getD i [])) psl26GensA[i]!) = true ∧
       (allLt 3 fun i => isInvA 26 psl26GensA[i]! (invCand 26 psl26GensA[i]!)) = true)
    ∧ (isInvA 1755 ruSdA (invCand 1755 ruSdA) = true ∧ isInvA 1755 ruSdB (invCand 1755 ruSdB) = true ∧
       inTitsA ruSdA = true ∧ inTitsA ruSdB = true ∧
       (allLt 3 fun i => inTitsK0 (CFSG.Quasithin.RuRank3.conjArr ruSdA titsK0Gens[i]!) &&
         inTitsK0 (CFSG.Quasithin.RuRank3.conjArr ruSdB titsK0Gens[i]!)) = true ∧
       eqA 1755 (powArr 1755 ruSdA 8) (idA 1755) = true ∧
       eqA 1755 (powArr 1755 ruSdA 4) (idA 1755) = false ∧
       eqA 1755 (compA 1755 ruSdB ruSdB) (idA 1755) = true ∧
       eqA 1755 (CFSG.Quasithin.RuRank3.conjArr ruSdB ruSdA) (powArr 1755 ruSdA 3) = true ∧
       (allLt 8 fun i => !eqA 1755 ruSdB (powArr 1755 ruSdA i)) = true) := by
  have cA := cOf pSA
  have cB := cOf pSB
  have hk := kPow
  simp only [bAnd_iff] at hk
  obtain ⟨p8, p4, pbb, pcj, p8s⟩ := hk
  refine ⟨⟨partA1, partA2, partA3, partA4, partA5⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sa_eq]
    exact isInv_of pSA
  · rw [sb_eq]
    exact isInv_of pSB
  · rw [sa_eq]
    exact inA_of_a pSA kDA
  · rw [sb_eq]
    exact inA_of_D pSB kDB
  · rw [allLt_iff]
    intro i hi
    have hk := allN_spec kSift i hi
    simp only [bAnd_iff] at hk
    obtain ⟨⟨ha1, ha2⟩, hb1, hb2⟩ := hk
    rw [sa_eq, sb_eq, conj_eq pSA hi, conj_eq pSB hi, inK0_of ha2 ha1, inK0_of hb2 hb1]
    rfl
  · rw [sa_eq, (powU cA 8).1, idA_eq', eqU (powU cA 8).2 cId]
    exact p8
  · rw [sa_eq, (powU cA 4).1, idA_eq', eqU (powU cA 4).2 cId]
    cases hq : Nat.beq (pw SA 4) (pidn 1755 11)
    · rfl
    · rw [hq] at p4
      exact absurd p4 Bool.false_ne_true
  · rw [sb_eq, cmp cB cB, idA_eq', eqU (cmpC cB cB) cId]
    exact pbb
  · rw [sb_eq, sa_eq]
    unfold CFSG.Quasithin.RuRank3.conjArr
    rw [invU pSB, cmp cB cA, cmp (cmpC cB cA) (cIOf pSB), (powU cA 3).1,
      eqU (cmpC (cmpC cB cA) (cIOf pSB)) (powU cA 3).2]
    exact pcj
  · rw [allLt_iff]
    intro i hi
    have h := allN_spec p8s i hi
    rw [sb_eq, sa_eq, (powU cA i).1, eqU cB (powU cA i).2]
    cases hq : Nat.beq SB (pw SA i)
    · rfl
    · rw [hq] at h
      exact absurd h Bool.false_ne_true

end CertificateChecks.KernelMisc.E7043

end
