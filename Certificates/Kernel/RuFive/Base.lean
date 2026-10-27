module

public import Certificates.Kernel.RuFive.KQ
public import Certificates.Kernel.Misc.RuInv.Proof
public import Certificates.Kernel.HeLoc.ChainFacts
public import CFSG.Certificates.Kernel.HeLoc.PTailSound
public import CFSG.Certificates.Kernel.HeLoc.TreeSound
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.J2HSound
public import CFSG.Certificates.Kernel.B3S3KSound
public import CFSG.Sporadic.Schreier.RuLocalFacts
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.Schreier.RuCheckOrbitsBase
public import CFSG.Sporadic.Schreier.RuRestrictBase

@[expose] public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelRuFive

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.HeLoc CFSG.KC.J2H
open CFSG.KC.B3S3K CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.HexFlat
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer
open CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Sporadic.RuSchreier CFSG.Sporadic.Schreier
open CFSG.Certificates CFSG.Certificates.Native

theorem sz : szOK 4060 12 = true := by decide +kernel

theorem eqA_self' (t : Array Nat) : eqA 4060 t t = true := CFSG.KS.Raw.eqA_self t

theorem unpackGet {p x : Nat} (hx : x < 4060) :
    (unpack 4060 12 p)[x]! = pg 12 (mask 12) p x := by
  rw [unpack, getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]

theorem repF_of_rep {p : Nat} {u : Equiv.Perm (Fin 4060)} (h : Rep 4060 (unpack 4060 12 p) u) :
    RepF 4060 (pg 12 (mask 12) p) u := fun x hx => by
  rw [← unpackGet hx]
  exact h ⟨x, hx⟩

theorem perm0 : ∀ j < 8, permB 4060 12 (S50.S j) = true := fun j hj =>
  permB_of_pp (pp_of_permOK sz (Orb.allN_iff.1 kPerm0 j hj))

theorem cs0_eq (j : Nat) (hj : j < 8) : ruCase0Arrs[j]! = unpack 4060 12 (S50.S j) := by
  have h := hexTable3_sound H50.all j hj
  rw [← H50.eq] at h
  rw [ruCase0Arrs, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  change hexTable3 4060 (4060 * j) ruCase0Hex = _
  rw [h, Nat.eq_of_beq_eq_true (Orb.allN_iff.1 kBind0 j hj)]

theorem hsize0 : ruCase0Arrs.size = 8 := by simp [ruCase0Arrs]

theorem binds0 : Binds 4060 12 S50.S 8 9 S50.BP ruCase0Arrs ruCase0BaseArr :=
  ⟨by norm_num, by norm_num, by norm_num, hsize0, cs0_eq, by decide,
    fun t ht => Nat.eq_of_beq_eq_true (Orb.allN_iff.1 kBase0 t ht)⟩

theorem arr0_0 : ruCase0Arrs[0]! = ruArr4060 0 := by
  rw [cs0_eq 0 (by norm_num), CertificateChecks.KernelMisc.RuInv.hA0, Nat.eq_of_beq_eq_true kGen00]

theorem arr0_1 : ruCase0Arrs[1]! = ruArr4060 1 := by
  rw [cs0_eq 1 (by norm_num), CertificateChecks.KernelMisc.RuInv.hA1, Nat.eq_of_beq_eq_true kGen01]

theorem words0 : ruCase0Words = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 8 derivs0 := by
  decide

theorem orb0 : rawOrbitSizes 4060 ruCase0Arrs ruCase0BaseArr = [4060, 1755, 1024, 4, 5, 1, 1, 1, 1] := by
  rw [rawOrbitSizesK_orb binds0 kPerm0 S50.ho (by norm_num)]
  have h : ∀ i < 9, rcnt (S50.LR i) = ([4060, 1755, 1024, 4, 5, 1, 1, 1, 1] : List Nat).getD i 0 :=
    fun i hi => Nat.eq_of_beq_eq_true (Orb.allN_iff.1 kOrb0 i hi)
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons,
    List.map_nil]
  rw [h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num), h 4 (by norm_num),
    h 5 (by norm_num), h 6 (by norm_num), h 7 (by norm_num), h 8 (by norm_num)]
  rfl

theorem cs1_eq (j : Nat) (hj : j < 10) : ruCase1Arrs[j]! = unpack 4060 12 (S51.S j) := by
  have h := hexTable3_sound H51.all j hj
  rw [← H51.eq] at h
  rw [ruCase1Arrs, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  change hexTable3 4060 (4060 * j) ruCase1Hex = _
  rw [h, Nat.eq_of_beq_eq_true (Orb.allN_iff.1 kBind1 j hj)]

theorem hsize1 : ruCase1Arrs.size = 10 := by simp [ruCase1Arrs]

theorem binds1 : Binds 4060 12 S51.S 10 5 S51.BP ruCase1Arrs ruCase1BaseArr :=
  ⟨by norm_num, by norm_num, by norm_num, hsize1, cs1_eq, by decide,
    fun t ht => Nat.eq_of_beq_eq_true (Orb.allN_iff.1 kBase1 t ht)⟩

theorem arr1_0 : ruCase1Arrs[0]! = ruArr4060 0 := by
  rw [cs1_eq 0 (by norm_num), CertificateChecks.KernelMisc.RuInv.hA0, Nat.eq_of_beq_eq_true kGen10]

theorem arr1_1 : ruCase1Arrs[1]! = ruArr4060 1 := by
  rw [cs1_eq 1 (by norm_num), CertificateChecks.KernelMisc.RuInv.hA1, Nat.eq_of_beq_eq_true kGen11]

theorem words1 : ruCase1Words = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 10 derivs1 := by
  decide

theorem orb1 : rawOrbitSizes 4060 ruCase1Arrs ruCase1BaseArr = [4060, 1755, 1024, 20, 1] := by
  rw [rawOrbitSizesK_orb binds1 kPerm1 S51.ho (by norm_num)]
  have h : ∀ i < 5, rcnt (S51.LR i) = ([4060, 1755, 1024, 20, 1] : List Nat).getD i 0 :=
    fun i hi => Nat.eq_of_beq_eq_true (Orb.allN_iff.1 kOrb1 i hi)
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons,
    List.map_nil]
  rw [h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num), h 4 (by norm_num)]
  rfl

theorem valid_a0 : validA 4060 (ruArr4060 0) = true := by
  rw [← arr0_0, cs0_eq 0 (by norm_num)]
  exact validA_of (perm0 0 (by norm_num))

theorem valid_a1 : validA 4060 (ruArr4060 1) = true := by
  rw [← arr0_1, cs0_eq 1 (by norm_num)]
  exact validA_of (perm0 1 (by norm_num))

theorem rep_ra0 : Rep 4060 (ruArr4060 0) ruA0 := rep_of_validA valid_a0

theorem rep_ra1 : Rep 4060 (ruArr4060 1) ruA1 := rep_of_validA valid_a1

section Ru

theorem closure_eq {S : Array (Array Nat)} (h0 : S[0]! = ruArr4060 0) (h1 : S[1]! = ruArr4060 1) :
    Subgroup.closure (Set.range fun j : Fin 2 => permOfArr 4060 S[j.val]!) = ruP := by
  rw [ruP]
  congr 1
  ext g
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, rfl⟩
    fin_cases j
    · exact Or.inl (by change permOfArr 4060 S[0]! = _; rw [h0]; rfl)
    · exact Or.inr (by change permOfArr 4060 S[1]! = _; rw [h1]; rfl)
  · rintro (rfl | rfl)
    · exact ⟨0, by change permOfArr 4060 S[0]! = _; rw [h0]; rfl⟩
    · exact ⟨1, by change permOfArr 4060 S[1]! = _; rw [h1]; rfl⟩

theorem chain0 : caseChainOK2 4060 ruCase0Arrs ruCase0BaseArr ruCase0Words (ruArr4060 0)
    (ruArr4060 1) = true := by
  have hcard : Nat.card (Subgroup.closure (Set.range fun j : Fin 2 =>
      permOfArr 4060 ruCase0Arrs[j.val]!)) ≤
      (rawOrbitSizes 4060 ruCase0Arrs ruCase0BaseArr).prod := by
    rw [orb0, closure_eq arr0_0 arr0_1, card_ruP]
    norm_num
  have hc := rawChainK_of_card_orb 1 binds0 S50.head S50.ho (by norm_num) hcard
  rw [← words0] at hc
  rw [caseChainOK2, hc, arr0_0, arr0_1, eqA_self', eqA_self']
  rfl

theorem chain1 : caseChainOK2 4060 ruCase1Arrs ruCase1BaseArr ruCase1Words (ruArr4060 0)
    (ruArr4060 1) = true := by
  have hcard : Nat.card (Subgroup.closure (Set.range fun j : Fin 2 =>
      permOfArr 4060 ruCase1Arrs[j.val]!)) ≤
      (rawOrbitSizes 4060 ruCase1Arrs ruCase1BaseArr).prod := by
    rw [orb1, closure_eq arr1_0 arr1_1, card_ruP]
    norm_num
  have hc := rawChainK_of_card_orb 1 binds1 S51.head S51.ho (by norm_num) hcard
  rw [← words1] at hc
  rw [caseChainOK2, hc, arr1_0, arr1_1, eqA_self', eqA_self']
  rfl

theorem chain0P : caseChainOK2P 4060 ruCase0Arrs ruCase0BaseArr ruCase0Words (ruArr4060 0)
    (ruArr4060 1) = true := chain0

theorem chain1P : caseChainOK2P 4060 ruCase1Arrs ruCase1BaseArr ruCase1Words (ruArr4060 0)
    (ruArr4060 1) = true := chain1

theorem hk2_0 : 2 ≤ ruCase0Arrs.size := by rw [hsize0]; norm_num

theorem hk2_1 : 2 ≤ ruCase1Arrs.size := by rw [hsize1]; norm_num

theorem hnd0 : ruCase0Base.Nodup := by decide

theorem hnd1 : ruCase1Base.Nodup := by decide

theorem orig0 : (RawSchreierDatum.ofArrays 4060 (by norm_num) ruCase0Arrs 2 hk2_0 ruCase0Base hnd0
    ruCase0Words).originalSubgroup = ruP := by
  obtain ⟨hc', e0, e1⟩ := caseChainOK2P_parts chain0P
  rw [originalSubgroup_ofArrays_twoP hc' rep_ra0 rep_ra1 e0 e1]
  rfl

theorem orig1 : (RawSchreierDatum.ofArrays 4060 (by norm_num) ruCase1Arrs 2 hk2_1 ruCase1Base hnd1
    ruCase1Words).originalSubgroup = ruP := by
  obtain ⟨hc', e0, e1⟩ := caseChainOK2P_parts chain1P
  rw [originalSubgroup_ofArrays_twoP hc' rep_ra0 rep_ra1 e0 e1]
  rfl

theorem arrays0 : ChainArrays (RawSchreierDatum.ofArrays 4060 (by norm_num) ruCase0Arrs 2 hk2_0
    ruCase0Base hnd0 ruCase0Words) (ruCase0Arrs.extract 0 2) ruCase0Arrs
    (ruCase0Base.map Fin.val).toArray ruCase0Words :=
  chainArrays_ofArrays (chainCheckFacts (caseChainOK2P_parts chain0P).1).strong_inv

theorem arrays1 : ChainArrays (RawSchreierDatum.ofArrays 4060 (by norm_num) ruCase1Arrs 2 hk2_1
    ruCase1Base hnd1 ruCase1Words) (ruCase1Arrs.extract 0 2) ruCase1Arrs
    (ruCase1Base.map Fin.val).toArray ruCase1Words :=
  chainArrays_ofArrays (chainCheckFacts (caseChainOK2P_parts chain1P).1).strong_inv

theorem sift0_iff {g : Array Nat} {G : Equiv.Perm (Fin 4060)} (hG : Rep 4060 g G) :
    siftA 4060 (rawLevels 4060 ruCase0Arrs ruCase0BaseArr) ruCase0BaseArr 0 g = true ↔ G ∈ ruP := by
  have h := siftA_iff_mem_originalSubgroup arrays0 (by norm_num) (caseChainOK2P_parts chain0P).1 hG
  rw [orig0] at h
  exact h

theorem sift1_iff {g : Array Nat} {G : Equiv.Perm (Fin 4060)} (hG : Rep 4060 g G) :
    siftA 4060 (rawLevels 4060 ruCase1Arrs ruCase1BaseArr) ruCase1BaseArr 0 g = true ↔ G ∈ ruP := by
  have h := siftA_iff_mem_originalSubgroup arrays1 (by norm_num) (caseChainOK2P_parts chain1P).1 hG
  rw [orig1] at h
  exact h

theorem faith0 : BaseFaithful ruP ruFiveKeys ∧
    ∀ j < ruCase0Arrs.size, permOfArr 4060 ruCase0Arrs[j]! ∈ ruP := by
  have hQ := (validSchreier_of_chainOK arrays0 (by norm_num) (caseChainOK2P_parts chain0P).1).1
  refine ⟨?_, fun j hj => ?_⟩
  · have h := baseFaithful_of_valid hQ
    rwa [orig0, RawSchreierDatum.ofArrays_base_toList] at h
  · have h := RawSchreierDatum.strong_get_mem_originalSubgroup _ hQ ⟨j, hj⟩
    rwa [RawSchreierDatum.ofArrays_strong_get, orig0] at h

theorem faith1 : ∀ j < ruCase1Arrs.size, permOfArr 4060 ruCase1Arrs[j]! ∈ ruP := by
  have hQ := (validSchreier_of_chainOK arrays1 (by norm_num) (caseChainOK2P_parts chain1P).1).1
  intro j hj
  have h := RawSchreierDatum.strong_get_mem_originalSubgroup _ hQ ⟨j, hj⟩
  rwa [RawSchreierDatum.ofArrays_strong_get, orig1] at h

theorem bs_lt : ∀ b ∈ bs, b < 4060 := by decide

theorem keys_lt : ∀ p ∈ ruFiveKeys, p < 4060 := by decide

theorem hF : ∀ x ∈ ruP, ∀ y ∈ ruP, (x ∈ ruP ↔ y ∈ ruP) →
    (∀ b (hb : b ∈ bs), (x ⟨b, bs_lt b hb⟩ : Nat) = y ⟨b, bs_lt b hb⟩) → x = y := by
  intro x hx y hy _ h
  have h1 := faith0.1 (y⁻¹ * x) (ruP.mul_mem (ruP.inv_mem hy) hx) fun z hz => by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
    exact Fin.ext (h z hz)
  exact (inv_mul_eq_one.1 h1).symm

theorem hmul : ∀ a ∈ ruP, ∀ b ∈ ruP, (a * b ∈ ruP ↔ (a ∈ ruP ↔ b ∈ ruP)) :=
  fun a ha b hb => iff_of_true (ruP.mul_mem ha hb) (iff_of_true ha hb)

end Ru

theorem arr_eq (k : Nat) (hk : k < 75) : ruFiveArr k = unpack 4060 12 (F k) := by
  have h := hexTable3_sound CertificateChecks.KernelMisc.RuFive.RG.all k hk
  rw [← CertificateChecks.KernelMisc.RuFive.RG.eq] at h
  rw [ruFiveArr]
  exact h

theorem perm_k (k : Nat) (hk : k < 75) :
    permOK 4060 12 (mask 12) (4060 * 12) (F k) (AI k) = true := Orb.allN_iff.1 kPermF k hk

@[expose] noncomputable def gp (k : Nat) : Equiv.Perm (Fin 4060) :=
  permOfArr 4060 (unpack 4060 12 (F k))

theorem rep_gp (k : Nat) (hk : k < 75) : Rep 4060 (unpack 4060 12 (F k)) (gp k) :=
  (rep_permOfArr (invEqK_sound (n := 4060) (w := 12) (p := F k) (r := AI k) (perm_k k hk)).2).1

theorem rep_gpi (k : Nat) (hk : k < 75) : Rep 4060 (unpack 4060 12 (AI k)) (gp k)⁻¹ :=
  (rep_permOfArr (invEqK_sound (n := 4060) (w := 12) (p := F k) (r := AI k) (perm_k k hk)).2).2

theorem repF_pa (k : Nat) (hk : k < 75) : RepF 4060 (pa k) (gp k) := repF_of_rep (rep_gp k hk)

theorem repF_pi (k : Nat) (hk : k < 75) : RepF 4060 (pi k) (gp k)⁻¹ := repF_of_rep (rep_gpi k hk)

theorem word_k (k : Nat) (hk : k < 75) :
    wordEqK 4060 12 (mask 12) (pidn 4060 12) S50.S S50.SI 8 (wd k) (F k) = true := by
  have hc : k / 20 < 4 := by omega
  have h : wordB (k / 20) = true := WB.all _ hc
  unfold wordB at h
  have h2 := Orb.allN_iff.1 h (k % 20) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul 20 (k / 20)) (k % 20) = k := Nat.div_add_mod k 20
  simp only [e] at h2
  rw [show Nat.blt k 75 = true from Nat.blt_eq.mpr hk] at h2
  exact h2

section Mem

theorem gp_mem (k : Nat) (hk : k < 75) : gp k ∈ ruP := by
  have hw := word_k k hk
  have hr := word_rep binds0 kPerm0 hw
  have e := CFSG.RankThree.Native.permOfArr_eq_of_rep hr
  rw [gp, e]
  exact sgnProd_mem (m := 8) (fun i hi => faith0.2 i (by rw [hsize0]; exact hi)) _
    (wordEqK_sound ⟨binds0.2.2.2.1, binds0.2.2.2.2.1⟩ kPerm0 hw).2

end Mem

end CertificateChecks.KernelRuFive

end
