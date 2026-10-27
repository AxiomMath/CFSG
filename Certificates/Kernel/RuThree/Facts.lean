module

public import Certificates.Kernel.RuThree.K
public import Certificates.Kernel.Misc.RuInv.Proof
public import Certificates.Kernel.HeLoc.ChainFacts
public import CFSG.Certificates.Kernel.HeLoc.PTailSound
public import CFSG.Certificates.Kernel.HeLoc.TreeSound
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.J2HSound
public import CFSG.Certificates.Kernel.B3S3KSound
public import CFSG.Sporadic.Schreier.RuLocalFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuThreeInputs
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.Schreier.RuCheckOrbitsBase
public import CFSG.Sporadic.Schreier.RuRestrictBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelRuThree

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.HeLoc CFSG.KC.J2H
open CFSG.KC.B3S3K CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.HexFlat
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer
open CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Sporadic.RuSchreier CFSG.Sporadic.Schreier
open CFSG.Certificates CFSG.Certificates.Native CFSG.EvenSporadicStandard.RuStd.S2

theorem sz : szOK 4060 12 = true := by decide +kernel

theorem hsize : ruThreeArrs.size = 11 := by
  unfold ruThreeArrs
  rw [Array.size_append, Array.size_ofFn]
  rfl

theorem arr0 : ruThreeArrs[0]! = ruArr4060 0 := by
  unfold ruThreeArrs
  rw [getElem!_pos _ 0 (by rw [Array.size_append, Array.size_ofFn]; decide),
    Array.getElem_append_left (by decide)]
  rfl

theorem arr1 : ruThreeArrs[1]! = ruArr4060 1 := by
  unfold ruThreeArrs
  rw [getElem!_pos _ 1 (by rw [Array.size_append, Array.size_ofFn]; decide),
    Array.getElem_append_left (by decide)]
  rfl

theorem arrk {k : Nat} (hk : k < 9) :
    ruThreeArrs[k + 2]! = hexTable3 4060 (4060 * k) ruThreeHex := by
  unfold ruThreeArrs
  rw [getElem!_pos _ (k + 2) (by rw [Array.size_append, Array.size_ofFn]; change k + 2 < 2 + 9; omega),
    Array.getElem_append_right (by change 2 ≤ k + 2; omega), Array.getElem_ofFn]
  simp only [List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add,
    Nat.reduceAdd, Nat.add_sub_cancel]

theorem perm0 : ∀ j < 11, permB 4060 12 (S3R.S j) = true := fun j hj =>
  permB_of_pp (pp_of_permOK sz (Orb.allN_iff.1 kPerm j hj))

theorem hA0' : ruArr4060 0 = unpack 4060 12 (S3R.S 0) := by
  rw [CertificateChecks.KernelMisc.RuInv.hA0, Nat.eq_of_beq_eq_true kGen0]

theorem hA1' : ruArr4060 1 = unpack 4060 12 (S3R.S 1) := by
  rw [CertificateChecks.KernelMisc.RuInv.hA1, Nat.eq_of_beq_eq_true kGen1]

theorem cs_eq (j : Nat) (hj : j < 11) : ruThreeArrs[j]! = unpack 4060 12 (S3R.S j) := by
  rcases (by omega : j = 0 ∨ j = 1 ∨ 2 ≤ j) with rfl | rfl | h2
  · rw [arr0, hA0']
  · rw [arr1, hA1']
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
    have hk : k < 9 := by omega
    have hb := Nat.eq_of_beq_eq_true (Orb.allN_iff.1 kBind k hk)
    have e2 : Nat.add 2 k = k + 2 := Nat.add_comm 2 k
    rw [arrk hk, R3.eq, hexTable3_sound R3.all k hk, hb, e2]

theorem binds : Binds 4060 12 S3R.S 11 7 S3R.BP ruThreeArrs ruThreeBaseArr :=
  ⟨by norm_num, by norm_num, by norm_num, hsize, cs_eq, by decide,
    fun t ht => Nat.eq_of_beq_eq_true (Orb.allN_iff.1 kBase t ht)⟩

theorem words : ruThreeWords = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 11 derivs := by
  decide

theorem orb : rawOrbitSizes 4060 ruThreeArrs ruThreeBaseArr = [4060, 2304, 650, 8, 3, 1, 1] := by
  rw [rawOrbitSizesK_orb binds kPerm S3R.ho (by norm_num)]
  have h : ∀ i < 7, rcnt (S3R.LR i) = ([4060, 2304, 650, 8, 3, 1, 1] : List Nat).getD i 0 :=
    fun i hi => Nat.eq_of_beq_eq_true (Orb.allN_iff.1 kOrb i hi)
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons,
    List.map_nil]
  rw [h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num), h 4 (by norm_num),
    h 5 (by norm_num), h 6 (by norm_num)]
  rfl

theorem valid0 : validA 4060 (ruArr4060 0) = true := by
  rw [hA0']
  exact validA_of (perm0 0 (by norm_num))

theorem valid1 : validA 4060 (ruArr4060 1) = true := by
  rw [hA1']
  exact validA_of (perm0 1 (by norm_num))

theorem eqA_self' (t : Array Nat) : eqA 4060 t t = true := CFSG.KS.Raw.eqA_self t

section Ru

theorem chain : caseChainOK2P 4060 ruThreeArrs ruThreeBaseArr ruThreeWords (ruArr4060 0)
    (ruArr4060 1) = true := by
  have hcard : Nat.card (Subgroup.closure (Set.range fun j : Fin 2 =>
      permOfArr 4060 ruThreeArrs[j.val]!)) ≤ (rawOrbitSizes 4060 ruThreeArrs ruThreeBaseArr).prod := by
    rw [orb]
    have e : Subgroup.closure (Set.range fun j : Fin 2 => permOfArr 4060 ruThreeArrs[j.val]!) =
        ruP := by
      rw [ruP]
      congr 1
      ext g
      simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨j, rfl⟩
        fin_cases j
        · exact Or.inl (by change permOfArr 4060 ruThreeArrs[0]! = _; rw [arr0]; rfl)
        · exact Or.inr (by change permOfArr 4060 ruThreeArrs[1]! = _; rw [arr1]; rfl)
      · rintro (rfl | rfl)
        · exact ⟨0, by change permOfArr 4060 ruThreeArrs[0]! = _; rw [arr0]; rfl⟩
        · exact ⟨1, by change permOfArr 4060 ruThreeArrs[1]! = _; rw [arr1]; rfl⟩
    rw [e, card_ruP]
    norm_num
  have hc := rawChainK_of_card_orb 1 binds S3R.head S3R.ho (by norm_num) hcard
  rw [← words] at hc
  rw [caseChainOK2P, hc, arr0, arr1, eqA_self', eqA_self']
  rfl

theorem rep_a0 : Rep 4060 (ruArr4060 0) ruA0 := rep_of_validA valid0

theorem rep_a1 : Rep 4060 (ruArr4060 1) ruA1 := rep_of_validA valid1

theorem hk2 : 2 ≤ ruThreeArrs.size := by rw [hsize]; norm_num

theorem hnd : ruThreeBase.Nodup := by decide

theorem orig : (RawSchreierDatum.ofArrays 4060 (by norm_num) ruThreeArrs 2 hk2 ruThreeBase hnd
    ruThreeWords).originalSubgroup = ruP := by
  obtain ⟨hc', e0, e1⟩ := caseChainOK2P_parts chain
  rw [originalSubgroup_ofArrays_twoP hc' rep_a0 rep_a1 e0 e1]
  rfl

theorem arrays : ChainArrays (RawSchreierDatum.ofArrays 4060 (by norm_num) ruThreeArrs 2 hk2
    ruThreeBase hnd ruThreeWords) (ruThreeArrs.extract 0 2) ruThreeArrs
    (ruThreeBase.map Fin.val).toArray ruThreeWords :=
  chainArrays_ofArrays (chainCheckFacts (caseChainOK2P_parts chain).1).strong_inv

theorem sift_iff {g : Array Nat} {G : Equiv.Perm (Fin 4060)} (hG : Rep 4060 g G) :
    siftA 4060 (rawLevels 4060 ruThreeArrs ruThreeBaseArr) ruThreeBaseArr 0 g = true ↔ G ∈ ruP := by
  have h := siftA_iff_mem_originalSubgroup arrays (by norm_num) (caseChainOK2P_parts chain).1 hG
  rw [orig] at h
  exact h

theorem faith : BaseFaithful ruP ruThreeKeys ∧
    ∀ j < ruThreeArrs.size, permOfArr 4060 ruThreeArrs[j]! ∈ ruP := by
  have hQ := (validSchreier_of_chainOK arrays (by norm_num) (caseChainOK2P_parts chain).1).1
  refine ⟨?_, fun j hj => ?_⟩
  · have h := baseFaithful_of_valid hQ
    rwa [orig, RawSchreierDatum.ofArrays_base_toList] at h
  · have h := RawSchreierDatum.strong_get_mem_originalSubgroup _ hQ ⟨j, hj⟩
    rwa [RawSchreierDatum.ofArrays_strong_get, orig] at h

theorem bs_lt : ∀ b ∈ bs, b < 4060 := by decide

theorem keys_lt : ∀ p ∈ ruThreeKeys, p < 4060 := by decide

theorem hF : ∀ x ∈ ruP, ∀ y ∈ ruP, (x ∈ ruP ↔ y ∈ ruP) →
    (∀ b (hb : b ∈ bs), (x ⟨b, bs_lt b hb⟩ : Nat) = y ⟨b, bs_lt b hb⟩) → x = y := by
  intro x hx y hy _ h
  have h1 := faith.1 (y⁻¹ * x) (ruP.mul_mem (ruP.inv_mem hy) hx) fun z hz => by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
    exact Fin.ext (h z hz)
  exact (inv_mul_eq_one.1 h1).symm

theorem hmul : ∀ a ∈ ruP, ∀ b ∈ ruP, (a * b ∈ ruP ↔ (a ∈ ruP ↔ b ∈ ruP)) :=
  fun a ha b hb => iff_of_true (ruP.mul_mem ha hb) (iff_of_true ha hb)

theorem word_k {k : Nat} (hk : k < 3) :
    wordEqK 4060 12 (mask 12) (pidn 4060 12) S3R.S S3R.SI 11 (cWords.getD k []) (CG k) = true ∧
      invEqK 4060 12 (mask 12) (4060 * 12) (CG k) (CGI k) = true :=
  (bAnd_iff _ _).1 (Orb.allN_iff.1 kWord k hk)

@[expose] noncomputable def gpC (k : Nat) : Equiv.Perm (Fin 4060) :=
  sgnProd (fun h => permOfArr 4060 ruThreeArrs[h]!) (cWords.getD k [])

theorem repC {k : Nat} (hk : k < 3) : Rep 4060 (unpack 4060 12 (CG k)) (gpC k) :=
  word_rep binds kPerm (word_k hk).1

theorem gens_eq {k : Nat} (hk : k < 3) : ruThreeC0Gens[k]! = unpack 4060 12 (CG k) := by
  have h := (wordEqK_sound ⟨binds.2.2.2.1, binds.2.2.2.2.1⟩ kPerm (word_k hk).1).1
  rw [← h]
  interval_cases k <;> rfl

theorem cgs : ∀ k < 3, Rep 4060 ruThreeC0Gens[k]! (gpC k) := fun k hk => by
  rw [gens_eq hk]
  exact repC hk

theorem unpackGet {p x : Nat} (hx : x < 4060) :
    (unpack 4060 12 p)[x]! = pg 12 (mask 12) p x := by
  rw [unpack, getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]

theorem cg : ∀ k < 3, RepF 4060 (gC k) (gpC k) := fun k hk x hx => by
  rw [← (repC hk) ⟨x, hx⟩, unpackGet hx]
  rfl

theorem cg_mem : ∀ k < 3, gpC k ∈ ruP := fun k hk =>
  sgnProd_mem (m := 11) (fun i hi => faith.2 i (by rw [hsize]; exact hi)) _
    (wordEqK_sound ⟨binds.2.2.2.1, binds.2.2.2.2.1⟩ kPerm (word_k hk).1).2

theorem ctree : TreeOK 3 2160 C0.P C0.L := treeOK_of fun i hi h0 => by
  have h := Orb.allN_iff.1 kTree i hi
  rwa [beq_zero_false h0] at h

theorem cedges : ∀ i < 2160, ∀ k < 3, CE i k < 2160 ∧
    treeArr 4060 ruThreeC0Gens C0.P C0.L (CE i k) =
      compA 4060 ruThreeC0Gens[k]! (treeArr 4060 ruThreeC0Gens C0.P C0.L i) :=
  edges_of_edgeAtK ctree cg cgs hmul cg_mem (fun k hk => iff_of_true (cg_mem k hk) rfl)
    (fun _ _ => by decide) bs_lt hF fun i hi => Orb.allN_iff.1 kEdge i hi

theorem ckeys_inj : ∀ a < 2160, ∀ b < 2160,
    keyA 4060 ruThreeKeys (treeArr 4060 ruThreeC0Gens C0.P C0.L a) =
      keyA 4060 ruThreeKeys (treeArr 4060 ruThreeC0Gens C0.P C0.L b) → a = b := by
  have hk := keys_inj_of_sortAtK (key := ckey) fun j hj => Orb.allN_iff.1 kSort j hj
  intro a ha b hb e
  rw [keyA_treeArr ctree cg cgs keys_lt ha, keyA_treeArr ctree cg cgs keys_lt hb] at e
  exact hk a ha b hb e

theorem cert_eq : ruThreeC0Cert = enumBfs 4060 ruThreeC0Gens ruThreeKeys 2180 := rfl

theorem gsize : ruThreeC0Gens.size = 3 := by
  unfold ruThreeC0Gens
  rfl

theorem c_pts : ruThreeC0Cert.pts =
    Array.ofFn (n := 2160) fun i => treeArr 4060 ruThreeC0Gens C0.P C0.L i.val := by
  rw [cert_eq]
  exact enumBfs_tree (ps := ruThreeKeys) (fuel := 2180) ctree cgs gsize (by norm_num) (by norm_num)
    ckeys_inj cedges kReplay

theorem c_enum : enumOK 4060 ruThreeC0Gens ruThreeKeys ruThreeC0Cert = true := by
  rw [cert_eq]
  exact enumOK_tree (ps := ruThreeKeys) (fuel := 2180) ctree cgs gsize (by norm_num) (by norm_num)
    ckeys_inj cedges

theorem c_size : ruThreeC0Cert.pts.size = 2160 := by rw [c_pts, Array.size_ofFn]

theorem c_get {k : Nat} (hk : k < 2160) :
    ruThreeC0Cert.pts[k]! = treeArr 4060 ruThreeC0Gens C0.P C0.L k := by
  rw [c_pts, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

theorem c_rep {k : Nat} (hk : k < 2160) :
    Rep 4060 ruThreeC0Cert.pts[k]! (treePerm gpC C0.P C0.L k) := by
  rw [c_get hk]
  exact rep_treeArr ctree cgs k hk

theorem c_mem {k : Nat} (hk : k < 2160) : treePerm gpC C0.P C0.L k ∈ ruP :=
  (trQ_spec ctree hmul cg_mem (fun k hk => iff_of_true (cg_mem k hk) rfl) (fun _ _ => by decide)
    2160 k hk.le hk).1

theorem lit0 (a b c : Array Nat) : (#[a, b, c] : Array (Array Nat))[0]! = a := rfl

theorem lines0 : ruThreeC0Gens[0]! = ruThreeLines[0]! := by
  unfold ruThreeC0Gens
  exact lit0 _ _ _

theorem x0_rep : Rep 4060 ruThreeLines[0]! (gpC 0) := by
  rw [← lines0]
  exact cgs 0 (by norm_num)

theorem x0_repF : RepF 4060 x0 (gpC 0) := cg 0 (by norm_num)

theorem x0_mem : gpC 0 ∈ ruP := cg_mem 0 (by norm_num)

theorem key_faith {a b : Array Nat} {A B : Equiv.Perm (Fin 4060)} (ha : Rep 4060 a A)
    (hb : Rep 4060 b B) (hA : A ∈ ruP) (hB : B ∈ ruP)
    (h : keyA 4060 ruThreeKeys a = keyA 4060 ruThreeKeys b) : A = B := by
  have hl := Nat.ofDigits_inj_of_len_eq (b := 4060) (by norm_num) (by simp)
    (fun l hl => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hl
      rw [ha.apply (keys_lt p hp)]
      exact (A _).2)
    (fun l hl => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hl
      rw [hb.apply (keys_lt p hp)]
      exact (B _).2) h
  have hpt : ∀ p (hp : p ∈ ruThreeKeys), (A ⟨p, keys_lt p hp⟩ : Nat) = B ⟨p, keys_lt p hp⟩ := by
    intro p hp
    have := List.map_inj_left.1 hl p hp
    rwa [ha.apply (keys_lt p hp), hb.apply (keys_lt p hp)] at this
  exact hF A hA B hB (iff_of_true hA hB) hpt

theorem sk_lt {SK SKI : Nat → Nat} {N : Nat}
    (h : ∀ j < N, SKI j < N ∧ SK (SKI j) = j) : ∀ j < N, SK j < N := by
  have hinj : Set.InjOn SKI (Finset.range N : Set Nat) := fun a ha b hb e => by
    rw [← (h a (by simpa using ha)).2, ← (h b (by simpa using hb)).2, e]
  have himg : (Finset.range N).image SKI = Finset.range N := Finset.eq_of_subset_of_card_le
    (fun y hy => by
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hy
      exact Finset.mem_range.2 (h a (by simpa using ha)).1)
    (by rw [Finset.card_image_of_injOn hinj])
  intro j hj
  have : j ∈ (Finset.range N).image SKI := by rw [himg]; simpa using hj
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 this
  rw [(h a (by simpa using ha)).2]
  simpa using ha

theorem csk_lt : ∀ j < 2160, C0.SK j < 2160 := sk_lt fun j hj => by
  have h := Orb.allN_iff.1 kSort j hj
  unfold sortAtK at h
  rw [bAnd_iff, bAnd_iff, Nat.blt_eq] at h
  exact ⟨h.1, Nat.eq_of_beq_eq_true h.2.1⟩

theorem any_mem {c : ArrCert} {t : Array Nat} {k : Nat}
    (hk : k < c.pts.size) (h : eqA 4060 t c.pts[k]! = true) : c.pts.toList.any (eqA 4060 t) = true := by
  rw [List.any_eq_true]
  refine ⟨c.pts[k]!, ?_, h⟩
  rw [getElem!_pos c.pts k hk]
  exact Array.getElem_mem_toList _

theorem base_lt : ∀ t < 7, ruThreeBaseArr[t]! < 4060 := by decide

theorem rels_ok : relsOKP 3 4060 ruThreeBaseArr ruThreeLines[0]! ruThreeRels = true := by
  rw [relsOKP, List.all_eq_true]
  intro r hr
  have h := List.all_eq_true.1 kRels r hr
  unfold relAt at h
  simp only [bAnd_iff, Nat.blt_eq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hs : ruThreeBaseArr.size = 7 := by decide
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, hs]
  refine ⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩
  rw [(rep_powArr x0_rep r.2.2).apply (base_lt _ h2), ← (RepF.powF x0_repF r.2.2) _ (base_lt _ h2)]
  exact Nat.eq_of_beq_eq_true h4

theorem tabs : TabsT 4060 12 11 7 S3R.BP T3R.NR T3R.NR S3R.S S3R.SI S3R.LR T3R.Ts T3R.LT T3R.PT
    T3R.QT 88 1024 4 1024 :=
  ⟨by decide, by decide, by decide, by decide, TS.all, LT.all, ptB_all, qtB_all⟩

theorem tc : TabChain 4060 12 11 7 S3R.BP 64 64 T3R.NR T3R.NR 88 1024 4 1024 S3R.S S3R.SI
    S3R.LR T3R.Ts T3R.LT T3R.PT T3R.QT ruThreeArrs ruThreeBaseArr ruThreeKeys :=
  ⟨binds, kPerm, S3R.ho, by norm_num, tabs, rfl⟩

theorem fr_ok : ∀ i < 7, fr i = 0 ∨ ∃ l e, fr i = 8 * l + e + 1 ∧ l < i ∧ e < 8 ∧
    (l, i, e) ∈ ruThreeRels := by
  intro i hi
  have h := Orb.allN_iff.1 kFR i hi
  by_cases h0 : fr i = 0
  · exact Or.inl h0
  · right
    rw [show Nat.beq (fr i) 0 = false from Bool.eq_false_iff.2 fun e => h0 (Nat.eq_of_beq_eq_true e)] at h
    simp only [bAnd_iff, Nat.blt_eq, List.any_eq_true] at h
    obtain ⟨h1, h2, r, hr, hr1, hr2, hr3⟩ := h
    refine ⟨(fr i - 1) / 8, (fr i - 1) % 8, by omega, h1, by omega, ?_⟩
    have e1 := Nat.eq_of_beq_eq_true hr1
    have e2 := Nat.eq_of_beq_eq_true hr2
    have e3 := Nat.eq_of_beq_eq_true hr3
    obtain ⟨a, b, c⟩ := r
    have e : (a, b, c) = ((fr i - 1) / 8, i, (fr i - 1) % 8) := by
      simp only [Prod.mk.injEq]
      exact ⟨e1, e2, e3⟩
    rw [← e]
    exact hr

theorem tail : ptailOK 4060 (rawLevels 4060 ruThreeArrs ruThreeBaseArr) ruThreeBaseArr
    ruThreeLines[0]! (powPA 3 4060 ruThreeLines[0]!) ruThreeRels ruThreeC0Cert.pts.toList 7 0
    (idA 4060) = true := by
  refine ptailOK_of_ptK_ tc x0_rep x0_repF (fun r hr => ?_) fr_ok keys_lt ?_ (by norm_num) kTail
  · have h := List.all_eq_true.1 kRels r hr
    unfold relAt at h
    rw [bAnd_iff, Nat.blt_eq] at h
    exact h.1
  · intro a A ha hA ⟨j, hj, e⟩
    have hR : A ∈ ruP := by
      refine (Subgroup.closure_le _).2 ?_ hA
      rintro _ ⟨i, rfl⟩
      exact faith.2 i (by rw [hsize]; exact i.2)
    have hm := csk_lt j hj
    unfold ckey cv at e
    rw [← keyA_treeArr ctree cg cgs keys_lt hm, ← c_get hm] at e
    have he := key_faith ha (c_rep hm) hR (c_mem hm) e
    exact any_mem (by rw [c_size]; exact hm) ((eqA_iff ha (c_rep hm)).2 he)

theorem eqOnL_rep {t u : Array Nat} {x y : Equiv.Perm (Fin 4060)} {f f' : Nat → Nat}
    (ht : Rep 4060 t x) (hu : Rep 4060 u y) (hf : RepF 4060 f x) (hf' : RepF 4060 f' y)
    (hx : x ∈ ruP) (hy : y ∈ ruP) (h : eqOnL bs f f' = true) : eqA 4060 t u = true :=
  (eqA_iff ht hu).2 (eq_of_eqOnL faith.1 hf hf' hx hy h)

theorem cent : centOKP 3 4060 ruThreeArrs ruThreeBaseArr ruThreeLines[0]! ruThreeRels ruThreeC0Gens
    ruThreeKeys ruThreeC0Cert 2160 = true := by
  simp only [centOKP, Bool.and_eq_true, beq_iff_eq, allLt_iff]
  have hs : ruThreeBaseArr.size = 7 := by decide
  refine ⟨⟨⟨⟨⟨rels_ok, c_enum⟩, c_size⟩, fun k hk => ?_⟩, fun k hk => ?_⟩, by rw [hs]; exact tail⟩
  · have hk3 : k < 3 := hk
    exact eqOnL_rep (rep_compA (cgs k hk3) x0_rep) (rep_compA x0_rep (cgs k hk3))
      ((cg k hk3).comp x0_repF) (x0_repF.comp (cg k hk3)) (ruP.mul_mem (cg_mem k hk3) x0_mem)
      (ruP.mul_mem x0_mem (cg_mem k hk3)) (Orb.allN_iff.1 kComm k hk3)
  · have hk3 : k < 3 := hk
    exact (sift_iff (cgs k hk3)).2 (cg_mem k hk3)

theorem inv_ok : ruThreeInvOK = true := by
  have h1 := kInv1
  have h2 := kInv2
  have h3 := kInv3
  have hv := cgs 1 (by norm_num)
  have hvf := cg 1 (by norm_num)
  have hvm := cg_mem 1 (by norm_num)
  unfold ruThreeInvOK
  have e1 : eqA 4060 ruThreeC0Gens[1]! (idA 4060) = false := by
    cases e : eqA 4060 ruThreeC0Gens[1]! (idA 4060)
    · rfl
    · have he := (eqA_iff hv rep_idA).1 e
      have := eqOnL_of_eq bs_lt hvf (he ▸ RepF.one)
      rw [this] at h1
      exact absurd h1 (by decide)
  have e2 : eqA 4060 (compA 4060 ruThreeC0Gens[1]! ruThreeC0Gens[1]!) (idA 4060) = true :=
    eqOnL_rep (rep_compA hv hv) rep_idA (hvf.comp hvf) RepF.one (ruP.mul_mem hvm hvm) ruP.one_mem h2
  have e3 : ((List.range 4060).any fun p => (ruThreeC0Gens[1]!)[p]! == p) = true := by
    rw [anyNP_eq, List.any_eq_true] at h3
    obtain ⟨p, hp, hpe⟩ := h3
    rw [List.mem_range] at hp
    rw [List.any_eq_true]
    refine ⟨p, List.mem_range.2 hp, ?_⟩
    rw [gens_eq (by norm_num), unpackGet hp]
    rw [beq_iff_eq]
    exact Nat.eq_of_beq_eq_true hpe
  rw [e1, e2, e3]
  rfl

open CFSG.EvenSporadicStandard.RuStd.S2 CFSG.RankThree.PartOne CFSG.RankThree.Native
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.RuSchreier in
open Certificates in
theorem ok24946 :
    caseChainOK2P 4060 ruThreeArrs ruThreeBaseArr ruThreeWords (ruArr4060 0) (ruArr4060 1) =
        true ∧
      rawOrbitSizes 4060 ruThreeArrs ruThreeBaseArr = [4060, 2304, 650, 8, 3, 1, 1] ∧
      validA 4060 (ruArr4060 0) = true ∧ validA 4060 (ruArr4060 1) = true ∧
      centOKP 3 4060 ruThreeArrs ruThreeBaseArr ruThreeLines[0]! ruThreeRels ruThreeC0Gens
        ruThreeKeys ruThreeC0Cert 2160 = true ∧
      eqA 4060 ruThreeC0Gens[0]! ruThreeLines[0]! = true ∧
      ruThreeInvOK = true :=
  ⟨chain, orb, valid0, valid1, cent, by rw [lines0]; exact eqA_self' _, inv_ok⟩

end Ru

end CertificateChecks.KernelRuThree

end
