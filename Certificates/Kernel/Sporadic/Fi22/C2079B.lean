module

public import Certificates.Kernel.Sporadic.Fi22.C2079A
public import CFSG.Certificates.Kernel.Spor.SiftBKProof
public import CFSG.Certificates.Kernel.Spor.ConjTreeSound
public import CFSG.Sporadic.FischerOddCore.Fi22CentOrder
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fo22C

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.ConjTree
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore CertificateChecks.KernelSpor

theorem bindsH (htext : fi22Cent3510Text = Fi22E2065.textP) {c st kS BP : Nat}
    {PS : Nat → Nat} (hc : c < 5) (hst : fi22CentStrongStart.getD c 0 = st)
    (hcnt : fi22CentStrongCount.getD c 0 = kS) (hline : st + kS ≤ 306)
    (hbind : Fi22C2066.bindK PS kS st = true) (hbase : Fi22C2066.baseK BP = true) :
    Binds 3510 12 PS kS 6 BP (fi22CentStrong c) #[0, 1, 2, 3, 6, 4] := by
  refine ⟨by norm_num, by norm_num, by norm_num, by rw [fi22CentStrong, Array.size_ofFn, hcnt],
    fun j hj => ?_, rfl, fun t ht => Nat.eq_of_beq_eq_true (allN_spec hbase t ht)⟩
  rw [fi22CentStrong_get hc (by rw [hcnt]; exact hj), fi22CentArr, fi22CentBytes, htext, hst,
    Fi22E2065.cent_eq (by omega), Nat.eq_of_beq_eq_true (allN_spec hbind j hj)]
  rfl

theorem bindsH2 (htext : fi22Cent3510Text = Fi22E2065.textP) :
    Binds 3510 12 Fi22H2.S 9 6 Fi22H2.BP (fi22CentStrong 2) #[0, 1, 2, 3, 6, 4] :=
  bindsH htext (st := 35) (by norm_num) rfl rfl (by norm_num) Fi22C2066.b2 Fi22C2066.p2
theorem bindsH3 (htext : fi22Cent3510Text = Fi22E2065.textP) :
    Binds 3510 12 Fi22H3.S 19 6 Fi22H3.BP (fi22CentStrong 3) #[0, 1, 2, 3, 6, 4] :=
  bindsH htext (st := 44) (by norm_num) rfl rfl (by norm_num) Fi22C2066.b3 Fi22C2066.p3
theorem bindsH4 (htext : fi22Cent3510Text = Fi22E2065.textP) :
    Binds 3510 12 Fi22H4.S 16 6 Fi22H4.BP (fi22CentStrong 4) #[0, 1, 2, 3, 6, 4] :=
  bindsH htext (st := 63) (by norm_num) rfl rfl (by norm_num) Fi22C2066.b4 Fi22C2066.p4

theorem strong_le_H {c : Nat} (hc : c < 5) :
    Subgroup.closure {g : Equiv.Perm (Fin 3510) |
      ∃ j < (fi22CentStrong c).size, permOfArr 3510 (fi22CentStrong c)[j]! = g} ≤ fi22H c := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨j, hj, rfl⟩
  have h := RawSchreierDatum.strong_get_mem_originalSubgroup _ (fi22HChain_valid hc) ⟨j, hj⟩
  have e : (fi22HChain c).strong.get ⟨j, hj⟩ = permOfArr 3510 (fi22CentStrong c)[j]! :=
    RawSchreierDatum.ofArrays_strong_get (n := 3510) ⟨j, hj⟩
  rwa [e] at h

theorem mem_H
    {c kS kO BP : Nat} {PS PSI LR ST : Nat → Nat} {D : List (List Int)} (hc : c < 5)
    (hb : Binds 3510 12 PS kS 6 BP (fi22CentStrong c) #[0, 1, 2, 3, 6, 4])
    (hh : headK 3510 12 (mask 12) (3510 * 12) (pidn 3510 12) PS PSI kS kO D 6 BP = true)
    (ht : TreeOK 3510 12 PS PSI LR kS 6 BP) (hst : StepsOK 3510 12 PS ST kS 6 BP)
    {q : Nat} {G : Equiv.Perm (Fin 3510)} (hq : Rep 3510 (unpack 3510 12 q) G) (hG : G ∈ fi22P)
    (hs : siftBK 3510 12 (mask 12) (3510 * 12) 6 PS PSI LR ST kS 6 0
      (baseImK 12 (mask 12) 6 q BP) = true) : G ∈ fi22H c := by
  have hsz : (fi22CentStrong c).size = kS := hb.2.2.2.1
  refine strong_le_H hc (siftBK_mem hb hh ht hst (X := fi22P) (fun j hj => ?_)
    (fun G hG hfix => Fi22C2066.fi22P_sep hG hfix) hq hG hs)
  exact ((fi22H_le hc) (strong_le_H hc (Subgroup.subset_closure ⟨j, hsz ▸ hj, rfl⟩))).1

theorem ct_of_sl {N NS CH : Nat} {f : Nat → Bool} (hN : N ≤ NS * CH)
    (hs : ∀ s < NS, allN CH (fun d => strictB (Nat.add (s * CH) d) (fun i =>
      bIf(Nat.blt i N, f i, true))) = true) : ∀ i < N, f i = true := by
  intro i hi
  obtain ⟨hCH, hsk, e⟩ := slice_cover hN hi
  have h1 := allN_spec (hs (i / CH) hsk) (i % CH) (Nat.mod_lt _ hCH)
  rw [strictB_eq, e] at h1
  exact bIf_of_true (Nat.blt_eq ▸ hi) h1

theorem getElem_extract9 {a : Array (Array Nat)} {j : Nat} (hj : j < 9) (ha : 9 ≤ a.size) :
    (a.extract 0 9)[j]! = a[j]! := by
  rw [getElem!_pos _ j (by simp; omega), getElem!_pos a j (by omega), Array.getElem_extract]
  simp

@[expose] noncomputable def datum (S : Array (Array Nat)) (k : Nat) (hk : k ≤ S.size)
    (base : List (Fin 3510)) (hb : base.Nodup) (W : Array (List Int)) : RawSchreierDatum 3510 :=
  RawSchreierDatum.ofArrays 3510 (by norm_num) S k hk base hb W

theorem datum_arrays {S : Array (Array Nat)} {k : Nat} {hk : k ≤ S.size} {base : List (Fin 3510)}
    {hb : base.Nodup} {W : Array (List Int)} {baseArr : Array Nat}
    (hB : (base.map Fin.val).toArray = baseArr) (h : rawChainOK 3510 (S.extract 0 k) S baseArr W 4 = true) :
    ChainArrays (datum S k hk base hb W) (S.extract 0 k) S baseArr W := by
  have hA := chainArrays_ofArrays (n := 3510) (hn := by norm_num) (k := k) (hk := hk) (base := base)
    (hb := hb) (W := W) (chainCheckFacts (hB ▸ h)).strong_inv
  rw [hB] at hA
  exact hA

theorem siftA_of_closure {S : Array (Array Nat)} {k : Nat} (hk : k ≤ S.size)
    {base : List (Fin 3510)} (hb : base.Nodup) {W : Array (List Int)} {baseArr : Array Nat}
    (hB : (base.map Fin.val).toArray = baseArr) (h : rawChainOK 3510 (S.extract 0 k) S baseArr W 4 = true)
    {g : Array Nat} {G : Equiv.Perm (Fin 3510)} (hg : Rep 3510 g G)
    (hG : G ∈ Subgroup.closure {x : Equiv.Perm (Fin 3510) | ∃ j < S.size, permOfArr 3510 S[j]! = x}) :
    siftA 3510 (rawLevels 3510 S baseArr) baseArr 0 g = true := by
  have hA := datum_arrays (hk := hk) (hb := hb) hB h
  have hv := (validSchreier_of_chainOK hA (by norm_num) h).1
  refine (siftA_iff_mem_originalSubgroup hA (by norm_num) h hg).2 ((Subgroup.closure_le _).2 ?_ hG)
  rintro _ ⟨j, hj, rfl⟩
  have hm := RawSchreierDatum.strong_get_mem_originalSubgroup _ hv ⟨j, hj⟩
  have e : (datum S k hk base hb W).strong.get ⟨j, hj⟩ = permOfArr 3510 S[j]! :=
    RawSchreierDatum.ofArrays_strong_get (n := 3510) ⟨j, hj⟩
  rwa [e] at hm

theorem inNormalOK_of {S : Array (Array Nat)} {base : Array Nat} {Sh hgens : Array (Array Nat)}
    (h0 : siftA 3510 (rawLevels 3510 Sh fo22HBase) fo22HBase 0 S[0]! = true)
    (h1 : siftA 3510 (rawLevels 3510 Sh fo22HBase) fo22HBase 0 S[1]! = true)
    (hc : ∀ j < hgens.size, siftA 3510 (rawLevels 3510 S base) base 0 (conjA 3510 hgens[j]! S[0]!) =
      true ∧ siftA 3510 (rawLevels 3510 S base) base 0 (conjA 3510 hgens[j]! S[1]!) = true) :
    fo22InNormalOK S base Sh hgens = true := by
  unfold fo22InNormalOK
  simp only [Bool.and_eq_true]
  refine ⟨⟨h0, h1⟩, allLt_iff.2 fun j hj => ?_⟩
  simp only [Bool.and_eq_true]
  exact hc j hj

theorem rep_conj {g x : Array Nat} {G X : Equiv.Perm (Fin 3510)} (hg : Rep 3510 g G)
    (hgi : isInvA 3510 g (invCand 3510 g) = true) (hx : Rep 3510 x X) :
    Rep 3510 (conjA 3510 g x) (G * (X * G⁻¹)) :=
  rep_compA hg (rep_compA hx (rep_inv_of_isInvA hg hgi))

theorem hcnH3 : ∀ j < 19, Fi22X.cn (Fi22H3.S j) = true :=
  allN_spec ((bAnd_iff (allN 19 (fun j => Fi22X.cn (Fi22H3.S j)))
    (allN 19 (fun j => Fi22X.siftP (Fi22H3.S j)))).1 Fi22C2066.s3).1
theorem hcnH4 : ∀ j < 16, Fi22X.cn (Fi22H4.S j) = true :=
  allN_spec ((bAnd_iff (allN 16 (fun j => Fi22X.cn (Fi22H4.S j)))
    (allN 16 (fun j => Fi22X.siftP (Fi22H4.S j)))).1 Fi22C2066.s4).1

theorem inNormal3
    (htext : fi22Cent3510Text = Fi22E2065.textP) :
    fo22InNormalOK fo22N3Strong #[9, 0, 1, 2] (fi22CentStrong 3)
      ((fi22CentStrong 3).extract 0 9) = true := by
  rw [n3S]
  have hbH := bindsH3 htext
  have hN : ∀ i < 7, Rep 3510 SN3[i]! (permOfArr 3510 SN3[i]!) ∧
      isInvA 3510 SN3[i]! (invCand 3510 SN3[i]!) = true ∧ permOfArr 3510 SN3[i]! ∈ fi22P := by
    intro i hi
    obtain ⟨h1, -, h3⟩ := by simpa only [bAnd_iff] using allN_spec Fo22M.cnN3 i hi
    rw [ofFn_get hi]
    exact ⟨(rep_of_perm h3).1, (rep_of_perm h3).2, mem_P h1 (allN_spec Fo22M.pN3 i hi) h3⟩
  have hH : ∀ i < 2, siftA 3510 (rawLevels 3510 (fi22CentStrong 3) fo22HBase) fo22HBase 0 SN3[i]! =
      true := by
    intro i hi
    obtain ⟨hr, -, hp⟩ := hN i (by omega)
    refine (siftA_iff_mem_fi22H (c := 3) (by norm_num) hr).2 ?_
    have e : SN3[i]! = unpack 3510 12 (Fo22N3.S i) := ofFn_get (by omega)
    have hr' : Rep 3510 (unpack 3510 12 (Fo22N3.S i)) (permOfArr 3510 SN3[i]!) := fun x => by
      rw [← e]
      exact hr x
    have hs : siftBK 3510 12 (mask 12) (3510 * 12) 6 Fi22H3.S Fi22H3.SI Fi22H3.LR Fi22H3.ST 19 6 0
        (baseImK 12 (mask 12) 6 (Fo22N3.S i) Fi22H3.BP) = true := allN_spec Fo22M.hN3 i hi
    exact mem_H (by norm_num) hbH Fi22H3.head Fi22H3.tl Fi22H3.hst hr' hp hs
  have hC : ∀ j < 9, ∀ i < 2, siftA 3510 (rawLevels 3510 SN3 #[9, 0, 1, 2]) #[9, 0, 1, 2] 0
      (conjA 3510 ((fi22CentStrong 3).extract 0 9)[j]! SN3[i]!) = true := by
    intro j hj i hi
    obtain ⟨hr, -, hp⟩ := hN i (by omega)
    have hj' := allN_spec Fo22M.cnH3 j hj
    obtain ⟨hcsi, hperm⟩ := (bAnd_iff (Fi22X.cn (Fi22H3.SI j))
      (permOK 3510 12 (mask 12) (3510 * 12) (Fi22H3.S j) (Fi22H3.SI j))).1 hj'
    have hcs := hcnH3 j (by omega)
    obtain ⟨hci, -, -⟩ := by simpa only [bAnd_iff] using allN_spec Fo22M.cnN3 i (by omega)
    have hgj : ((fi22CentStrong 3).extract 0 9)[j]! = unpack 3510 12 (Fi22H3.S j) := by
      rw [getElem_extract9 hj (by rw [hbH.2.2.2.1]; norm_num), hbH.2.2.2.2.1 j (by omega)]
    have hrg := rep_of_perm hperm
    have hconj : Rep 3510 (conjA 3510 ((fi22CentStrong 3).extract 0 9)[j]! SN3[i]!)
        (permOfArr 3510 (unpack 3510 12 (Fi22H3.S j)) * (permOfArr 3510 SN3[i]! *
          (permOfArr 3510 (unpack 3510 12 (Fi22H3.S j)))⁻¹)) := by
      rw [hgj]
      exact rep_conj hrg.1 hrg.2 hr
    have he : conjA 3510 ((fi22CentStrong 3).extract 0 9)[j]! SN3[i]! =
        unpack 3510 12 (pconj 3510 12 (Fi22H3.S j) (Fo22N3.S i) (Fi22H3.SI j)) := by
      rw [hgj, ofFn_get (by omega), conj_unpack hcs hci hcsi hperm]
    have hconj' : Rep 3510 (unpack 3510 12 (pconj 3510 12 (Fi22H3.S j) (Fo22N3.S i) (Fi22H3.SI j)))
        (permOfArr 3510 (unpack 3510 12 (Fi22H3.S j)) * (permOfArr 3510 SN3[i]! *
          (permOfArr 3510 (unpack 3510 12 (Fi22H3.S j)))⁻¹)) := by
      rw [← he]
      exact hconj
    refine siftA_of_closure (by simp) (base := finL [9, 0, 1, 2]) (by decide) rfl chainN3 hconj ?_
    have hgH : permOfArr 3510 (unpack 3510 12 (Fi22H3.S j)) ∈ fi22P := by
      have := strong_le_H (c := 3) (by norm_num) (Subgroup.subset_closure
        ⟨j, by rw [hbH.2.2.2.1]; omega, rfl⟩)
      rw [hbH.2.2.2.2.1 j (by omega)] at this
      exact ((fi22H_le (c := 3) (by norm_num)) this).1
    have hs : siftBK 3510 12 (mask 12) (3510 * 12) 7 Fo22N3x.S Fo22N3x.SI Fo22N3x.LR Fo22N3x.ST 7 7 0
        (baseImK 12 (mask 12) 7 (pconj 3510 12 (Fi22H3.S j) (Fo22N3.S i) (Fi22H3.SI j))
          Fo22N3x.BP) = true := allN_spec (allN_spec Fo22M.cN3 j hj) i hi
    refine siftBK_mem bindsN3x Fo22N3x.head Fo22N3x.tl Fo22N3x.hst (X := fi22P)
      (fun k hk => (hN k hk).2.2) (fun _ hG hfix => sepP7 hG hfix) hconj' ?_ hs
    exact fi22P.mul_mem hgH (fi22P.mul_mem hp (fi22P.inv_mem hgH))
  have hsz : ((fi22CentStrong 3).extract 0 9).size = 9 := by
    rw [Array.size_extract, hbH.2.2.2.1]
    rfl
  exact inNormalOK_of (hH 0 (by norm_num)) (hH 1 (by norm_num)) fun j hj =>
    ⟨hC j (hsz ▸ hj) 0 (by norm_num), hC j (hsz ▸ hj) 1 (by norm_num)⟩

theorem inNormal4
    (htext : fi22Cent3510Text = Fi22E2065.textP) :
    fo22InNormalOK fo22N4Strong #[0, 1, 2] (fi22CentStrong 4)
      ((fi22CentStrong 4).extract 0 9) = true := by
  rw [n4S]
  have hbH := bindsH4 htext
  have hN : ∀ i < 7, Rep 3510 SN4[i]! (permOfArr 3510 SN4[i]!) ∧
      isInvA 3510 SN4[i]! (invCand 3510 SN4[i]!) = true ∧ permOfArr 3510 SN4[i]! ∈ fi22P := by
    intro i hi
    obtain ⟨h1, -, h3⟩ := by simpa only [bAnd_iff] using allN_spec Fo22M.cnN4 i hi
    rw [ofFn_get hi]
    exact ⟨(rep_of_perm h3).1, (rep_of_perm h3).2, mem_P h1 (allN_spec Fo22M.pN4 i hi) h3⟩
  have hH : ∀ i < 2, siftA 3510 (rawLevels 3510 (fi22CentStrong 4) fo22HBase) fo22HBase 0 SN4[i]! =
      true := by
    intro i hi
    obtain ⟨hr, -, hp⟩ := hN i (by omega)
    refine (siftA_iff_mem_fi22H (c := 4) (by norm_num) hr).2 ?_
    have e : SN4[i]! = unpack 3510 12 (Fo22N4.S i) := ofFn_get (by omega)
    have hr' : Rep 3510 (unpack 3510 12 (Fo22N4.S i)) (permOfArr 3510 SN4[i]!) := fun x => by
      rw [← e]
      exact hr x
    have hs : siftBK 3510 12 (mask 12) (3510 * 12) 6 Fi22H4.S Fi22H4.SI Fi22H4.LR Fi22H4.ST 16 6 0
        (baseImK 12 (mask 12) 6 (Fo22N4.S i) Fi22H4.BP) = true := allN_spec Fo22M.hN4 i hi
    exact mem_H (by norm_num) hbH Fi22H4.head Fi22H4.tl Fi22H4.hst hr' hp hs
  have hC : ∀ j < 9, ∀ i < 2, siftA 3510 (rawLevels 3510 SN4 #[0, 1, 2]) #[0, 1, 2] 0
      (conjA 3510 ((fi22CentStrong 4).extract 0 9)[j]! SN4[i]!) = true := by
    intro j hj i hi
    obtain ⟨hr, -, hp⟩ := hN i (by omega)
    have hj' := allN_spec Fo22M.cnH4 j hj
    obtain ⟨hcsi, hperm⟩ := (bAnd_iff (Fi22X.cn (Fi22H4.SI j))
      (permOK 3510 12 (mask 12) (3510 * 12) (Fi22H4.S j) (Fi22H4.SI j))).1 hj'
    have hcs := hcnH4 j (by omega)
    obtain ⟨hci, -, -⟩ := by simpa only [bAnd_iff] using allN_spec Fo22M.cnN4 i (by omega)
    have hgj : ((fi22CentStrong 4).extract 0 9)[j]! = unpack 3510 12 (Fi22H4.S j) := by
      rw [getElem_extract9 hj (by rw [hbH.2.2.2.1]; norm_num), hbH.2.2.2.2.1 j (by omega)]
    have hrg := rep_of_perm hperm
    have hconj : Rep 3510 (conjA 3510 ((fi22CentStrong 4).extract 0 9)[j]! SN4[i]!)
        (permOfArr 3510 (unpack 3510 12 (Fi22H4.S j)) * (permOfArr 3510 SN4[i]! *
          (permOfArr 3510 (unpack 3510 12 (Fi22H4.S j)))⁻¹)) := by
      rw [hgj]
      exact rep_conj hrg.1 hrg.2 hr
    have he : conjA 3510 ((fi22CentStrong 4).extract 0 9)[j]! SN4[i]! =
        unpack 3510 12 (pconj 3510 12 (Fi22H4.S j) (Fo22N4.S i) (Fi22H4.SI j)) := by
      rw [hgj, ofFn_get (by omega), conj_unpack hcs hci hcsi hperm]
    have hconj' : Rep 3510 (unpack 3510 12 (pconj 3510 12 (Fi22H4.S j) (Fo22N4.S i) (Fi22H4.SI j)))
        (permOfArr 3510 (unpack 3510 12 (Fi22H4.S j)) * (permOfArr 3510 SN4[i]! *
          (permOfArr 3510 (unpack 3510 12 (Fi22H4.S j)))⁻¹)) := by
      rw [← he]
      exact hconj
    refine siftA_of_closure (by simp) (base := finL [0, 1, 2]) (by decide) rfl chainN4 hconj ?_
    have hgH : permOfArr 3510 (unpack 3510 12 (Fi22H4.S j)) ∈ fi22P := by
      have := strong_le_H (c := 4) (by norm_num) (Subgroup.subset_closure
        ⟨j, by rw [hbH.2.2.2.1]; omega, rfl⟩)
      rw [hbH.2.2.2.2.1 j (by omega)] at this
      exact ((fi22H_le (c := 4) (by norm_num)) this).1
    have hs : siftBK 3510 12 (mask 12) (3510 * 12) 6 Fo22N4x.S Fo22N4x.SI Fo22N4x.LR Fo22N4x.ST 7 6 0
        (baseImK 12 (mask 12) 6 (pconj 3510 12 (Fi22H4.S j) (Fo22N4.S i) (Fi22H4.SI j))
          Fo22N4x.BP) = true := allN_spec (allN_spec Fo22M.cN4 j hj) i hi
    refine siftBK_mem bindsN4x Fo22N4x.head Fo22N4x.tl Fo22N4x.hst (X := fi22P)
      (fun k hk => (hN k hk).2.2) (fun _ hG hfix => Fi22C2066.fi22P_sep hG hfix) hconj' ?_ hs
    exact fi22P.mul_mem hgH (fi22P.mul_mem hp (fi22P.inv_mem hgH))
  have hsz : ((fi22CentStrong 4).extract 0 9).size = 9 := by
    rw [Array.size_extract, hbH.2.2.2.1]
    rfl
  exact inNormalOK_of (hH 0 (by norm_num)) (hH 1 (by norm_num)) fun j hj =>
    ⟨hC j (hsz ▸ hj) 0 (by norm_num), hC j (hsz ▸ hj) 1 (by norm_num)⟩

end CertificateChecks.KernelSpor.Fo22C

end
