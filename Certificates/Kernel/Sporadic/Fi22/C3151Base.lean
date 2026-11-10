
module

public import Certificates.Kernel.Sporadic.Fi22.C3151ABase
public import Certificates.Kernel.Sporadic.Fi22.F3151S0
public import Certificates.Kernel.Sporadic.Fi22.F3151S1
public import Certificates.Kernel.Sporadic.Fi22.F3151S2
public import Certificates.Kernel.Sporadic.Fi22.F3151S3
public import CFSG.Certificates.Kernel.Spor.LevelTrSound
public import CFSG.Certificates.Kernel.Spor.TextSound
public import CFSG.Monster.B.Fischer.Fi22CoverCheckInputs
import Mathlib.Tactic.NormNum

@[expose] public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelSpor.Fi22F2.scanAll CertificateChecks.KernelSpor.Fi22F2.scanSl 256

namespace CertificateChecks.KernelSpor.Fi22C3151

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.Text
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Fischer CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Fi22F2
open CertificateChecks.KernelSpor.Fi22LabA (unpack_get' strictB_eq' offs_parts out6_eq rep_facts
  countP_range_rec)
open CertificateChecks.KernelSpor.Fi22LabX (fixK)

theorem scanOK : ScanOK := fun I hI => by
  have h := allN_spec (scanAll (I / 512) (by change I / 512 < 256; omega)) (I % 512) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul (I / 512) 512) (I % 512) = I := by
    rw [Nat.add_eq, Nat.mul_eq]
    omega
  rwa [e] at h

theorem arr_eq {L : Nat} (hL : L < 151) : fi22OuterArr3510 L = unpack 3510 12 (Fi22OutT.L L) := by
  have h := hexBind_sound Fi22OutT.all L hL
  rw [Nat.zero_add, ← Fi22OutT.eq] at h
  exact h

theorem u_eq {j : Nat} (hj : j < 54) : (fi22OuterStrong3510 7)[j]! = unpack 3510 12 (U j) := by
  have hl : fi22OuterLine3510 7 j = 39 + j := by
    unfold fi22OuterLine3510
    simp [fi22OuterLines3510]
  unfold fi22OuterStrong3510
  rw [getElem!_pos _ j (by simpa [fi22OuterLines3510] using hj), Array.getElem_ofFn]
  change fi22OuterArr3510 (fi22OuterLine3510 7 j) = _
  rw [hl, arr_eq (by omega)]
  rfl

theorem h_eq {j : Nat} (hj : j < 54) : (fi22OuterStrong3510 8)[j]! = unpack 3510 12 (H j) := by
  have hl : fi22OuterLine3510 8 j = 93 + j := by
    unfold fi22OuterLine3510
    simp [fi22OuterLines3510]
  unfold fi22OuterStrong3510
  rw [getElem!_pos _ j (by simpa [fi22OuterLines3510] using hj), Array.getElem_ofFn]
  change fi22OuterArr3510 (fi22OuterLine3510 8 j) = _
  rw [hl, arr_eq (by omega)]
  rfl

theorem size7 : (fi22OuterStrong3510 7).size = 54 := by
  simp [fi22OuterStrong3510, fi22OuterLines3510]

theorem size4 : (fi22OuterStrong3510 4).size = 13 := by
  simp [fi22OuterStrong3510, fi22OuterLines3510]

theorem lev_size : fi22TLevels.size = 6 := by
  simp [fi22TLevels, rawLevels]

theorem lev_pts : fi22TLevels[0]!.pts.size = 1024 ∧ fi22TLevels[1]!.pts.size = 32 ∧
    fi22TLevels[2]!.pts.size = 4 := by
  obtain ⟨-, -, -, c0, c1, c2⟩ := offs_parts
  refine ⟨?_, ?_, ?_⟩
  · rw [← c0]
    exact (levelTr_sound Fi22X.bindsT Fi22TC.head Fi22TC.hl (i := 0) (by norm_num)).1
  · rw [← c1]
    exact (levelTr_sound Fi22X.bindsT Fi22TC.head Fi22TC.hl (i := 1) (by norm_num)).1
  · rw [← c2]
    exact (levelTr_sound Fi22X.bindsT Fi22TC.head Fi22TC.hl (i := 2) (by norm_num)).1

theorem inR_iff {x : Nat × Nat × Nat} :
    CS3.InR fi22TLevels x ↔ x.1 < 1024 ∧ x.2.1 < 32 ∧ x.2.2 < 4 := by
  rw [CS3.InR, lev_pts.1, lev_pts.2.1, lev_pts.2.2]

theorem sz_eq : CS3.sz fi22TLevels = 131072 := by
  rw [CS3.sz, lev_pts.1, lev_pts.2.1, lev_pts.2.2]

theorem idx_xN {I : Nat} (hI : I < 131072) : idx3 fi22TLevels (xN I) = I := by
  unfold idx3 xN
  rw [lev_pts.2.1, lev_pts.2.2]
  simp only
  omega

theorem dec_eq (I : Nat) : CS3.dec fi22TLevels I = xN I := by
  unfold CS3.dec xN
  rw [lev_pts.2.1, lev_pts.2.2]

theorem lvOK : Dec.LvOK 3510 fi22TLevels (#[0, 1, 2, 3, 6, 4] : Array Nat).toList :=
  Dec.lvOK_rawLevels Fi22X.bindsT Fi22X.permT fun t ht => by interval_cases t <;> decide

def toF (x : Nat × Nat × Nat) : Fin 1024 × Fin 32 × Fin 4 :=
  (⟨x.1 % 1024, Nat.mod_lt _ (by norm_num)⟩, ⟨x.2.1 % 32, Nat.mod_lt _ (by norm_num)⟩,
    ⟨x.2.2 % 4, Nat.mod_lt _ (by norm_num)⟩)

theorem toF_val {x : Nat × Nat × Nat} (h : CS3.InR fi22TLevels x) :
    ((toF x).1.val, (toF x).2.1.val, (toF x).2.2.val) = x := by
  rw [inR_iff] at h
  obtain ⟨a, b, c⟩ := x
  unfold toF
  simp only [Prod.mk.injEq] at h ⊢
  omega

theorem toF_xN {I : Nat} (h : I < 131072) : toF (xN I) = xF I := by
  simp [toF, xN, xF]

noncomputable def gT (k : Nat) : Equiv.Perm (Fin 3510) := permOfArr 3510 (fi22OuterStrong3510 4)[k]!

theorem gens_get {k : Nat} (hk : k < 9) :
    ((fi22OuterStrong3510 4).extract 0 9)[k]! = (fi22OuterStrong3510 4)[k]! := by
  rw [getElem!_pos _ k (by simp [size4]; omega), getElem!_pos _ k (by rw [size4]; omega)]
  simp

theorem ginv_get {k : Nat} (hk : k < 9) :
    (((fi22OuterStrong3510 4).extract 0 9).map (invCand 3510))[k]! =
      invCand 3510 (fi22OuterStrong3510 4)[k]! := by
  rw [getElem!_pos _ k (by simp [size4]; omega), Array.getElem_map, ← getElem!_pos _ k
    (by simp [size4]; omega), gens_get hk]

theorem gT_mem {k : Nat} (hk : k < 9) : gT k ∈ fi22OuterT := by
  rw [fi22OuterT, RawSchreierDatum.originalSubgroup]
  refine Subgroup.subset_closure ?_
  rw [Set.mem_ofPred_eq, fi22OuterChainT, RawSchreierDatum.mem_ofArrays_original]
  exact ⟨k, hk, rfl⟩

theorem root_parts {j : Nat} (hj : j < 54) : RT j < 131072 ∧ PPf (RT j) < 3263 ∧
    ∀ p < 3510, pg 12 (mask 12) (U j) p = gI (RT j) p := by
  have h := allN_spec (rootAll (j / 6) (by change j / 6 < 9; omega)) (j % 6) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul (j / 6) 6) (j % 6) = j := by
    rw [Nat.add_eq, Nat.mul_eq]
    omega
  rw [e] at h
  unfold rootRow at h
  rw [strictB_eq'] at h
  obtain ⟨a, b, c⟩ := by simpa only [bAnd_iff] using h
  exact ⟨blt_t a, blt_t b, fun p hp => Nat.eq_of_beq_eq_true (allN_spec c p hp)⟩

theorem inR_xN {I : Nat} (h : I < 131072) : CS3.InR fi22TLevels (xN I) := by
  rw [inR_iff]
  unfold xN
  simp only
  omega

theorem tp_parts : (∀ k < 256, R k < 3510 ∧ Qf (R k) = k) ∧
    (∀ p < 3510, Qf p < 256 → R (Qf p) = p) ∧
    ∀ s < 9, ∀ p < 3510, (Qf p < 256 ↔ Qf (pg 12 (mask 12) (Fi22X.TS s) p) < 256) := by
  have htp : tpK = true := tpOK
  unfold tpK at htp
  obtain ⟨a, b, c⟩ := by simpa only [bAnd_iff] using htp
  refine ⟨fun k hk => ?_, fun p hp hq => ?_, fun s hs p hp => ?_⟩
  · obtain ⟨a1, a2⟩ := (bAnd_iff _ _).1 (allN_spec a k hk)
    exact ⟨blt_t a1, Nat.eq_of_beq_eq_true a2⟩
  · exact Nat.eq_of_beq_eq_true (bIf_true (allN_spec b p hp) (t_blt hq))
  · have h := allN_spec (allN_spec c s hs) p hp
    rw [strictB_eq'] at h
    by_cases hq : Qf p < 256
    · exact ⟨fun _ => blt_t (bIf_true h (t_blt hq)), fun _ => hq⟩
    · have hq' : Nat.blt (Qf p) 256 = false := by
        cases e : Nat.blt (Qf p) 256
        · rfl
        · exact absurd (blt_t e) hq
      have h' := bIf_false h hq'
      refine ⟨fun h1 => absurd h1 hq, fun h2 => ?_⟩
      rw [t_blt h2] at h'
      exact absurd h' (by decide)

theorem tp_eq : fi22OuterTPointsNat = (List.range 256).map R := by
  have h := CFSG.KC.Misc.HexFlat.hexTable3_sound Fi22OTP.all 0 (by norm_num)
  rw [← Fi22OTP.eq, Nat.mul_zero] at h
  unfold fi22OuterTPointsNat hex3List
  refine List.map_congr_left fun k hk => ?_
  have hk' := List.mem_range.1 hk
  have e : (hexTable3 256 0 fi22OuterTPointsHex)[k]! =
      CFSG.Monster.B.Max2.Native.hexAt fi22OuterTPointsHex.toUTF8 (3 * k) 3 := by
    simp [hexTable3, hk']
  rw [← e, h, unpack_get' hk']
  rfl

theorem mem_tp {p : Nat} (hp : p < 3510) : p ∈ fi22OuterTPointsNat ↔ Qf p < 256 := by
  obtain ⟨a, b, -⟩ := tp_parts
  rw [tp_eq, List.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [(a k (List.mem_range.1 hk)).2]
    exact List.mem_range.1 hk
  · intro hq
    exact ⟨Qf p, List.mem_range.2 hq, b p hp hq⟩

theorem tp_nodup : fi22OuterTPointsNat.Nodup := by
  obtain ⟨a, -, -⟩ := tp_parts
  rw [tp_eq]
  refine List.Nodup.map_on (fun x hx y hy e => ?_) List.nodup_range
  rw [← (a x (List.mem_range.1 hx)).2, e, (a y (List.mem_range.1 hy)).2]

theorem tp_inv : ∀ k < 9, ∀ p < 3510, fi22OuterTPointsNat.contains p =
    fi22OuterTPointsNat.contains ((fi22OuterStrong3510 4)[k]!)[p]! := by
  intro k hk p hp
  obtain ⟨-, -, c⟩ := tp_parts
  rw [Fi22X.outT_eq (by omega), unpack_get' hp]
  have hq : pg 12 (mask 12) (Fi22X.TS k) p < 3510 :=
    Fi22LabA.cn_lt (allN_spec Fi22X.cnT k (by omega)) p hp
  rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem, mem_tp hp, mem_tp hq]
  exact c k hk p hp

theorem tp_moves : ∀ x : Fin 1024 × Fin 32 × Fin 4, x ≠ (0, 0, 0) →
    moves3 fi22TLevels fi22TPointsArr x.1 x.2.1 x.2.2 = true := by
  intro x hx
  obtain ⟨a, -, -⟩ := tp_parts
  have hl := iX_lt x
  have h0 : iX x ≠ 0 := fun e => hx (by
    have := x.1.2
    have := x.2.1.2
    have := x.2.2.2
    unfold iX at e
    ext <;> simp only [Fin.val_zero] <;> omega)
  have hm := (scan_parts (scanOK _ hl)).2.2 h0
  have e : xN (iX x) = (x.1.val, x.2.1.val, x.2.2.val) := by rw [← xF_val hl, xF_iX]
  simp only [xN, Prod.mk.injEq] at e
  rw [e.1, e.2.1, e.2.2] at hm
  have hsz : fi22TPointsArr.size = 256 := by simp [fi22TPointsArr, tp_eq]
  have hget : ∀ k < 256, fi22TPointsArr[k]! = R k := fun k hk => by
    rw [fi22TPointsArr, tp_eq, List.getElem!_toArray, getElem!_pos _ k (by simpa using hk),
      List.getElem_map, List.getElem_range]
  unfold moves3
  unfold movB at hm
  rw [hsz]
  cases e1 : allLt 256 (fun k => tr3 fi22TLevels x.1 x.2.1 x.2.2 fi22TPointsArr[k]! == fi22TPointsArr[k]!)
  · rfl
  · exfalso
    have hall : allN 256 (fun k => Nat.beq (g3 x.1 x.2.1 x.2.2 (R k)) (R k)) = true :=
      allN_of_forall fun k hk => by
        have := allLt_iff.1 e1 k hk
        rw [beq_iff_eq, hget k hk, ← g3_eq x.1.2 x.2.1.2 x.2.2.2 (a k hk).1] at this
        rw [this]
        exact Nat.beq_refl _
    rw [hall] at hm
    exact absurd hm (by decide)

theorem h_parts {j : Nat} (hj : j < 54) : Fi22X.cn (H j) = true ∧ Fi22X.siftP (H j) = true ∧
    Fi22X.cn (U j) = true ∧ ∃ i < 3, Nat.beq (Fi22X.c (H j) (U j)) (Fi22X.c (Fi22LabX.O6 i) (H j)) =
      true := by
  have h := allN_spec (hAll (j / 6) (by change j / 6 < 9; omega)) (j % 6) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul (j / 6) 6) (j % 6) = j := by
    rw [Nat.add_eq, Nat.mul_eq]
    omega
  rw [e] at h
  unfold hRow at h
  obtain ⟨a, b, c, d⟩ := by simpa only [bAnd_iff] using h
  rw [strictB_eq'] at d
  refine ⟨a, b, c, ?_⟩
  cases e0 : Nat.beq (Fi22X.c (H j) (U j)) (Fi22X.c (Fi22LabX.O6 0) (H j))
  · cases e1 : Nat.beq (Fi22X.c (H j) (U j)) (Fi22X.c (Fi22LabX.O6 1) (H j))
    · exact ⟨2, by norm_num, bIf_false (bIf_false d e0) e1⟩
    · exact ⟨1, by norm_num, e1⟩
  · exact ⟨0, by norm_num, e0⟩

theorem x_facts : ∀ i < 3, siftA 3510 (rawLevels 3510 fi22StrongArrs fi22BaseArr) fi22BaseArr 0
      (fi22OuterStrong3510 6)[i]! = true ∧
    eqA 3510 (fi22OuterStrong3510 6)[i]! (idA 3510) = false ∧
    eqA 3510 (compA 3510 (fi22OuterStrong3510 6)[i]! (fi22OuterStrong3510 6)[i]!)
      (idA 3510) = true := by
  intro i hi
  obtain ⟨h6, -, hinv, -, -, -, -, -, -, hP, -⟩ := rep_facts
  obtain ⟨a, b⟩ := hinv i (by omega)
  have e : (fi22OuterStrong3510 6)[i]! = unpack 3510 12 (Fi22ExtT.L (21 + i)) := by
    rw [out6_eq hi, h6 i hi]
  rw [e]
  exact ⟨Fi22C3150.siftA_of rfl (hP i hi).1 (hP i hi).2, neIdK_sound a, sqIdK_sound b⟩

theorem card_fix (P : Nat) :
    (Finset.univ.filter fun p : Fin 3510 => (unpack 3510 12 P)[p.val]! = p.val).card = fixK P := by
  have e : (Finset.univ.filter fun p : Fin 3510 => (unpack 3510 12 P)[p.val]! = p.val) =
      Finset.univ.filter fun p : Fin 3510 => Nat.beq (pg 12 (mask 12) P p.val) p.val = true :=
    Finset.filter_congr fun p _ => by
      rw [unpack_get' p.2]
      exact ⟨fun h => by rw [h]; exact Nat.beq_refl _, Nat.eq_of_beq_eq_true⟩
  rw [e, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  unfold fixK
  exact (CFSG.Sporadic.FischerOddCore.card_fin_subtype_eq_countP 3510
    (fun i => Nat.beq (pg 12 (mask 12) P i) i)).trans
      (countP_range_rec (f := fun i => Nat.beq (pg 12 (mask 12) P i) i)
        (g := fun i => Nat.beq (pg 12 (mask 12) P i) i) 3510 fun _ _ => rfl)

theorem fix_counts :
    (Finset.univ.filter fun p : Fin 3510 => ((fi22OuterStrong3510 6)[0]!)[p.val]! = p.val).card =
      54 ∧
    (Finset.univ.filter fun p : Fin 3510 => ((fi22OuterStrong3510 6)[1]!)[p.val]! = p.val).card =
      182 ∧
    (Finset.univ.filter fun p : Fin 3510 => ((fi22OuterStrong3510 6)[2]!)[p.val]! = p.val).card =
      694 := by
  obtain ⟨h6, -, -, f1, f2, f3, -, -, -, -, -⟩ := rep_facts
  refine ⟨?_, ?_, ?_⟩
  · rw [out6_eq (by norm_num), ← h6 0 (by norm_num), card_fix]
    exact f1
  · rw [out6_eq (by norm_num), ← h6 1 (by norm_num), card_fix]
    exact f2
  · rw [out6_eq (by norm_num), ← h6 2 (by norm_num), card_fix]
    exact f3

theorem x3_eq : eqA 3510 (fi22OuterStrong3510 6)[2]! (fi22OuterStrong3510 1)[0]! = true := by
  obtain ⟨h6, -, -, -, -, -, -, -, -, hP, -⟩ := rep_facts
  obtain ⟨a, b⟩ := by simpa only [bAnd_iff] using zE
  have cO : Fi22X.cn (Fi22LabX.O6 2) = true := by
    rw [← h6 2 (by norm_num)]
    exact (hP 2 (by norm_num)).1
  rw [out6_eq (by norm_num), Fi22E2073.outE]
  exact Fi22X.eqA_of cO b a

end CertificateChecks.KernelSpor.Fi22C3151

end
