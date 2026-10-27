module

public import Certificates.Kernel.LocalComp.Co1Cen2BW
public import Certificates.Kernel.Co1B.Prim2045
public import CFSG.Certificates.Kernel.LocalCompCo1PWSound
public import CFSG.Sporadic.Co1Block.TwoBD
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1Cen2BTests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1Cen2BData
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1EndData

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.Co1Cen2B

open CFSG.KS.Raw CFSG.KS.SporSch.M24 CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block
open CFSG.ComponentClassification.RankTwoSporadic.Co1 CertificateChecks.KernelSporSch.Co1Packed
open CFSG.KC.Co1End CFSG.KC.Co1PW CFSG.KC.Co1T CertificateChecks.KernelCo1B
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.KC.Enum CFSG.KC.Pack CFSG.Certificates.Native
open CFSG.KS.Prim (compEqK neIdK invEqK compEqK_sound neIdK_sound invEqK_sound)
open CFSG.KS (mask)

@[expose] noncomputable def powK (X e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) idM (fun _ acc => mulK acc X) e

theorem powK_unpack (X : Nat) : ∀ e, pow (unpack 24 24 X) e = unpack 24 24 (powK X e)
  | 0 => MatL.unpack_idM.symm
  | e + 1 => by
    change mul (pow (unpack 24 24 X) e) (unpack 24 24 X) = unpack 24 24 (mulK (powK X e) X)
    rw [powK_unpack X e, MatL.unpack_mulK]

theorem kE : Nat.beq (powK (mulK (Cent2045.D2.M 19) (Cent2045.D2.M 21)) 13) TA.E = true := by
  quickRfl

theorem kH : dagK H.M H.MI 2 H.N co1Cen2BH = true := by quickRfl

theorem kH0 : (Nat.beq (H.M 0) (Cent2045.D2.M 19) && Nat.beq (H.M 1) (Cent2045.D2.M 21) &&
    Nat.beq H.N 4) = true := by quickRfl

theorem kC : dagK C.M C.MI 2 C.N co1Cen2BC = true := by quickRfl

theorem kC0 : (Nat.beq (C.M 0) PA && Nat.beq (C.M 1) PB && Nat.beq C.N 9) = true := by quickRfl

theorem kZ : Nat.beq (mulK (mulK (H.M 2) (H.M 3)) (mulK (H.MI 2) (H.MI 3))) TA.Z = true := by
  quickRfl

theorem kInv : (eqK (mulK (H.M 2) (H.MI 2)) idM && eqK (mulK (H.M 3) (H.MI 3)) idM) = true := by
  quickRfl

theorem kT : (Nat.beq (CFSG.KC.Co1F2.trK 24 TA.E) TA.T1 && Nat.beq (CFSG.KC.Co1F2.trK 24 TA.Z) TA.T2 &&
    Nat.beq (CFSG.KC.Co1F2.trK 24 (C.M 8)) TA.T3) = true := by quickRfl

theorem kPZ2 : compEqK 1365 11 (mask 11) (1365 * 11) TA.PZ TA.PZ TA.PZ2 = true := by quickRfl

theorem kNZ2 : neIdK 1365 11 (mask 11) (1365 * 11) (pidn 1365 11) TA.PZ2 = true := by quickRfl

theorem kPC : invEqK 1365 11 (mask 11) (1365 * 11) TA.PC TA.PCI = true := by quickRfl

theorem kSC : signK 1365 11 (mask 11) TA.PC TA.SW TA.SK = true := by quickRfl

theorem kKC : Nat.beq (Nat.mod TA.SK 2) 1 = true := by quickRfl

theorem kMoved : ∀ p ∈ [1, 5, 83], ∃ j < 4, Prim2045.stp j p ≠ p := by decide +kernel

theorem e2_eq : co1E2R = unpack 24 24 TA.E := by
  unfold co1E2R
  rw [Tri2045.rx_eq, Tri2045.ry_eq, ← MatL.unpack_mulK, powK_unpack, Nat.eq_of_beq_eq_true kE]

theorem h0 : H.M 0 = Cent2045.D2.M 19 ∧ H.M 1 = Cent2045.D2.M 21 ∧ H.N = 4 := by
  have h := kH0
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem c0 : C.M 0 = PA ∧ C.M 1 = PB ∧ C.N = 9 := by
  have h := kC0
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem h_eq : dag [twoBXYRows.1, twoBXYRows.2] (co1Cen2BH.map decWord) =
    (rowsOf H.M H.N, rowsOf H.MI H.N, true) := by
  refine dagK_sound ?_ kH
  rw [Tri2045.rx_eq, Tri2045.ry_eq, ← h0.1, ← h0.2.1]
  rfl

theorem c_eq : dag [aR, bR] (co1Cen2BC.map decWord) = (rowsOf C.M C.N, rowsOf C.MI C.N, true) := by
  refine dagK_sound ?_ kC
  rw [aR_u, bR_u, ← c0.1, ← c0.2.1]
  rfl

theorem eU : entryR (rowsOf H.M H.N) 3 = unpack 24 24 (H.M 2) := entryR_rows (by quickRfl)

theorem eV : entryR (rowsOf H.M H.N) 4 = unpack 24 24 (H.M 3) := entryR_rows (by quickRfl)

theorem eC : entryR (rowsOf C.M C.N) 9 = unpack 24 24 (C.M 8) := entryR_rows (by quickRfl)

theorem z_eq : commRows (unpack 24 24 (H.M 2)) (unpack 24 24 (H.M 3)) = unpack 24 24 TA.Z := by
  unfold commRows
  rw [inv_of_dagK kH (k := 2) (by rw [h0.2.2]; norm_num),
    inv_of_dagK kH (k := 3) (by rw [h0.2.2]; norm_num), ← MatL.unpack_mulK, ← MatL.unpack_mulK,
    ← MatL.unpack_mulK, Nat.eq_of_beq_eq_true kZ]

theorem invs_ok : invsOK (rowsOf H.M H.N) [3, 4] = true := by
  unfold invsOK
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [eU, eV, inv_of_dagK kH (k := 2) (by rw [h0.2.2]; norm_num),
    inv_of_dagK kH (k := 3) (by rw [h0.2.2]; norm_num), ← MatL.unpack_mulK, ← MatL.unpack_mulK,
    ← MatL.unpack_idM, beq_unpack, beq_unpack]
  exact kInv

theorem okA : Native.triOK (Native.triTable twoBTris) twoBTris (unpack 24 24 PA) = true ∧
    Native.triPerm (Native.triTable twoBTris) twoBTris (unpack 24 24 PA) =
      unpack 1365 11 (pidn 1365 11) :=
  Tri2045.triOK_of Tri2045.kTA' (slices_all (f := triOneK (Tri2045.TB.T 12) Tri2045.TB.PT
    (pidn 1365 11)) (L := 128) (NS := 11) WA.all (by norm_num))

theorem tr_eq : CFSG.KC.Co1F2.trK 24 TA.E = TA.T1 ∧ CFSG.KC.Co1F2.trK 24 TA.Z = TA.T2 ∧
    CFSG.KC.Co1F2.trK 24 (C.M 8) = TA.T3 := by
  have h := kT
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem okE : Native.triOK (Native.triTable twoBTris) twoBTris (unpack 24 24 TA.E) = true ∧
    Native.triPerm (Native.triTable twoBTris) twoBTris (unpack 24 24 TA.E) =
      unpack 1365 11 (pidn 1365 11) :=
  Tri2045.triOK_of tr_eq.1 (slices_all (f := triOneK TA.T1 Tri2045.TB.PT (pidn 1365 11))
    (L := 128) (NS := 11) WE.all (by norm_num))

theorem okZ : Native.triOK (Native.triTable twoBTris) twoBTris (unpack 24 24 TA.Z) = true ∧
    Native.triPerm (Native.triTable twoBTris) twoBTris (unpack 24 24 TA.Z) =
      unpack 1365 11 TA.PZ :=
  Tri2045.triOK_of tr_eq.2.1 (slices_all (f := triOneK TA.T2 Tri2045.TB.PT TA.PZ) (L := 128)
    (NS := 11) WZ.all (by norm_num))

theorem okC : Native.triOK (Native.triTable twoBTris) twoBTris (unpack 24 24 (C.M 8)) = true ∧
    Native.triPerm (Native.triTable twoBTris) twoBTris (unpack 24 24 (C.M 8)) =
      unpack 1365 11 TA.PC :=
  Tri2045.triOK_of tr_eq.2.2 (slices_all (f := triOneK TA.T3 Tri2045.TB.PT TA.PC) (L := 128)
    (NS := 11) WC.all (by norm_num))

theorem sign_strong {j P T k : Nat} (hj : j < 6) (hP : Nat.beq (Tri2045.RO.S j) P = true)
    (hs : signK 1365 11 (mask 11) P T k = true) (hk : Nat.beq (Nat.mod k 2) 0 = true) :
    Equiv.Perm.sign (permOfArr 1365 twoBStrong[j]!) = 1 := by
  have hr := Tri2045.strong_rep (j := j) hj
  rw [Tri2045.strong_facts.2 j hj, Nat.eq_of_beq_eq_true hP] at hr ⊢
  rw [Tri2045.sign_rep hr hs]
  exact Even.neg_one_pow (Nat.even_iff.2 (Nat.eq_of_beq_eq_true hk))

theorem not_sift :
    siftA 1365 (rawLevels 1365 twoBStrong twoBChainBase.toArray) twoBChainBase.toArray 0
      (unpack 1365 11 TA.PC) = false := by
  have hP := invEqK_sound kPC
  have hG := (rep_permOfArr hP.2).1
  have hsign : Equiv.Perm.sign (permOfArr 1365 (unpack 1365 11 TA.PC)) = -1 := by
    rw [Tri2045.sign_rep hG kSC]
    exact Odd.neg_one_pow (Nat.odd_iff.2 (Nat.eq_of_beq_eq_true kKC))
  cases h : siftA 1365 (rawLevels 1365 twoBStrong twoBChainBase.toArray) twoBChainBase.toArray 0
      (unpack 1365 11 TA.PC) with
  | false => rfl
  | true =>
    exfalso
    rw [← twoB_baseArr] at h
    have hmem := (CFSG.Sporadic.Schreier.Tits.siftA_iff_mem_ofArrays (hn := by norm_num)
      (hk := twoBStrong_two_le) (hb := twoB_nodup) twoB_allPerms (by norm_num : 0 < 4)
      twoB_chainOK hG).1 h
    rw [CFSG.Sporadic.Schreier.Tits.originalSubgroup_ofArrays] at hmem
    have hle : Subgroup.closure (Set.range fun i : Fin 2 => permOfArr 1365 twoBStrong[(i : ℕ)]!) ≤
        alternatingGroup (Fin 1365) := by
      rw [Subgroup.closure_le]
      rintro g ⟨⟨i, hi⟩, rfl⟩
      refine Equiv.Perm.mem_alternatingGroup.2 ?_
      interval_cases i
      · exact sign_strong (by norm_num) Tri2045.kS0 Tri2045.kSX Tri2045.kKX
      · exact sign_strong (by norm_num) Tri2045.kS1 Tri2045.kSY Tri2045.kKY
    have := Equiv.Perm.mem_alternatingGroup.1 (hle hmem)
    rw [hsign] at this
    exact absurd this (by decide)

theorem tri_ok :
    co1Cen2BTriOK (Native.triTable twoBTris) twoBTris (unpack 24 24 PA) (unpack 24 24 TA.E)
      (unpack 24 24 TA.Z) (unpack 24 24 (C.M 8)) (rawLevels 1365 twoBStrong twoBChainBase.toArray)
      twoBChainBase.toArray = true := by
  unfold co1Cen2BTriOK
  rw [okA.1, okA.2, okE.1, okE.2, okZ.1, okZ.2, okC.1, okC.2, compEqK_sound kPZ2,
    neIdK_sound kNZ2, not_sift, Tri2045.idA_eq, Tri2045.eqA_refl]
  rfl

theorem moved_ok : co1Cen2BMovedOK twoBHSteps = true := by
  unfold co1Cen2BMovedOK
  rw [List.all_eq_true]
  intro p hp
  obtain ⟨j, hj, hne⟩ := kMoved p hp
  have hp' : p < 1365 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    omega
  rw [Array.any_eq_true]
  refine ⟨j, by rw [Prim2045.hst.1]; exact hj, ?_⟩
  rw [← getElem!_pos twoBHSteps j (by rw [Prim2045.hst.1]; exact hj), Prim2045.hst.2 j hj p hp']
  simpa using hne

theorem check :
    co1Cen2BCheck co1Cen2BH co1Cen2BUV co1Cen2BC co1Cen2BIC = true := by
  unfold co1Cen2BCheck
  rw [h_eq, c_eq]
  simp only [co1Cen2BUV, co1Cen2BIC]
  rw [eU, eV, eC, z_eq, e2_eq, Tri2045.rx_eq, Tri2045.ry_eq, aR_u, tri_ok, moved_ok, invs_ok,
    powK_unpack, ← MatL.unpack_idM, ← MatL.unpack_mulK, ← MatL.unpack_mulK]
  simp only [validRows_unpack, beq_unpack, commR_unpack, bne]
  quickRfl

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoSporadic.Co1 in
open Certificates in
theorem cert15045 : co1Cen2BCheck co1Cen2BH co1Cen2BUV co1Cen2BC co1Cen2BIC = true := check

end CertificateChecks.KernelLC.Co1Cen2B

end
