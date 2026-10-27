module

public import CFSG.RankThree.Native.HSMcLAuxData
public import CFSG.Sporadic.Schreier.PairHSCert
public import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.RankThree.Native.HSMcLSmallCheckInputs
public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.Misc.PairCountSound
public import CFSG.Certificates.Kernel.Misc.PermClosSound
public import CFSG.Monster.B.Co2.PermArr
import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.Harness
meta import CFSG.RankThree.Native.HSMcLSmallCheckInputs
meta import CFSG.RankThree.Native.HSMcLAuxData
meta import CFSG.Sporadic.Schreier.PairHSCertInputs
meta import CFSG.Sporadic.Schreier.PairMcLCertInputs
meta import CFSG.Sporadic.SmallOddCore.McLData

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.HSMcL

@[expose] def d1 : List (List Int) := CFSG.RankThree.Native.hs100Words.toList.drop 2

@[expose] def d2 : List (List Int) := CFSG.RankThree.Native.hs100RWords.toList.drop 3

@[expose] def d3 : List (List Int) := CFSG.RankThree.Native.mcl275RWords.toList.drop 3

end CertificateChecks.KernelMisc.HSMcL

end

#ks_chars CertificateChecks.KernelMisc.HSMcL.HX CFSG.RankThree.Native.hs100Hex
#kmisc_hexflat CertificateChecks.KernelMisc.HSMcL.HX CFSG.RankThree.Native.hs100Hex 3 100 7 16
#ks_chars CertificateChecks.KernelMisc.HSMcL.RX CFSG.RankThree.Native.hs100RHex
#kmisc_hexflat CertificateChecks.KernelMisc.HSMcL.RX CFSG.RankThree.Native.hs100RHex 3 100 7 17
#ks_chars CertificateChecks.KernelMisc.HSMcL.MX CFSG.RankThree.Native.mcl275RHex
#kmisc_hexflat CertificateChecks.KernelMisc.HSMcL.MX CFSG.RankThree.Native.mcl275RHex 3 275 9 14
#ks_chars CertificateChecks.KernelMisc.HSMcL.MS CFSG.Sporadic.Schreier.mclStrongHex
#kmisc_hexflat CertificateChecks.KernelMisc.HSMcL.MS CFSG.Sporadic.Schreier.mclStrongHex 4 275 9 2
#ks_chars CertificateChecks.KernelMisc.HSMcL.MC CFSG.Sporadic.SmallOddCore.mclCentHex
#kmisc_hexflat CertificateChecks.KernelMisc.HSMcL.MC CFSG.Sporadic.SmallOddCore.mclCentHex 3 275 9 1
#ks_chars CertificateChecks.KernelMisc.HSMcL.KX CFSG.RankThree.Native.hs100KappaHex
#kmisc_hexflat CertificateChecks.KernelMisc.HSMcL.KX CFSG.RankThree.Native.hs100KappaHex 3 3850 7 2
#ks_chars CertificateChecks.KernelMisc.HSMcL.HS CFSG.Sporadic.Schreier.hsStrongHex
#kmisc_hexflat CertificateChecks.KernelMisc.HSMcL.HS CFSG.Sporadic.Schreier.hsStrongHex 4 3850 12 2
#kmisc_sortpair CertificateChecks.KernelMisc.HSMcL.SG CFSG.RankThree.Native.hs100Kappa1
  CFSG.RankThree.Native.hs100Kappa2 100 3850

#ks_rawchain CertificateChecks.KernelMisc.HSMcL.C1 100 7 100 CFSG.RankThree.Native.hs100StrongArrs
  CFSG.RankThree.Native.hs100BaseArr 2 CertificateChecks.KernelMisc.HSMcL.d1
#ks_rawchain CertificateChecks.KernelMisc.HSMcL.C2 100 7 100 CFSG.RankThree.Native.hs100RArrs
  CFSG.RankThree.Native.hs100RBaseArr 3 CertificateChecks.KernelMisc.HSMcL.d2
#ks_rawchain CertificateChecks.KernelMisc.HSMcL.C3 275 9 55 CFSG.RankThree.Native.mcl275RArrs
  CFSG.RankThree.Native.mcl275RBaseArr 3 CertificateChecks.KernelMisc.HSMcL.d3

public section

namespace CertificateChecks.KernelMisc.HSMcL

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.HexFlat CFSG.KC.Misc.PairCount
open CFSG.RankThree.Native CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier
open CFSG.Monster.B.Co2 (allLt_iff)
open CFSG.KC.Misc.Clos (allN_iff)

theorem hs100Arr_eq (j : ℕ) (hj : j < 16) : hs100Arr j = unpack 100 7 (HX.F j) := by
  rw [hs100Arr, HX.eq]
  exact hexTable3_sound HX.all j hj

theorem hs100RArrs_get (j : ℕ) (hj : j < 17) : hs100RArrs[j]! = unpack 100 7 (RX.F j) := by
  unfold hs100RArrs
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn, RX.eq]
  exact hexTable3_sound RX.all j hj

theorem mcl275RArrs_get (j : ℕ) (hj : j < 14) : mcl275RArrs[j]! = unpack 275 9 (MX.F j) := by
  unfold mcl275RArrs
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn, MX.eq]
  exact hexTable3_sound MX.all j hj

theorem mclStrongArrs_get (j : ℕ) (hj : j < 2) : mclStrongArrs[j]! = unpack 275 9 (MS.F j) := by
  unfold mclStrongArrs
  rw [getElem!_pos _ j (by simp; omega), Array.getElem_ofFn, MS.eq]
  exact hexTable_sound MS.all j hj

theorem mclOuter_eq :
    CFSG.Sporadic.SmallOddCore.Native.natArr CFSG.Sporadic.SmallOddCore.mclOuterTbl =
      unpack 275 9 (MC.F 0) := by
  rw [CFSG.Sporadic.SmallOddCore.mclOuterTbl, CFSG.Sporadic.SmallOddCore.mclCentTbl, MC.eq]
  exact hexT_sound MC.all (by norm_num) 0 (by norm_num)

theorem hsStrongArrs_get (j : ℕ) (hj : j < 2) : hsStrongArrs[j]! = unpack 3850 12 (HS.F j) := by
  unfold hsStrongArrs
  rw [getElem!_pos _ j (by simp; omega), Array.getElem_ofFn, HS.eq]
  exact hexTable_sound HS.all j hj

theorem kappa1_eq : hs100Kappa1 = unpack 3850 7 (KX.F 0) := by
  have h := hexTable3_sound KX.all 0 (by norm_num)
  rw [Nat.mul_zero, ← KX.eq] at h
  exact h

theorem kappa2_eq : hs100Kappa2 = unpack 3850 7 (KX.F 1) := by
  have h := hexTable3_sound KX.all 1 (by norm_num)
  rw [Nat.mul_one, ← KX.eq] at h
  exact h

theorem c1_perm : allN 15 (fun j => permOK 100 7 (mask 7) (100 * 7) (C1.S j) (C1.SI j)) = true := by
  quickRfl

theorem c1_FS : ∀ j < 15, HX.F j = C1.S j := by decide +kernel

theorem c1_binds : Binds 100 7 C1.S 15 5 C1.BP hs100StrongArrs hs100BaseArr := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [hs100StrongArrs], fun j hj => ?_,
    by decide +kernel, by decide +kernel⟩
  rw [← c1_FS j hj, ← hs100Arr_eq j (by omega)]
  unfold hs100StrongArrs
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

theorem c1_words : hs100Words = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 15 d1 := by
  decide +kernel

theorem chain1 : rawChainOK 100 (hs100StrongArrs.extract 0 2) hs100StrongArrs hs100BaseArr
    hs100Words 1 = true := by
  rw [c1_words]
  exact rawChainK_sound (NS := 1) (CH := 100) c1_binds C1.head C1.hl (by norm_num) C1.hs

theorem orbits1 : rawOrbitSizes 100 hs100StrongArrs hs100BaseArr = [100, 77, 60, 12, 8] := by
  rw [rawOrbitSizesK_sound c1_binds c1_perm C1.hl]
  decide +kernel

theorem sq15 : eqA 100 (compA 100 (hs100Arr 15) (hs100Arr 15)) (idA 100) = true := by
  rw [hs100Arr_eq 15 (by norm_num)]
  exact sqIdK_sound (by quickRfl)

theorem inv15 : isInvA 100 (hs100Arr 15) (invCand 100 (hs100Arr 15)) = true := by
  rw [hs100Arr_eq 15 (by norm_num)]
  obtain ⟨h1, h2⟩ := invEqK_sound (n := 100) (w := 7) (p := HX.F 15) (r := HX.F 15) (by quickRfl)
  rw [h1]
  exact h2

theorem strong_eq : hs100StrongArrs = Array.ofFn fun j : Fin 15 => unpack 100 7 (HX.F j) := by
  unfold hs100StrongArrs
  exact congrArg (Array.ofFn (n := 15)) (funext fun j => hs100Arr_eq j (by omega))

theorem moved : allLt 100 (fun x => x == 0 || (List.range 15).any fun j =>
    (hs100StrongArrs[j]!)[0]! == 0 && (hs100StrongArrs[j]!)[x]! != x) = true := by
  rw [strong_eq, allLt_iff]
  decide +kernel

theorem c2_perm : allN 17 (fun j => permOK 100 7 (mask 7) (100 * 7) (C2.S j) (C2.SI j)) = true := by
  quickRfl

theorem c2_FS : ∀ j < 17, RX.F j = C2.S j := by decide +kernel

theorem c2_binds : Binds 100 7 C2.S 17 6 C2.BP hs100RArrs hs100RBaseArr := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [hs100RArrs], fun j hj => ?_,
    by decide +kernel, by decide +kernel⟩
  rw [← c2_FS j hj]
  exact hs100RArrs_get j hj

theorem c2_words : hs100RWords = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 3 17 d2 := by
  decide +kernel

theorem chain2 : rawChainOK 100 (hs100RArrs.extract 0 3) hs100RArrs hs100RBaseArr hs100RWords 1 =
    true := by
  rw [c2_words]
  exact rawChainK_sound (NS := 1) (CH := 100) c2_binds C2.head C2.hl (by norm_num) C2.hs

theorem orbits2 : rawOrbitSizes 100 hs100RArrs hs100RBaseArr = [100, 77, 16, 45, 8, 2] := by
  rw [rawOrbitSizesK_sound c2_binds c2_perm C2.hl]
  decide +kernel

theorem r_eq (j k : ℕ) (hj : j < 17) (hk : k < 16) (h : eqK (RX.F j) (HX.F k) = true) :
    eqA 100 hs100RArrs[j]! (hs100Arr k) = true := by
  rw [hs100RArrs_get j hj, hs100Arr_eq k hk]
  exact eqK_sound h

theorem c3_perm : allN 14 (fun j => permOK 275 9 (mask 9) (275 * 9) (C3.S j) (C3.SI j)) = true := by
  quickRfl

theorem c3_FS : ∀ j < 14, MX.F j = C3.S j := by decide +kernel

theorem c3_binds : Binds 275 9 C3.S 14 5 C3.BP mcl275RArrs mcl275RBaseArr := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [mcl275RArrs], fun j hj => ?_,
    by decide +kernel, by decide +kernel⟩
  rw [← c3_FS j hj]
  exact mcl275RArrs_get j hj

theorem c3_words : mcl275RWords = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 3 14 d3 := by
  decide +kernel

theorem chain3 : rawChainOK 275 (mcl275RArrs.extract 0 3) mcl275RArrs mcl275RBaseArr
    mcl275RWords 1 = true := by
  rw [c3_words]
  exact rawChainK_sound (NS := 5) (CH := 55) c3_binds C3.head C3.hl (by norm_num) C3.hs

theorem orbits3 : rawOrbitSizes 275 mcl275RArrs mcl275RBaseArr = [275, 112, 81, 45, 16] := by
  rw [rawOrbitSizesK_sound c3_binds c3_perm C3.hl]
  decide +kernel

theorem m_eq (j : ℕ) (hj : j < 2) (h : eqK (MX.F j) (MS.F j) = true) :
    eqA 275 mcl275RArrs[j]! mclStrongArrs[j]! = true := by
  rw [mcl275RArrs_get j (by omega), mclStrongArrs_get j hj]
  exact eqK_sound h

theorem m_outer : eqA 275 mcl275RArrs[2]!
    (CFSG.Sporadic.SmallOddCore.Native.natArr CFSG.Sporadic.SmallOddCore.mclOuterTbl) = true := by
  rw [mcl275RArrs_get 2 (by norm_num), mclOuter_eq]
  exact eqK_sound (by quickRfl)

theorem m_outer_inv : isInvA 275
    (CFSG.Sporadic.SmallOddCore.Native.natArr CFSG.Sporadic.SmallOddCore.mclOuterTbl)
    (invCand 275 (CFSG.Sporadic.SmallOddCore.Native.natArr
      CFSG.Sporadic.SmallOddCore.mclOuterTbl)) = true := by
  rw [mclOuter_eq]
  obtain ⟨h1, h2⟩ := invEqK_sound (n := 275) (w := 9) (p := MC.F 0) (r := MC.F 0) (by quickRfl)
  rw [h1]
  exact h2

theorem kpair : pairK 3850 7 (KX.F 0) (KX.F 1) = true := by quickRfl

theorem kbelow : CFSG.KC.LQT.P.allN 3850 (fun x => Nat.blt (pg 7 (mask 7) (KX.F 1) x) 100) = true := by
  quickRfl

theorem k1_lt {x : ℕ} (hx : x < 3850) : pg 7 (mask 7) (KX.F 0) x < pg 7 (mask 7) (KX.F 1) x :=
  Nat.blt_eq ▸ (allN_iff _ _).1 kpair x hx

theorem k2_lt {x : ℕ} (hx : x < 3850) : pg 7 (mask 7) (KX.F 1) x < 100 :=
  Nat.blt_eq ▸ (allN_iff _ _).1 kbelow x hx

theorem kappa_order : allLt 3850 (fun x => decide (hs100Kappa1[x]! < hs100Kappa2[x]!) &&
    decide (hs100Kappa2[x]! < 100)) = true := by
  rw [allLt_iff]
  intro x hx
  rw [kappa1_eq, kappa2_eq, unpack_get hx, unpack_get hx, Bool.and_eq_true, decide_eq_true_eq,
    decide_eq_true_eq]
  exact ⟨k1_lt hx, k2_lt hx⟩

theorem equiv_of (A G j k : ℕ) (hA : hsStrongArrs[j]! = unpack 3850 12 A)
    (hG : hs100Arr k = unpack 100 7 G)
    (h : CFSG.KC.LQT.P.allN 3850 (fun x => (decide (pg 12 (mask 12) A x < 3850) &&
      decide (pg 7 (mask 7) (KX.F 0) x < 100) && decide (pg 7 (mask 7) (KX.F 1) x < 100)) &&
      ((pg 7 (mask 7) (KX.F 0) (pg 12 (mask 12) A x) ==
            pg 7 (mask 7) G (pg 7 (mask 7) (KX.F 0) x) &&
          pg 7 (mask 7) (KX.F 1) (pg 12 (mask 12) A x) ==
            pg 7 (mask 7) G (pg 7 (mask 7) (KX.F 1) x)) ||
        (pg 7 (mask 7) (KX.F 0) (pg 12 (mask 12) A x) ==
            pg 7 (mask 7) G (pg 7 (mask 7) (KX.F 1) x) &&
          pg 7 (mask 7) (KX.F 1) (pg 12 (mask 12) A x) ==
            pg 7 (mask 7) G (pg 7 (mask 7) (KX.F 0) x)))) = true) :
    hs100KappaEquiv hsStrongArrs[j]! (hs100Arr k) = true := by
  unfold hs100KappaEquiv
  rw [allLt_iff]
  intro x hx
  have hx' := (allN_iff _ _).1 h x hx
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hx'
  obtain ⟨⟨⟨hy, h1⟩, h2⟩, he⟩ := hx'
  rw [hA, hG, kappa1_eq, kappa2_eq]
  simp only []
  rw [unpack_get hx, unpack_get hx, unpack_get hx, unpack_get hy, unpack_get hy, unpack_get h1,
    unpack_get h2]
  exact he

theorem equiv0 : hs100KappaEquiv hsStrongArrs[0]! (hs100Arr 0) = true :=
  equiv_of (HS.F 0) (HX.F 0) 0 0 (hsStrongArrs_get 0 (by norm_num))
    (hs100Arr_eq 0 (by norm_num)) (by quickRfl)

theorem equiv1 : hs100KappaEquiv hsStrongArrs[1]! (hs100Arr 1) = true :=
  equiv_of (HS.F 1) (HX.F 1) 1 1 (hsStrongArrs_get 1 (by norm_num))
    (hs100Arr_eq 1 (by norm_num)) (by quickRfl)

theorem K1_val (x : Fin 3850) : (hs100K1 x : ℕ) = pg 7 (mask 7) (KX.F 0) x := by
  rw [hs100K1, Fin.val_mk, kappa1_eq, unpack_get x.2]
  exact Nat.mod_eq_of_lt ((k1_lt x.2).trans (k2_lt x.2))

theorem K2_val (x : Fin 3850) : (hs100K2 x : ℕ) = pg 7 (mask 7) (KX.F 1) x := by
  rw [hs100K2, Fin.val_mk, kappa2_eq, unpack_get x.2]
  exact Nat.mod_eq_of_lt (k2_lt x.2)

@[expose] noncomputable def kE (k : ℕ) : ℕ :=
  Nat.add (Nat.mul 100 (pg 7 (mask 7) (KX.F 0) k)) (pg 7 (mask 7) (KX.F 1) k)

theorem s0 : CFSG.KC.Misc.Clos.allR 0 770 (CFSG.KC.Misc.Clos.sortAt 3850 kE SG) = true := by
  quickRfl
theorem s1 : CFSG.KC.Misc.Clos.allR 770 770 (CFSG.KC.Misc.Clos.sortAt 3850 kE SG) = true := by
  quickRfl
theorem s2 : CFSG.KC.Misc.Clos.allR 1540 770 (CFSG.KC.Misc.Clos.sortAt 3850 kE SG) = true := by
  quickRfl
theorem s3 : CFSG.KC.Misc.Clos.allR 2310 770 (CFSG.KC.Misc.Clos.sortAt 3850 kE SG) = true := by
  quickRfl
theorem s4 : CFSG.KC.Misc.Clos.allR 3080 770 (CFSG.KC.Misc.Clos.sortAt 3850 kE SG) = true := by
  quickRfl

theorem sorted : ∀ i < 3850, CFSG.KC.Misc.Clos.sortAt 3850 kE SG i = true :=
  CFSG.KC.Misc.Clos.forall_of_chunks 770 5 _ fun c hc => by
    interval_cases c
    · exact s0
    · exact s1
    · exact s2
    · exact s3
    · exact s4

theorem kappa_inj : Function.Injective hs100Kappa := by
  intro x y hxy
  have key : ∀ x y : Fin 3850, hs100Kappa x = hs100Kappa y →
      (hs100K1 x : ℕ) ≤ hs100K1 y := by
    intro x y h
    have hm : hs100K1 y ∈ hs100Kappa x := by rw [h]; simp [hs100Kappa]
    simp only [hs100Kappa, Finset.mem_insert, Finset.mem_singleton] at hm
    have hl := k1_lt x.2
    rw [← K1_val, ← K2_val] at hl
    rcases hm with hm | hm
    · rw [hm]
    · rw [hm]
      omega
  have h1 : (hs100K1 x : ℕ) = hs100K1 y := le_antisymm (key x y hxy) (key y x hxy.symm)
  have h2 : (hs100K2 x : ℕ) = hs100K2 y := by
    have hm : hs100K2 x ∈ hs100Kappa y := by rw [← hxy]; simp [hs100Kappa]
    simp only [hs100Kappa, Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm
    · have := k1_lt x.2
      rw [← K1_val, ← K2_val] at this
      rw [hm] at this
      omega
    · rw [hm]
  rw [K1_val, K1_val] at h1
  rw [K2_val, K2_val] at h2
  exact Fin.ext (CFSG.KC.Misc.Clos.sort_distinct sorted x x.2 y y.2 (by
    change Nat.add (Nat.mul 100 _) _ = Nat.add (Nat.mul 100 _) _
    rw [h1, h2]))

theorem kappa_card (x : Fin 3850) : (hs100Kappa x).card = 2 := by
  apply Finset.card_pair
  intro h
  have := k1_lt x.2
  rw [← K1_val, ← K2_val, h] at this
  exact lt_irrefl _ this

theorem kappa_zero : hs100Kappa 0 = {0, 78} := by
  have h1 : hs100K1 0 = 0 := Fin.ext (by rw [K1_val]; decide +kernel)
  have h2 : hs100K2 0 = 78 := Fin.ext (by rw [K2_val]; decide +kernel)
  rw [hs100Kappa, h1, h2]

theorem cnt0 : CFSG.KC.Misc.PairCount.cntK 3850 7 (KX.F 0) (KX.F 1) 0 50 77 = true := by quickRfl
theorem cnt1 : CFSG.KC.Misc.PairCount.cntK 3850 7 (KX.F 0) (KX.F 1) 50 50 77 = true := by quickRfl

theorem kappa_count (i : Fin 100) :
    (Finset.univ.filter fun x => i ∈ hs100Kappa x).card = 77 := by
  have hc : cntAt 3850 7 (KX.F 0) (KX.F 1) i = 77 := by
    rcases Nat.lt_or_ge (i : ℕ) 50 with h | h
    · have := (allN_iff _ _).1 cnt0 i h
      have e : Nat.add 0 (i : ℕ) = i := Nat.zero_add _
      rw [e] at this
      exact Nat.eq_of_beq_eq_true this
    · have := (allN_iff _ _).1 cnt1 (i - 50) (by omega)
      have e : Nat.add 50 ((i : ℕ) - 50) = i := Nat.add_sub_cancel' h
      rw [e] at this
      exact Nat.eq_of_beq_eq_true this
  rw [← hc, ← cntAt_sound kpair]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro x _
  simp only [hs100Kappa, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, K1_val, K2_val]

open CFSG CFSG.RankThree CFSG.RankThree.Native CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Sporadic.Schreier in
open Certificates in
theorem facts : (

    rawChainOK 100 (hs100StrongArrs.extract 0 2) hs100StrongArrs hs100BaseArr hs100Words 1 =
        true ∧
      rawOrbitSizes 100 hs100StrongArrs hs100BaseArr = [100, 77, 60, 12, 8] ∧
      eqA 100 (compA 100 (hs100Arr 15) (hs100Arr 15)) (idA 100) = true ∧
      isInvA 100 (hs100Arr 15) (invCand 100 (hs100Arr 15)) = true ∧
      allLt 100 (fun x => x == 0 || (List.range 15).any fun j =>
        (hs100StrongArrs[j]!)[0]! == 0 && (hs100StrongArrs[j]!)[x]! != x) = true
)
    ∧ (

    rawChainOK 100 (hs100RArrs.extract 0 3) hs100RArrs hs100RBaseArr hs100RWords 1 = true ∧
      rawOrbitSizes 100 hs100RArrs hs100RBaseArr = [100, 77, 16, 45, 8, 2] ∧
      eqA 100 hs100RArrs[0]! (hs100Arr 0) = true ∧ eqA 100 hs100RArrs[1]! (hs100Arr 1) = true ∧
      eqA 100 hs100RArrs[2]! (hs100Arr 15) = true
)
    ∧ (

    rawChainOK 275 (mcl275RArrs.extract 0 3) mcl275RArrs mcl275RBaseArr mcl275RWords 1 = true ∧
      rawOrbitSizes 275 mcl275RArrs mcl275RBaseArr = [275, 112, 81, 45, 16] ∧
      eqA 275 mcl275RArrs[0]! mclStrongArrs[0]! = true ∧
      eqA 275 mcl275RArrs[1]! mclStrongArrs[1]! = true ∧
      eqA 275 mcl275RArrs[2]! (CFSG.Sporadic.SmallOddCore.Native.natArr
        CFSG.Sporadic.SmallOddCore.mclOuterTbl) = true ∧
      isInvA 275 (CFSG.Sporadic.SmallOddCore.Native.natArr CFSG.Sporadic.SmallOddCore.mclOuterTbl)
        (invCand 275 (CFSG.Sporadic.SmallOddCore.Native.natArr
          CFSG.Sporadic.SmallOddCore.mclOuterTbl)) = true
)
    ∧ (

    allLt 3850 (fun x => decide (hs100Kappa1[x]! < hs100Kappa2[x]!) &&
        decide (hs100Kappa2[x]! < 100)) = true ∧
      hs100KappaEquiv hsStrongArrs[0]! (hs100Arr 0) = true ∧
      hs100KappaEquiv hsStrongArrs[1]! (hs100Arr 1) = true
)
    ∧ (

    Function.Injective hs100Kappa ∧ (∀ x, (hs100Kappa x).card = 2) ∧ hs100Kappa 0 = {0, 78} ∧
      ∀ i : Fin 100, (Finset.univ.filter fun x => i ∈ hs100Kappa x).card = 77
) :=
  ⟨⟨chain1, orbits1, sq15, inv15, moved⟩,
    ⟨chain2, orbits2, r_eq 0 0 (by norm_num) (by norm_num) (by quickRfl),
      r_eq 1 1 (by norm_num) (by norm_num) (by quickRfl),
      r_eq 2 15 (by norm_num) (by norm_num) (by quickRfl)⟩,
    ⟨chain3, orbits3, m_eq 0 (by norm_num) (by quickRfl), m_eq 1 (by norm_num) (by quickRfl),
      m_outer, m_outer_inv⟩,
    ⟨kappa_order, equiv0, equiv1⟩,
    ⟨kappa_inj, kappa_card, kappa_zero, kappa_count⟩⟩

end CertificateChecks.KernelMisc.HSMcL

end
