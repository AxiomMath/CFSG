module

public import Certificates.Kernel.McLAS.ThreeF
public import Certificates.Kernel.McLAS.FiveTabs
public import Certificates.Kernel.McLAS.InvChk0
public import Certificates.Kernel.McLAS.InvChk1
public import Certificates.Kernel.Sporadic.OddCore.MNF
public import Certificates.Kernel.Sporadic.OddCore.McLTH
public import CFSG.Certificates.Kernel.Item434.PkSound
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Misc.ArrBind

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMcLAS

open CFSG.Sporadic.Recognition.McLAS CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.KS.McLAS Subgroup

local notation "⟪" p "⟫" => tabT (unpack 275 9 p)

#kc_forall_tree ip_all (fun s => CertificateChecks.KernelMcLAS.ipSl s = true) 112
  CertificateChecks.KernelMcLAS.InvChk.ci

theorem ord6K_sound {X : Nat} (hX : Cn X) {g : Equiv.Perm (Fin 275)} (hg : Rep 275 ⟪X⟫ g)
    (h : ord6K X = true) : g ^ 4 = 1 ∨ g ^ 6 = 1 ∨ g ^ 5 = 1 := by
  unfold ord6K at h
  simp only [CFSG.KS.PEnum.strictB_app'] at h
  have c2 := canonK_pcomp hX hX
  have c4 := canonK_pcomp c2 c2
  have c3 := canonK_pcomp c2 hX
  have r2 := rep_pc hX hX hg hg
  have r4 := rep_pc c2 c2 r2 r2
  have r3 := rep_pc c2 hX r2 hg
  have r6 := rep_pc c3 c3 r3 r3
  have r5 := rep_pc c4 hX r4 hg
  have hid1 : Rep 275 ⟪McLAS.idK⟫ (1 : Equiv.Perm (Fin 275)) := by
    rw [← hid]
    exact Rep.idT (by norm_num)
  cases e4 : Nat.beq (pcK (pcK X X) (pcK X X)) McLAS.idK
  · rw [e4] at h
    cases e6 : Nat.beq (pcK (pcK (pcK X X) X) (pcK (pcK X X) X)) McLAS.idK
    · rw [e6] at h
      right; right
      rw [show g ^ 5 = g * g * (g * g) * g by simp only [pow_succ, pow_zero, one_mul, mul_assoc]]
      exact eq_of_beq r5 hid1 h
    · right; left
      rw [show g ^ 6 = g * g * g * (g * g * g) by simp only [pow_succ, pow_zero, one_mul, mul_assoc]]
      exact eq_of_beq r6 hid1 e6
  · left
    rw [show g ^ 4 = g * g * (g * g) by simp only [pow_succ, pow_zero, one_mul, mul_assoc]]
    exact eq_of_beq r4 hid1 e4

theorem any_ord {T : Table} {g : Equiv.Perm (Fin 275)} (hT : Rep 275 T g)
    (h : g ^ 4 = 1 ∨ g ^ 6 = 1 ∨ g ^ 5 = 1) :
    (List.range 6).any (fun i => ordTest 275 (i + 1) T) = true := by
  have hpos : 0 < orderOf g := orderOf_pos g
  have hle : orderOf g ≤ 6 := by
    rcases h with h | h | h
    · exact (Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h)).trans (by norm_num)
    · exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h)
    · exact (Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h)).trans (by norm_num)
  rw [List.any_eq_true]
  refine ⟨orderOf g - 1, List.mem_range.2 (by omega), ?_⟩
  rw [Nat.sub_add_cancel hpos]
  exact (ordTest_iff_perm hT hpos).2 rfl

theorem invProd_ok :
    invProdCheck = true := by
  have hroot : CertificateChecks.KernelSpor.MN.R1.R = CertificateChecks.KernelSpor.MNd.F 4 :=
    Nat.eq_of_beq_eq_true CertificateChecks.KernelSpor.MNd.bindR.2.2.1
  have ht0 : invTab0 = ⟪CertificateChecks.KernelSpor.MNd.F 4⟫ := by
    unfold invTab0
    exact CertificateChecks.KernelSpor.MNd.tabF (by norm_num)
  have hh : penumHdK CertificateChecks.KernelSpor.MN.R1.R CertificateChecks.KernelSpor.MN.R1.cnt
      30000 CertificateChecks.KernelSpor.MN.R1.T CertificateChecks.KernelSpor.MN.R1.PL = true := by
    quickRfl
  have hR := conjH_sound (k := 2) (X := CertificateChecks.KernelSpor.MN.R1.R) (x := invTab0)
    (cap := 30000) CertificateChecks.KernelSpor.MNd.hn
    (TabsOK_congr (CertificateChecks.KernelSpor.MNd.pair_of CertificateChecks.KernelSpor.MNd.bindR.1).1
      CertificateChecks.KernelSpor.MNd.pg_tabs)
    (TabsOK_congr (CertificateChecks.KernelSpor.MNd.pair_of CertificateChecks.KernelSpor.MNd.bindR.1).2
      CertificateChecks.KernelSpor.MNd.pgi_tabs)
    (by rw [ht0, hroot]) hh CertificateChecks.KernelSpor.MNd.r1_pe CertificateChecks.KernelSpor.MNd.r1_hs
  have hF4 := CertificateChecks.KernelSpor.MNd.Fc (k := 4) (by norm_num)
  have hrep0' : Rep 275 invTab0 (tp 275 invTab0) :=
    rep_tp (CertificateChecks.KernelSpor.MNd.permF (k := 4) (by norm_num))
  have hrep0 : Rep 275 ⟪CertificateChecks.KernelSpor.MNd.F 4⟫ (tp 275 invTab0) := by
    generalize hg : tp 275 invTab0 = g
    have h := hrep0'
    rw [hg, ht0] at h
    exact h
  unfold invProdCheck
  simp only [hR.1, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨CertificateChecks.KernelSpor.MNd.permF (k := 4) (by norm_num), ?_⟩, ?_⟩, hR.2.1⟩,
    hR.2.2⟩, ?_⟩, ?_⟩
  · rw [ht0, ordTest_eq hF4 2]
    decide +kernel
  · rw [allIn_eq_true]
    intro l _ hl
    exact pgInv_ok hl
  · rw [hRec_size, CertificateChecks.KernelSpor.MNd.sizes.1]
  · refine all_hRec fun i hi => ?_
    beta_reduce
    have hc := penumPt_canon (CertificateChecks.KernelSpor.MNd.r1_pe i hi)
    obtain ⟨c, -, hcr⟩ := conjTreeOK_spec mclP hgP hrep0' hR.2.1 i (by rw [hRec_size]; exact hi)
    rw [hRec_get hi] at hcr
    have hip := slice_at (cnt := CertificateChecks.KernelSpor.MN.R1.cnt) (NS := 112)
      (by rw [CertificateChecks.KernelSpor.MNd.sizes.1]; norm_num) ip_all i hi
    rw [hroot] at hip
    have hpr := rep_pc hF4 hc hrep0 hcr
    rw [ht0, compT_unpack hF4 hc]
    exact any_ord hpr (ord6K_sound (canonK_pcomp hF4 hc) hpr hip)

theorem sylowThree_ok : sylowThreeOK = true := by
  have hsub := CertificateChecks.KernelSpor.McLTK.subT
  unfold subEnumOK at hsub
  simp only [Bool.and_eq_true, beq_iff_eq] at hsub
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hsub
  have hth := CertificateChecks.KernelSpor.McLTK.thompson_ok
  unfold thompsonCheck enumT at hth
  simp only [Bool.and_eq_true, beq_iff_eq] at hth
  have hri := CertificateChecks.KernelSpor.McLTK.rInT_ok
  unfold rInTCheck at hri
  simp only [Bool.and_eq_true] at hri
  have hx := memT_at (PL := CertificateChecks.KernelSpor.McLTT.PL) (TTc (k := 0) (by norm_num))
    CertificateChecks.KernelMcLAS.ThreeChk.x_in_t
  have heT := CertificateChecks.KernelSpor.McLTK.eT.1
  unfold enumT at heT
  rw [← heT, ← tabTT (k := 0) (by norm_num)] at hx
  unfold sylowThreeOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, hth.2⟩, hx⟩, ?_⟩
  · rw [tabTT (k := 0) (by norm_num)]
    exact permOK_unpack (TTc (by norm_num)) (TTinv (by norm_num))
  · rw [List.all_toArray]
    exact hri.2

theorem m11_gens : m11Gens = #[unpack 275 9 (CertificateChecks.KernelSpor.MNd.F 18),
    unpack 275 9 (CertificateChecks.KernelSpor.MNd.F 19),
    unpack 275 9 (CertificateChecks.KernelSpor.MNd.F 20),
    unpack 275 9 (CertificateChecks.KernelSpor.MNd.F 21)] := by
  unfold m11Gens
  apply Array.ext (by simp)
  intro i h1 _
  simp only [Array.size_ofFn] at h1
  simp only [Array.getElem_ofFn]
  interval_cases i <;>
    (rw [CertificateChecks.KernelSpor.MNd.tabF (by norm_num),
      natArr_tabT (CertificateChecks.KernelSpor.MNd.Fc (by norm_num))]; rfl)

theorem m11_ok : m11Check = true := by
  have h17 : natArr outerTab = unpack 275 9 (CertificateChecks.KernelSpor.MNd.F 17) := by
    unfold outerTab
    rw [CertificateChecks.KernelSpor.MNd.tabF (by norm_num),
      natArr_tabT (CertificateChecks.KernelSpor.MNd.Fc (by norm_num))]
  have hp : permOK 275 outerTab = true := CertificateChecks.KernelSpor.MNd.permF (by norm_num)
  have hq : (List.range 4).all (fun k => permOK 275 (mclCentTbl (k + 18))) = true :=
    List.all_eq_true.2 fun k hk => CertificateChecks.KernelSpor.MNd.permF (by simp at hk; omega)
  unfold m11Check m11Rest
  rw [hp, hq, m11_gens, h17]
  decide +kernel

theorem fv_eq {k : Nat} (hk : k < 71) : CFSG.RankThree.Native.mcl275FiveArr k = unpack 275 9 (FV.F k) := by
  unfold CFSG.RankThree.Native.mcl275FiveArr
  rw [FV.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable3_sound FV.all k hk

theorem fp_eq : fivePowArr = unpack 275 9 (FP.F 0) := by
  unfold fivePowArr
  rw [FP.eq]
  have := CFSG.KC.Misc.HexFlat.hexTable3_sound FP.all 0 (by norm_num)
  simpa using this

theorem siftA_eq {X : Nat} (hX : Cn X) :
    CFSG.Monster.B.Co2.Native.siftA 275 CFSG.RankThree.Native.mcl275PLevels PairMcL.baseArr 0
      (unpack 275 9 X) = sK X := by
  have h := sift_eq hX
  unfold mclSift at h
  rw [natArr_tabT hX] at h
  exact h

theorem any_range_congr {m : ℕ} {f g : ℕ → Bool} (h : ∀ k < m, f k = g k) :
    (List.range m).any f = (List.range m).any g := by
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨k, hk, hk'⟩
    exact ⟨k, hk, by rw [← h k hk]; exact hk'⟩
  · rintro ⟨k, hk, hk'⟩
    exact ⟨k, hk, by rw [h k hk]; exact hk'⟩

theorem fv_canon : allN 71 (fun k => canonK 275 9 (mask 9) (275 * 9) (FV.F k)) = true := by
  quickRfl

theorem fvc {k : Nat} (hk : k < 71) : Cn (FV.F k) := CFSG.KS.Raw.Orb.allN_iff.1 fv_canon k hk

theorem fiveOuter_ok : fiveOuterCheck = true := by
  have e0 : (List.range CFSG.RankThree.Native.mcl275FiveC0Gens.size).any
      (fun k => !CFSG.Monster.B.Co2.Native.siftA 275 CFSG.RankThree.Native.mcl275PLevels
        PairMcL.baseArr 0 CFSG.RankThree.Native.mcl275FiveC0Gens[k]!) =
      (List.range 3).any (fun k => !sK (FV.F (64 + k))) := by
    rw [show CFSG.RankThree.Native.mcl275FiveC0Gens.size = 3 from rfl]
    refine any_range_congr fun k hk => ?_
    have e : CFSG.RankThree.Native.mcl275FiveC0Gens[k]! =
        CFSG.RankThree.Native.mcl275FiveArr (64 + k) := by
      interval_cases k <;> rfl
    rw [e, fv_eq (by omega), siftA_eq (fvc (by omega))]
  have e1 : (List.range CFSG.RankThree.Native.mcl275FiveC1Gens.size).any
      (fun k => !CFSG.Monster.B.Co2.Native.siftA 275 CFSG.RankThree.Native.mcl275PLevels
        PairMcL.baseArr 0 CFSG.RankThree.Native.mcl275FiveC1Gens[k]!) =
      (List.range 4).any (fun k => !sK (FV.F (67 + k))) := by
    rw [show CFSG.RankThree.Native.mcl275FiveC1Gens.size = 4 from rfl]
    refine any_range_congr fun k hk => ?_
    have e : CFSG.RankThree.Native.mcl275FiveC1Gens[k]! =
        CFSG.RankThree.Native.mcl275FiveArr (67 + k) := by
      interval_cases k <;> rfl
    rw [e, fv_eq (by omega), siftA_eq (fvc (by omega))]
  unfold fiveOuterCheck
  rw [e0, e1]
  decide +kernel

theorem fivePower_ok : fivePowerCheck = true := by
  have hpG : CFSG.KC.Misc.ArrEnum.permB 275 9 (FP.F 0) = true := by quickRfl
  have hpL : CFSG.KC.Misc.ArrEnum.permB 275 9 (FV.F 3) = true := by quickRfl
  have pG := CFSG.KC.Item434.pk_unpack hn hpG
  have pL := CFSG.KC.Item434.pk_unpack hn hpL
  have hG : canonK 275 9 (mask 9) (275 * 9) (FP.F 0) = true := by quickRfl
  have hL : CFSG.RankThree.Native.mcl275FiveLines[1]! = unpack 275 9 (FV.F 3) := by
    rw [← fv_eq (k := 3) (by norm_num)]
    rfl
  unfold fivePowerCheck
  rw [fp_eq, hL, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨CFSG.KC.Item434.isInvA_pk pG, ?_⟩, ?_⟩
  · rw [siftA_eq hG]
    decide +kernel
  · rw [CFSG.KC.Item434.eqA_pk hn (CFSG.KC.Item434.pk_conjA hn pG pL)
      (CFSG.KC.Item434.pk_powArr hn pL 2)]
    decide +kernel

end CertificateChecks.KernelMcLAS

end
