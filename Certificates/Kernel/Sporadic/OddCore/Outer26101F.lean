module

public import Certificates.Kernel.Sporadic.OddCore.Outer26101K
public import Certificates.Kernel.Sporadic.OddCore.Outer26100F
public import Certificates.Kernel.Sporadic.OddCore.Beta24603F
public import Certificates.Kernel.Sporadic.OddCore.S16J3Sift27810
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaJ3
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3HModel

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.O26101

open Subgroup
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.KS.ColH
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier.PairNative
open CFSG.EvenSporadicStandard.Fin76b.Beta CFSG.EvenSporadicStandard.Fin76b.TC3H
open CFSG.EvenSporadicStandard.HypOne CFSG.Certificates CFSG.Certificates.Native
open CertificateChecks.KernelSpor

local notation "⟪" x "⟫" => tabT (unpack 6156 13 x)

theorem base : S16J3.cK (TC3HJ3P 0) = true ∧ S16J3.cK (J3CentP 0) = true ∧
    S16J3.iK (TC3HJ3P 0) (S16J3.pc (TC3HJ3P 0) (S16J3.pc (TC3HJ3P 0) (S16J3.pc (TC3HJ3P 0)
      (S16J3.pc (TC3HJ3P 0) (S16J3.pc (TC3HJ3P 0) (S16J3.pc (TC3HJ3P 0) (TC3HJ3P 0))))))) = true ∧
    S16J3.outJ3 x0Out (TC3HJ3P 0) = true ∧
    SqrtK26102.j3W x0uWord (S16J3.pc (TC3HJ3P 0) (J3CentP 0)) = true ∧
    Nat.beq (S16J3.pc (TC3HJ3P 0) (J3BetaP 7)) (S16J3.pc (J3BetaP 7) (TC3HJ3P 0)) = true := by
  simpa only [bAnd_iff] using o26101_base

theorem hx0 : canonK 6156 13 (mask 13) (6156 * 13) (TC3HJ3P 0) = true := base.1

theorem sift_of_word {X : Nat} {wd : List Int} (hX : canonK 6156 13 (mask 13) (6156 * 13) X = true)
    (h : SqrtK26102.j3W wd X = true) : j3Sift ⟪X⟫ = true := by
  unfold j3Sift
  rw [natArr_tabT hX, CertificateChecks.KernelSporSch.J3KT.sift_of h]

theorem outerOK : j3OuterOK = true := by
  obtain ⟨hc, hu, hi, hout, hw, hcomm⟩ := base
  have hcomm' : Nat.beq (pcomp 6156 13 (mask 13) (TC3HJ3P 0) (J3BetaP 7))
      (pcomp 6156 13 (mask 13) (J3BetaP 7) (TC3HJ3P 0)) = true := hcomm
  unfold j3OuterOK zOK
  rw [j3OuterTbl, B24603.cent_eq (by norm_num), SqrtK26102.j3Tbl_eq (by norm_num),
    J3BetaA5.beta_tab (by norm_num), compT_unpack hc hu, permOK_unpack hc hi,
    commTT_unpack hc B24603.hbc, S16J3.sift_false_of_out hc hi hout,
    sift_of_word (canonK_pcomp hc hu) hw, hcomm']
  rfl

theorem ap_TK {k i : ℕ} (hi : i < 6156) : ap (B24603.TK k) i = lane16 (B24603Col i) k := by
  unfold ap
  rw [B24603.TK, colT_get hi, UInt32.toNat_ofNat',
    Nat.mod_eq_of_lt (lt_trans (lane16_lt _ _) (by norm_num))]

theorem sq_ne_one {g x : Equiv.Perm (Fin 6156)} {k i : ℕ} (hg : Rep 6156 (B24603.TK k) g)
    (hx : Rep 6156 ⟪TC3HJ3P 0⟫ x) (hi : i < 6156) (h : mvK (TC3HJ3P 0) k i = true) :
    g * x * (g * x) ≠ 1 := by
  have apX : ∀ j < 6156, idx 6156 x j = pg 13 (mask 13) (TC3HJ3P 0) j := fun j hj => by
    rw [← hx j hj]
    exact B24603.tab_toNat hx0 hj
  have apG : ∀ j < 6156, idx 6156 g j = lane16 (B24603Col j) k := fun j hj => by
    rw [← hg j hj]
    exact ap_TK hj
  intro e
  have h0 : idx 6156 (g * x * (g * x)) i = i := by rw [e, idx_one]
  rw [idx_mul, idx_mul, idx_mul] at h0
  have ha := pg_lt' hx0 hi
  rw [apX i hi, apG _ ha] at h0
  have hb : lane16 (B24603Col (pg 13 (mask 13) (TC3HJ3P 0) i)) k < 6156 := by
    rw [← apG _ ha]
    exact idx_lt g ha
  rw [apX _ hb, apG _ (pg_lt' hx0 hb)] at h0
  revert h
  unfold mvK
  rw [h0, Nat.beq_refl]
  decide

theorem countOuter :
    j3CountOuter = 0 := by
  classical
  have hchk := Certificates.certificate24603.1
  have hperm := (betaHomCheck_permOK hchk).2.2
  have hpermx : permOK 6156 (j3Tbl 0) = true := by
    have h := outerOK
    simp only [j3OuterOK, zOK, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact h.1.1.1
  have hgs : List.Forall₂ (CFSG.Monster.B.Co2.Rep 6156) [natArr (j3BetaTbl 7)]
      [tp 6156 (j3BetaTbl 7)] :=
    List.Forall₂.cons (co2Rep_natArr_iff.2 (rep_tp hperm)) List.Forall₂.nil
  have hx : CFSG.Monster.B.Co2.Rep 6156 (natArr (j3Tbl 0)) (tp 6156 (j3Tbl 0)) :=
    co2Rep_natArr_iff.2 (rep_tp hpermx)
  have hcount := card_eq_countW (f := commSqxW 6156 (natArr (j3BetaTbl 7)) (natArr (j3Tbl 0)))
    (Pr := fun g => g * tp 6156 (j3BetaTbl 7) = tp 6156 (j3BetaTbl 7) * g ∧
      g * tp 6156 (j3Tbl 0) * (g * tp 6156 (j3Tbl 0)) = 1)
    j3ChainArrays (by norm_num) PairJ3.chain_check.1 j3_groups (fun w g hw _ => by
      rw [commSqxW, Bool.and_eq_true, commW_iff hgs hw, sqxW_iff hx hw]
      simp)
  rw [show blocksOf 6156 (rawLevels 6156 j3StrongArrs PairJ3.baseArr) PairJ3.groups =
    PairJ3.blocks from rfl, ← PairJ3.parCount_eq, ← j3P_eq_original] at hcount
  unfold j3CountOuter
  rw [← hcount, Nat.card_eq_zero]
  left
  constructor
  rintro ⟨⟨g, hgP⟩, hc, hsq⟩
  obtain ⟨ht, hd, -⟩ := betaHomCheck_permOK hchk
  have hmem := Certificates.certificate24603.2
  simp only [j3MemOK, Bool.and_eq_true] at hmem
  obtain ⟨⟨⟨hs8, hs9⟩, -⟩, -⟩ := hmem
  have hD := j3_groupData
  have htX := (hD.sift _ _ (rep_tp ht)).1 hs8
  have hdX := (hD.sift _ _ (rep_tp hd)).1 hs9
  obtain ⟨k, hk, hrep⟩ := O26100.cover_of_check (by norm_num) hchk htX hdX
    CFSG.EvenSporadicStandard.Fin76b.J3.card_centralizer_beta g
    (mem_inf.mpr ⟨hgP, mem_centralizer_singleton_iff.2 hc⟩)
  rw [B24603.gens_eq, B24603.mul_eq, B24603.LK_size] at hk
  rw [B24603.gens_eq, B24603.mul_eq, B24603.LK_get hk] at hrep
  set x := tp 6156 (j3Tbl 0) with hxdef
  have hxr : Rep 6156 (j3Tbl 0) x := rep_tp hpermx
  rw [SqrtK26102.j3Tbl_eq (by norm_num)] at hxr
  have hm := allN_spec o26101_sq k hk
  unfold mv01 at hm
  cases h0 : mvK (TC3HJ3P 0) k 0
  · rw [h0] at hm
    exact sq_ne_one hrep hxr (by norm_num) hm hsq
  · exact sq_ne_one hrep hxr (by norm_num) h0 hsq

end CertificateChecks.KernelSpor.O26101

end
