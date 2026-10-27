module

public import Certificates.Kernel.Sporadic.OddCore.Outer26100K
public import Certificates.Kernel.Sporadic.OddCore.Beta24601F
public import Certificates.Kernel.Sporadic.OddCore.SqrtGlue26102
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaJ2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3HModel
public import CFSG.Sporadic.Schreier.PairJ2Order
public import CFSG.Sporadic.Schreier.PairJ2Pairs
public import CFSG.Sporadic.Schreier.PairJ2Check
public import CFSG.Sporadic.Schreier.PairJ2Cert
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaSq
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddKernelInvolutionFusion

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.O26100

open Subgroup
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier.PairNative
open CFSG.EvenSporadicStandard.Fin76b.Beta CFSG.EvenSporadicStandard.Fin76b.TC3H
open CFSG.EvenSporadicStandard.HypOne CFSG.Certificates CFSG.Certificates.Native
open CertificateChecks.KernelSpor

local notation "⟪" x "⟫" => tabT (unpack 315 9 x)

theorem cover_of_check {n : ℕ} (hn : n < 2 ^ 32) {X : Subgroup (Equiv.Perm (Fin n))}
    {tT dT bT : Table} {pg : Array Table} (hchk : betaHomCheck n tT dT bT pg = true)
    (htX : tp n tT ∈ X) (hdX : tp n dT ∈ X)
    (hcard : Nat.card ↥(X ⊓ centralizer ({tp n bT} : Set (Equiv.Perm (Fin n)))) = 1080) :
    ∀ x ∈ X ⊓ centralizer ({tp n bT} : Set (Equiv.Perm (Fin n))),
      ∃ k < (mulClosureH n #[tT, dT] 1100).1.size, Rep n (mulClosureH n #[tT, dT] 1100).1[k]! x := by
  classical
  simp only [betaHomCheck, Bool.and_eq_true, beq_iff_eq] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, -⟩, -⟩, -⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hchk
  rw [Array.all_eq_true'] at h1
  simp only [Bool.and_eq_true] at h1
  have hgA : ∀ x ∈ #[tT, dT], permOK n x = true := fun x hx => (h1 x hx).1
  have hginv : ∀ x ∈ #[tT, dT], invOK n x (invT n x) = true := fun x hx => (h1 x hx).2
  obtain ⟨-, hcov, hKcard⟩ := enum_spec hn hgA hginv h7 (closedOK_of_closedOKH h9) h8
  rw [Array.all_eq_true'] at h6
  have rb := rep_tp h2
  have hKle : closure (tp n '' {x | x ∈ #[tT, dT]}) ≤
      X ⊓ centralizer ({tp n bT} : Set (Equiv.Perm (Fin n))) := by
    rw [closure_le]
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨?_, mem_centralizer_singleton_iff.2 ((commTT_iff rb (rep_tp (hgA x hx))).1
      (h6 x hx)).symm⟩
    simp at hx
    rcases hx with rfl | rfl
    · exact htX
    · exact hdX
  have hKeq := eq_of_le_of_card_ge hKle (by rw [hcard, hKcard, h10])
  intro x hx
  rw [← hKeq] at hx
  exact hcov x hx

theorem base : S16J2.cK (TC3HJ2T.F 0) = true ∧
    S16J2.iK (TC3HJ2T.F 0) (J2Cn.pw 11 (TC3HJ2T.F 0)) = true ∧
    J2Cn.sK (TC3HJ2T.F 0) = false ∧ J2Cn.sK (J2Cn.pc (TC3HJ2T.F 0) (J2Cn.F 0)) = true ∧
    J2Cn.commK (TC3HJ2T.F 0) (J2BetaT.F 7) = true := by
  have h := o26100_base
  simp only [bAnd_iff] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, ?_, h4, h5⟩
  revert h3
  cases J2Cn.sK (TC3HJ2T.F 0) <;> decide

theorem hx0 : canonK 315 9 (mask 9) (315 * 9) (TC3HJ2T.F 0) = true := base.1

theorem outerOK : j2OuterOK = true := by
  obtain ⟨-, hi, hs, hsu, hc⟩ := base
  unfold j2OuterOK zOK
  rw [j2OuterTbl, J2Cn.tabF (by norm_num : 0 < 42), SqrtK26102.j2Tbl_eq (by norm_num),
    B24601.beta_tab (by norm_num), compT_unpack hx0 (J2Cn.Fc (by norm_num)),
    permOK_unpack hx0 hi, J2Cn.sift_eq hx0, J2Cn.sift_eq (canonK_pcomp hx0 (J2Cn.Fc (by norm_num))),
    J2Cn.commF hx0 B24601.hbc]
  change (true && !J2Cn.sK (TC3HJ2T.F 0) &&
    (J2Cn.sK (TC3HJ2T.F 0) || J2Cn.sK (J2Cn.pc (TC3HJ2T.F 0) (J2Cn.F 0))) &&
    J2Cn.commK (TC3HJ2T.F 0) (J2BetaT.F 7)) = true
  rw [hs, hsu, hc]
  rfl

theorem sq_ne {k : ℕ} (hk : k < 1080) :
    Nat.beq (J2Cn.pc (J2Cn.pc (B24601R.T k) (TC3HJ2T.F 0)) (J2Cn.pc (B24601R.T k) (TC3HJ2T.F 0)))
      J2Cn.idK = false := by
  have h := allN_spec o26100_sq k hk
  unfold nsqK at h
  revert h
  cases Nat.beq (J2Cn.pc (J2Cn.pc (B24601R.T k) (TC3HJ2T.F 0))
    (J2Cn.pc (B24601R.T k) (TC3HJ2T.F 0))) J2Cn.idK <;> decide

theorem countOuter :
    j2CountOuter = 0 := by
  classical
  have hchk := Certificates.certificate24601.1
  have hperm := (betaHomCheck_permOK hchk).2.2
  have hpermx : permOK 315 (j2Tbl 0) = true := by
    have h := outerOK
    simp only [j2OuterOK, zOK, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact h.1.1.1
  have hgs : List.Forall₂ (CFSG.Monster.B.Co2.Rep 315) [natArr (j2BetaTbl 7)]
      [tp 315 (j2BetaTbl 7)] :=
    List.Forall₂.cons (co2Rep_natArr_iff.2 (rep_tp hperm)) List.Forall₂.nil
  have hx : CFSG.Monster.B.Co2.Rep 315 (natArr (j2Tbl 0)) (tp 315 (j2Tbl 0)) :=
    co2Rep_natArr_iff.2 (rep_tp hpermx)
  have hcount := card_eq_countW (f := commSqxW 315 (natArr (j2BetaTbl 7)) (natArr (j2Tbl 0)))
    (Pr := fun g => g * tp 315 (j2BetaTbl 7) = tp 315 (j2BetaTbl 7) * g ∧
      g * tp 315 (j2Tbl 0) * (g * tp 315 (j2Tbl 0)) = 1)
    j2ChainArrays (by norm_num) PairJ2.chain_check.1 j2_groups (fun w g hw _ => by
      rw [commSqxW, Bool.and_eq_true, commW_iff hgs hw, sqxW_iff hx hw]
      simp)
  rw [show blocksOf 315 (rawLevels 315 j2StrongArrs PairJ2.baseArr) PairJ2.groups =
    PairJ2.blocks from rfl, ← j2P_eq_original] at hcount
  unfold j2CountOuter
  rw [← hcount, Nat.card_eq_zero]
  left
  constructor
  rintro ⟨⟨g, hgP⟩, hc, hsq⟩
  obtain ⟨ht, hd, -⟩ := betaHomCheck_permOK hchk
  have hmem := Certificates.certificate24601.2
  simp only [j2MemOK, Bool.and_eq_true] at hmem
  obtain ⟨⟨⟨hs8, hs9⟩, -⟩, -⟩ := hmem
  have hD := j2_groupData
  have htX := (hD.sift _ _ (rep_tp ht)).1 hs8
  have hdX := (hD.sift _ _ (rep_tp hd)).1 hs9
  obtain ⟨k, hk, hrep⟩ := cover_of_check (by norm_num) hchk htX hdX
    CFSG.EvenSporadicStandard.Fin76b.J2.card_centralizer_beta g
    (mem_inf.mpr ⟨hgP, mem_centralizer_singleton_iff.2 hc⟩)
  rw [B24601.gens_eq, B24601.mul_eq', show (hRec 315 9 1080 B24601R.T B24601R.PL).1 = B24601.LK
    from rfl, B24601.LK_size] at hk
  rw [B24601.gens_eq, B24601.mul_eq', show (hRec 315 9 1080 B24601R.T B24601R.PL).1 = B24601.LK
    from rfl, B24601.LK_get hk] at hrep
  set x := tp 315 (j2Tbl 0) with hxdef
  have hxr : Rep 315 (j2Tbl 0) x := rep_tp hpermx
  rw [SqrtK26102.j2Tbl_eq (by norm_num)] at hxr
  have hT := B24601.hT hk
  have hgx := Rep.compT hrep hxr
  rw [compT_unpack hT hx0] at hgx
  have hgx2 := Rep.compT hgx hgx
  have hy := canonK_pcomp hT hx0
  rw [compT_unpack hy hy] at hgx2
  have he := (tblEq_idT_iff (by norm_num) hgx2).2 hsq
  rw [B24601.hid, tblEq_unpack (canonK_pcomp hy hy) B24601.hidc] at he
  have hne := sq_ne hk
  change Nat.beq (pcomp 315 9 (mask 9) (pcomp 315 9 (mask 9) (B24601R.T k) (TC3HJ2T.F 0))
    (pcomp 315 9 (mask 9) (B24601R.T k) (TC3HJ2T.F 0))) (pidn 315 9) = false at hne
  rw [hne] at he
  exact Bool.false_ne_true he

end CertificateChecks.KernelSpor.O26100

end
