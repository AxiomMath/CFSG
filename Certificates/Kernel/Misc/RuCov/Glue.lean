
module

public import Certificates.Kernel.Misc.RuCov.S
public import Certificates.Kernel.Misc.RuCov.L
public import Certificates.Kernel.Misc.RuCov.Bind
public import Certificates.Kernel.Misc.RuScan.Glue
public import Certificates.Kernel.Misc.RuSq.Bind
public import Certificates.Kernel.Misc.RuInv.Check
public import CFSG.Certificates.Kernel.Misc.RuCovSound
public import CFSG.Quasithin.Vol2.KGFactG2RuE64
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.FactsB2Cover
import CFSG.Certificates.Kernel.Common.ForallTree
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Fours
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.HypOnePrelude
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.Schreier.RuOddCoreBase
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelMisc.RuCov

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Prim CFSG.KC.Misc.RuInv
  CFSG.KC.Misc.RuInv.P CFSG.KC.Misc.RuBase CFSG.KC.Misc.RuScan CFSG.KC.Misc.RuCov
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.RuSchreier
  CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.Ru CertificateChecks.KernelSporSch
  CertificateChecks.KernelMisc.RuScan CFSG.Quasithin.H13.Ch4.G2Ru

#kc_forall_tree sAll (fun q => ch7229s_ q = true) 16 CertificateChecks.KernelMisc.RuCov.ch7229s_
#kc_forall_tree lAll (fun q => ch7229l_ q = true) 28 CertificateChecks.KernelMisc.RuCov.ch7229l_
#kc_forall_tree cAll (fun r => ch7229c_ r = true) 4 CertificateChecks.KernelMisc.RuCov.ch7229c_
#kc_forall_tree dAll (fun r => ch7229d_ r = true) 5 CertificateChecks.KernelMisc.RuCov.ch7229d_

section Reps

theorem prepR0 : PRep 4060 12 (HR 0) ruZ := by
  rw [Nat.eq_of_beq_eq_true ch7229z]
  exact prep_Z

theorem prepR1 : PRep 4060 12 (HR 1) ruA0 := by
  rw [Nat.eq_of_beq_eq_true ch7229a]
  exact prep_A0

theorem g6I_eq : g6IA = rawInvs 4060 g6A := by
  simp [g6IA, g6A, rawInvs, ruInv]

theorem binds6' {a b c d e f : Array Nat} {A B C D E F : Nat} (ha : a = unpack 4060 12 A)
    (hb : b = unpack 4060 12 B) (hc : c = unpack 4060 12 C) (hd : d = unpack 4060 12 D)
    (he : e = unpack 4060 12 E) (hf : f = unpack 4060 12 F) :
    (#[a, b, c, d, e, f] : Array (Array Nat)).size = 6 ∧ ∀ j < 6,
      (#[a, b, c, d, e, f] : Array (Array Nat))[j]! = unpack 4060 12 (gen6 A B C D E F j) := by
  refine ⟨rfl, fun j hj => ?_⟩
  rcases j with _ | _ | _ | _ | _ | _ | j
  exacts [ha, hb, hc, hd, he, hf, absurd hj (by omega)]

theorem binds6 : g6A.size = 6 ∧ ∀ j < 6, g6A[j]! =
    unpack 4060 12 (gen6 RuG.A0 RuG.A1 RuG.C0 RuG.C1 RuG.Ns0 RuG.Ns1 j) := by
  rw [g6A]
  exact binds6' RuG.a0_eq RuG.a1_eq RuG.c0_eq RuG.c1_eq RuG.ns0_eq RuG.ns1_eq

theorem perms6' {A B C D E F AI BI CI DI EI FI : Nat} (ha : RuG.pk A AI = true)
    (hb : RuG.pk B BI = true) (hc : RuG.pk C CI = true) (hd : RuG.pk D DI = true)
    (he : RuG.pk E EI = true) (hf : RuG.pk F FI = true) :
    allN 6 (fun j => permOK 4060 12 (mask 12) (4060 * 12) (gen6 A B C D E F j)
      (gen6 AI BI CI DI EI FI j)) = true := by
  refine CFSG.KC.Misc.RuBase.allN_iff.2 fun j hj => ?_
  rcases j with _ | _ | _ | _ | _ | _ | j
  exacts [ha, hb, hc, hd, he, hf, absurd hj (by omega)]

theorem perms6 : allN 6 (fun j => permOK 4060 12 (mask 12) (4060 * 12)
    (gen6 RuG.A0 RuG.A1 RuG.C0 RuG.C1 RuG.Ns0 RuG.Ns1 j)
    (gen6 RuG.A0I RuG.A1I RuG.C0I RuG.C1I RuG.Ns0I RuG.Ns1I j)) = true :=
  perms6' RuG.pA0 RuG.pA1 RuG.pC0 RuG.pC1 RuG.pNs0 RuG.pNs1

theorem prepO : PRep 4060 12 (HR 6) (wG (otherZW.getD 0 [])) := by
  obtain ⟨e, hl⟩ := wordEqK_sound binds6 perms6 ch7229o
  have ea : wA (otherZW.getD 0 []) = unpack 4060 12 (HR 6) := by
    rw [wA, g6I_eq]
    exact e
  exact prep_of' ea (rep_wA hl)

theorem prepOA : PRep 4060 12 (HR 12) (abG (otherAW.getD 0 [])) := by
  obtain ⟨e, hl⟩ := wordEqK_sound (RuG.binds2 RuG.a0_eq RuG.a1_eq) (RuG.perms2 RuG.pA0 RuG.pA1)
    ch7229p
  have ea : abA (otherAW.getD 0 []) = unpack 4060 12 (HR 12) := by
    rw [abA, RuG.invs2]
    exact e
  exact prep_of' ea (rep_abA hl)

theorem getD_mem {l : List (List ℤ)} {i : Nat} (hi : i < l.length) : l.getD i [] ∈ l := by
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

theorem hWordsZ_length : hWordsZ.length = 4 := rfl

theorem hWordsA_length : hWordsA.length = 5 := rfl

theorem repZ {ρ : Nat} (hρ : ρ < 5) : ∃ r ∈ repsZG, PRep 4060 12 (HR (2 + ρ)) r := by
  rcases Nat.lt_or_ge ρ 4 with h4 | h4
  · have hc := cAll ρ h4
    unfold ch7229c_ at hc
    refine ⟨_, List.mem_append_left _ (List.mem_map.2 ⟨cosetWords.getD ρ [], ?_, rfl⟩),
      cjEq_sound (prep_H (i := ρ) (by omega)) prep_Z hc⟩
    rw [cosetWords, List.getD_append _ _ _ _ (by rw [hWordsZ_length]; exact h4)]
    exact getD_mem (by rw [hWordsZ_length]; exact h4)
  · obtain rfl : ρ = 4 := by omega
    exact ⟨_, List.mem_append_right _ (List.mem_map.2 ⟨_, getD_mem (by decide), rfl⟩), prepO⟩

theorem repA {ρ : Nat} (hρ : ρ < 6) : ∃ r ∈ repsAG, PRep 4060 12 (HR (7 + ρ)) r := by
  rcases Nat.lt_or_ge ρ 5 with h5 | h5
  · have hc := dAll ρ h5
    unfold ch7229d_ at hc
    have hH := prep_H (i := 4 + ρ) (by omega)
    have e5 : 4 + ρ + 1 = 5 + ρ := by omega
    rw [e5] at hH
    refine ⟨_, List.mem_append_left _ (List.mem_map.2 ⟨cosetWords.getD (4 + ρ) [], ?_, rfl⟩),
      cjEq_sound hH prep_A0 hc⟩
    rw [cosetWords, List.getD_append_right _ _ _ _ (by rw [hWordsZ_length]; omega),
      hWordsZ_length, Nat.add_sub_cancel_left]
    exact getD_mem (by rw [hWordsA_length]; exact h5)
  · obtain rfl : ρ = 5 := by omega
    exact ⟨_, List.mem_append_right _ (List.mem_map.2 ⟨_, getD_mem (by decide), rfl⟩), prepOA⟩

end Reps

theorem cLev
    {l a : Nat} (hl : l < 3) (ha : a < rcnt (RuCS.LR l)) :
    ∃ g ∈ ruC, PRep 4060 12 (RuCS.TR (roff 4060 48720 (RuCS.LR l) + a)) g := by
  obtain ⟨s, P⟩ := levT_prep RuCNF.bindsC RuCNF.pC RuCS.hl hl
  have hA : ChainArrays ruChainC ((ruField4060 1).extract 0 2) (ruField4060 1)
      (ruBaseArr 4060 ruCBase) (ruWordsArr 2 7 ruCDerivations) := ruChain_arrays ruChainC_check.1
  have hb : ruChainC.baseCount = 3 := rfl
  refine ⟨_, ?_, P a ha⟩
  rw [← ruChainC_sub]
  exact chain_levT_mem_original hA (by norm_num) ruChainC_check.1 (by rw [hb]; exact hl)
    (by rw [s]; exact ha)

theorem lLev
    {l a : Nat} (hl : l < 2) (ha : a < rcnt (RuLS.LR l)) :
    ∃ g ∈ ruL, PRep 4060 12 (RuLS.TR (roff 4060 48720 (RuLS.LR l) + a)) g := by
  obtain ⟨s, P⟩ := levT_prep RuL.binds RuL.perm RuLS.hl hl
  have hA : ChainArrays ruChainL ((ruField4060 5).extract 0 3) (ruField4060 5)
      (ruBaseArr 4060 ruLChainBase) (ruWordsArr 3 6 ruLChainDerivations) :=
    ruChain_arrays ruL_check.1
  have hb : ruChainL.baseCount = 2 := rfl
  refine ⟨_, ?_, P a ha⟩
  rw [← ruChainL_sub]
  exact chain_levT_mem_original hA (by norm_num) ruL_check.1 (by rw [hb]; exact hl)
    (by rw [s]; exact ha)

theorem cS_prod : rcnt (RuSqS.LR 0) * rcnt (RuSqS.LR 1) = 16 * 1024 := by
  rw [Nat.eq_of_beq_eq_true KernelMisc.RuInv.cnt0, Nat.eq_of_beq_eq_true KernelMisc.RuInv.cnt1]

theorem sq_apply {s : Equiv.Perm (Fin 4060)} (h2 : s ^ 2 = 1) (y : Fin 4060) : s (s y) = y := by
  rw [← Equiv.Perm.mul_apply, ← pow_two, h2]
  rfl

theorem conj_of_base
    {c s r : Equiv.Perm (Fin 4060)} (hc : c ∈ ruP) (hs : s ∈ ruP)
    (hr : r ∈ ruP) (h : ∀ b (hb : b < 4), c (s ⟨b, by omega⟩) = r (c ⟨b, by omega⟩)) :
    c * s * c⁻¹ = r := by
  have e : c * s = r * c := eq_of_base (ruP.mul_mem hc hs) (ruP.mul_mem hr hc) fun b hb => by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h b hb]
  rw [e, mul_inv_cancel_right]

theorem prod3_mem {H : Subgroup (Equiv.Perm (Fin 4060))} {a b c : Equiv.Perm (Fin 4060)}
    (ha : a ∈ H) (hb : b ∈ H) (hc : c ∈ H) : [a, b, c].prod ∈ H := by
  simp only [List.prod_cons, List.prod_nil, mul_one]
  exact H.mul_mem ha (H.mul_mem hb hc)

theorem prod2_mem {H : Subgroup (Equiv.Perm (Fin 4060))} {a b : Equiv.Perm (Fin 4060)}
    (ha : a ∈ H) (hb : b ∈ H) : [a, b].prod ∈ H := by
  simp only [List.prod_cons, List.prod_nil, mul_one]
  exact H.mul_mem ha hb

section Covers

theorem coverS {s : Equiv.Perm (Fin 4060)} (hs : s ∈ ruS) (h2 : s ^ 2 = 1) (h1 : s ≠ 1)
    (hz : s ≠ ruZ) : ∃ r ∈ repsZG, ∃ c ∈ ruC, c * s * c⁻¹ = r := by
  have hA := ruChainS4060_arrays
  have hsS : s ∈ ruChainS4060.originalSubgroup := by rw [ruChainS4060_sub]; exact hs
  have hm := mem_products_of_mem hA (by norm_num) ruInv_check.1 hsS
  rw [ruChainS4060_baseCount] at hm
  obtain ⟨i, hi, g₀, g₁, P0, P1, rfl⟩ := enum2 RuSq.bindsSq RuSq.permS RuSqS.hl hm
  rw [cS_prod] at hi
  have hpl : PL [RuSqS.TR (roff 4060 48720 (RuSqS.LR 0) + i / rcnt (RuSqS.LR 1)),
      RuSqS.TR (roff 4060 48720 (RuSqS.LR 1) + i % rcnt (RuSqS.LR 1))] [g₀, g₁] :=
    .cons P0 (.cons P1 .nil)
  have e : [g₀, g₁].prod = g₀ * g₁ := by simp
  rw [← e] at hs h2 h1 hz ⊢
  have hsP : [g₀, g₁].prod ∈ ruP := ruS_le hs
  have hck : ∀ q < 16, chkCov RuSqS.LR RuSqS.TR WS (HR 0)
      (k3C RuCS.TR (roff 4060 48720 (RuCS.LR 0)) (roff 4060 48720 (RuCS.LR 1))
        (roff 4060 48720 (RuCS.LR 2)) (rcnt (RuCS.LR 0)) (rcnt (RuCS.LR 1)) (rcnt (RuCS.LR 2))
        (fun r => HR (Nat.add 2 r)) 5) (1024 * q) 1024 = true := fun q hq => by
    have h := sAll q hq
    unfold ch7229s_ at h
    simp only [CFSG.KC.Misc.RuScan.strictB_eq] at h
    exact h
  rcases recK_sound hpl prepR0 (chkCov_all (K := 16) (cnt := 1024) hck i hi) with
    ⟨y, hy⟩ | hb | hb | hk
  · exact absurd (sq_apply h2 y) hy
  · exact absurd (eq_of_base hsP ruP.one_mem fun b hb' => by rw [hb b hb']; rfl) h1
  · exact absurd (eq_of_base hsP ruZ_mem fun b hb' => by rw [hb b hb']) hz
  · obtain ⟨ρ, hρ, a0, ha0, a1, ha1, a2, ha2, hcj⟩ := k3C_sound hk
    obtain ⟨c0, hc0, Q0⟩ := cLev (l := 0) (by norm_num) ha0
    obtain ⟨c1, hc1, Q1⟩ := cLev (l := 1) (by norm_num) ha1
    obtain ⟨c2, hc2, Q2⟩ := cLev (l := 2) (by norm_num) ha2
    obtain ⟨r, hrm, hR⟩ := repZ hρ
    have hcs := conjOK_sound hpl (.cons Q0 (.cons Q1 (.cons Q2 .nil))) hR hcj
    have hcC := prod3_mem hc0 hc1 hc2
    exact ⟨r, hrm, _, hcC, conj_of_base (ruC_le hcC) hsP (repsZG_mem r hrm) hcs⟩

theorem coverC {x : Equiv.Perm (Fin 4060)} (hx : x ∈ ruC) (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1)
    (hxz : x ≠ ruZ) : ∃ r ∈ repsZG, ∃ c ∈ ruC, c * x * c⁻¹ = r := by
  obtain ⟨c, hc, hs⟩ := CFSG.EvenSporadicStandard.RuStd.B2.exists_conj_mem_ruS_of_mem_ruC hx
    (orderOf_eq_prime hx2 hx1)
  have ex : x = c * (c⁻¹ * x * c) * c⁻¹ := by group
  have hcz : c * ruZ = ruZ * c := by
    have hm := (Subgroup.mem_inf.mp (ruC_le_centralizer hc)).2
    have := Subgroup.mem_centralizer_singleton_iff.mp hm
    first
    | exact this
    | exact this.symm
  have h2 : (c⁻¹ * x * c) ^ 2 = 1 := by
    have e : (c⁻¹ * x * c) ^ 2 = c⁻¹ * (x * x) * c := by
      rw [pow_two]
      group
    rw [e, ← pow_two, hx2]
    group
  have h1 : c⁻¹ * x * c ≠ 1 := fun e => hx1 (by rw [ex, e]; group)
  have hz : c⁻¹ * x * c ≠ ruZ := fun e => hxz (by rw [ex, e, hcz]; group)
  obtain ⟨r, hr, c', hc', e⟩ := coverS hs h2 h1 hz
  exact ⟨r, hr, c' * c⁻¹, ruC.mul_mem hc' (ruC.inv_mem hc), by rw [← e]; group⟩

end Covers

theorem lRec : ∀ i < 28 * 4160, recK [RuLS.TR (roff 4060 48720 (RuLS.LR 0) + i / rcnt (RuLS.LR 1)),
    RuLS.TR (roff 4060 48720 (RuLS.LR 1) + i % rcnt (RuLS.LR 1))] (HR 1)
      (k3L RuLS.TR (roff 4060 48720 (RuLS.LR 0)) (roff 4060 48720 (RuLS.LR 1))
        (rcnt (RuLS.LR 0)) (rcnt (RuLS.LR 1)) (fun r => HR (Nat.add 7 r)) 6) (WL i) = true := by
  refine chkCov_all (K := 28) (cnt := 4160) fun q hq => ?_
  have h := lAll q hq
  unfold ch7229l_ at h
  simp only [CFSG.KC.Misc.RuScan.strictB_eq] at h
  exact h

section CoverL

theorem lConj {ss : List Nat} {s : Equiv.Perm (Fin 4060)} {gs : List (Equiv.Perm (Fin 4060))}
    (hpl : PL ss gs) (hs : gs.prod = s) (hsP : s ∈ ruP) {r : Nat}
    (hk : k3L RuLS.TR (roff 4060 48720 (RuLS.LR 0)) (roff 4060 48720 (RuLS.LR 1))
      (rcnt (RuLS.LR 0)) (rcnt (RuLS.LR 1)) (fun r => HR (Nat.add 7 r)) 6 ss r = true) :
    ∃ r ∈ repsAG, ∃ c ∈ ruL, c * s * c⁻¹ = r := by
  obtain ⟨ρ, hρ, a0, ha0, a1, ha1, hcj⟩ := k3L_sound hk
  obtain ⟨c0, hc0, Q0⟩ := lLev (l := 0) (by norm_num) ha0
  obtain ⟨c1, hc1, Q1⟩ := lLev (l := 1) (by norm_num) ha1
  obtain ⟨r, hrm, hR⟩ := repA hρ
  have hcs := conjOK_sound hpl (.cons Q0 (.cons Q1 .nil)) hR hcj
  rw [hs] at hcs
  have hcL := prod2_mem hc0 hc1
  exact ⟨r, hrm, _, hcL, conj_of_base (ruL_le hcL) hsP (repsAG_mem r hrm) hcs⟩

theorem coverL_of {τ : Equiv.Perm (Fin 4060)} {T : Nat} {W : Nat → Nat}
    {K3 : List Nat → Nat → Bool} (hτ : τ ∈ ruP) (hT : PRep 4060 12 T τ)
    (hrec : ∀ i < 28 * 4160, recK [RuLS.TR (roff 4060 48720 (RuLS.LR 0) + i / rcnt (RuLS.LR 1)),
      RuLS.TR (roff 4060 48720 (RuLS.LR 1) + i % rcnt (RuLS.LR 1))] T K3 (W i) = true)
    (hK : ∀ (ss : List Nat) (gs : List (Equiv.Perm (Fin 4060))) (s : Equiv.Perm (Fin 4060))
      (r : Nat), PL ss gs → gs.prod = s → s ∈ ruP → K3 ss r = true →
        ∃ r ∈ repsAG, ∃ c ∈ ruL, c * s * c⁻¹ = r)
    {x : Equiv.Perm (Fin 4060)} (hx : x ∈ ruL) (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) (hxτ : x ≠ τ) :
    ∃ r ∈ repsAG, ∃ c ∈ ruL, c * x * c⁻¹ = r := by
  obtain ⟨i, hi, g₀, g₁, P0, P1, rfl⟩ := enumL hx
  have hpl : PL [RuLS.TR (roff 4060 48720 (RuLS.LR 0) + i / rcnt (RuLS.LR 1)),
      RuLS.TR (roff 4060 48720 (RuLS.LR 1) + i % rcnt (RuLS.LR 1))] [g₀, g₁] :=
    .cons P0 (.cons P1 .nil)
  have e : [g₀, g₁].prod = g₀ * g₁ := by simp
  rw [← e] at hx hx2 hx1 hxτ
  have hsP : [g₀, g₁].prod ∈ ruP := ruL_le hx
  rcases recK_sound hpl hT (hrec i hi) with ⟨y, hy⟩ | hb | hb | hk
  · exact absurd (sq_apply hx2 y) hy
  · exact absurd (eq_of_base hsP ruP.one_mem fun b hb' => by rw [hb b hb']; rfl) hx1
  · exact absurd (eq_of_base hsP hτ fun b hb' => by rw [hb b hb']) hxτ
  · exact hK _ _ _ _ hpl rfl hsP hk

theorem coverL {x : Equiv.Perm (Fin 4060)} (hx : x ∈ ruL) (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1)
    (hxa : x ≠ ruA0) : ∃ r ∈ repsAG, ∃ c ∈ ruL, c * x * c⁻¹ = r :=
  coverL_of ruA0_mem prepR1 lRec (fun _ _ _ _ hpl hs hsP hk => lConj hpl hs hsP hk) hx hx2 hx1 hxa

end CoverL

section Fix

theorem fixCnts : fixC (HR 6) = 0 ∧ fixC (HR 12) = 92 := by
  have h := ch7229f
  rw [Orb.bAnd_eq, Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem fixZ : ∀ w ∈ otherZW, (fixSet (wG w)).ncard = 0 := by
  intro w hw
  have hw' : w = otherZW.getD 0 [] := by
    rw [otherZW, List.mem_singleton] at hw
    exact hw
  rw [hw', ← length_fixedList_eq (rep_unpack prepO), ← fixC_eq prepO, fixCnts.1]

theorem fixA : ∀ w ∈ otherAW, (fixSet (abG w)).ncard = 92 := by
  intro w hw
  have hw' : w = otherAW.getD 0 [] := by
    rw [otherAW, List.mem_singleton] at hw
    exact hw
  rw [hw', ← length_fixedList_eq (rep_unpack prepOA), ← fixC_eq prepOA, fixCnts.2]

end Fix

end CertificateChecks.KernelMisc.RuCov

end
