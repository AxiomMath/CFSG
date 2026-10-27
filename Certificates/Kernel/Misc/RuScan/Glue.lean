
module

public import Certificates.Kernel.Misc.RuScan.H
public import Certificates.Kernel.Misc.RuScan.P3
public import Certificates.Kernel.Misc.RuScan.Bnd
public import Certificates.Kernel.Misc.RuScan.KB
public import Certificates.Kernel.Misc.RuScan.VB
public import Certificates.Kernel.Misc.RuScan.C0
public import Certificates.Kernel.Misc.RuScan.C1
public import Certificates.Kernel.Misc.RuScan.C2
public import Certificates.Kernel.Misc.RuScan.C3
public import Certificates.Kernel.Misc.RuScan.C6
public import Certificates.Kernel.Misc.RuScan.C7
public import Certificates.Kernel.Misc.RuScan.C8
public import Certificates.Kernel.Misc.RuScan.L0
public import Certificates.Kernel.Misc.RuScan.L1
public import Certificates.Kernel.Misc.RuScan.L8
public import Certificates.Kernel.SporSch.Ru.Gens
public import Certificates.Kernel.SporSch.Ru.LFacts
public import Certificates.Kernel.SporSch.Ru.CNFacts
public import CFSG.Certificates.Kernel.Misc.RuScanSound
public import CFSG.Quasithin.Vol2.KGFactC31RuBaseBase
public import CFSG.Quasithin.Vol2.KGFactC31RuScanData
public import CFSG.Sporadic.Schreier.RuCheckChains
public import CFSG.Sporadic.Schreier.RuCheckL
public import CFSG.Sporadic.Schreier.RuChainSpec
public import CFSG.Sporadic.Schreier.RuLocalFacts
import CFSG.Certificates.Kernel.Common.ForallTree
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.FactsB2Inputs
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Quasithin.Vol2.KGFactC31RuRefKBase
public import CFSG.Sporadic.HeldB.Common
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Schreier.RuLGroup
public import CFSG.Sporadic.Schreier.RuPair
public import CFSG.Sporadic.Schreier.RuSylow
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelMisc.RuScan

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Prim CFSG.KC.Misc.RuInv
  CFSG.KC.Misc.RuInv.P CFSG.KC.Misc.RuBase CFSG.KC.Misc.RuScan CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.RuSchreier CFSG.Quasithin.KGC31
  CFSG.Quasithin.KGC31.Ru CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.RuLines

#kc_forall_tree hAll (fun i => ch7230h_ i = true) 9 CertificateChecks.KernelMisc.RuScan.ch7230h_
#kc_forall_tree c0All (fun q => ch7230c0_ q = true) 60 CertificateChecks.KernelMisc.RuScan.ch7230c0_
#kc_forall_tree c1All (fun q => ch7230c1_ q = true) 60 CertificateChecks.KernelMisc.RuScan.ch7230c1_
#kc_forall_tree c2All (fun q => ch7230c2_ q = true) 60 CertificateChecks.KernelMisc.RuScan.ch7230c2_
#kc_forall_tree c3All (fun q => ch7230c3_ q = true) 60 CertificateChecks.KernelMisc.RuScan.ch7230c3_
#kc_forall_tree c6All (fun q => ch7230c6_ q = true) 28 CertificateChecks.KernelMisc.RuScan.ch7230c6_
#kc_forall_tree c7All (fun q => ch7230c7_ q = true) 28 CertificateChecks.KernelMisc.RuScan.ch7230c7_
#kc_forall_tree c8All (fun q => ch7230c8_ q = true) 28 CertificateChecks.KernelMisc.RuScan.ch7230c8_
#kc_forall_tree l0All (fun q => ch7230l0_ q = true) 60 CertificateChecks.KernelMisc.RuScan.ch7230l0_
#kc_forall_tree l1All (fun q => ch7230l1_ q = true) 60 CertificateChecks.KernelMisc.RuScan.ch7230l1_
#kc_forall_tree l2All (fun q => ch7230l2_ q = true) 60 CertificateChecks.KernelMisc.RuScan.ch7230l2_
#kc_forall_tree l3All (fun q => ch7230l3_ q = true) 60 CertificateChecks.KernelMisc.RuScan.ch7230l3_
#kc_forall_tree l8All (fun q => ch7230l8_ q = true) 28 CertificateChecks.KernelMisc.RuScan.ch7230l8_
#kc_forall_tree b0All (fun q => ch7230b0_ q = true) 15 CertificateChecks.KernelMisc.RuScan.ch7230b0_
#kc_forall_tree b1All (fun q => ch7230b1_ q = true) 15 CertificateChecks.KernelMisc.RuScan.ch7230b1_
#kc_forall_tree b2All (fun q => ch7230b2_ q = true) 15 CertificateChecks.KernelMisc.RuScan.ch7230b2_
#kc_forall_tree b3All (fun q => ch7230b3_ q = true) 15 CertificateChecks.KernelMisc.RuScan.ch7230b3_
#kc_forall_tree b6All (fun q => ch7230b6_ q = true) 7 CertificateChecks.KernelMisc.RuScan.ch7230b6_
#kc_forall_tree b7All (fun q => ch7230b7_ q = true) 7 CertificateChecks.KernelMisc.RuScan.ch7230b7_
#kc_forall_tree b8All (fun q => ch7230b8_ q = true) 7 CertificateChecks.KernelMisc.RuScan.ch7230b8_
#kc_forall_tree k0All (fun q => ch7230k0_ q = true) 96 CertificateChecks.KernelMisc.RuScan.ch7230k0_
#kc_forall_tree k1All (fun q => ch7230k1_ q = true) 34 CertificateChecks.KernelMisc.RuScan.ch7230k1_
#kc_forall_tree k2All (fun q => ch7230k2_ q = true) 2 CertificateChecks.KernelMisc.RuScan.ch7230k2_
#kc_forall_tree k3All (fun q => ch7230k3_ q = true) 12 CertificateChecks.KernelMisc.RuScan.ch7230k3_
#kc_forall_tree k8All (fun q => ch7230k8_ q = true) 3 CertificateChecks.KernelMisc.RuScan.ch7230k8_

@[expose] def NoBad (y τ : Equiv.Perm (Fin 4060)) : Prop :=
  (∀ e ∈ [125, 7, 13, 29], y ^ e ≠ 1) ∨
    ∃ j : Nat, τ * (y ^ j * τ * (y ^ j)⁻¹) ≠ y ^ j * τ * (y ^ j)⁻¹ * τ

@[expose] def LeafAt (V : Nat → Nat) (l : Nat) (y τ : Equiv.Perm (Fin 4060)) : Prop :=
  1 ≤ V (64 + 32 * l + 28) ∧ V (64 + 32 * l + 28) ≤ 7 ∧ ∀ b (hb : b < 4),
    (∀ j, 1 ≤ j → j < V (64 + 32 * l + 28) →
      (((y ^ j * τ * (y ^ j)⁻¹) ⟨b, by omega⟩ : Fin 4060) : Nat) =
        V (64 + 32 * l + 4 * (j - 1) + b)) ∧
    (((y ^ V (64 + 32 * l + 28) * τ * (y ^ V (64 + 32 * l + 28))⁻¹) ⟨b, by omega⟩ : Fin 4060) :
      Nat) = (τ ⟨b, by omega⟩ : Nat)

theorem prep_of' {a : Array Nat} {P : Nat} {g : Equiv.Perm (Fin 4060)}
    (ha : a = unpack 4060 12 P) (h : Rep 4060 a g) : PRep 4060 12 P g := by
  subst ha
  exact prep_of_rep h

section Prep

theorem prep_A0 : PRep 4060 12 (RuT4060.L 0) ruA0 := prep_of' RuG.a0_eq rep_ruA0

theorem prep_Z : PRep 4060 12 (HP 0) ruZ := by
  rw [Nat.eq_of_beq_eq_true ch7230hz]
  exact prep_of' RuG.z_eq rep_ruZ

theorem prep_H {i : Nat} (hi : i < 9) :
    PRep 4060 12 (HP (i + 1)) (abG (cosetWords.getD i [])) := by
  have h := hAll i hi
  unfold ch7230h_ at h
  obtain ⟨e, hl⟩ := wordEqK_sound (RuG.binds2 RuG.a0_eq RuG.a1_eq) (RuG.perms2 RuG.pA0 RuG.pA1) h
  have ea : abA (cosetWords.getD i []) = unpack 4060 12 (HP (i + 1)) := by
    rw [abA, RuG.invs2]
    exact e
  exact prep_of' ea (rep_abA hl)

end Prep

theorem rec_sound {ys : List Nat} {gs : List (Equiv.Perm (Fin 4060))} (hpl : PL ys gs) {T : Nat}
    {τ : Equiv.Perm (Fin 4060)} (hT : PRep 4060 12 T τ) {Kh V : Nat → Nat} {r : Nat}
    (hB : witB r = true) (hW : Nat.land r 3 ≠ 2 → witK ys T r = true)
    (hL : Nat.land r 3 = 2 → ∃ p, (∀ k < 28, Kh (32 * p + k) < 4060) ∧
      leafOK ys T Kh V (r >>> 2) p = true) :
    NoBad gs.prod τ ∨ ∃ l, LeafAt V l gs.prod τ := by
  by_cases hr : Nat.land r 3 = 2
  · obtain ⟨p, hK, hc⟩ := hL hr
    exact Or.inr ⟨_, leafOK_sound hpl hT hK hc⟩
  · exact Or.inl (witK_sound hpl hT hB (hW hr))

theorem chkL3_all {LR TR W Kh V : Nat → Nat} {H T K cnt : Nat}
    (h : ∀ q < K, chkL3 LR TR W Kh V H T (cnt * q) cnt (V (q + 1)) (V q) = true) :
    ∀ i < K * cnt, Nat.land (W i) 3 = 2 → ∃ p < V (i / cnt + 1),
      leafOK [H, TR (roff 4060 48720 (LR 0) + i / rcnt (LR 2) / rcnt (LR 1)),
        TR (roff 4060 48720 (LR 1) + i / rcnt (LR 2) % rcnt (LR 1)),
        TR (roff 4060 48720 (LR 2) + i % rcnt (LR 2))] T Kh V (W i >>> 2) p = true := by
  intro i hi hr
  obtain ⟨hq, hd, e⟩ := chunk_of hi
  have := chkL3_sound (h _ hq) _ hd
  rw [e] at this
  exact this hr

theorem chkL2_all {LR TR W Kh V : Nat → Nat} {H T K cnt : Nat}
    (h : ∀ q < K, chkL2 LR TR W Kh V H T (cnt * q) cnt (V (q + 1)) (V q) = true) :
    ∀ i < K * cnt, Nat.land (W i) 3 = 2 → ∃ p < V (i / cnt + 1),
      leafOK [H, TR (roff 4060 48720 (LR 0) + i / rcnt (LR 1)),
        TR (roff 4060 48720 (LR 1) + i % rcnt (LR 1))] T Kh V (W i >>> 2) p = true := by
  intro i hi hr
  obtain ⟨hq, hd, e⟩ := chunk_of hi
  have := chkL2_sound (h _ hq) _ hd
  rw [e] at this
  exact this hr

theorem hints_lt {Kh : Nat → Nat} {M N p : Nat} (hK : ∀ i < M, Kh i < 4060) (hN : 32 * N ≤ M)
    (hp : p < N) : ∀ k < 28, Kh (32 * p + k) < 4060 :=
  fun k hk => hK _ (by omega)

theorem vb_all {V : Nat → Nat} {n m : Nat} (h : allN n (fun q => Nat.ble (V (Nat.succ q)) m) = true) :
    ∀ q < n, V (q + 1) ≤ m :=
  fun q hq => Nat.le_of_ble_eq_true (CFSG.KC.Misc.RuBase.allN_iff.1 h q hq)

section CScan

theorem cC_prod : rcnt (RuCS.LR 0) * rcnt (RuCS.LR 1) * rcnt (RuCS.LR 2) = 60 * 4096 := by
  rw [Nat.eq_of_beq_eq_true RuCNF.cC0, Nat.eq_of_beq_eq_true RuCNF.cC1,
    Nat.eq_of_beq_eq_true RuCNF.cC2]

theorem scanC {W Kh V : Nat → Nat} {H M : Nat} {h : Equiv.Perm (Fin 4060)}
    (hH : PRep 4060 12 H h)
    (hck : ∀ q < 60, chk3D RuCS.LR RuCS.TR W H (HP 0) (4096 * q) 4096 = true)
    (hbd : ∀ q < 15, bndK W (16384 * q) 16384 = true)
    (hlf : ∀ q < 60, chkL3 RuCS.LR RuCS.TR W Kh V H (HP 0) (4096 * q) 4096 (V (q + 1)) (V q) =
      true)
    (hK : ∀ i < M, Kh i < 4060) (hvb : ∀ q < 60, 32 * V (q + 1) ≤ M)
    {c : Equiv.Perm (Fin 4060)} (hc : c ∈ ruC) :
    NoBad (h * c) ruZ ∨ ∃ l, LeafAt V l (h * c) ruZ := by
  have hA : ChainArrays ruChainC ((ruField4060 1).extract 0 2) (ruField4060 1)
      (ruBaseArr 4060 ruCBase) (ruWordsArr 2 7 ruCDerivations) := ruChain_arrays ruChainC_check.1
  have hcC : c ∈ ruChainC.originalSubgroup := by rw [ruChainC_sub]; exact hc
  have hm := mem_products_of_mem hA (by norm_num) ruChainC_check.1 hcC
  rw [show ruChainC.baseCount = 3 from rfl] at hm
  obtain ⟨i, hi, g₀, g₁, g₂, P0, P1, P2, rfl⟩ := enum3 RuCNF.bindsC RuCNF.pC RuCS.hl hm
  rw [cC_prod] at hi
  have hpl : PL [H, RuCS.TR (roff 4060 48720 (RuCS.LR 0) + i / rcnt (RuCS.LR 2) / rcnt (RuCS.LR 1)),
      RuCS.TR (roff 4060 48720 (RuCS.LR 1) + i / rcnt (RuCS.LR 2) % rcnt (RuCS.LR 1)),
      RuCS.TR (roff 4060 48720 (RuCS.LR 2) + i % rcnt (RuCS.LR 2))] [h, g₀, g₁, g₂] :=
    .cons hH (.cons P0 (.cons P1 (.cons P2 .nil)))
  have e : [h, g₀, g₁, g₂].prod = h * (g₀ * g₁ * g₂) := by simp [mul_assoc]
  rw [← e]
  refine rec_sound (Kh := Kh) hpl prep_Z (bnd_all hbd i (by omega)) (chk3D_all hck i hi)
    fun hr => ?_
  obtain ⟨p, hp, hc⟩ := chkL3_all hlf i hi hr
  have hq : i / 4096 < 60 := by omega
  exact ⟨p, hints_lt hK (hvb _ hq) hp, hc⟩

theorem scan0 {c : Equiv.Perm (Fin 4060)} (hc : c ∈ ruC) :
    NoBad (abG (cosetWords.getD 0 []) * c) ruZ ∨
      ∃ l, LeafAt V0 l (abG (cosetWords.getD 0 []) * c) ruZ :=
  scanC (M := 96 * 8192) (prep_H (i := 0) (by norm_num)) c0All b0All l0All
    (kbnd_all (K := 96) (cnt := 8192) k0All)
    (fun q hq => by have := vb_all ch7230v0 q hq; omega) hc

theorem scan1 {c : Equiv.Perm (Fin 4060)} (hc : c ∈ ruC) :
    NoBad (abG (cosetWords.getD 1 []) * c) ruZ ∨
      ∃ l, LeafAt V1 l (abG (cosetWords.getD 1 []) * c) ruZ :=
  scanC (M := 34 * 8192) (prep_H (i := 1) (by norm_num)) c1All b1All l1All
    (kbnd_all (K := 34) (cnt := 8192) k1All)
    (fun q hq => by have := vb_all ch7230v1 q hq; omega) hc

theorem scan2 {c : Equiv.Perm (Fin 4060)} (hc : c ∈ ruC) :
    NoBad (abG (cosetWords.getD 2 []) * c) ruZ ∨
      ∃ l, LeafAt V2 l (abG (cosetWords.getD 2 []) * c) ruZ :=
  scanC (M := 2 * 8192) (prep_H (i := 2) (by norm_num)) c2All b2All l2All
    (kbnd_all (K := 2) (cnt := 8192) k2All)
    (fun q hq => by have := vb_all ch7230v2 q hq; omega) hc

theorem scan3 {c : Equiv.Perm (Fin 4060)} (hc : c ∈ ruC) :
    NoBad (abG (cosetWords.getD 3 []) * c) ruZ ∨
      ∃ l, LeafAt V3 l (abG (cosetWords.getD 3 []) * c) ruZ :=
  scanC (M := 12 * 8192) (prep_H (i := 3) (by norm_num)) c3All b3All l3All
    (kbnd_all (K := 12) (cnt := 8192) k3All)
    (fun q hq => by have := vb_all ch7230v3 q hq; omega) hc

end CScan

section LScan

theorem cL_prod : rcnt (RuLS.LR 0) * rcnt (RuLS.LR 1) = 28 * 4160 := by
  rw [Nat.eq_of_beq_eq_true RuL.cnt0, Nat.eq_of_beq_eq_true RuL.cnt1]

theorem enumL {c : Equiv.Perm (Fin 4060)} (hc : c ∈ ruL) :
    ∃ i < 28 * 4160, ∃ g₀ g₁ : Equiv.Perm (Fin 4060),
      PRep 4060 12 (RuLS.TR (roff 4060 48720 (RuLS.LR 0) + i / rcnt (RuLS.LR 1))) g₀ ∧
      PRep 4060 12 (RuLS.TR (roff 4060 48720 (RuLS.LR 1) + i % rcnt (RuLS.LR 1))) g₁ ∧
      c = g₀ * g₁ := by
  have hA : ChainArrays ruChainL ((ruField4060 5).extract 0 3) (ruField4060 5)
      (ruBaseArr 4060 ruLChainBase) (ruWordsArr 3 6 ruLChainDerivations) :=
    ruChain_arrays ruL_check.1
  have hcL : c ∈ ruChainL.originalSubgroup := by rw [ruChainL_sub]; exact hc
  have hm := mem_products_of_mem hA (by norm_num) ruL_check.1 hcL
  rw [show ruChainL.baseCount = 2 from rfl] at hm
  obtain ⟨i, hi, g₀, g₁, P0, P1, rfl⟩ := enum2 RuL.binds RuL.perm RuLS.hl hm
  rw [cL_prod] at hi
  exact ⟨i, hi, g₀, g₁, P0, P1, rfl⟩

theorem scanL {W : Nat → Nat} {H : Nat} {h : Equiv.Perm (Fin 4060)} (hH : PRep 4060 12 H h)
    (hck : ∀ q < 28, chk2 RuLS.LR RuLS.TR W H (RuT4060.L 0) (4160 * q) 4160 = true)
    (hbd : ∀ q < 7, bndK W (16640 * q) 16640 = true) {c : Equiv.Perm (Fin 4060)}
    (hc : c ∈ ruL) : NoBad (h * c) ruA0 := by
  obtain ⟨i, hi, g₀, g₁, P0, P1, rfl⟩ := enumL hc
  have hpl : PL [H, RuLS.TR (roff 4060 48720 (RuLS.LR 0) + i / rcnt (RuLS.LR 1)),
      RuLS.TR (roff 4060 48720 (RuLS.LR 1) + i % rcnt (RuLS.LR 1))] [h, g₀, g₁] :=
    .cons hH (.cons P0 (.cons P1 .nil))
  have e : [h, g₀, g₁].prod = h * (g₀ * g₁) := by simp [mul_assoc]
  rw [← e]
  exact witK_sound hpl prep_A0 (bnd_all hbd i (by omega)) (chk2_all hck i hi)

theorem scan6 {c : Equiv.Perm (Fin 4060)} (hc : c ∈ ruL) :
    NoBad (abG (cosetWords.getD 6 []) * c) ruA0 :=
  scanL (prep_H (i := 6) (by norm_num)) c6All b6All hc

theorem scan7 {c : Equiv.Perm (Fin 4060)} (hc : c ∈ ruL) :
    NoBad (abG (cosetWords.getD 7 []) * c) ruA0 :=
  scanL (prep_H (i := 7) (by norm_num)) c7All b7All hc

theorem scan8 {c : Equiv.Perm (Fin 4060)} (hc : c ∈ ruL) :
    NoBad (abG (cosetWords.getD 8 []) * c) ruA0 ∨
      ∃ l, LeafAt V8 l (abG (cosetWords.getD 8 []) * c) ruA0 := by
  obtain ⟨i, hi, g₀, g₁, P0, P1, rfl⟩ := enumL hc
  have hpl : PL [HP 9, RuLS.TR (roff 4060 48720 (RuLS.LR 0) + i / rcnt (RuLS.LR 1)),
      RuLS.TR (roff 4060 48720 (RuLS.LR 1) + i % rcnt (RuLS.LR 1))]
      [abG (cosetWords.getD 8 []), g₀, g₁] :=
    .cons (prep_H (i := 8) (by norm_num)) (.cons P0 (.cons P1 .nil))
  have e : [abG (cosetWords.getD 8 []), g₀, g₁].prod = abG (cosetWords.getD 8 []) * (g₀ * g₁) := by
    simp [mul_assoc]
  rw [← e]
  have hK := kbnd_all (K := 3) (cnt := 8192) k8All
  refine rec_sound (Kh := K8) hpl prep_A0 (bnd_all (K := 7) (cnt := 16640) b8All i (by omega))
    (chk2D_all (K := 28) (cnt := 4160) c8All i hi) fun hr => ?_
  obtain ⟨p, hp, hc⟩ := chkL2_all (K := 28) (cnt := 4160) l8All i hi hr
  have hq : i / 4160 < 28 := by omega
  have hv := vb_all ch7230v8 _ hq
  exact ⟨p, hints_lt (M := 3 * 8192) hK (by omega) hp, hc⟩

theorem rep_of_eqA' {t u : Array Nat} {g : Equiv.Perm (Fin 4060)} (hu : Rep 4060 u g)
    (he : eqA 4060 t u = true) : Rep 4060 t g := fun x => by
  rw [eqA, allLt_iff] at he
  have := he x x.2
  rw [beq_iff_eq] at this
  rw [this, hu x]

theorem prep_LGen {l : Nat} (hl : l < 3) :
    PRep 4060 12 (RuT4060.L (Nat.add 39 l)) (ruLGens.getD l 1) := by
  refine prep_of' ((RuL.field_get (by omega)).trans (row4060 (by omega))) ?_
  exact rep_of_eqA' (rep_ruLGens l hl) (ruL_check.2.2.1 l hl)

theorem closure_LGen :
    Subgroup.closure {g | ∃ l < 3, ruLGens.getD l 1 = g} = ruL := by
  rw [ruL]
  congr 1
  ext g
  rw [ruLGens_eq]
  simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨l, hl, rfl⟩
    rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2) with rfl | rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by norm_num, rfl⟩
    · exact ⟨1, by norm_num, rfl⟩
    · exact ⟨2, by norm_num, rfl⟩

theorem scan45 {i : Nat} (hi : i = 4 ∨ i = 5) {c : Equiv.Perm (Fin 4060)} (hc : c ∈ ruL) :
    ∀ e ∈ [125, 7, 13, 29], (abG (cosetWords.getD i []) * c) ^ e ≠ 1 := by
  have hp : p3K (HP (i + 1)) (RuT4060.L 0) (fun l => RuT4060.L (Nat.add 39 l)) 3 = true := by
    rcases hi with rfl | rfl
    · exact ch7230p3_4
    · exact ch7230p3_5
  have hK : ∀ c ∈ Subgroup.closure {g | ∃ l < 3, ruLGens.getD l 1 = g}, c * ruA0 = ruA0 * c := by
    intro c hc
    rw [closure_LGen] at hc
    exact Subgroup.mem_centralizer_singleton_iff.mp (ruL_le_centralizer hc).2
  have h := p3_ne_one (prep_H (i := i) (by omega)) prep_A0 (fun l hl => prep_LGen hl) hp hK c
    (by rw [closure_LGen]; exact hc)
  intro e he
  apply h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;> norm_num

end LScan

theorem eq_of_base
    {g g' : Equiv.Perm (Fin 4060)} (hg : g ∈ ruP) (hg' : g' ∈ ruP)
    (h : ∀ b (hb : b < 4), ((g ⟨b, by omega⟩ : Fin 4060) : Nat) = (g' ⟨b, by omega⟩ : Nat)) :
    g = g' := by
  have h1 := ruJoin_baseFaithful (g'⁻¹ * g) (ruP.mul_mem (ruP.inv_mem hg') hg) fun x hx => by
    have hx4 : (x : Nat) < 4 := by
      simp only [ruJoinBase, List.mem_cons, List.not_mem_nil, or_false] at hx
      omega
    have e : g x = g' x := Fin.ext (h x hx4)
    rw [Equiv.Perm.mul_apply, e]
    simp
  calc g = g' * (g'⁻¹ * g) := by group
    _ = g' := by rw [h1, mul_one]

theorem conj_mem {y τ : Equiv.Perm (Fin 4060)} (hy : y ∈ ruP) (hτ : τ ∈ ruP) (j : Nat) :
    y ^ j * τ * (y ^ j)⁻¹ ∈ ruP :=
  ruP.mul_mem (ruP.mul_mem (ruP.pow_mem hy j) hτ) (ruP.inv_mem (ruP.pow_mem hy j))

section Leaves

theorem leaf_period {V : Nat → Nat} {l : Nat} {y τ : Equiv.Perm (Fin 4060)} (hy : y ∈ ruP)
    (hτ : τ ∈ ruP) (h : LeafAt V l y τ) :
    y ^ V (64 + 32 * l + 28) * τ * (y ^ V (64 + 32 * l + 28))⁻¹ = τ :=
  eq_of_base (conj_mem hy hτ _) hτ fun b hb => (h.2.2 b hb).2

theorem leaf_eq {V : Nat → Nat} {l : Nat} {y y' τ : Equiv.Perm (Fin 4060)} (hy : y ∈ ruP)
    (hy' : y' ∈ ruP) (hτ : τ ∈ ruP) (h : LeafAt V l y τ) (h' : LeafAt V l y' τ) {j : Nat}
    (hj : j < V (64 + 32 * l + 28)) :
    y ^ j * τ * (y ^ j)⁻¹ = y' ^ j * τ * (y' ^ j)⁻¹ := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp
  · exact eq_of_base (conj_mem hy hτ _) (conj_mem hy' hτ _) fun b hb =>
      ((h.2.2 b hb).1 j hj0 hj).trans ((h'.2.2 b hb).1 j hj0 hj).symm

end Leaves

end CertificateChecks.KernelMisc.RuScan

end
