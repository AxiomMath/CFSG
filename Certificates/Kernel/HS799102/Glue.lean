module

public import Certificates.Kernel.HS799102.ClassChecks
public import Certificates.Kernel.HS799102.ClassChecks3
public import Certificates.Kernel.HS799102.ChainChecks
public import Certificates.Kernel.HS799102.GlueChecks
public import Certificates.Kernel.HS100.Chain
public import CFSG.Certificates.Kernel.PCentExtCheck
public import CFSG.RankThree.Native.HSMcLSmall
public import CFSG.RankThree.Native.HSMcLFiveCentralizers
import CFSG.Certificates.Kernel.Misc.ArrEnumUnpack
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.PK.Perm.Inv
import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHS799102

open CFSG.KC.PCent CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin
open CFSG.KC.Misc.ArrEnum (pp_of_permB)
open CFSG.KC.Misc.HexFlat (hexTable3_sound)
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.RankThree.PartTwo.Sec21.Holder214Theta
open scoped commutatorElement

theorem gl_sz : CFSG.KS.Raw.szOK 100 7 = true := by quickRfl

theorem rep_toPerm {p : Nat} (hp : PP 100 7 p) : Rep 100 (unpack 100 7 p) (toPerm 100 7 p) :=
  fun x => by rw [Orb.unpack_get x.2, toPerm_apply hp]

theorem permOfArr_unpack {p : Nat} (hp : PP 100 7 p) :
    permOfArr 100 (unpack 100 7 p) = toPerm 100 7 p := by
  have h := rep_toPerm hp
  have hc : (∀ i < 100, (unpack 100 7 p)[i]! < 100) ∧
      ∀ i < 100, ∀ j < 100, (unpack 100 7 p)[i]! = (unpack 100 7 p)[j]! → i = j :=
    ⟨fun i hi => h.lt hi, fun i hi j hj hij => by
      rw [h.apply hi, h.apply hj] at hij
      have := (toPerm 100 7 p).injective (Fin.ext hij)
      simpa using this⟩
  ext x
  rw [permOfArr, dite_eq_left hc]
  change (unpack 100 7 p)[(x : ℕ)]! = _
  exact h x

theorem band {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  revert h
  cases a <;> cases b <;> decide

theorem pp_pG : ∀ k < 4, PP 100 7 (pG k) := fun k hk =>
  pp_of_permB gl_sz (Orb.allN_iff.1 (band ch799102_perm).1 k hk)

theorem pp_TH : ∀ k < 9, PP 100 7 (TH.F k) := fun k hk =>
  pp_of_permB gl_sz (Orb.allN_iff.1 (of_decide_eq_true (band ch799102_perm).2) k hk)

theorem tperm : (∀ k < 21, PP 100 7 (TV1.F k)) ∧ (∀ k < 23, PP 100 7 (TV2.F k)) ∧
    (∀ k < 21, PP 100 7 (TV3.F k)) := by
  obtain ⟨h12, h3⟩ := band ch799102_tperm
  obtain ⟨h1, h2⟩ := band h12
  exact ⟨fun k hk => pp_of_permB gl_sz (Orb.allN_iff.1 h1 k hk),
    fun k hk => pp_of_permB gl_sz (Orb.allN_iff.1 h2 k hk),
    fun k hk => pp_of_permB gl_sz (Orb.allN_iff.1 (of_decide_eq_true h3) k hk)⟩

theorem closure_pG : Subgroup.closure (gens 100 7 pG 4) = hs100P := by
  have h := ch799102_bind
  unfold pGBind at h
  obtain ⟨h012, h3⟩ := band h
  obtain ⟨h01, h2⟩ := band h012
  obtain ⟨h0, h1⟩ := band h01
  have hA : toPerm 100 7 (pG 0) = hs100A := by
    rw [hs100A, CertificateChecks.KernelHS100.hs100Arr_eq 0 (by norm_num),
      ← Nat.eq_of_beq_eq_true h0, permOfArr_unpack (pp_pG 0 (by norm_num))]
  have hB : toPerm 100 7 (pG 1) = hs100B := by
    rw [hs100B, CertificateChecks.KernelHS100.hs100Arr_eq 1 (by norm_num),
      ← Nat.eq_of_beq_eq_true h1, permOfArr_unpack (pp_pG 1 (by norm_num))]
  have hpa : PP 100 7 (CertificateChecks.KernelHS100.HP.F 0) := Nat.eq_of_beq_eq_true h0 ▸ pp_pG 0 (by norm_num)
  have hpb : PP 100 7 (CertificateChecks.KernelHS100.HP.F 1) := Nat.eq_of_beq_eq_true h1 ▸ pp_pG 1 (by norm_num)
  have hA' : toPerm 100 7 (pG 2) = hs100A⁻¹ := by
    rw [Nat.eq_of_beq_eq_true h2, toPerm_inv hpa, ← hA, Nat.eq_of_beq_eq_true h0]
  have hB' : toPerm 100 7 (pG 3) = hs100B⁻¹ := by
    rw [Nat.eq_of_beq_eq_true h3, toPerm_inv hpb, ← hB, Nat.eq_of_beq_eq_true h1]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have ha : hs100A ∈ hs100P := Subgroup.subset_closure (Set.mem_insert _ _)
    have hb : hs100B ∈ hs100P := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    interval_cases k
    · rw [hA]; exact ha
    · rw [hB]; exact hb
    · rw [hA']; exact hs100P.inv_mem ha
    · rw [hB']; exact hs100P.inv_mem hb
  · rw [hs100P, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · rw [← hA]; exact gen_mem (by norm_num)
    · rw [← hB]; exact gen_mem (by norm_num)

theorem toPerm_v (k : Nat) (hk : k < 9) : toPerm 100 7 (TH.F k) = permOfArr 100 (hsThArr k) := by
  rw [hsThArr, TH.eq, hexTable3_sound TH.all k hk, permOfArr_unpack (pp_TH k hk)]

theorem mem_of_memK {g v : Nat} (hg : PP 100 7 g) (hv : PP 100 7 v) (h : memK g v = true) :
    toPerm 100 7 g ∈ Subgroup.closure (gens 100 7 pG 4) ⊓ Subgroup.centralizer {toPerm 100 7 v} := by
  unfold memK at h
  obtain ⟨h1, h2⟩ := band h
  have h := And.intro h1 (Nat.eq_of_beq_eq_true h2)
  refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  · rw [closure_pG]
    exact mem_hs100P_of_sift (rep_toPerm hg) (CertificateChecks.KernelHS100.siftP rfl h.1)
  · rw [← toPerm_mul hv hg, ← toPerm_mul hg hv, h.2]

theorem commK_eq (x y : Nat) : commK x y = commP 100 7 x y := rfl

theorem lens : R1.length = 1100 ∧ R2.length = 1100 ∧ R3.length = 15400 := by
  obtain ⟨h12, h3⟩ := band ch799102_len
  obtain ⟨h1, h2⟩ := band h12
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2,
    Nat.eq_of_beq_eq_true (of_decide_eq_true h3)⟩

theorem nprods : (N1.map fun lv => lv.2.2.2.length).prod = 40320 ∧
    (N2.map fun lv => lv.2.2.2.length).prod = 40320 ∧
    (N3.map fun lv => lv.2.2.2.length).prod = 2880 := by
  obtain ⟨h12, h3⟩ := band ch799102_nprods
  obtain ⟨h1, h2⟩ := band h12
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3⟩


theorem card_pG (r m : Nat) (h : r * m = 44352000) :
    Nat.card (Subgroup.closure (gens 100 7 pG 4)) = r * m := by
  rw [closure_pG, card_hs100P, h]

theorem mem_parts {F : Nat → Nat} {nF o o' ng v : Nat} (hF : ∀ k < nF, PP 100 7 (F k))
    (hv : PP 100 7 v) (hlt : o + ng ≤ nF) (hlt' : o' + 4 ≤ nF)
    (h : (allN ng (fun k => memK (F (Nat.add o k)) v) &&
      allN 4 (fun j => memK (F (Nat.add o' j)) v)) = true) :
    (∀ k < ng, PP 100 7 (F (o + k)) ∧
      toPerm 100 7 (F (o + k)) ∈ Subgroup.closure (gens 100 7 pG 4) ∧
      toPerm 100 7 (F (o + k)) * toPerm 100 7 v = toPerm 100 7 v * toPerm 100 7 (F (o + k))) ∧
    ∀ k < 2, ∃ a b, PP 100 7 a ∧ PP 100 7 b ∧
      toPerm 100 7 a ∈ Subgroup.closure (gens 100 7 pG 4) ⊓
        Subgroup.centralizer {toPerm 100 7 v} ∧
      toPerm 100 7 b ∈ Subgroup.closure (gens 100 7 pG 4) ⊓
        Subgroup.centralizer {toPerm 100 7 v} ∧
      commP 100 7 (F (Nat.add o' (Nat.mul 2 k))) (F (Nat.add o' (Nat.add (Nat.mul 2 k) 1))) =
        commP 100 7 a b := by
  have h := band h
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · have hp := hF (o + k) (by omega)
    have hm := mem_of_memK hp hv (Orb.allN_iff.1 h.1 k hk)
    exact ⟨hp, (Subgroup.mem_inf.1 hm).1,
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hm).2⟩
  · have ha := hF (o' + 2 * k) (by omega)
    have hb := hF (o' + (2 * k + 1)) (by omega)
    exact ⟨_, _, ha, hb, mem_of_memK ha hv (Orb.allN_iff.1 h.2 (2 * k) (by omega)),
      mem_of_memK hb hv (Orb.allN_iff.1 h.2 (2 * k + 1) (by omega)), rfl⟩

theorem o2_v1 : ∀ Q : Subgroup (Equiv.Perm (Fin 100)), IsPGroup 2 Q →
    Q ≤ ⁅hs100P ⊓ Subgroup.centralizer {permOfArr 100 hsThV1},
      hs100P ⊓ Subgroup.centralizer {permOfArr 100 hsThV1}⁆ →
    ⁅hs100P ⊓ Subgroup.centralizer {permOfArr 100 hsThV1},
      hs100P ⊓ Subgroup.centralizer {permOfArr 100 hsThV1}⁆ ≤
        Subgroup.normalizer (Q : Set (Equiv.Perm (Fin 100))) → Q = ⊥ := by
  have hv := pp_TH 2 (by norm_num)
  obtain ⟨hM, hW⟩ := mem_parts (o := 15) (ng := 2) (o' := 17) tperm.1 hv (by norm_num)
    (by norm_num) ch799102_mem1
  have hn := band ch799102_n1
  have h := eq_bot_of_checks (G := pG) (GI := pGI) (Mg := mG1) (Dg := dG1) (ngen := 4) (nm := 2)
    (v := TH.F 2) (x := X1) (r := 1100) (m := 40320) (R := R1) (RO := O1) (L := N1) (WS := W1)
    gl_sz pp_pG hv ch799102_c1 lens.1 nprods.1 (card_pG 1100 40320 (by norm_num)) hM hn.1 hn.2
    (fun k hk => by
      rw [dG1, dGen, commK_eq]
      exact hW k hk)
    ch799102_w1 ch799102_o1
  rw [closure_pG, toPerm_v 2 (by norm_num)] at h
  exact h

theorem o2_v2 : ∀ Q : Subgroup (Equiv.Perm (Fin 100)), IsPGroup 2 Q →
    Q ≤ ⁅hs100P ⊓ Subgroup.centralizer {permOfArr 100 hsThV2},
      hs100P ⊓ Subgroup.centralizer {permOfArr 100 hsThV2}⁆ →
    ⁅hs100P ⊓ Subgroup.centralizer {permOfArr 100 hsThV2},
      hs100P ⊓ Subgroup.centralizer {permOfArr 100 hsThV2}⁆ ≤
        Subgroup.normalizer (Q : Set (Equiv.Perm (Fin 100))) → Q = ⊥ := by
  have hv := pp_TH 3 (by norm_num)
  obtain ⟨hM, hW⟩ := mem_parts (o := 16) (ng := 3) (o' := 19) tperm.2.1 hv (by norm_num)
    (by norm_num) ch799102_mem2
  have hn := band ch799102_n2
  have h := eq_bot_of_checks (G := pG) (GI := pGI) (Mg := mG2) (Dg := dG2) (ngen := 4) (nm := 3)
    (v := TH.F 3) (x := X2) (r := 1100) (m := 40320) (R := R2) (RO := O2) (L := N2) (WS := W2)
    gl_sz pp_pG hv ch799102_c2 lens.2.1 nprods.2.1 (card_pG 1100 40320 (by norm_num)) hM hn.1 hn.2
    (fun k hk => by
      rw [dG2, dGen, commK_eq]
      exact hW k hk)
    ch799102_w2 ch799102_o2
  rw [closure_pG, toPerm_v 3 (by norm_num)] at h
  exact h

theorem o2_v3 : ∀ Q : Subgroup (Equiv.Perm (Fin 100)), IsPGroup 2 Q →
    Q ≤ ⁅hs100P ⊓ Subgroup.centralizer {permOfArr 100 hsThV3},
      hs100P ⊓ Subgroup.centralizer {permOfArr 100 hsThV3}⁆ →
    ⁅hs100P ⊓ Subgroup.centralizer {permOfArr 100 hsThV3},
      hs100P ⊓ Subgroup.centralizer {permOfArr 100 hsThV3}⁆ ≤
        Subgroup.normalizer (Q : Set (Equiv.Perm (Fin 100))) → Q = ⊥ := by
  have hv := pp_TH 4 (by norm_num)
  obtain ⟨hM, hW⟩ := mem_parts (o := 13) (ng := 4) (o' := 17) tperm.2.2 hv (by norm_num)
    (by norm_num) ch799102_mem3
  have hn := band ch799102_n3
  have h := eq_bot_of_checks (G := pG) (GI := pGI) (Mg := mG3) (Dg := dG3) (ngen := 4) (nm := 4)
    (v := TH.F 4) (x := X3) (r := 15400) (m := 2880) (R := R3) (RO := O3) (L := N3) (WS := W3)
    gl_sz pp_pG hv ch799102_c3 lens.2.2 nprods.2.2 (card_pG 15400 2880 (by norm_num)) hM hn.1 hn.2
    (fun k hk => by
      rw [dG3, dGen, commK_eq]
      exact hW k hk)
    ch799102_w3 ch799102_o3
  rw [closure_pG, toPerm_v 4 (by norm_num)] at h
  exact h

end CertificateChecks.KernelHS799102

end
