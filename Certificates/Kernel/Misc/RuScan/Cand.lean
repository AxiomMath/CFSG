
module

public import Certificates.Kernel.Misc.RuScan.Glue
public import Certificates.Kernel.Misc.RuScan.CC
public import Certificates.Kernel.Misc.RuScan.XK
public import Certificates.Kernel.Misc.RuScan.LB
public import CFSG.Certificates.Kernel.Misc.RuScanCSound
public import CFSG.Quasithin.Vol2.KGFactC31RuScanBase
public import CFSG.Sporadic.Schreier.RuEnum
import CFSG.Certificates.Kernel.Common.ForallTree
public import CFSG.Quasithin.Vol2.KGFactC31Ident
public import CFSG.Quasithin.Vol2.KGFactC31RuBigZBase
public import CFSG.Sporadic.Schreier.RuAutInnerBase
public import Certificates.Kernel.SporSch.J4S.NoCP

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelMisc.RuScan

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Prim CFSG.KC.Misc.RuInv
  CFSG.KC.Misc.RuInv.P CFSG.KC.Misc.RuBase CFSG.KC.Misc.RuScan CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.RuSchreier CFSG.Quasithin.KGC31
  CFSG.Quasithin.KGC31.Ru CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.RuLines

#kc_forall_tree q0All (fun c => ch7230q0_ c = true) 17 CertificateChecks.KernelMisc.RuScan.ch7230q0_
#kc_forall_tree q1All (fun c => ch7230q1_ c = true) 10 CertificateChecks.KernelMisc.RuScan.ch7230q1_
#kc_forall_tree q2All (fun c => ch7230q2_ c = true) 2 CertificateChecks.KernelMisc.RuScan.ch7230q2_
#kc_forall_tree q3All (fun c => ch7230q3_ c = true) 3 CertificateChecks.KernelMisc.RuScan.ch7230q3_
#kc_forall_tree xkAll (fun g => ch7230xk_ g = true) 23 CertificateChecks.KernelMisc.RuScan.ch7230xk_
#kc_forall_tree xbAll (fun t => ch7230xb_ t = true) 5 CertificateChecks.KernelMisc.RuScan.ch7230xb_

section Tj

variable {M : Type} [Group M]

theorem tj_add (y τ : M) {P : Nat} (h : tj y τ P = τ) (m : Nat) : tj y τ (m + P) = tj y τ m := by
  simp only [tj] at h ⊢
  calc y ^ (m + P) * τ * (y ^ (m + P))⁻¹ = y ^ m * (y ^ P * τ * (y ^ P)⁻¹) * (y ^ m)⁻¹ := by
        rw [pow_add]
        group
    _ = y ^ m * τ * (y ^ m)⁻¹ := by rw [h]

theorem tj_mod (y τ : M) {P : Nat} (hP : 0 < P) (h : tj y τ P = τ) (j : Nat) :
    tj y τ j = tj y τ (j % P) := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases Nat.lt_or_ge j P with hj | hj
    · rw [Nat.mod_eq_of_lt hj]
    · obtain ⟨m, rfl⟩ : ∃ m, j = m + P := ⟨j - P, by omega⟩
      rw [tj_add y τ h, ih m (by omega), Nat.add_mod_right]

theorem mP_mem {y τ : M} {K : Subgroup M} (h : ∀ j, tj y τ j ∈ K) (m n : Nat) :
    mP y τ m n ∈ K := by
  rw [mP]
  refine Subgroup.list_prod_mem _ ?_
  intro x hx
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
  split_ifs
  · exact h j
  · exact Subgroup.one_mem _

theorem mP_congr {y y' τ : M} (h : ∀ j, tj y τ j = tj y' τ j) (m n : Nat) :
    mP y τ m n = mP y' τ m n := by
  simp only [mP, h]

theorem conj_mP_congr {y y' τ : M} (h : ∀ j, tj y τ j = tj y' τ j) (m n : Nat) :
    y * mP y τ m n * y⁻¹ = y' * mP y' τ m n * y'⁻¹ := by
  rw [conj_mP, conj_mP]
  simp only [h]

theorem comm_of_coprime {y τ : M} {e P : Nat} (he : y ^ e = 1) (hP : tj y τ P = τ)
    (hc : Nat.Coprime e P) : y * τ * y⁻¹ = τ := by
  have he' : y ^ e ∈ Subgroup.centralizer ({τ} : Set M) := by
    rw [he]
    exact Subgroup.one_mem _
  have hP' : y ^ P ∈ Subgroup.centralizer ({τ} : Set M) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [tj] at hP
    calc y ^ P * τ = y ^ P * τ * (y ^ P)⁻¹ * y ^ P := by group
      _ = τ * y ^ P := by rw [hP]
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hc
  have hy : y = (y ^ e) ^ u * (y ^ P) ^ v := by
    rw [← zpow_natCast y e, ← zpow_natCast y P, ← zpow_mul, ← zpow_mul, ← zpow_add,
      mul_comm (e : ℤ) u, mul_comm (P : ℤ) v, huv, zpow_one]
  have hyH : y ∈ Subgroup.centralizer ({τ} : Set M) := by
    rw [hy]
    exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ he' u) (Subgroup.zpow_mem _ hP' v)
  rw [Subgroup.mem_centralizer_singleton_iff] at hyH
  calc y * τ * y⁻¹ = τ * y * y⁻¹ := by rw [hyH]
    _ = τ := by group

end Tj

theorem lbK_sound {V : Nat → Nat} {n : Nat} (h : lbK V n = true) {l : Nat} (hl : l < 256)
    (hn : n ≤ l) : ¬ (1 ≤ V (64 + 32 * l + 28) ∧ V (64 + 32 * l + 28) ≤ 7) := by
  have := CFSG.KC.Misc.RuBase.allN_iff.1 h l hl
  simp only [Bool.or_eq_true, Nat.blt_eq, Nat.beq_eq] at this
  omega

theorem v_mod {V : Nat → Nat} {B : Nat}
    (hV : ∀ i, V i = Nat.land (Nat.shiftRight B (Nat.shiftLeft (Nat.land i 8191) 4)) 65535)
    (n : Nat) : V n = V (n % 8192) := by
  have e : ∀ x, Nat.land x 8191 = x % 8192 := fun x => Nat.and_two_pow_sub_one_eq_mod x 13
  rw [hV n, hV (n % 8192), e, e, Nat.mod_mod]

theorem v0_mod (n : Nat) : V0 n = V0 (n % 8192) := v_mod (B := V0.b0) (fun _ => rfl) n
theorem v1_mod (n : Nat) : V1 n = V1 (n % 8192) := v_mod (B := V1.b0) (fun _ => rfl) n
theorem v2_mod (n : Nat) : V2 n = V2 (n % 8192) := v_mod (B := V2.b0) (fun _ => rfl) n
theorem v3_mod (n : Nat) : V3 n = V3 (n % 8192) := v_mod (B := V3.b0) (fun _ => rfl) n
theorem v8_mod (n : Nat) : V8 n = V8 (n % 8192) := v_mod (B := V8.b0) (fun _ => rfl) n

theorem leafAt_mod {V : Nat → Nat} (hV : ∀ n, V n = V (n % 8192)) {l : Nat}
    {y τ : Equiv.Perm (Fin 4060)} (h : LeafAt V l y τ) : LeafAt V (l % 256) y τ := by
  have e : ∀ a a', a % 8192 = a' % 8192 → V a = V a' := fun a a' h => by
    rw [hV a, hV a', h]
  obtain ⟨h1, h2, h3⟩ := h
  have eq : V (64 + 32 * (l % 256) + 28) = V (64 + 32 * l + 28) := e _ _ (by omega)
  refine ⟨by rw [eq]; exact h1, by rw [eq]; exact h2, fun b hb => ⟨fun j hj1 hj2 => ?_, ?_⟩⟩
  · rw [eq] at hj2
    exact ((h3 b hb).1 j hj1 hj2).trans (e _ _ (by omega))
  · rw [eq]
    exact (h3 b hb).2

theorem leaf_lt {V : Nat → Nat} (hV : ∀ n, V n = V (n % 8192)) {n : Nat} (hb : lbK V n = true)
    {l : Nat} {y τ : Equiv.Perm (Fin 4060)} (h : LeafAt V l y τ) :
    l % 256 < n ∧ LeafAt V (l % 256) y τ := by
  have h' := leafAt_mod hV h
  refine ⟨?_, h'⟩
  by_contra hn
  exact lbK_sound hb (Nat.mod_lt _ (by norm_num)) (by omega) ⟨h'.1, h'.2.1⟩

@[expose] def fl (g : Nat) : Nat × List Int := candData.flatten.getD g (0, [])

@[expose] noncomputable def xsG (g k : Nat) : Equiv.Perm (Fin 4060) :=
  wG (fl g).2 * wG ((refW (fl g).1).getD k []) * (wG (fl g).2)⁻¹

theorem xsG_mem (g k : Nat) : xsG g k ∈ ruP :=
  ruP.mul_mem (ruP.mul_mem (wG_mem _) (wG_mem _)) (ruP.inv_mem (wG_mem _))

theorem fl_coff : ∀ i ∈ [0, 1, 2, 3, 8], ∀ ci < ncand i,
    coff i + ci < 23 ∧ fl (coff i + ci) = (candData.getD i []).getD ci (0, []) := by
  decide +kernel

theorem refG_eq (t : Nat) : refG t = (refW t).map wG := by
  rcases t with _ | _ | _ | _ | _ | t
  · exact ofFn_vOf (ws := basisEW) (k := 3) rfl
  · exact ofFn_vOf (ws := basis64W) (k := 6) rfl
  · exact ofFn_vOf (ws := basis3W) (k := 3) rfl
  · exact ofFn_vOf (ws := basis16W) (k := 4) rfl
  · exact ofFn_vOf (ws := basis32W) (k := 5) rfl
  · rfl

theorem refW_length {t : Nat} (ht : t < 5) : (refW t).length = rk t := by
  interval_cases t <;> rfl

theorem mem_candElts {c : Nat × List Int} (hc : c.1 < 5) {x : Equiv.Perm (Fin 4060)} :
    x ∈ candElts c ↔ ∃ k < rk c.1, x = wG c.2 * wG ((refW c.1).getD k []) * (wG c.2)⁻¹ := by
  rw [candElts, refG_eq, List.map_map, List.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw
    refine ⟨k, by rw [← refW_length hc]; exact hk, ?_⟩
    rw [List.getD_eq_getElem _ _ hk]
    rfl
  · rintro ⟨k, hk, rfl⟩
    rw [← refW_length hc] at hk
    exact ⟨_, List.getElem_mem hk, by rw [List.getD_eq_getElem _ _ hk]; rfl⟩

section XP

theorem get6 {α : Type} [Inhabited α] (a b c d e f : α) :
    (#[a, b, c, d, e, f] : Array α)[0]! = a ∧ (#[a, b, c, d, e, f] : Array α)[1]! = b ∧
    (#[a, b, c, d, e, f] : Array α)[2]! = c ∧ (#[a, b, c, d, e, f] : Array α)[3]! = d ∧
    (#[a, b, c, d, e, f] : Array α)[4]! = e ∧ (#[a, b, c, d, e, f] : Array α)[5]! = f :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem gen6_eq (a b c d e f : Nat) : gen6 a b c d e f 0 = a ∧ gen6 a b c d e f 1 = b ∧
    gen6 a b c d e f 2 = c ∧ gen6 a b c d e f 3 = d ∧ gen6 a b c d e f 4 = e ∧
    gen6 a b c d e f 5 = f :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem g6A_eq : g6A = #[ruA0A, ruA1A, ruC0A, ruC1A, ruNs0A, ruNs1A] := rfl

theorem g6_binds : g6A.size = 6 ∧ ∀ j < 6,
    g6A[j]! = unpack 4060 12 (gen6 RuG.A0 RuG.A1 RuG.C0 RuG.C1 RuG.Ns0 RuG.Ns1 j) := by
  rw [g6A_eq]
  have hg := get6 ruA0A ruA1A ruC0A ruC1A ruNs0A ruNs1A
  have hn := gen6_eq RuG.A0 RuG.A1 RuG.C0 RuG.C1 RuG.Ns0 RuG.Ns1
  refine ⟨rfl, fun j hj => ?_⟩
  rcases j with _ | _ | _ | _ | _ | _ | j
  · rw [hg.1, hn.1]
    exact RuG.a0_eq
  · rw [hg.2.1, hn.2.1]
    exact RuG.a1_eq
  · rw [hg.2.2.1, hn.2.2.1]
    exact RuG.c0_eq
  · rw [hg.2.2.2.1, hn.2.2.2.1]
    exact RuG.c1_eq
  · rw [hg.2.2.2.2.1, hn.2.2.2.2.1]
    exact RuG.ns0_eq
  · rw [hg.2.2.2.2.2, hn.2.2.2.2.2]
    exact RuG.ns1_eq
  · omega

theorem g6_perms : allN 6 (fun j => permOK 4060 12 (mask 12) (4060 * 12)
    (gen6 RuG.A0 RuG.A1 RuG.C0 RuG.C1 RuG.Ns0 RuG.Ns1 j)
    (gen6 RuG.A0I RuG.A1I RuG.C0I RuG.C1I RuG.Ns0I RuG.Ns1I j)) = true := by
  have hn := gen6_eq RuG.A0 RuG.A1 RuG.C0 RuG.C1 RuG.Ns0 RuG.Ns1
  have hi := gen6_eq RuG.A0I RuG.A1I RuG.C0I RuG.C1I RuG.Ns0I RuG.Ns1I
  refine CFSG.KC.Misc.RuBase.allN_iff.2 fun j hj => ?_
  rcases j with _ | _ | _ | _ | _ | _ | j
  · rw [hn.1, hi.1]
    exact RuG.pA0
  · rw [hn.2.1, hi.2.1]
    exact RuG.pA1
  · rw [hn.2.2.1, hi.2.2.1]
    exact RuG.pC0
  · rw [hn.2.2.2.1, hi.2.2.2.1]
    exact RuG.pC1
  · rw [hn.2.2.2.2.1, hi.2.2.2.2.1]
    exact RuG.pNs0
  · rw [hn.2.2.2.2.2, hi.2.2.2.2.2]
    exact RuG.pNs1
  · omega

theorem g6IA_eq : g6IA = rawInvs 4060 g6A := rfl

theorem rep_word6 {wd : List Int} {r : Nat} (h : word6 wd r = true) :
    lettersOK 6 wd = true ∧ PRep 4060 12 r (wG wd) := by
  unfold word6 at h
  obtain ⟨e, hl⟩ := wordEqK_sound g6_binds g6_perms h
  refine ⟨hl, prep_of' ?_ (rep_wA hl)⟩
  rw [wA, g6IA_eq]
  exact e

theorem prep_xk {g : Nat} (hg : g < 23) :
    PRep 4060 12 (XP (2 * g)) (wG (fl g).2) ∧ PRep 4060 12 (XP (2 * g + 1)) (wG (fl g).2)⁻¹ := by
  have h := xkAll g hg
  unfold ch7230xk_ at h
  rw [bAnd_eq', Bool.and_eq_true] at h
  obtain ⟨hw, hi⟩ := h
  have hp := (rep_word6 hw).2
  refine ⟨hp, prep_of' ?_ (rep_ruInv' (rep_unpack hp))⟩
  rw [ruInv]
  exact (invEqK_sound hi).1

theorem prep_xb {t : Nat} (ht : t < 5) {k : Nat} (hk : k < rk t) :
    PRep 4060 12 (XP (46 + boff t + k)) (wG ((refW t).getD k [])) := by
  have h := xbAll t ht
  unfold ch7230xb_ at h
  exact (rep_word6 (CFSG.KC.Misc.RuBase.allN_iff.1 h k hk)).2

theorem cAp_xs {g : Nat} (hg : g < 23) (ht : (fl g).1 < 5) {k : Nat} (hk : k < rk (fl g).1)
    (v : Fin 4060) : cAp XP g (46 + boff (fl g).1 + k) v = (xsG g k v : Nat) := by
  obtain ⟨hK, hKI⟩ := prep_xk hg
  exact cAp_eq hK (prep_xb ht hk) hKI v

theorem cand_of {i : Nat} (hi : i ∈ [0, 1, 2, 3, 8]) {ci : Nat} (hci : ci < ncand i)
    (ht : ctyp i ci < 5) :
    (∀ k < rk (ctyp i ci), ∀ v : Fin 4060,
      cAp XP (coff i + ci) (46 + boff (ctyp i ci) + k) v = (xsG (coff i + ci) k v : Nat)) ∧
    ∃ cg ∈ candsG i (if ctyp i ci < 3 then 7 else 5),
      ∀ x, x ∈ cg ↔ ∃ k < rk (ctyp i ci), x = xsG (coff i + ci) k := by
  obtain ⟨hg, hf⟩ := fl_coff i hi ci hci
  refine ⟨fun k hk v => ?_, ?_⟩
  · have := cAp_xs hg (by rw [hf]; exact ht) (k := k) (by rw [hf]; exact hk) v
    rw [hf] at this
    exact this
  · have hmem : (candData.getD i []).getD ci (0, []) ∈ candData.getD i [] := by
      rw [List.getD_eq_getElem _ _ hci]
      exact List.getElem_mem hci
    refine ⟨candElts ((candData.getD i []).getD ci (0, [])), List.mem_map.2 ⟨_,
      List.mem_filter.2 ⟨hmem, by rw [refPrime]; exact beq_self_eq_true _⟩, rfl⟩, fun x => ?_⟩
    rw [mem_candElts ht]
    unfold xsG
    rw [hf]
    exact Iff.rfl

end XP

section Reps

theorem memC {j k : Nat} (hj : j < 3)
    (hk : k < (ChainArrays.lev 4060 (ruField4060 1) (ruBaseArr 4060 ruCBase) j).pts.size) :
    ChainArrays.levT 4060 (ruField4060 1) (ruBaseArr 4060 ruCBase) j k ∈ ruP := by
  have hA : ChainArrays ruChainC ((ruField4060 1).extract 0 2) (ruField4060 1)
      (ruBaseArr 4060 ruCBase) (ruWordsArr 2 7 ruCDerivations) := ruChain_arrays ruChainC_check.1
  have h := chain_levT_mem_original hA (by norm_num) ruChainC_check.1
    (by rw [show ruChainC.baseCount = 3 from rfl]; exact hj) hk
  rw [ruChainC_sub] at h
  exact ruC_le h

theorem rep3 {i : Nat} (hi : i < 245760) : ∃ g₀ g₁ g₂ : Equiv.Perm (Fin 4060),
    g₀ ∈ ruP ∧ g₁ ∈ ruP ∧ g₂ ∈ ruP ∧
    PRep 4060 12 (RuCS.TR (roff 4060 48720 (RuCS.LR 0) + i / rcnt (RuCS.LR 2) / rcnt (RuCS.LR 1)))
      g₀ ∧
    PRep 4060 12 (RuCS.TR (roff 4060 48720 (RuCS.LR 1) + i / rcnt (RuCS.LR 2) % rcnt (RuCS.LR 1)))
      g₁ ∧
    PRep 4060 12 (RuCS.TR (roff 4060 48720 (RuCS.LR 2) + i % rcnt (RuCS.LR 2))) g₂ := by
  obtain ⟨s0, P0⟩ := levT_prep (S := ruField4060 1) (base := ruBaseArr 4060 ruCBase)
    RuCNF.bindsC RuCNF.pC RuCS.hl (i := 0) (by norm_num)
  obtain ⟨s1, P1⟩ := levT_prep (S := ruField4060 1) (base := ruBaseArr 4060 ruCBase)
    RuCNF.bindsC RuCNF.pC RuCS.hl (i := 1) (by norm_num)
  obtain ⟨s2, P2⟩ := levT_prep (S := ruField4060 1) (base := ruBaseArr 4060 ruCBase)
    RuCNF.bindsC RuCNF.pC RuCS.hl (i := 2) (by norm_num)
  have c0 := Nat.eq_of_beq_eq_true RuCNF.cC0
  have c1 := Nat.eq_of_beq_eq_true RuCNF.cC1
  have c2 := Nat.eq_of_beq_eq_true RuCNF.cC2
  have h0 : i / rcnt (RuCS.LR 2) / rcnt (RuCS.LR 1) < rcnt (RuCS.LR 0) := by
    rw [c0, c1, c2]
    omega
  have h1 : i / rcnt (RuCS.LR 2) % rcnt (RuCS.LR 1) < rcnt (RuCS.LR 1) := by
    rw [c1, c2]
    omega
  have h2 : i % rcnt (RuCS.LR 2) < rcnt (RuCS.LR 2) := by
    rw [c2]
    omega
  exact ⟨_, _, _, memC (by norm_num) (by rw [s0]; exact h0), memC (by norm_num) (by rw [s1]; exact h1),
    memC (by norm_num) (by rw [s2]; exact h2), P0 _ h0, P1 _ h1, P2 _ h2⟩

theorem memL {j k : Nat} (hj : j < 2)
    (hk : k < (ChainArrays.lev 4060 (ruField4060 5) (ruBaseArr 4060 ruLChainBase) j).pts.size) :
    ChainArrays.levT 4060 (ruField4060 5) (ruBaseArr 4060 ruLChainBase) j k ∈ ruP := by
  have hA : ChainArrays ruChainL ((ruField4060 5).extract 0 3) (ruField4060 5)
      (ruBaseArr 4060 ruLChainBase) (ruWordsArr 3 6 ruLChainDerivations) :=
    ruChain_arrays ruL_check.1
  have h := chain_levT_mem_original hA (by norm_num) ruL_check.1
    (by rw [show ruChainL.baseCount = 2 from rfl]; exact hj) hk
  rw [ruChainL_sub] at h
  exact ruL_le h

theorem rep2 {i : Nat} (hi : i < 116480) : ∃ g₀ g₁ : Equiv.Perm (Fin 4060),
    g₀ ∈ ruP ∧ g₁ ∈ ruP ∧
    PRep 4060 12 (RuLS.TR (roff 4060 48720 (RuLS.LR 0) + i / rcnt (RuLS.LR 1))) g₀ ∧
    PRep 4060 12 (RuLS.TR (roff 4060 48720 (RuLS.LR 1) + i % rcnt (RuLS.LR 1))) g₁ := by
  obtain ⟨s0, P0⟩ := levT_prep (S := ruField4060 5) (base := ruBaseArr 4060 ruLChainBase)
    RuL.binds RuL.perm RuLS.hl (i := 0) (by norm_num)
  obtain ⟨s1, P1⟩ := levT_prep (S := ruField4060 5) (base := ruBaseArr 4060 ruLChainBase)
    RuL.binds RuL.perm RuLS.hl (i := 1) (by norm_num)
  have c0 := Nat.eq_of_beq_eq_true RuL.cnt0
  have c1 := Nat.eq_of_beq_eq_true RuL.cnt1
  have h0 : i / rcnt (RuLS.LR 1) < rcnt (RuLS.LR 0) := by
    rw [c0, c1]
    omega
  have h1 : i % rcnt (RuLS.LR 1) < rcnt (RuLS.LR 1) := by
    rw [c1]
    omega
  exact ⟨_, _, memL (by norm_num) (by rw [s0]; exact h0), memL (by norm_num) (by rw [s1]; exact h1),
    P0 _ h0, P1 _ h1⟩

end Reps

section Transfer

theorem leaf_tj {V : Nat → Nat} {l : Nat} {y y' τ : Equiv.Perm (Fin 4060)} (hy : y ∈ ruP)
    (hy' : y' ∈ ruP) (hτ : τ ∈ ruP) (h : LeafAt V l y τ) (h' : LeafAt V l y' τ) (j : Nat) :
    tj y τ j = tj y' τ j := by
  have hP : 0 < V (64 + 32 * l + 28) := h.1
  rw [tj_mod y τ hP (leaf_period hy hτ h) j, tj_mod y' τ hP (leaf_period hy' hτ h') j]
  exact leaf_eq hy hy' hτ h h' (Nat.mod_lt _ hP)

theorem elem_transfer {V : Nat → Nat} {l : Nat} {y yr τ : Equiv.Perm (Fin 4060)} (hy : y ∈ ruP)
    (hyr : yr ∈ ruP) (hτ : τ ∈ ruP) (h : LeafAt V l y τ) (hr : LeafAt V l yr τ)
    {xs : Nat → Equiv.Perm (Fin 4060)} {r S Tm k : Nat} (hxs : ∀ m < r, xs m ∈ ruP) (hk : k < r)
    (he : ∀ b (hb : b < 4),
      ((mP yr τ S (V (64 + 32 * l + 28))) ⟨b, by omega⟩ : Nat) = (xs k ⟨b, by omega⟩ : Nat) ∧
      ((yr * xs k * yr⁻¹) ⟨b, by omega⟩ : Nat) = ((mQ xs Tm r) ⟨b, by omega⟩ : Nat)) :
    xs k ∈ orbSub y τ ∧ y * xs k * y⁻¹ = mQ xs Tm r := by
  have ht := leaf_tj hy hyr hτ h hr
  have e1 : mP yr τ S (V (64 + 32 * l + 28)) = xs k :=
    eq_of_base (mP_mem (fun j => conj_mem hyr hτ j) _ _) (hxs k hk) fun b hb => (he b hb).1
  have e2 : yr * xs k * yr⁻¹ = mQ xs Tm r :=
    eq_of_base (ruP.mul_mem (ruP.mul_mem hyr (hxs k hk)) (ruP.inv_mem hyr)) (mQ_mem xs Tm r hxs)
      fun b hb => (he b hb).2
  have e3 : mP y τ S (V (64 + 32 * l + 28)) = xs k := (mP_congr ht _ _).trans e1
  refine ⟨?_, ?_⟩
  · rw [← e3]
    exact mem_orbSub_mP y τ S _
  · calc y * xs k * y⁻¹ = y * mP y τ S (V (64 + 32 * l + 28)) * y⁻¹ := by rw [e3]
      _ = yr * mP yr τ S (V (64 + 32 * l + 28)) * yr⁻¹ := conj_mP_congr ht _ _
      _ = yr * xs k * yr⁻¹ := by rw [e1]
      _ = mQ xs Tm r := e2

theorem leaf_cand {Kh V CT : Nat → Nat} {T nc go dofs nl : Nat} {τ : Equiv.Perm (Fin 4060)}
    (hT : PRep 4060 12 T τ) (hτ : τ ∈ ruP)
    (hcand : ∀ l < nl, ∃ ys : List Nat, ∃ gs : List (Equiv.Perm (Fin 4060)), PL ys gs ∧
      gs.prod ∈ ruP ∧ candOK ys T Kh V XP CT nc go DC l (16 * (dofs + l)) = true)
    {xs : Nat → Nat → Equiv.Perm (Fin 4060)} (hxP : ∀ ci k, xs ci k ∈ ruP)
    (hxs : ∀ ci < nc, CT ci < 5 → ∀ k < rk (CT ci), ∀ v : Fin 4060,
      cAp XP (go + ci) (46 + boff (CT ci) + k) v = (xs ci k v : Nat))
    {y : Equiv.Perm (Fin 4060)} (hy : y ∈ ruP) {l : Nat} (hl : l < nl) (hL : LeafAt V l y τ) :
    ∃ ci < nc, CT ci < 5 ∧ (if CT ci < 3 then 7 else 5) = V (64 + 32 * l + 28) ∧
      ∀ k < rk (CT ci), xs ci k ∈ orbSub y τ ∧ ∃ Tm, y * xs ci k * y⁻¹ = mQ (xs ci) Tm (rk (CT ci)) := by
  obtain ⟨ys, gs, hpl, hgP, hc⟩ := hcand l hl
  obtain ⟨hK, hlf, hci, ht, hq, hel⟩ := candOK_sound hc
  have hr : LeafAt V l gs.prod τ := leafOK_sound hpl hT hK hlf
  refine ⟨_, hci, ht, hq, fun k hk => ?_⟩
  have hx := hxs _ hci ht
  have he := elemOK_sound hpl hT (xs := xs (DC (16 * (dofs + l) + 2))) (fun k' hk' v => hx k' hk' v)
    hk (hel k hk)
  obtain ⟨h1, h2⟩ := elem_transfer hy hgP hτ hL hr (fun m _ => hxP _ m) hk he
  exact ⟨h1, _, h2⟩

end Transfer

theorem prime_eq {y τ : Equiv.Perm (Fin 4060)} (hmv : y * τ * y⁻¹ ≠ τ) {es : List Nat} {q : Nat}
    (hes : (es, q) ∈ ruGroups) {e : Nat} (hee : e ∈ es) (hye : y ^ e = 1) {t : Nat}
    (hper : tj y τ (if t < 3 then 7 else 5) = τ) : (if t < 3 then 7 else 5) = q := by
  have hnc : ¬ Nat.Coprime e (if t < 3 then 7 else 5) := fun hc => hmv (comm_of_coprime hye hper hc)
  simp only [ruGroups, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hes
  rcases hes with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hee <;>
    rcases hee with rfl | rfl <;> split_ifs at hnc ⊢ <;> first | rfl | exact (hnc (by decide)).elim

theorem mem_es {es : List Nat} {q : Nat} (hes : (es, q) ∈ ruGroups) {e : Nat} (hee : e ∈ es) :
    e ∈ [125, 7, 13, 29] := by
  simp only [ruGroups, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hes
  rcases hes with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all

theorem concl_of_noBad {i : Nat} {y τ : Equiv.Perm (Fin 4060)} (h : NoBad y τ) {es : List Nat}
    {q : Nat} (hes : (es, q) ∈ ruGroups) : CandConcl i y τ es q := by
  rintro ⟨e, hee, hye⟩ hcomm
  rcases h with hnb | ⟨j, hj⟩
  · exact absurd hye (hnb e (mem_es hes hee))
  · exact absurd (hcomm j) hj

section Concl

theorem concl_gen {i : Nat} (hi : i ∈ [0, 1, 2, 3, 8]) {Kh V : Nat → Nat} {T dofs nl : Nat}
    {τ y : Equiv.Perm (Fin 4060)} (hT : PRep 4060 12 T τ) (hτ : τ ∈ ruP) (hy : y ∈ ruP)
    (hmv : y * τ * y⁻¹ ≠ τ) (hV : ∀ n, V n = V (n % 8192)) (hb : lbK V nl = true)
    (hcand : ∀ l < nl, ∃ ys : List Nat, ∃ gs : List (Equiv.Perm (Fin 4060)), PL ys gs ∧
      gs.prod ∈ ruP ∧ candOK ys T Kh V XP (ctyp i) (ncand i) (coff i) DC l (16 * (dofs + l)) = true)
    (hscan : NoBad y τ ∨ ∃ l, LeafAt V l y τ) {es : List Nat} {q : Nat}
    (hes : (es, q) ∈ ruGroups) : CandConcl i y τ es q := by
  rcases hscan with hnb | ⟨l, hL⟩
  · exact concl_of_noBad hnb hes
  intro ⟨e, hee, hye⟩ _
  obtain ⟨hl, hL'⟩ := leaf_lt hV hb hL
  obtain ⟨ci, hci, ht, hP, hk⟩ := leaf_cand hT hτ hcand (xs := fun ci k => xsG (coff i + ci) k)
    (fun _ _ => xsG_mem _ _) (fun ci hci ht => (cand_of hi hci ht).1) hy hl hL'
  have hper : tj y τ (if ctyp i ci < 3 then 7 else 5) = τ := by
    rw [hP]
    exact leaf_period hy hτ hL'
  have hq := prime_eq hmv hes hee hye hper
  obtain ⟨cg, hcg, hiff⟩ := (cand_of hi hci ht).2
  rw [hq] at hcg
  refine ⟨cg, hcg, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨k, hk', rfl⟩ := (hiff x).1 hx
    exact (hk k hk').1
  · obtain ⟨k, hk', rfl⟩ := (hiff x).1 hx
    obtain ⟨Tm, e2⟩ := (hk k hk').2
    rw [e2]
    exact mQ_mem _ _ _ fun m hm => Subgroup.subset_closure ((hiff _).2 ⟨m, hm, rfl⟩)

theorem cand_cover {P : Nat → Prop} {K : Nat} (h : ∀ c < K, ∀ d < 8, P (Nat.mul 8 c + d)) :
    ∀ l < 8 * K, P l := fun l hl => by
  have := h (l / 8) (by omega) (l % 8) (by omega)
  have e : Nat.mul 8 (l / 8) + l % 8 = l := Nat.div_add_mod l 8
  rwa [e] at this

theorem candC_leaves {Kh V CT : Nat → Nat} {H nc go dofs K : Nat} {h : Equiv.Perm (Fin 4060)}
    (hH : PRep 4060 12 H h) (hh : h ∈ ruP)
    (hq : ∀ c < K, candC3 RuCS.LR RuCS.TR DC Kh V XP CT nc go H (HP 0) 245760 dofs (Nat.mul 8 c) 8 =
      true) :
    ∀ l < 8 * K, ∃ ys : List Nat, ∃ gs : List (Equiv.Perm (Fin 4060)), PL ys gs ∧
      gs.prod ∈ ruP ∧ candOK ys (HP 0) Kh V XP CT nc go DC l (16 * (dofs + l)) = true :=
  cand_cover fun c hc d hd => by
    obtain ⟨hN, hok⟩ := candC3_sound (hq c hc) d hd
    obtain ⟨g₀, g₁, g₂, m0, m1, m2, P0, P1, P2⟩ := rep3 hN
    refine ⟨_, [h, g₀, g₁, g₂], .cons hH (.cons P0 (.cons P1 (.cons P2 .nil))), ?_, hok⟩
    simp only [List.prod_cons, List.prod_nil]
    exact ruP.mul_mem hh (ruP.mul_mem m0 (ruP.mul_mem m1 (ruP.mul_mem m2 ruP.one_mem)))

theorem candFactC {i : Nat} (hi : i < 4) {c : Equiv.Perm (Fin 4060)} (hc : c ∈ ruC)
    (hmv : cosetH i * c * ruZ * (cosetH i * c)⁻¹ ≠ ruZ) {es : List Nat} {q : Nat}
    (hes : (es, q) ∈ ruGroups) : CandConcl i (cosetH i * c) ruZ es q := by
  have hy : cosetH i * c ∈ ruP := ruP.mul_mem (abG_mem _) (ruC_le hc)
  interval_cases i
  · exact concl_gen (by simp) prep_Z ruZ_mem hy hmv v0_mod ch7230lb0
      (candC_leaves (prep_H (i := 0) (by norm_num)) (abG_mem _) q0All) (scan0 hc) hes
  · exact concl_gen (by simp) prep_Z ruZ_mem hy hmv v1_mod ch7230lb1
      (candC_leaves (prep_H (i := 1) (by norm_num)) (abG_mem _) q1All) (scan1 hc) hes
  · exact concl_gen (by simp) prep_Z ruZ_mem hy hmv v2_mod ch7230lb2
      (candC_leaves (prep_H (i := 2) (by norm_num)) (abG_mem _) q2All) (scan2 hc) hes
  · exact concl_gen (by simp) prep_Z ruZ_mem hy hmv v3_mod ch7230lb3
      (candC_leaves (prep_H (i := 3) (by norm_num)) (abG_mem _) q3All) (scan3 hc) hes

theorem cand8_leaves :
    ∀ l < 6, ∃ ys : List Nat, ∃ gs : List (Equiv.Perm (Fin 4060)), PL ys gs ∧
      gs.prod ∈ ruP ∧ candOK ys (RuT4060.L 0) K8 V8 XP (ctyp 8) (ncand 8) (coff 8) DC l
        (16 * (256 + l)) = true := fun l hl => by
  obtain ⟨hN, hok⟩ := candC2_sound ch7230q8 l hl
  rw [Nat.zero_add] at hN hok
  obtain ⟨g₀, g₁, m0, m1, P0, P1⟩ := rep2 hN
  refine ⟨_, [abG (cosetWords.getD 8 []), g₀, g₁],
    .cons (prep_H (i := 8) (by norm_num)) (.cons P0 (.cons P1 .nil)), ?_, hok⟩
  simp only [List.prod_cons, List.prod_nil]
  exact ruP.mul_mem (abG_mem _) (ruP.mul_mem m0 (ruP.mul_mem m1 ruP.one_mem))

theorem candFactL {i : Nat} (hi4 : 4 ≤ i) (hi : i < 9) {c : Equiv.Perm (Fin 4060)} (hc : c ∈ ruL)
    (hmv : cosetH i * c * ruA0 * (cosetH i * c)⁻¹ ≠ ruA0) {es : List Nat} {q : Nat}
    (hes : (es, q) ∈ ruGroups) : CandConcl i (cosetH i * c) ruA0 es q := by
  have hy : cosetH i * c ∈ ruP := ruP.mul_mem (abG_mem _) (ruL_le hc)
  interval_cases i
  · exact concl_of_noBad (Or.inl (scan45 (Or.inl rfl) hc)) hes
  · exact concl_of_noBad (Or.inl (scan45 (Or.inr rfl) hc)) hes
  · exact concl_of_noBad (scan6 hc) hes
  · exact concl_of_noBad (scan7 hc) hes
  · exact concl_gen (by simp) prep_A0 ruA0_mem hy hmv v8_mod ch7230lb8 cand8_leaves (scan8 hc) hes

end Concl

end CertificateChecks.KernelMisc.RuScan

end
