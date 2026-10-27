module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps107TripleDefs
public import CFSG.LieType.Multipliers.U43Bridge
import CFSG.HardMathSupport.Timmesfeld.LieRank.Exc3Models
import CFSG.Certificates.Kernel.Misc.PermInvClsSound
import CFSG.Certificates.Kernel.LocalQTPermSound
import Certificates.Kernel.Multipliers.BindListSound
import Certificates.Kernel.U43Triple.Checks
import Certificates.Kernel.U43Triple.Cls
import Certificates.Kernel.U43Triple.Bind

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU43T

open Equiv CFSG.KC.Enum CFSG.KS CFSG.KC.Misc.Clos CFSG.KC.Misc.ClosW CFSG.KC.Misc.InvCls
  CFSG.KC.BindList CFSG.LieType.Multipliers.U43
open scoped Pointwise

theorem hw10 : 820 + 1 < 2 ^ 10 := by norm_num

theorem hn820 : 820 < 16777216 := by norm_num

theorem code_of_bind {t : Array ℕ} {g : Perm (Fin 820)} {P : ℕ}
    (hr : CFSG.Monster.B.Co2.Rep 820 t g) (hs : t.size = 820)
    (hc : CFSG.KS.Prim.canonK 820 10 (mask 10) 8200 P = true)
    (hb : bindListK 10 (mask 10) P t.toList 0 = true) : P = wcode 10 g := by
  have hP : P >>> (820 * 10) = 0 := by
    unfold CFSG.KS.Prim.canonK at hc
    rw [bAnd_iff, bAnd_iff] at hc
    have e : (820 * 10 : ℕ) = 8200 := by norm_num
    rw [e]
    exact Nat.eq_of_beq_eq_true hc.2.1
  refine CFSG.KS.PF.eq_of_fields (by norm_num) hP (wcode_shr hw10 g) fun i hi => ?_
  rw [pg_wcode_nat (by norm_num) g hi]
  have h1 := bindListK_get t.toList 0 hb i (by simp [hs, hi])
  have h2 := hr.apply hi
  rw [getElem!_pos t i (by rw [hs]; exact hi)] at h2
  simp only [Array.getElem_toList, Nat.zero_add] at h1
  rw [← h1, h2]

theorem tabA_size : tabA.size = 820 := by decide +kernel

theorem tabB_size : tabB.size = 820 := by decide +kernel

theorem X_code : ∀ a < [psi xElt, psi yElt].length,
    X a = wcode 10 ([psi xElt, psi yElt].getD a 1) := by
  have hc := (allN_iff _ _).1 canonX
  intro a ha
  change a < 2 at ha
  interval_cases a
  · exact code_of_bind rep_tabA tabA_size (hc 0 (by norm_num)) bindTA
  · exact code_of_bind rep_tabB tabB_size (hc 1 (by norm_num)) bindTB

theorem exists_d : ∀ i : Fin 3, ∃ d : X₀, wcode 10 (psi d) = A i := by
  have hxy : Subgroup.closure {g | g ∈ [psi xElt, psi yElt]} ≤ psi.range := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq] at hg
    rcases hg with rfl | rfl
    exacts [⟨xElt, rfl⟩, ⟨yElt, rfl⟩]
  intro i
  have h := (allN_iff _ _).1 genD i i.isLt
  unfold wWordAt at h
  obtain ⟨h1, h2⟩ := CFSG.KC.LQT.P.andB_iff.1 h
  rw [CFSG.KC.LQT.P.beq_iff] at h2
  obtain ⟨g, hg, hgw⟩ := wword_mem hw10 hn820 [psi xElt, psi yElt] X_code h1
  obtain ⟨d, rfl⟩ := hxy hg
  exact ⟨d, hgw.trans h2⟩

noncomputable def gsD (d : Fin 3 → X₀) : List (Perm (Fin 820)) := [psi (d 0), psi (d 1), psi (d 2)]

theorem gsD_A {d : Fin 3 → X₀} (hd : ∀ i, wcode 10 (psi (d i)) = A i) :
    ∀ a < (gsD d).length, A a = wcode 10 ((gsD d).getD a 1) := by
  intro a ha
  change a < 3 at ha
  interval_cases a
  exacts [(hd 0).symm, (hd 1).symm, (hd 2).symm]

theorem gsD_range (d : Fin 3 → X₀) : Subgroup.closure {g | g ∈ gsD d} ≤ psi.range := by
  rw [Subgroup.closure_le]
  intro g hg
  simp only [gsD, List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq] at hg
  rcases hg with rfl | rfl | rfl
  exacts [⟨d 0, rfl⟩, ⟨d 1, rfl⟩, ⟨d 2, rfl⟩]

theorem word_gsD {d : Fin 3 → X₀} (hd : ∀ i, wcode 10 (psi (d i)) = A i) {W : ℕ → List ℕ}
    {C : ℕ → ℕ} {j : ℕ} (h : wWordAt 820 10 A 3 W C j = true) :
    ∃ g ∈ Subgroup.closure {g | g ∈ gsD d}, wcode 10 g = C j := by
  unfold wWordAt at h
  obtain ⟨h1, h2⟩ := CFSG.KC.LQT.P.andB_iff.1 h
  rw [CFSG.KC.LQT.P.beq_iff] at h2
  obtain ⟨g, hg, hgw⟩ := wword_mem hw10 hn820 (gsD d) (gsD_A hd) h1
  exact ⟨g, hg, hgw.trans h2⟩

theorem ne_of_bif {a b : ℕ}
    (h : Bool.rec (motive := fun _ => Bool) true false (Nat.beq a b) = true) : a ≠ b := by
  intro e
  rw [e, Nat.beq_refl] at h
  exact Bool.false_ne_true h

theorem sq_of_sqIdK {p : ℕ} {g : Perm (Fin 820)} (hp : p = wcode 10 g)
    (h : CFSG.KS.Prim.sqIdK 820 10 (mask 10) 8200 (pidn 820 10) p = true) : g * g = 1 := by
  have henc := wcode_enc hw10 hn820
  unfold CFSG.KS.Prim.sqIdK at h
  rw [bAnd_iff] at h
  have e := Nat.eq_of_beq_eq_true h.2
  rw [hp, ← henc.enc_mul, ← henc.enc_one] at e
  exact henc.inj e

theorem ne_of_neIdK {p : ℕ} {g : Perm (Fin 820)} (hp : p = wcode 10 g)
    (h : CFSG.KS.Prim.neIdK 820 10 (mask 10) 8200 (pidn 820 10) p = true) : g ≠ 1 := by
  have henc := wcode_enc hw10 hn820
  unfold CFSG.KS.Prim.neIdK at h
  rw [bAnd_iff] at h
  intro e
  apply ne_of_bif h.2
  rw [hp, e, henc.enc_one]

theorem inv_d {d : Fin 3 → X₀}
    (hd : ∀ i, wcode 10 (psi (d i)) = A i) : ∀ i, d i * d i = 1 ∧ d i ≠ 1 := by
  intro i
  have h := (allN_iff _ _).1 invA i i.isLt
  obtain ⟨h1, h2⟩ := CFSG.KC.LQT.P.andB_iff.1 h
  refine ⟨psi_injective ?_, fun h1' => ne_of_neIdK (hd i).symm h2 ?_⟩
  · rw [map_mul, map_one]
    exact sq_of_sqIdK (hd i).symm h1
  · rw [h1', map_one]

theorem gen_d {d : Fin 3 → X₀}
    (hd : ∀ i, wcode 10 (psi (d i)) = A i) :
    Subgroup.closure ({d 0, d 1, d 2} : Set X₀) = ⊤ := by
  have henc := wcode_enc hw10 hn820
  let H := Subgroup.closure ({d 0, d 1, d 2} : Set X₀)
  have hmap : Subgroup.closure {g | g ∈ gsD d} ≤ H.map psi := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [gsD, List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq] at hg
    rcases hg with rfl | rfl | rfl
    · exact ⟨d 0, Subgroup.subset_closure (by simp), rfl⟩
    · exact ⟨d 1, Subgroup.subset_closure (by simp), rfl⟩
    · exact ⟨d 2, Subgroup.subset_closure (by simp), rfl⟩
  have hmem : ∀ a < 2, ∀ z : X₀, X a = wcode 10 (psi z) → z ∈ H := by
    intro a ha z hz
    obtain ⟨g, hg, hgw⟩ := word_gsD hd ((allN_iff _ _).1 genX a ha)
    have e : g = psi z := henc.inj (hgw.trans hz)
    rw [e] at hg
    exact (Subgroup.mem_map_iff_mem psi_injective).1 (hmap hg)
  have hx : xElt ∈ H := hmem 0 (by norm_num) xElt (X_code 0 (by norm_num))
  have hy : yElt ∈ H := hmem 1 (by norm_num) yElt (X_code 1 (by norm_num))
  refine top_le_iff.1 ?_
  rw [← closure_xy, Subgroup.closure_le]
  rintro z (rfl | rfl)
  exacts [hx, hy]

theorem listT {d : Fin 3 → X₀} (hd : ∀ i, wcode 10 (psi (d i)) = A i) :
    ∃ T : Subgroup (Perm (Fin 820)), T ≤ Subgroup.closure {g | g ∈ gsD d} ∧ Nat.card T = 128 ∧
      (∀ g ∈ T, ∃ k < 128, wcode 10 g = E k) ∧
      ∃ el : ℕ → Perm (Fin 820), ∀ k < 128, el k ∈ T ∧ wcode 10 (el k) = E k := by
  have henc := wcode_enc hw10 hn820
  have hG : ∀ j : Fin 3, ∃ t ∈ Subgroup.closure {g | g ∈ gsD d}, wcode 10 t = G j := fun j =>
    word_gsD hd ((allN_iff _ _).1 genG j j.isLt)
  choose tg htg htgw using hG
  let gT : List (Perm (Fin 820)) := [tg 0, tg 1, tg 2]
  have hGT : ∀ j < gT.length, G j = wcode 10 (gT.getD j 1) := by
    intro j hj
    change j < 3 at hj
    interval_cases j
    exacts [(htgw 0).symm, (htgw 1).symm, (htgw 2).symm]
  have hTgs : Subgroup.closure {g | g ∈ gT} ≤ Subgroup.closure {g | g ∈ gsD d} := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [gT, List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq] at hg
    rcases hg with rfl | rfl | rfl
    exacts [htg 0, htg 1, htg 2]
  obtain ⟨hlist, -, hcl⟩ := clos_card henc gT hGT (N := 128) (by norm_num)
    ((allN_iff _ _).1 treeT) ((allN_iff _ _).1 sortT)
  obtain ⟨hcard, hall⟩ := hcl ((allN_iff _ _).1 closedT)
  choose! el hel hele using hlist
  exact ⟨_, hTgs, hcard, hall, el, fun k hk => ⟨hel k hk, hele k hk⟩⟩

theorem conj_d {d : Fin 3 → X₀}
    (hd : ∀ i, wcode 10 (psi (d i)) = A i) :
    ∀ x : X₀, x ^ 2 = 1 → x ≠ 1 → ∃ g : X₀, g * d 0 * g⁻¹ = x := by
  have henc := wcode_enc hw10 hn820
  have hfin : Finite X₀ := Nat.finite_of_card_ne_zero (by rw [card_X₀]; norm_num)
  obtain ⟨CT, hTgs, hcard, hall, el, hel⟩ := listT hd
  have h0 : wcode 10 (psi (d 0)) = A 0 := hd 0
  have hrep := (allN_iff _ _).1 repT
  rw [← h0] at hrep
  have hconj := invCls_sound hw10 hn820 (gsD d) (gsD_A hd) (psi (d 0)) el
    (fun k hk => (hel k hk).2.symm) ((allN_iff _ _).1 clsT) hrep
  have hgs := gsD_range d
  let T2 : Subgroup X₀ := CT.comap psi
  have hCT : CT ≤ psi.range := hTgs.trans hgs
  have hT2map : T2.map psi = CT := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.2 hCT
  have hT2card : Nat.card T2 = 128 := by
    rw [← Subgroup.card_map_of_injective psi_injective, hT2map]
    exact hcard
  intro x hx2 hx1
  have hfac : (Nat.card X₀).factorization 2 = 7 := by rw [card_X₀]; decide +kernel
  have hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P2 : Sylow 2 X₀ := Sylow.ofCard T2 (by rw [hT2card, hfac]; norm_num)
  have hP2 : (P2 : Subgroup X₀) = T2 := Sylow.coe_ofCard T2 _
  have hxord : orderOf x = 2 := orderOf_eq_prime hx2 hx1
  have hzp : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxord]; norm_num)
  obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq X₀ Q P2
  have htmem : c * x * c⁻¹ ∈ T2 := by
    have hmem : c * x * c⁻¹ ∈ (P2 : Subgroup X₀) := by
      rw [← hc, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul x (MulAut.conj c) (Q : Subgroup X₀)
        (hQ (Subgroup.mem_zpowers x))
    rwa [hP2] at hmem
  obtain ⟨k, hk, hke⟩ := hall _ htmem
  have hek : psi (c * x * c⁻¹) = el k := henc.inj (hke.trans (hel k hk).2.symm)
  have hsq : el k * el k = 1 := by
    have hpow : c * x * c⁻¹ * (c * x * c⁻¹) = 1 := by
      have e : c * x * c⁻¹ * (c * x * c⁻¹) = c * (x * x) * c⁻¹ := by group
      rw [e, ← pow_two, hx2]
      group
    rw [← hek, ← map_mul, hpow, map_one]
  have hne : el k ≠ 1 := by
    rw [← hek]
    intro h1
    apply hx1
    have h2 : c * x * c⁻¹ = 1 := psi_injective (by rw [h1, map_one])
    calc x = c⁻¹ * (c * x * c⁻¹) * c := by group
      _ = 1 := by rw [h2]; group
  obtain ⟨s, hs, c', hc', hconj'⟩ := hconj k hk hsq hne
  obtain ⟨u, hu⟩ : c' * (el s)⁻¹ ∈ psi.range :=
    Subgroup.mul_mem _ (hgs hc') (Subgroup.inv_mem _ (hCT (hel s hs).1))
  rw [← hu, ← hek, ← map_mul, ← map_mul] at hconj'
  have hu' : u * (c * x * c⁻¹) = d 0 * u := psi_injective hconj'
  refine ⟨c⁻¹ * u⁻¹, ?_⟩
  calc c⁻¹ * u⁻¹ * d 0 * (c⁻¹ * u⁻¹)⁻¹ = c⁻¹ * (u⁻¹ * (d 0 * u)) * c := by group
    _ = c⁻¹ * (u⁻¹ * (u * (c * x * c⁻¹))) * c := by rw [hu']
    _ = x := by group

public theorem u43TripleGen_of_triple (d : Fin 3 → X₀) (hinv : ∀ i, d i * d i = 1 ∧ d i ≠ 1)
    (hgen : Subgroup.closure ({d 0, d 1, d 2} : Set X₀) = ⊤)
    (hconj : ∀ x : X₀, x ^ 2 = 1 → x ≠ 1 → ∃ g : X₀, g * d 0 * g⁻¹ = x) :
    CFSG.LocalAnalysis.WeakClosure81.U43TripleGen := by
  intro S _instS _finS hS e he2 he1
  obtain ⟨φ⟩ := CFSG.HardMathSupport.Timmesfeld.LieRank.nonempty_mulEquiv_X₀_of_lieModel hS
  have hx2 : φ e ^ 2 = 1 := by rw [← map_pow, he2, map_one]
  have hx1 : φ e ≠ 1 := fun hh => he1 (φ.injective (by rw [hh, map_one]))
  obtain ⟨h0, hh0⟩ := hconj (φ e) hx2 hx1
  have hh0' : h0 * d 0 * h0⁻¹ = φ.toMonoidHom e := hh0
  have hgi : ∀ i : Fin 3, ∃ gi : X₀, gi * d 0 * gi⁻¹ = d i := fun i =>
    hconj (d i) (by rw [pow_two]; exact (hinv i).1) (hinv i).2
  choose g3 hg3 using hgi
  let a : Fin 3 → S := fun i => φ.symm (g3 i * h0⁻¹)
  have ha : ∀ i : Fin 3, φ.toMonoidHom (a i) = g3 i * h0⁻¹ := fun i => φ.apply_symm_apply _
  have himage : ∀ i : Fin 3, φ.toMonoidHom (a i * e * (a i)⁻¹) = d i := by
    intro i
    rw [map_mul, map_mul, map_inv, ha i, ← hh0', ← hg3 i]
    group
  let H : Subgroup S :=
    Subgroup.closure {a 0 * e * (a 0)⁻¹, a 1 * e * (a 1)⁻¹, a 2 * e * (a 2)⁻¹}
  have hHmap : Subgroup.map φ.toMonoidHom H = ⊤ := by
    dsimp only [H]
    rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton,
      himage 0, himage 1, himage 2]
    exact hgen
  have hHtop : H = ⊤ :=
    Subgroup.map_injective (f := φ.toMonoidHom) φ.injective (by
      rw [hHmap, Subgroup.map_top_of_surjective φ.toMonoidHom φ.surjective])
  exact ⟨a 0, a 1, a 2, by simpa only [H] using hHtop⟩

public theorem u43TripleGen_kernel :
    CFSG.LocalAnalysis.WeakClosure81.U43TripleGen := by
  choose d hd using exists_d
  exact u43TripleGen_of_triple d (inv_d hd) (gen_d hd) (conj_d hd)

end CertificateChecks.KernelU43T
