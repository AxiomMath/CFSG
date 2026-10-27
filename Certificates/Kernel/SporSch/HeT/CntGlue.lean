
module

public import Certificates.Kernel.SporSch.HeT.CntData
public import CFSG.Certificates.Kernel.SporSch.HeSrchSound
public import CFSG.Certificates.Kernel.HeFixKSound
public import CFSG.Sporadic.HeldB.InnerClassBase
public import CFSG.Sporadic.HeldB.OuterClassBase
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.HeAutKSound
public import CFSG.Certificates.Kernel.HeFixKFix
public import CFSG.Certificates.Kernel.PermToolSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HeCn

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.BfsPin
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.HeldB
open CertificateChecks.KernelSporSch CertificateChecks.KernelSpor CertificateChecks.KernelSporSch.HeO16

theorem lr0 : Nat.beq (rcnt (HeC.LR 0)) 8330 = true := by quickRfl
theorem lr1 : Nat.beq (rcnt (HeC.LR 1)) 4480 = true := by quickRfl

theorem repF_of_rep {p : Nat} {g : Equiv.Perm (Fin 8330)} (h : Rep 8330 (unpack 8330 14 p) g) :
    RepF 8330 (pm p) g := fun x hx => by
  rw [← h ⟨x, hx⟩]
  exact (unpackGet hx).symm

theorem rep_pm {p q : Nat} (h : permOK 8330 14 (mask 14) (8330 * 14) p q = true) :
    RepF 8330 (pm p) (permOfArr 8330 (unpack 8330 14 p)) :=
  repF_of_rep (rep_permOfArr (invEqK_sound h).2).1

theorem repF_of_rb {T : Nat → Nat} {P : Nat} {g : Equiv.Perm (Fin 8330)}
    (h : rbAll T P = true) (hP : RepF 8330 (pm P) g) : RepF 8330 (pmR T) g := fun x hx => by
  rw [← hP x hx]
  exact Nat.eq_of_beq_eq_true (allN_spec h x hx)

theorem perm_eq_of_repF {f g : Nat → Nat} {a b : Equiv.Perm (Fin 8330)} (ha : RepF 8330 f a)
    (hb : RepF 8330 g b) (h : ∀ x < 8330, f x = g x) : a = b :=
  Equiv.ext fun x => Fin.ext (by rw [← ha x x.2, ← hb x x.2]; exact h x x.2)

theorem slices {f : Nat → Bool} (h : ∀ s < 49, allN 170 (fun j => f (Nat.add (Nat.mul s 170) j)) =
    true) : ∀ x < 8330, f x = true := by
  intro x hx
  have h1 := allN_spec (h (x / 170) (by omega)) (x % 170) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul (x / 170) 170) (x % 170) = x := by
    change x / 170 * 170 + x % 170 = x
    exact Nat.div_add_mod' x 170
  rwa [e] at h1

theorem conj_of_cj {X Y : Nat → Nat} {F : Nat} {x y : Equiv.Perm (Fin 8330)} (hX : RepF 8330 (pmR X) x)
    (hY : RepF 8330 (pmR Y) y) (hF : nfValidK 5 HeC.LR F = true)
    (hc : ∀ s < 49, cjB X Y F s = true) : E F * x = y * E F := by
  refine perm_eq_of_repF ((E_rep hF).comp hX) (hY.comp (E_rep hF)) ?_
  have hc' : ∀ s < 49, allN 170 (fun j => (fun x => Nat.beq (HeTc.nfp F (pmR X x))
      (pmR Y (HeTc.nfp F x))) (Nat.add (Nat.mul s 170) j)) = true := fun s hs => by
    have := hc s hs
    unfold cjB at this
    simpa only [strictB_val] using this
  have h := slices (f := fun x => Nat.beq (HeTc.nfp F (pmR X x)) (pmR Y (HeTc.nfp F x))) hc'
  exact fun x hx => Nat.eq_of_beq_eq_true (h x hx)

theorem cent_card {c x y : Equiv.Perm (Fin 8330)} (hc : c ∈ heP) (h : c * x = y * c) :
    Nat.card {g : heP // (g : Equiv.Perm (Fin 8330)) * x = y * g} =
      Nat.card {g : heP // y * (g : Equiv.Perm (Fin 8330)) = g * y} := by
  have hx : x = c⁻¹ * y * c := by rw [mul_assoc, ← h, inv_mul_cancel_left]
  refine Nat.card_congr
    { toFun := fun g => ⟨g * ⟨c, hc⟩⁻¹, ?_⟩
      invFun := fun g => ⟨g * ⟨c, hc⟩, ?_⟩
      left_inv := fun g => Subtype.ext (by simp)
      right_inv := fun g => Subtype.ext (by simp) }
  · have hg0 : (g : Equiv.Perm (Fin 8330)) * x = y * g := g.2
    have hg : (g : Equiv.Perm (Fin 8330)) * (c⁻¹ * y * c) = y * g := by
      rw [← hx]
      exact hg0
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc y * (↑↑g * c⁻¹) = ↑↑g * c⁻¹ * y * c * c⁻¹ := by
          rw [show ↑↑g * c⁻¹ * y * c = ↑↑g * (c⁻¹ * y * c) by group, hg]
          group
      _ = ↑↑g * c⁻¹ * y := by group
  · have hg : y * (g : Equiv.Perm (Fin 8330)) = g * y := g.2
    rw [hx]
    simp only [Subgroup.coe_mul]
    calc ↑↑g * c * (c⁻¹ * y * c) = ↑↑g * y * c := by group
      _ = y * (↑↑g * c) := by rw [← hg]; group

theorem srch_eq_of_or {X Y V R Z : Nat → Nat} {x y : Equiv.Perm (Fin 8330)}
    (hX : RepF 8330 (pmR X) x) (hY : RepF 8330 (pmR Y) y) (hx0 : pmR X 0 = 0) (hx1 : pmR X 1 = 2)
    (hxy : ∀ g ∈ heChain.originalSubgroup, (g * x)⁻¹ * (y * g) ∈ heChain.originalSubgroup)
    {e : Nat} (hE : e < 8330 → srchAAt 14 9 HeTb.NR HeTb.NR HeTb.LT HeTb.PT HeTb.QT HeC.LR heBase 0
      (pmR X) (pmR Y) e = 0)
    (h : ∀ k < 8330, orAt X Y V R Z e k = true) :
    ∀ k < 8330, srchAAt 14 9 HeTb.NR HeTb.NR HeTb.LT HeTb.PT HeTb.QT HeC.LR heBase 0
      (pmR X) (pmR Y) k = V k := by
  have hrep : ∀ k < 8330, R k = k → srchAAt 14 9 HeTb.NR HeTb.NR HeTb.LT HeTb.PT HeTb.QT HeC.LR
      heBase 0 (pmR X) (pmR Y) k = V k := fun k hk hr => by
    have hk' := h k hk
    have hb : Nat.beq (R k) k = true := by
      rw [Nat.beq_eq]
      exact hr
    unfold orAt at hk'
    rw [strictB_val, hb] at hk'
    cases hkE : Nat.beq k e
    · rw [hkE] at hk'
      exact Nat.eq_of_beq_eq_true hk'
    · rw [hkE] at hk'
      have hke : k = e := Nat.eq_of_beq_eq_true hkE
      subst hke
      rw [hE hk, Nat.eq_of_beq_eq_true hk']
  have hcard : ∀ k < 8330, srchAAt 14 9 HeTb.NR HeTb.NR HeTb.LT HeTb.PT HeTb.QT HeC.LR heBase 0
      (pmR X) (pmR Y) k = Nat.card {g : heChain.originalSubgroup //
        (((g : Equiv.Perm (Fin 8330)) ⟨0, by norm_num⟩ : Fin 8330) : Nat) = p0K k ∧
          (g : Equiv.Perm (Fin 8330)) * x = y * g} := fun k hk =>
    srchAAt_sound (b0 := 0) (b1 := 1) (b2 := 2) (bs := [3, 4]) heChainArrays heChain_check.1
      (by norm_num) HeTc.tc hX hY hxy hx0 hx1 (by norm_num)
      (by rw [Nat.eq_of_beq_eq_true lr0]; exact hk)
  intro k hk
  cases hr : Nat.beq (R k) k
  · have hk' := h k hk
    unfold orAt at hk'
    rw [strictB_val, hr, strictB_val] at hk'
    simp only [bAnd_iff] at hk'
    obtain ⟨hr1, hrr, hV, hp, hF, hz, hc⟩ := hk'
    rw [Nat.blt_eq] at hr1 hp
    have hrr := Nat.eq_of_beq_eq_true hrr
    have hz := Nat.eq_of_beq_eq_true hz
    have hzm : E (Z k) ∈ heChain.originalSubgroup := E_mem hF
    have hzy : E (Z k) * y = y * E (Z k) :=
      comm_of_eqOnL he_baseFaithful (E_rep hF) hY (comm_mem_of_hxy hxy hzm) hc
    have e := fib_card_mul (x := x) hzm hzy ⟨0, by norm_num⟩ ⟨p0K (R k), hp⟩
    have hzp : ((E (Z k) ⟨p0K (R k), hp⟩ : Fin 8330) : Nat) = p0K k := by
      rw [← E_rep hF _ hp, hz]
    rw [hzp] at e
    rw [hcard k hk, e, ← hcard (R k) hr1, hrep (R k) hr1 hrr, Nat.eq_of_beq_eq_true hV]
  · exact hrep k hk (Nat.eq_of_beq_eq_true hr)

theorem cent_of_or {X Y : Nat → Nat} {F : Nat} {x y : Equiv.Perm (Fin 8330)}
    (hX : RepF 8330 (pmR X) x) (hY : RepF 8330 (pmR Y) y) (hF : nfValidK 5 HeC.LR F = true)
    (hc : ∀ s < 49, cjB X Y F s = true) (hx0 : pmR X 0 = 0) (hx1 : pmR X 1 = 2)
    (hxy : ∀ g ∈ heChain.originalSubgroup, (g * x)⁻¹ * (y * g) ∈ heChain.originalSubgroup)
    {V R Z : Nat → Nat} {e : Nat} (hE : e < 8330 → srchAAt 14 9 HeTb.NR HeTb.NR HeTb.LT HeTb.PT
      HeTb.QT HeC.LR heBase 0 (pmR X) (pmR Y) e = 0) (hV : ∀ s < 49, orB X Y V R Z e s = true) :
    Nat.card {g : heP // y * (g : Equiv.Perm (Fin 8330)) = g * y} = sumN 8330 V := by
  have hcm : E F ∈ heP := by
    rw [heP_eq_originalSubgroup]
    exact E_mem hF
  have hor : ∀ k < 8330, orAt X Y V R Z e k = true := slices (f := orAt X Y V R Z e) hV
  have hsum : sumN (rcnt (HeC.LR 0)) (srchAAt 14 9 HeTb.NR HeTb.NR HeTb.LT HeTb.PT HeTb.QT HeC.LR
      heBase 0 (pmR X) (pmR Y)) = sumN 8330 V := by
    rw [Nat.eq_of_beq_eq_true lr0, sumN_eq, sumN_eq]
    exact congrArg List.sum (List.map_congr_left fun k hk =>
      srch_eq_of_or hX hY hx0 hx1 hxy hE hor k (List.mem_range.1 hk))
  rw [← cent_card hcm (conj_of_cj hX hY hF hc), ← hsum]
  have hs : sumN (rcnt (HeC.LR 0)) (srchAAt 14 9 HeTb.NR HeTb.NR HeTb.LT HeTb.PT HeTb.QT HeC.LR
      heBase 0 (pmR X) (pmR Y)) =
      Nat.card {g : heChain.originalSubgroup // (g : Equiv.Perm (Fin 8330)) * x = y * g} :=
    srchA_sound (b0 := 0) (b1 := 1) (b2 := 2) (bs := [3, 4]) heChainArrays
      heChain_check.1 (by norm_num) HeTc.tc hX hY hxy hx0 hx1
  rw [hs]
  have e := heP_eq_originalSubgroup
  revert e
  generalize heChain.originalSubgroup = K
  rintro rfl
  rfl

theorem hxy_of_mem {X Y : Nat → Nat} {F : Nat} {x y : Equiv.Perm (Fin 8330)}
    (hX : RepF 8330 (pmR X) x) (hY : RepF 8330 (pmR Y) y) (hF : nfValidK 5 HeC.LR F = true)
    (hc : ∀ s < 49, cjB X Y F s = true) (hy : y ∈ heP) :
    ∀ g ∈ heChain.originalSubgroup, (g * x)⁻¹ * (y * g) ∈ heChain.originalSubgroup := by
  have h := conj_of_cj hX hY hF hc
  have hx : x = (E F)⁻¹ * (y * E F) := by rw [← h, inv_mul_cancel_left]
  have hE : E F ∈ heP := by
    rw [heP_eq_originalSubgroup]
    exact E_mem hF
  rw [← heP_eq_originalSubgroup]
  intro g hg
  rw [hx]
  exact heP.mul_mem (heP.inv_mem (heP.mul_mem hg (heP.mul_mem (heP.inv_mem hE)
    (heP.mul_mem hy hE)))) (heP.mul_mem hy hg)

theorem hxy_u {X Y : Nat → Nat}
    {F : Nat} {x : Equiv.Perm (Fin 8330)} (hX : RepF 8330 (pmR X) x)
    (hY : RepF 8330 (pmR Y) heAutU) (hF : nfValidK 5 HeC.LR F = true)
    (hc : ∀ s < 49, cjB X Y F s = true) :
    ∀ g ∈ heChain.originalSubgroup, (g * x)⁻¹ * (heAutU * g) ∈ heChain.originalSubgroup := by
  have h := conj_of_cj hX hY hF hc
  have hx : x = (E F)⁻¹ * (heAutU * E F) := by rw [← h, inv_mul_cancel_left]
  have hE : E F ∈ heP := by
    rw [heP_eq_originalSubgroup]
    exact E_mem hF
  rw [← heP_eq_originalSubgroup]
  intro g hg
  have e : (g * ((E F)⁻¹ * (heAutU * E F)))⁻¹ * (heAutU * g) =
      (E F)⁻¹ * (heAutU⁻¹ * (E F * g⁻¹) * heAutU) * g := by group
  rw [hx, e, heAutU_inv]
  exact heP.mul_mem (heP.mul_mem (heP.inv_mem hE)
    (heAutU_conj_mem (heP.mul_mem hE (heP.inv_mem hg)))) hg

theorem stab_sum {U : Nat → Nat} {V : Nat → Nat} (h : ∀ q < 35, stB U V q = true) :
    cnt0R HeC.LR (twK 14 HeTb.NR HeTb.NR HeTb.LT HeTb.PT heBase U) 0 (rcnt (HeC.LR 1)) =
      sumN 35 V := by
  have e0 : ∀ (t : Nat → Bool) (m : Nat), cnt0R HeC.LR t 0 m =
      sumN m (fun j => cnt234 HeC.LR t 0 j) := fun t m => by
    unfold cnt0R
    congr 1
    funext j
    exact congrArg _ (Nat.zero_add j)
  rw [e0, Nat.eq_of_beq_eq_true lr1, show (4480 : Nat) = 35 * 128 from rfl, sumN_mul, sumN_eq,
    sumN_eq]
  exact congrArg List.sum (List.map_congr_left fun q hq =>
    Nat.eq_of_beq_eq_true (h q (List.mem_range.1 hq)))

theorem tw_of_cnt {U : Nat → Nat} {u : Equiv.Perm (Fin 8330)}
    (hU : RepF 8330 U u) (hm : ∀ g ∈ heP, (u * g) ^ 2 ∈ heP) {V : Nat → Nat}
    (hV : ∀ q < 35, stB U V q = true) :
    Nat.card {x : heP // (u * x) ^ 2 = 1 ∧ (x : Equiv.Perm (Fin 8330)) 0 = 0} = sumN 35 V := by
  rw [← stab_sum hV]
  have ht : ∀ F, nfValidK 5 HeC.LR F = true → F % 65536 = 0 →
      (twK 14 HeTb.NR HeTb.NR HeTb.LT HeTb.PT heBase U F = true ↔ (u * E F) ^ 2 = 1) := by
    intro F hF _
    have hE : E F ∈ heP := by
      rw [heP_eq_originalSubgroup]
      exact E_mem hF
    have hm' := hm _ hE
    rw [heP_eq_originalSubgroup] at hm'
    exact twK_iff he_baseFaithful he_bs_lt (E_rep hF) hU hm'
  have hs : cnt0R HeC.LR (twK 14 HeTb.NR HeTb.NR HeTb.LT HeTb.PT heBase U) 0 (rcnt (HeC.LR 1)) =
      Nat.card {g : heChain.originalSubgroup // (g : Equiv.Perm (Fin 8330)) 0 = 0 ∧
        (u * g) ^ 2 = 1} :=
    stab0_sound (b0 := 0) (bs := [1, 2, 3, 4]) heChainArrays heChain_check.1 (by norm_num) HeTc.tc
      (by norm_num) (Pr := fun g => (u * g) ^ 2 = 1) ht
  rw [hs]
  have e := heP_eq_originalSubgroup
  revert e
  generalize heChain.originalSubgroup = K
  rintro rfl
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => ⟨fun h => ⟨h.2, h.1⟩,
    fun h => ⟨h.2, h.1⟩⟩)

theorem fix0_of_mem1 {g : Equiv.Perm (Fin 8330)}
    (hg : g ∈ heChain.levelSubgroup 1) : g 0 = 0 := by
  have h := ((heChain.mem_levelSubgroup_iff heChain_valid.1 1 (by decide) g).1 hg).2
  exact h 0 (by decide)

theorem forall₂_exists {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ a ∈ l₁, ∃ b ∈ l₂, R a b
  | _, _, .nil, _, h => absurd h List.not_mem_nil
  | _, _, .cons hab h, a, hm => by
    rcases List.mem_cons.1 hm with rfl | hm
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨b, hb, hr⟩ := forall₂_exists h a hm
      exact ⟨b, List.mem_cons_of_mem _ hb, hr⟩

theorem fix0_block {gs : List (List ℕ)}
    (hg : ∀ G ∈ gs, ∀ i ∈ G, 1 ≤ i ∧ i < 5) :
    ∀ B ∈ blocksOf 8330 (rawLevels 8330 heStrongArrs heBase.toArray) gs, ∀ t ∈ B, t[0]! = 0 := by
  have hgi : ∀ G ∈ gs, ∀ i ∈ G, i < heChain.baseCount := fun G hG i hi => (hg G hG i hi).2
  have hR := repBlocks_blocksOf heChainArrays (chainCheckFacts heChain_check.1) hgi
  intro B hB t ht
  rw [blocksOf] at hB
  obtain ⟨G, hG, rfl⟩ := List.mem_map.1 hB
  have hRG : List.Forall₂ (Rep 8330) (blockOf 8330 (G.map (levelArr
      (rawLevels 8330 heStrongArrs heBase.toArray)))).toList
      (products (G.map (levList 8330 heStrongArrs heBase.toArray))) := by
    rw [RepBlocks, blocksOf, List.forall₂_map_left_iff, List.forall₂_map_right_iff] at hR
    exact List.forall₂_same.1 hR G hG
  obtain ⟨g, hgm, hrep⟩ := forall₂_exists hRG t (Array.mem_toList_iff.2 ht)
  have hmem : g ∈ heChain.levelSubgroup 1 := by
    refine mem_of_mem_products (heChain.levelSubgroup 1).toSubmonoid _ ?_ g hgm
    intro T hT u hu
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hT
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hu
    exact heChain.levelSubgroup_antitone 1 i (hg G hG i hi).1
      (heChainArrays.levT_mem (chainCheckFacts heChain_check.1) (hg G hG i hi).2
        (List.mem_range.1 hk))
  have h0 := hrep (0 : Fin 8330)
  rw [fix0_of_mem1 hmem] at h0
  exact h0

theorem heBlocks_fix0' :
    ((heBlock1.all fun t => t[0]! == 0) && heBlock2.all fun t => t[0]! == 0) = true := by
  have h := fix0_block (gs := [[1], [2, 3, 4]]) (by decide)
  have hb : blocksOf 8330 (rawLevels 8330 heStrongArrs heBase.toArray) [[1], [2, 3, 4]] =
      [heBlock1, heBlock2] := rfl
  rw [hb] at h
  rw [Bool.and_eq_true, Array.all_eq_true', Array.all_eq_true']
  exact ⟨fun t ht => beq_iff_eq.2 (h _ List.mem_cons_self t ht),
    fun t ht => beq_iff_eq.2 (h _ (List.mem_cons_of_mem _ List.mem_cons_self) t ht)⟩

theorem heBlock12_fix0' {t1 t2 : Array ℕ} (h1 : t1 ∈ heBlock1)
    (h2 : t2 ∈ heBlock2) : t1[0]! = 0 ∧ t2[0]! = 0 := by
  have h := heBlocks_fix0'
  rw [Bool.and_eq_true, Array.all_eq_true', Array.all_eq_true'] at h
  exact ⟨beq_iff_eq.1 (h.1 t1 h1), beq_iff_eq.1 (h.2 t2 h2)⟩

end CertificateChecks.KernelSporSch.HeCn

end
