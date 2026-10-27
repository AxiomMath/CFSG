module

public import Certificates.Kernel.S5Ext.Glue
public import Certificates.Kernel.S5Ext.Checks
public import CFSG.Certificates.Kernel.S5Ext.Bridge

set_option maxRecDepth 100000

public section

open CFSG.KD.S5Ext CFSG.CGT.PushingUpLit.SolK CFSG.Certificates.Kernel.S5K

namespace CertificateChecks.S5K

theorem treeE : ∀ e, e < 1152 → ∃ f : Nat → Nat, IsAutN f ∧ HasKey f (l20 AKP e) := by
  have hsg := ch271071_sg
  rw [Bool.and_eq_true] at hsg
  exact tree_sound hsg.1 hsg.2 (Nat.eq_of_beq_eq_true ch271071_ide) ch271071_tree

noncomputable def gF (e : Nat) : Nat → Nat :=
  if h : e < 1152 then Classical.choose (treeE e h) else id

theorem gF_spec {e : Nat} (h : e < 1152) : IsAutN (gF e) ∧ HasKey (gF e) (l20 AKP e) := by
  rw [gF, dif_pos h]
  exact Classical.choose_spec (treeE e h)

theorem autK_len : autK.length = 1152 := by
  rw [← lenL_eq]
  exact Nat.eq_of_beq_eq_true ch271071_len

theorem autK_sort : autK.Pairwise (· < ·) ∧ ∀ x ∈ autK, x < 1048576 :=
  sort_sound (K := autK) (b := 1048576) ch271071_sort

theorem akp_lane : ∀ i (hi : i < autK.length), l20 AKP i = autK[i] :=
  pack_sound ch271071_pack fun x hx => autK_sort.2 x hx

theorem l20_lt (x i : Nat) : l20 x i < 2 ^ 20 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem key_eq_of_toF {f g : Nat → Nat} {k k' : Nat} (hf : IsAutN f) (hg : IsAutN g)
    (hfk : HasKey f k) (hgk : HasKey g k') (hk : k < 2 ^ 20) (hk' : k' < 2 ^ 20)
    (h : toF f = toF g) : k = k' := by
  have v : ∀ x : Fin 32, f x.val = g x.val := fun x => by
    rw [← toF_val hf, ← toF_val hg, h]
  exact key_eq_of_fields hk hk' (hfk.1.symm.trans ((v 1).trans hgk.1))
    (hfk.2.1.symm.trans ((v 2).trans hgk.2.1)) (hfk.2.2.1.symm.trans ((v 8).trans hgk.2.2.1))
    (hfk.2.2.2.symm.trans ((v 16).trans hgk.2.2.2))

theorem pm_vals {f : Fin 32 → Fin 32} (hf : ∀ i j, f (extraMulFin i j) = extraMulFin (f i) (f j))
    (i j : Fin 32) : pm (f i).val (f j).val = (f (extraMulFin i j)).val := by
  rw [← extraMulFin_val, hf]

theorem inv_mem : ∀ x : Fin 32, x ≠ 0 → extraMulFin x x = 0 → x.val ∈ invsL := by decide

theorem tab_complete (f : Fin 32 → Fin 32) (hf : ∀ i j, f (extraMulFin i j) = extraMulFin (f i) (f j))
    (hi : Function.Injective f) : ∃ e, e < 1152 ∧ toF (gF e) = f := by
  have h0 := hom_zero hf
  have hne : ∀ x : Fin 32, x ≠ 0 → f x ≠ 0 := fun x hx h => hx (hi (h.trans h0.symm))
  have hsq : ∀ x : Fin 32, extraMulFin x x = 0 → f x ≠ 0 → (f x).val ∈ invsL := fun x hx hfx =>
    inv_mem _ hfx (by rw [← hf, hx, h0])
  have m1 := hsq 1 (by decide) (hne 1 (by decide))
  have m2 := hsq 2 (by decide) (hne 2 (by decide))
  have m8 := hsq 8 (by decide) (hne 8 (by decide))
  have m16 := hsq 16 (by decide) (hne 16 (by decide))
  have hab : pm (f 1).val (f 2).val = pm (f 2).val (f 1).val := by
    rw [pm_vals hf, pm_vals hf, (by decide : extraMulFin 1 2 = extraMulFin 2 1)]
  have hac : pm (f 1).val (f 8).val = pm (f 8).val (f 1).val := by
    rw [pm_vals hf, pm_vals hf, (by decide : extraMulFin 1 8 = extraMulFin 8 1)]
  have hbd : pm (f 2).val (f 16).val = pm (f 16).val (f 2).val := by
    rw [pm_vals hf, pm_vals hf, (by decide : extraMulFin 2 16 = extraMulFin 16 2)]
  have hcd : pm (f 8).val (f 16).val = pm (f 16).val (f 8).val := by
    rw [pm_vals hf, pm_vals hf, (by decide : extraMulFin 8 16 = extraMulFin 16 8)]
  have hs : pm (pm (f 1).val (f 16).val) (pm (f 1).val (f 16).val) =
      pm (pm (f 8).val (f 2).val) (pm (f 8).val (f 2).val) := by
    rw [pm_vals hf 1 16, pm_vals hf 8 2, pm_vals hf, pm_vals hf,
      (by decide : extraMulFin (extraMulFin 1 16) (extraMulFin 1 16) =
        extraMulFin (extraMulFin 8 2) (extraMulFin 8 2))]
  have hs0 : pm (pm (f 1).val (f 16).val) (pm (f 1).val (f 16).val) ≠ 0 := by
    rw [pm_vals hf 1 16, pm_vals hf]
    intro h
    exact hne _ (by decide) (Fin.ext h)
  have hmem := enum_sound ch271071_cmp ch271071_enum m1 m2 m8 m16 hab hac hbd hcd hs hs0
  obtain ⟨e, he, hke⟩ := List.mem_iff_getElem.mp hmem
  have he' : e < 1152 := autK_len ▸ he
  refine ⟨e, he', ?_⟩
  obtain ⟨ha, hk⟩ := gF_spec he'
  have hkey : l20 AKP e = keyN (f 1).val (f 2).val (f 8).val (f 16).val := (akp_lane e he).trans hke
  have hF := keyN_fields (f 1).isLt (f 2).isLt (f 8).isLt (f 16).isLt
  rw [← hkey] at hF
  refine S5Ext.hom_ext_gens _ _ (fun i j => toF_hom ha i j) (fun i j => hf i j)
    (hom_zero (toF_hom ha)) h0 ?_ ?_ ?_ ?_
  · exact Fin.ext ((toF_val ha 1).trans (hk.1.trans hF.1))
  · exact Fin.ext ((toF_val ha 2).trans (hk.2.1.trans hF.2.1))
  · exact Fin.ext ((toF_val ha 8).trans (hk.2.2.1.trans hF.2.2.1))
  · exact Fin.ext ((toF_val ha 16).trans (hk.2.2.2.trans hF.2.2.2))

theorem tab_inj' {e e' : Nat} (he : e < 1152) (he' : e' < 1152) (h : toF (gF e) = toF (gF e')) :
    e = e' := by
  have hk := key_eq_of_toF (gF_spec he).1 (gF_spec he').1 (gF_spec he).2 (gF_spec he').2
    (l20_lt _ _) (l20_lt _ _) h
  have hl : e < autK.length := autK_len ▸ he
  have hl' : e' < autK.length := autK_len ▸ he'
  rw [akp_lane e hl, akp_lane e' hl'] at hk
  have hnd : autK.Nodup := autK_sort.1.imp fun h => Nat.ne_of_lt h
  exact hnd.getElem_inj_iff.mp hk

theorem el_all : ∀ g, g < 128 →
    IsAutN (lT (lE ELP g)) ∧ HasKey (lT (lE ELP g)) (l20 KEYL g) := by
  intro g hg
  rcases (by omega : g < 32 ∨ (32 ≤ g ∧ g < 64) ∨ (64 ≤ g ∧ g < 96) ∨ 96 ≤ g) with
    h | h | h | h
  · exact el_sound ch271071_el0 g (by omega) (by omega)
  · exact el_sound ch271071_el1 g h.1 (by omega)
  · exact el_sound ch271071_el2 g h.1 (by omega)
  · exact el_sound ch271071_el3 g h (by omega)

theorem rows_all : ∀ g c, g < 128 → c < 128 → ∀ f : Nat → Nat, HasKey f (l20 KEYL c) →
    HasKey (fun x => lT (lE ELP g) (f x)) (l20 KEYL (lM MP g c)) := by
  intro g c hg hc
  rcases (by omega : g < 32 ∨ (32 ≤ g ∧ g < 64) ∨ (64 ≤ g ∧ g < 96) ∨ 96 ≤ g) with
    h | h | h | h
  · exact rows_sound ch271071_rows0 g c (by omega) (by omega) hc
  · exact rows_sound ch271071_rows1 g c h.1 (by omega) hc
  · exact rows_sound ch271071_rows2 g c h.1 (by omega) hc
  · exact rows_sound ch271071_rows3 g c h (by omega) hc

theorem isAutN_comp {f g : Nat → Nat} (hf : IsAutN f) (hg : IsAutN g) :
    IsAutN (fun x => f (g x)) := by
  refine ⟨fun x hx => hf.1 _ (hg.1 x hx), fun x y hx hy => ?_, fun x y hx hy h => ?_⟩
  · change f (g (pm x y)) = pm (f (g x)) (f (g y))
    rw [hg.2.1 x y hx hy, hf.2.1 _ _ (hg.1 x hx) (hg.1 y hy)]
  · exact hg.2.2 x y hx hy (hf.2.2 _ _ (hg.1 x hx) (hg.1 y hy) h)

theorem isAutN_id : IsAutN id :=
  ⟨fun _ hx => hx, fun x y hx hy => rfl, fun _ _ _ _ h => h⟩

theorem lM_lt (MP g c : Nat) : lM MP g c < 128 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem lCI_lt (CIL t : Nat) : lCI CIL t < 128 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem lmul_tab' {g c : Nat} (hg : g < 128) (hc : c < 128) (x : Fin 32) :
    toF (lT (lE ELP (lM MP g c))) x = toF (lT (lE ELP g)) (toF (lT (lE ELP c)) x) := by
  have hgc := el_all _ (lM_lt MP g c)
  have hcomp := isAutN_comp (el_all g hg).1 (el_all c hc).1
  have he := toF_eq_of_key hgc.1 hcomp hgc.2 (rows_all g c hg hc _ (el_all c hc).2)
  rw [he]
  apply Fin.ext
  rw [toF_val hcomp, toF_val (el_all g hg).1, toF_val (el_all c hc).1]

theorem invs_all : l20 KEYL LIDE = IDK ∧
    ∀ g, g < 128 → lM MP g (lI INVP g) = LIDE ∧ lI INVP g < 128 :=
  inv_sound ch271071_inv

theorem lide_lt' : LIDE < 128 := by
  rw [← (invs_all.2 0 (by decide)).1]
  exact lM_lt _ _ _

theorem idk_key : HasKey id IDK := by
  unfold HasKey IDK
  decide

theorem lide_tab' (x : Fin 32) : toF (lT (lE ELP LIDE)) x = x := by
  have h := el_all _ lide_lt'
  rw [invs_all.1] at h
  rw [toF_eq_of_key h.1 isAutN_id h.2 idk_key]
  exact Fin.ext (toF_val isAutN_id x)

theorem ltab_inj' {g g' : Nat} (hg : g < 128) (hg' : g' < 128)
    (h : toF (lT (lE ELP g)) = toF (lT (lE ELP g'))) : g = g' := by
  have hk := key_eq_of_toF (el_all g hg).1 (el_all g' hg').1 (el_all g hg).2 (el_all g' hg').2
    (l20_lt _ _) (l20_lt _ _) h
  have hinc := inc_sound ch271071_inc
  rcases Nat.lt_trichotomy g g' with hl | hl | hl
  · exact absurd hk (Nat.ne_of_lt (hinc g g' hl (by omega)))
  · exact hl
  · exact absurd hk.symm (Nat.ne_of_lt (hinc g' g hl (by omega)))

def RecC (k : Nat) : Prop :=
  ∀ g, g < 128 → tb (lC CATP k) g = false → tb (lC CATP k) (lM MP g g) = true →
    (∀ c, c < 128 → tb (lC CATP k) c = true →
      tb (lC CATP k) (lM MP (lM MP g c) (lI INVP g)) = true) →
    ∃ g₀ k', g₀ < 128 ∧ tb (lC CATP k') g = true ∧
      ∀ x, tb (lC CATP k') x = true ↔
        (tb (lC CATP k) x = true ∨ ∃ c, c < 128 ∧ tb (lC CATP k) c = true ∧ lM MP g₀ c = x)

def WitC (k : Nat) : Prop :=
  ∃ as ts : List Nat, as.length + ts.length ≤ 4 ∧
    (∀ a ∈ as, tb (lC CATP k) a = true) ∧
    (∀ t ∈ ts, t < 32 ∧ tb (lC CATP k) (lCI CIL t) = true) ∧
    (∀ P : Nat → Prop, (∀ i, i < 32 → tb (lC CATP k) (lCI CIL i) = true → P (lCI CIL i)) →
      (∀ a ∈ as, ∀ x, x < 128 → P x → P (lM MP a x)) →
      ∀ α, tb (lC CATP k) α = true → P α) ∧
    (∀ Q : Nat → Prop, (∀ α, tb (lC CATP k) α = true → ∀ t ∈ ts, Q (lT (lE ELP α) t)) →
      (∀ x y, Q x → Q y → Q (pm x y)) → ∀ i, i < 32 → tb (lC CATP k) (lCI CIL i) = true → Q i)

theorem by_chunk {P : Nat → Prop} (hc : ∀ i, i < 18 → ∀ k, 32 * i ≤ k → k < 32 * i + 32 → P k) :
    ∀ k, k < 576 → P k :=
  fun k hk => hc (k / 32) (by omega) k (by omega) (by omega)

theorem recs_all : ∀ k, k < 576 → RecC k := by
  apply by_chunk
  intro i hi k h1 h2
  have hs := ch271071_sq
  interval_cases i
  · exact recs_sound hs ch271071_r0 k h1 (by rw [(by decide +kernel : r0.length = 32)]; omega)
  · exact recs_sound hs ch271071_r1 k h1 (by rw [(by decide +kernel : r1.length = 32)]; omega)
  · exact recs_sound hs ch271071_r2 k h1 (by rw [(by decide +kernel : r2.length = 32)]; omega)
  · exact recs_sound hs ch271071_r3 k h1 (by rw [(by decide +kernel : r3.length = 32)]; omega)
  · exact recs_sound hs ch271071_r4 k h1 (by rw [(by decide +kernel : r4.length = 32)]; omega)
  · exact recs_sound hs ch271071_r5 k h1 (by rw [(by decide +kernel : r5.length = 32)]; omega)
  · exact recs_sound hs ch271071_r6 k h1 (by rw [(by decide +kernel : r6.length = 32)]; omega)
  · exact recs_sound hs ch271071_r7 k h1 (by rw [(by decide +kernel : r7.length = 32)]; omega)
  · exact recs_sound hs ch271071_r8 k h1 (by rw [(by decide +kernel : r8.length = 32)]; omega)
  · exact recs_sound hs ch271071_r9 k h1 (by rw [(by decide +kernel : r9.length = 32)]; omega)
  · exact recs_sound hs ch271071_r10 k h1 (by rw [(by decide +kernel : r10.length = 32)]; omega)
  · exact recs_sound hs ch271071_r11 k h1 (by rw [(by decide +kernel : r11.length = 32)]; omega)
  · exact recs_sound hs ch271071_r12 k h1 (by rw [(by decide +kernel : r12.length = 32)]; omega)
  · exact recs_sound hs ch271071_r13 k h1 (by rw [(by decide +kernel : r13.length = 32)]; omega)
  · exact recs_sound hs ch271071_r14 k h1 (by rw [(by decide +kernel : r14.length = 32)]; omega)
  · exact recs_sound hs ch271071_r15 k h1 (by rw [(by decide +kernel : r15.length = 32)]; omega)
  · exact recs_sound hs ch271071_r16 k h1 (by rw [(by decide +kernel : r16.length = 32)]; omega)
  · exact recs_sound hs ch271071_r17 k h1 (by rw [(by decide +kernel : r17.length = 32)]; omega)

theorem wits_all : ∀ k, k < 576 → WitC k := by
  apply by_chunk
  intro i hi k h1 h2
  interval_cases i
  · exact wits_sound ch271071_w0 k h1 (by rw [(by decide +kernel : w0.length = 32)]; omega)
  · exact wits_sound ch271071_w1 k h1 (by rw [(by decide +kernel : w1.length = 32)]; omega)
  · exact wits_sound ch271071_w2 k h1 (by rw [(by decide +kernel : w2.length = 32)]; omega)
  · exact wits_sound ch271071_w3 k h1 (by rw [(by decide +kernel : w3.length = 32)]; omega)
  · exact wits_sound ch271071_w4 k h1 (by rw [(by decide +kernel : w4.length = 32)]; omega)
  · exact wits_sound ch271071_w5 k h1 (by rw [(by decide +kernel : w5.length = 32)]; omega)
  · exact wits_sound ch271071_w6 k h1 (by rw [(by decide +kernel : w6.length = 32)]; omega)
  · exact wits_sound ch271071_w7 k h1 (by rw [(by decide +kernel : w7.length = 32)]; omega)
  · exact wits_sound ch271071_w8 k h1 (by rw [(by decide +kernel : w8.length = 32)]; omega)
  · exact wits_sound ch271071_w9 k h1 (by rw [(by decide +kernel : w9.length = 32)]; omega)
  · exact wits_sound ch271071_w10 k h1 (by rw [(by decide +kernel : w10.length = 32)]; omega)
  · exact wits_sound ch271071_w11 k h1 (by rw [(by decide +kernel : w11.length = 32)]; omega)
  · exact wits_sound ch271071_w12 k h1 (by rw [(by decide +kernel : w12.length = 32)]; omega)
  · exact wits_sound ch271071_w13 k h1 (by rw [(by decide +kernel : w13.length = 32)]; omega)
  · exact wits_sound ch271071_w14 k h1 (by rw [(by decide +kernel : w14.length = 32)]; omega)
  · exact wits_sound ch271071_w15 k h1 (by rw [(by decide +kernel : w15.length = 32)]; omega)
  · exact wits_sound ch271071_w16 k h1 (by rw [(by decide +kernel : w16.length = 32)]; omega)
  · exact wits_sound ch271071_w17 k h1 (by rw [(by decide +kernel : w17.length = 32)]; omega)

theorem tb_zero (g : Nat) : tb 0 g = false := by
  unfold tb
  rw [Nat.zero_shiftRight, Nat.zero_and]
  rfl

theorem cat_K {k g : Nat} (h : tb (lC CATP k) g = true) : k < 576 := by
  by_contra hk
  rw [bnd_sound ch271071_bnd k (by omega), tb_zero] at h
  exact Bool.false_ne_true h

@[expose] def fin32 (n : Nat) : Fin 32 := ⟨n % 32, Nat.mod_lt _ (by decide)⟩

theorem fin32_val (x : Fin 32) : fin32 x.val = x := Fin.ext (Nat.mod_eq_of_lt x.isLt)

theorem cat_wit' (k : Nat) (hk : k < 576) : ∃ (as : List ℕ) (ts : List (Fin 32)),
    as.length + ts.length ≤ 4 ∧ (∀ a ∈ as, tb (lC CATP k) a = true) ∧
    (∀ t ∈ ts, tb (lC CATP k) (lCI CIL t.val) = true) ∧
    (∀ P : ℕ → Prop, (∀ i : Fin 32, tb (lC CATP k) (lCI CIL i.val) = true → P (lCI CIL i.val)) →
      (∀ a ∈ as, ∀ x, x < 128 → P x → P (lM MP a x)) → ∀ α, tb (lC CATP k) α = true → P α) ∧
    (∀ Q : Fin 32 → Prop, (∀ α, tb (lC CATP k) α = true → ∀ t ∈ ts, Q (toF (lT (lE ELP α)) t)) →
      (∀ x y, Q x → Q y → Q (extraMulFin x y)) →
      ∀ i : Fin 32, tb (lC CATP k) (lCI CIL i.val) = true → Q i) := by
  obtain ⟨as, ts, hlen, has, hts, hP, hQ⟩ := wits_all k hk
  refine ⟨as, ts.map fin32, by rw [List.length_map]; exact hlen, has, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
    change tb (lC CATP k) (lCI CIL (t0 % 32)) = true
    rw [Nat.mod_eq_of_lt (hts t0 ht0).1]
    exact (hts t0 ht0).2
  · intro P h1 h2
    exact hP P (fun i hi => h1 ⟨i, hi⟩) h2
  · intro Q h1 h2 i hi
    have hQ' := hQ (fun n => n < 32 ∧ Q (fin32 n))
      (fun α hα t ht => by
        refine ⟨Nat.lt_of_le_of_lt Nat.and_le_right (by decide), ?_⟩
        have he : fin32 (lT (lE ELP α) t) = toF (lT (lE ELP α)) (fin32 t) := by
          apply Fin.ext
          change lT (lE ELP α) t % 32 = lT (lE ELP α) (t % 32) % 32
          rw [Nat.mod_eq_of_lt (hts t ht).1]
        rw [he]
        exact h1 α hα _ (List.mem_map.mpr ⟨t, ht, rfl⟩))
      (fun x y hx hy => by
        refine ⟨pm_lt' hx.1 hy.1, ?_⟩
        have he : fin32 (pm x y) = extraMulFin (fin32 x) (fin32 y) := by
          apply Fin.ext
          rw [extraMulFin_val]
          change pm x y % 32 = pm (x % 32) (y % 32)
          rw [Nat.mod_eq_of_lt hx.1, Nat.mod_eq_of_lt hy.1, Nat.mod_eq_of_lt (pm_lt' hx.1 hy.1)]
        rw [he]
        exact h2 _ _ hx.2 hy.2) i.val i.isLt hi
    rw [← fin32_val i]
    exact hQ'.2

noncomputable def s5kFacts : S5KFacts where
  N := 1152
  tab e := toF (gF e)
  tab_hom e he i j := toF_hom (gF_spec he).1 i j
  tab_injective e he := toF_injective (gF_spec he).1
  complete f hf hi := tab_complete f hf hi
  tab_inj e e' he he' h := tab_inj' he he' h
  N_eq := by norm_num
  M := 128
  ltab g := toF (lT (lE ELP g))
  ltab_hom g hg i j := toF_hom (el_all g hg).1 i j
  ltab_injective g hg := toF_injective (el_all g hg).1
  ltab_inj g g' hg hg' h := ltab_inj' hg hg' h
  M_eq := by norm_num
  lmul := lM MP
  lmul_lt g c _ _ := lM_lt MP g c
  lmul_tab g c hg hc x := lmul_tab' hg hc x
  lide := LIDE
  lide_lt := lide_lt'
  lide_tab := lide_tab'
  linv := lI INVP
  linv_lt g hg := (invs_all.2 g hg).2
  linv_tab g hg x := by
    have hgi := (invs_all.2 g hg)
    apply toF_injective (el_all g hg).1
    rw [← lmul_tab' hg hgi.2, hgi.1, lide_tab']
  lci i := lCI CIL i.val
  lci_lt i := lCI_lt CIL i.val
  lci_tab i x := by
    have ha := (el_all _ (lCI_lt CIL i.val)).1
    apply Fin.ext
    rw [extraMulFin_val, extraMulFin_val, toF_val ha]
    exact ci_sound ch271071_ci i.val x.val i.isLt x.isLt
  K := 576
  Cat k g := tb (lC CATP k) g = true
  cat_lt _ _ _ h := tb_lC_lt h
  cat_one := ⟨ONEK, by decide +kernel, fun g => by
    rw [Nat.eq_of_beq_eq_true ch271071_one]
    exact tb_single⟩
  cat_step k hk g hg hng hsq hn := by
    obtain ⟨g₀, k', hg₀, hk', hiff⟩ := recs_all k hk g hg (by simpa using hng) hsq
      (fun c _ hc => hn c hc)
    refine ⟨k', cat_K hk', g₀, hg₀, hk', fun x => ?_⟩
    rw [hiff x]
    constructor
    · rintro (h | ⟨c, _, hc, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨c, hc, rfl⟩
    · rintro (h | ⟨c, hc, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨c, tb_lC_lt hc, hc, rfl⟩
  cat_wit k hk := cat_wit' k hk

end CertificateChecks.S5K
