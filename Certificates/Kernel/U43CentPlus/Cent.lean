module

public import Certificates.Kernel.U43CentPlus.Sound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU43CentPlus

open CFSG.KC.Enum CFSG.KC.U43Mod CFSG.KC.U43CentPlus CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb
  CFSG.KS.U43Mod CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.EvenSporadicStandard.M24Std.CU43 CertificateChecks.KernelU43B CFSG.Quasithin.H13.U43
  CertificateChecks.KernelU43Mod Subgroup

theorem eq_or_eq_of_card_two {α : Type*} (h : Nat.card α = 2) {u v w : α} (huv : u ≠ v) :
    w = u ∨ w = v := by
  obtain ⟨x, y, -, hxy⟩ := Nat.card_eq_two_iff.1 h
  have hm : ∀ z : α, z = x ∨ z = y := fun z => by
    have : z ∈ ({x, y} : Set α) := hxy ▸ Set.mem_univ z
    simpa using this
  rcases hm u with rfl | rfl <;> rcases hm v with rfl | rfl <;> rcases hm w with rfl | rfl <;>
    simp_all

theorem kTM_spec {i j : ℕ} (hi : i < 3) (hj : j < 3) :
    TM (Nat.add (Nat.mul 3 i) j) < 128 ∧ baseEq bs (fun q => GT (Nat.succ i) (GT (Nat.succ j) q))
      (GC (TM (Nat.add (Nat.mul 3 i) j))) = true := by
  have h := allN_spec (allN_spec kTM i hi) j hj
  rw [CFSG.KS.U43Mod.strictB_eq, bAnd_iff, blt_iff] at h
  exact h

theorem kL_spec {c : ℕ} (hc : c < 128) : LT c < 128 := by
  have h := kL
  rw [Bool.and_eq_true] at h
  exact blt_iff.1 (allN_spec h.1 c hc)

theorem kL_inc : incK 128 (fun c => bKey (GC (LT c))) = true := by
  have h := kL
  rw [Bool.and_eq_true] at h
  exact h.2

theorem TP_mul_succ {i j : ℕ} (hi : i < 3) (hj : j < 3) :
    TP (Nat.succ i) * TP (Nat.succ j) = CE (TM (Nat.add (Nat.mul 3 i) j)) := by
  refine eq_of_baseEq (P.mul_mem (TP_mem (by omega)) (TP_mem (by omega)))
    (CE_mem (kTM_spec hi hj).1) (f := fun q => GT (Nat.succ i) (GT (Nat.succ j) q))
    (fun q hq => ?_) (GC_eq (kTM_spec hi hj).1) (kTM_spec hi hj).2
  rw [GT_eq (by omega : Nat.succ j < 4) q hq, GT_eq (by omega : Nat.succ i < 4) _ (Fin.is_lt _),
    Fin.eta, Equiv.Perm.mul_apply]

theorem one_eq_QP : ∃ j < 32, QP j = 1 := by
  obtain ⟨j, hj, e⟩ := QS_one
  exact ⟨j, hj, e⟩

theorem TP_mul {k m : ℕ} (hk : k < 4) (hm : m < 4) :
    ∃ x < 32, ∃ n < 4, TP k * TP m = QP x * TP n := by
  obtain ⟨j1, hj1, e1⟩ := one_eq_QP
  rcases k with _ | i
  · exact ⟨j1, hj1, m, hm, by rw [TP_zero, e1, one_mul]⟩
  rcases m with _ | j
  · exact ⟨j1, hj1, i + 1, hk, by rw [TP_zero, e1, mul_one, one_mul]⟩
  have hi : i < 3 := by omega
  have hj : j < 3 := by omega
  refine ⟨Nat.mod (TM (Nat.add (Nat.mul 3 i) j)) 32, mod32_lt _,
    Nat.div (TM (Nat.add (Nat.mul 3 i) j)) 32, div32_lt (kTM_spec hi hj).1, ?_⟩
  rw [TP_mul_succ hi hj, CE]

theorem iota_bij : Function.Bijective (fun j : Fin 32 => (⟨QP j, QP_mem_Q0 j.2⟩ : Q0)) := by
  refine ⟨fun i j e => Fin.ext (QP_inj i.2 j.2 (congrArg Subtype.val e)), ?_⟩
  rintro ⟨x, j, hj, rfl⟩
  exact ⟨⟨j, hj⟩, rfl⟩

@[expose] noncomputable def iota : Fin 32 ≃ Q0 := Equiv.ofBijective _ iota_bij

theorem iota_val (y : Fin 32) : ((iota y : Q0) : Equiv.Perm (Fin 820)) = QP y := by
  rw [iota, Equiv.ofBijective_apply]

@[expose] noncomputable def psi : H4 →* Equiv.Perm (Fin 32) :=
  (Equiv.permCongrHom iota.symm).toMonoidHom.comp
    ((MulAut.toPerm _).comp (Q0.normalizerMonoidHom.comp (inclusion H4_le_normalizer)))

theorem psi_apply (g : H4) (x : Fin 32) :
    psi g x = iota.symm (Q0.normalizerMonoidHom (inclusion H4_le_normalizer g) (iota x)) := rfl

theorem psi_spec (g : H4) (x : Fin 32) :
    QP (psi g x) = (g : Equiv.Perm (Fin 820)) * QP x * (g : Equiv.Perm (Fin 820))⁻¹ := by
  rw [← iota_val (psi g x), psi_apply, Equiv.apply_symm_apply, ← iota_val x]
  rfl

theorem psi_EP {i : ℕ} (hi : i < 4) (y : H4) (hy : (y : Equiv.Perm (Fin 820)) = EP i) :
    psi y = sig i := by
  refine Equiv.ext fun x => Fin.ext (QP_inj (Fin.is_lt _) (Fin.is_lt _) ?_)
  rw [psi_spec, sig_apply hi x, hy]
  exact EP_conj hi x.2

theorem range_psi : psi.range = closure (sig '' Set.Iio 4) := by
  have ht : closure (((↑) : H4 → Equiv.Perm (Fin 820)) ⁻¹' (m4 '' Set.Iio 4)) = ⊤ :=
    closure_closure_coe_preimage
  rw [MonoidHom.range_eq_map, ← ht, MonoidHom.map_closure]
  congr 1
  ext s
  constructor
  · rintro ⟨y, ⟨i, hi, hy⟩, rfl⟩
    have hi' : i < 4 := hi
    exact ⟨i, hi, (psi_EP hi' y (hy.symm.trans (EP_eq hi').symm)).symm⟩
  · rintro ⟨i, hi, rfl⟩
    have hi' : i < 4 := hi
    exact ⟨⟨m4 i, m4_mem_H4 hi'⟩, ⟨i, hi, rfl⟩, psi_EP hi' _ (EP_eq hi').symm⟩

theorem card_sig : Nat.card (closure (sig '' Set.Iio 4)) = 576 :=
  card_of_kTree (n := 32) (S := sig) (T := KP) (w := 5) (m := mask 5) (iw := 10) (im := mask 10)
    (bs := ix32) (G := GP) rfl (fun _ hp => List.mem_range.1 hp)
    (fun _ hj q hq => (sig_apply hj ⟨q, hq⟩).symm)
    (fun x _ y _ h => Equiv.ext fun z => h z.1 (List.mem_range.2 z.2)) kKP

theorem card_ker_psi : Nat.card psi.ker = 2 := by
  have h := Subgroup.card_mul_index psi.ker
  rw [Subgroup.index_ker, range_psi, card_sig, card_H4] at h
  omega

theorem cent_Q0 {g : Equiv.Perm (Fin 820)} (hg : g ∈ P) (hc : ∀ j < 32, g * QP j = QP j * g) :
    g = 1 ∨ g = CP 0 := by
  have hker : ∀ x (hx : x ∈ H4), (∀ j < 32, x * QP j = QP j * x) → (⟨x, hx⟩ : H4) ∈ psi.ker := by
    intro x hx hcx
    rw [MonoidHom.mem_ker]
    refine Equiv.ext fun y => Fin.ext (QP_inj (Fin.is_lt _) (Fin.is_lt _) ?_)
    rw [psi_spec, Equiv.Perm.one_apply]
    change x * QP y * x⁻¹ = QP y
    rw [hcx y y.2, mul_inv_cancel_right]
  have hgH : g ∈ H4 := mem_H4 hg (by rw [← QP_IA]; exact hc _ kIA_spec.1)
  have haH : CP 0 ∈ H4 := mem_H4 (CP_mem (by norm_num)) rfl
  have hu : (1 : H4) ∈ psi.ker := psi.ker.one_mem
  have hv := hker (CP 0) haH fun j hj => (comm_of_mem_H4 (QP_mem_H4 hj)).symm
  have hw := hker g hgH hc
  have huv : (⟨1, hu⟩ : psi.ker) ≠ ⟨⟨CP 0, haH⟩, hv⟩ := fun e =>
    CP0_ne (congrArg (fun z : psi.ker => ((z : H4) : Equiv.Perm (Fin 820))) e).symm
  rcases eq_or_eq_of_card_two card_ker_psi (w := ⟨⟨g, hgH⟩, hw⟩) huv with e | e
  · exact Or.inl (congrArg (fun z : psi.ker => ((z : H4) : Equiv.Perm (Fin 820))) e)
  · exact Or.inr (congrArg (fun z : psi.ker => ((z : H4) : Equiv.Perm (Fin 820))) e)

theorem S1_mul {x y : Equiv.Perm (Fin 820)} (hx : ∃ j < 32, ∃ k < 4, QP j * TP k = x)
    (hy : ∃ j < 32, ∃ k < 4, QP j * TP k = y) : ∃ j < 32, ∃ k < 4, QP j * TP k = x * y := by
  obtain ⟨j, hj, k, hk, rfl⟩ := hx
  obtain ⟨j', hj', k', hk', rfl⟩ := hy
  have hc : TP k * QP j' * (TP k)⁻¹ ∈ Q0 :=
    (mem_normalizer_iff.1 (H4_le_normalizer (TP_mem_H4 hk)) (QP j')).1 (QP_mem_Q0 hj')
  obtain ⟨j'', hj'', e''⟩ := mem_Q0.1 hc
  obtain ⟨x, hx, n, hn, et⟩ := TP_mul hk hk'
  have h1 := (kMT_spec hj hj'').1
  refine ⟨mtI (mtI j j'') x, (kMT_spec h1 hx).1, n, hn, ?_⟩
  have e : QP j * TP k * (QP j' * TP k') = QP j * (TP k * QP j' * (TP k)⁻¹) * (TP k * TP k') := by
    group
  rw [e, ← e'', et, ← mul_assoc, QP_mul hj hj'', QP_mul h1 hx]

theorem S1_one : ∃ j < 32, ∃ k < 4, QP j * TP k = 1 := by
  obtain ⟨j1, hj1, e1⟩ := one_eq_QP
  exact ⟨j1, hj1, 0, by norm_num, by rw [TP_zero, e1, one_mul]⟩

@[expose] noncomputable def S1 : Subgroup (Equiv.Perm (Fin 820)) where
  carrier := {g | ∃ j < 32, ∃ k < 4, QP j * TP k = g}
  mul_mem' := S1_mul
  one_mem' := S1_one
  inv_mem' := inv_mem_of_mul (S := {g | ∃ j < 32, ∃ k < 4, QP j * TP k = g}) S1_one
    fun _ hx _ hy => S1_mul hx hy

theorem CE_mem_S1 {c : ℕ} (hc : c < 128) : CE c ∈ S1 :=
  ⟨Nat.mod c 32, mod32_lt c, Nat.div c 32, div32_lt hc, by rw [CE]⟩

theorem mem_S1_iff {x : Equiv.Perm (Fin 820)} : x ∈ S1 ↔ ∃ c < 128, CE c = x := by
  constructor
  · rintro ⟨j, hj, k, hk, rfl⟩
    refine ⟨32 * k + j, by omega, ?_⟩
    have e1 : Nat.mod (32 * k + j) 32 = j := by
      change (32 * k + j) % 32 = j
      omega
    have e2 : Nat.div (32 * k + j) 32 = k := by
      change (32 * k + j) / 32 = k
      omega
    rw [CE, e1, e2]
  · rintro ⟨c, hc, rfl⟩
    exact CE_mem_S1 hc

theorem card_S1 : Nat.card S1 = 128 := by
  have h128 : Nat.card (Fin 128) = 128 := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  let f : Fin 128 → S1 := fun c => ⟨CE c, CE_mem_S1 c.2⟩
  have hf : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨c, hc, rfl⟩ := mem_S1_iff.1 hx
    exact ⟨⟨c, hc⟩, rfl⟩
  let g : Fin 128 → S1 := fun c => ⟨CE (LT c), CE_mem_S1 (kL_spec c.2)⟩
  have hg : Function.Injective g := fun a b e => Fin.ext (inj_of_incK (n := 128)
    (F := fun c => GC (LT c)) (g := fun c => CE (LT c)) (fun i hi => GC_eq (kL_spec hi)) kL_inc
    a.2 b.2 (congrArg Subtype.val e))
  have h1 := Nat.card_le_card_of_surjective f hf
  have h2 := Nat.card_le_card_of_injective g hg
  omega

theorem S1_le_H4 : S1 ≤ H4 := by
  rintro _ ⟨j, hj, k, hk, rfl⟩
  exact H4.mul_mem (QP_mem_H4 hj) (TP_mem_H4 hk)

end CertificateChecks.KernelU43CentPlus

end
