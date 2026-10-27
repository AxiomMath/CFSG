module

public import Certificates.Kernel.J3Coset.Cover
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3OuterInvSound
import Certificates.Kernel.J3Coset.ChecksSmall

public section

namespace CertificateChecks.KernelJ3C

open CFSG.KC.J3C CFSG.KD.J3C CFSG.KS MulAction CFSG.AGLEmbedding.KFactProofs.J3Sylow
  CFSG.AGLEmbedding.KFactProofs.J3OuterInv CFSG.Quasithin

@[expose] noncomputable def tau : Equiv.Perm (Fin nn) where
  toFun i := ⟨tb 8 i.val, (perm_facts i.val i.isLt).2.2.2.2.2.2.1⟩
  invFun i := ⟨tb 9 i.val, (perm_facts i.val i.isLt).2.2.2.2.2.2.2.1⟩
  left_inv i := Fin.ext (perm_facts i.val i.isLt).2.2.2.2.2.2.2.2.1
  right_inv i := Fin.ext (perm_facts i.val i.isLt).2.2.2.2.2.2.2.2.2

theorem tau_val (i : Fin nn) : (tau i).val = tb 8 i.val := rfl

theorem tau_symm_val (i : Fin nn) : (tau.symm i).val = tb 9 i.val := rfl

theorem out_facts : codesIn 6 7 phiW1 = true ∧ codesIn 6 7 phiW2 = true ∧
    (wv tb [8, 6, 9] beta0 == wv tb phiW1 beta0) = true ∧
    (wv tb [8, 7, 9] beta0 == wv tb phiW2 beta0) = true ∧
    (!memB (maskOf Oc.flatten) (tb 8 beta0)) = true ∧
    (∀ r ∈ Zr, (r.1 == beta0 || (List.range' 1 7).all fun k =>
      !(baseEq tb beta0 (rep k [5] ++ r.2) (r.2 ++ rep k [5]))) = true) := by
  have h := out_ok
  unfold outChk at h
  simp only [Bool.and_eq_true, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, List.all_eq_true.1 h6⟩

theorem tau_zero : tau pt0 = pt0 := Fin.ext fix_facts.2.2.2.2.1

theorem tau_symm_zero : tau.symm pt0 = pt0 := by
  rw [Equiv.symm_apply_eq, tau_zero]

theorem y_facts : ∀ r ∈ Oc.flatten, r.2.2.2.1 < nn := by
  have h := y_ok
  unfold yChk at h
  rw [List.all_eq_true] at h
  intro r hr
  have := h r hr
  simpa using this

section Outer

variable {J : Type} [Group J] [Finite J] [MulAction J (Fin nn)] {g : ℕ → J}

variable (hg : Acts g)
include hg

theorem stab_orbit (hJ : Nat.card J = 50232960) {k : J} (hk : k ∈ stabilizer J pt0) :
    (k • ptB).val ∈ Oc.flatten.map Prod.fst := by
  obtain ⟨hnd, hlen, hrec⟩ := o_facts
  have hlt : ∀ x ∈ Oc.flatten.map Prod.fst, x < nn := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
    rw [← (hrec r hr).2]
    exact wv_lt hg (codesIn_lt (hrec r hr).1 (by decide) (by decide)) beta0_lt
  set S : Set (Fin nn) := {q : Fin nn | q.val ∈ Oc.flatten.map Prod.fst}
  have hS : S ⊆ orbit (stabilizer J pt0) ptB := by
    intro q hq
    obtain ⟨r, hr, hrq⟩ := List.mem_map.1 hq
    obtain ⟨hc, hv⟩ := hrec r hr
    refine ⟨⟨ev g r.2.1, k_stab hg hc⟩, Fin.ext ?_⟩
    change (ev g r.2.1 • ptB).val = q.val
    rw [ev_smul hg (codesIn_lt hc (by decide) (by decide))]
    exact hv.trans hrq
  have hSn : S.ncard = 1944 := by rw [ncard_val_mem hnd hlt, List.length_map, hlen]
  have hidx := Subgroup.card_mul_index (stabilizer (stabilizer J pt0) ptB)
  rw [index_stabilizer, card_stab hJ hg] at hidx
  have hpos : 0 < Nat.card (stabilizer (stabilizer J pt0) ptB) := Nat.card_pos
  have hle : (orbit (stabilizer J pt0) ptB).ncard ≤ S.ncard := by
    rw [hSn]
    have := Nat.le_mul_of_pos_left ((orbit (stabilizer J pt0) ptB).ncard) hpos
    omega
  have heq := Set.eq_of_subset_of_ncard_le hS hle (Set.toFinite _)
  have hmem : k • ptB ∈ orbit (stabilizer J pt0) ptB := ⟨⟨k, hk⟩, rfl⟩
  rw [← heq] at hmem
  exact hmem

theorem stab_word (hJ : Nat.card J = 50232960) {x : J} (hx : x ∈ stabilizer J pt0) :
    ∃ r ∈ Oc.flatten, x = ev g r.2.1 ∧ r.1 = (x • ptB).val := by
  obtain ⟨r, hr, hrx⟩ := List.mem_map.1 (stab_orbit hg hJ hx)
  obtain ⟨hc, hv⟩ := o_facts.2.2 r hr
  refine ⟨r, hr, base_eq hJ hg ?_ ?_, hrx⟩
  · rw [mem_stabilizer_iff.1 hx, mem_stabilizer_iff.1 (k_stab hg hc)]
  · apply Fin.ext
    rw [ev_smul hg (codesIn_lt hc (by decide) (by decide))]
    exact hrx.symm.trans hv.symm

theorem outer [IsSimpleGroup J] (hJ : Nat.card J = 50232960)
    (hgen : Subgroup.closure ({g 0, g 2} : Set J) = ⊤) :
    ∃ φ : MulAut J, (∀ x ∈ PP g, φ x ∈ PP g) ∧ φ ∉ (MulAut.conj : J →* MulAut J).range ∧
      (∀ z ∈ centerOf (PP g), z ≠ 1 →
        Subgroup.centralizer {z} ≤ Subgroup.normalizer ((PP g : Subgroup J) : Set J) →
        Subgroup.centralizer {z} ≤ PP g) ∧
      (∀ x ∈ Subgroup.normalizer ((PP g : Subgroup J) : Set J), (MulAut.conj x * φ) ^ 2 = 1 →
        ∀ E : Subgroup J, E ≤ PP g → IsMulCommutative E → (∀ e ∈ E, e ^ 3 = 1) →
          Nat.card E = 9 → ∃ e ∈ E, (MulAut.conj x * φ) e ≠ e) := by
  have := faithful hg
  have D := localData hg hJ
  have hco := coatom hg hJ
  have hN : Subgroup.normalizer ((PP g : Subgroup J) : Set J) = stabilizer J pt0 :=
    D.normalizer_eq hco
  have cA := codesAB_lt fix_facts.2.2.2.2.2.2.2.2.2.2.1
  have cB := codesAB_lt fix_facts.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨o1, o2, o3, o4, o5, o6⟩ := out_facts
  have ha : tau * MulAction.toPermHom J (Fin nn) (g 0) =
      MulAction.toPermHom J (Fin nn) (ev g phiA) * tau := by
    ext i
    simp only [Equiv.Perm.mul_apply, MulAction.toPermHom_apply, MulAction.toPerm_apply]
    rw [tau_val, ev_smul hg cA, tau_val, hg 0 (by decide)]
    exact (s_facts i.val i.isLt).1
  have hb : tau * MulAction.toPermHom J (Fin nn) (g 2) =
      MulAction.toPermHom J (Fin nn) (ev g phiB) * tau := by
    ext i
    simp only [Equiv.Perm.mul_apply, MulAction.toPermHom_apply, MulAction.toPerm_apply]
    rw [tau_val, ev_smul hg cB, tau_val, hg 2 (by decide)]
    exact (s_facts i.val i.isLt).2
  obtain ⟨φ, hφ⟩ := exists_induced_aut hgen tau ha hb
  have hφpt : ∀ x i, φ x • i = tau (x • tau.symm i) := by
    intro x i
    have := congrArg (fun π : Equiv.Perm (Fin nn) => π i) (hφ x)
    simpa [Equiv.Perm.mul_apply, Equiv.Perm.inv_def] using this
  have hφp : ∀ c, c = 6 ∨ c = 7 → ∃ w, codesIn 6 7 w = true ∧ φ (g c) = ev g w := by
    intro c hc
    have key : ∀ w, codesIn 6 7 w = true → (wv tb [8, c, 9] beta0 == wv tb w beta0) = true →
        φ (g c) = ev g w := by
      intro w hw hb'
      apply base_eq hJ hg
      · rw [hφpt, tau_symm_zero, mem_stabilizer_iff.1 (P_le_stab hg
            (Subgroup.subset_closure (by rcases hc with rfl | rfl <;> simp))), tau_zero,
          mem_stabilizer_iff.1 (P_le_stab hg (ev_P hw))]
      · apply Fin.ext
        rw [hφpt, tau_val, hg c (by omega), tau_symm_val,
          ev_smul hg (codesIn_lt hw (by decide) (by decide))]
        have e := eq_of_beq hb'
        rw [wv_cons, wv_cons, wv_cons] at e
        exact e
    rcases hc with rfl | rfl
    · exact ⟨phiW1, o1, key phiW1 o1 o3⟩
    · exact ⟨phiW2, o2, key phiW2 o2 o4⟩
  have hφP : ∀ x ∈ PP g, φ x ∈ PP g := by
    have hle : PP g ≤ (PP g).comap φ.toMonoidHom := by
      rw [PP, Subgroup.closure_le]
      rintro _ (rfl | h)
      · obtain ⟨w, hw, e⟩ := hφp 6 (Or.inl rfl)
        change φ (g 6) ∈ PP g
        rw [e]
        exact ev_P hw
      · rw [Set.mem_singleton_iff] at h
        subst h
        obtain ⟨w, hw, e⟩ := hφp 7 (Or.inr rfl)
        change φ (g 7) ∈ PP g
        rw [e]
        exact ev_P hw
    exact fun x hx => hle hx
  refine ⟨φ, hφP, ?_, ?_, ?_⟩
  ·
    rintro ⟨h, hh⟩
    have hNh : h ∈ Subgroup.normalizer ((PP g : Subgroup J) : Set J) := by
      apply Subgroup.mem_normalizer_fintype
      intro n hn
      have := hφP n hn
      rw [← hh] at this
      simpa [MulAut.conj_apply] using this
    rw [hN] at hNh
    set c : Equiv.Perm (Fin nn) := (MulAction.toPermHom J (Fin nn) h)⁻¹ * tau
    have hc0 : c pt0 = pt0 := by
      simp only [c, Equiv.Perm.mul_apply, tau_zero]
      rw [Equiv.Perm.inv_eq_iff_eq]
      simp only [MulAction.toPermHom_apply, MulAction.toPerm_apply]
      exact (mem_stabilizer_iff.1 hNh).symm
    have hcc : ∀ x : J, c * MulAction.toPermHom J (Fin nn) x =
        MulAction.toPermHom J (Fin nn) x * c := by
      intro x
      have h1 := hφ x
      rw [← hh, MulAut.conj_apply, map_mul, map_mul, map_inv] at h1
      simp only [c]
      have : tau * MulAction.toPermHom J (Fin nn) x =
          MulAction.toPermHom J (Fin nn) h * MulAction.toPermHom J (Fin nn) x *
            (MulAction.toPermHom J (Fin nn) h)⁻¹ * tau := by
        rw [h1]; group
      rw [mul_assoc, this]
      group
    have hc1 := eq_one_of_comm (trans hg) hc0 hcc
    have htau : tau = MulAction.toPermHom J (Fin nn) h := by
      simp only [c] at hc1
      exact (inv_mul_eq_one.1 hc1).symm
    have hB := stab_orbit hg hJ hNh
    have e1 : (h • ptB).val = tb 8 beta0 := by
      have := congrArg (fun π : Equiv.Perm (Fin nn) => (π ptB).val) htau
      simp only [MulAction.toPermHom_apply, MulAction.toPerm_apply] at this
      rw [tau_val] at this
      exact this.symm
    rw [e1] at hB
    have hm : memB (maskOf Oc.flatten) (tb 8 beta0) = true := by
      rw [memB_maskOf]
      obtain ⟨r, hr, e⟩ := List.mem_map.1 hB
      exact ⟨r, hr, e⟩
    rw [hm] at o5
    exact absurd o5 (by decide)
  ·
    intro z hz hz1 hC y hy
    have hyH : y ∈ stabilizer J pt0 := by rw [← hN]; exact hC hy
    obtain ⟨k, hk8, p, hp, rfl⟩ := D.decomp hyH
    have hzc : g 5 ^ k * p * z = z * (g 5 ^ k * p) := Subgroup.mem_centralizer_singleton_iff.1 hy
    have hpz : p * z = z * p := (mem_centerOf.1 hz).2 p hp
    have hsz : g 5 ^ k * z = z * g 5 ^ k := by
      have h1 : g 5 ^ k * z * p = z * g 5 ^ k * p := by
        calc g 5 ^ k * z * p = g 5 ^ k * (p * z) := by rw [mul_assoc, hpz]
          _ = z * (g 5 ^ k * p) := by rw [← mul_assoc, hzc]
          _ = z * g 5 ^ k * p := by rw [mul_assoc]
      exact mul_right_cancel h1
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [pow_zero, one_mul]
      exact hp
    · exfalso
      obtain ⟨i, rfl⟩ := (D.Z_mem z).1 hz
      have hr := List.getElem_mem (l := Zr) (zr_lt i)
      obtain ⟨hzP, -, -, -, hzv⟩ := zz_facts hg hJ i
      have h6 := o6 _ hr
      simp only [Bool.or_eq_true, beq_iff_eq, List.all_eq_true] at h6
      rcases h6 with h | h
      · apply hz1
        apply free hJ hg (P_le_stab hg hzP)
        apply Fin.ext
        rw [hzv, h]
        rfl
      · have hk := h k (List.mem_range'_1.2 ⟨hk0, by omega⟩)
        have hc8 := codesIn_lt (zr_facts _ hr).1 (by decide) (by decide)
        have hne := word_ne' hg (rep k [5] ++ (Zr[i.val]'(zr_lt i)).2)
          ((Zr[i.val]'(zr_lt i)).2 ++ rep k [5]) (codes_app (rep_codes s_codes k) hc8)
          (codes_app hc8 (rep_codes s_codes k)) hk
        rw [ev_append, ev_append, ev_rep, ev_single] at hne
        apply hne
        have hzi : zz g i = ev g (Zr[i.val]'(zr_lt i)).2 := by unfold zz; rw [zr_get]
        rw [← hzi]
        exact hsz
  ·
    intro x hx hsq E hEP _ hE3 hE9
    by_contra hfix
    push Not at hfix
    rw [hN] at hx
    obtain ⟨r, hr, rfl, -⟩ := stab_word hg hJ hx
    have hc8 := codesIn_lt (o_facts.2.2 r hr).1 (by decide) (by decide)
    set u : Equiv.Perm (Fin nn) := MulAction.toPermHom J (Fin nn) (ev g r.2.1) * tau with hu_def
    have hu : ∀ i, (u i).val = wv tb r.2.1 (tb 8 i.val) := by
      intro i
      simp only [hu_def, Equiv.Perm.mul_apply, MulAction.toPermHom_apply,
        MulAction.toPerm_apply]
      rw [ev_smul hg hc8, tau_val]
    have hconj : ∀ e, MulAction.toPermHom J (Fin nn) ((MulAut.conj (ev g r.2.1) * φ) e) =
        u * MulAction.toPermHom J (Fin nn) e * u⁻¹ := by
      intro e
      rw [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, hφ, hu_def]
      group
    have hu0 : u pt0 = pt0 := by
      simp only [hu_def, Equiv.Perm.mul_apply, tau_zero, MulAction.toPermHom_apply,
        MulAction.toPerm_apply]
      exact mem_stabilizer_iff.1 hx
    have hu2 : u * u = 1 := by
      refine eq_one_of_comm (trans hg) (by rw [Equiv.Perm.mul_apply, hu0, hu0]) fun e => ?_
      have h1 := congrArg (fun α : MulAut J => α e) hsq
      simp only [MulAut.one_apply] at h1
      rw [pow_two, MulAut.mul_apply] at h1
      have h2 := congrArg (MulAction.toPermHom J (Fin nn)) h1
      rw [hconj, hconj] at h2
      calc u * u * MulAction.toPermHom J (Fin nn) e
          = (u * (u * MulAction.toPermHom J (Fin nn) e * u⁻¹) * u⁻¹) * (u * u) := by group
        _ = MulAction.toPermHom J (Fin nn) e * (u * u) := by rw [h2]
    have hy := y_facts r hr
    have hrec := rec_facts r hr
    unfold recOK at hrec
    by_cases hk : (r.2.2.1 == 0) = true
    · rw [if_pos hk] at hrec
      apply ne_of_nb hrec
      have := congrArg (fun π : Equiv.Perm (Fin nn) => (π ⟨r.2.2.2.1, hy⟩).val) hu2
      simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] at this
      rw [hu, hu] at this
      exact this
    · rw [if_neg hk] at hrec
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hrec
      obtain ⟨⟨⟨⟨huy, hfw⟩, hf9⟩, hjs⟩, hall⟩ := hrec
      have hf8 := codesIn_lt hfw (by decide) (by decide)
      have hle : E ≤ Subgroup.zpowers (ev g r.2.2.2.2.1) := by
        intro e he
        obtain ⟨q, hq, rfl, hqv⟩ := elt_of_P hg hJ (hEP he)
        obtain ⟨hqc, hqw, -⟩ := q_facts.2.2.2 q hq
        have hq8 := codesIn_lt hqc (by decide) (by decide)
        have hfe := hfix _ he
        have hcomm : u * MulAction.toPermHom J (Fin nn) (ev g q.2) =
            MulAction.toPermHom J (Fin nn) (ev g q.2) * u := by
          have h2 := congrArg (MulAction.toPermHom J (Fin nn)) hfe
          rw [hconj] at h2
          calc u * MulAction.toPermHom J (Fin nn) (ev g q.2)
              = (u * MulAction.toPermHom J (Fin nn) (ev g q.2) * u⁻¹) * u := by group
            _ = MulAction.toPermHom J (Fin nn) (ev g q.2) * u := by rw [h2]
        have hpt := congrArg (fun π : Equiv.Perm (Fin nn) => (π ⟨r.2.2.2.1, hy⟩).val) hcomm
        simp only [Equiv.Perm.mul_apply, MulAction.toPermHom_apply, MulAction.toPerm_apply] at hpt
        rw [hu, ev_smul hg hq8, ev_smul hg hq8, hu] at hpt
        simp only at hpt
        rw [huy] at hpt
        obtain ⟨t, ht, hqt⟩ := List.getElem_of_mem hq
        have hQl : Qr.length = 243 := q_facts.2.1
        have htj : t < r.2.2.2.2.2.length := by rw [hjs]; rw [hQl] at ht; exact ht
        have hmem : (q, r.2.2.2.2.2[t]) ∈ Qr.zip r.2.2.2.2.2 := by
          rw [List.mem_iff_getElem]
          refine ⟨t, by rw [List.length_zip]; exact Nat.lt_min.2 ⟨ht, htj⟩, ?_⟩
          rw [List.getElem_zip, hqt]
        have hj := hall _ hmem
        by_cases hj9 : r.2.2.2.2.2[t] < 9
        · rw [if_pos hj9] at hj
          have he : ev g q.2 = ev g r.2.2.2.2.1 ^ r.2.2.2.2.2[t] := by
            rw [← ev_rep]
            apply base_eq hJ hg
            · rw [mem_stabilizer_iff.1 (P_le_stab hg (ev_P hqc)),
                mem_stabilizer_iff.1 (P_le_stab hg (ev_rep (g := g) _ _ ▸
                  Subgroup.pow_mem _ (ev_P hfw) _))]
            · apply Fin.ext
              rw [ev_smul hg hq8, ev_smul hg (rep_codes hf8 _)]
              exact hqw.trans (eq_of_beq hj).symm
          rw [he]
          exact ⟨(r.2.2.2.2.2[t] : ℤ), by simp⟩
        · rw [if_neg hj9] at hj
          exact absurd (hpt.trans hqw) (ne_of_nb hj)
      exact false_of_le_zpowers hE3 hE9 hle

end Outer

end CertificateChecks.KernelJ3C

end
