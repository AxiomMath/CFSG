module

public import Certificates.Kernel.J3Coset.Facts
public import Mathlib.GroupTheory.Subgroup.Simple
import Certificates.Kernel.J3Coset.ChecksSmall

public section

namespace CertificateChecks.KernelJ3C

open CFSG.KC.J3C CFSG.KD.J3C CFSG.KS CFSG.KS.Raw.Orb MulAction

theorem codesAB_lt {w : List ℕ} (h : codesAB w = true) : ∀ c ∈ w, c < 8 := by
  intro c hc
  unfold codesAB at h
  rw [List.all_eq_true] at h
  have := h c hc
  simp only [decide_eq_true_eq] at this
  omega

theorem codesIn_mem {a b : ℕ} {w : List ℕ} (h : codesIn a b w = true) :
    ∀ c ∈ w, c = a ∨ c = b := by
  intro c hc
  unfold codesIn at h
  rw [List.all_eq_true] at h
  have := h c hc
  simpa using this

theorem codesIn_lt {a b : ℕ} {w : List ℕ} (h : codesIn a b w = true) (ha : a < 8) (hb : b < 8) :
    ∀ c ∈ w, c < 8 := by
  intro c hc
  rcases codesIn_mem h c hc with rfl | rfl <;> assumption

theorem fix_facts : tb 4 0 = 0 ∧ tb 5 0 = 0 ∧ tb 6 0 = 0 ∧ tb 7 0 = 0 ∧ tb 8 0 = 0 ∧
    beta0 = tb 2 0 ∧ codesAB wK1 = true ∧ codesAB wK2 = true ∧ codesIn 4 5 wP1 = true ∧
    codesIn 4 5 wP2 = true ∧ codesAB phiA = true ∧ codesAB phiB = true ∧
    rels.all codesAB = true ∧ sortedB roots = true ∧ roots.length = 20 ∧ roots.head? = some 0 ∧
    gws.length = 19 ∧ ∀ i < 19, codesAB (gws.getD i []) = true ∧
      wv tb (gws.getD i []) 0 = roots.getD (i + 1) 0 := by
  have h := fix_ok
  simp only [fixChk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, List.all_eq_true.2 h13, h14, h15,
    h16, h17, h18⟩

theorem beta0_ne : beta0 ≠ 0 := by
  have h := idx_ok
  simp only [idxChk, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
    beq_eq_false_iff_ne, ne_eq] at h
  exact h.2

theorem beta0_lt : beta0 < nn := by
  rw [fix_facts.2.2.2.2.2.1]
  exact (perm_facts 0 (by decide)).2.2.1

section Core

variable {J : Type} [Group J] [MulAction J (Fin nn)]

@[expose] def Acts (g : ℕ → J) : Prop := ∀ c < 8, ∀ i : Fin nn, (g c • i).val = tb c i.val

@[expose] noncomputable def pt0 : Fin nn := ⟨0, by decide⟩

@[expose] noncomputable def ptB : Fin nn := ⟨beta0, beta0_lt⟩

variable {g : ℕ → J}

theorem ev_smul (hg : Acts g) : ∀ {w : List ℕ}, (∀ c ∈ w, c < 8) → ∀ i : Fin nn,
    (ev g w • i).val = wv tb w i.val
  | [], _, i => by rw [ev_nil, one_smul]; rfl
  | c :: w, hw, i => by
    rw [ev_cons, mul_smul, wv_cons, hg c (hw c List.mem_cons_self),
      ev_smul hg (fun d hd => hw d (List.mem_cons_of_mem c hd)) i]

theorem wv_lt (hg : Acts g) {w : List ℕ} (hw : ∀ c ∈ w, c < 8) {y : ℕ} (hy : y < nn) :
    wv tb w y < nn := by
  have := ev_smul hg hw ⟨y, hy⟩
  rw [← this]
  exact Fin.isLt _

theorem ev_single (c : ℕ) : ev g [c] = g c := by simp [ev]

theorem fix_letter (hg : Acts g) {c : ℕ} (hc : c < 8) (h : tb c 0 = 0) : g c • pt0 = pt0 :=
  Fin.ext ((hg c hc pt0).trans h)

theorem fgw0 (j : ℕ) : fgw 0 j = if j = 0 then [0] else [2] := by
  simp [fgw]

theorem trans (hg : Acts g) : ∀ p : Fin nn, ∃ x : J, x • pt0 = p := by
  intro p
  have hf := forest_facts (f := 0) (by decide)
  obtain ⟨r, hr, hRr, k, -, hk⟩ := forest_reach (MulAction.toPermHom J (Fin nn)) hf ⊤
    (fun j => ev g (fgw 0 j)) (fun _ _ => Subgroup.mem_top _) (fun j _ i => by
      rw [MulAction.toPermHom_apply, MulAction.toPerm_apply]
      refine ev_smul hg (fun c hc => ?_) i
      rw [fgw0] at hc
      split_ifs at hc <;> simp_all) p.val p.isLt
  have hr0 : r = 0 := by rw [← hRr]; simp [rf]
  subst hr0
  refine ⟨k, ?_⟩
  rw [MulAction.toPermHom_apply, MulAction.toPerm_apply] at hk
  exact hk

theorem faithful [IsSimpleGroup J] (hg : Acts g) : FaithfulSMul J (Fin nn) := by
  have hker : (MulAction.toPermHom J (Fin nn)).ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MulAction.toPermHom J (Fin nn)).ker with
      h | h
    · exact h
    · exfalso
      have hm : g 2 ∈ (MulAction.toPermHom J (Fin nn)).ker := h ▸ Subgroup.mem_top _
      rw [MonoidHom.mem_ker] at hm
      have h1 := congrArg (fun π : Equiv.Perm (Fin nn) => (π pt0).val) hm
      simp only [MulAction.toPermHom_apply, MulAction.toPerm_apply, Equiv.Perm.coe_one,
        id_eq] at h1
      rw [hg 2 (by decide) pt0] at h1
      exact beta0_ne (fix_facts.2.2.2.2.2.1.trans h1)
  refine ⟨fun {x y} hxy => ?_⟩
  have hinj := (MonoidHom.ker_eq_bot_iff _).1 hker
  apply hinj
  ext i
  simp only [MulAction.toPermHom_apply, MulAction.toPerm_apply]
  rw [hxy i]

variable [Finite J]

theorem card_stab (hJ : Nat.card J = 50232960) (hg : Acts g) :
    Nat.card (stabilizer J pt0) = 1944 := by
  have horb : orbit J pt0 = Set.univ := Set.eq_univ_of_forall fun p => trans hg p
  have hidx : (stabilizer J pt0).index = nn := by
    rw [index_stabilizer, horb, Set.ncard_univ, Nat.card_fin]
  have := Subgroup.card_mul_index (stabilizer J pt0)
  rw [hidx, hJ] at this
  have h2 : Nat.card (stabilizer J pt0) * 25840 = 50232960 := this
  omega

theorem o_facts : (Oc.flatten.map Prod.fst).Nodup ∧ Oc.flatten.length = 1944 ∧
    ∀ r ∈ Oc.flatten, codesIn 4 5 r.2.1 = true ∧ wv tb r.2.1 beta0 = r.1 := by
  have h := o_ok
  simp only [oChk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨(sortedB_pairwise h1).imp (fun hab => Nat.ne_of_lt hab), h2, h3⟩

theorem k_stab (hg : Acts g) {w : List ℕ} (hw : codesIn 4 5 w = true) :
    ev g w ∈ stabilizer J pt0 := by
  apply ev_mem
  intro c hc
  rw [mem_stabilizer_iff]
  rcases codesIn_mem hw c hc with rfl | rfl
  · exact fix_letter hg (by decide) fix_facts.1
  · exact fix_letter hg (by decide) fix_facts.2.1

theorem free (hJ : Nat.card J = 50232960) (hg : Acts g) {k : J} (hk : k ∈ stabilizer J pt0)
    (hkb : k • ptB = ptB) : k = 1 := by
  obtain ⟨hnd, hlen, hrec⟩ := o_facts
  have hlt : ∀ x ∈ Oc.flatten.map Prod.fst, x < nn := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
    rw [← (hrec r hr).2]
    exact wv_lt hg (codesIn_lt (hrec r hr).1 (by decide) (by decide)) beta0_lt
  refine eq_one_of_orbit (K := stabilizer J pt0) (b := ptB)
    (S := {q : Fin nn | q.val ∈ Oc.flatten.map Prod.fst}) ?_ ?_ hk hkb
  · intro q hq
    obtain ⟨r, hr, hrq⟩ := List.mem_map.1 hq
    obtain ⟨hc, hv⟩ := hrec r hr
    refine ⟨⟨ev g r.2.1, k_stab hg hc⟩, Fin.ext ?_⟩
    change (ev g r.2.1 • ptB).val = q.val
    rw [ev_smul hg (codesIn_lt hc (by decide) (by decide))]
    exact hv.trans hrq
  · rw [card_stab hJ hg, ncard_val_mem hnd hlt, List.length_map, hlen]

theorem base_eq (hJ : Nat.card J = 50232960) (hg : Acts g) {x y : J} (h0 : x • pt0 = y • pt0)
    (h1 : x • ptB = y • ptB) : x = y := by
  have hk : y⁻¹ * x ∈ stabilizer J pt0 := by
    rw [mem_stabilizer_iff, mul_smul, h0, inv_smul_smul]
  have hkb : (y⁻¹ * x) • ptB = ptB := by rw [mul_smul, h1, inv_smul_smul]
  have := free hJ hg hk hkb
  rw [inv_mul_eq_one] at this
  exact this.symm

theorem word_eq (hJ : Nat.card J = 50232960) (hg : Acts g) (w v : List ℕ)
    (hw : ∀ c ∈ w, c < 8) (hv : ∀ c ∈ v, c < 8) (h : baseEq tb beta0 w v = true) :
    ev g w = ev g v := by
  obtain ⟨h0, h1⟩ := baseEq_spec h
  apply base_eq hJ hg
  · apply Fin.ext
    rw [ev_smul hg hw, ev_smul hg hv]
    exact h0
  · apply Fin.ext
    rw [ev_smul hg hw, ev_smul hg hv]
    exact h1

theorem word_ne (hg : Acts g) (w v : List ℕ) (hw : ∀ c ∈ w, c < 8) (hv : ∀ c ∈ v, c < 8)
    {y : ℕ} (hy : y < nn) (h : wv tb w y ≠ wv tb v y) : ev g w ≠ ev g v := by
  intro e
  apply h
  rw [← ev_smul hg hw ⟨y, hy⟩, ← ev_smul hg hv ⟨y, hy⟩, e]

end Core

end CertificateChecks.KernelJ3C

end
