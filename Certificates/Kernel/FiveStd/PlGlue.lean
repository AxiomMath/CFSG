module

public import Certificates.Kernel.FiveStd.Pl
public import Certificates.Kernel.FiveStd.CsOrder
public import Certificates.Kernel.FiveStd.DiagGlue

public section

namespace CertificateChecks.FiveStd

open CFSG.KC.FiveStdK CFSG.GH74.GLS.LU.Local.FiveStd CFSG.GH74.GLS.LU.Local.Five

theorem plF_eq (k : Nat) : plF k = clsOK G GI 2 (PU.getD k 0) (PR.getD k 0) (PM.getD k 0)
    (PB.getD k 0) (PC.getD k 0) oneK := rfl

theorem pl_ok : ∀ k < 3, plF k = true := by
  intro k hk
  interval_cases k
  · exact ch5147p.p0
  · exact ch5147p.p1
  · exact ch5147p.p2

theorem pl_card : ∀ k < 3, PM.getD k 0 * PC.getD k 0 = 28800 := by decide +kernel

theorem pl_glue (k : Nat) (hk : k < 3) :
    validE (decE (PU.getD k 0)) = true ∧
    (∀ b, validE b = true → (mulE b (decE (PU.getD k 0)) = mulE (decE (PU.getD k 0)) b ↔
      b ∈ decL (f20 (PB.getD k 0)) (PC.getD k 0))) ∧
    (decL (f20 (PB.getD k 0)) (PC.getD k 0)).Nodup ∧
    ∀ j < PC.getD k 0, validK (f20 (PB.getD k 0) j) = true := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcls := pl_ok k hk
  rw [plF_eq] at hcls
  have hgen := (clsOK_spec hcls).1
  have hg : ∀ l < 2, validE (decE (f20 G l)) = true ∧ codeE (decE (f20 G l)) = f20 G l :=
    fun l hl => ⟨valid_decE (hgen l hl).1, codeE_decE (validK_lt (hgen l hl).1)⟩
  obtain ⟨h1, -, -, h4, h5, -, -⟩ := cls_sound (Mat.model_ιF (F := ZMod 5)) (fun l => decE (f20 G l))
    hg ((allN_iff _ _).1 gi_valid) tree_all hcls (pl_card k hk)
  exact ⟨h1, h4, h5, fun j hj => (cPt_spec ((clsOK_spec hcls).2.2.2.2.1 j hj)).1⟩

theorem filter_Cs_codes {p : E → Bool} {B n : Nat} {PL : List Nat}
    (hmem : ∀ x, validE x = true → (p x = true ↔ x ∈ decL (f20 B) n))
    (hLnd : (decL (f20 B) n).Nodup) (hB : ∀ j < n, validK (f20 B j) = true)
    (hlen : PL.length = n) (hin : ∀ j < n, PL.contains (f20 B j) = true)
    (hsP : (PL.map keyC).Pairwise (· < ·)) :
    (Cs.filter p).map codeE = PL := by
  set LB := (decL (f20 B) n).map codeE with hLB
  have hLBe : LB = (List.range n).map (f20 B) := by
    rw [hLB, decL, List.map_map]
    exact List.map_congr_left fun j hj => codeE_decE (validK_lt (hB j (List.mem_range.1 hj)))
  have hLBnd : LB.Nodup := hLnd.map codeE_injective
  have hsub : LB ⊆ PL := by
    intro c hc
    rw [hLBe] at hc
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hc
    exact List.contains_iff_mem.1 (hin j (List.mem_range.1 hj))
  have hperm : LB.Perm PL := (List.subperm_of_subset hLBnd hsub).perm_of_length_le (by
    rw [hlen, hLBe, List.length_map, List.length_range])
  have hmemPL : ∀ c, c ∈ PL ↔ ∃ x, validE x = true ∧ x ∈ decL (f20 B) n ∧ codeE x = c := by
    intro c
    rw [← hperm.mem_iff, hLB, List.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨j, hj, rfl⟩ := mem_decL.1 hx
      exact ⟨_, valid_decE (hB j hj), hx, rfl⟩
    · rintro ⟨x, -, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
  have hmemF : ∀ c, c ∈ (Cs.filter p).map codeE ↔ c ∈ PL := by
    intro c
    rw [hmemPL, List.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨hxC, hpx⟩ := List.mem_filter.1 hx
      have hxv := (mem_Cs_iff x).1 hxC
      exact ⟨x, hxv, (hmem x hxv).1 hpx, rfl⟩
    · rintro ⟨x, hxv, hx, rfl⟩
      exact ⟨x, List.mem_filter.2 ⟨(mem_Cs_iff x).2 hxv, (hmem x hxv).2 hx⟩, rfl⟩
  have hsF : (((Cs.filter p).map codeE).map keyC).Pairwise (· < ·) := by
    have hc := List.isChain_iff_pairwise.1 cs_chain
    have e : ((Cs.filter p).map codeE).map keyC = (Cs.filter p).map fun x => keyC (codeE x) := by
      rw [List.map_map]
      rfl
    rw [e]
    exact hc.sublist (List.filter_sublist.map _)
  have hkey : ((Cs.filter p).map codeE).map keyC = PL.map keyC := by
    apply List.Pairwise.eq_of_mem_iff hsF hsP
    intro k
    constructor
    · intro h
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 h
      exact List.mem_map.2 ⟨c, (hmemF c).1 hc, rfl⟩
    · intro h
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 h
      exact List.mem_map.2 ⟨c, (hmemF c).2 hc, rfl⟩
  have hlt : ∀ c ∈ PL, c < 781250 := by
    intro c hc
    obtain ⟨x, -, -, rfl⟩ := (hmemPL c).1 hc
    exact codeE_lt x
  have inv : ∀ L : List Nat, (∀ c ∈ L, c < 781250) → (L.map keyC).map unkeyC = L := by
    intro L hL
    rw [List.map_map]
    conv_rhs => rw [← List.map_id L]
    exact List.map_congr_left fun c hc => unkeyC_keyC (hL c hc)
  rw [← inv _ (fun c hc => hlt c ((hmemF c).1 hc)), hkey, inv _ hlt]

theorem PlOf_codes (k : Nat) (hk : k < 3) : (PlOf (decE (PU.getD k 0))).map codeE = PLc k := by
  obtain ⟨-, hcen, hnd, hB⟩ := pl_glue k hk
  obtain ⟨hlen, -, hin⟩ := pl_set k hk
  unfold PlOf
  refine filter_Cs_codes (fun x hx => ?_) hnd hB hlen hin (pl_key k hk)
  rw [Bool.and_eq_true, commE, commE, beq_iff_eq, beq_iff_eq, ← hcen x hx]
  exact ⟨fun h => h.2, fun h => ⟨z_central hx, h⟩⟩

theorem conjI_inv (g x : E) : conjI g (invE g) x = conjE g x := rfl

theorem beq_code (x y : E) : (x == y) = Nat.beq (codeE x) (codeE y) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq']
  exact codeE_injective.eq_iff.symm

theorem normK_code (g : E) : normK g = normKc K1c K2c (codeE g) := by
  unfold normK normKc normKK
  simp only [letB_eq, allL_eq, memL_eq, conjI_inv]
  rw [← K1l_codes, ← K2l_codes, List.all_map, List.all_map]
  congr 1
  · congr 1
    funext y
    rw [Function.comp_apply, inL_codeE, conj_code]
  · congr 1
    funext y
    rw [Function.comp_apply, inL_codeE, conj_code]

theorem els4Of_codes (k : Nat) (hk : k < 3) : (els4Of (decE (PU.getD k 0))).map codeE = E4c k := by
  unfold els4Of
  rw [map_filter_codeE _ _ _ normK_code,
    map_filter_codeE _ _ (fun c => ordK c == 4) (fun x => by simp only [ordK_codeE]), PlOf_codes k hk]
  exact pl_e4 k hk

theorem nodupL_pp (a b : E) : nodupL (ppE a b 4 4) = decide (ppK (codeE a) (codeE b) 4 4).Nodup := by
  rw [Bool.eq_iff_iff, nodupL_codeE, map_ppE, decide_eq_true_iff]

theorem tp_map (L : List E) (hL : ∀ a ∈ L, normK a = true) :
    (L.flatMap fun a => L.filterMap fun b => if isTorusPair a b then some (a, b) else none).map
        (fun p => (codeE p.1, codeE p.2)) = tpL (L.map codeE) := by
  unfold tpL
  rw [List.map_flatMap, List.flatMap_map]
  refine List.flatMap_congr fun a ha => ?_
  rw [List.map_filterMap, List.filterMap_map]
  refine List.filterMap_congr fun b hb => ?_
  have e : isTorusPair a b = tpCond (codeE a) (codeE b) := by
    unfold isTorusPair tpCond
    rw [hL a ha, hL b hb, nodupL_pp, commE_codeE, ← ordK_codeE, ← ordK_codeE, Bool.and_true,
      Bool.and_true]
  simp only [Function.comp_apply, e]
  cases tpCond (codeE a) (codeE b) <;> rfl

theorem tpOf_codes (k : Nat) (hk : k < 3) :
    (tpOf (decE (PU.getD k 0))).map (fun p => (codeE p.1, codeE p.2)) = tpL (E4c k) := by
  unfold tpOf
  dsimp only
  rw [tp_map (els4Of (decE (PU.getD k 0))) (fun a ha => (List.mem_filter.1 ha).2), els4Of_codes k hk]

theorem checkP_code (t u a b : E) : checkP t u a b = checkPK K1c (codeE t) (codeE u) (codeE a)
    (codeE b) ((PlOf u).map codeE) ((tpOf u).map fun p => (codeE p.1, codeE p.2)) := by
  unfold checkP checkPK WlOf normG
  simp only [List.length_map, List.all_map, List.any_map, Function.comp_def, inL_codeE, map_ppE,
    codeE_zE, codeE_mulE, conj_code, conjI_inv, beq_code, List.all_cons, List.all_nil, ← K1l_codes,
    List.filter_map, List.isEmpty_map]

theorem rk_pu : (RK.getD 0 (0, 0)).2 = PU.getD 0 0 ∧ (RK.getD 1 (0, 0)).2 = PU.getD 1 0 ∧
    (RK.getD 2 (0, 0)).2 = PU.getD 0 0 ∧ (RK.getD 3 (0, 0)).2 = PU.getD 2 0 := by
  decide +kernel

end CertificateChecks.FiveStd

end
