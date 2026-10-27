module

public import Certificates.Kernel.FiveStd.SylGlue
public import Certificates.Kernel.FiveStd.Cover
public import Certificates.Kernel.FiveStd.BaseGlue

public section

namespace CertificateChecks.FiveStd

open CFSG.KC.FiveStdK CFSG.GH74.GLS.LU.Local.FiveStd

theorem K1l_codes : K1l.map codeE = K1c := by decide +kernel

theorem K2l_codes : K2l.map codeE = K2c := by decide +kernel

theorem reps_codes : ∀ k < 4, ∃ r ∈ reps, RK.getD k (0, 0) = (codeE r.1, codeE r.2) := by
  decide +kernel

theorem reps_index : ∀ r ∈ reps, ∃ k < 4, RK.getD k (0, 0) = (codeE r.1, codeE r.2) := by
  decide +kernel

theorem conj_code (x y : E) : codeE (conjE x y) = cjK (codeE x) (invK (codeE x)) (codeE y) := by
  rw [← codeE_invE, cjK_codeE]

theorem allL_eq (L : List Nat) (f : Nat → Bool) : allL L f = L.all f := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    change andB (f x) (allL L f) = _
    rw [andB_eq, ih, List.all_cons]

theorem memL_eq (L : List Nat) (c : Nat) : memL L c = L.contains c := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    change orB (Nat.beq x c) (memL L c) = _
    rw [orB_eq, ih, List.contains_cons]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq', beq_iff_eq]
    exact eq_comm

theorem swapsK_code (x : E) : swapsK x = swapsKK K1c K2c (codeE x) := by
  unfold swapsK swapsKK
  simp only [letB_eq, allL_eq, memL_eq]
  rw [← K1l_codes, List.all_map]
  congr 1
  funext y
  rw [Function.comp_apply, inL_codeE, K2l_codes, conj_code]

theorem normK1_code (x : E) : normK1 x = normKK K1c (codeE x) := by
  unfold normK1 normKK
  simp only [letB_eq, allL_eq, memL_eq]
  rw [← K1l_codes, List.all_map]
  congr 1
  funext y
  rw [Function.comp_apply, inL_codeE, conj_code]

theorem S0s_codes : S0s.map codeE = S0sL := by
  rw [S0s, map_filter_codeE _ _ _ swapsK_code, S0_codes, cv_s0s]

theorem S0n_codes : S0n.map codeE = S0nL := by
  rw [S0n, map_filter_codeE _ _ _ normK1_code, S0_codes, cv_s0n]

theorem bne_zE (u : E) : (u != zE) = !(Nat.beq (codeE u) zK) := by
  rw [bne, ← codeE_zE]
  congr 1
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq']
  exact codeE_injective.eq_iff.symm

theorem pairCond_code (t u : E) : pairCond t u = pairCondK S0sL S0nL (codeE t) (codeE u) := by
  unfold pairCond pairCondK
  rw [inL_codeE, inL_codeE, S0s_codes, S0n_codes, ← ordK_codeE, ← ordK_codeE, commE_codeE, bne_zE]

theorem pairs_map (M L : List E) (pc : E → E → Bool) (pk : Nat → Nat → Bool)
    (h : ∀ x y, pc x y = pk (codeE x) (codeE y)) :
    (M.flatMap fun t => (L.filter fun u => pc t u).map fun u => (t, u)).map
        (fun p => (codeE p.1, codeE p.2)) =
      (M.map codeE).flatMap fun t => ((L.map codeE).filter (pk t)).map fun u => (t, u) := by
  induction M with
  | nil => rfl
  | cons t M ih =>
    rw [List.flatMap_cons, List.map_append, ih, List.map_cons, List.flatMap_cons, List.map_map,
      List.filter_map, List.map_map]
    congr 1
    rw [List.filter_congr fun u _ => h t u]
    rfl

theorem Pairs_codes : Pairs.map (fun p => (codeE p.1, codeE p.2)) = PW.map fun e => (e.1, e.2.1) := by
  rw [← cv_pairs, Pairs, pairs_map _ _ _ _ pairCond_code, S0_codes]

theorem gam_of {g : E} (hv : validE g = true) (hs : g.s = false) : g ∈ Gam := by
  rw [Gam, List.mem_filter, hs]
  exact ⟨(mem_Cs_iff g).2 hv, rfl⟩

theorem cover_check : coverCheck = true := by
  unfold coverCheck
  dsimp only
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [beq_iff_eq, ← List.length_map (f := fun p => (codeE p.1, codeE p.2)), Pairs_codes,
      List.length_map]
    rfl
  · rw [List.all_eq_true]
    intro r hr
    rw [pairCond_code]
    obtain ⟨k, hk4, hke⟩ := reps_index r hr
    have hmem : RK.getD k (0, 0) ∈ RK := by
      rw [List.getD_eq_getElem _ _ (by rw [RK]; exact hk4)]
      exact List.getElem_mem _
    have := List.all_eq_true.1 cv_reps _ hmem
    rwa [hke] at this
  · rw [List.all_eq_true]
    intro p hp
    have hq := List.mem_map_of_mem (f := fun p : E × E => (codeE p.1, codeE p.2)) hp
    rw [Pairs_codes] at hq
    obtain ⟨e, he, hee⟩ := List.mem_map.1 hq
    have hw := List.all_eq_true.1 cv_wit e he
    unfold cwOK at hw
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hw
    obtain ⟨⟨⟨⟨hk, hv⟩, hs⟩, h1⟩, h2⟩ := hw
    obtain ⟨r, hr, hre⟩ := reps_codes _ ((blt_iff _ _).1 hk)
    rw [hre] at h1 h2
    set g := decE e.2.2.2 with hgd
    have hgc : codeE g = e.2.2.2 := codeE_decE (validK_lt hv)
    have hgv : validE g = true := valid_decE hv
    have hgs : g.s = false := by
      have h0 := Nat.eq_of_beq_eq_true hs
      rw [← hgc, fS_codeE] at h0
      cases hb : g.s
      · rfl
      · rw [hb] at h0
        exact absurd h0 (by decide)
    have hc1 : conjE g r.1 = p.1 := by
      apply codeE_injective
      rw [conj_code, hgc, Nat.eq_of_beq_eq_true h1]
      exact (Prod.ext_iff.1 hee).1
    have hc2 : conjE g r.2 = p.2 := by
      apply codeE_injective
      rw [conj_code, hgc, Nat.eq_of_beq_eq_true h2]
      exact (Prod.ext_iff.1 hee).2
    rw [List.any_eq_true]
    refine ⟨Gam.map fun g => conjPair g r, List.mem_map_of_mem hr, ?_⟩
    rw [List.contains_iff_mem, List.mem_map]
    refine ⟨g, gam_of hgv hgs, ?_⟩
    unfold conjPair
    rw [hc1, hc2]

end CertificateChecks.FiveStd

end
