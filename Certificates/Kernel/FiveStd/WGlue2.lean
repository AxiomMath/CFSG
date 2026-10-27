module

public import Certificates.Kernel.FiveStd.WGlue
public import Certificates.Kernel.FiveStd.WChk2

public section

namespace CertificateChecks.FiveStd

open CFSG.KC.FiveStdK CFSG.GH74.GLS.LU.Local.FiveStd CFSG.GH74.GLS.LU.Local.Five

local instance instFact5''' : Fact (Nat.Prime 5) := fact5

local notation "ιF" => Mat.ιF (ZMod 5)

theorem mem_code_iff {L : List E} {x : E} : codeE x ∈ L.map codeE ↔ x ∈ L := by
  constructor
  · intro h
    obtain ⟨y, hy, he⟩ := List.mem_map.1 h
    rwa [← codeE_injective he]
  · exact List.mem_map_of_mem

theorem mem_powers5 {g x : E} : x ∈ powers g 5 ↔ ∃ i < 5, powE g i = x := by
  simp [powers, List.mem_map, List.mem_range]

theorem memL_iff {L : List Nat} {c : Nat} : memL L c = true ↔ c ∈ L := by
  rw [memL_eq, List.contains_iff_mem]

theorem allL_mem {L : List Nat} {f : Nat → Bool} (h : allL L f = true) {c : Nat} (hc : c ∈ L) : f c = true :=
  List.all_eq_true.1 (by rw [← allL_eq]; exact h) c hc

theorem conj_mem {L : List E} {C : List Nat} (hL : L.map codeE = C) {v x : E}
    (h : memL C (cjK (codeE v) (invK (codeE v)) (codeE x)) = true) : conjE v x ∈ L := by
  rw [memL_iff, ← conj_code, ← hL] at h
  exact mem_code_iff.1 h

theorem norm_filter_of {t g a b : E} (ht : validE t = true) (hg : validE g = true)
    (ha : validE a = true) (hb : validE b = true) {g2c dc : Nat} {Hc VL : List Nat}
    (hcl : (Nat.beq (cjK (codeE t) (invK (codeE t)) (codeE g)) g2c &&
      Nat.beq (cjK dc (invK dc) (RP.getD 2 0)) g2c) = true)
    (hdc : validK dc = true)
    (hsub : cenSubK (p2K K1c g2c) (CB.getD 2 0) (CM.getD 2 0) dc (invK dc) = true)
    (hsup : cenSupK (p2K K1c g2c) g2c = true)
    (hH : (ppE a b 4 4).map codeE = Hc) (hVl : 4 ≤ VL.length) (hnz : nzK g2c Hc VL K1c = true) :
    eqL (Cs.filter fun c => normG c [conjE t g] (powers (conjE t g) 5))
      (prod3 (powers (conjE t g) 5) K1l (ppE a b 4 4)) = true := by
  have hcl' := hcl
  rw [Bool.and_eq_true, beq_iff_eq', beq_iff_eq'] at hcl'
  obtain ⟨h1, h2⟩ := hcl'
  set g2 := conjE t g with hg2d
  have hg2 : validE g2 = true := hM5.valid_conjE ht hg
  have hg2c : codeE g2 = g2c := by rw [hg2d, conj_code, h1]
  obtain ⟨hrk, -⟩ := cls_glue 2 (by norm_num)
  have hrc : codeE (decE (RP.getD 2 0)) = RP.getD 2 0 :=
    codeE_decE (validK_lt (clsOK_spec (clsF_eq 2 ▸ cls_ok 2 (by norm_num))).2.1)
  set d := decE dc
  have hd : validE d = true := valid_decE hdc
  have hdcode : codeE d = dc := codeE_decE (validK_lt hdc)
  have hgd : g2 = conjE d (decE (RP.getD 2 0)) := by
    apply codeE_injective
    rw [hg2c, conj_code, hdcode, hrc, h2]
  have hP := prod2_codes g2
  rw [hg2c] at hP
  have hX := map_powers g2 5
  rw [hg2c] at hX
  unfold nzK at hnz
  simp only [andB_eq, Bool.and_eq_true] at hnz
  obtain ⟨hne, hHn, hVi, hVn⟩ := hnz
  have hX2v : V (powers g2 5) := hM5.V_powers hg2 5
  have hK1v : ∀ k ∈ K1l, validE k = true := fun k hk => List.all_eq_true.1 k1_valid k hk
  have hH0v : V (ppE a b 4 4) := hM5.V_ppE ha hb 4 4
  unfold eqL subL
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  constructor
  · intro c hc
    obtain ⟨hcC, hn⟩ := List.mem_filter.1 hc
    have hcv := (mem_Cs_iff c).1 hcC
    unfold normG at hn
    rw [List.all_cons, List.all_nil, Bool.and_true, conjI_inv, inL, List.contains_iff_mem,
      mem_powers5] at hn
    obtain ⟨i, hi, hci⟩ := hn
    have hi0 : i ≠ 0 := by
      rintro rfl
      have e : g2 = oneE := by
        rw [← cj_back hM5 hcv hg2, ← hci]
        exact cj_one hM5 (hM5.valid_inv _ hcv)
      have : Nat.beq g2c oneK = true := by
        rw [← hg2c, e]
        exact Nat.beq_refl _
      rw [this] at hne
      exact absurd hne (by decide)
    have hv := (allN_iff _ _).1 hVi (i - 1) (by omega)
    rw [letB_eq, Bool.and_eq_true, beq_iff_eq'] at hv
    obtain ⟨hvH, hvc⟩ := hv
    rw [show Nat.succ (i - 1) = i by omega] at hvc
    obtain ⟨h, hhH, hhc⟩ := mem_codes hH (memL_iff.1 hvH)
    have hhv := hH0v h hhH
    have hhy : conjE h g2 = powE g2 i := by
      apply codeE_injective
      rw [conj_code, ← powK_codeE, hhc, hg2c]
      exact hvc
    obtain ⟨j, hj, hcj⟩ := conj_cands (by norm_num) hd hgd hhv hhy hcv hci.symm
    have hb := cb_valid 2 (by norm_num) j hj
    have hm := (allN_iff _ _).1 hsub j hj
    have hyP : conjE d (decE (f20 (CB.getD 2 0) j)) ∈ prod2 (powers g2 5) K1l := by
      apply conj_mem hP
      rw [hdcode, codeE_decE (validK_lt hb)]
      exact hm
    unfold prod2 mulLL at hyP
    simp only [List.mem_flatMap, List.mem_map] at hyP
    obtain ⟨x, hx, k, hk, hxk⟩ := hyP
    have hVh : codeE h ∈ VL := by
      rw [hhc, List.getD_eq_getElem _ _ (by omega)]
      exact List.getElem_mem _
    have hvn := allL_mem hVn hVh
    rw [Bool.and_eq_true] at hvn
    have hx' : conjE h x ∈ powers g2 5 := by
      apply conj_mem hX
      exact allL_mem hvn.1 (by rw [← hX]; exact List.mem_map_of_mem hx)
    have hk' : conjE h k ∈ K1l := by
      apply conj_mem K1l_codes
      exact allL_mem hvn.2 (by rw [← K1l_codes]; exact List.mem_map_of_mem hk)
    have hxv := hX2v x hx
    have hkv := hK1v k hk
    have hx'v := hM5.valid_conjE hhv hxv
    have hk'v := hM5.valid_conjE hhv hkv
    have heq : c = mulE (mulE (conjE h x) (conjE h k)) h := by
      rw [hcj, ← hxk]
      apply hM5.inj _ _ (hM5.valid_mul _ _ hhv (hM5.valid_mul _ _ hxv hkv))
        (hM5.valid_mul _ _ (hM5.valid_mul _ _ hx'v hk'v) hhv)
      rw [hM5.map_mul _ _ hhv (hM5.valid_mul _ _ hxv hkv), hM5.map_mul _ _ hxv hkv,
        hM5.map_mul _ _ (hM5.valid_mul _ _ hx'v hk'v) hhv, hM5.map_mul _ _ hx'v hk'v,
        hM5.map_conjE hhv hxv, hM5.map_conjE hhv hkv]
      group
    rw [inL, List.contains_iff_mem, heq]
    unfold prod3 mulLL
    simp only [List.mem_flatMap, List.mem_map]
    exact ⟨_, ⟨conjE h x, hx', conjE h k, hk', rfl⟩, h, hhH, rfl⟩
  · intro y hy
    unfold prod3 mulLL at hy
    simp only [List.mem_flatMap, List.mem_map] at hy
    obtain ⟨xk, ⟨x, hx, k, hk, rfl⟩, h, hhH, rfl⟩ := hy
    have hxv := hX2v x hx
    have hkv := hK1v k hk
    have hhv := hH0v h hhH
    have hxkv := hM5.valid_mul _ _ hxv hkv
    have hyv := hM5.valid_mul _ _ hxkv hhv
    have hhm := allL_mem hHn (by rw [← hH]; exact List.mem_map_of_mem hhH)
    have hhm' : memL (powersK g2c 5) (cjK (codeE h) (invK (codeE h)) (codeE g2)) = true := by
      rw [hg2c]
      exact hhm
    obtain ⟨i, hi, hhi⟩ := mem_powers5.1 (conj_mem hX hhm')
    have hxkP : mulE x k ∈ prod2 (powers g2 5) K1l := by
      unfold prod2 mulLL
      simp only [List.mem_flatMap, List.mem_map]
      exact ⟨x, hx, k, hk, rfl⟩
    have hcm := allL_mem hsup (by rw [← hP]; exact List.mem_map_of_mem hxkP)
    rw [andB_eq, Bool.and_eq_true, ← hg2c, ← commE_codeE] at hcm
    have hcomm : Commute (ιF (mulE x k)) (ιF g2) := (hM5.commE_iff hxkv hg2).1 hcm.2
    have hc' := hcomm.pow_right i
    have hhi' : ιF h * ιF g2 * (ιF h)⁻¹ = ιF g2 ^ i := by
      rw [← hM5.map_conjE hhv hg2, ← hhi, hM5.map_powE hg2]
    rw [inL, List.contains_iff_mem, List.mem_filter]
    refine ⟨(mem_Cs_iff _).2 hyv, ?_⟩
    unfold normG
    rw [List.all_cons, List.all_nil, Bool.and_true, conjI_inv, inL, List.contains_iff_mem, mem_powers5]
    refine ⟨i, hi, ?_⟩
    apply hM5.inj _ _ (hM5.valid_powE hg2 i) (hM5.valid_conjE hyv hg2)
    rw [hM5.map_powE hg2, hM5.map_conjE hyv hg2, hM5.map_mul _ _ hxkv hhv]
    calc ιF g2 ^ i = ιF (mulE x k) * ιF g2 ^ i * (ιF (mulE x k))⁻¹ := by
          rw [hc'.eq]
          group
      _ = ιF (mulE x k) * (ιF h * ιF g2 * (ιF h)⁻¹) * (ιF (mulE x k))⁻¹ := by rw [hhi']
      _ = _ := by group

end CertificateChecks.FiveStd

end
