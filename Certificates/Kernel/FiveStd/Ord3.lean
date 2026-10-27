module

public import CFSG.Certificates.Kernel.FiveStdKSylConjSound
public import Certificates.Kernel.FiveStd.DiagGlue
public import Certificates.Kernel.FiveStd.Syl

public section

namespace CertificateChecks.FiveStd

open CFSG.KC.FiveStdK CFSG.GH74.GLS.LU.Local.FiveStd CFSG.GH74.GLS.LU.Local.Five

theorem rp_ord5 : ordK (RP.getD 0 0) = 5 ∧ ordK (RP.getD 1 0) = 5 ∧ ordK (RP.getD 2 0) = 5 := by
  decide +kernel

theorem r3_nodup : (ppK 30751 78799 3 3).Nodup := by decide +kernel

theorem r3_codes : (ppE (decE 30751) (decE 78799) 3 3).map codeE = ppK 30751 78799 3 3 := by
  rw [map_ppE, codeE_decE (by norm_num), codeE_decE (by norm_num)]

theorem conj_rep3 {g : E} (hg : validE g = true) (h3 : powE g 3 = oneE) (h1 : g ≠ oneE) :
    ∃ k, 3 ≤ k ∧ k < 5 ∧ ∃ c, validE c = true ∧ g = conjE c (decE (RP.getD k 0)) := by
  have hfact : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h5 : Fact (Nat.Prime 5) := fact5
  have hM := Mat.model_ιF (F := ZMod 5)
  have hgen := (clsOK_spec (clsF_eq 0 ▸ cls_ok 0 (by norm_num))).1
  have hK := card_vSub hM (fun l => decE (f20 G l))
    (fun l hl => ⟨valid_decE (hgen l hl).1, codeE_decE (validK_lt (hgen l hl).1)⟩) tree_all
  obtain ⟨hx, hy, hxy, hxp, hyp, -, -, hall⟩ := syl_sound syl3
  have hnd : (ppE (decE 30751) (decE 78799) 3 3).Nodup := List.Nodup.of_map codeE (r3_codes ▸ r3_nodup)
  obtain ⟨c, hc, i, hi, j, hj, hgc⟩ :=
    conj_into_pp hM hK (p := 3) (by norm_num) (by norm_num) hx hy hxy hxp hyp hnd hg h3
  have hij : i ≠ 0 ∨ j ≠ 0 := by
    by_contra hne
    obtain ⟨rfl, rfl⟩ : i = 0 ∧ j = 0 := by omega
    apply h1
    rw [hgc]
    change conjE c (mulE oneE oneE) = oneE
    rw [oneE_mulE hM.valid_one, cj_one hM hc]
  obtain ⟨k, hk, j', hj', he⟩ := hall i hi j hj hij
  have hhv := hM.valid_mul _ _ (hM.valid_powE hx i) (hM.valid_powE hy j)
  have hmem : mulE (powE (decE 30751) i) (powE (decE 78799) j) ∈
      decL (fun j => oCode (f96 (OR.getD k 0) j)) (OM.getD k 0) :=
    mem_decL.2 ⟨j', hj', by rw [he, decE_codeE]⟩
  obtain ⟨hrk, horb, -⟩ := cls_glue k hk
  obtain ⟨c', hc', hce⟩ := (horb _ hhv).2 hmem
  have hg' : g = conjE (mulE c c') (decE (RP.getD k 0)) := by
    rw [hgc, ← hce, cj_cj hM hc hc' hrk]
  have hk3 : 3 ≤ k := by
    by_contra hk3
    have h5' : ordE (decE (RP.getD k 0)) = 5 := by
      rw [← ordK_codeE, codeE_decE (validK_lt ((clsOK_spec (clsF_eq k ▸ cls_ok k hk)).2.1))]
      interval_cases k
      · exact rp_ord5.1
      · exact rp_ord5.2.1
      · exact rp_ord5.2.2
    have := ord_conj hM (hM.valid_mul _ _ hc hc') hrk h5' (by norm_num)
    rw [← hg'] at this
    have hp := (pow5_iff hM hg).1 (Or.inr this)
    have hgo := hM.orderOf_of_ordE hg this (by norm_num)
    have h3' : Mat.ιF (ZMod 5) g ^ 3 = 1 := by rw [← hM.map_powE hg, h3, hM.map_one]
    have := orderOf_dvd_of_pow_eq_one h3'
    rw [hgo] at this
    exact absurd this (by norm_num)
  exact ⟨k, hk3, hk, _, hM.valid_mul _ _ hc hc', hg'⟩

end CertificateChecks.FiveStd

end
