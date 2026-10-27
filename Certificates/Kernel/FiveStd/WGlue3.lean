module

public import Certificates.Kernel.FiveStd.WGlue2
public import Certificates.Kernel.FiveStd.WChk3

public section

namespace CertificateChecks.FiveStd

open CFSG.KC.FiveStdK CFSG.GH74.GLS.LU.Local.FiveStd CFSG.GH74.GLS.LU.Local.Five

local instance instFact5'''' : Fact (Nat.Prime 5) := fact5

local notation "ιF" => Mat.ιF (ZMod 5)

theorem orb_code (k : Nat) (hk : k < 5) (j : Nat) (hj : j < OM.getD k 0) :
    codeE (decE (oCode (f96 (OR.getD k 0) j))) = oCode (f96 (OR.getD k 0) j) := by
  have hcls := cls_ok k hk
  rw [clsF_eq] at hcls
  have hspec := clsOK_spec hcls
  have hg : ∀ l < 2, validE (decE (f20 G l)) = true ∧ codeE (decE (f20 G l)) = f20 G l :=
    fun l hl => ⟨valid_decE (hspec.1 l hl).1, codeE_decE (validK_lt (hspec.1 l hl).1)⟩
  have hrc : codeE (decE (RP.getD k 0)) = RP.getD k 0 := codeE_decE (validK_lt hspec.2.1)
  obtain ⟨hrk, -⟩ := cls_glue k hk
  have hgi := gi_eq hM5 (fun l => decE (f20 G l)) hg ((allN_iff _ _).1 gi_valid)
    fun l hl => (hspec.1 l hl).2
  obtain ⟨x, -, hxc, -⟩ := orb_sound hM5 (fun l => decE (f20 G l)) hg hgi hrk
    (fun j hj => hrc ▸ hspec.2.2.2.1 j hj) j hj
  rw [← hxc, decE_codeE]

theorem nx_filter_of {t g a b : E} (ht : validE t = true) (hg : validE g = true)
    (ha : validE a = true) (hb : validE b = true) {XXl NXl : List Nat} {W : List (Nat × Nat)} {dc : Nat}
    (hXX : (ppE g (conjE t g) 5 5).map codeE = XXl)
    (hNX : (prod3 (ppE g (conjE t g) 5 5) (ppE a b 4 4) [oneE, t]).map codeE = NXl)
    (hdc : validK dc = true) (hdg : Nat.beq (cjK dc (invK dc) (RP.getD 2 0)) (codeE g) = true)
    (hnx : nxK (codeE g) (codeE (conjE t g)) dc (invK dc) (CB.getD 2 0) (CM.getD 2 0) (OR.getD 2 0)
      (OM.getD 2 0) XXl NXl W = true)
    (hsup : nxSup XXl NXl (codeE g) (codeE (conjE t g)) = true) :
    eqL (Cs.filter fun c => normG c [g, conjE t g] (ppE g (conjE t g) 5 5))
      (prod3 (ppE g (conjE t g) 5 5) (ppE a b 4 4) [oneE, t]) = true := by
  set g2 := conjE t g with hg2d
  have hg2 : validE g2 = true := hM5.valid_conjE ht hg
  obtain ⟨hrk, horb, -⟩ := cls_glue 2 (by norm_num)
  have hrc : codeE (decE (RP.getD 2 0)) = RP.getD 2 0 :=
    codeE_decE (validK_lt (clsOK_spec (clsF_eq 2 ▸ cls_ok 2 (by norm_num))).2.1)
  set d := decE dc
  have hd : validE d = true := valid_decE hdc
  have hdcode : codeE d = dc := codeE_decE (validK_lt hdc)
  have hgd : g = conjE d (decE (RP.getD 2 0)) := by
    apply codeE_injective
    rw [conj_code, hdcode, hrc]
    exact ((beq_iff_eq' _ _).1 hdg).symm
  unfold nxK at hnx
  rw [andB_eq, Bool.and_eq_true] at hnx
  obtain ⟨hW, hO⟩ := hnx
  unfold eqL subL
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  constructor
  · intro c hc
    obtain ⟨hcC, hn⟩ := List.mem_filter.1 hc
    have hcv := (mem_Cs_iff c).1 hcC
    unfold normG at hn
    rw [List.all_cons, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, conjI_inv,
      conjI_inv] at hn
    obtain ⟨h1, h2⟩ := hn
    set y := conjE c g with hyd
    have hyv : validE y = true := hM5.valid_conjE hcv hg
    have hyR : conjE (mulE c d) (decE (RP.getD 2 0)) = y := by
      rw [hyd, hgd, cj_cj hM5 hcv hd hrk]
    obtain ⟨j, hj, hje⟩ := mem_decL.1 ((horb y hyv).1 ⟨_, hM5.valid_mul _ _ hcv hd, hyR⟩)
    have hyc : codeE y = oCode (f96 (OR.getD 2 0) j) := by rw [← hje, orb_code 2 (by norm_num) j hj]
    have hO' := (allN_iff _ _).1 hO j hj
    rw [letB_eq, orB_eq, Bool.or_eq_true, ← hyc] at hO'
    have hm1 : memL XXl (codeE y) = true := by
      rw [memL_iff, ← hXX]
      exact List.mem_map_of_mem (by rw [inL, List.contains_iff_mem] at h1; exact h1)
    rcases hO' with h | h
    · rw [hm1] at h
      exact absurd h (by decide)
    obtain ⟨e, he, hey⟩ := List.any_eq_true.1 h
    rw [beq_iff_eq'] at hey
    have hwe := List.all_eq_true.1 hW e he
    unfold nxW at hwe
    rw [andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq'] at hwe
    obtain ⟨hwv, hwg, hall⟩ := hwe
    set w := decE e.2
    have hw : validE w = true := valid_decE hwv
    have hwcode : codeE w = e.2 := codeE_decE (validK_lt hwv)
    have hwy : conjE w g = y := by
      apply codeE_injective
      rw [conj_code, hwcode, hwg, hey]
    obtain ⟨j', hj', hcj⟩ := conj_cands (by norm_num) hd hgd hw hwy hcv rfl
    have hb := cb_valid 2 (by norm_num) j' hj'
    have hcc : codeE c = mulK e.2 (cjK dc (invK dc) (f20 (CB.getD 2 0) j')) := by
      rw [hcj, codeE_mulE, conj_code, hwcode, hdcode, codeE_decE (validK_lt hb)]
    have hk := (allN_iff _ _).1 hall j' hj'
    rw [letB_eq, orB_eq, Bool.or_eq_true, ← hcc] at hk
    have hm2 : memL XXl (cjK (codeE c) (invK (codeE c)) (codeE g2)) = true := by
      rw [memL_iff, ← conj_code, ← hXX]
      exact List.mem_map_of_mem (by rw [inL, List.contains_iff_mem] at h2; exact h2)
    rcases hk with h | h
    · rw [hm2] at h
      exact absurd h (by decide)
    rw [memL_iff, ← hNX] at h
    rw [inL, List.contains_iff_mem]
    exact mem_code_iff.1 h
  · intro y hy
    have hyc : codeE y ∈ NXl := by
      rw [← hNX]
      exact List.mem_map_of_mem hy
    have hf := allL_mem hsup hyc
    rw [andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true, validK_codeE] at hf
    obtain ⟨hyv, hg1, hg2'⟩ := hf
    rw [inL, List.contains_iff_mem, List.mem_filter]
    refine ⟨(mem_Cs_iff y).2 hyv, ?_⟩
    unfold normG
    rw [List.all_cons, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, conjI_inv,
      conjI_inv, inL, inL, List.contains_iff_mem, List.contains_iff_mem]
    exact ⟨conj_mem hXX hg1, conj_mem hXX hg2'⟩

end CertificateChecks.FiveStd

end
