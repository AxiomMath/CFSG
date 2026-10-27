module

public import Certificates.Kernel.FiveStd.PlGlue
public import Certificates.Kernel.FiveStd.Ord3
public import Certificates.Kernel.FiveStd.NChk
public import Certificates.Kernel.FiveStd.DiagCheck

public section

namespace CertificateChecks.FiveStd

open CFSG.KC.FiveStdK CFSG.GH74.GLS.LU.Local.FiveStd CFSG.GH74.GLS.LU.Local.Five

@[expose] def tripC (q : E × E × List E) : Nat × Nat × List Nat := (codeE q.1, codeE q.2.1, q.2.2.map codeE)

@[expose] def pairC (p : E × E) : Nat × Nat := (codeE p.1, codeE p.2)

theorem syl36_codes : Syl36.map tripC = SylT := by
  rw [syl_table, ← X1cands_codes, ← Y1cands_codes, Syl36, List.map_flatMap, List.flatMap_map]
  refine List.flatMap_congr fun gx _ => ?_
  rw [List.map_map, List.map_map]
  refine List.map_congr_left fun gy _ => ?_
  simp only [Function.comp_apply, tripC, map_ppE]

theorem normAll_code (hs gens L : List E) :
    normAll hs gens L = normAllK (hs.map codeE) (gens.map codeE) (L.map codeE) := by
  unfold normAll normG normAllK
  simp only [List.all_map, Function.comp_def, conjI_inv, inL_codeE, conj_code]

theorem z4pairs_codes (els : List E) : (z4pairs els).map pairC = z4K (els.map codeE) := by
  unfold z4pairs z4K
  rw [List.map_flatMap, List.flatMap_map]
  refine List.flatMap_congr fun a _ => ?_
  rw [List.map_filterMap, List.filterMap_map]
  refine List.filterMap_congr fun b _ => ?_
  have e : (commE a b && nodupL (ppE a b 4 4)) =
      (Nat.beq (mulK (codeE a) (codeE b)) (mulK (codeE b) (codeE a)) &&
        decide (ppK (codeE a) (codeE b) 4 4).Nodup) := by
    rw [commE_codeE, nodupL_pp]
  simp only [Function.comp_apply, e]
  cases (Nat.beq (mulK (codeE a) (codeE b)) (mulK (codeE b) (codeE a)) &&
    decide (ppK (codeE a) (codeE b) 4 4).Nodup) <;> rfl

theorem all_swap {α β : Type} (S : List α) (Z : List β) (f : α → β → Bool) :
    (S.all fun q => Z.all fun p => f q p) = (Z.all fun p => S.all fun q => f q p) := by
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true]
  exact ⟨fun h p hp q hq => h q hq p hp, fun h q hq p hp => h p hp q hq⟩

theorem sylowTorus_code (Pl : List E) :
    sylowTorusCheck Pl = sylTK K1c K2c SylT (z4K ((Pl.map codeE).filter fun x => ordK x == 4)) := by
  unfold sylowTorusCheck sylTK
  rw [← map_filter_codeE _ _ (fun x => ordK x == 4) (fun x => by rw [ordK_codeE]), ← z4pairs_codes,
    ← syl36_codes, all_swap, List.all_map]
  refine congrArg _ (funext fun p => ?_)
  rw [Function.comp_apply, List.all_map]
  refine congrArg _ (funext fun q => ?_)
  simp only [Function.comp_apply, tripC, pairC, normAll_code, normK_code, List.map_cons, List.map_nil]

theorem nrm2_eq (a b x y : Nat) (L : List Nat) :
    nrm2 a (invK a) b (invK b) x y L = normAllK [a, b] [x, y] L := by
  unfold nrm2 normAllK
  simp only [andB_eq, memL_eq, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc]

theorem sylTK_of_E {K1 K2 E4 : List Nat} {S : List (Nat × Nat × List Nat)} {Z4 : List (Nat × Nat)}
    (hE : ∀ x ∈ E4, normKc K1 K2 x = true) (h : sylTE S E4 Z4 = true) : sylTK K1 K2 S Z4 = true := by
  unfold sylTE at h
  unfold sylTK
  rw [List.all_eq_true] at h ⊢
  intro p hp
  have hp' := h p hp
  rw [orB_eq, andB_eq, memL_eq, memL_eq, letB_eq, letB_eq, Bool.or_eq_true, Bool.and_eq_true] at hp'
  rw [List.all_eq_true]
  intro q hq
  rcases hp' with ⟨h1, h2⟩ | h3
  · rw [hE _ (List.contains_iff_mem.1 h1), hE _ (List.contains_iff_mem.1 h2)]
    simp
  · have := List.all_eq_true.1 h3 q hq
    rw [nrm2_eq] at this
    rw [this]
    rfl

theorem e4_normK (k : Nat) (hk : k < 3) : ∀ x ∈ E4c k, normKc K1c K2c x = true := by
  intro x hx
  rw [← pl_e4 k hk] at hx
  exact (List.mem_filter.1 hx).2

theorem sylowTorus_reps (k : Nat) (hk : k < 3) : sylowTorusCheck (PlOf (decE (PU.getD k 0))) = true := by
  rw [sylowTorus_code, PlOf_codes k hk]
  apply sylTK_of_E (e4_normK k hk)
  interval_cases k
  · exact nc_syl0
  · exact nc_syl0
  · exact nc_syl2

theorem noInv2_code (H0 : List E) (r : E) :
    (let cs := H0.map fun h => conjE h r
     cs.any fun x => cs.any fun y => ordE (mulE x y) % 2 == 0 || ordE (mulE x y) % 5 == 0) =
      noInvR (H0.map codeE) (codeE r) := by
  unfold noInvR noInvQ ev5
  simp only [List.any_map, Function.comp_def, ← conj_code, ← codeE_mulE, ordK_codeE]

theorem noInv2_tori (H0 : List E) (k : Nat) (hk : k = 0 ∨ k = 2) (hH : H0.map codeE = HT k) :
    ((Cs.filter fun x => ordE x == 3).all fun r =>
      let cs := H0.map fun h => conjE h r
      cs.any fun x => cs.any fun y => ordE (mulE x y) % 2 == 0 || ordE (mulE x y) % 5 == 0) = true := by
  have h5 : Fact (Nat.Prime 5) := fact5
  have hM := Mat.model_ιF (F := ZMod 5)
  rw [List.all_eq_true]
  intro r hr
  obtain ⟨hrC, h3⟩ := List.mem_filter.1 hr
  rw [beq_iff_eq] at h3
  have hrv := (mem_Cs_iff r).1 hrC
  have ho := hM.orderOf_of_ordE hrv h3 (by norm_num)
  have hp3 : powE r 3 = oneE := by
    apply hM.inj _ _ (hM.valid_powE hrv 3) hM.valid_one
    rw [hM.map_powE hrv, hM.map_one, ← ho, pow_orderOf_eq_one]
  have hr1 : r ≠ oneE := by
    rintro rfl
    rw [ordE_oneE] at h3
    exact absurd h3 (by norm_num)
  obtain ⟨c, hc3, hc5, d, hd, rfl⟩ := conj_rep3 hrv hp3 hr1
  obtain ⟨hrk, horb, -⟩ := cls_glue c hc5
  have hmem := (horb _ (hM.valid_conjE hd hrk)).1 ⟨d, hd, rfl⟩
  obtain ⟨j, hj, he⟩ := mem_decL.1 hmem
  have hcls := cls_ok c hc5
  rw [clsF_eq] at hcls
  have hspec := clsOK_spec hcls
  have hg : ∀ l < 2, validE (decE (f20 G l)) = true ∧ codeE (decE (f20 G l)) = f20 G l :=
    fun l hl => ⟨valid_decE (hspec.1 l hl).1, codeE_decE (validK_lt (hspec.1 l hl).1)⟩
  have hrc : codeE (decE (RP.getD c 0)) = RP.getD c 0 := codeE_decE (validK_lt hspec.2.1)
  have hgi := gi_eq hM (fun l => decE (f20 G l)) hg ((allN_iff _ _).1 gi_valid)
    fun l hl => (hspec.1 l hl).2
  obtain ⟨x, -, hxc, -⟩ := orb_sound hM (fun l => decE (f20 G l)) hg hgi hrk
    (fun j hj => hrc ▸ hspec.2.2.2.1 j hj) j hj
  have hcode : codeE (conjE d (decE (RP.getD c 0))) = oCode (f96 (OR.getD c 0) j) := by
    rw [← he, ← hxc, decE_codeE]
  have hchk : noInvR (HT k) (oCode (f96 (OR.getD c 0) j)) = true := by
    have hc34 : c = 3 ∨ c = 4 := by omega
    rcases hk with rfl | rfl <;> rcases hc34 with rfl | rfl
    · exact (allN_iff _ _).1 nc_inv03 j hj
    · exact (allN_iff _ _).1 nc_inv04 j hj
    · exact (allN_iff _ _).1 nc_inv23 j hj
    · exact (allN_iff _ _).1 nc_inv24 j hj
  rw [noInv2_code, hH, hcode]
  exact hchk

end CertificateChecks.FiveStd

end
