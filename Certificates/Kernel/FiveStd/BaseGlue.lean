module

public import Certificates.Kernel.FiveStd.ClsGlue
public import Certificates.Kernel.FiveStd.S0Base
public import Certificates.Kernel.FiveStd.Coset
public import CFSG.Certificates.Kernel.FiveStdKBaseSound
public import CFSG.Certificates.Kernel.FiveStdKListSound

public section

namespace CertificateChecks.FiveStd

open CFSG.KC.FiveStdK CFSG.GH74.GLS.LU.Local.FiveStd

theorem and16 {a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 : Bool} (h1 : a1 = true)
    (h2 : a2 = true) (h3 : a3 = true) (h4 : a4 = true) (h5 : a5 = true) (h6 : a6 = true)
    (h7 : a7 = true) (h8 : a8 = true) (h9 : a9 = true) (h10 : a10 = true) (h11 : a11 = true)
    (h12 : a12 = true) (h13 : a13 = true) (h14 : a14 = true) (h15 : a15 = true) (h16 : a16 = true) :
    (a1 && a2 && a3 && a4 && a5 && a6 && a7 && a8 && a9 && a10 && a11 && a12 && a13 && a14 && a15 &&
      a16) = true := by
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, Bool.and_self]

theorem k1_valid : K1l.all validE = true := by decide +kernel

theorem k2_valid : K2l.all validE = true := by decide +kernel

theorem s0gens_codes : S0gens.map codeE = S0gK := by decide +kernel

theorem r4_mem : ∀ ri ∈ R4I, ∃ r ∈ R4, S0c.contains r = true ∧ invK r = ri := by decide +kernel

theorem S0c_length : S0c.length = 128 := by decide +kernel

theorem S0_codes : S0.map codeE = S0c := by
  rw [S0, map_closureL, s0gens_codes, s0_closure]

theorem S0_eq : S0 = S0c.map decE := by
  rw [← S0_codes, List.map_map]
  conv_lhs => rw [← List.map_id S0]
  congr 1
  funext x
  exact (decE_codeE x).symm

theorem mem_S0 (x : E) : x ∈ S0 ↔ codeE x ∈ S0c := by
  rw [← S0_codes, List.mem_map]
  constructor
  · intro h
    exact ⟨x, h, rfl⟩
  · rintro ⟨y, hy, he⟩
    rwa [← codeE_injective he]

theorem S0c_lt {c : Nat} (hc : c ∈ S0c) : c < 781250 :=
  validK_lt (List.all_eq_true.1 s0_valid c hc)

theorem nodup_Cs : Cs.Nodup := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hgen := (clsOK_spec (clsF_eq 0 ▸ cls_ok 0 (by norm_num))).1
  exact nodup_Cs_of_tree (Mat.model_ιF (F := ZMod 5)) (fun l => decE (f20 G l))
    (fun l hl => ⟨valid_decE (hgen l hl).1, codeE_decE (validK_lt (hgen l hl).1)⟩) tree_all

theorem cs_coset : (Cs.all fun c => S0.any fun s => inKK (mulE c (invE s))) = true := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hgen := (clsOK_spec (clsF_eq 0 ▸ cls_ok 0 (by norm_num))).1
  rw [List.all_eq_true]
  intro c hc
  obtain ⟨i, hi, hic⟩ := tree_cover (Mat.model_ιF (F := ZMod 5)) (fun l => decE (f20 G l))
    (fun l hl => ⟨valid_decE (hgen l hl).1, codeE_decE (validK_lt (hgen l hl).1)⟩) tree_all c
    ((mem_Cs_iff c).1 hc)
  have h := (allN_iff _ _).1 (coset_chunks (i / 900) (by omega)) (i % 900) (Nat.mod_lt _ (by omega))
  have hi' : Nat.add (900 * (i / 900)) (i % 900) = i := by
    rw [nat_add]
    omega
  rw [hi'] at h
  obtain ⟨ri, hri, hk⟩ := List.any_eq_true.1 h
  obtain ⟨r, -, hr, hinv⟩ := r4_mem ri hri
  have hrS : r ∈ S0c := List.contains_iff_mem.1 hr
  rw [List.any_eq_true]
  refine ⟨decE r, (mem_S0 _).2 (by rw [codeE_decE (S0c_lt hrS)]; exact hrS), ?_⟩
  rw [← inKKK_codeE, codeE_mulE, codeE_invE, codeE_decE (S0c_lt hrS), hinv, ← hic]
  exact hk

theorem base_check : baseCheck = true := by
  unfold baseCheck
  refine and16 (beq_iff_eq.2 length_Cs) (List.all_eq_true.2 fun x hx => (mem_Cs_iff x).1 hx)
    k1_valid k2_valid ?_ (decide_eq_true (sorted_codes nodup_Cs)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    cs_coset
  · rw [List.all_eq_true]
    intro x hx
    rw [← validK_codeE]
    exact List.all_eq_true.1 s0_valid _ ((mem_S0 x).1 hx)
  · rw [nodupL_codeE, S0_codes]
    exact s0_nodup
  · rw [beq_iff_eq, ← List.length_map (f := codeE), S0_codes]
    exact S0c_length
  · rw [inL_codeE, S0_codes, codeE_oneE]
    exact s0_one
  · rw [inL_codeE, S0_codes, codeE_zE]
    exact s0_z
  · rw [List.all_eq_true]
    intro y hy
    rw [commE_codeE, codeE_zE]
    exact List.all_eq_true.1 s0_zcomm _ ((mem_S0 y).1 hy)
  · rw [List.all_eq_true]
    intro x hx
    rw [List.all_eq_true]
    intro y hy
    rw [inL_codeE, S0_codes, codeE_mulE]
    exact List.all_eq_true.1 (List.all_eq_true.1 s0_mul _ ((mem_S0 x).1 hx)) _ ((mem_S0 y).1 hy)
  · rw [List.all_eq_true]
    intro x hx
    rw [inL_codeE, S0_codes, codeE_invE]
    exact List.all_eq_true.1 s0_inv _ ((mem_S0 x).1 hx)
  · rw [beq_iff_eq, S0_eq, List.filter_map, List.length_map, ← s0_cent]
    congr 1
    apply List.filter_congr
    intro c hc
    simp only [Function.comp_apply, List.all_map]
    rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    refine forall₂_congr fun d hd => ?_
    simp only [Function.comp_apply]
    rw [commE_codeE, codeE_decE (S0c_lt hc), codeE_decE (S0c_lt hd)]
  · rw [beq_iff_eq, S0_eq, List.filter_map, List.length_map, ← s0_kk]
    congr 1

end CertificateChecks.FiveStd

end
