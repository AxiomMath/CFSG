module

public import CFSG.Certificates.Kernel.Misc.Sp6WSound
public import Certificates.Kernel.Misc.Sp6W.Checks
public import Certificates.Kernel.Misc.Sp6W.Norm
public import Certificates.Kernel.Misc.G22C.Final

public section

namespace CFSG.KC.Sp6W

open CFSG.KGroups.Sp6 CFSG.Quasithin.H13 CFSG.Quasithin.H13.KGSp6 CFSG.KD.Sp6W CFSG.KC.Mat8P
  CFSG.KD.G22W CFSG.KC.G22W CFSG.KC.G22C

@[expose] noncomputable def nRecK : Bool :=
  (List.range 42).all fun i => Nat.blt (D.N i) T64 && goodK (D.N i) &&
    colsK (D.N i) == n0List.getD i [] && Nat.blt (D.NP i) 12096 &&
    colsK (numX REC (D.NP i)) == n0List.getD i []

theorem sp6w_nrec : nRecK = true := by decide +kernel

theorem sp6w_nU : n0List.all (fun n => maskL (uL.map (mulVecC n)) == maskL uL) = true := by
  decide +kernel

theorem sp6w_nS : n0List.all (fun n => (List.range 7).any fun k =>
    mulC s0 n == mulC n (powC s0 k)) = true := by
  decide +kernel

theorem sp6w_n_facts (i : ℕ) (hi : i < 42) : GoodL (D.N i) ∧ colsK (D.N i) = n0List.getD i [] ∧
    D.NP i < 12096 ∧ colsK (numX REC (D.NP i)) = n0List.getD i [] := by
  have h := sp6w_nrec
  simp only [nRecK, List.all_eq_true, List.mem_range, Bool.and_eq_true, Nat.blt_eq,
    beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h i hi
  exact ⟨goodL_of h1 h2, h3, h4, h5⟩

theorem sp6w_mem_n0 {n : List ℕ} (hn : n ∈ n0List) : ∃ i < 42, n0List.getD i [] = n := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hn
  rw [n0List_length] at hi
  exact ⟨i, hi, List.getD_eq_getElem _ _ (by rw [n0List_length]; exact hi)⟩

theorem sp6w_w_all : ∀ t < 34146, wRec D.N D.Z D.W 34146 831 t = true := by
  have hs : ∀ lo n hi, wRange D.N D.Z D.W 34146 831 lo n hi = true → n ≤ 64 * hi →
      ∀ t, lo ≤ t → t < lo + n → wRec D.N D.Z D.W 34146 831 t = true := by
    intro lo n hi h hn t hlo ht
    have h1 := CFSG.KC.G2Three.allBelow_g2 h hn (t - lo) (by omega)
    have e : Nat.add lo (t - lo) = t := Nat.add_sub_cancel' hlo
    rw [e] at h1
    exact h1
  intro t ht
  by_cases h0 : t < 4288
  · exact hs _ _ _ sp6w_w0_ok (by norm_num) t (by omega) (by omega)
  by_cases h1 : t < 8576
  · exact hs _ _ _ sp6w_w1_ok (by norm_num) t (by omega) (by omega)
  by_cases h2 : t < 12864
  · exact hs _ _ _ sp6w_w2_ok (by norm_num) t (by omega) (by omega)
  by_cases h3 : t < 17152
  · exact hs _ _ _ sp6w_w3_ok (by norm_num) t (by omega) (by omega)
  by_cases h4 : t < 21440
  · exact hs _ _ _ sp6w_w4_ok (by norm_num) t (by omega) (by omega)
  by_cases h5 : t < 25728
  · exact hs _ _ _ sp6w_w5_ok (by norm_num) t (by omega) (by omega)
  by_cases h6 : t < 30016
  · exact hs _ _ _ sp6w_w6_ok (by norm_num) t (by omega) (by omega)
  · exact hs _ _ _ sp6w_w7_ok (by norm_num) t (by omega) (by omega)

theorem cert4157_wit : witCheck 64 KGCert.g22Elems n0List 6047 = true := by
  have hG := CFSG.KD.G22C.g22c_facts.1
  have hNG : ∀ n ∈ n0List, n ∈ KGCert.g22Elems := by
    intro n hn
    obtain ⟨i, hi, rfl⟩ := sp6w_mem_n0 hn
    obtain ⟨-, -, h3, h4⟩ := sp6w_n_facts i hi
    rw [hG, mem_map_range]
    exact ⟨_, h3, h4⟩
  have hU : ∀ n ∈ n0List, maskL (uL.map (mulVecC n)) = maskL uL := by
    have h := sp6w_nU
    simp only [List.all_eq_true, beq_iff_eq] at h
    exact h
  have hNs : ∀ n ∈ n0List, ∃ k, mulC s0 n = mulC n (powC s0 k) := by
    have h := sp6w_nS
    simp only [List.all_eq_true, List.any_eq_true, beq_iff_eq] at h
    intro n hn
    obtain ⟨k, -, hk⟩ := h n hn
    exact ⟨k, hk⟩
  refine witCheck_of (N := D.N) (Z := D.Z) (W := D.W) (m := 34146) (nz := 831)
    (fun i hi => ⟨(sp6w_n_facts i hi).1, (sp6w_n_facts i hi).2.1⟩)
    (fun j hj => CFSG.KC.G2Three.allBelow_g2 sp6w_z_ok (by norm_num) j hj) sp6w_w_all rfl hNG hU
    (n0_closed CFSG.KC.Sp6N.cert4157_count_norm.2 (fun n hn => iso_of_mem_G (hNG n hn)) hNs)

end CFSG.KC.Sp6W

end
