module

public import CFSG.Certificates.Kernel.J4NPVerdict.Facts
public import Certificates.Kernel.J4Q.C4025
public import Certificates.Kernel.J4M2.Base
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Gens
public import CFSG.Quasithin.Vol2.KGFactC31J4M4F

public section

namespace CertificateChecks.KernelJ4NPV

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A
  CFSG.KC.J4Q CFSG.KD.J4Q
  CFSG.KD.J4NPV CFSG.KC.J4NPV CertificateChecks.KernelJ4Q CFSG.Quasithin.J4M2
  CFSG.Quasithin.KGC31.J4M4

theorem vjg_getN_eq (d : Nat) : ∀ (l : List Nat) (i : Nat), getN d l i = l.getD i d
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => vjg_getN_eq d l i

theorem vjg_getN_lt {l : List Nat} {i : Nat} (h : i < l.length) (d d' : Nat) :
    getN d l i = l.getD i d' := by
  rw [vjg_getN_eq, List.getD_eq_getElem _ _ h, List.getD_eq_getElem _ _ h]

theorem vjg_getN_ge {d : Nat} {l : List Nat} {i : Nat} (h : l.length ≤ i) : getN d l i = d := by
  rw [vjg_getN_eq, List.getD_eq_default _ _ h]

theorem vjg_takeK {α : Type} : ∀ (n : Nat) (l : List α), takeK n l = l.take n
  | 0, [] => rfl
  | _ + 1, [] => rfl
  | 0, _ :: _ => rfl
  | n + 1, x :: l => by
    change x :: takeK n l = x :: l.take n
    rw [vjg_takeK n l]

theorem vjg_dropK {α : Type} : ∀ (n : Nat) (l : List α), dropK n l = l.drop n
  | 0, _ => rfl
  | n + 1, [] => by
    change dropK n [] = []
    rw [vjg_dropK n []]
    exact List.drop_nil
  | n + 1, _ :: l => by
    change dropK n l = l.drop n
    exact vjg_dropK n l

theorem vjg_allK {α : Type} {f : α → Bool} : ∀ {l : List α}, allK f l = true → ∀ d ∈ l, f d = true
  | [], _, d, hd => absurd hd List.not_mem_nil
  | x :: l, h, d, hd => by
    change andB (f x) (allK f l) = true at h
    obtain ⟨h1, h2⟩ := vj_andB_iff.1 h
    rcases List.mem_cons.1 hd with rfl | hd
    · exact h1
    · exact vjg_allK h2 d hd

theorem vj_chunk {α : Type} {f : α → Bool} {n m : Nat} {ds : List α} (hlen : ds.length ≤ n * m)
    (h : ∀ i < m, chunkB f n ds i = true) : ∀ d ∈ ds, f d = true := by
  intro d hd
  obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hd
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0, Nat.zero_mul] at hlen
      omega
    · exact h0
  have hi : idx / n < m := by
    rw [Nat.div_lt_iff_lt_mul hn]
    rw [Nat.mul_comm] at hlen
    omega
  have hc := h _ hi
  have e : chunkB f n ds (idx / n) = allK f ((ds.drop (n * (idx / n))).take n) := by
    unfold chunkB
    rw [vjg_takeK, vjg_dropK]
    rfl
  rw [e] at hc
  apply vjg_allK hc
  have hk : n * (idx / n) + idx % n = idx := Nat.div_add_mod idx n
  have hm : idx % n < n := Nat.mod_lt _ hn
  have hlt : idx % n < ((ds.drop (n * (idx / n))).take n).length := by
    rw [List.length_take, List.length_drop]
    omega
  have e2 : ((ds.drop (n * (idx / n))).take n)[idx % n] = ds[idx] := by
    rw [List.getElem_take, List.getElem_drop]
    congr 1
  rw [← e2]
  exact List.getElem_mem hlt

theorem vjg_rep {X : Array V2} {M : Nat} {x : J} (h : WfA X ∧ encR X = M) (hx : Mx x = rowsMatrix X) :
    VjRep M x :=
  ⟨X, h.1, h.2, hx.symm⟩

theorem vjg_l5 (i : Nat) : VjRep (getN one vjT.l5 i) (gen5 i) :=
  vjg_rep (gens_append locMats_size loc_gens base_gens i) (g5Mats_spec matFacts i).symm

theorem vjg_l5i (i : Nat) : VjRep (getN one vjT.l5i i) (gen5 i)⁻¹ :=
  vjg_rep (gens_append locInvs_size loc_invs base_invs i) (g5Invs_spec matFacts i).symm

theorem vjg_km {i : Nat} (hi : i < 4) : VjRep (getN one mkKMs i) (kJ i) := by
  have h := kRows_enc hi
  rw [← kTab_get hi] at h
  exact vjg_rep h (Mx_kJ matFacts hi)

theorem vjg_kJ_of_le {i : Nat} (hi : 4 ≤ i) : kJ i = 1 := by
  have hk : kWords.getD i [] = [] := List.getD_eq_default _ _ (by simp [kWords]; omega)
  unfold kJ
  rw [hk]
  rfl

theorem vjg_km_all (i : Nat) : VjRep (getN one vjT.km i) (kJ i) := by
  by_cases hi : i < 4
  · exact vjg_km hi
  · rw [vjg_kJ_of_le (by omega), vjg_getN_ge (by change 4 ≤ i; omega)]
    exact vjRep_one hK

theorem vjg_km' {i : Nat} (hi : i < 4) : VjRep (vjT.km.getD i 0) (kJ i) := by
  rw [← vjg_getN_lt (l := vjT.km) hi one 0]
  exact vjg_km_all i

theorem vjg_us {i : Nat} (hi : i < 11) : VjRep (vjT.us.getD i 0) (uJ i) := by
  have h := uTab_enc i (by rw [Us_length]; exact hi)
  rw [vjg_getN_lt (l := Us) (by rw [Us_length]; exact hi) one 0] at h
  exact vjg_rep h (Mx_uJ matFacts hi)

theorem vjg_gE_of_le {m : Nat} (hm : 32 ≤ m) : gE m = 1 := by
  have hk : kWords.getD (m - 28) [] = [] :=
    List.getD_eq_default _ _ (by simp [kWords]; omega)
  unfold gE genWord
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), hk]
  rfl

theorem vjg_ge (i : Nat) : VjRep (getN one vjT.ge i) (gE i) := by
  by_cases h28 : i < 28
  · have h := CertificateChecks.KernelJ4M2.gm_enc (n := i) (by omega)
    have e : CertificateChecks.KernelJ4M2.gmK i = getN one vjT.ge i := by
      interval_cases i <;> rfl
    rw [e] at h
    exact vjg_rep h (Mx_gE matFacts (n := i) (by omega))
  · by_cases h32 : i < 32
    · obtain ⟨j, rfl⟩ : ∃ j, i = 28 + j := ⟨i - 28, by omega⟩
      have hj : j < 4 := by omega
      rw [gE_k hj]
      have e : getN one vjT.ge (28 + j) = getN one mkKMs j := by
        interval_cases j <;> rfl
      rw [e]
      exact vjg_km hj
    · rw [vjg_gE_of_le (by omega), vjg_getN_ge (by change 32 ≤ i; omega)]
      exact vjRep_one hK

theorem vjg_gei (i : Nat) : VjRep (getN one vjT.gei i) (gE i)⁻¹ := by
  obtain ⟨hlen, h⟩ := invsK_spec vj79_ginv
  have hl : vjT.ge.length = 32 := rfl
  by_cases hi : i < 32
  · obtain ⟨hc, hm⟩ := h i (by rw [hl]; exact hi)
    have hg := vjg_ge i
    rw [vjg_getN_lt (by rw [hl]; exact hi) one 0] at hg
    rw [vjg_getN_lt (by rw [← hlen, hl]; exact hi) one 0]
    exact vjRep_inv hK hg hc hm
  · rw [vjg_gE_of_le (by omega), inv_one, vjg_getN_ge (by rw [← hlen, hl]; omega)]
    exact vjRep_one hK

theorem vjg_base (i : Nat) : VjRep (getN one [A, B] i) (baseJ i) := by
  refine vjg_rep (base_gens i) ?_
  rw [Mx_apply, coe_baseJ]
  exact (baseMats_spec matFacts i).symm

theorem vjg_basei (i : Nat) : VjRep (getN one [Ai, Bi] i) (baseJ i)⁻¹ := by
  refine vjg_rep (base_invs i) ?_
  have h := baseInvs_spec matFacts i
  rw [← coe_baseJ] at h
  exact Mx_inv_of _ _ h

theorem vjg_w (i : Nat) :
    VjRep (getN one [W1, W2] i) (m4gen i) ∧ VjRep (getN one [W1i, W2i] i) (m4gen i)⁻¹ := by
  obtain ⟨hw, hi⟩ := vj_andB_iff.1 vj79_w
  obtain ⟨-, hw⟩ := wordsK_spec hw
  obtain ⟨-, hi⟩ := invsK_spec hi
  have h1 := vjRep_wordJ hK vjg_base vjg_basei w1Word
  have h2 := vjRep_wordJ hK vjg_base vjg_basei w2Word
  rw [← w1_eq] at h1
  rw [← w2_eq] at h2
  rcases (show i = 0 ∨ i = 1 ∨ 2 ≤ i by omega) with rfl | rfl | hi2
  · have e : W1 = wordJ c rm one [A, B] [Ai, Bi] w1Word := hw 0 (by decide)
    obtain ⟨hc, hm⟩ := hi 0 (by decide)
    have hc' : canonJ pad W1i = true := hc
    have hm' : mulJ c rm W1 W1i = one := hm
    rw [← e] at h1
    exact ⟨h1, vjRep_inv hK h1 hc' hm'⟩
  · have e : W2 = wordJ c rm one [A, B] [Ai, Bi] w2Word := hw 1 (by decide)
    obtain ⟨hc, hm⟩ := hi 1 (by decide)
    have hc' : canonJ pad W2i = true := hc
    have hm' : mulJ c rm W2 W2i = one := hm
    rw [← e] at h2
    exact ⟨h2, vjRep_inv hK h2 hc' hm'⟩
  · have e : m4gen i = 1 := by
      unfold m4gen
      rw [if_neg (by omega), if_neg (by omega)]
    rw [e, inv_one, vjg_getN_ge (by change 2 ≤ i; omega), vjg_getN_ge (by change 2 ≤ i; omega)]
    exact ⟨vjRep_one hK, vjRep_one hK⟩

theorem vjg_fm {j : Nat} (hj : j < 10) : VjRep (vjT.fm.getD j 0) (fJn j) := by
  obtain ⟨-, h⟩ := wordsK_spec vj79_f
  rw [h j hj]
  exact vjRep_wordJ hK (fun i => (vjg_w i).1) (fun i => (vjg_w i).2) _

theorem vj_tabs : TabsOK vjT gen5 gE uJ kJ fJn where
  consts := ⟨pad, t0, t1, t2, t3, t4, t5, t6, hK⟩
  l5 := vjg_l5
  l5i := vjg_l5i
  ge := vjg_ge
  gei := vjg_gei
  us_len := rfl
  us := fun _ hi => vjg_us hi
  km_len := rfl
  km := vjg_km_all
  km' := fun _ hi => vjg_km' hi
  fm_len := rfl
  fm := fun _ hj => vjg_fm hj

theorem vj_comm : ∀ i < 11, ∀ j < 11, uJ i * uJ j = uJ j * uJ i :=
  comm_of_commK vj_tabs vj79_ucomm

end CertificateChecks.KernelJ4NPV

end
