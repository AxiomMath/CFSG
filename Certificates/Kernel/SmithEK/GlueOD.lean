module

public import Certificates.Kernel.SmithEK.GlueOU

public section

set_option exponentiation.threshold 1000

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE CFSG.SmithE.K CFSG.F4.Native CFSG.Fischer CFSG.Fischer.Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.KC.Misc.O73

attribute [local irreducible] CFSG.F4.Native.uPts CFSG.F4.Native.uPos perpTab uaPts

theorem countP_range_mem (q : Nat → Bool) {n : Nat} : ∀ {l : List Nat}, l.Nodup →
    (∀ x ∈ l, x < n) → (List.range n).countP (fun a => decide (a ∈ l) && q a) = l.countP q
  | [], _, _ => by simp
  | x :: l, hnd, hl => by
    rw [List.nodup_cons] at hnd
    have ih := countP_range_mem q hnd.2 fun y hy => hl y (List.mem_cons_of_mem _ hy)
    have hx : x < n := hl x List.mem_cons_self
    by_cases hq : q x = true
    · rw [CFSG.SmithE.K.countP_range_split _ (fun a => decide (a ∈ l) && q a) x (fun a => ?_)
        (by simp [hnd.1]), if_pos hx, ih, List.countP_cons_of_pos hq]
      by_cases hax : a = x
      · subst hax
        simp [hq, hnd.1]
      · simp [hax]
    · rw [List.countP_cons_of_neg hq, ← ih]
      refine List.countP_congr fun a _ => ?_
      by_cases hax : a = x
      · subst hax
        simp [hq, hnd.1]
      · simp [hax]

theorem uaMem_iff_mem {j : Nat} (hj : j < 891) (a : Nat) :
    uaMem uaPts[j]! a = true ↔ a ∈ (List.range 21).map fun k => (uaPts[j]!)[k]! := by
  unfold uaMem
  rw [anyIn_eq_true, List.mem_map]
  simp only [beq_iff_eq, List.mem_range]

theorem uaMeet_eq_meetK {j : Nat} (hj : j < 891) :
    uaMeet uaPts[0]! uaPts[j]! = meetK (packK pb.P) (pb.P.getD 0 0) j := by
  obtain ⟨-, hlt, hinj, -⟩ := CFSG.LargeExtraspecial.SMod20.uaPlane_parts hj
  obtain ⟨-, hlt0, -⟩ := CFSG.LargeExtraspecial.SMod20.uaPlane_parts (i := 0) (by omega)
  set wl := (List.range 21).map fun k => (uaPts[j]!)[k]! with hwl
  have hnd : wl.Nodup := by
    refine (List.nodup_range).map_on fun a ha b hb e => ?_
    by_contra hab
    exact hinj a (List.mem_range.1 ha) b (List.mem_range.1 hb) hab e
  have hwlt : ∀ x ∈ wl, x < 693 := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    exact hlt k (List.mem_range.1 hk)
  have hc : cntB 693 (pb.P.getD 0 0 &&& pb.P.getD j 0) =
      (List.range 21).countP fun k => uaMem uaPts[0]! (uaPts[j]!)[k]! := by
    unfold cntB
    have e1 : (List.range 693).countP (fun a => (pb.P.getD 0 0 &&& pb.P.getD j 0).testBit a) =
        (List.range 693).countP (fun a => decide (a ∈ wl) && (pb.P.getD 0 0).testBit a) := by
      refine List.countP_congr fun a ha => ?_
      have ha' := List.mem_range.1 ha
      rw [Nat.testBit_and, ← uaMem_pb hj ha', Bool.and_comm]
      cases h : uaMem uaPts[j]! a
      · have : a ∉ wl := fun hm => by rw [(uaMem_iff_mem hj a).2 hm] at h; exact absurd h (by simp)
        simp [this]
      · have hm : a ∈ wl := (uaMem_iff_mem hj a).1 h
        simp [hm]
    rw [e1, countP_range_mem _ hnd hwlt, hwl, List.countP_map]
    refine List.countP_congr fun k hk => ?_
    simp only [Function.comp_apply]
    rw [uaMem_pb (by omega) (hlt k (List.mem_range.1 hk))]
  have hx : pb.P.getD 0 0 &&& pb.P.getD j 0 < 2 ^ 693 :=
    lt_of_le_of_lt Nat.and_le_left (pb_lt (by omega))
  have hle : cntB 693 (pb.P.getD 0 0 &&& pb.P.getD j 0) ≤ 21 := by
    rw [hc]
    exact le_trans List.countP_le_length (by simp)
  unfold meetK uaMeet
  rw [at'_packK _ pb_all_lt]
  change _ = cntK 21 (pb.P.getD 0 0 &&& pb.P.getD j 0)
  rw [cntK_eq 21 _ hx hle, hc]

theorem find?_range_first {p : ℕ → Bool} {n m : ℕ} (hm : m < n) (hp : p m = true)
    (h : ∀ k < m, p k = false) : (List.range n).find? p = some m := by
  rw [List.find?_eq_some_iff_getElem]
  refine ⟨hp, m, by simpa using hm, by simp, fun j hj => ?_⟩
  simp only [List.getElem_range, Bool.not_eq_true']
  exact h j hj

theorem uaDRoot_eq {j : Nat} (hj : j < 891) :
    uaDRoot uaPts (uaMeet uaPts[0]! uaPts[j]!) =
      dRootK po.DS (meetK (packK pb.P) (pb.P.getD 0 0) j) := by
  obtain ⟨hcls, hlen, hlt, hfirst⟩ := dsK_sound c21262ds_0
  rw [uaMeet_eq_meetK hj]
  have key : ∀ i < 4, uaDRoot uaPts ([21, 5, 1, 0].getD i 0) = po.DS.getD i 0 := by
    intro i hi
    have hmem : ([21, 5, 1, 0].getD i 0, po.DS.getD i 0) ∈ List.zip [21, 5, 1, 0] po.DS := by
      rw [List.mem_iff_getElem]
      refine ⟨i, by simp [hlen]; omega, ?_⟩
      rw [List.getElem_zip]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : i < po.DS.length)]
      interval_cases i <;> rfl
    obtain ⟨h1, h2⟩ := hfirst _ hmem
    have hd : po.DS.getD i 0 < 891 :=
      hlt _ (by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
    unfold uaDRoot
    rw [find?_range_first hd (by rw [beq_iff_eq, uaMeet_eq_meetK hd]; exact h1) fun k hk => by
      rw [beq_eq_false_iff_ne, uaMeet_eq_meetK (by omega)]
      exact h2 k hk]
    rfl
  rcases hcls j hj with h | h | h | h <;> rw [h]
  · exact key 0 (by omega)
  · exact key 1 (by omega)
  · exact key 2 (by omega)
  · exact key 3 (by omega)

theorem plp_get {p : Nat} (hp : p < 891) (m : Nat) :
    at' 10 (at' 210 po.PLP p) m = (po.PL.getD p []).getD m 0 := by
  have h := plpK_sound c21262plp_0 p (by rw [poPL_len]; exact hp)
  rw [Nat.zero_add] at h
  rw [h, at'_pack10]
  intro x hx
  have := (plK_sound c21262pl_0 p (by rw [pb_len]; exact hp)).2.1 x hx
  omega

theorem reachD : CFSG.SmithL6.K.Reach 891 34
    (fun j => j == uaDRoot uaPts (uaMeet uaPts[0]! uaPts[j]!))
    (fun g j' j => uaMeet uaPts[0]! uaPts[j']! == uaMeet uaPts[0]! uaPts[j]! &&
      allIn 0 21 fun m => uaMem uaPts[j]! (stabAp tvTabs stabWords[g]! (uaPts[j']!)[m]!)) := by
  have h := CFSG.SmithL6.K.reach_of_treeK c21262dtree_0
  intro Q hroot hstep
  refine h Q (fun v hv hr => hroot v hv ?_) (fun g hg u hu v hv he hQ => hstep g hg u hu v hv ?_ hQ)
  · rw [beq_iff_eq, uaDRoot_eq hv, ← Nat.beq_eq]
    exact hr
  · unfold edgeD at he
    rw [Bool.and_eq_true, Nat.beq_eq, wImgP_iff] at he
    rw [Bool.and_eq_true, beq_iff_eq, uaMeet_eq_meetK hu, uaMeet_eq_meetK hv]
    refine ⟨he.1, allIn_eq_true.2 fun m _ hm => ?_⟩
    obtain ⟨-, hlt, -⟩ := CFSG.LargeExtraspecial.SMod20.uaPlane_parts hu
    have hmem := uaPts_mem_pl hu hm
    obtain ⟨m', hm', hx⟩ := List.getElem_of_mem hmem
    have hlen := (plK_sound c21262pl_0 u (by rw [pb_len]; exact hu)).1
    have hm'' : m' < 21 := hlen ▸ hm'
    have hb := he.2 m' hm''
    rw [plp_get hu, List.getD_eq_getElem _ _ hm', hx, sw_get hg, at'_packK _ pb_all_lt] at hb
    have hS := stabAp_TP (sw_mem hg) (hlt m hm)
    rw [uaMem_pb hv hS.2, hS.1]
    exact hb

end CertificateChecks.KernelSmithEK
