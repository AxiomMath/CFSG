module

public import Certificates.Kernel.J4M4.Facts

public section

namespace CertificateChecks.KernelJ4M4

open CFSG.KC.J4M4 CFSG.KC.J4Tree CFSG.KC.F2W CFSG.J4Tree.Native CFSG.J4Tree.Native.Node
open CFSG.J4Tree.M4 CFSG.KC.Co1F2

theorem node_parts :
    (treeBasis 539).all (fun ce => WL.contains (ccK ce)) = true ∧
    (treeWv 539).all (fun ce => RL.contains (ccK ce)) = true ∧
    kGens.all (fun k => (treeWv 539).all fun w =>
      eqC (mulW 12 (ccK k) (ccK w)) (mulW 12 (ccK w) (ccK k))) = true ∧
    fBasis.all (fun f => KL.contains (ccK f)) = true ∧
    fBasis.all (fun f => !eqC (ccK f) oneK) = true ∧
    fBasis.all (fun f => eqC (mulW 12 (ccK f) (ccK f)) oneK &&
      IR.any (fun r => Nat.beq r.1 (ccK f) && Nat.beq (CL.getD r.2.1 []).length 4)) = true ∧
    eqC (mulW 12 gcK GCI) oneK = true ∧
    fBasis.all (fun b => FL.contains (mulW 12 (mulW 12 gcK (ccK b)) GCI)) = true ∧
    (treeWv 539).any (fun w => WL.all fun k => !eqC k (mulW 12 (mulW 12 gcK (ccK w)) GCI)) =
      true ∧
    sextMasks.all (fun c => WL.contains (etaCK (tblC uCode) c)) = true := by
  have h := node_k
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem rc_gc : RC (codeOfWord gWord) gcK := rc_codeOfWord x_wf xi_wf gWord

theorem rc_gci : RC (codeOfWord gWord).inv GCI := rc_of_rows inv_g

theorem all_map_true {p : Code → Bool} {L : List (ℕ × ℕ)} (h : ∀ ce ∈ L, p (cc ce) = true) :
    (L.map cc).all p = true := by
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨ce, hce, rfl⟩ := List.mem_map.mp hx
  exact h ce hce

theorem any_map_true {p : Code → Bool} {L : List (ℕ × ℕ)} (h : ∃ ce ∈ L, p (cc ce) = true) :
    (L.map cc).any p = true := by
  rw [List.any_eq_true]
  obtain ⟨ce, hce, h⟩ := h
  exact ⟨cc ce, List.mem_map_of_mem hce, h⟩

theorem class_all : (closureOf (kGens.map cc)).toList.all
    (classOK (pairsOf (kGens.map cc)) (closureOf (fBasis.map cc))) = true := by
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨k, hk, hxk⟩ := (set_mem K_T K_C x).mp (Std.HashSet.mem_toList.mp hx)
  unfold classOK
  have hsq : (x * x == 1) = eqC (mulW 12 k k) oneK := rc_beq_eq (rc_mul hxk hxk) rc_one
  cases hc : eqC (mulW 12 k k) oneK
  · rw [bne, hsq, hc]
    rfl
  · have hsqk := sq_k
    unfold sqK at hsqk
    rw [eqL_iff] at hsqk
    have hin : k ∈ IR.map fun r => r.1 := by
      rw [← hsqk]
      exact List.mem_filter.mpr ⟨hk, hc⟩
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hin
    obtain ⟨horb, hsize, hF⟩ := orbit_of_rec hr hxk
    unfold classCore
    rw [horb, hsize, Bool.true_and, Bool.or_eq_true, Bool.or_eq_true]
    right
    by_cases h4 : (CL.getD r.2.1 []).length = 4
    · right
      exact set_contains (certOK_sound small_parts.1.1) small_parts.1.2 hxk (hF h4)
    · left
      simpa using h4

theorem basis_all : (fBasis.map cc).all (basisClassOK (pairsOf (kGens.map cc))) = true := by
  rw [List.all_eq_true]
  intro b hb
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hb
  have h := List.all_eq_true.mp node_parts.2.2.2.2.2.1 f hf
  rw [Bool.and_eq_true, List.any_eq_true] at h
  obtain ⟨hsq, r, hr, hr'⟩ := h
  rw [Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq] at hr'
  have hx : RC (cc f) r.1 := by rw [hr'.1]; exact rc_cc' f
  obtain ⟨horb, hsize, -⟩ := orbit_of_rec hr hx
  unfold basisClassOK basisCore
  rw [rc_beq_eq (rc_mul (rc_cc' f) (rc_cc' f)) rc_one, hsq, horb, hsize, hr'.2]
  rfl

theorem pairs_ok : pairsOK (pairsOf (kGens.map cc)) = true := by
  unfold pairsOK
  rw [List.all_eq_true]
  intro p hp
  obtain ⟨s, hs, rfl⟩ := List.mem_iff_getElem.mp hp
  have e := List.getD_eq_getElem (pairsOf (kGens.map cc)) (1, 1) hs
  obtain ⟨h1, h2⟩ := gp_rc s hs
  rw [e] at h1 h2
  rw [Bool.and_eq_true, rc_beq_eq (rc_mul h1 h2) rc_one, wf_of_rc h2]
  have hs10 : s < 10 := gp_len ▸ hs
  exact ⟨List.all_eq_true.mp pairs_k s (List.mem_range.mpr hs10), rfl⟩

theorem k539_ok : k539OK (closureOf (kGens.map cc)) (closureOf (fBasis.map cc))
    (closureOf ((treeWv 539).map cc)) (closureOf ((treeBasis 539).map cc)) (kGens.map cc)
    (fBasis.map cc) ((treeWv 539).map cc) ((treeBasis 539).map cc)
    (pairsOf (kGens.map cc)) (codeOfWord gWord) (codeOfWord gWord).inv = true := by
  obtain ⟨⟨hFT, hFC⟩, ⟨hWT, hWC⟩, ⟨hRT, hRC⟩, -, -⟩ := small_parts
  replace hFT := certOK_sound hFT
  replace hWT := certOK_sound hWT
  replace hRT := certOK_sound hRT
  obtain ⟨n1, n2, n3, n4, n5, -, n7, n8, n9, n10⟩ := node_parts
  have hgc := rc_gc
  have hgci := rc_gci
  have c6 : ((treeBasis 539).map cc).all (closureOf ((treeWv 539).map cc)).contains = true :=
    all_map_true fun ce hce => set_contains hWT hWC (rc_cc' ce) (List.all_eq_true.mp n1 ce hce)
  have c7 : ((treeWv 539).map cc).all (closureOf ((treeBasis 539).map cc)).contains = true :=
    all_map_true fun ce hce => set_contains hRT hRC (rc_cc' ce) (List.all_eq_true.mp n2 ce hce)
  have c8 : (kGens.map cc).all (fun k => ((treeWv 539).map cc).all fun w => k * w == w * k) =
      true := all_map_true fun k hk => all_map_true fun w hw => by
    rw [rc_beq_eq (rc_mul (rc_cc' k) (rc_cc' w)) (rc_mul (rc_cc' w) (rc_cc' k))]
    exact List.all_eq_true.mp (List.all_eq_true.mp n3 k hk) w hw
  have c9 : (fBasis.map cc).all (closureOf (kGens.map cc)).contains = true :=
    all_map_true fun f hf => set_contains K_T K_C (rc_cc' f) (List.all_eq_true.mp n4 f hf)
  have c10 : (fBasis.map cc).all (fun x => x != 1) = true := all_map_true fun f hf => by
    rw [bne, rc_beq_eq (rc_cc' f) rc_one]
    exact List.all_eq_true.mp n5 f hf
  have c14 : (codeOfWord gWord * (codeOfWord gWord).inv == 1) = true := by
    rw [rc_beq_eq (rc_mul hgc hgci) rc_one]
    exact n7
  have c15 : (codeOfWord gWord).inv.wf = true := wf_of_rc hgci
  have c16 : (fBasis.map cc).all (fun b => (closureOf (fBasis.map cc)).contains
      (codeOfWord gWord * b * (codeOfWord gWord).inv)) = true := all_map_true fun b hb =>
    set_contains hFT hFC (rc_mul (rc_mul hgc (rc_cc' b)) hgci) (List.all_eq_true.mp n8 b hb)
  have c17 : ((treeWv 539).map cc).any (fun w => !(closureOf ((treeWv 539).map cc)).contains
      (codeOfWord gWord * w * (codeOfWord gWord).inv)) = true := by
    rw [List.any_eq_true] at n9
    obtain ⟨w, hw, hw'⟩ := n9
    refine any_map_true ⟨w, hw, ?_⟩
    rw [set_not_contains hWT hWC (rc_mul (rc_mul hgc (rc_cc' w)) hgci) hw']
    rfl
  have c18 : sextMasks.all (fun c => (closureOf ((treeWv 539).map cc)).contains (etaCode c)) =
      true := by
    rw [List.all_eq_true] at n10 ⊢
    exact fun c hc => set_contains hWT hWC (rc_etaCode u_wf c) (n10 c hc)
  have c5 : ((closureOf (kGens.map cc)).size == 16384) = true := by
    rw [set_size K_T K_C bound_parts.1, bound_parts.2.1]
    rfl
  unfold k539OK
  simp only [set_sub K_T K_C, set_sub hFT hFC, set_sub hWT hWC, set_sub hRT hRC, c5, c6, c7, c8,
    c9, c10, pairs_ok, class_all, basis_all, c14, c15, c16, c17, c18, Bool.and_self]

theorem hOK_of {h : ℕ × ℕ} {y w : List (ℕ × ℕ)}
    (h1 : y.all (fun y => eqC (mulW 12 (ccK h) (ccK y)) (mulW 12 (ccK y) (ccK h))) = true)
    (h2 : w.any (fun w => !eqC (mulW 12 (ccK h) (ccK w)) (mulW 12 (ccK w) (ccK h))) = true) :
    hOK (cc h) (y.map cc) (w.map cc) = true := by
  have e1 : (y.map cc).all (fun y => cc h * y == y * cc h) = true := all_map_true fun ce hce => by
    rw [rc_beq_eq (rc_mul (rc_cc' h) (rc_cc' ce)) (rc_mul (rc_cc' ce) (rc_cc' h))]
    exact List.all_eq_true.mp h1 ce hce
  have e2 : (w.map cc).any (fun w => cc h * w != w * cc h) = true := by
    obtain ⟨ce, hce, h'⟩ := List.any_eq_true.mp h2
    refine any_map_true ⟨ce, hce, ?_⟩
    rw [bne, rc_beq_eq (rc_mul (rc_cc' h) (rc_cc' ce)) (rc_mul (rc_cc' ce) (rc_cc' h))]
    exact h'
  unfold hOK
  rw [e1, e2]
  rfl

theorem yOK_of {y w : List (ℕ × ℕ)} {yin os : List ℕ} {SL : List ℕ}
    {SY : List (List (ℕ × ℕ × ℕ))}
    (hT : certOK (actR (y.map ccK)) y.length oneK SL SY = true)
    (hC : closeOK (actR (y.map ccK)) y.length SL = true)
    (h1 : Nat.beq y.length yin.length = true)
    (h2 : (List.range y.length).all (fun i =>
      eqC (ccK (y.getD i (0, 0))) (maskK w (yin.getD i 0)) && os.contains (yin.getD i 0)) = true)
    (h3 : os.all (fun o => SL.contains (maskK w o)) = true) :
    yOK y w yin os = true := by
  unfold yOK yCore
  replace hT := certOK_sound hT
  rw [set_sub hT hC]
  have e1 : (y.length == yin.length) = true := beq_iff_eq.mpr (Nat.beq_eq ▸ h1)
  have e2 : (List.range y.length).all (fun i => cc (y.getD i (0, 0)) == maskCodeL w (yin.getD i 0) &&
      os.contains (yin.getD i 0)) = true := by
    rw [List.all_eq_true] at h2 ⊢
    intro i hi
    rw [rc_beq_eq (rc_cc' _) (rc_maskCodeL u_wf k_wf w _)]
    exact h2 i hi
  have e3 : os.all (fun o => (closureOf (y.map cc)).contains (maskCodeL w o)) = true := by
    rw [List.all_eq_true] at h3 ⊢
    exact fun o ho => set_contains hT hC (rc_maskCodeL u_wf k_wf w o) (h3 o ho)
  rw [e1, e2, e3]
  rfl

theorem codeChecks_ok : codeChecks () = true := by
  obtain ⟨-, -, -, ⟨hY1T, hY1C⟩, ⟨hY2T, hY2C⟩⟩ := small_parts
  have hh := h_k
  have hy := y_k
  simp only [Bool.and_eq_true] at hh hy
  unfold codeChecks
  rw [coords_k, k539_ok, hOK_of hh.1.1.1 hh.1.1.2, hOK_of hh.1.2 hh.2,
    yOK_of hY1T hY1C hy.1.1.1.1.1 hy.1.1.1.1.2 hy.1.1.1.2,
    yOK_of hY2T hY2C hy.1.1.2 hy.1.2 hy.2]
  rfl

end CertificateChecks.KernelJ4M4
