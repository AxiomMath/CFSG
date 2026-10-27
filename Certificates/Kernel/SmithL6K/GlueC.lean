module

public import Certificates.Kernel.SmithL6K.ChecksC0
public import Certificates.Kernel.SmithL6K.ChecksC1
public import Certificates.Kernel.SmithL6K.ChecksC2
public import Certificates.Kernel.SmithL6K.ChecksC3
public import Certificates.Kernel.SmithL6K.ChecksC4
public import Certificates.Kernel.SmithL6K.ChecksCR
public import Certificates.Kernel.SmithL6K.GlueW
public import CFSG.Certificates.Kernel.SmithL6KCSound

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6 CFSG.SmithL6.K CFSG.SmithL6.Kernel Matrix

theorem cx_pins' : cxU = ugC tvc ∧ cxL = [tvc.getD 0 0, tvc.getD 224 0] ∧
    ∀ i < 1395, fldW 64 cxAn i = annArr[i]! := by
  have h := cx_pins
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hU, hL⟩, hlen⟩, hall⟩ := h
  refine ⟨hU, hL, fun i hi => ?_⟩
  have hi' : i < anm.zipIdx.length := by rw [List.length_zipIdx, hlen]; exact hi
  have hm := List.getElem_mem hi'
  rw [List.getElem_zipIdx] at hm
  have e := hall _ hm
  simp only [Nat.zero_add] at e
  rw [e, annArr_eq hi, getD_of_lt (by rw [hlen]; exact hi)]

theorem cx_tvc_code : ∀ k < 1953, tvc.getD k 0 = codeOf (tvPair k) := fun _ hk => (tvPair_code hk).symm

theorem cx_code {j : Nat} (hj : j < 5) (a : Nat) {x : Nat} (hx : x < 1953) :
    candC cxU cxL j a (codeOf (tvPair x)) = codeOf (tvPair (trCandT (trLift j) a)[x]!) ∧
      (trCandT (trLift j) a)[x]! < 1953 := by
  rw [cx_pins'.1, cx_pins'.2.1]
  exact candC_code cx_tvc_code hj a hx

theorem cx_scans : ∀ j < 5, ∃ S, scanC tvc tcP cxU cxL cxRM j S 0 = true
  | 0, _ => ⟨_, cx_scan0⟩
  | 1, _ => ⟨_, cx_scan1⟩
  | 2, _ => ⟨_, cx_scan2⟩
  | 3, _ => ⟨_, cx_scan3⟩
  | 4, _ => ⟨_, cx_scan4⟩

theorem cx_cases {j : Nat} (hj : j < 5) {a : Nat} (ha : a < 512) :
    (∀ x < 1953, (trCandT (trLift j) a)[x]! = x) ∨
      (∃ x < 1953, (trCandT (trLift j) a)[(trCandT (trLift j) a)[x]!]! ≠ x) ∨
      ∃ k < 5, ∃ G H : Matrix (Fin 6) (Fin 6) (ZMod 2), Hᵀ * G = 1 ∧
        ∀ x < 1953, ∀ y < 1953, vP (codeOf (tvPair y)) = G *ᵥ vP (codeOf (tvPair x)) →
          fP (codeOf (tvPair y)) = H *ᵥ fP (codeOf (tvPair x)) →
          vP (codeOf (tvPair (trCandT (trLift (repsC.getD k (0, 0)).1) (repsC.getD k (0, 0)).2)[y]!))
              = G *ᵥ vP (codeOf (tvPair (trCandT (trLift j) a)[x]!)) ∧
            fP (codeOf (tvPair (trCandT (trLift (repsC.getD k (0, 0)).1) (repsC.getD k (0, 0)).2)[y]!))
              = H *ᵥ fP (codeOf (tvPair (trCandT (trLift j) a)[x]!)) := by
  obtain ⟨S, hS⟩ := cx_scans j hj
  have hRM := beq_iff_eq.1 cx_repsM
  rw [cx_pins'.1, cx_pins'.2.1] at hS hRM
  exact cand_cases tvc_length cx_tvc_code (fun _ hk => fld_tcP hk) hRM hj hS ha

theorem inPlane_iff {i x : Nat} (hi : i < 1395) :
    inPlane i x = ((fldW 64 wmP i).testBit (tvPair x).1 && (fldW 64 cxAn i).testBit (tvPair x).2) := by
  rw [inPlane, maskArr_get hi, ← wmP_eq hi, cx_pins'.2.2 i hi]

theorem cx_plane {j a i i' : Nat} (hj : j < 5) (h : planeK (candC cxU cxL j a) wmP cxAn i i' = true) :
    i < 1395 ∧ i' < 1395 ∧
      ∀ x < 1953, inPlane i x = true → inPlane i' (trCandT (trLift j) a)[x]! = true := by
  obtain ⟨hi, hi', hp⟩ := planeK_sound h
  refine ⟨hi, hi', fun x hx hin => ?_⟩
  have hP := tvP_tvPair hx
  rw [inPlane_iff hi, Bool.and_eq_true] at hin
  have e := hp _ hP.1 _ hP.2.1 hP.2.2.1 hP.2.2.2.1 hin.1 hin.2
  obtain ⟨ec, hlt⟩ := cx_code hj a hx
  have ec' : candC cxU cxL j a (64 * (tvPair x).1 + (tvPair x).2) =
      codeOf (tvPair (trCandT (trLift j) a)[x]!) := ec
  have hQ := tvP_tvPair hlt
  rw [ec', codeOf_div hQ, codeOf_mod hQ] at e
  rw [inPlane_iff hi', e.1, e.2]
  rfl

theorem cx_fix {j a i : Nat} (hj : j < 5) (hi : i < 1395)
    (h : fixPlaneC (candC cxU cxL j a) (fldW 64 wmP i) (fldW 64 cxAn i) = true) :
    ∀ x < 1953, inPlane i x = true → (trCandT (trLift j) a)[x]! = x := by
  intro x hx hin
  have hP := tvP_tvPair hx
  rw [inPlane_iff hi, Bool.and_eq_true] at hin
  have e := fixPlaneC_sound h _ hP.1 _ hP.2.1 hP.2.2.1 hP.2.2.2.1 hin.1 hin.2
  obtain ⟨ec, hlt⟩ := cx_code hj a hx
  have ec' : candC cxU cxL j a (64 * (tvPair x).1 + (tvPair x).2) =
      codeOf (tvPair (trCandT (trLift j) a)[x]!) := ec
  rw [ec'] at e
  exact codeOf_tvPair_inj hlt hx e

theorem cx_reps : ∀ k < 5, repOK cxU cxL wtP wmP cxAn k (cxR.getD k []) = true
  | 0, _ => cx_rep0
  | 1, _ => cx_rep1
  | 2, _ => cx_rep2
  | 3, _ => cx_rep3
  | 4, _ => cx_rep4

theorem cx_rep_facts {k : Nat} (hk : k < 5) :
    ∃ P : List (Nat × Nat), P.length = 6 ∧
      (∀ p ∈ P, p.1 < 1395 ∧ p.2 < 1395 ∧ ∀ x < 1953, inPlane p.1 x = true →
        inPlane p.2 (trCandT (trLift (repsC.getD k (0, 0)).1) (repsC.getD k (0, 0)).2)[x]! = true) ∧
      (∀ m, 0 < m → m < 64 → trXorSel (P.map fun p => wt p.2 ^^^ wt p.1) m ≠ 0) ∧
      ((∃ i i', i < 1395 ∧ i' < 1395 ∧ (∀ x < 1953, inPlane i x = true →
          inPlane i' (trCandT (trLift (repsC.getD k (0, 0)).1) (repsC.getD k (0, 0)).2)[x]! = true) ∧
          fB (wt i') (wt i) = true) ∨
        (∃ i < 1395, ∀ x < 1953, inPlane i x = true →
          (trCandT (trLift (repsC.getD k (0, 0)).1) (repsC.getD k (0, 0)).2)[x]! = x) ∨
        k = 3) := by
  have hr : (repsC.getD k (0, 0)).1 < 5 := by
    have := repsC_fst k hk
    by_cases h3 : k < 3 <;> omega
  obtain ⟨_, hpl, hind, hbr⟩ := repOK_sound (cx_reps k hk)
  have hpl' := fun p hp => cx_plane hr (hpl p hp)
  obtain ⟨hlen, hind'⟩ := indep6_sound hind
  have hd : dVecK wtP (pairsOf ((cxR.getD k []).drop 3)) =
      (pairsOf ((cxR.getD k []).drop 3)).map fun p => wt p.2 ^^^ wt p.1 := by
    unfold dVecK
    refine List.map_congr_left fun p hp => ?_
    rw [wtP_eq (hpl' p hp).2.1, wtP_eq (hpl' p hp).1]
  refine ⟨pairsOf ((cxR.getD k []).drop 3), by rw [← hlen, dVecK, List.length_map], hpl',
    fun m hm0 hm => by rw [← hd]; exact hind' m hm0 hm, ?_⟩
  rcases hbr with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h1
  · obtain ⟨hi, hi', hp⟩ := cx_plane hr h1
    refine Or.inl ⟨_, _, hi, hi', hp, ?_⟩
    rw [← wtP_eq hi, ← wtP_eq hi']
    exact h2
  · exact Or.inr (Or.inl ⟨_, h1, cx_fix hr h1 h2⟩)
  · exact Or.inr (Or.inr h1)

theorem cx_fx_iff {q : Nat} : q ∈ cxFx ↔ q ∈ trFixL (trCandT (trLift 4) 0) := by
  have h := (fpOK_sound cx_fp).2.2.2.2.1 q
  rw [h, trFixL, List.mem_filter, List.mem_range, beq_iff_eq]
  constructor
  · rintro ⟨hq, he⟩
    have hq' : q < 1953 := by rwa [tvc_length] at hq
    rw [← getD_of_lt (d := 0) hq, cx_tvc_code q hq', (cx_code (by decide) 0 hq').1] at he
    exact ⟨hq', codeOf_tvPair_inj (cx_code (by decide) 0 hq').2 hq' he⟩
  · rintro ⟨hq', he⟩
    have hq : q < tvc.length := by rw [tvc_length]; exact hq'
    refine ⟨hq, ?_⟩
    rw [← getD_of_lt (d := 0) hq, cx_tvc_code q hq', (cx_code (by decide) 0 hq').1, he]

theorem cx_outer : ∃ bs : List Nat, bs.length ≤ 8 ∧ ∃ pl : List (Nat × Nat),
    (∀ q ∈ pl, q.1 < 1395 ∧ q.2 < 1395 ∧
      (∀ x < 1953, inPlane q.1 x = true → inPlane q.2 (trCandT (trLift 4) 0)[x]! = true) ∧
      ∃ m, trXorSel bs m = wt q.2 ^^^ wt q.1) ∧
    (∀ t < 20, ∃ m, trXorSel (pl.map fun q => wt q.1) m = 2 ^ t) ∧
    (trFixL (trCandT (trLift 4) 0)).length % 2 = 1 ∧
    (∃ q₀ ∈ trFixL (trCandT (trLift 4) 0), ∀ Q : Nat → Prop, Q q₀ →
      (∀ q ∈ trFixL (trCandT (trLift 4) 0), ∀ u ∈ trFixL (trCandT (trLift 4) 0), Q u →
        Q (tvImg q u)) → ∀ v ∈ trFixL (trCandT (trLift 4) 0), Q v) ∧
    ∃ b6 : List Nat, b6.length = 6 ∧ (∀ x ∈ b6, x ∈ trFixL (trCandT (trLift 4) 0)) ∧
      ∀ m, 0 < m → m < 64 → trXorSel (b6.map fun x => (tvPair x).1) m ≠ 0 := by
  obtain ⟨hbs, _, hpl, hum, -, hnd, hodd, hreach, hb6, hind⟩ := fpOK_sound cx_fp
  have hpl' : ∀ q ∈ cxPl, q.1 < 1395 ∧ q.2 < 1395 ∧
      (∀ x < 1953, inPlane q.1 x = true → inPlane q.2 (trCandT (trLift 4) 0)[x]! = true) ∧
      ∃ m, trXorSel cxBs m = wt q.2 ^^^ wt q.1 := fun q hq => by
    obtain ⟨hp, m, hm⟩ := hpl q hq
    obtain ⟨hi, hi', hx⟩ := cx_plane (by decide) hp
    exact ⟨hi, hi', hx, m, by rw [hm, wtP_eq hi, wtP_eq hi']⟩
  have hperm : cxFx.Perm (trFixL (trCandT (trLift 4) 0)) :=
    (List.perm_ext_iff_of_nodup hnd (List.nodup_range.filter _)).2 fun q => cx_fx_iff
  have hlt : ∀ q ∈ cxFx, q < 1953 := fun q hq => by
    have := (cx_fx_iff.1 hq)
    rw [trFixL, List.mem_filter, List.mem_range] at this
    exact this.1
  have hne : 0 < cxFx.length := Nat.pos_of_ne_zero fun h0 => by
    rw [h0] at hodd
    exact absurd hodd (by decide)
  refine ⟨cxBs, hbs, cxPl, hpl', fun t ht => ⟨cxUm.getD t 0, ?_⟩, by rw [← hperm.length_eq]; exact hodd,
    ⟨cxFx.getD 0 0, cx_fx_iff.1 (by rw [getD_of_lt hne]; exact List.getElem_mem hne),
      fun Q h0 hstep v hv => ?_⟩, cxB6, ?_, fun x hx => cx_fx_iff.1 (hb6 x hx), ?_⟩
  · have e : cxPl.map (fun q => wt q.1) = cxPl.map fun p => fldW 20 wtP p.1 :=
      List.map_congr_left fun q hq => (wtP_eq (hpl' q hq).1).symm
    rw [e]
    exact hum t ht
  · have hmem : ∀ i < cxFx.length, cxFx.getD i 0 ∈ trFixL (trCandT (trLift 4) 0) := fun i hi =>
      cx_fx_iff.1 (by rw [getD_of_lt hi]; exact List.getElem_mem hi)
    have key := hreach (fun i => Q (cxFx.getD i 0)) (fun i _ hi => by
        rw [beq_iff_eq] at hi
        rw [hi]
        exact h0)
      (fun g hg u hu w hw he hQ => by
        unfold fxEdge at he
        rw [beq_iff_eq] at he
        have hg' := hlt (cxFx.getD g 0) (by rw [getD_of_lt hg]; exact List.getElem_mem hg)
        have hu' := hlt (cxFx.getD u 0) (by rw [getD_of_lt hu]; exact List.getElem_mem hu)
        have hw' := hlt (cxFx.getD w 0) (by rw [getD_of_lt hw]; exact List.getElem_mem hw)
        rw [fld_tcP hg', fld_tcP hu', fld_tcP hw', conjF_code hg' hu'] at he
        rw [← codeOf_tvPair_inj (tvImg_lt hg' hu') hw' he]
        exact hstep _ (hmem g hg) _ (hmem u hu) hQ)
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (cx_fx_iff.2 hv)
    have := key i hi
    rwa [getD_of_lt hi] at this
  · have h := (indep6_sound hind).1
    rwa [List.length_map] at h
  · have e : cxB6.map (fun x => fldW 12 tcP x / 64) = cxB6.map fun x => (tvPair x).1 :=
      List.map_congr_left fun x hx => by
        have hx' := hlt x (hb6 x hx)
        rw [fld_tcP hx', codeOf_div (tvP_tvPair hx')]
    have h := indep6_sound hind
    rw [e] at h
    exact h.2

end CertificateChecks.KernelSmithL6K
