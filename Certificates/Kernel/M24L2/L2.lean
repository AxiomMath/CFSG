
module

public import Certificates.Kernel.M24L2.Ctx
public import Certificates.Kernel.M24L2.L2Check
public import Certificates.Kernel.M24L2.L2DCheck
public import Certificates.Kernel.M24L2.L2FcCheck
public import CFSG.Certificates.Kernel.M24L2.L2FcSound
public import CFSG.Certificates.Kernel.M24L2.MaskSound

public section

namespace CertificateChecks.KernelM24L2

open CFSG.KC.M24L2 CFSG.CGT.M24R

theorem slices_glL {Q : Nat → Bool} {F : List (Nat × Nat × Nat) → Bool}
    (hF : ∀ E, F E = true → Q 33825 = true ∧ ∀ e ∈ E, Q e.1 = true)
    (hK : ∀ k < 20, F (glES.getD k []) = true) : ∀ m ∈ glL, Q m = true := by
  intro m hm
  unfold glL at hm
  rcases List.mem_cons.1 hm with rfl | hm
  · exact (hF _ (hK 0 (by norm_num))).1
  · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hm
    obtain ⟨E, hE, heE⟩ := List.mem_flatten.1 he
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hE
    have h20 : glES.length = 20 := rfl
    have h := hK k (by rw [h20] at hk; exact hk)
    rw [List.getD_eq_getElem _ _ hk] at h
    exact (hF _ h).2 e heE

theorem sliceSpec {Q : Nat → Bool} {E : List (Nat × Nat × Nat)}
    (h : (Q (nat_lit 33825) && allL (fun e => letN e.1 fun m => Q m) E) = true) :
    Q 33825 = true ∧ ∀ e ∈ E, Q e.1 = true := by
  rw [Bool.and_eq_true, allL_eq, List.all_eq_true] at h
  exact ⟨h.1, fun e he => by have := h.2 e he; rwa [letN_eq] at this⟩

theorem faK_all : ∀ k < 20, faK k = true := by
  intro k hk
  interval_cases k
  exacts [faK0, faK1, faK2, faK3, faK4, faK5, faK6, faK7, faK8, faK9, faK10, faK11, faK12, faK13,
    faK14, faK15, faK16, faK17, faK18, faK19]

theorem fbK_all : ∀ k < 20, fbK k = true := by
  intro k hk
  interval_cases k
  exacts [fbK0, fbK1, fbK2, fbK3, fbK4, fbK5, fbK6, fbK7, fbK8, fbK9, fbK10, fbK11, fbK12, fbK13,
    fbK14, fbK15, fbK16, fbK17, fbK18, fbK19]

theorem dK_all : ∀ k < 20, dK k = true := by
  intro k hk
  interval_cases k
  exacts [dK0, dK1, dK2, dK3, dK4, dK5, dK6, dK7, dK8, dK9, dK10, dK11, dK12, dK13, dK14, dK15,
    dK16, dK17, dK18, dK19]

theorem dLK_all : ∀ k < 20, dLK k = true := by
  intro k hk
  interval_cases k
  exacts [dLK0, dLK1, dLK2, dLK3, dLK4, dLK5, dLK6, dLK7, dLK8, dLK9, dLK10, dLK11, dLK12, dLK13,
    dLK14, dLK15, dLK16, dLK17, dLK18, dLK19]

theorem glL_contains_zero : glL.contains 0 = false := by
  rw [Bool.eq_false_iff]
  intro h
  rw [List.contains_iff_mem] at h
  unfold glL at h
  rcases List.mem_cons.1 h with h | h
  · exact absurd h (by norm_num)
  · obtain ⟨e, he, he0⟩ := List.mem_map.1 h
    obtain ⟨E, hE, heE⟩ := List.mem_flatten.1 he
    have hz := glL_zero
    rw [allL_eq, List.all_eq_true] at hz
    have := hz E hE
    rw [allL_eq, List.all_eq_true] at this
    have := this e heE
    rw [he0] at this
    simp at this

theorem l2_facts : relCheck = true ∧ ctxCheck (mkCtx ()) = true ∧ tCheck (mkCtx ()) = true ∧
    tNormCheck (mkCtx ()) = true ∧ bCheck (mkCtx ()) = true ∧ faCheck (mkCtx ()) = true ∧
    fbCheck (mkCtx ()) = true ∧ dCheck (mkCtx ()) = true ∧ fcCheck (mkCtx ()) = true := by
  obtain ⟨hR, hnd, hL, hlen⟩ := reach
  have hGL := mask_contains invK_all tree_ok
  have hG : ∀ n, validK glMask n = true → n ∈ (mkCtx ()).codes := fun n h =>
    mem_of_validK hR hGL h
  refine ⟨relCheck_eq ▸ rel_ok, ctxCheck_of hR hnd hL hlen, tCheck_eq ▸ tC_ok,
    tNormCheck_eq ▸ tN_ok, bCheck_eq ▸ b_ok, ?_, ?_, ?_, ?_⟩
  · exact faCheck_of hR hL hG (slices_glL (F := faE glMask faW) (fun E h => sliceSpec h) faK_all)
  · exact fbCheck_of hR hL hG (slices_glL (F := fbE glMask fbW) (fun E h => sliceSpec h) fbK_all)
  · exact dCheck_of hR hL dP1_ok (slices_glL (F := dE) (fun E h => sliceSpec h) dK_all) dP3_ok
  · have hdl : ∀ d ∈ dL, validK glMask d = true ∧ normBK d = true := by
      have h := dL_ok
      rw [allL_eq, List.all_eq_true] at h
      intro d hd
      have := h d hd
      rwa [Bool.and_eq_true] at this
    have hth : ∀ i : Fin 3, validK glMask (thC i) = true := by
      have h := th_ok
      rw [List.all_eq_true] at h
      exact fun i => h i (List.mem_finRange i)
    have hfc : fcTreeK dL fcAllK thCodesK 3 [] = true := by
      rw [fcAllK_eq dTwin_length]
      exact fc_ok
    exact fcCheck_of hR hL glL_contains_zero hG dL_sorted hdl
      (slices_glL (F := dLE dL) (fun E h => sliceSpec h) dLK_all) hth hfc

end CertificateChecks.KernelM24L2
