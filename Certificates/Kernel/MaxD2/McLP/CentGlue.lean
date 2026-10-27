module

public import Certificates.Kernel.MaxD2.McLP.Glue
public import Certificates.Kernel.MaxD2.McLP.CentChecks
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMaxD2.McLP

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 CFSG.KS.PEnum CFSG.KS.Row
open CFSG.PSL3Four.Native Certificates.MaxD2Perm Certificates.MaxD2Heis Certificates.MclCentOver

theorem invsOK_of {n w k : Nat} {S : Array Tab} {PS PSI : Nat → Nat}
    (hS : S.size = k ∧ ∀ l < k, S[l]! = unpack n w (PS l))
    (hp : ∀ l < k, permOK n w (mask w) (n * w) (PS l) (PSI l) = true) :
    invsOK n S (S.map (invTab n)) = true := by
  unfold invsOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨by simp, allBelow_iff'.2 fun l hl => ?_⟩
  rw [hS.1] at hl
  rw [getElem!_pos _ l (by simp [hS.1, hl]), Array.getElem_map,
    ← getElem!_pos S l (by rw [hS.1]; exact hl), hS.2 l hl, inv_u (hp l hl), inv_comp (hp l hl)]
  simp [size_u]

theorem hC : HypsC mclFiveDataP KH := hypsH.toHypsBC.toHypsC

theorem hD : mclFiveDataP.n = 275 := rfl

theorem hn : szOK 275 9 = true := hC.hn

theorem hb : mclFiveDataP.gT[1]! = unpack 275 9 (GP 1) := gT_bind 1 (by decide)

theorem cb : Cn 275 9 (GP 1) := (perm_canon (c_gp_perm hC (j := 1) (by decide)) hn).1

theorem htT : wT mclFiveDataP mclFiveDataP.tW = unpack 275 9 (TT 0) := c_wT_u hC hypsH.hTw

theorem ct : Cn 275 9 (TT 0) := (perm_canon hypsH.hTp hn).1

theorem nk : NE.k = 4 := by decide +kernel

theorem ng_size : (nGens mclFiveDataP).size = 4 := by
  rw [← nk]
  exact (c_ngens hC).1

theorem ng_bind : (nGens mclFiveDataP).size = NE.k ∧
    ∀ l < NE.k, (nGens mclFiveDataP)[l]! = unpack 275 9 (NE.G l) :=
  ⟨(c_ngens hC).1, fun l hl => c_ng_get hC hl⟩

theorem co_all : ∀ k < 5, wordEqK 275 9 (mask 9) (pidn 275 9) NE.G NGI NE.k (cW[k]!) (CO k) = true ∧
    canonK 275 9 (mask 9) (275 * 9) (CO k) = true ∧
    permOK 275 9 (mask 9) (275 * 9) (CO k) (COI k) = true := by
  intro k hk
  have h := (PK.allN_iff.1 k_co) k hk
  simp only [Bool.and_eq_true] at h
  exact h

theorem cs_size : (cGens mclFiveDataP).size = 5 := by simp [cGens, cW]

theorem cs_get {k : Nat} (hk : k < 5) : (cGens mclFiveDataP)[k]! = unpack 275 9 (CO k) := by
  unfold cGens
  rw [map_get _ (by simpa [cW] using hk)]
  exact wordT_u ng_bind (PK.allN_iff.2 fun l hl => hC.hNI l hl) (co_all k hk).1

theorem cs_bind : (cGens mclFiveDataP).size = 5 ∧
    ∀ l < 5, (cGens mclFiveDataP)[l]! = unpack 275 9 (CO l) :=
  ⟨cs_size, fun _ hl => cs_get hl⟩

theorem cc_co {k : Nat} (hk : k < 5) : Cn 275 9 (CO k) := (co_all k hk).2.1

theorem cb_all : allN 5 (fun k => Nat.beq (pcomp 275 9 (mask 9) (CO k) (GP 1))
      (pcomp 275 9 (mask 9) (GP 1) (CO k))) = true ∧
    Nat.beq (pw 275 9 (GP 1) 5) (pidn 275 9) = true ∧
    bIf(Nat.beq (GP 1) (pidn 275 9), false, true) = true ∧
    Nat.beq (CO 0) (GP 1) = true ∧
    Nat.blt (r32 CHB 0) RE.cnt = true ∧ Nat.beq (RE.T (r32 CHB 0)) (GP 1) = true ∧
    Nat.beq (pcomp 275 9 (mask 9) (GP 1) (RE.G 0)) (pcomp 275 9 (mask 9) (RE.G 0) (GP 1)) = true ∧
    Nat.beq (pcomp 275 9 (mask 9) (GP 1) (RE.G 1)) (pcomp 275 9 (mask 9) (RE.G 1) (GP 1)) = true ∧
    Nat.beq (pcomp 275 9 (mask 9) (TT 0) (GP 1))
      (pcomp 275 9 (mask 9) (pw 275 9 (GP 1) 2) (TT 0)) = true ∧
    allN NE.k (fun i => Nat.blt (r32 CHB (Nat.add i 1)) 5 &&
      Nat.beq (pcomp 275 9 (mask 9) (NE.G i) (GP 1))
        (pcomp 275 9 (mask 9) (pw 275 9 (GP 1) (r32 CHB (Nat.add i 1))) (NE.G i))) = true := by
  have h := k_cb
  unfold cbK at h
  simp only [Bool.and_eq_true] at h
  exact h

theorem xone_all : ∀ k < 452, xOneK k = true := by
  intro k hk
  have sl : ∀ s, s < 4 → xK (113 * s) 113 = true := by
    intro s hs
    interval_cases s
    exacts [k_x0, k_x1, k_x2, k_x3]
  have h := (PK.allN_iff.1 (sl (k / 113) (by omega))) (k % 113) (by omega)
  have e : Nat.add (113 * (k / 113)) (k % 113) = k := by
    change 113 * (k / 113) + k % 113 = k
    omega
  rw [e] at h
  exact h

theorem x_facts {i β : Nat} (hi : i < 113) (hβ : β < 4) :
    XT (4 * i + β) = pcomp 275 9 (mask 9) (REP (i + 1)) (pw 275 9 (TT 0) β) ∧
    permOK 275 9 (mask 9) (275 * 9) (XT (4 * i + β)) (XTI (4 * i + β)) = true ∧
    wordEqK 275 9 (mask 9) (pidn 275 9) (xlK (4 * i + β)) (xliK (4 * i + β)) 6
      (aW[4 * i + β]!) (GP 0) = true ∧
    wordEqK 275 9 (mask 9) (pidn 275 9) (xlK (4 * i + β)) (xliK (4 * i + β)) 6 [1] (GP 1) =
      true := by
  have h := xone_all (4 * i + β) (by omega)
  unfold xOneK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have e1 : Nat.add (Nat.div (4 * i + β) 4) 1 = i + 1 := by
    change (4 * i + β) / 4 + 1 = i + 1
    omega
  have e2 : Nat.mod (4 * i + β) 4 = β := by
    change (4 * i + β) % 4 = β
    omega
  rw [e1, e2] at h1
  exact ⟨Nat.eq_of_beq_eq_true h1, h2, h3, h4⟩

theorem x_eq {i β : Nat} (hi : i < 113) (hβ : β < 4) :
    xT mclFiveDataP i β = unpack 275 9 (XT (4 * i + β)) := by
  have hr := c_rep_perm hC (i := i + 1) (by change i + 1 < 114; omega)
  unfold xT
  rw [c_rep_get hC (i := i + 1) (by change i + 1 < 114; omega), htT]
  change comp 275 (unpack 275 9 (REP (i + 1)))
    (Certificates.FusD2Perm.powT 275 (unpack 275 9 (TT 0)) β) = _
  rw [powT_u hn ct β, (x_facts hi hβ).1]
  exact comp_u hr.1 (pw_canon hn ct β)

theorem x_bind {i β : Nat} (hi : i < 113) (hβ : β < 4) :
    (cGens mclFiveDataP ++ #[xT mclFiveDataP i β]).size = 6 ∧ ∀ l < 6,
      (cGens mclFiveDataP ++ #[xT mclFiveDataP i β])[l]! = unpack 275 9 (xlK (4 * i + β) l) := by
  refine ⟨by simp [cs_size], fun l hl => ?_⟩
  rw [getElem!_pos _ l (by simp [cs_size]; omega)]
  unfold xlK
  rw [PK.nIf_eq]
  by_cases h : l < 5
  · rw [Array.getElem_append_left (by rw [cs_size]; exact h),
      ← getElem!_pos _ l (by rw [cs_size]; exact h), cs_get h, if_pos (Nat.blt_eq.mpr h)]
  · have hl' : l = 5 := by omega
    subst hl'
    rw [if_neg (by simp [Nat.blt_eq]), Array.getElem_append_right (by rw [cs_size])]
    simp [cs_size, x_eq hi hβ]

theorem x_perm {i β : Nat} (hi : i < 113) (hβ : β < 4) :
    ∀ l < 6, permOK 275 9 (mask 9) (275 * 9) (xlK (4 * i + β) l) (xliK (4 * i + β) l) = true := by
  intro l hl
  unfold xlK xliK
  rw [PK.nIf_eq, PK.nIf_eq]
  by_cases h : l < 5
  · rw [if_pos (Nat.blt_eq.mpr h), if_pos (Nat.blt_eq.mpr h)]
    exact (co_all l h).2.2
  · rw [if_neg (by simp [Nat.blt_eq]; omega), if_neg (by simp [Nat.blt_eq]; omega)]
    exact (x_facts hi hβ).2.1

theorem case_ok {i β : Nat} (hi : i < 113) (hβ : β < 4) :
    (invsOK 275 #[xT mclFiveDataP i β] #[invTab 275 (xT mclFiveDataP i β)] &&
      Certificates.OverD2Perm.genOK mclFiveDataP
        (cGens mclFiveDataP ++ #[xT mclFiveDataP i β])
        (cGensI mclFiveDataP ++ #[invTab 275 (xT mclFiveDataP i β)])
        [aW[4 * i + β]!, [1]]) = true := by
  obtain ⟨-, hp, hw0, hw1⟩ := x_facts hi hβ
  rw [Bool.and_eq_true]
  constructor
  · have e : #[invTab 275 (xT mclFiveDataP i β)] = #[xT mclFiveDataP i β].map (invTab 275) := by
      simp
    rw [e]
    exact invsOK_of (k := 1) (PS := fun _ => XT (4 * i + β)) (PSI := fun _ => XTI (4 * i + β))
      ⟨rfl, fun l hl => by
        have : l = 0 := by omega
        subst this
        simp [x_eq hi hβ]⟩ fun _ _ => hp
  · have e : cGensI mclFiveDataP ++ #[invTab 275 (xT mclFiveDataP i β)] =
        (cGens mclFiveDataP ++ #[xT mclFiveDataP i β]).map (invTab mclFiveDataP.n) := by
      simp [cGensI, Array.map_append, hD]
    rw [e]
    unfold Certificates.OverD2Perm.genOK
    simp only [Bool.and_eq_true, beq_iff_eq]
    refine ⟨by rw [hC.hGs]; rfl, allBelow_iff'.2 fun j hj => ?_⟩
    have hj' : j < KH.kG := by rw [← hC.hGs]; exact hj
    have hpa : allN 6 (fun l => permOK 275 9 (mask 9) (275 * 9) (xlK (4 * i + β) l)
        (xliK (4 * i + β) l)) = true := PK.allN_iff.2 (x_perm hi hβ)
    have hj2 : j < 2 := hj'
    interval_cases j
    · exact c_word_eq hC hj' (x_bind hi hβ) hpa hw0
    · exact c_word_eq hC hj' (x_bind hi hβ) hpa hw1

theorem mcl_centOver : checkCentOver mclFiveDataP = true := by
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10⟩ := cb_all
  have hrE := (h_rEnum_eq hypsH).1
  unfold checkCentOver
  simp only [Bool.and_eq_true, and_assoc, hD]
  refine ⟨c_checkInv_of hC, c_invsN hC, invsOK_of cs_bind fun l hl => (co_all l hl).2.2,
    by rw [cs_size]; rfl, ?_, ?_, ?_, ?_, checkHR_of hypsH, ?_, ?_, ?_, ?_,
    by rw [k_aw]; exact beq_self_eq_true _, by rw [hC.hGs]; rfl, ?_⟩
  · rw [cs_size, allBelow_iff']
    intro k hk
    rw [cs_get hk, hb, comp_u (cc_co hk) cb, comp_u cb (cc_co hk), eq_u (cc (cc_co hk) cb)
      (cc cb (cc_co hk))]
    exact (PK.allN_iff.1 hc1) k hk
  · rw [hb]
    change (Certificates.FusD2Perm.powT 275 (unpack 275 9 (GP 1)) 5 == idTab 275) = true
    rw [powT_u hn cb 5, id_u hn, eq_u (pw_canon hn cb 5) (pidn_canon hn)]
    exact hc2
  · rw [hb]
    change (!(unpack 275 9 (GP 1) == idTab 275)) = true
    have h3 : Nat.beq (GP 1) (pidn 275 9) = false := bnot_e (c := Nat.beq (GP 1) (pidn 275 9)) hc3
    rw [id_u hn, eq_u cb (pidn_canon hn), h3]
    rfl
  · rw [cs_get (by decide), hb, eq_u (cc_co (by decide)) cb]
    exact hc4
  · rw [hrE, hb]
    exact (h_foundR hypsH cb).2 ⟨r32 CHB 0, Nat.blt_eq.mp hc5, Nat.eq_of_beq_eq_true hc6⟩
  · have hr0 : Cn 275 9 (RE.G 0) := h_rg_canon hypsH (j := 0) (by decide)
    have hr1 : Cn 275 9 (RE.G 1) := h_rg_canon hypsH (j := 1) (by decide)
    unfold commutesUV
    rw [h_rg_get hypsH (j := 0) (by decide), h_rg_get hypsH (j := 1) (by decide), hb]
    change ((comp 275 (unpack 275 9 (GP 1)) (unpack 275 9 (RE.G 0)) ==
        comp 275 (unpack 275 9 (RE.G 0)) (unpack 275 9 (GP 1))) &&
      (comp 275 (unpack 275 9 (GP 1)) (unpack 275 9 (RE.G 1)) ==
        comp 275 (unpack 275 9 (RE.G 1)) (unpack 275 9 (GP 1)))) = true
    rw [comp_u cb hr0, comp_u hr0 cb, comp_u cb hr1, comp_u hr1 cb, eq_u (cc cb hr0) (cc hr0 cb),
      eq_u (cc cb hr1) (cc hr1 cb), hc7, hc8]
    rfl
  · rw [htT, hb]
    change (comp 275 (unpack 275 9 (TT 0)) (unpack 275 9 (GP 1)) ==
      comp 275 (Certificates.FusD2Perm.powT 275 (unpack 275 9 (GP 1)) 2)
        (unpack 275 9 (TT 0))) = true
    rw [powT_u hn cb 2, comp_u ct cb, comp_u (pw_canon hn cb 2) ct,
      eq_u (cc ct cb) (cc (pw_canon hn cb 2) ct)]
    exact hc9
  · rw [ng_size, allBelow_iff']
    intro i hi
    have hi' : i < NE.k := by rw [nk]; exact hi
    have h := (PK.allN_iff.1 hc10) i hi'
    rw [Bool.and_eq_true] at h
    have cg : Cn 275 9 (NE.G i) := (hC.hNG i hi').2
    rw [anyBelow_iff]
    refine ⟨r32 CHB (Nat.add i 1), Nat.blt_eq.mp h.1, ?_⟩
    rw [c_ng_get hC hi', hb]
    change (comp 275 (unpack 275 9 (NE.G i)) (unpack 275 9 (GP 1)) ==
      comp 275 (Certificates.FusD2Perm.powT 275 (unpack 275 9 (GP 1)) (r32 CHB (Nat.add i 1)))
        (unpack 275 9 (NE.G i))) = true
    rw [powT_u hn cb, comp_u cg cb, comp_u (pw_canon hn cb _) cg,
      eq_u (cc cg cb) (cc (pw_canon hn cb _) cg)]
    exact h.2
  · have hr : mclFiveDataP.repW.length = 113 := by decide +kernel
    rw [hr, allBelow_iff']
    intro i hi
    rw [allBelow_iff']
    intro β hβ
    exact case_ok hi hβ

end CertificateChecks.KernelMaxD2.McLP

end
