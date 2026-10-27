module

public import Certificates.Kernel.Sporadic.J3C.GlueP

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelSpor.J3CGlue

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.PC CFSG.KS.CentReg CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.J3Data CFSG.Monster.B CFSG.Monster.B.Co2.Native CFSG.Sporadic.J3.Native
  CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen CertificateChecks.KernelSpor
  CertificateChecks.KernelSpor.J3K CertificateChecks.KernelSpor.J3C
  CertificateChecks.KernelSchreierFam

@[expose] noncomputable def κ (h : Nat) : Equiv.Perm (Fin 20520) := Co2.permOfArr 20520 kStrong[h]!

@[expose] noncomputable def σK (l : Nat) : Equiv.Perm (Fin 20520) :=
  if l = 0 then κ 0 else if l = 1 then (κ 0)⁻¹ else if l = 2 then κ 1 else (κ 1)⁻¹

theorem σK0 : σK 0 = κ 0 := by
  unfold σK
  rw [if_pos rfl]

theorem σK1 : σK 1 = (κ 0)⁻¹ := by
  unfold σK
  rw [if_neg (by decide), if_pos rfl]

theorem σK2 : σK 2 = κ 1 := by
  unfold σK
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]

theorem σK3 : σK 3 = (κ 1)⁻¹ := by
  unfold σK
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide)]

theorem kArr : ∀ h < 2, kStrong[h]! = Array.ofFn (n := 20520) fun x => KLr (2 * h) x.val := by
  intro h hh
  rw [J3CqBind.kk_bind h hh]
  interval_cases h
  · change CFSG.KS.Raw.unpack 20520 15 J3Cq.K0 = _
    rw [Nat.eq_of_beq_eq_true kl0]
    exact CFSG.KC.HexaStabK.unpack_pmk (by norm_num)
      fun x hx => lt_trans (invK_spec klInv (j := 0) (by norm_num) hx).1 (by norm_num)
  · change CFSG.KS.Raw.unpack 20520 15 J3Cq.K1 = _
    rw [Nat.eq_of_beq_eq_true kl2]
    exact CFSG.KC.HexaStabK.unpack_pmk (by norm_num)
      fun x hx => lt_trans (invK_spec klInv (j := 1) (by norm_num) hx).1 (by norm_num)

theorem kGet {h x : Nat} (hh : h < 2) (hx : x < 20520) : (kStrong[h]!)[x]! = KLr (2 * h) x := by
  rw [kArr h hh, Co2.getElem!_ofFn_nat _ hx]

theorem klPair {h x : Nat} (hh : h < 2) (hx : x < 20520) :
    KLr (2 * h) x < 20520 ∧ KLr (2 * h + 1) x < 20520 ∧ KLr (2 * h + 1) (KLr (2 * h) x) = x :=
  invK_spec klInv (j := h) (by omega) hx

theorem isInvK : ∀ h < 2, isInvA 20520 kStrong[h]! kInv[h]! = true := by
  intro h hh
  have e : kInv[h]! = invCand 20520 kStrong[h]! :=
    J3CqBind.map_get _ _ (by rw [J3CqBind.kStrong_size]; exact hh)
  rw [e]
  refine CFSG.KC.Co2Mem.isInvA_invCand (fun i hi => ?_) (fun i j hi hj hij => ?_)
  · rw [kGet hh hi]
    exact (klPair hh hi).1
  · rw [kGet hh hi, kGet hh hj] at hij
    rw [← (klPair hh hi).2.2, ← (klPair hh hj).2.2, hij]

theorem repK (h : Nat) (hh : h < 2) :
    Co2.Rep 20520 kStrong[h]! (κ h) ∧ Co2.Rep 20520 kInv[h]! (κ h)⁻¹ :=
  Co2.rep_permOfArr (isInvK h hh)

theorem actK : ∀ h < 2, ∀ x < 20520, actN (κ h) x = KLr (2 * h) x := fun h hh x hx => by
  rw [actN_of_lt _ hx, ← (repK h hh).1.apply hx, kGet hh hx]

theorem actKi : ∀ h < 2, ∀ x < 20520, actN (κ h)⁻¹ x = KLr (2 * h + 1) x := fun h hh =>
  invAct (f := KLr (2 * h)) (fi := KLr (2 * h + 1)) (actK h hh) fun _ hx =>
    ⟨(klPair hh hx).2.1, (klPair hh hx).2.2⟩

theorem actK0 : ∀ x < 20520, actN (κ 0) x = KLr 0 x := fun x hx => by
  have h := actK 0 (by norm_num) x hx
  rwa [Nat.mul_zero] at h

theorem actK1 : ∀ x < 20520, actN (κ 1) x = KLr 2 x := fun x hx => by
  have h := actK 1 (by norm_num) x hx
  rwa [Nat.mul_one] at h

theorem actKi0 : ∀ x < 20520, actN (κ 0)⁻¹ x = KLr 1 x := fun x hx => by
  have h := actKi 0 (by norm_num) x hx
  rwa [Nat.mul_zero, Nat.zero_add] at h

theorem actKi1 : ∀ x < 20520, actN (κ 1)⁻¹ x = KLr 3 x := fun x hx => by
  have h := actKi 1 (by norm_num) x hx
  have e : 2 * 1 + 1 = 3 := rfl
  rwa [e] at h

theorem actSK : ∀ l < 4, ∀ x < 20520, actN (σK l) x = KLr l x := by
  intro l hl x hx
  interval_cases l
  · rw [σK0]
    exact actK0 x hx
  · rw [σK1]
    exact actKi0 x hx
  · rw [σK2]
    exact actK1 x hx
  · rw [σK3]
    exact actKi1 x hx

theorem actSKi : ∀ l < 4, ∀ x < 20520, actN (σK l)⁻¹ x = KLr (Nat.xor l 1) x := by
  intro l hl x hx
  interval_cases l
  · have e : Nat.xor 0 1 = 1 := rfl
    rw [σK0, e]
    exact actKi0 x hx
  · have e : Nat.xor 1 1 = 0 := rfl
    rw [σK1, e, inv_inv]
    exact actK0 x hx
  · have e : Nat.xor 2 1 = 3 := rfl
    rw [σK2, e]
    exact actKi1 x hx
  · have e : Nat.xor 3 1 = 2 := rfl
    rw [σK3, e, inv_inv]
    exact actK1 x hx

theorem κK (h : Nat) (hh : h < 2) : κ h ∈ J3Groups.K := Subgroup.subset_closure ⟨h, hh, rfl⟩

theorem σKK : ∀ l < 4, σK l ∈ J3Groups.K := by
  intro l hl
  interval_cases l
  · rw [σK0]
    exact κK 0 (by norm_num)
  · rw [σK1]
    exact J3Groups.K.inv_mem (κK 0 (by norm_num))
  · rw [σK2]
    exact κK 1 (by norm_num)
  · rw [σK3]
    exact J3Groups.K.inv_mem (κK 1 (by norm_num))

theorem kRange : J3Groups.K ≤ Subgroup.closure (Set.range fun t : Fin 4 => σK t.val) := by
  unfold J3Groups.K J3Groups.gen
  rw [Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  interval_cases i
  · exact Subgroup.subset_closure ⟨0, σK0⟩
  · exact Subgroup.subset_closure ⟨2, σK2⟩

theorem repLetter : ∀ l : Int, l ≠ 0 → l.natAbs ≤ 2 →
    Co2.Rep 20520 (letterA kStrong kInv l) (σK (sgnL l)) := by
  intro l h0 h2
  rcases (by omega : l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2) with rfl | rfl | rfl | rfl
  · have e : sgnL 1 = 0 := rfl
    rw [e, σK0]
    exact (repK 0 (by norm_num)).1
  · have e : sgnL (-1) = 1 := rfl
    rw [e, σK1]
    exact (repK 0 (by norm_num)).2
  · have e : sgnL 2 = 2 := rfl
    rw [e, σK2]
    exact (repK 1 (by norm_num)).1
  · have e : sgnL (-2) = 3 := rfl
    rw [e, σK3]
    exact (repK 1 (by norm_num)).2

theorem repWP : ∀ w : List Int, lettersOK 2 w = true →
    Co2.Rep 20520 (wordA 20520 kStrong kInv w) (wordP σK w)
  | [], _ => by
    have e : wordP σK [] = 1 := by
      unfold wordP
      rw [List.map_nil, List.prod_nil]
    rw [e]
    simpa [wordA] using (Co2.rep_idA (n := 20520))
  | l :: w, hw => by
    simp only [lettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hw
    obtain ⟨⟨hl0, hl2⟩, hw⟩ := hw
    have hw' : lettersOK 2 w = true := by simpa [lettersOK, List.all_eq_true] using hw
    have e1 : wordA 20520 kStrong kInv (l :: w) =
        compA 20520 (letterA kStrong kInv l) (wordA 20520 kStrong kInv w) := rfl
    have e2 : wordP σK (l :: w) = σK (sgnL l) * wordP σK w := by
      unfold wordP
      rw [List.map_cons, List.prod_cons]
    rw [e1, e2]
    exact Co2.rep_compA (repLetter l hl0 hl2) (repWP w hw')

theorem sgnLt : ∀ w : List Int, lettersOK 2 w = true → ∀ z ∈ w, sgnL z < 4 := by
  intro w hw z hz
  unfold lettersOK at hw
  have := List.all_eq_true.1 hw z hz
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at this
  rcases (by omega : z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2) with rfl | rfl | rfl | rfl <;> decide

end CertificateChecks.KernelSpor.J3CGlue

end
