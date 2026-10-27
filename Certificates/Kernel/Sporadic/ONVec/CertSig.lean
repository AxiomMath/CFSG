module

public import Certificates.Kernel.Sporadic.ONVec.CertForm

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONVec

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.F3.Native CFSG.Sporadic.Fi23.Native
open CFSG.Sporadic.ON.Native CFSG.ONSchreier.Native CFSG.Sporadic.Th.Native
open CertificateChecks.KernelSpor

variable (sigAll : ∀ s < 1023, sigS s = true) (ssortAll : ∀ s < 1023, ssortS s = true)

theorem band {a b : Bool} (ha : a = true) (hb : b = true) : (a && b) = true := by
  rw [ha, hb]
  rfl

theorem bl_eq : BL = CFSG.ONSchreier.Data.baseList := rfl

theorem base_lt : ∀ k < 29, CFSG.ONSchreier.Data.baseList[k]! < 245520 := by decide

theorem sigRows_eq : sigRows (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits))
    (rowsOf 154 CFSG.ONSchreier.Data.formPayload) CFSG.ONSchreier.Data.baseList = rowsV SR := by
  refine arr_ext' (by unfold sigRows; exact Array.size_ofFn) (rowsV_size _) fun k hk => ?_
  rw [rowsV_get hk]
  unfold sigRows
  rw [getElem!_ofFn' hk]
  by_cases hb : k < 29
  · have hlen : CFSG.ONSchreier.Data.baseList.length = 29 := rfl
    rw [if_pos (by rw [hlen]; exact hb), key_get (base_lt k hb),
      toV_wOfK (canon_key _ (base_lt k hb)), form_eq, comb_rowsV cm_list cm_canon]
    unfold SR
    rw [Nat.blt_eq.mpr hb]
    have e : CFSG.ONSchreier.Data.baseList[k]! = at0 BL k := by
      rw [bl_eq]
      unfold at0
      rw [List.getD_eq_getElem?_getD, List.getElem!_eq_getElem?_getD]
      rfl
    rw [e]
  · have hlen : CFSG.ONSchreier.Data.baseList.length = 29 := rfl
    rw [if_neg (by rw [hlen]; exact hb)]
    unfold SR
    have : Nat.blt k 29 = false := by
      cases e : Nat.blt k 29
      · rfl
      · exact absurd (Nat.blt_eq.mp e) hb
    rw [this]
    change V.zero = vOf 0
    apply V.ext_bits <;> intro t <;> simp [vOf, vP, vM, V.zero]

theorem sig_canon : ∀ j < 154, canon (ONS.CA j) = true := (tposK_spec sigK).2.1

theorem hST : ((transpose 154 (sigRows (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits))
      (rowsOf 154 CFSG.ONSchreier.Data.formPayload) CFSG.ONSchreier.Data.baseList)).map ofV).size =
      154 ∧ ONS.LA.length = 154 ∧
    ∀ j < 154, ((transpose 154 (sigRows (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits))
      (rowsOf 154 CFSG.ONSchreier.Data.formPayload) CFSG.ONSchreier.Data.baseList)).map ofV)[j]! =
        wOfK (ONS.LA.getD j 0) := by
  rw [sigRows_eq, transpose_rowsV sigK]
  refine ⟨by rw [Array.size_map, rowsV_size], ?_, fun j hj => ?_⟩
  · have h := lensK
    simp only [bAnd_iff] at h
    exact Nat.eq_of_beq_eq_true h.2.2.2.2.2.2
  · rw [getElem!_map' (by rw [rowsV_size]; exact hj), rowsV_get hj,
      Nat.eq_of_beq_eq_true (allN_spec sigLK j hj)]
    rfl

theorem sigLA_canon : ∀ j < 154, canon (ONS.LA.getD j 0) = true := fun j hj => by
  rw [Nat.eq_of_beq_eq_true (allN_spec sigLK j hj)]
  exact sig_canon j hj

include sigAll in
theorem sigs_eq : sigsOf (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits))
    ((transpose 154 (sigRows (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits))
      (rowsOf 154 CFSG.ONSchreier.Data.formPayload) CFSG.ONSchreier.Data.baseList)).map ofV) =
    Array.ofFn (n := 245520) fun i => wOfK (key ONS.K i.val) := by
  unfold sigsOf
  refine arr_ext' (n := 245520) Array.size_ofFn Array.size_ofFn fun i hi => ?_
  rw [getElem!_ofFn' hi, getElem!_ofFn' hi]
  dsimp only
  rw [key_get hi, mv_sound hST sigLA_canon (canon_key i hi),
    ← (sigAt_spec (ON.pt_of sigAll (fun _ => rfl) i hi)).2]

include sigAll ssortAll in
theorem sig_ok : sigOK (sigsOf (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits))
      ((transpose 154 (sigRows (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits))
        (rowsOf 154 CFSG.ONSchreier.Data.formPayload) CFSG.ONSchreier.Data.baseList)).map ofV))
    (posOf (indexOf (sigsOf (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits))
      ((transpose 154 (sigRows (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits))
        (rowsOf 154 CFSG.ONSchreier.Data.formPayload) CFSG.ONSchreier.Data.baseList)).map ofV)))
      nPts) = true := by
  have hc : ∀ i < 245520, canon (key ONS.K i) = true := fun i hi =>
    (sigAt_spec (ON.pt_of sigAll (fun _ => rfl) i hi)).1
  have hs : ∀ i < 245520, sortAt ONS.K ONS.SO ONS.SOI 245520 i = true :=
    ON.pt_of ssortAll fun _ => rfl
  have h : sigOK (Array.ofFn (n := 245520) fun i => wOfK (key ONS.K i.val))
      (posOf (indexOf (Array.ofFn (n := 245520) fun i => wOfK (key ONS.K i.val))) nPts) = true := by
    unfold sigOK posOf
    refine band (beq_iff_eq.mpr Array.size_ofFn) ?_
    unfold CFSG.Sporadic.Th.Native.allIn
    rw [Nat.all_eq_finRange_all, List.all_eq_true]
    intro ⟨k, hk⟩ _
    have hk' : k < 245520 := Nat.lt_of_lt_of_le hk (Nat.sub_le _ _)
    have hi : 0 + k < 245520 := by omega
    have hidx := index_sound rfl hc hs (0 + k) hi (nPts ())
    refine band ?_ (beq_iff_eq.mpr hidx)
    rw [getElem!_ofFn' hi]
    exact canon_sound (hc _ hi)
  rw [← sigs_eq sigAll] at h
  exact h

end CertificateChecks.KernelSpor.ONVec

end
