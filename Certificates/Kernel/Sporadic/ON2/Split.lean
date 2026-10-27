module

public import Certificates.Kernel.Sporadic.ON2.Final
public import Certificates.Kernel.Sporadic.ON2.Basis
public import Certificates.Kernel.Sporadic.ON2.Assemble
public import Certificates.Kernel.Sporadic.ON2.Neg
public import CFSG.Certificates.Kernel.Spor.ONSplitSound
public import Certificates.Data.Kernel.ON.BasisLit
public import CFSG.Certificates.Kernel.Spor.ONNegSound
public import CFSG.Certificates.Kernel.Spor.RawSlSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.NormNum
public import CFSG.Certificates.Kernel.Spor.ONMvSound
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.Perm.Basic
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON2

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.F3.Native CFSG.Sporadic.Fi23.Native
open CFSG.Sporadic.ON.Native CFSG.Sporadic.ON.Kernel CFSG.ONSchreier.Native CFSG.Sporadic.Th.Native
open CertificateChecks.KernelSpor.ON (cols_of canon_of list_eq strictB_eq' pt_of)

theorem hcA : (colsA ()).size = 154 ∧ ONW.LA.length = 154 ∧
    ∀ j < 154, (colsA ())[j]! = wOfK (ONW.LA.getD j 0) := by
  unfold colsA rowsA
  exact cols_of ONSeedA.eq colsAK2 (list_eq ONW.LA ONW.CA (allN_spec listA2)) rfl

theorem hcB : (colsB ()).size = 154 ∧ ONW.LB.length = 154 ∧
    ∀ j < 154, (colsB ())[j]! = wOfK (ONW.LB.getD j 0) := by
  unfold colsB rowsB
  exact cols_of ONSeedB.eq colsBK2 (list_eq ONW.LB ONW.CB (allN_spec listB2)) rfl

theorem hroot : rootW () = wOfK (key ONW.K 0) := by
  rw [← digitsK_sound rootK2, ← ONRootW.eq]
  rfl

theorem keys2 : (orbitData ()).keys = Array.ofFn (n := 245520) fun i => wOfK (key ONW.K i.val) := by
  unfold orbitData
  exact bfsK_keys (SL := 240) (NS := 1023) (SO := ONW.SO) (SOI := ONW.SOI) (NX := ONW.NX) (K := ONW.K)
    hcA hcB (canon_of colsAK2 (list_eq ONW.LA ONW.CA (allN_spec listA2)))
    (canon_of colsBK2 (list_eq ONW.LB ONW.CB (allN_spec listB2))) hroot (by norm_num)
    (pt_of mvAll fun _ => rfl) (by norm_num) (Nat.eq_of_beq_eq_true nx0) (Nat.eq_of_beq_eq_true nx1)
    ordAll (pt_of sortAll fun _ => rfl)

theorem canon2 : ∀ h < 245520, canon (key ONW.K h) = true := by
  intro h hh
  have e := pt_of mvAll (fun _ => rfl) h hh
  unfold mvAt at e
  simp only [strictB_eq'] at e
  exact ((bAnd_iff _ _).1 e).1

theorem key_get {i : Nat} (hi : i < 245520) : (orbitData ()).keys[i]! = wOfK (key ONW.K i) := by
  rw [keys2, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem getD_of_lt {α : Type} {l : List α} {i : Nat} {d : α} (h : i < l.length) : l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem lenX : List.length XL = 154 := Nat.eq_of_beq_eq_true ((bAnd_iff (Nat.beq (List.length XL) 154)
  (Nat.beq (List.length RbL) 154)).1 lensOK).1

theorem lenR : List.length RbL = 154 := Nat.eq_of_beq_eq_true ((bAnd_iff (Nat.beq (List.length XL) 154)
  (Nat.beq (List.length RbL) 154)).1 lensOK).2

theorem matrix_ok : matrixChecks () = true := by
  unfold matrixChecks rowsA rowsB
  rw [ONSeedA.eq, ONSeedB.eq]
  have h := matrixK_sound colsAK2 colsBK2
    ⟨hcA.2.1, list_eq ONW.LA ONW.CA (allN_spec listA2)⟩ ⟨hcB.2.1, list_eq ONW.LB ONW.CB (allN_spec listB2)⟩
    (fun j hj => Nat.eq_of_beq_eq_true (allN_spec matA j hj))
    (fun j hj => Nat.eq_of_beq_eq_true (allN_spec matB j hj))
  rw [Bool.and_eq_true]
  exact h

theorem orbit_ok : orbitOK nPts (colsA ()) (colsB ()) (orbitData ()) posOrb 3 = true := by
  unfold posOrb orbitData
  exact orbitOK_sound (SL := 240) (NS := 1023) (SO := ONW.SO) (SOI := ONW.SOI) (NX := ONW.NX) (K := ONW.K)
    hcA hcB (canon_of colsAK2 (list_eq ONW.LA ONW.CA (allN_spec listA2)))
    (canon_of colsBK2 (list_eq ONW.LB ONW.CB (allN_spec listB2))) hroot (by norm_num)
    (pt_of mvAll fun _ => rfl) (by norm_num) (Nat.eq_of_beq_eq_true nx0) (Nat.eq_of_beq_eq_true nx1)
    ordAll (pt_of sortAll fun _ => rfl) 3

theorem neg_ok : negOK nPts (orbitData ()) (negTable (orbitData ()) posOrb) = true := by
  have hidx := index_sound keys2 canon2 (pt_of sortAll fun _ => rfl)
  unfold negOK
  rw [CFSG.KS.TW.allIn_iff]
  intro i hi
  have e := pt_of negAll (fun _ => rfl) i hi
  unfold negAt at e
  rw [strictB_eq'] at e
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 e
  obtain ⟨h3, -⟩ := (bAnd_iff _ _).1 h2
  have hj : tab ONW2.NEG i < 245520 := Nat.blt_eq ▸ h1
  have hk : key ONW.K (tab ONW2.NEG i) = vneg (key ONW.K i) := Nat.eq_of_beq_eq_true h3
  have hneg : (orbitData ()).keys[i]!.neg = (orbitData ()).keys[tab ONW2.NEG i]! := by
    rw [key_get hi, key_get hj, wOfK_vneg (canon2 i hi), hk]
  have hap : ap (negTable (orbitData ()) posOrb) i = tab ONW2.NEG i := by
    unfold ap negTable posOrb
    rw [getElem!_pos _ i (by simp [keys2]; omega), Array.getElem_map, ← getElem!_pos _ i (by simp [keys2]; omega),
      hneg, hidx _ hj, UInt32.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  rw [hap, ← hneg]
  simp [hj]

theorem X_get {k : Nat} (hk : k < 154) : basisXLit[k]! = wOfK (XL.getD k 0) := by
  have h := allN_spec basisOK k hk
  obtain ⟨-, hp, hm, -⟩ := (by simpa only [bAnd_iff] using h :
    canon (List.getD XL k 0) = true ∧ Nat.blt (List.getD basisXPairs k (0, 0)).1 (Nat.pow 2 154) = true ∧
      Nat.blt (List.getD basisXPairs k (0, 0)).2 (Nat.pow 2 154) = true ∧
      Nat.beq (mv RbL (List.getD XL k 0)) (vmk (Nat.pow 2 k) 0) = true)
  have hp' : (List.getD basisXPairs k (0, 0)).1 < 2 ^ 256 :=
    lt_trans (Nat.blt_eq ▸ hp) (by norm_num)
  have hm' : (List.getD basisXPairs k (0, 0)).2 < 2 ^ 256 :=
    lt_trans (Nat.blt_eq ▸ hm) (by norm_num)
  have hlen : basisXPairs.length = 154 := rfl
  unfold basisXLit XL
  rw [getElem!_pos _ k (by simp [hlen, hk]), List.getElem_toArray, List.getElem_map, getD_of_lt (by simp [hlen, hk]),
    List.getElem_map, wOfK_vmk (by rw [getD_of_lt (by omega)] at hp'; exact hp')
      (by rw [getD_of_lt (by omega)] at hm'; exact hm')]

theorem X_canon {k : Nat} (hk : k < 154) : canon (XL.getD k 0) = true := by
  have h := allN_spec basisOK k hk
  exact ((bAnd_iff _ _).1 h).1

theorem hX : basisXLit.size = 154 ∧ XL.length = 154 ∧ ∀ k < 154, basisXLit[k]! = wOfK (XL.getD k 0) :=
  ⟨rfl, lenX, fun _ hk => X_get hk⟩

theorem cq_eq {t : Nat} (_ : t < 154) : cq t = chainQ[t]! := rfl

theorem Rb_get {t : Nat} (ht : t < 154) : (basisRows (orbitData ()))[t]! = wOfK (RbL.getD t 0) := by
  unfold basisRows RbL
  rw [getElem!_pos _ t (by simpa [chainQ_size] using ht), Array.getElem_map,
    ← getElem!_pos chainQ t (by simpa [chainQ_size] using ht), key_get (by rw [← cq_eq ht]; exact cq_lt ht),
    getD_of_lt (by simp; omega), List.getElem_map, List.getElem_range, cq_eq ht]

theorem hRb : (basisRows (orbitData ())).size = 154 ∧ RbL.length = 154 ∧
    ∀ t < 154, (basisRows (orbitData ()))[t]! = wOfK (RbL.getD t 0) :=
  ⟨by simp [basisRows, chainQ_size], lenR,
    fun t ht => Rb_get ht⟩

theorem Rb_canon {t : Nat} (ht : t < 154) : canon (RbL.getD t 0) = true := by
  unfold RbL
  rw [getD_of_lt (by simp; omega), List.getElem_map, List.getElem_range]
  exact canon2 _ (cq_lt ht)

theorem basis_ok : basisChecks (basisRows (orbitData ())) basisXLit = true := by
  unfold basisChecks
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨⟨⟨chainQ_size, ?_⟩, hX.1⟩, ?_⟩, ?_⟩
  · rw [Array.all_eq_true]
    intro t ht
    rw [← getElem!_pos chainQ t ht, ← cq_eq (by rwa [chainQ_size] at ht)]
    exact decide_eq_true (cq_lt (by rwa [chainQ_size] at ht))
  · rw [Array.all_eq_true]
    intro k hk
    have hk' : k < 154 := by rwa [hX.1] at hk
    rw [← getElem!_pos basisXLit k hk, X_get hk']
    have := canon_sound (X_canon hk')
    unfold canon154 at this
    simp only [Bool.and_eq_true] at this
    exact this.1.1.1.1
  · apply Array.ext (by simp [mulW, idW, idM, hX.1])
    intro k h1 h2
    have hk : k < 154 := by simpa [idW, idM] using h2
    have h := allN_spec basisOK k hk
    obtain ⟨-, -, -, h4⟩ := (by simpa only [bAnd_iff] using h :
      canon (List.getD XL k 0) = true ∧ Nat.blt (List.getD basisXPairs k (0, 0)).1 (Nat.pow 2 154) = true ∧
        Nat.blt (List.getD basisXPairs k (0, 0)).2 (Nat.pow 2 154) = true ∧
        Nat.beq (mv RbL (List.getD XL k 0)) (vmk (Nat.pow 2 k) 0) = true)
    simp only [mulW, idW, idM, Array.getElem_map, Array.getElem_ofFn]
    rw [← getElem!_pos basisXLit k (by rw [hX.1]; exact hk), X_get hk]
    change mulVecT (basisRows (orbitData ())) (wOfK (XL.getD k 0)) = _
    have hp : Nat.pow 2 k < 2 ^ 256 := Nat.pow_lt_pow_right (by norm_num) (by omega)
    rw [mv_sound hRb (fun _ ht => Rb_canon ht) (X_canon hk), Nat.eq_of_beq_eq_true h4,
      ← wOfK_vmk hp (by norm_num), Nat.shiftLeft_eq, Nat.one_mul]
    rfl

theorem coefs_eq {c : Nat} (hc : c < 245520) :
    coefs basisXLit (orbitData ()).keys[c]! = wOfK (CO c) := by
  unfold coefs CO
  rw [key_get hc]
  exact mv_sound hX (fun _ hk => X_canon hk) (canon2 c hc)

theorem support_ok : supportChecks (orbitData ()) (basisRows (orbitData ())) basisXLit = true := by
  have hv : ∀ s < 7, checkVecs[s]! < 245520 ∧ canon (CO checkVecs[s]!) = true ∧
      mv RbL (CO checkVecs[s]!) = key ONW.K checkVecs[s]! ∧
      bIf(bit (vP (CO checkVecs[s]!)) 0, true, bit (vM (CO checkVecs[s]!)) 0) = true := by
    intro s hs
    have h := allN_spec supOK s hs
    rw [strictB_eq'] at h
    obtain ⟨a, b, c, d⟩ := (by simpa only [bAnd_iff] using h :
      Nat.blt checkVecs[s]! 245520 = true ∧ canon (CO checkVecs[s]!) = true ∧
      Nat.beq (mv RbL (CO checkVecs[s]!)) (key ONW.K checkVecs[s]!) = true ∧
      bIf(bit (vP (CO checkVecs[s]!)) 0, true, bit (vM (CO checkVecs[s]!)) 0) = true)
    exact ⟨Nat.blt_eq ▸ a, b, Nat.eq_of_beq_eq_true c, d⟩
  have hsz : checkVecs.size = 7 := rfl
  unfold supportChecks
  simp only [Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [Array.all_eq_true]
    intro s hs
    rw [← getElem!_pos checkVecs s hs]
    exact decide_eq_true (hv s (by rwa [hsz] at hs)).1
  · rw [Array.all_eq_true]
    intro s hs
    have hs7 : s < 7 := by rwa [hsz] at hs
    obtain ⟨h1, h2, h3, h4⟩ := hv s hs7
    rw [← getElem!_pos checkVecs s hs, coefs_eq h1]
    have e : combW 154 (basisRows (orbitData ())) (wOfK (CO checkVecs[s]!)) = (orbitData ()).keys[checkVecs[s]!]! := by
      change mulVecT (basisRows (orbitData ())) (wOfK (CO checkVecs[s]!)) = _
      rw [mv_sound hRb (fun _ ht => Rb_canon ht) h2, h3, key_get h1]
    rw [e, (bits_sound h2 (by norm_num)).1, (bits_sound h2 (by norm_num)).2]
    simp only [decide_true, Bool.true_and]
    revert h4
    cases bit (vP (CO checkVecs[s]!)) 0 <;> cases bit (vM (CO checkVecs[s]!)) 0 <;> decide
  · rw [CFSG.KS.TW.allIn_iff]
    intro t ht
    have h := allN_spec supCover t ht
    rw [Array.any_eq_true]
    by_contra hn
    simp only [not_exists, Bool.not_eq_true] at hn
    have hall : allN 7 (fun s => Bool.not (bIf(bit (vP (CO (checkVecs[s]!))) t, true,
        bit (vM (CO (checkVecs[s]!))) t))) = true := by
      apply CFSG.KS.Raw.allN_of_forall
      intro s hs
      have := hn s (by rw [hsz]; exact hs)
      rw [← getElem!_pos checkVecs s (by rw [hsz]; exact hs), coefs_eq (hv s hs).1,
        (bits_sound (hv s hs).2.1 ht).1, (bits_sound (hv s hs).2.1 ht).2] at this
      revert this
      cases bit (vP (CO checkVecs[s]!)) t <;> cases bit (vM (CO checkVecs[s]!)) t <;> decide
    rw [hall] at h
    exact absurd h (by decide)

theorem inv_ok : invOK nPts (orbitData ()).alpha (invT nPts (orbitData ()).alpha) = true ∧
    invOK nPts (orbitData ()).beta (invT nPts (orbitData ()).beta) = true := by
  have hb := fun i hi => inv_facts invAll (i := i) hi
  have hA : CFSG.KS.TW.TR 245520 (orbitData ()).alpha (tab ONW.A) :=
    natTab_TR (orb_tabs mvAll ordAll sortAll).1 fun i hi => (hb i hi).1
  have hB : CFSG.KS.TW.TR 245520 (orbitData ()).beta (tab ONW.B) :=
    natTab_TR (orb_tabs mvAll ordAll sortAll).2 fun i hi => (hb i hi).2.1
  exact ⟨CFSG.KS.TW.invOK_of hA (CFSG.KS.TW.invT_TR (by norm_num) hA (g := tab ONW.U0) fun i hi =>
      ⟨(hb i hi).2.2.1, (hb i hi).2.2.2.2.2.2.1, (hb i hi).2.2.2.2.1⟩) fun i hi => (hb i hi).2.2.2.2.1,
    CFSG.KS.TW.invOK_of hB (CFSG.KS.TW.invT_TR (by norm_num) hB (g := tab ONW.U1) fun i hi =>
      ⟨(hb i hi).2.2.2.1, (hb i hi).2.2.2.2.2.2.2, (hb i hi).2.2.2.2.2.1⟩) fun i hi => (hb i hi).2.2.2.2.2.1⟩

theorem facts272164 : matrixChecks () = true ∧
    orbitOK nPts (colsA ()) (colsB ()) (orbitData ()) posOrb 3 = true ∧
    negOK nPts (orbitData ()) (negTable (orbitData ()) posOrb) = true ∧
    basisChecks (basisRows (orbitData ())) basisXLit = true ∧
    supportChecks (orbitData ()) (basisRows (orbitData ())) basisXLit = true ∧
    invOK nPts (orbitData ()).alpha (invT nPts (orbitData ()).alpha) = true ∧
    invOK nPts (orbitData ()).beta (invT nPts (orbitData ()).beta) = true :=
  ⟨matrix_ok, orbit_ok, neg_ok, basis_ok, support_ok, inv_ok⟩

end CertificateChecks.KernelSpor.ON2

end
