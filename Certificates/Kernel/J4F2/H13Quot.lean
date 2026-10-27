module

public import CFSG.Quasithin.H13.J4QuotInputs
public import CFSG.Quasithin.H13.J4Words
public import CFSG.Sporadic.HS.SmallF2Spec
public import Certificates.Data.CFSGNative.H13.J4Data
public import Certificates.Data.CFSGNative.H13.J4Elems
public import Certificates.Data.CFSGNative.H13.J4Data
public import Certificates.Kernel.J4F2.H13
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4F2

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native CFSG.Quasithin.H13.J4.Native
open CFSG.Quasithin.H13.J4 CertificateChecks.KernelJ4Q

abbrev RE (X Y : Array V2) : Prop := ∀ i : Nat, X[i]?.getD V2.zero = Y[i]?.getD V2.zero

theorem re_refl (X : Array V2) : RE X X := fun _ => rfl

theorem frTable_congr {Y Y' : Array V2} (h : RE Y Y') : frTable Y = frTable Y' := by
  unfold frTable frEntry
  simp only [h]

theorem frApply_zero (Y : Array V2) : frApply (frTable Y) V2.zero = V2.zero := by
  simp [frApply, frWord, frWord6, frByte, frTable, frEntry, V2.zero, V2.xor]

theorem getD_mulRows (X Y : Array V2) (i : Nat) :
    (mulRows X Y)[i]?.getD V2.zero = frApply (frTable Y) (X[i]?.getD V2.zero) := by
  unfold mulRows
  cases h : X[i]? with
  | none => simp [h, frApply_zero]
  | some x => simp [h]

theorem re_mul {X X' Y Y' : Array V2} (hX : RE X X') (hY : RE Y Y') :
    RE (mulRows X Y) (mulRows X' Y') := fun i => by
  rw [getD_mulRows, getD_mulRows, hX, frTable_congr hY]

theorem mulRows_congr (X : Array V2) {Y Y' : Array V2} (hY : RE Y Y') :
    mulRows X Y = mulRows X Y' := by
  unfold mulRows
  rw [frTable_congr hY]

theorem transposeRows_congr {X X' : Array V2} (h : RE X X') : transposeRows X = transposeRows X' := by
  unfold transposeRows
  simp only [h]

theorem rowsAgree_congr {X X' : Array V2} (h : RE X X') (d : Nat) (f : Nat → Nat → Bool) :
    rowsAgree X d f = rowsAgree X' d f := by
  unfold rowsAgree
  simp only [h]

theorem rowsZero_congr {X X' : Array V2} (h : RE X X') : rowsZero X = rowsZero X' := by
  unfold rowsZero
  simp only [h]

theorem addRows_eq (X Y : Array V2) : addRows X Y = CFSG.Sporadic.J4.QT2A.addRows X Y := rfl

@[expose] def padRows (X : Array V2) : Array V2 :=
  X ++ (List.replicate (112 - X.size) V2.zero).toArray

theorem re_pad (X : Array V2) : RE X (padRows X) := fun i => by
  unfold padRows
  by_cases hi : i < X.size
  · rw [Array.getElem?_append_left hi]
  · rw [Array.getElem?_append_right (by omega), Array.getElem?_eq_none (by omega)]
    simp only [Option.getD_none, List.getElem?_toArray, List.getElem?_replicate]
    split <;> rfl

@[expose] noncomputable def agreeK (x d : Nat) (f : Nat → Nat → Bool) : Bool :=
  (List.range d).all fun i => (List.range d).all fun j => x.testBit (128 * i + j) == f i j

theorem rowsAgree_eq {X : Array V2} {x : Nat} (hX : WfA X ∧ encR X = x) {d : Nat} (hd : d ≤ 112)
    (f : Nat → Nat → Bool) : rowsAgree X d f = agreeK x d f := by
  unfold rowsAgree agreeK
  apply mkRange_congr
  intro i hi
  apply mkRange_congr
  intro j hj
  rw [← hX.2, encR_bit]
  have h1 : (128 * i + j) / 128 = i := by omega
  have h2 : (128 * i + j) % 128 = j := by omega
  have hi' : i < 112 := by omega
  rw [h1, h2, testBit_v2N _ (by omega)]
  simp [hi']

@[expose] noncomputable def rowsK (x : Nat) (g : Nat → Nat) : Bool :=
  (List.range 112).all fun i => Nat.beq (rowJ rm x i) (g i)

theorem rowsAgree_full {X : Array V2} {x : Nat} (hX : WfA X ∧ encR X = x) (g : Nat → Nat)
    (hg : ∀ i < 112, g i < 2 ^ 112) (f : Nat → Nat → Bool)
    (hf : ∀ i < 112, ∀ j < 112, f i j = (g i).testBit j) : rowsAgree X 112 f = rowsK x g := by
  unfold rowsAgree rowsK
  apply mkRange_congr
  intro i hi
  have hw : ∀ k (h : k < X.size), X[k].wf = true := Array.all_eq_true.mp hX.1.2
  have hr : rowJ rm x i = v2N (X[i]?.getD V2.zero) := by
    rw [(consts_c hK).2, ← hX.2]
    exact rowJ_eq hw hi
  have hlt := v2N_lt112 (CFSG.Sporadic.J4.rows_getD_wf (rows_wf_of hX.1) i)
  rw [hr]
  apply Bool.eq_iff_iff.mpr
  rw [List.all_eq_true]
  constructor
  · intro h
    have e : v2N (X[i]?.getD V2.zero) = g i := by
      apply Nat.eq_of_testBit_eq
      intro j
      by_cases hj : j < 112
      · have h1 := beq_iff_eq.mp (h j (List.mem_range.mpr hj))
        rw [← testBit_v2N _ (by omega), h1, hf i hi j hj]
      · have hle : 2 ^ 112 ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega)
        rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt hle),
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hg i hi) hle)]
    rw [e]
    exact Nat.beq_refl _
  · intro h j hj
    have hj' := List.mem_range.mp hj
    rw [testBit_v2N _ (by omega), Nat.eq_of_beq_eq_true h, hf i hi j hj']
    exact beq_self_eq_true _

theorem rowsZero_eq {X : Array V2} {x : Nat} (hX : WfA X ∧ encR X = x) :
    rowsZero X = rowsK x (fun _ => 0) := by
  rw [← rowsAgree_full hX (fun _ => 0) (fun _ _ => by omega) (fun _ _ => false)
    (fun _ _ j _ => (Nat.zero_testBit j).symm)]
  unfold rowsZero rowsAgree
  apply mkRange_congr
  intro i _
  apply mkRange_congr
  intro j _
  cases (X[i]?.getD V2.zero).testBit j <;> rfl

@[expose] def diag12 (i : Nat) : Nat := if i < 12 then 2 ^ i else 0

theorem diag12_bits : ∀ i < 112, ∀ j < 112,
    (decide (i < 12) && i == j) = (diag12 i).testBit j := by
  intro i _ j _
  unfold diag12
  by_cases h : i < 12
  · rw [if_pos h, Nat.testBit_two_pow]
    apply Bool.eq_iff_iff.mpr
    simp [h]
  · simp [h]

theorem diag12_lt : ∀ i < 112, diag12 i < 2 ^ 112 := by
  intro i hi
  unfold diag12
  split
  · exact Nat.pow_lt_pow_right (by omega) (by omega)
  · exact Nat.two_pow_pos 112

@[expose] def phiP : Array V2 := padRows phiRows

@[expose] def eP : Array V2 := padRows eCols

@[expose] noncomputable def phiN : Nat := encR phiP

@[expose] noncomputable def eN : Nat := encR eP

@[expose] noncomputable def gN : Nat := encR gRows

@[expose] noncomputable def hN : Nat := encR hRows

theorem wf_phi : phiP.toList.all V2.wf = true := by quickRfl

theorem wf_e : eP.toList.all V2.wf = true := by quickRfl

theorem wf_g : gRows.toList.all V2.wf = true := by quickRfl

theorem wf_h : hRows.toList.all V2.wf = true := by quickRfl

theorem mk_phi : WfA phiP ∧ encR phiP = phiN :=
  ⟨⟨by simp [phiP, padRows, phiRows], by rw [← Array.all_toList]; exact wf_phi⟩, rfl⟩

theorem mk_e : WfA eP ∧ encR eP = eN :=
  ⟨⟨by simp [eP, padRows, eCols], by rw [← Array.all_toList]; exact wf_e⟩, rfl⟩

theorem mk_g : WfA gRows ∧ encR gRows = gN :=
  ⟨⟨by simp [gRows], by rw [← Array.all_toList]; exact wf_g⟩, rfl⟩

theorem mk_h : WfA hRows ∧ encR hRows = hN :=
  ⟨⟨by simp [hRows], by rw [← Array.all_toList]; exact wf_h⟩, rfl⟩

theorem re_phi : RE phiRows phiP := re_pad phiRows

theorem re_e : RE eCols eP := re_pad eCols

@[expose] noncomputable def quotChecksW (phi e g h : Nat) : Bool :=
  strictB (Nat.xor tK.1 one) fun tt => strictB (trJ t0 t1 t2 t3 t4 t5 t6 e) fun et =>
    rowsK (mulJ c rm phi tt) (fun _ => 0) && rowsK (mulJ c rm tt et) (fun _ => 0) &&
    rowsK (mulJ c rm phi et) diag12 &&
    Nat.beq (Nat.xor (Nat.xor (mulJ c rm tt g) (mulJ c rm h tt)) (mulJ c rm et phi)) one

@[expose] noncomputable def quotChecksK : Bool := quotChecksW phiN eN gN hN

theorem quotChecksK_ok : quotChecksK = true := by quickRfl

@[expose] noncomputable def imageChecksW (phi e : Nat) : Bool :=
  strictB (trJ t0 t1 t2 t3 t4 t5 t6 e) fun et =>
    agreeK (mulJ c rm (mulJ c rm phi tK.1) et) 12 (fun a b => a == b) &&
    (List.range 12).all (fun i => agreeK
      (mulJ c rm (mulJ c rm phi (rcK (coreBasisConjugators.getD i [])).1) et) 12
      (fun a b => a == b)) &&
    agreeK (mulJ c rm (mulJ c rm phi (uvK.getD 0 prOneK).1) et) 12
      (fun a b => (uRows12.getD a 0).testBit b) &&
    agreeK (mulJ c rm (mulJ c rm phi (uvK.getD 1 prOneK).1) et) 12
      (fun a b => (vRows12.getD a 0).testBit b)

@[expose] noncomputable def imageChecksK : Bool := imageChecksW phiN eN

theorem imageChecksK_ok : imageChecksK = true := by quickRfl

theorem quotChecks_neg_phi : notB (quotChecksW (Nat.xor phiN 1) eN gN hN) = true := by quickRfl

theorem quotChecks_neg_g : notB (quotChecksW phiN eN (Nat.xor gN 1) hN) = true := by quickRfl

theorem imageChecks_neg_phi : notB (imageChecksW (Nat.xor phiN 1) eN) = true := by quickRfl

theorem imageChecks_neg_e : notB (imageChecksW phiN (Nat.xor eN 1)) = true := by quickRfl

theorem mk_T : WfA (addRows (tOf (uvPairsOf (basePairs ()))).1 (idRows ())) ∧
    encR (addRows (tOf (uvPairsOf (basePairs ()))).1 (idRows ())) = Nat.xor tK.1 one := by
  rw [addRows_eq]
  have h := enc_addRows pe_t.1.1 mkId.1
  rw [pe_t.1.2, mkId.2] at h
  exact h

theorem mk_Et : WfA (transposeRows eCols) ∧
    encR (transposeRows eCols) = trJ t0 t1 t2 t3 t4 t5 t6 eN := by
  rw [transposeRows_congr re_e]
  exact ⟨wf_transposeRows _, by rw [enc_transposeRows hK mk_e.1, mk_e.2]⟩

theorem quotChecks_eq : quotChecks = quotChecksK := by
  unfold quotChecks quotChecksK quotChecksW
  simp only [strictB_eq]
  rw [rowsZero_congr (re_mul re_phi (re_refl _)), rowsZero_eq (mkMul mk_phi mk_T),
    rowsZero_eq (mkMul mk_T mk_Et),
    rowsAgree_congr (re_mul re_phi (re_refl _)),
    rowsAgree_full (mkMul mk_phi mk_Et) diag12 diag12_lt _ diag12_bits,
    mulRows_congr _ re_phi, addRows_eq, addRows_eq]
  have h1 := enc_addRows (mkMul mk_T mk_g).1 (mkMul mk_h mk_T).1
  rw [(mkMul mk_T mk_g).2, (mkMul mk_h mk_T).2] at h1
  have h2 := enc_addRows h1.1 (mkMul mk_Et mk_phi).1
  rw [h1.2, (mkMul mk_Et mk_phi).2] at h2
  rw [mkEq h2 mkId]

theorem mk_img {X : Array V2} {x : Nat} (hX : WfA X ∧ encR X = x) (f : Nat → Nat → Bool) :
    rowsAgree (mulRows (mulRows phiRows X) (transposeRows eCols)) 12 f =
      agreeK (mulJ c rm (mulJ c rm phiN x) (trJ t0 t1 t2 t3 t4 t5 t6 eN)) 12 f := by
  rw [rowsAgree_congr (re_mul (re_mul re_phi (re_refl X)) (re_refl _))]
  exact rowsAgree_eq (mkMul (mkMul mk_phi hX) mk_Et) (by omega) f

theorem imageChecks_eq : imageChecks = imageChecksK := by
  unfold imageChecks imageChecksK imageChecksW
  simp only [strictB_eq]
  rw [mk_img pe_t.1, mk_img (pt_uv 0).1, mk_img (pt_uv 1).1,
    mkRange_congr (fun i _ => mk_img (pe_rc (coreBasisConjugators.getD i [])).1 _)]

open Certificates in
open CFSG CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.J4 CFSG.Sporadic.J4 in
open CFSG.Sporadic.J4.Native CFSG.Quasithin.H13.J4.Native Matrix in
theorem c7015 :
    (quotChecks = true)
    ∧ (imageChecks = true) :=
  ⟨quotChecks_eq.trans quotChecksK_ok, imageChecks_eq.trans imageChecksK_ok⟩

end CertificateChecks.KernelJ4F2

end
