module

public import Certificates.Data.Kernel.SmithD6.EaK
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.ForallChunks
import all Certificates.Data.SmithD6Model

set_option maxRecDepth 100000

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KD.SmithD6 CFSG.KD.SmithD6Stab CFSG.KD.SmithD6Ea

#kc_each CertificateChecks.SmithD6Ea d6ea eaChunkOK 0 179

public section

namespace CertificateChecks.SmithD6Ea

#kc_forall_chunks eaChunks_ok (fun c => eaChunkOK c = true) 179 CertificateChecks.SmithD6Ea.d6ea 1

theorem eaKC_length : JEA.eaKC.length = 179 := by decide +kernel

theorem eaKC_flatten_length : JEA.eaKC.flatten.length = 1578 := by decide +kernel

theorem cbw_ok : eaCBWOK = true := by decide +kernel

open CFSG.KD.SmithD6ST CFSG.KD.SmithD6Reps in
theorem tvColsP_eq (p : Nat × Nat) : CFSG.KD.SmithD6Reps.tvColsP p =
    ⟨List.ofFn (n := 32) fun c => (((bitsOf p.1).foldl
      (fun acc i => (bitsOf p.2).foldl (fun acc j => acc ^^^ pairMat[i * 12 + j]!) acc) 0 >>>
        (32 * c.val)) &&& 0xFFFFFFFF) ^^^ 2 ^ c.val⟩ := by
  unfold CFSG.KD.SmithD6Reps.tvColsP
  exact Array.toList_inj.1 Array.toList_ofFn

open CFSG.KD.SmithD6ST CFSG.KD.SmithD6Reps in
@[expose] noncomputable def eaRestrL (pr : Nat × Nat) : List Nat :=
  ea7Bits.map fun m => applyCols ⟨List.ofFn (n := 32) fun c => (((bitsOf pr.1).foldl
      (fun acc i => (bitsOf pr.2).foldl (fun acc j => acc ^^^ pairMat[i * 12 + j]!) acc) 0 >>>
        (32 * c.val)) &&& 0xFFFFFFFF) ^^^ 2 ^ c.val⟩ (2 ^ m)

open CFSG.KD.SmithD6ST CFSG.KD.SmithD6Reps in
theorem eaRestr_eq (pr : Nat × Nat) : eaRestr pr = eaRestrL pr := by
  unfold eaRestr eaRestrL
  rw [tvColsP_eq]

@[expose] noncomputable def eaGoG (A : Nat → Bool) (V : Nat → Nat) : List Nat → Nat → Bool
  | [], _ => true
  | k :: ks, prev => A k && decide (prev < V k) && eaGoG A V ks (V k)

theorem eaGoG_split (A : Nat → Bool) (V : Nat → Nat) :
    ∀ (l : List Nat) (n prev : Nat), 0 < n → eaGoG A V (l.take n) prev = true →
      eaGoG A V (l.drop n) (V (l.getD (n - 1) 0)) = true → n ≤ l.length →
      eaGoG A V l prev = true
  | [], n, _, hn, _, _, hl => absurd hl (by simp; omega)
  | k :: ks, 1, prev, _, h1, h2, _ => by
    simp only [List.take_succ_cons, List.take_zero, eaGoG, Bool.and_true, List.drop_succ_cons,
      List.drop_zero, Nat.sub_self, List.getD_cons_zero] at h1 h2 ⊢
    rw [h1, h2]
    rfl
  | k :: ks, m + 2, prev, _, h1, h2, hl => by
    simp only [List.take_succ_cons, eaGoG, Bool.and_eq_true] at h1
    simp only [List.drop_succ_cons] at h2
    simp only [eaGoG, Bool.and_eq_true]
    refine ⟨h1.1, eaGoG_split A V ks (m + 1) (V k) (by omega) h1.2 ?_ (by simp at hl; omega)⟩
    simpa using h2

open CFSG.KD.SmithD6ST CFSG.KD.SmithD6Reps in
@[expose] noncomputable def eaF4A (k : Nat) : Bool := lineTree.memB k && eaInK k

open CFSG.KD.SmithD6ST CFSG.KD.SmithD6Reps in
@[expose] noncomputable def eaF4V (k : Nat) : Nat := packL (eaRestrL (pairK k))

open CFSG.KD.SmithD6ST CFSG.KD.SmithD6Reps in
theorem eaF4Go_eq : ∀ (l : List Nat) (prev : Nat), eaF4Go l prev = eaGoG eaF4A eaF4V l prev
  | [], _ => rfl
  | k :: ks, prev => by
    simp only [eaF4Go, eaGoG, eaF4A, eaF4V, eaRestr_eq, eaF4Go_eq ks]
    rfl

@[expose] noncomputable def eaQ1 : List Nat := JEA.eaQ.drop 395
@[expose] noncomputable def eaQ2 : List Nat := eaQ1.drop 395
@[expose] noncomputable def eaQ3 : List Nat := eaQ2.drop 395

theorem f4_a : eaGoG eaF4A eaF4V (JEA.eaQ.take 395) 0 = true := by decide +kernel
theorem f4_b : eaGoG eaF4A eaF4V (eaQ1.take 395) (eaF4V (JEA.eaQ.getD 394 0)) = true := by
  decide +kernel
theorem f4_c : eaGoG eaF4A eaF4V (eaQ2.take 395) (eaF4V (eaQ1.getD 394 0)) = true := by
  decide +kernel
theorem f4_d : eaGoG eaF4A eaF4V eaQ3 (eaF4V (eaQ2.getD 394 0)) = true := by decide +kernel
theorem f4_len : JEA.eaQ.length == 1578 && decide (395 ≤ JEA.eaQ.length) &&
    decide (395 ≤ eaQ1.length) && decide (395 ≤ eaQ2.length) = true := by decide +kernel

theorem f4_ok : eaF4OK = true := by
  unfold eaF4OK
  rw [eaF4Go_eq]
  have hl := f4_len
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hl
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := hl
  rw [Bool.and_eq_true]
  refine ⟨h0, ?_⟩
  refine eaGoG_split _ _ _ 395 0 (by omega) f4_a ?_ h1
  refine eaGoG_split _ _ _ 395 _ (by omega) f4_b ?_ h2
  exact eaGoG_split _ _ _ 395 _ (by omega) f4_c f4_d h3

open CFSG.KD.SmithD6ST CFSG.KD.SmithD6Reps in
theorem f3_ok : eaF3All = true := by
  unfold eaF3All eaF3OK
  simp only [tvColsP_eq]
  decide +kernel

theorem rig_ok : eaRigP eaInF0K (fun p => pairK (keyAt p)) = true := by decide +kernel

theorem lv0_ok : eaLvOK 0 = true := by decide +kernel

theorem lv1_ok : eaLvOK 1 = true := by decide +kernel

theorem lv2_ok : eaLvOK 2 = true := by decide +kernel

theorem lv3_ok : eaLvOK 3 = true := by decide +kernel

theorem lv4_ok : eaLvOK 4 = true := by decide +kernel

theorem a_ok : eaAOK = true := by decide +kernel

end CertificateChecks.SmithD6Ea

end
