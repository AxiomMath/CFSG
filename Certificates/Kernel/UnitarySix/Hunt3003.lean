module

public import Certificates.Kernel.UnitarySix.Hunt3003Checks
public import CFSG.Certificates.Kernel.U6Sound3003
public import CFSG.Certificates.Kernel.U6Hunt.ChunkL

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Mathieu CFSG.Certificates CFSG.Certificates.Native
open CFSG.KC.U6 CFSG.EvenSmallLie.UnitarySix.Hunt CFSG.ComponentClassification.WittDesign
open CFSG.Sporadic.Mathieu
open CFSG.KLie.CT (fget sumN)

namespace M22C

@[expose] noncomputable def SA : Array (Array Nat) :=
  Array.ofFn (n := 11) fun j => unpack 22 5 (S j.val)

theorem binds : Binds 22 5 S 11 5 BP SA m22Base := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [SA], fun j hj => ?_, rfl, ?_⟩
  · rw [SA, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  · intro t ht
    interval_cases t <;> rfl

theorem raw : rawChainOK 22 (SA.extract 0 2) SA m22Base
    (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 11 m22Der) 1 = true :=
  rawChainK_sound (NS := 1) (CH := 22) binds head hl (by norm_num) hs

theorem gens : CFSG.Monster.B.Co2.Rep 22 SA[0]! m22gA ∧ CFSG.Monster.B.Co2.Rep 22 SA[1]! m22gB := by
  have h0 : ∀ x : Fin 22, pg 5 (mask 5) (S 0) x.val = (m22gA x : ℕ) := by decide +kernel
  have h1 : ∀ x : Fin 22, pg 5 (mask 5) (S 1) x.val = (m22gB x : ℕ) := by decide +kernel
  refine ⟨fun x => ?_, fun x => ?_⟩
  · rw [SA, getElem!_pos _ 0 (by simp), Array.getElem_ofFn]
    simp only [unpack]
    rw [getElem!_pos _ x.val (by simp), Array.getElem_ofFn]
    exact h0 x
  · rw [SA, getElem!_pos _ 1 (by simp), Array.getElem_ofFn]
    simp only [unpack]
    rw [getElem!_pos _ x.val (by simp), Array.getElem_ofFn]
    exact h1 x

theorem sizes : ∀ i < 5, rcnt (LR i) = [22, 21, 20, 16, 3].getD i 0 := by
  intro i hi
  interval_cases i <;> decide

end M22C

theorem kChunks : ∀ a < 22, chunkK R8 R0 RY keys8 keys0 keysY M22C.TR oM a = VN.getD a 0 :=
  fun a ha => (chunkL_eq _ _ _ _ _ _ _ _ _).symm.trans (Nat.eq_of_beq_eq_true
    (CFSG.KC.Co3Bfs.cover_of_blocks (B := 1) (nb := 22) (by omega) (by decide) CB.all a ha))

open Certificates in
open CFSG.EvenSmallLie.UnitarySix.Hunt CFSG.ComponentClassification.WittDesign in
theorem cert3003 : (rootCheck 256 tab8 list8 = true ∧ rootCheck 256 tab0 list0 = true ∧
      rootCheck 512 tabY listY = true ∧ list8.Pairwise (fun a b => keyT a < keyT b) ∧
      list0.Pairwise (fun a b => keyT a < keyT b) ∧ listY.Pairwise (fun a b => keyT a < keyT b))
    ∧ (m22Count (fun f => (missOut (tf tab8) list8 f || missOut (tf tab0) list0 f || missIn (tf
        tabY) listY f) = true) = 0)
    ∧ (m22Count (fun f => sqMulB (tf tab8) f = true) = 1716)
    ∧ (m22Count (fun f => (sqB f && !eqB id f) = true) = 1155)
    ∧ (m22Count (fun f => commB (tf tab8) f = true) = 1344)
    ∧ (m22Count (fun f => commB (tf tab0) f = true) = 320)
    ∧ (m22Count (fun f => commB (tf tabY) f = true) = 384) := by
  have hc := sound3003C M22C.binds permC M22C.hl M22C.raw M22C.gens M22C.sizes kDig
    (fun k hk => (kKeys k hk).1) kChunks Nat.one_pos
  obtain ⟨c0, c1, c2, c3, c4, c5⟩ := hc
  have hN : ∀ k < 6, fget (sumN 22 fun a => VN.getD a 0) k 20 =
      [0, 1716, 1155, 1344, 320, 384].getD k 0 := by
    intro k hk
    have := congrArg (fun l => l.getD k 0) kTot
    simpa [List.getD_eq_getElem?_getD, hk] using this
  have hm : ∀ L : List Nat, (∀ k ∈ L, k ∈ keys8 ++ keys0 ++ keysY) →
      ∀ x ∈ L, x < 2 ^ 110 ∧ ∀ i < 22, fget (unkey x) i 5 < 22 := fun L hL x hx => kKeys x (hL x hx)
  refine ⟨⟨sound3003R (kDig _ (by simp)) (hm _ (fun k hk => by simp [hk])) kRoot8,
    sound3003R (kDig _ (by simp)) (hm _ (fun k hk => by simp [hk])) kRoot0,
    sound3003R (kDig _ (by simp)) (hm _ (fun k hk => by simp [hk])) kRootY,
    sound3003P kSorted.1 (fun k hk => (kKeys k (by simp [hk])).1),
    sound3003P kSorted.2.1 (fun k hk => (kKeys k (by simp [hk])).1),
    sound3003P kSorted.2.2 (fun k hk => (kKeys k (by simp [hk])).1)⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← card_m22_subtype]; exact c0.trans (hN 0 (by norm_num))
  · rw [← card_m22_subtype]; exact c1.trans (hN 1 (by norm_num))
  · rw [← card_m22_subtype]; exact c2.trans (hN 2 (by norm_num))
  · rw [← card_m22_subtype]; exact c3.trans (hN 3 (by norm_num))
  · rw [← card_m22_subtype]; exact c4.trans (hN 4 (by norm_num))
  · rw [← card_m22_subtype]; exact c5.trans (hN 5 (by norm_num))

end CertificateChecks.KernelU6

end
