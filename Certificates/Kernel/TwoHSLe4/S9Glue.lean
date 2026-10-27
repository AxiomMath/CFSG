module

public import Certificates.Kernel.TwoHSLe4.S9Chk
public import Certificates.Kernel.TwoHSLe4.S9Sub0
public import Certificates.Kernel.TwoHSLe4.S9Sub1
public import Certificates.Kernel.TwoHSLe4.S9Sub2
public import Certificates.Kernel.TwoHSLe4.S9Sub3
import Mathlib.Tactic.IntervalCases
import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CertificateChecks.KernelTwoHSLe4.S9

open CFSG.EvenSporadicStandard.TwoHS CFSG.KC.Enum

theorem toR4_matOfList (l : List ℕ) : toR4 (matOfList l) = rl l := by
  simp [toR4, matOfList, rl, ZMod.val_natCast]

theorem q0R_eq : q0R = q0Data.map rl := by
  simp [q0R, q0List, Function.comp_def, toR4_matOfList]

theorem shatR_eq : shatR = shatData.map rl := by
  simp [shatR, shatList, Function.comp_def, toR4_matOfList]

theorem ofR4_genL (l : ℕ) : ofR4 (genL l) = gamma1Mat ∨ ofR4 (genL l) = gamma2Mat := by
  unfold genL
  split_ifs
  · left
    rw [← toR4_matOfList, ofR4_toR4]
    rfl
  · right
    rw [← toR4_matOfList, ofR4_toR4]
    rfl

theorem word_mem {R : Set M4} (hmul : ∀ A ∈ R, ∀ B ∈ R, A * B ∈ R) (h1 : (1 : M4) ∈ R)
    (hg1 : gamma1Mat ∈ R) (hg2 : gamma2Mat ∈ R) (w : List ℕ) : ofR4 (wordR w) ∈ R := by
  have key : ∀ (w : List ℕ) (a : R4), ofR4 a ∈ R →
      ofR4 (w.foldl (fun a l => rmul a (genL l)) a) ∈ R := by
    intro w
    induction w with
    | nil => intro a ha; exact ha
    | cons l w ih =>
      intro a ha
      rw [List.foldl_cons]
      refine ih _ ?_
      rw [ofR4_rmul]
      refine hmul _ ha _ ?_
      rcases ofR4_genL l with e | e <;> rw [e]
      · exact hg1
      · exact hg2
  exact key w R4.one (by rw [ofR4_one]; exact h1)

theorem sub_all : ∀ x ∈ shatR.sublists, subCheck x = true := by
  have hs : shatR = shatA ++ shatB := by
    rw [shatR_eq, shatA, shatB, List.take_append_drop]
  have hB : shatB.sublists.length = 16 := by decide +kernel
  have hc : ∀ j < 16, subChunk j = true := by
    intro j hj
    interval_cases j
    · exact sub0
    · exact sub1
    · exact sub2
    · exact sub3
    · exact sub4
    · exact sub5
    · exact sub6
    · exact sub7
    · exact sub8
    · exact sub9
    · exact sub10
    · exact sub11
    · exact sub12
    · exact sub13
    · exact sub14
    · exact sub15
  intro x hx
  rw [hs, List.sublists_append] at hx
  simp only [List.bind_eq_flatMap, List.mem_flatMap, List.mem_map] at hx
  obtain ⟨y, hy, z, hz, rfl⟩ := hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
  have h := hc j (hB ▸ hj)
  unfold subChunk at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at h
  exact List.all_eq_true.1 h z hz

theorem listFacts : ListFacts := by
  obtain ⟨h1, h2⟩ := q0_ok
  obtain ⟨h4, h5, h6, h7, h8, h9⟩ := shat_ok
  rw [← q0R_eq] at h1 h2
  rw [← shatR_eq] at h4 h5 h6 h7 h8 h9
  have hone : ∀ A ∈ shatList, toR4 A = R4.one → A = 1 := fun A _ hA => by
    rw [← ofR4_toR4 A, hA, ofR4_one]
  refine ⟨List.Nodup.of_map toR4 h2, by simpa [q0R] using h1, ?_, List.Nodup.of_map toR4 h5,
    by simpa [shatR] using h4, ?_, ?_, ?_, ?_, sub_of_check (List.Nodup.of_map toR4 h5) sub_all⟩
  · intro R hmul h1R hg1 hg2 A hA
    have hm : toR4 A ∈ q0Data.map rl := by
      rw [← q0R_eq]
      exact List.mem_map.2 ⟨A, hA, rfl⟩
    obtain ⟨i, hi, hei⟩ := List.getElem_of_mem hm
    have hlen : (q0Data.map rl).length = 336 := by rw [← q0R_eq]; exact h1
    have hw := CFSG.KS.allN_spec w_ok i (hlen ▸ hi)
    rw [beq_iff_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some,
      hei] at hw
    have := word_mem hmul h1R hg1 hg2 (wdec (WT i))
    rwa [hw, ofR4_toR4] at this
  · obtain ⟨A, hA, hA1⟩ := mem_shatR h6
    rw [← hone A hA hA1]
    exact hA
  · intro A hA B hB
    obtain ⟨C, hC, hCe⟩ := mem_shatR (h7 _ (toR4_mem_shatR hA) _ (toR4_mem_shatR hB))
    have : A * B = C := by
      rw [← ofR4_toR4 A, ← ofR4_toR4 B, ← ofR4_rmul, ← hCe, ofR4_toR4]
    rw [this]
    exact hC
  · intro A hA
    obtain ⟨b, hb, hb1, hb2⟩ := h8 _ (toR4_mem_shatR hA)
    obtain ⟨B, hB, rfl⟩ := mem_shatR hb
    refine ⟨B, hB, ?_, ?_⟩
    · rw [← ofR4_toR4 A, ← ofR4_toR4 B, ← ofR4_rmul, hb1, ofR4_one]
    · rw [← ofR4_toR4 A, ← ofR4_toR4 B, ← ofR4_rmul, hb2, ofR4_one]
  · obtain ⟨a, ha, ha3⟩ := h9
    obtain ⟨A, hA, rfl⟩ := mem_shatR ha
    refine ⟨A, hA, ?_⟩
    have : (A 2 2).val = 3 := ha3
    rw [← ZMod.natCast_zmod_val (A 2 2), this]
    rfl

end CertificateChecks.KernelTwoHSLe4.S9

end
