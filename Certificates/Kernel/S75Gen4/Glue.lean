module

public import CFSG.Certificates.Kernel.S75Gen4.Sound
public import Certificates.Kernel.S75Gen4.Checks
public import Certificates.Kernel.S75Gen4.Recs

public section

namespace CertificateChecks.KernelS75Gen4

open CFSG.KD.S5Ext CFSG.KD.S75Gen4 CFSG.OddStandard.Solomon75.AhatData

theorem genSwaps10 : genSwaps 10 = swL := by decide
theorem genSwaps11 : genSwaps 11 = swL := by decide

theorem idC10 : ∀ x : Fin 10, pt (idC 10) x.val = x.val := by decide +kernel
theorem idC11 : ∀ x : Fin 11, pt (idC 11) x.val = x.val := by decide +kernel

theorem swPt10 : ∀ k, k < (genSwaps 10).length → ∀ x : Fin 10,
    pt (swC 10 ((genSwaps 10).getD k [])) x.val = (swapsPerm 10 ((genSwaps 10).getD k []) x).val := by
  decide +kernel

theorem swPt11 : ∀ k, k < (genSwaps 11).length → ∀ x : Fin 11,
    pt (swC 11 ((genSwaps 11).getD k [])) x.val = (swapsPerm 11 ((genSwaps 11).getD k []) x).val := by
  decide +kernel

theorem tab10 : TabChecks 10 TAB10 MP INVP GI TREE where
  idC_pt := idC10
  sw_pt := swPt10
  id := ch6132_id10
  lanes := ch6132_inc10
  sw := by rw [genSwaps10]; exact ch6132_sw10
  mp := mp_all ch6132_mp10a ch6132_mp10b ch6132_mp10c ch6132_mp10d
  tree := ch6132_tree.1
  treeAll := ch6132_tree.2
  inv := ch6132_inv

theorem tab11 : TabChecks 11 TAB11 MP INVP GI TREE where
  idC_pt := idC11
  sw_pt := swPt11
  id := ch6132_id11
  lanes := ch6132_inc11
  sw := by rw [genSwaps11]; exact ch6132_sw11
  mp := mp_all ch6132_mp11a ch6132_mp11b ch6132_mp11c ch6132_mp11d
  tree := ch6132_tree.1
  treeAll := ch6132_tree.2
  inv := ch6132_inv

theorem by_chunk {P : Nat → Prop} (hc : ∀ i, i < 18 → ∀ k, 32 * i ≤ k → k < 32 * i + 32 → P k) :
    ∀ k, k < 576 → P k :=
  fun k hk => hc (k / 32) (by omega) k (by omega) (by omega)

theorem chunk {α : Type} {B : Nat → List α → Prop} {k0 : Nat} {rs : List α} (hb : B k0 rs)
    (hl : rs.length = 32) : ∀ k, k0 ≤ k → k < k0 + 32 →
      ∃ (k1 : Nat) (rs' : List α), B k1 rs' ∧ k1 ≤ k ∧ k < k1 + rs'.length :=
  fun _ h1 h2 => ⟨k0, rs, hb, h1, hl ▸ h2⟩

theorem recs_all : ∀ k, k < 576 → ∃ (k0 : ℕ) (rs : List (ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ))),
    recsB MP INVP SQP CATP k0 rs = true ∧ k0 ≤ k ∧ k < k0 + rs.length := by
  apply by_chunk
  intro i hi k h1 h2
  interval_cases i
  · exact chunk (B := fun k0 rs => recsB MP INVP SQP CATP k0 rs = true) ch6132_r0 (by decide +kernel) k h1 h2
  · exact chunk (B := fun k0 rs => recsB MP INVP SQP CATP k0 rs = true) ch6132_r1 (by decide +kernel) k h1 h2
  · exact chunk (B := fun k0 rs => recsB MP INVP SQP CATP k0 rs = true) ch6132_r2 (by decide +kernel) k h1 h2
  · exact chunk (B := fun k0 rs => recsB MP INVP SQP CATP k0 rs = true) ch6132_r3 (by decide +kernel) k h1 h2
  · exact chunk (B := fun k0 rs => recsB MP INVP SQP CATP k0 rs = true) ch6132_r4 (by decide +kernel) k h1 h2
  · exact chunk (B := fun k0 rs => recsB MP INVP SQP CATP k0 rs = true) ch6132_r5 (by decide +kernel) k h1 h2
  · exact chunk (B := fun k0 rs => recsB MP INVP SQP CATP k0 rs = true) ch6132_r6 (by decide +kernel) k h1 h2
  · exact chunk (B := fun k0 rs => recsB MP INVP SQP CATP k0 rs = true) ch6132_r7 (by decide +kernel) k h1 h2
  · exact chunk (B := fun k0 rs => recsB MP INVP SQP CATP k0 rs = true) ch6132_r8 (by decide +kernel) k h1 h2
  · exact chunk (B := fun k0 rs => recsB MP INVP SQP CATP k0 rs = true) ch6132_r9 (by decide +kernel) k h1 h2
  · exact chunk (B := fun k0 rs => recsB MP INVP SQP CATP k0 rs = true) ch6132_r10 (by decide +kernel) k h1 h2
  · exact chunk (B := fun k0 rs => recsB MP INVP SQP CATP k0 rs = true) ch6132_r11 (by decide +kernel) k h1 h2
  · exact chunk (B := fun k0 rs => recsB MP INVP SQP CATP k0 rs = true) ch6132_r12 (by decide +kernel) k h1 h2
  · exact chunk (B := fun k0 rs => recsB MP INVP SQP CATP k0 rs = true) ch6132_r13 (by decide +kernel) k h1 h2
  · exact chunk (B := fun k0 rs => recsB MP INVP SQP CATP k0 rs = true) ch6132_r14 (by decide +kernel) k h1 h2
  · exact chunk (B := fun k0 rs => recsB MP INVP SQP CATP k0 rs = true) ch6132_r15 (by decide +kernel) k h1 h2
  · exact chunk (B := fun k0 rs => recsB MP INVP SQP CATP k0 rs = true) ch6132_r16 (by decide +kernel) k h1 h2
  · exact chunk (B := fun k0 rs => recsB MP INVP SQP CATP k0 rs = true) ch6132_r17 (by decide +kernel) k h1 h2

theorem gens10 : ∀ k, k < 576 → ∃ r : List ℕ × List (ℕ × ℕ × ℕ) × ℕ,
    genRecB 10 TAB10 MP (lC CATP k) r = true := by
  apply by_chunk
  intro i hi k h1 h2
  interval_cases i
  · exact genRecsB_at q0 _ ch6132_q0 k h1 (by rw [(by decide +kernel : q0.length = 32)]; omega)
  · exact genRecsB_at q1 _ ch6132_q1 k h1 (by rw [(by decide +kernel : q1.length = 32)]; omega)
  · exact genRecsB_at q2 _ ch6132_q2 k h1 (by rw [(by decide +kernel : q2.length = 32)]; omega)
  · exact genRecsB_at q3 _ ch6132_q3 k h1 (by rw [(by decide +kernel : q3.length = 32)]; omega)
  · exact genRecsB_at q4 _ ch6132_q4 k h1 (by rw [(by decide +kernel : q4.length = 32)]; omega)
  · exact genRecsB_at q5 _ ch6132_q5 k h1 (by rw [(by decide +kernel : q5.length = 32)]; omega)
  · exact genRecsB_at q6 _ ch6132_q6 k h1 (by rw [(by decide +kernel : q6.length = 32)]; omega)
  · exact genRecsB_at q7 _ ch6132_q7 k h1 (by rw [(by decide +kernel : q7.length = 32)]; omega)
  · exact genRecsB_at q8 _ ch6132_q8 k h1 (by rw [(by decide +kernel : q8.length = 32)]; omega)
  · exact genRecsB_at q9 _ ch6132_q9 k h1 (by rw [(by decide +kernel : q9.length = 32)]; omega)
  · exact genRecsB_at q10 _ ch6132_q10 k h1 (by rw [(by decide +kernel : q10.length = 32)]; omega)
  · exact genRecsB_at q11 _ ch6132_q11 k h1 (by rw [(by decide +kernel : q11.length = 32)]; omega)
  · exact genRecsB_at q12 _ ch6132_q12 k h1 (by rw [(by decide +kernel : q12.length = 32)]; omega)
  · exact genRecsB_at q13 _ ch6132_q13 k h1 (by rw [(by decide +kernel : q13.length = 32)]; omega)
  · exact genRecsB_at q14 _ ch6132_q14 k h1 (by rw [(by decide +kernel : q14.length = 32)]; omega)
  · exact genRecsB_at q15 _ ch6132_q15 k h1 (by rw [(by decide +kernel : q15.length = 32)]; omega)
  · exact genRecsB_at q16 _ ch6132_q16 k h1 (by rw [(by decide +kernel : q16.length = 32)]; omega)
  · exact genRecsB_at q17 _ ch6132_q17 k h1 (by rw [(by decide +kernel : q17.length = 32)]; omega)

theorem q_len : (q0 ++ q1 ++ q2 ++ q3 ++ q4 ++ q5 ++ q6 ++ q7 ++ q8 ++ q9 ++ q10 ++ q11 ++ q12 ++
    q13 ++ q14 ++ q15 ++ q16 ++ q17).length = 576 := by decide +kernel

theorem gens11 : ∀ k, k < 576 → ∃ r : List ℕ × List (ℕ × ℕ × ℕ) × ℕ,
    genRecB 11 TAB11 MP (lC CATP k) r = true := fun k hk =>
  genRecsB_at _ 0 ch6132_d11 k (Nat.zero_le k) (by rw [q_len]; exact hk)

theorem gen4Good10 : Gen4Good 10 (P0 10) :=
  gen4Good_of_checks tab10 ch6132_sq ch6132_bnd ch6132_one recs_all gens10

theorem gen4Good11 : Gen4Good 11 (P0 11) :=
  gen4Good_of_checks tab11 ch6132_sq ch6132_bnd ch6132_one recs_all gens11

end CertificateChecks.KernelS75Gen4

end
