module

public import Certificates.Kernel.HeLoc.SevenMem
public import Certificates.Kernel.HeLoc.SevenMem0
public import Certificates.Kernel.HeLoc.SevenMem1
public import Certificates.Kernel.HeLoc.SevenMem2
public import Certificates.Kernel.HeLoc.Mem

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHeLoc.Seven

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.HeLoc
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB CFSG.RankThree.Native
open CFSG.RankThree.PartOne CertificateChecks.KernelSpor

theorem arr_eq (k : Nat) (hk : k < 75) : heSevenArr k = unpack 8330 14 (A k) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound SH.all k hk
  rw [← SH.eq] at h
  rw [heSevenArr]
  exact h

@[expose] noncomputable def gp (k : Nat) : Equiv.Perm (Fin 8330) := permOfArr 8330 (unpack 8330 14 (A k))

theorem perm_k (k : Nat) (hk : k < 75) :
    permOK 8330 14 (mask 14) (8330 * 14) (A k) (AI k) = true := allN_spec kPerm k hk

theorem rep_gp (k : Nat) (hk : k < 75) : Rep 8330 (unpack 8330 14 (A k)) (gp k) :=
  (rep_permOfArr (invEqK_sound (n := 8330) (w := 14) (p := A k) (r := AI k) (perm_k k hk)).2).1

theorem rep_gpi (k : Nat) (hk : k < 75) : Rep 8330 (unpack 8330 14 (AI k)) (gp k)⁻¹ :=
  (rep_permOfArr (invEqK_sound (n := 8330) (w := 14) (p := A k) (r := AI k) (perm_k k hk)).2).2

theorem repF_pa (k : Nat) (hk : k < 75) : RepF 8330 (pa k) (gp k) := Five.repF_of_rep (rep_gp k hk)

theorem repF_pi (k : Nat) (hk : k < 75) : RepF 8330 (pi k) (gp k)⁻¹ :=
  Five.repF_of_rep (rep_gpi k hk)

theorem memB_k (k c : Nat) (hk : k < 75) (hc : c < 10) :
    memB (A k) (NF.getD k 0) (FL.getD k 0) c = true := by
  have e : memI (10 * k + c) = memB (A k) (NF.getD k 0) (FL.getD k 0) c := by
    unfold memI
    rw [show (10 * k + c) / 10 = k by omega, show (10 * k + c) % 10 = c by omega]
  rw [← e]
  rcases (by omega : 10 * k + c < 250 ∨ (250 ≤ 10 * k + c ∧ 10 * k + c < 500) ∨
      (500 ≤ 10 * k + c ∧ 10 * k + c < 750)) with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact M0.all _ (show 10 * k + c < 250 from h)
  · have := M1.all (10 * k + c - 250) (show 10 * k + c - 250 < 250 by omega)
    unfold mem1 at this
    rwa [show Nat.add 250 (10 * k + c - 250) = 10 * k + c from Nat.add_sub_cancel' h1] at this
  · have := M2.all (10 * k + c - 500) (show 10 * k + c - 500 < 250 by omega)
    unfold mem2 at this
    rwa [show Nat.add 500 (10 * k + c - 500) = 10 * k + c from Nat.add_sub_cancel' h1] at this

theorem nf_k (k : Nat) (hk : k < 75) : nfValidK 5 HeC.LR (NF.getD k 0) = true ∧ FL.getD k 0 < 2 := by
  have h := allN_spec kNF k hk
  rw [bAnd_iff, Nat.blt_eq] at h
  exact h

theorem gp_mem (k : Nat)
    (hk : k < 75) : gp k ∈ heAutGroup ∧ (gp k ∈ heP ↔ FL.getD k 0 = 0) :=
  (mem_of_memB (perm_k k hk) (nf_k k hk).1 (nf_k k hk).2 fun c hc => memB_k k c hk hc).2

theorem lit3_0 (a b c : Array Nat) : (#[a, b, c] : Array (Array Nat))[0]! = a := rfl
theorem lit3_1 (a b c : Array Nat) : (#[a, b, c] : Array (Array Nat))[1]! = b := rfl
theorem lit3_2 (a b c : Array Nat) : (#[a, b, c] : Array (Array Nat))[2]! = c := rfl
theorem lit2_0 (a b : Array Nat) : (#[a, b] : Array (Array Nat))[0]! = a := rfl
theorem lit2_1 (a b : Array Nat) : (#[a, b] : Array (Array Nat))[1]! = b := rfl

theorem trans_eq (j : Nat) (hj : j < 57) : heSevenTransporters[j]! = unpack 8330 14 (A (2 + j)) := by
  rw [heSevenTransporters, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn,
    show j + 2 = 2 + j by omega]
  exact arr_eq (2 + j) (by omega)

theorem repIx_lt (i : Nat) : repIx i < 75 := by
  unfold repIx
  cases Nat.beq i 0 <;> cases Nat.beq i 1 <;> decide

theorem reps_eq (i : Nat) (hi : i < 3) : heSevenReps[i]! = unpack 8330 14 (A (repIx i)) := by
  rw [heSevenReps, heSevenC0Gens, heSevenC1Gens, heSevenC2Gens, lit3_0, lit3_0, lit3_0]
  interval_cases i
  · rw [lit3_0]
    exact arr_eq 59 (by norm_num)
  · rw [lit3_1]
    exact arr_eq 65 (by norm_num)
  · rw [lit3_2]
    exact arr_eq 70 (by norm_num)

theorem rec_lt : ∀ j < 57, heSevenRec.getD j 0 < 3 := by decide

@[expose] noncomputable def lp (j : Nat) : Equiv.Perm (Fin 8330) :=
  gp (2 + j) * gp (repIx (rc j)) * (gp (2 + j))⁻¹

theorem repF_ln (j : Nat) (hj : j < 57) : RepF 8330 (ln j) (lp j) := by
  have h := (repF_pa (2 + j) (by omega)).comp ((repF_pa (repIx (rc j)) (repIx_lt _)).comp
    (repF_pi (2 + j) (by omega)))
  rw [lp, mul_assoc]
  exact h

theorem rep_line (j : Nat) (hj : j < 57) : Rep 8330 heSevenLines[j]! (lp j) := by
  rw [heSevenLines, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  change Rep 8330 (conjA 8330 heSevenTransporters[j]! heSevenReps[heSevenRec.getD j 0 % 3]!) _
  rw [trans_eq j hj, reps_eq _ (Nat.mod_lt _ (by norm_num))]
  have hv := CFSG.RankThree.Native.F2.validA_of_rep (rep_gp (2 + j) (by omega))
  have h := rep_conjA hv (rep_gp (repIx (heSevenRec.getD j 0 % 3)) (repIx_lt _))
  rw [CFSG.RankThree.Native.permOfArr_eq_of_rep (rep_gp (2 + j) (by omega))] at h
  exact h

theorem bs_lt : ∀ b ∈ bs, b < 8330 := by decide

theorem faithful :
    ∀ x ∈ heAutGroup, ∀ y ∈ heAutGroup, (x ∈ heP ↔ y ∈ heP) →
      (∀ b (hb : b ∈ bs), (x ⟨b, bs_lt b hb⟩ : Nat) = y ⟨b, bs_lt b hb⟩) → x = y := by
  intro x hx y hy hxy hb
  refine he_eq_of_base hx hy hxy fun b hb5 => Fin.ext ?_
  have hm : (b : Nat) ∈ bs := by
    simp only [bs, List.mem_cons, List.not_mem_nil, or_false]
    omega
  exact hb b hm

theorem eq_of_P
    {f f' : Nat → Nat} {x y : Equiv.Perm (Fin 8330)} (hf : RepF 8330 f x) (hf' : RepF 8330 f' y)
    (hx : x ∈ heP) (hy : y ∈ heP) (h : eqOnL bs f f' = true) : x = y :=
  faithful x (heP_le_heAutGroup hx) y (heP_le_heAutGroup hy) (iff_of_true hx hy) fun b hb => by
    rw [← hf b (bs_lt b hb), ← hf' b (bs_lt b hb)]
    exact (eqOnL_iff _ _ _).1 h b hb

end CertificateChecks.KernelHeLoc.Seven

end
