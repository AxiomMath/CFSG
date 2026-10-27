module

public import Certificates.Kernel.HeLoc.FiveLQ
public import Certificates.Kernel.HeLoc.Mem

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHeLoc.FiveL

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.HeLoc
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB CFSG.RankThree.Native
open CFSG.RankThree.PartOne CertificateChecks.KernelSpor

theorem arr_eq (k : Nat) (hk : k < 13) : heFiveArr k = unpack 8330 14 (A k) := Five.arr_eq k hk

theorem lit2_0 (a b : Array Nat) : (#[a, b] : Array (Array Nat))[0]! = a := rfl
theorem lit2_1 (a b : Array Nat) : (#[a, b] : Array (Array Nat))[1]! = b := rfl

@[expose] noncomputable def gp (k : Nat) : Equiv.Perm (Fin 8330) :=
  permOfArr 8330 (unpack 8330 14 (A k))

theorem perm_k (k : Nat) (hk : k < 13) :
    permOK 8330 14 (mask 14) (8330 * 14) (A k) (AI k) = true := allN_spec kPerm k hk

theorem rep_gp (k : Nat) (hk : k < 13) : Rep 8330 (unpack 8330 14 (A k)) (gp k) :=
  (rep_permOfArr (invEqK_sound (n := 8330) (w := 14) (p := A k) (r := AI k) (perm_k k hk)).2).1

theorem rep_gpi (k : Nat) (hk : k < 13) : Rep 8330 (unpack 8330 14 (AI k)) (gp k)⁻¹ :=
  (rep_permOfArr (invEqK_sound (n := 8330) (w := 14) (p := A k) (r := AI k) (perm_k k hk)).2).2

theorem repF_pa (k : Nat) (hk : k < 13) : RepF 8330 (pa k) (gp k) := Five.repF_of_rep (rep_gp k hk)

theorem repF_pi (k : Nat) (hk : k < 13) : RepF 8330 (pi k) (gp k)⁻¹ :=
  Five.repF_of_rep (rep_gpi k hk)

theorem memB_k (k c : Nat) (hk : k < 13) (hc : c < 10) :
    memB (A k) (NF5.getD k 0) (FL5.getD k 0) c = true := by
  have e : memI (10 * k + c) = memB (A k) (NF5.getD k 0) (FL5.getD k 0) c := by
    unfold memI
    rw [show (10 * k + c) / 10 = k by omega, show (10 * k + c) % 10 = c by omega]
  rw [← e]
  exact M5.all _ (show 10 * k + c < 130 by omega)

theorem nf_k (k : Nat) (hk : k < 13) :
    nfValidK 5 HeC.LR (NF5.getD k 0) = true ∧ FL5.getD k 0 < 2 := by
  have h := allN_spec kNF k hk
  rw [bAnd_iff, Nat.blt_eq] at h
  exact h

theorem gp_mem (k : Nat)
    (hk : k < 13) : gp k ∈ heAutGroup ∧ (gp k ∈ heP ↔ FL5.getD k 0 = 0) :=
  (mem_of_memB (perm_k k hk) (nf_k k hk).1 (nf_k k hk).2 fun c hc => memB_k k c hk hc).2

theorem gp_inP (k : Nat)
    (hk : k < 13) (h : FL5.getD k 0 = 0) : gp k ∈ heP := (gp_mem k hk).2.2 h

theorem gp_one : gp 2 = 1 := by
  have hA : A 2 = pidn 8330 14 := Nat.eq_of_beq_eq_true kId
  refine (repF_pa 2 (by norm_num)).unique fun x hx => ?_
  rw [pa, hA, CFSG.KS.PF.pg_pidn (by norm_num) (by norm_num) hx]
  rfl

@[expose] noncomputable def lp (j : Nat) : Equiv.Perm (Fin 8330) :=
  gp (2 + j) * gp 8 * (gp (2 + j))⁻¹

theorem repF_ln (j : Nat) (hj : j < 6) : RepF 8330 (ln j) (lp j) := by
  have h := (repF_pa (2 + j) (by omega)).comp ((repF_pa 8 (by norm_num)).comp
    (repF_pi (2 + j) (by omega)))
  rw [lp, mul_assoc]
  exact h

theorem trans_eq (j : Nat) (hj : j < 6) : heFiveTransporters[j]! = unpack 8330 14 (A (2 + j)) := by
  rw [heFiveTransporters, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn,
    show j + 2 = 2 + j by omega]
  exact arr_eq (2 + j) (by omega)

theorem rec_zero : ∀ j < 6, heFiveRec.getD j 0 = 0 := by decide

theorem rep_x0 : Rep 8330 heFiveReps[0 % 1]! (gp 8) := by
  rw [heFiveReps, heFiveC0Gens]
  change Rep 8330 (heFiveArr 8) (gp 8)
  rw [arr_eq 8 (by norm_num)]
  exact rep_gp 8 (by norm_num)

theorem rep_line (j : Nat) (hj : j < 6) : Rep 8330 heFiveLines[j]! (lp j) := by
  rw [heFiveLines, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  change Rep 8330 (conjA 8330 heFiveTransporters[j]! heFiveReps[heFiveRec.getD j 0 % 1]!) _
  rw [trans_eq j hj, rec_zero j hj]
  have hv := CFSG.RankThree.Native.F2.validA_of_rep (rep_gp (2 + j) (by omega))
  have h := rep_conjA hv rep_x0
  rw [CFSG.RankThree.Native.permOfArr_eq_of_rep (rep_gp (2 + j) (by omega))] at h
  exact h

theorem fl_P : FL5.getD 0 0 = 0 ∧ FL5.getD 1 0 = 0 ∧ FL5.getD 8 0 = 0 ∧ FL5.getD 10 0 = 0 ∧
    FL5.getD 11 0 = 0 ∧ FL5.getD 9 0 = 1 ∧ FL5.getD 12 0 = 1 := by decide

theorem lp_inP (j : Nat)
    (hj : j < 6) : lp j ∈ heP := by
  have hh := (gp_mem (2 + j) (by omega)).1
  have hr := gp_inP 8 (by norm_num) fl_P.2.2.1
  rw [lp, he_mul_mem_iff (heAutGroup.mul_mem hh (heP_le_heAutGroup hr)) (heAutGroup.inv_mem hh),
    he_mul_mem_iff hh (heP_le_heAutGroup hr), inv_mem_iff]
  constructor
  · intro h
    exact h.2 hr
  · intro h
    exact ⟨fun _ => hr, fun _ => h⟩

end CertificateChecks.KernelHeLoc.FiveL

end
