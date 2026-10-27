module

public import Certificates.Kernel.J4Q.MaskU
public import Certificates.Kernel.J4Q.MaskBlkData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q

@[expose] noncomputable def getBL (l : List (List (List Nat))) (i : Nat) : List (List Nat) :=
  List.rec (motive := fun _ => Nat → List (List Nat)) (fun _ => List.nil)
    (fun m _ ih i => Nat.rec (motive := fun _ => List (List Nat)) m (fun j _ => ih j) i) l i

theorem getBL_eq : ∀ (l : List (List (List Nat))) (i : Nat), getBL l i = l.getD i []
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => getBL_eq l i

@[expose] noncomputable def tabAt (e : Nat) : List Nat := getL (getBL mkTLB (e / 32)) (e % 32)

theorem blk_chk : (mkTL == mkTLB.flatten && mkTLB.all fun b => b.length == 32) = true := by
  quickRfl

theorem getD_flatten {α : Type} (d : α) : ∀ (B : List (List α)), (∀ b ∈ B, b.length = 32) →
    ∀ (q r : Nat), r < 32 → B.flatten.getD (32 * q + r) d = (B.getD q []).getD r d
  | [], _, q, r, _ => by simp
  | b :: B, hB, q, r, hr => by
    have hb : b.length = 32 := hB b List.mem_cons_self
    rw [List.flatten_cons]
    rcases q with _ | q
    · rw [Nat.mul_zero, Nat.zero_add, List.getD_cons_zero, List.getD_eq_getElem?_getD,
        List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
    · have h := getD_flatten d B (fun c hc => hB c (List.mem_cons_of_mem _ hc)) q r hr
      have hi : 32 * (q + 1) + r - b.length = 32 * q + r := by omega
      rw [List.getD_cons_succ, ← h, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by omega), hi]

theorem tabAt_eq {e : Nat} (_he : e < 1024) : tabAt e = mkTL.getD e [] := by
  have h := blk_chk
  rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  unfold tabAt
  rw [getL_eq, getBL_eq, h.1, ← getD_flatten [] mkTLB (fun b hb => beq_iff_eq.1 (h.2 b hb)) (e / 32)
    (e % 32) (Nat.mod_lt _ (by decide)), Nat.div_add_mod]

end CertificateChecks.KernelJ4Q

end
