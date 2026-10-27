module

public import Certificates.Kernel.J4Hub.Fam
public import CFSG.Certificates.Kernel.Orders.J4.Checks.W0
public import CFSG.Certificates.Kernel.Orders.J4.Checks.W1
public import CFSG.Certificates.Kernel.Orders.J4.Checks.W2
public import CFSG.Certificates.Kernel.Orders.J4.Checks.W3
public import CFSG.Certificates.Kernel.Orders.J4.Checks.W4
public import CFSG.Certificates.Kernel.Orders.J4.Checks.W5
public import CFSG.Certificates.Kernel.Orders.J4.Checks.W6
public import CFSG.Certificates.Kernel.Orders.J4.Checks.W7
public import CFSG.Certificates.Kernel.Orders.J4.Checks.S2
public import CFSG.Certificates.Kernel.Orders.J4.Checks.S3
public import CFSG.Certificates.Kernel.Orders.J4.Checks.S11
public import CFSG.Certificates.Kernel.Orders.J4.Checks.O
public import CFSG.Certificates.Kernel.J4Hub.SlpChain
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.J4Hub.PcSound
import CFSG.Certificates.Kernel.J4Hub.FlagSound
import CFSG.Open.Defs

public section

namespace CertificateChecks.KernelJ4Hub

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KS.J4Hub CFSG.Sporadic.J4

noncomputable abbrev OMUL : Nat → Nat → Nat :=
  mulR 2 8 896 112 6 CFSG.KD.OrdJ4.L CFSG.KD.OrdJ4.H CFSG.KD.OrdJ4.CM CFSG.KD.OrdJ4.RM

noncomputable abbrev OV : Nat → Bool := validM 2 100352 CFSG.KD.OrdJ4.L CFSG.KD.OrdJ4.H

theorem ord_v1 : OV (CFSG.KD.OrdJ4.RW 1) = true := (andB_true (andB_true CFSG.KD.OrdJ4.d1_end).2).2
theorem ord_v2 : OV (CFSG.KD.OrdJ4.RW 2) = true := (andB_true (andB_true CFSG.KD.OrdJ4.d2_end).2).2

theorem oregs3 : RegsIn 2 112 8 896 100352 CFSG.KD.OrdJ4.L CFSG.KD.OrdJ4.H J CFSG.KD.OrdJ4.RW 3 := by
  intro r h0 h3
  obtain rfl | rfl : r = 1 ∨ r = 2 := by omega
  · exact ⟨ord_v1, gA, Subgroup.subset_closure (Set.mem_insert _ _), by rw [gA_val', matA, ord_A]⟩
  · exact ⟨ord_v2, gB, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl),
      by rw [gB_val', matB, ord_B]⟩

#kc_forall_chunks W.all (fun j => CFSG.KD.OrdJ4.wsC j = true) 8 CFSG.KD.OrdJ4.wsC 1

open CFSG.KD.OrdJ4 in
theorem ord_regs : RegsIn 2 112 8 896 100352 L H J RW 3623 :=
  slp_chain (nb := 100352) consts rfl (fun j => WS.getD j []) (fun j => WSt.getD j 0) 8 W.all
    (by decide) oregs3

noncomputable abbrev OVM : Nat → Nat → Nat :=
  vecR 2 8 896 112 6 CFSG.KD.OrdJ4.LV CFSG.KD.OrdJ4.HV CFSG.KD.OrdJ4.RM

theorem blk_of {PT : Nat → Nat → Nat} {PR n q BL b : Nat} {TC SC : List (List Nat)}
    {N SS : List Nat}
    (hbf : blkBF CFSG.KD.OrdJ4.RW OVM (validM 2 896 CFSG.KD.OrdJ4.LV CFSG.KD.OrdJ4.HV) PR BL n PT b
      = true)
    (hbt : blkBT CFSG.KD.OrdJ4.RW OVM PR BL n PT TC N b = true) (hbs : blkBS PT N SC SS b = true)
    (hbn : blkBN q BL N SS b = true) :
    ∃ PT : Nat → Nat, ∃ TC SC : List Nat, ∃ SS : Nat,
      baseFixed CFSG.KD.OrdJ4.RW OVM (validM 2 896 CFSG.KD.OrdJ4.LV CFSG.KD.OrdJ4.HV) PR (PT 0)
        (blkTo BL b) n = true ∧
      Nat.beq (runTree CFSG.KD.OrdJ4.RW PT OVM PR (blkFr BL b) n TC 2)
        (Nat.succ (q ^ (blkTo BL b - blkFr BL b))) = true ∧
      Nat.beq (runSorted PT (q ^ (blkTo BL b - blkFr BL b)) SC 1) SS = true ∧
      sortedAll (q ^ (blkTo BL b - blkFr BL b)) SS = true := by
  obtain ⟨h1, h2⟩ := andB_true hbn
  have hN : N.getD b 0 = q ^ (blkTo BL b - blkFr BL b) := Nat.eq_of_beq_eq_true h2
  refine ⟨PT b, TC.getD b [], SC.getD b [], SS.getD b 0, hbf, ?_, ?_, ?_⟩
  · rw [← hN]
    exact hbt
  · rw [← hN]
    exact hbs
  · rw [← hN]
    exact h1

open CFSG.KD.OrdJ4 in
theorem s2_blocks : BlocksOK 2 112 8 896 6 RM LV HV RW
    (nat_lit 0x876086f0864085d085208470832081f080c07ff07ea07df07c807bd07b007a207960781077407690754) 21 2 16
    (nat_lit 0x15141413131212111110100f0f0e0e0d0d0c0c0b0b0606050503030202010100) :=
  ⟨s2_bl, fun b hb => blk_of (S2.BF.all b hb) (S2.BT.all b hb) (S2.BS.all b hb) (S2.BN.all b hb)⟩

open CFSG.KD.OrdJ4 in
theorem s3_blocks : BlocksOK 2 112 8 896 6 RM LV HV RW (nat_lit 0xb120d1a0d19) 3 3 3
    (nat_lit 0x30202010100) :=
  ⟨s3_bl, fun b hb => blk_of (S3.BF.all b hb) (S3.BT.all b hb) (S3.BS.all b hb) (S3.BN.all b hb)⟩

open CFSG.KD.OrdJ4 in
theorem s11_blocks : BlocksOK 2 112 8 896 6 RM LV HV RW (nat_lit 0xd8c0d840d80) 3 11 2
    (nat_lit 0x3020200) :=
  ⟨s11_bl, fun b hb =>
    blk_of (S11.BF.all b hb) (S11.BT.all b hb) (S11.BS.all b hb) (S11.BN.all b hb)⟩

theorem sylow2 : 2 ^ 21 ∣ Nat.card J :=
  sylowFlag_sound' (hnb := rfl) CFSG.KD.OrdJ4.consts ord_regs Nat.prime_two CFSG.KD.OrdJ4.s2_pr
    CFSG.KD.OrdJ4.s2_fl CFSG.KD.OrdJ4.s2_uni_0 s2_blocks

theorem sylow3 : 3 ^ 3 ∣ Nat.card J :=
  sylowPc_sound' (hnb := rfl) (PR := CFSG.KD.OrdJ4.S3.PR) (PW := CFSG.KD.OrdJ4.S3.PW) (n := 3)
    (pb := 2) (Cs := CFSG.KD.OrdJ4.S3.PC) CFSG.KD.OrdJ4.consts ord_regs Nat.prime_three
    CFSG.KD.OrdJ4.s3_pr
    CFSG.KD.OrdJ4.s3_pw CFSG.KD.OrdJ4.s3_pc s3_blocks

theorem sylow11 : 11 ^ 3 ∣ Nat.card J :=
  sylowPc_sound' (hnb := rfl) (PR := CFSG.KD.OrdJ4.S11.PR) (PW := CFSG.KD.OrdJ4.S11.PW) (n := 3)
    (pb := 4) (Cs := CFSG.KD.OrdJ4.S11.PC) (q := 11) CFSG.KD.OrdJ4.consts ord_regs (by norm_num)
    CFSG.KD.OrdJ4.s11_pr
    CFSG.KD.OrdJ4.s11_pw CFSG.KD.OrdJ4.s11_pc s11_blocks

theorem prime_dvd {r q : Nat} (hq : q.Prime) (hq' : q < 65536) (h0 : 0 < r) (h1 : r < 3623)
    (h : primeOK CFSG.KD.OrdJ4.RW OMUL CFSG.KD.OrdJ4.ONE 3623 r q = true) : q ∣ Nat.card J := by
  obtain ⟨hv, g, hg, hgm⟩ := ord_regs r h0 h1
  obtain ⟨hp, hne⟩ := prime_sound' (hnb := rfl) CFSG.KD.OrdJ4.consts hq' hv h
  have hpow : (⟨g, hg⟩ : J) ^ q = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, hgm, hp]
    rfl
  have hne1 : (⟨g, hg⟩ : J) ≠ 1 := by
    intro e
    apply hne
    rw [← hgm, show g = 1 from congrArg Subtype.val e]
    rfl
  have := orderOf_eq_prime (hp := ⟨hq⟩) hpow hne1
  rw [← this]
  exact orderOf_dvd_natCard _

theorem card_dvd : 86775571046077562880 ∣ Nat.card J := by
  have h5 := prime_dvd (by norm_num) (by norm_num) (by norm_num) (by norm_num) CFSG.KD.OrdJ4.o5
  have h7 := prime_dvd (by norm_num) (by norm_num) (by norm_num) (by norm_num) CFSG.KD.OrdJ4.o7
  have h23 := prime_dvd (by norm_num) (by norm_num) (by norm_num) (by norm_num) CFSG.KD.OrdJ4.o23
  have h29 := prime_dvd (by norm_num) (by norm_num) (by norm_num) (by norm_num) CFSG.KD.OrdJ4.o29
  have h31 := prime_dvd (by norm_num) (by norm_num) (by norm_num) (by norm_num) CFSG.KD.OrdJ4.o31
  have h37 := prime_dvd (by norm_num) (by norm_num) (by norm_num) (by norm_num) CFSG.KD.OrdJ4.o37
  have h43 := prime_dvd (by norm_num) (by norm_num) (by norm_num) (by norm_num) CFSG.KD.OrdJ4.o43
  have e : (86775571046077562880 : ℕ) =
      2 ^ 21 * 3 ^ 3 * 11 ^ 3 * 5 * 7 * 23 * 29 * 31 * 37 * 43 := by norm_num
  rw [e]
  refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) ?_ h43
  refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) ?_ h37
  refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) ?_ h31
  refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) ?_ h29
  refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) ?_ h23
  refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) ?_ h7
  refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) ?_ h5
  refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) ?_ sylow11
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) sylow2 sylow3

end CertificateChecks.KernelJ4Hub

end
