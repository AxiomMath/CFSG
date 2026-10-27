module

public import Certificates.Kernel.Ly3085.Seed
public import CFSG.Certificates.Kernel.Orders.Ly.Data.Sel
public import CFSG.Certificates.Kernel.Orders.Ly.Checks.D
public import CFSG.Certificates.Kernel.Orders.Ly.Checks.K
public import CFSG.Certificates.Kernel.Orders.Ly.Checks.O
public import CFSG.Certificates.Kernel.Orders.Ly.Checks.S2
public import CFSG.Certificates.Kernel.Orders.Ly.Checks.S3
public import CFSG.Certificates.Kernel.Orders.Ly.Checks.S5
public import CFSG.Certificates.Kernel.Orders.Ly.Checks.W0
public import CFSG.Certificates.Kernel.Orders.Ly.Checks.W1
public import CFSG.Certificates.Kernel.Orders.Ly.Checks.W2
public import CFSG.Certificates.Kernel.Orders.Ly.Checks.W3
public import CFSG.Certificates.Kernel.Orders.Ly.Checks.W4
public import CFSG.Certificates.Kernel.Orders.Ly.Checks.W5
public import CFSG.Certificates.Kernel.Orders.Ly.Checks.W6
public import CFSG.Certificates.Kernel.Orders.Ly.Checks.W7
public import CFSG.Certificates.Kernel.J4Hub.PcSound
public import CFSG.Certificates.Kernel.J4Hub.FlagSound
public import CFSG.Certificates.Kernel.J4Hub.SlpChain
import Certificates.Kernel.Ly3085.Bytes
import Certificates.Kernel.Sporadic.OrdCommon
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness
import all CFSG.Blueprint.NativeSporadic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLy

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KS.J4Hub CFSG.Sporadic.Ly

noncomputable abbrev OMUL : Nat → Nat → Nat :=
  mulR 5 12 1332 111 8 CFSG.KD.OrdLy.L CFSG.KD.OrdLy.H CFSG.KD.OrdLy.CM CFSG.KD.OrdLy.RM

noncomputable abbrev OVM : Nat → Nat → Nat :=
  vecR 5 12 1332 111 8 CFSG.KD.OrdLy.LV CFSG.KD.OrdLy.HV CFSG.KD.OrdLy.RM

open CFSG.KD.OrdLy in
theorem o_mA : sA = ordMat 5 111 12 1332 (RW 1) := by
  have h := seed_sound (hnb := rfl) (Cs := List.range 71) consts ord1_bytes rfl d1 d1_end
  change CFSG.Blueprint.NativeSporadic.decode 5 111 1 CFSG.Blueprint.NativeSporadic.LySeed1 = _
  rw [CFSG.KD.BrLy.LySeedA.eq, h]

open CFSG.KD.OrdLy in
theorem o_mB : sB = ordMat 5 111 12 1332 (RW 2) := by
  have h := seed_sound (hnb := rfl) (Cs := List.range 71) consts ord2_bytes rfl d2 d2_end
  change CFSG.Blueprint.NativeSporadic.decode 5 111 1 CFSG.Blueprint.NativeSporadic.LySeed2 = _
  rw [CFSG.KD.BrLy.LySeedB.eq, h]

open CFSG.KD.OrdLy in
theorem o_regs3 : RegsIn 5 111 12 1332 147852 L H JS RW 3 := by
  intro r h0 h3
  obtain rfl | rfl : r = 1 ∨ r = 2 := by omega
  · exact ⟨(andT' (andT' d1_end).2).2, _, (aS det_sA).2, o_mA⟩
  · exact ⟨(andT' (andT' d2_end).2).2, _, (bS det_sB).2, o_mB⟩

#kc_forall_chunks W.all (fun j => CFSG.KD.OrdLy.wsC j = true) 8 CFSG.KD.OrdLy.wsC 1

open CFSG.KD.OrdLy in
theorem o_regs : RegsIn 5 111 12 1332 147852 L H JS RW 5418 :=
  slp_chain (nb := 147852) consts rfl (fun j => WS.getD j []) (fun j => WSt.getD j 0) 8 W.all
    (by decide) o_regs3

theorem blk_of {PT : Nat → Nat → Nat} {PR n q BL b : Nat} {TC SC : List (List Nat)}
    {N SS : List Nat}
    (hbf : blkBF CFSG.KD.OrdLy.RW OVM (validM 5 1332 CFSG.KD.OrdLy.LV CFSG.KD.OrdLy.HV) PR BL n PT b
      = true)
    (hbt : blkBT CFSG.KD.OrdLy.RW OVM PR BL n PT TC N b = true) (hbs : blkBS PT N SC SS b = true)
    (hbn : blkBN q BL N SS b = true) :
    ∃ PT : Nat → Nat, ∃ TC SC : List Nat, ∃ SS : Nat,
      baseFixed CFSG.KD.OrdLy.RW OVM (validM 5 1332 CFSG.KD.OrdLy.LV CFSG.KD.OrdLy.HV) PR (PT 0)
        (blkTo BL b) n = true ∧
      Nat.beq (runTree CFSG.KD.OrdLy.RW PT OVM PR (blkFr BL b) n TC 2)
        (Nat.succ (q ^ (blkTo BL b - blkFr BL b))) = true ∧
      Nat.beq (runSorted PT (q ^ (blkTo BL b - blkFr BL b)) SC 1) SS = true ∧
      sortedAll (q ^ (blkTo BL b - blkFr BL b)) SS = true := by
  obtain ⟨h1, h2⟩ := andT' hbn
  have hN : N.getD b 0 = q ^ (blkTo BL b - blkFr BL b) := Nat.eq_of_beq_eq_true h2
  refine ⟨PT b, TC.getD b [], SC.getD b [], SS.getD b 0, hbf, ?_, ?_, ?_⟩
  · rw [← hN]
    exact hbt
  · rw [← hN]
    exact hbs
  · rw [← hN]
    exact h1

open CFSG.KD.OrdLy in
theorem s2_blocks : BlocksOK 5 111 12 1332 8 RM LV HV RW (nat_lit 0x9fd09f509f309f009ee09e809e609df)
    8 2 7 (nat_lit 0x807070606050504040303020200) :=
  ⟨s2_bl, fun b hb => blk_of (S2.BF.all b hb) (S2.BT.all b hb) (S2.BS.all b hb) (S2.BN.all b hb)⟩

open CFSG.KD.OrdLy in
theorem s3_blocks : BlocksOK 5 111 12 1332 8 RM LV HV RW (nat_lit 0x12ff12fa12f512f212ed12e812e6)
    7 3 5 (nat_lit 0x7060605050404010100) :=
  ⟨s3_bl, fun b hb => blk_of (S3.BF.all b hb) (S3.BT.all b hb) (S3.BS.all b hb) (S3.BN.all b hb)⟩

open CFSG.KD.OrdLy in
theorem s5_blocks : BlocksOK 5 111 12 1332 8 RM LV HV RW (nat_lit 0x14de14da14ca14c514bc14ad)
    6 5 5 (nat_lit 0x6050504040303010100) :=
  ⟨s5_bl, fun b hb => blk_of (S5.BF.all b hb) (S5.BT.all b hb) (S5.BS.all b hb) (S5.BN.all b hb)⟩

open CFSG.KD.OrdLy in
theorem sylow2 : 2 ^ 8 ∣ Nat.card JS :=
  sylowPc_sound' (nb := nat_lit 147852) (hnb := rfl) (PR := S2.PR) (PW := S2.PW) (n := 8) (pb := 1)
    (Cs := S2.PC) (q := 2) consts o_regs Nat.prime_two s2_pr s2_pw s2_pc
    s2_blocks

open CFSG.KD.OrdLy in
theorem sylow3 : 3 ^ 7 ∣ Nat.card JS :=
  sylowPc_sound' (nb := nat_lit 147852) (hnb := rfl) (PR := S3.PR) (PW := S3.PW) (n := 7) (pb := 2)
    (Cs := S3.PC) (q := 3) consts o_regs Nat.prime_three s3_pr s3_pw s3_pc
    s3_blocks

open CFSG.KD.OrdLy in
theorem sylow5 : 5 ^ 6 ∣ Nat.card JS :=
  sylowFlag_sound' (nb := nat_lit 147852) (hnb := rfl) consts o_regs (by norm_num) s5_pr s5_fl
    s5_uni_0 s5_blocks

theorem prime_dvd {r q : Nat} (hq : q.Prime) (hq' : q < 65536) (h0 : 0 < r) (h1 : r < 5418)
    (h : primeOK CFSG.KD.OrdLy.RW OMUL CFSG.KD.OrdLy.ONE 5418 r q = true) :
    q ∣ Nat.card JS := by
  obtain ⟨hv, g, hg, hgm⟩ := o_regs r h0 h1
  have hps := prime_sound' (hnb := rfl) CFSG.KD.OrdLy.consts hq' hv h
  have hp : ordMat 5 111 12 1332 (CFSG.KD.OrdLy.RW r) ^ q = 1 := hps.1
  have hne : ordMat 5 111 12 1332 (CFSG.KD.OrdLy.RW r) ≠ 1 := hps.2
  have hpow : (⟨g, hg⟩ : JS) ^ q = 1 := by
    apply matS_injective
    rw [matS_pow, matS_one]
    change ((g : GL (Fin 111) (ZMod 5)) : Matrix (Fin 111) (Fin 111) (ZMod 5)) ^ q = 1
    rw [hgm, hp]
  have hne1 : (⟨g, hg⟩ : JS) ≠ 1 := by
    intro e
    apply hne
    have hg1 : g = 1 := congrArg Subtype.val e
    rw [← hgm, hg1]
    rfl
  have := orderOf_eq_prime (hp := ⟨hq⟩) hpow hne1
  rw [← this]
  exact orderOf_dvd_natCard _

theorem card_dvd : 51765179004000000 ∣ Nat.card JS := by
  have h7 := prime_dvd (by norm_num) (by norm_num) (by norm_num) (by norm_num) CFSG.KD.OrdLy.o7
  have h11 := prime_dvd (by norm_num) (by norm_num) (by norm_num) (by norm_num) CFSG.KD.OrdLy.o11
  have h31 := prime_dvd (by norm_num) (by norm_num) (by norm_num) (by norm_num) CFSG.KD.OrdLy.o31
  have h37 := prime_dvd (by norm_num) (by norm_num) (by norm_num) (by norm_num) CFSG.KD.OrdLy.o37
  have h67 := prime_dvd (by norm_num) (by norm_num) (by norm_num) (by norm_num) CFSG.KD.OrdLy.o67
  have e : (51765179004000000 : ℕ) = 2 ^ 8 * 3 ^ 7 * 5 ^ 6 * 7 * 11 * 31 * 37 * 67 := by norm_num
  rw [e]
  refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) ?_ h67
  refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) ?_ h37
  refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) ?_ h31
  refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) ?_ h11
  refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) ?_ h7
  refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) ?_ sylow5
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) sylow2 sylow3

end CertificateChecks.KernelLy

end
