module

public import Certificates.Kernel.HN3166.Seed
public import CFSG.Certificates.Kernel.Orders.HN.Data.Sel
public import CFSG.Certificates.Kernel.Orders.HN.Checks.D
public import CFSG.Certificates.Kernel.Orders.HN.Checks.K
public import CFSG.Certificates.Kernel.Orders.HN.Checks.O
public import CFSG.Certificates.Kernel.Orders.HN.Checks.S2
public import CFSG.Certificates.Kernel.Orders.HN.Checks.S3
public import CFSG.Certificates.Kernel.Orders.HN.Checks.S5
public import CFSG.Certificates.Kernel.Orders.HN.Checks.W0
public import CFSG.Certificates.Kernel.Orders.HN.Checks.W1
public import CFSG.Certificates.Kernel.Orders.HN.Checks.W2
public import CFSG.Certificates.Kernel.Orders.HN.Checks.W3
public import CFSG.Certificates.Kernel.Orders.HN.Checks.W4
public import CFSG.Certificates.Kernel.Orders.HN.Checks.W5
public import CFSG.Certificates.Kernel.Orders.HN.Checks.W6
public import CFSG.Certificates.Kernel.Orders.HN.Checks.W7
public import CFSG.Certificates.Kernel.J4Hub.PcSound
public import CFSG.Certificates.Kernel.J4Hub.FlagSound
public import CFSG.Certificates.Kernel.J4Hub.SlpChain
import Certificates.Kernel.HN3166.Bytes
import Certificates.Kernel.Sporadic.OrdCommon
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness
import all CFSG.Blueprint.NativeSporadic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHN

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KS.J4Hub CFSG.Sporadic.F5

local notation "Dt" => CFSG.Sporadic.HN.Native.hnData

noncomputable abbrev OMUL : Nat → Nat → Nat :=
  mulR 5 13 1729 133 9 CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CFSG.KD.OrdHN.CM CFSG.KD.OrdHN.RM

noncomputable abbrev OVM : Nat → Nat → Nat :=
  vecR 5 13 1729 133 9 CFSG.KD.OrdHN.LV CFSG.KD.OrdHN.HV CFSG.KD.OrdHN.RM

open CFSG.KD.OrdHN in
theorem o_mA : mA Dt = ordMat 5 (Dt).d 13 1729 (RW 1) := by
  have h := seed_sound (hnb := rfl) (Cs := List.range 71) consts ord1_bytes rfl d1 d1_end
  change CFSG.Blueprint.NativeSporadic.decode 5 133 1 CFSG.Sporadic.HN.Native.seedA = _
  rw [CFSG.KD.BrHN.HNSeedA.eq, h]
  rfl

open CFSG.KD.OrdHN in
theorem o_mB : mB Dt = ordMat 5 (Dt).d 13 1729 (RW 2) := by
  have h := seed_sound (hnb := rfl) (Cs := List.range 71) consts ord2_bytes rfl d2 d2_end
  change CFSG.Blueprint.NativeSporadic.decode 5 133 1 CFSG.Sporadic.HN.Native.seedB = _
  rw [CFSG.KD.BrHN.HNSeedB.eq, h]
  rfl

open CFSG.KD.OrdHN in
theorem o_regs3 : RegsIn 5 (Dt).d 13 1729 229957 L H (J Dt) RW 3 := by
  intro r h0 h3
  obtain rfl | rfl : r = 1 ∨ r = 2 := by omega
  · exact ⟨(andT' (andT' d1_end).2).2, _, gA_mem, o_mA⟩
  · exact ⟨(andT' (andT' d2_end).2).2, _, gB_mem, o_mB⟩

#kc_forall_chunks W.all (fun j => CFSG.KD.OrdHN.wsC j = true) 8 CFSG.KD.OrdHN.wsC 1

open CFSG.KD.OrdHN in
theorem o_regs : RegsIn 5 (Dt).d 13 1729 229957 L H (J Dt) RW 799 :=
  slp_chain (nb := 229957) consts rfl (fun j => WS.getD j []) (fun j => WSt.getD j 0) 8 W.all
    (by decide) o_regs3

theorem blk_of {PT : Nat → Nat → Nat} {PR n q BL b : Nat} {TC SC : List (List Nat)}
    {N SS : List Nat}
    (hbf : blkBF CFSG.KD.OrdHN.RW OVM (validM 5 1729 CFSG.KD.OrdHN.LV CFSG.KD.OrdHN.HV) PR BL n PT b
      = true)
    (hbt : blkBT CFSG.KD.OrdHN.RW OVM PR BL n PT TC N b = true) (hbs : blkBS PT N SC SS b = true)
    (hbn : blkBN q BL N SS b = true) :
    ∃ PT : Nat → Nat, ∃ TC SC : List Nat, ∃ SS : Nat,
      baseFixed CFSG.KD.OrdHN.RW OVM (validM 5 1729 CFSG.KD.OrdHN.LV CFSG.KD.OrdHN.HV) PR (PT 0)
        (blkTo BL b) n = true ∧
      Nat.beq (runTree CFSG.KD.OrdHN.RW PT OVM PR (blkFr BL b) n TC 2)
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

open CFSG.KD.OrdHN in
theorem s2_blocks : BlocksOK 5 133 13 1729 9 RM LV HV RW
    (nat_lit 0x153014a013d01340127011a010f010200fb00f300e900e100d500cc) 14 2 7
    (nat_lit 0xe0d0d0b0b090904040202010100) :=
  ⟨s2_bl, fun b hb => blk_of (S2.BF.all b hb) (S2.BT.all b hb) (S2.BS.all b hb) (S2.BN.all b hb)⟩

open CFSG.KD.OrdHN in
theorem s3_blocks : BlocksOK 5 133 13 1729 9 RM LV HV RW (nat_lit 0x1e101de01d901d401ce01cb) 6 3 3
    (nat_lit 0x60404020200) :=
  ⟨s3_bl, fun b hb => blk_of (S3.BF.all b hb) (S3.BT.all b hb) (S3.BS.all b hb) (S3.BN.all b hb)⟩

open CFSG.KD.OrdHN in
theorem s5_blocks : BlocksOK 5 133 13 1729 9 RM LV HV RW (nat_lit 0x2ca02bf02af02a8029f0293) 6 5 3
    (nat_lit 0x60303010100) :=
  ⟨s5_bl, fun b hb => blk_of (S5.BF.all b hb) (S5.BT.all b hb) (S5.BS.all b hb) (S5.BN.all b hb)⟩

open CFSG.KD.OrdHN in
theorem sylow2 : 2 ^ 14 ∣ Nat.card (J Dt) :=
  sylowPc_sound' (nb := nat_lit 229957) (hnb := rfl) (PR := S2.PR) (PW := S2.PW) (n := nat_lit 14)
    (pb := nat_lit 1) (Cs := S2.PC) consts o_regs Nat.prime_two s2_pr s2_pw s2_pc s2_blocks

open CFSG.KD.OrdHN in
theorem sylow3 : 3 ^ 6 ∣ Nat.card (J Dt) :=
  sylowPc_sound' (nb := nat_lit 229957) (hnb := rfl) (PR := S3.PR) (PW := S3.PW) (n := nat_lit 6)
    (pb := nat_lit 2) (Cs := S3.PC) consts o_regs Nat.prime_three s3_pr s3_pw s3_pc
    s3_blocks

open CFSG.KD.OrdHN in
theorem sylow5 : 5 ^ 6 ∣ Nat.card (J Dt) :=
  sylowFlag_sound' (nb := nat_lit 229957) (hnb := rfl) consts o_regs (by norm_num) s5_pr s5_fl
    s5_uni_0 s5_blocks

theorem prime_dvd {r q : Nat} (hq : q.Prime) (hq' : q < 65536) (h0 : 0 < r) (h1 : r < 799)
    (h : primeOK CFSG.KD.OrdHN.RW OMUL CFSG.KD.OrdHN.ONE 799 r q = true) :
    q ∣ Nat.card (J Dt) := by
  obtain ⟨hv, g, hg, hgm⟩ := o_regs r h0 h1
  have hps := prime_sound' (hnb := rfl) CFSG.KD.OrdHN.consts hq' hv h
  have hp : ordMat 5 (Dt).d 13 1729 (CFSG.KD.OrdHN.RW r) ^ q = 1 := hps.1
  have hne : ordMat 5 (Dt).d 13 1729 (CFSG.KD.OrdHN.RW r) ≠ 1 := hps.2
  have hpow : (⟨g, hg⟩ : J Dt) ^ q = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, hgm, hp]
    rfl
  have hne1 : (⟨g, hg⟩ : J Dt) ≠ 1 := by
    intro e
    apply hne
    have hg1 : g = 1 := congrArg Subtype.val e
    rw [← hgm, hg1]
    rfl
  have := orderOf_eq_prime (hp := ⟨hq⟩) hpow hne1
  rw [← this]
  exact orderOf_dvd_natCard _

theorem card_dvd : 273030912000000 ∣ Nat.card (J Dt) := by
  have h7 := prime_dvd (by norm_num) (by norm_num) (by norm_num) (by norm_num) CFSG.KD.OrdHN.o7
  have h11 := prime_dvd (by norm_num) (by norm_num) (by norm_num) (by norm_num) CFSG.KD.OrdHN.o11
  have h19 := prime_dvd (by norm_num) (by norm_num) (by norm_num) (by norm_num) CFSG.KD.OrdHN.o19
  have e : (273030912000000 : ℕ) = 2 ^ 14 * 3 ^ 6 * 5 ^ 6 * 7 * 11 * 19 := by norm_num
  rw [e]
  refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) ?_ h19
  refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) ?_ h11
  refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) ?_ h7
  refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) ?_ sylow5
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) sylow2 sylow3

end CertificateChecks.KernelHN

end
