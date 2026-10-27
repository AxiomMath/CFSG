module

public import Certificates.Kernel.Sporadic.OddCore.SuzBtSZG
public import Certificates.Kernel.Sporadic.OddCore.SuzBtCF
public import CFSG.Certificates.Kernel.Spor.BTupMSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzBtCG

open CFSG.KC.Enum CFSG.KS CFSG.KS.BTup CertificateChecks.KernelSpor
open CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.C1Model
open CFSG.Sporadic.SuzRecog.SuzL34Cert
open CertificateChecks.KernelSpor.SuzBtG CertificateChecks.KernelSpor.SuzBtZG
  CertificateChecks.KernelSpor.SuzBtSZG

theorem hcl : ∀ i < SuzBtS1.cnt, btClsK 4 SuzBtS1.cnt SuzBtS1C.r0 33 (mask 33) SuzBtL1.cnt
    SuzBtS1.K SuzBtS1.R SuzBtS1Z.RT SuzBtL1.K SuzBtS1C.TG SuzBtS1C.E i = true := by
  intro i hi
  have hi' := hi
  rw [SuzBtSF.kCnt] at hi'
  rcases Nat.lt_or_ge i 4096 with h1 | h1
  · rcases Nat.lt_or_ge i 2048 with h2 | h2
    · rcases Nat.lt_or_ge i 1024 with h3 | h3
      · exact CFSG.KS.BTup.btClsSl_spec SuzBtCF.kCl0 (by omega) (by omega) hi
      · exact CFSG.KS.BTup.btClsSl_spec SuzBtCF.kCl1 (by omega) (by omega) hi
    · rcases Nat.lt_or_ge i 3072 with h3 | h3
      · exact CFSG.KS.BTup.btClsSl_spec SuzBtCF.kCl2 (by omega) (by omega) hi
      · exact CFSG.KS.BTup.btClsSl_spec SuzBtCF.kCl3 (by omega) (by omega) hi
  · rcases Nat.lt_or_ge i 6144 with h2 | h2
    · rcases Nat.lt_or_ge i 5120 with h3 | h3
      · exact CFSG.KS.BTup.btClsSl_spec SuzBtCF.kCl4 (by omega) (by omega) hi
      · exact CFSG.KS.BTup.btClsSl_spec SuzBtCF.kCl5 (by omega) (by omega) hi
    · rcases Nat.lt_or_ge i 7168 with h3 | h3
      · exact CFSG.KS.BTup.btClsSl_spec SuzBtCF.kCl6 (by omega) (by omega) hi
      · exact CFSG.KS.BTup.btClsSl_spec SuzBtCF.kCl7 (by omega) (by omega) hi


theorem cls_bound : ∀ e : Equiv.Perm (Fin 1782), e ∈ decSubgroup s1pDecs → e * e = 1 →
    e ≠ 1 → e ∉ decSubgroup l1Decs → 9 ≤ Nat.card ↥{x : Equiv.Perm (Fin 1782) |
      ∃ g ∈ decSubgroup s1pDecs, x = g * e * g⁻¹} := by
  intro e he he2 he1 heL
  rw [← genSub_dec s1pDecs] at he ⊢
  rw [← genSub_dec l1Decs] at heL
  have hrZ : ∀ i < SuzBtS1.cnt, btRtK 4 4 SuzBtS1.cnt SuzBtS1Z.S SuzBtS1.R SuzBtS1.POS
      SuzBtS1Z.RT i = true := fun i hi => (half hi).elim
    (fun h => btRtSl_spec SuzBtSZF.kZRt0 (Nat.zero_le _) (by omega) hi)
    (fun h => btRtSl_spec SuzBtSZF.kZRt1 h.1 h.2 hi)
  exact btCls_sound hgS hpS hfixS hbS
    (fun j hj => mov_base hbS (hgS j hj) (CFSG.KS.Raw.Orb.allN_iff.1 SuzBtSZF.kZS j hj)) hrZ
    (by norm_num) SuzBtSF.kHd SuzBtCF.kHd hcl (L := genSub 1782 4 lgp)
    (fun q hq => btKey_mem hgL hbL hpL hq)
    (fun x hx l hl e' => invE1_ext (s1_le hx) (l1_le hl) e') he he2 he1 heL

theorem f1Prop : F1Prop := f1Prop_of_cls cls_bound

end CertificateChecks.KernelSpor.SuzBtCG

end
