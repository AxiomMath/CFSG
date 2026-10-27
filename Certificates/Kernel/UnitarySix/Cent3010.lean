
module

public import Certificates.Kernel.UnitarySix.Cent3010Base

public import Certificates.Kernel.UnitarySix.KQFacts
public import CFSG.Sporadic.Schreier.RuEnum
public import CFSG.Certificates.NativeSchreierEnum
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Mathieu CFSG.Certificates CFSG.Certificates.Native
open CFSG.Certificates.ChainArrays CFSG.KC.U6 CFSG.EvenSmallLie.UnitarySix

theorem cent3010 :
    (∀ k ∈ Subgroup.closure {g | g ∈ kGens}, (∀ a ∈ aGens, k * a = a * k) → k = 1) ∧
      ∀ k ∈ Subgroup.closure {g | g ∈ kGens}, k * j3 = j3 * k →
        ∀ a ∈ Subgroup.closure {g | g ∈ aGens}, (a * k) ^ 2 ≠ j3 := by
  have hA := KQ.arrays
  have hF := chainCheckFacts KQ.raw
  have hsz := kQ_lev_size
  have htr := trK_sound KQ.binds KQ.perm KQ.hl
  have hQ : kQ.originalSubgroup = Subgroup.closure {g | g ∈ kGensG u62Letters kWords} := by
    rw [kQ, CFSG.Sporadic.Schreier.certificate_originalSubgroup]
    rfl
  have hb0 : 0 < kQ.baseCount := by
    change 0 < 3
    norm_num
  have hb1 : 1 < kQ.baseCount := by
    change 1 < 3
    norm_num
  have hb2 : 2 < kQ.baseCount := by
    change 2 < 3
    norm_num
  have hb3 : 3 ≤ kQ.baseCount := le_refl 3
  refine sound3010C (X := fun i k => levT 693 KQ.SA kBase i k) letters_eq aWN_eq kWN_eq tWN_eq
    k3010S (fun i hi k hk => ?_) (fun i hi k hk => ?_) (fun g hg => ?_) ?_ kCent
  · have hk' : k < rcnt (KQ.LR i) := by rw [(hsz i hi).2]; exact hk
    have := htr i hi k hk'
    interval_cases i <;> exact this
  · rw [← hQ]
    exact CFSG.Sporadic.RuSchreier.chain_levT_mem_original hA (by norm_num) KQ.raw
      (lt_of_lt_of_le hi hb3) (by rw [(hsz i hi).1]; exact hk)
  · rw [← hQ] at hg
    obtain ⟨a, ha, b, hb, c, hc, h⟩ := hA.exists_prod3 (by norm_num) KQ.raw hb3
      (fun i h3 h3' => absurd h3' (by change ¬ i < 3; omega)) hg
    rw [(hsz 0 (by norm_num)).1] at ha
    rw [(hsz 1 (by norm_num)).1] at hb
    rw [(hsz 2 (by norm_num)).1] at hc
    exact ⟨a, ha, b, hb, c, hc, h⟩
  · exact ⟨hA.levT_zero hF hb0, hA.levT_zero hF hb1, hA.levT_zero hF hb2⟩

end CertificateChecks.KernelU6

end
