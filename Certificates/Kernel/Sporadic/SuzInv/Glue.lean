module

public import CFSG.Certificates.Kernel.Spor.RawCongr
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CertificateChecks.KernelSpor.SuzInv

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem chain_of {S O : Array (Array Nat)} {base : Array Nat} {W : Array (List Int)}
    {PS G : Nat → Nat} {kS kO nb BP : Nat} (hb : Binds 1782 11 PS kS nb BP S base)
    (hO : O.size = kO) (hk : kO ≤ kS) (hOg : ∀ k < kO, O[k]! = unpack 1782 11 (G k))
    (hg : allN kO (fun k => Nat.beq (G k) (PS k)) = true)
    (hc : rawChainOK 1782 (S.extract 0 kO) S base W 4 = true) :
    rawChainOK 1782 O S base W 4 = true := by
  have hS : S.size = kS := hb.2.2.2.1
  rw [rawChainOK_congr (O' := S.extract 0 kO) (by simp [hO, hS]; omega)]
  · exact hc
  · intro k hkO
    rw [hO] at hkO
    rw [getElem!_pos (S.extract 0 kO) k (by simp [hS]; omega), Array.getElem_extract,
      ← getElem!_pos S (0 + k) (by omega), Nat.zero_add, hOg k hkO,
      Nat.eq_of_beq_eq_true (allN_spec hg k hkO), hb.2.2.2.2.1 k (by omega)]

end CertificateChecks.KernelSpor.SuzInv

end
