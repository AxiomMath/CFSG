module

public import Certificates.Data.Kernel.Fi22Dc2.Defs
public import Certificates.Kernel.Sporadic.Fi22.X2069Ext
public import Certificates.Kernel.Sporadic.Fi22.X2069PT
public import Certificates.Kernel.SporSch.Ru.RowsGen

public noncomputable section

namespace CFSG.KD.Fi22Dc2

@[expose] def tOK (j : Nat) : Bool :=
  (List.range 3510).all fun p => Nat.beq
    (P (CFSG.KC.Enum.pg 12 (CFSG.KS.mask 12) (CertificateChecks.KernelSpor.Fi22X.TS j) (Q p)))
    (CFSG.KC.E64F.wordF L (tw j) p)

@[expose] def aOK (k : Nat) : Bool :=
  (List.range 3510).all fun p => Nat.beq (L (5 + k) p)
    (P (CFSG.KC.Enum.pg 12 (CFSG.KS.mask 12) (CertificateChecks.KernelSpor.Fi22ChT.F k) (Q p)))

end CFSG.KD.Fi22Dc2

#kss_each CFSG.KD.Fi22Dc2.LT CFSG.KD.Fi22Dc2.tOK 9

#kss_each CFSG.KD.Fi22Dc2.LA CFSG.KD.Fi22Dc2.aOK 2

namespace CFSG.KD.Fi22Dc2

theorem lets_T (hQ : ∀ p < 3510, Q p < 3510) : ∀ j < 9, ∀ p < 3510,
    P (((CFSG.Monster.B.Fischer.fi22OuterStrong3510 4)[j]!)[Q p]!) =
      CFSG.KC.E64F.wordF L (tw j) p := by
  intro j hj p hp
  rw [CertificateChecks.KernelSpor.Fi22X.outT_eq (by omega), CFSG.KS.Raw.unpack,
    getElem!_pos _ (Q p) (by simpa using hQ p hp), Array.getElem_ofFn]
  have h : tOK j = true := LT.all j hj
  unfold tOK at h
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.1 h p (List.mem_range.2 hp))

theorem lets_ab (hQ : ∀ p < 3510, Q p < 3510) : ∀ k < 2, ∀ p < 3510,
    L (5 + k) p = P ((CFSG.Monster.B.Fischer.fi22StrongArrs[k]!)[Q p]!) := by
  intro k hk p hp
  rw [CertificateChecks.KernelSpor.Fi22X.strong_eq (by omega), CFSG.KS.Raw.unpack,
    getElem!_pos _ (Q p) (by simpa using hQ p hp), Array.getElem_ofFn]
  have h : aOK k = true := LA.all k hk
  unfold aOK at h
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.1 h p (List.mem_range.2 hp))

end CFSG.KD.Fi22Dc2

end
