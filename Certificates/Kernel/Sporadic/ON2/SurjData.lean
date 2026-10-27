module

public import Certificates.Kernel.Sporadic.ON2.Checks
public import Certificates.Kernel.Sporadic.FLGen
public import CFSG.Certificates.Kernel.Spor.TabWords
public meta import Certificates.Kernel.Sporadic.ON2.Checks

public section

set_option maxRecDepth 400000

#kon_flists CFSG.KS.ON.tab CertificateChecks.KernelSpor.ONW CertificateChecks.KernelSpor.IMF
  CertificateChecks.KernelSpor.ON2.imgM 0 7

#kon_flists CFSG.KS.ON.tab CertificateChecks.KernelSpor.ONW CertificateChecks.KernelSpor.IIF
  CertificateChecks.KernelSpor.ON2.imgInvM 0 7

#kon_nests CFSG.KS.ON.tab CertificateChecks.KernelSpor.ONW CertificateChecks.KernelSpor.IMN
  CertificateChecks.KernelSpor.ON2.imgM 0 7

#kon_nests CFSG.KS.ON.tab CertificateChecks.KernelSpor.ONW CertificateChecks.KernelSpor.IIN
  CertificateChecks.KernelSpor.ON2.imgInvM 0 7

namespace CertificateChecks.KernelSpor.ON2

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.TW CFSG.KS.Words CFSG.KS.FLGen

@[expose] noncomputable def IMF (k : Nat) : List (Nat → Nat) :=
  cond (Nat.beq k 0) IMF0 (cond (Nat.beq k 1) IMF1 (cond (Nat.beq k 2) IMF2
    (cond (Nat.beq k 3) IMF3 (cond (Nat.beq k 4) IMF4 (cond (Nat.beq k 5) IMF5
      (cond (Nat.beq k 6) IMF6 ((decW (IMW.WC k) (IMW.WL k)).map (GZ ST SU))))))))

@[expose] noncomputable def IIF (k : Nat) : List (Nat → Nat) :=
  cond (Nat.beq k 0) IIF0 (cond (Nat.beq k 1) IIF1 (cond (Nat.beq k 2) IIF2
    (cond (Nat.beq k 3) IIF3 (cond (Nat.beq k 4) IIF4 (cond (Nat.beq k 5) IIF5
      (cond (Nat.beq k 6) IIF6 ((decW (IIW.WC k) (IIW.WL k)).map (GZ ST SU))))))))

@[expose] noncomputable def IMGF (k x : Nat) : Nat :=
  cond (Nat.beq k 0) (IMN0 x) (cond (Nat.beq k 1) (IMN1 x) (cond (Nat.beq k 2) (IMN2 x)
    (cond (Nat.beq k 3) (IMN3 x) (cond (Nat.beq k 4) (IMN4 x) (cond (Nat.beq k 5) (IMN5 x)
      (cond (Nat.beq k 6) (IMN6 x) (traceR (IMF k) x)))))))

@[expose] noncomputable def IMGIF (k x : Nat) : Nat :=
  cond (Nat.beq k 0) (IIN0 x) (cond (Nat.beq k 1) (IIN1 x) (cond (Nat.beq k 2) (IIN2 x)
    (cond (Nat.beq k 3) (IIN3 x) (cond (Nat.beq k 4) (IIN4 x) (cond (Nat.beq k 5) (IIN5 x)
      (cond (Nat.beq k 6) (IIN6 x) (traceR (IIF k) x)))))))

theorem IMGF_trace : ∀ k x, IMGF k x = traceR (IMF k) x
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ => by kernelRfl
  | _ + 7, _ => rfl

theorem IMGIF_trace : ∀ k x, IMGIF k x = traceR (IIF k) x
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ => by kernelRfl
  | _ + 7, _ => rfl

@[expose] noncomputable def surjF (t : Nat) : Bool :=
  strictB (cq t) fun x => bAnd(Nat.beq (trace IMGF IMGIF (SRW.WC 0) (SRW.WL 0) x) (tab ONW.A x),
    Nat.beq (trace IMGF IMGIF (SRW.WC 1) (SRW.WL 1) x) (tab ONW.B x))

theorem IMF0_eq : IMF0 = (decW (IMW.WC 0) (IMW.WL 0)).map (GZ ST SU) := by kernelRfl
theorem IMF1_eq : IMF1 = (decW (IMW.WC 1) (IMW.WL 1)).map (GZ ST SU) := by kernelRfl
theorem IMF2_eq : IMF2 = (decW (IMW.WC 2) (IMW.WL 2)).map (GZ ST SU) := by kernelRfl
theorem IMF3_eq : IMF3 = (decW (IMW.WC 3) (IMW.WL 3)).map (GZ ST SU) := by kernelRfl
theorem IMF4_eq : IMF4 = (decW (IMW.WC 4) (IMW.WL 4)).map (GZ ST SU) := by kernelRfl
theorem IMF5_eq : IMF5 = (decW (IMW.WC 5) (IMW.WL 5)).map (GZ ST SU) := by kernelRfl
theorem IMF6_eq : IMF6 = (decW (IMW.WC 6) (IMW.WL 6)).map (GZ ST SU) := by kernelRfl
theorem IIF0_eq : IIF0 = (decW (IIW.WC 0) (IIW.WL 0)).map (GZ ST SU) := by kernelRfl
theorem IIF1_eq : IIF1 = (decW (IIW.WC 1) (IIW.WL 1)).map (GZ ST SU) := by kernelRfl
theorem IIF2_eq : IIF2 = (decW (IIW.WC 2) (IIW.WL 2)).map (GZ ST SU) := by kernelRfl
theorem IIF3_eq : IIF3 = (decW (IIW.WC 3) (IIW.WL 3)).map (GZ ST SU) := by kernelRfl
theorem IIF4_eq : IIF4 = (decW (IIW.WC 4) (IIW.WL 4)).map (GZ ST SU) := by kernelRfl
theorem IIF5_eq : IIF5 = (decW (IIW.WC 5) (IIW.WL 5)).map (GZ ST SU) := by kernelRfl
theorem IIF6_eq : IIF6 = (decW (IIW.WC 6) (IIW.WL 6)).map (GZ ST SU) := by kernelRfl

theorem IMF_eq : ∀ k, IMF k = (decW (IMW.WC k) (IMW.WL k)).map (GZ ST SU)
  | 0 => IMF0_eq
  | 1 => IMF1_eq
  | 2 => IMF2_eq
  | 3 => IMF3_eq
  | 4 => IMF4_eq
  | 5 => IMF5_eq
  | 6 => IMF6_eq
  | _ + 7 => rfl

theorem IIF_eq : ∀ k, IIF k = (decW (IIW.WC k) (IIW.WL k)).map (GZ ST SU)
  | 0 => IIF0_eq
  | 1 => IIF1_eq
  | 2 => IIF2_eq
  | 3 => IIF3_eq
  | 4 => IIF4_eq
  | 5 => IIF5_eq
  | 6 => IIF6_eq
  | _ + 7 => rfl

theorem IMGF_eq : IMGF = IMG := by
  funext k x
  unfold IMG
  rw [IMGF_trace, IMF_eq, traceR_map, trace_eq]

theorem IMGIF_eq : IMGIF = IMGI := by
  funext k x
  unfold IMGI
  rw [IMGIF_trace, IIF_eq, traceR_map, trace_eq]

theorem surjF_eq (t : Nat) : surjF t = surjQ t := by
  unfold surjF surjQ
  rw [IMGF_eq, IMGIF_eq]

@[expose] noncomputable def relF (t : Nat) : Bool :=
  strictB (cq t) fun x => allN RLW.N fun j => Nat.beq (trace IMGF IMGIF (RLW.WC j) (RLW.WL j) x) x

theorem relF_eq (t : Nat) : relF t = relQ t := by
  unfold relF relQ
  rw [IMGF_eq, IMGIF_eq]

end CertificateChecks.KernelSpor.ON2

end
